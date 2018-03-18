from enum import Enum
from typing import List, Optional, Tuple

import z3
from orderedset import OrderedSet

from ..ast import EVar, Expr, Invariant
from ..checker import Checker, Decision
from ..typecheck import typecheck_invariant
from ..envs import ValEnv, TypeEnv, Z3ExprEnv
from ..eval import eval_invariant
from ..guess_and_check import NothingFoundException, StateExplorer
from ..z3_.z3_util import result_to_decision, scoped
from ..z3_.version_env import VersionEnv
from ..z3_.fresh_name import FreshName
from ..z3_ import compile

class Label(Enum):
    REACHABLE = "reachable"
    UNREACHABLE = "unreachable"

class InteractiveChecker(Checker):
    def __init__(self) -> None:
        Checker.__init__(self)

        self.solver = z3.Solver()
        self.fresh = FreshName()
        self.invariant_refinements: List[Invariant] = []
        self.unreachable: List[z3.ExprRef] = []
        # TODO(mwhittaker): Use reachable states to label counterexamples. It's
        # a little challening because Z3 counterexamples involve Z3
        # expressions, not values. We could evaluate a Z3 expression into a
        # value.
        self.reachable = StateExplorer(self.crdt_env, self.start_state,
                                       self.invariants, self.transactions)

        self.counterexample1: Optional[Z3ExprEnv] = None
        self.counterexample1_label: Optional[Label] = None
        self.counterexample2: Optional[Z3ExprEnv] = None
        self.counterexample2_label: Optional[Label] = None

    def _state_satisfies_invs(self, state: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, state) for inv in invs)

    def _compile_expr(self,
                      e: Expr,
                      venv: VersionEnv) -> Tuple[OrderedSet, z3.ExprRef]:
        return compile.compile_expr(e, venv, self.type_env, self.fresh)

    def _venv_satisfies_inv(self,
                            venv: VersionEnv,
                            inv: z3.ExprRef) \
                            -> OrderedSet:
        zss, ze = self._compile_expr(inv, venv)
        zss.add(ze)
        return zss

    def _venv_satisfies_refined_i(self, venv: VersionEnv) -> z3.ExprRef:
        zss = OrderedSet()

        for inv in self.invariants.values():
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(inv_ze)

        for inv in self.invariant_refinements:
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(inv_ze)

        return z3.And(list(zss))

    def _extract_counterexample_from_model(self, \
                                           model: z3.ModelRef, \
                                           venv: VersionEnv,
                                           tenv: TypeEnv) -> Z3ExprEnv:
        z3_expr_env: Z3ExprEnv = dict()
        for (v, typ) in tenv.items():
            x = EVar(v)
            zx = compile.compile_var(x, venv, tenv)
            z3_expr_env[v] = model[zx]
        return z3_expr_env

    def _is_refined_i_closed(self) -> Decision:
        with scoped(self.solver):
            # Assert rhs satisfies invariant.
            lhs_venv = VersionEnv('lhs')
            self.solver.add(self._venv_satisfies_refined_i(lhs_venv))

            # Assert lhs satisfies invariant.
            rhs_venv = VersionEnv('rhs')
            self.solver.add(self._venv_satisfies_refined_i(rhs_venv))

            # Compute join.
            join_venv = VersionEnv('joined')
            zss, join_env = compile.compile_join(lhs_venv, rhs_venv, join_venv,
                                                 self.crdt_env, self.type_env,
                                                 self.fresh)
            self.solver.add(list(zss))

            # Assert join satisfies invariant.
            self.solver.add(z3.Not(self._venv_satisfies_refined_i(join_env)))

            print(self.solver.sexpr())

            # Check if we're I - NR closed.
            result = self.solver.check()

            # If z3 is stuck, we're stuck.
            if result == z3.unknown:
                return Decision.UNKNOWN

            # If there are no counterexamples, then we are invariant-closed.
            if result == z3.unsat:
                return Decision.YES

            # Otherwise, we are are not invariant-closed, and we have a
            # counterexample.
            model = self.solver.model()
            self.counterexample1 = self._extract_counterexample_from_model(
                model, lhs_venv, self.type_env)
            self.counterexample2 = self._extract_counterexample_from_model(
                model, rhs_venv, self.type_env)

            return Decision.UNKNOWN

    def check_iconfluence(self) -> Decision:
        if (self.counterexample1 is not None and
            self.counterexample1_label is None):
            print("Counterexample 1 is unlabelled.")
            return Decision.UNKNOWN

        if (self.counterexample2 is not None and
            self.counterexample2_label is None):
            print("Counterexample 2 is unlabelled.")
            return Decision.UNKNOWN

        if (self.counterexample1 is not None and
            self.counterexample2 is not None):
            pass


        if not self._state_satisfies_invs(self.start_state):
            return Decision.NO
        else:
            return self._is_refined_i_closed()

    def counterexample1_reachable(self):
        self.counterexample1_label = Label.REACHABLE

    def counterexample1_unreachable(self):
        self.counterexample1_label = Label.UNREACHABLE

    def counterexample2_reachable(self):
        self.counterexample2_label = Label.REACHABLE

    def counterexample2_unreachable(self):
        self.counterexample2_label = Label.UNREACHABLE

    def refine_invariant(self, inv: Invariant):
        inv = typecheck_invariant(inv, self.type_env)
        self.invariant_refinements.append(inv)
