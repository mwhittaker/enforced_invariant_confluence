from enum import Enum
from typing import List, Optional, Tuple

import z3
from orderedset import OrderedSet

from ..ast import EVar, Expr, Invariant
from ..checker import Checker, Decision
from ..typecheck import typecheck_invariant
from ..envs import ValEnv, TypeEnv, Z3ExprEnv
from ..eval import eval_invariant
from ..z3_.z3_util import result_to_decision, scoped
from ..z3_.version_env import VersionEnv
from ..z3_.fresh_name import FreshName
from ..z3_ import compile

class Label(Enum):
    REACHABLE = "reachable"
    UNREACHABLE = "unreachable"


class InteractiveChecker(Checker):
    """
    MISSING features
        - state xploration + labelling
        - integrating negative examples into invarinatn
    """
    def __init__(self) -> None:
        Checker.__init__(self)

        self.solver = z3.Solver()
        self.fresh = FreshName()
        self.invariant_refinements: List[Invariant] = []
        self.counterexample1: Optional[Z3ExprEnv] = None
        self.counterexample1_label: Optional[Label] = None
        self.counterexample2: Optional[Z3ExprEnv] = None
        self.counterexample2_label: Optional[Label] = None

    # TODO compile start state to z3 expression and check it agains invs.
    def _state_satisfies_invs(self, state: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, state) for inv in invs)

    def _compile_expr(self,
                      e: Expr,
                      venv: VersionEnv) -> Tuple[OrderedSet, z3.ExprRef]:
        return compile.compile_expr(e, venv, self.type_env, self.fresh)

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

            # Check if we're I - NR closed.
            result = self.solver.check()

            # If z3 is stuck, we're stuck.
            if result == z3.unknown:
                print('Z3 got stuck!')
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

            print('Counterexample found.')
            print(f'counterexample1 = {self.counterexample1}.')
            print(f'counterexample2 = {self.counterexample2}.')

            return Decision.UNKNOWN

    def check_iconfluence(self) -> Decision:
        msg = ('Counterexample {0} is unlabelled. Call ' +
               '`counterexample{0}_reachable()` to label the counterexample ' +
               'as reachable or `counterexample{0}_unreachable()` to label ' +
               'the counterexample as unreachable.')
        if (self.counterexample1 is not None and
            self.counterexample1_label is None):
            print(msg.format(1))
            return Decision.UNKNOWN

        if (self.counterexample2 is not None and
            self.counterexample2_label is None):
            print(msg.format(2))
            return Decision.UNKNOWN

        if (self.counterexample1 is not None and
            self.counterexample2 is not None):
            if (self.counterexample1_label == Label.REACHABLE and
                self.counterexample2_label == Label.REACHABLE):
                return Decision.NO
            else:
                self.counterexample1 = None
                self.counterexample2 = None
                self.counterexample1_label = None
                self.counterexample2_label = None

        # TODO: Fix start state check.
        if not self._state_satisfies_invs(self.s0_vals):
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
