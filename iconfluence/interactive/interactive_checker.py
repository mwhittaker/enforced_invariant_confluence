from typing import List, Optional, Tuple

import z3
from orderedset import OrderedSet

from ..ast import Expr, Invariant
from ..checker import Checker, Decision
from ..envs import ValEnv
from ..envs import ValEnv
from ..eval import eval_invariant
from ..guess_and_check import NothingFoundException, StateExplorer
from ..z3_.z3_util import result_to_decision, scoped
from ..z3_.version_env import VersionEnv
from ..z3_.fresh_name import FreshName
from ..z3_ import compile

class InteractiveChecker(Checker):
    def __init__(self) -> None:
        Checker.__init__(self)

        self.solver = z3.Solver()
        self.fresh = FreshName()

        self.reachable_refinements: List[Invariant] = []
        self.unreachable_refinements: List[Invariant] = []
        self.reachable = StateExplorer(self.crdt_env, self.start_state,
                                       self.invariants, self.transactions)
        self.counterexample1: Optional[ValEnv] = None
        self.counterexample2: Optional[ValEnv] = None

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

        for inv in self.reachable_refinements:
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(inv_ze)

        for ninv in self.unreachable_refinements:
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(z3.Not(inv_ze))

        return z3.And(list(zss))

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
            # TODO(mwhittaker): Get counterexample
            return Decision.UNKNOWN

    def check_iconfluence(self) -> Decision:
        if not self._state_satisfies_invs(self.start_state):
            return Decision.NO
        else:
            return self._is_refined_i_closed()
