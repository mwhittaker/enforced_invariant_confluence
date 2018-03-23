from enum import Enum
from textwrap import wrap
from typing import List, Optional, Tuple

from colored import attr, fg
from orderedset import OrderedSet
import z3

from ..ast import Invariant
from ..checker import Checker, Decision
from ..envs import ValEnv
from ..z3_.compile import compile_expr, compile_join
from ..z3_.fresh_name import FreshName
from ..z3_.model import model_and_venv_to_state
from ..z3_.version_env import VersionEnv
from ..z3_.z3_util import scoped
from .arbitrary_start_checker import (ArbitraryStartChecker, _wrap_string_lhs,
                                      _wrap_string_rhs)

def _wrap_print(s: str) -> None:
    print('\n'.join(wrap(s, 80)))

class Label(Enum):
    COREACHABLE = "coreachable"
    COUNREACHABLE = "counreachable"

class ArbitraryStartInteractiveChecker(ArbitraryStartChecker):
    """
    TODO(mwhittaker): Document.
    """
    def __init__(self, verbose: bool = False) -> None:
        self.verbose = verbose
        self.solver = z3.Solver()
        self.fresh = FreshName()
        self.coreachable_refinements: List[Invariant] = []

        # Counterexamples.
        self.lhs: Optional[ValEnv] = None
        self.rhs: Optional[ValEnv] = None
        self.label: Optional[Label] = None
        self.counreachable_states: List[Tuple[ValEnv, ValEnv]] = []

    def __str__(self) -> str:
        return 'TODO'

    def __repr__(self) -> str:
        return str(self)

    def coreachable(self) -> None:
        self.label = Label.COREACHABLE

    def _venv_satisfies_invs(self,
                             venv: VersionEnv,
                             invs: List[Invariant]) \
                             -> OrderedSet:
        zss = OrderedSet()
        for inv in invs:
            inv_zss, inv_ze = compile_expr(inv, venv, self.type_env, self.fresh)
            zss |= inv_zss
            zss.add(inv_ze)
        return zss

    def _venv_doesnt_satisfy_invs(self,
                                  venv: VersionEnv,
                                  invs: List[Invariant]) \
                                  -> OrderedSet:
        zss = OrderedSet()
        zes = OrderedSet()
        for inv in invs:
            inv_zss, inv_ze = compile_expr(inv, venv, self.type_env, self.fresh)
            zss |= inv_zss
            zes.add(inv_ze)
        zss.add(z3.Not(z3.And(list(zes))))
        return zss

    def counreachable(self) -> None:
        self.label = Label.COUNREACHABLE

    def check(self) -> Decision:
        if self.lhs is not None:
            assert self.rhs is not None, self.rhs
            if self.label is None:
                m = ('You have not labelled whether lhs and rhs are ' +
                     'coreachable or counreachable. Please call the ' +
                     'coreachable() or counreachable() methods to label them.')
                _wrap_print(m)
                return Decision.UNKNOWN

        if self.lhs is not None:
            assert self.rhs is not None and self.label is not None
            if self.label == Label.COREACHABLE:
                return Decision.NO

            self.counreachable_states.append((self.lhs, self.rhs))
            # TODO(mwhittaker): Automatically refine coreachability.
            self.lhs = None
            self.rhs = None
            self.label = None

        with scoped(self.solver):
            # Assert that lhs and rhs satisfy the invariant.
            invs = list(self.invariants.values())
            lhs_venv = VersionEnv('lhs')
            lhs_zss = self._venv_satisfies_invs(lhs_venv, invs)
            rhs_venv = VersionEnv('rhs')
            rhs_zss = self._venv_satisfies_invs(rhs_venv, invs)

            # Assert that lhs and rhs are coreachable.
            if len(self.coreachable_refinements) > 0:
                lhs_rename_venv = lhs_venv.rename(_wrap_string_lhs)
                rhs_rename_venv = rhs_venv.rename(_wrap_string_rhs)
                coreachable_venv = lhs_rename_venv.update(rhs_rename_venv)
                coreachable_zss = self._venv_satisfies_invs(
                    coreachable_venv, self.coreachable_refinements)

            # Join environments.
            join_venv = VersionEnv('joined')
            join_zss, join_venv = compile_join(
                lhs_venv, rhs_venv, join_venv, self.crdt_env, self.type_env,
                self.fresh)

            # Assert that joined environment doesn't satisfy invariant.
            invs = self.coreachable_refinements
            join_zss |= self._venv_doesnt_satisfy_invs(join_venv, invs)

            # Register code and check for counterexamples.
            self.solver.add(list(lhs_zss | rhs_zss | join_zss))
            if self.verbose:
                print(f'{fg(206)}{self.solver.sexpr()}{attr(0)}')
            result = self.solver.check()

            # If Z3 is stuck, we're stuck.
            if result == z3.unknown:
                print('Z3 got stuck!')
                return Decision.UNKNOWN

            # If there are no counterexamples, we're invariant-confluent.
            if result == z3.unsat:
                return Decision.YES

            # Otherwise, there are counterexamples. Extract them.
            model = self.solver.model()
            vars = set(self.type_env.keys())
            self.lhs = model_and_venv_to_state(model, vars, lhs_venv)
            self.rhs = model_and_venv_to_state(model, vars, rhs_venv)
            join = model_and_venv_to_state(model, vars, join_venv)

            # TODO(mwhittaker): Check whether the states are reachable.

            # TODO(mwhittaker): Improve printing.
            m = ('The following two states (i.e. lhs and rhs) satisfy the ' +
                 'invariant, but their join does not. Please use the ' +
                 'coreachable() and counreachable() methods to label the ' +
                 'states as coreachable or counreachable.')
            _wrap_print(m)
            print('')
            print(f'  lhs = {self.lhs}.')
            print(f'  rhs = {self.rhs}.')
            print(f'  lhs join rhs = {join}.')

            return Decision.UNKNOWN

        raise NotImplementedError()
