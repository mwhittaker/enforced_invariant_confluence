from enum import Enum
from textwrap import wrap
from typing import Callable, Dict, List, Optional, Set, Tuple

from colored import attr, fg
from orderedset import OrderedSet
import z3

from ..ast import EVar, Invariant
from ..checker import Checker, Decision
from ..envs import CrdtEnv, TypeEnv, ValEnv
from ..typecheck import typecheck_invariant
from ..z3_.compile import compile_expr, compile_join, compile_var
from ..z3_.fresh_name import FreshName
from ..z3_.model import model_and_venv_to_state
from ..z3_.version_env import VersionEnv
from ..z3_.z3_util import scoped
from .arbitrary_start_checker import ArbitraryStartChecker

def _wrap_print(s: str) -> None:
    print('\n'.join(wrap(s, 80)))

def _box_string_lhs(s: str) -> str:
    return s + '_lhs'

def _box_string_rhs(s: str) -> str:
    return s + '_rhs'

def _box_var_lhs(v: EVar) -> EVar:
    v_boxed = EVar(_box_string_lhs(v.x))
    v_boxed.typ = v.typ
    return v_boxed

def _box_var_rhs(v: EVar) -> EVar:
    v_boxed = EVar(_box_string_rhs(v.x))
    v_boxed.typ = v.typ
    return v_boxed

class Colabel(Enum):
    COREACHABLE = "coreachable"
    COUNREACHABLE = "counreachable"

class ArbitraryStartInteractiveChecker(ArbitraryStartChecker):
    """
    TODO(mwhittaker): Document.
    """
    def __init__(self, verbose: bool = False) -> None:
        ArbitraryStartChecker.__init__(self)

        self.verbose = verbose
        self.solver = z3.Solver()
        self.fresh = FreshName()

        self.split_vars: Set[str] = set()
        self.coreachable_type_env: TypeEnv = dict()
        self.coreachable_crdt_env: CrdtEnv = dict()
        self.coreachable_refinements: List[Invariant] = []

        # Counterexamples.
        self.lhs: Optional[ValEnv] = None
        self.rhs: Optional[ValEnv] = None
        self.label: Optional[Colabel] = None
        self.counreachable_states: List[Tuple[ValEnv, ValEnv]] = []

    def __str__(self) -> str:
        strings: List[str] = []

        if len(self.coreachable_refinements) > 0:
            strings += ['Coreachable Refinements']
            for inv in self.coreachable_refinements:
                strings.append(f'  {inv}')

        if len(self.counreachable_states) > 0:
            strings += ['Counreachable States']
            strings += [f'  ...']
            for (lhs, rhs) in self.counreachable_states:
                strings += [f'  lhs = {lhs}']
                strings += [f'  rhs = {rhs}']

        if (self.lhs is not None and self.rhs is not None):
            strings += ['Pending States']
            strings.append(f'  lhs   = {self.lhs}')
            strings.append(f'  rhs   = {self.rhs}')
            strings.append(f'  label = {self.label}')

        return '\n'.join([ArbitraryStartChecker.__str__(self)] + strings)

    def _venv_satisfies_invs(self,
                             venv: VersionEnv,
                             tenv: TypeEnv,
                             invs: List[Invariant]) \
                             -> OrderedSet:
        zss = OrderedSet()
        for inv in invs:
            inv_zss, inv_ze = compile_expr(inv, venv, tenv, self.fresh)
            zss |= inv_zss
            zss.add(inv_ze)
        return zss

    def _venv_doesnt_satisfy_invs(self,
                                  venv: VersionEnv,
                                  tenv: TypeEnv,
                                  invs: List[Invariant]) \
                                  -> OrderedSet:
        zss = OrderedSet()
        zes = OrderedSet()
        for inv in invs:
            inv_zss, inv_ze = compile_expr(inv, venv, tenv, self.fresh)
            zss |= inv_zss
            zes.add(inv_ze)
        zss.add(z3.Not(z3.And(list(zes))))
        return zss

    def _rename_venvs(self,
                      from_venv: VersionEnv,
                      from_tenv: TypeEnv,
                      to_venv: VersionEnv,
                      to_tenv: TypeEnv,
                      renames: Dict[str, str]) \
                      -> Tuple[OrderedSet, VersionEnv]:
        zss = OrderedSet()
        for name, new_name in renames.items():
            from_typ = from_tenv[name]
            to_typ = to_tenv[new_name]
            assert from_typ == to_typ, (from_typ, to_typ)

            from_var = EVar(name)
            from_var.typ = from_typ
            to_var = EVar(new_name)
            to_var.typ = to_typ

            to_venv = to_venv.assign(new_name)
            from_var_z = compile_var(from_var, from_venv, from_tenv)
            to_var_z = compile_var(to_var, to_venv, to_tenv)
            zss.add(to_var_z == from_var_z)
        return zss, to_venv

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
            if self.label == Colabel.COREACHABLE:
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
            lhs_zss = self._venv_satisfies_invs(lhs_venv, self.type_env, invs)
            rhs_venv = VersionEnv('rhs')
            rhs_zss = self._venv_satisfies_invs(rhs_venv, self.type_env, invs)

            # Assert that lhs and rhs are coreachable.
            if len(self.coreachable_refinements) > 0:
                coreachable_venv = VersionEnv('coreachable')
                lhs_renames = {v: _box_string_lhs(v) for v in self.split_vars}
                coreachable_zss_lhs, coreachable_venv = self._rename_venvs(
                   lhs_venv, self.type_env, coreachable_venv,
                   self.coreachable_type_env, lhs_renames)
                rhs_renames = {v: _box_string_rhs(v) for v in self.split_vars}
                coreachable_zss_rhs, coreachable_venv = self._rename_venvs(
                   rhs_venv, self.type_env, coreachable_venv,
                   self.coreachable_type_env, rhs_renames)
                coreachable_zss = self._venv_satisfies_invs(
                    coreachable_venv, self.coreachable_type_env,
                    self.coreachable_refinements)
                coreachable_zss = (coreachable_zss_lhs |
                                   coreachable_zss_rhs |
                                   coreachable_zss)
            else:
                coreachable_zss = OrderedSet()

            # Join environments.
            join_venv = VersionEnv('joined')
            join_zss, join_venv = compile_join(
                lhs_venv, rhs_venv, join_venv, self.crdt_env, self.type_env,
                self.fresh)

            # Assert that joined environment doesn't satisfy invariant.
            join_zss |= self._venv_doesnt_satisfy_invs(
                join_venv, self.type_env, invs)

            # Register code and check for counterexamples.
            zss = lhs_zss | rhs_zss | coreachable_zss | join_zss
            self.solver.add(list(zss))
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

    def coreachable(self) -> None:
        self.label = Colabel.COREACHABLE

    def counreachable(self) -> None:
        self.label = Colabel.COUNREACHABLE

    def split(self, var: EVar) -> Tuple[EVar, EVar]:
        name = var.x
        name_lhs = _box_string_lhs(var.x)
        name_rhs = _box_string_rhs(var.x)

        assert name_lhs not in self.coreachable_type_env, name_lhs
        assert name_rhs not in self.coreachable_type_env, name_rhs
        assert name_lhs not in self.coreachable_crdt_env, name_lhs
        assert name_rhs not in self.coreachable_crdt_env, name_rhs
        self.coreachable_type_env[name_lhs] = self.type_env[name]
        self.coreachable_type_env[name_rhs] = self.type_env[name]
        self.coreachable_crdt_env[name_lhs] = self.crdt_env[name]
        self.coreachable_crdt_env[name_rhs] = self.crdt_env[name]

        self.split_vars.add(name)
        return (_box_var_lhs(var), _box_var_rhs(var))

    def refine_coreachable(self, inv: Invariant) -> None:
        inv = typecheck_invariant(inv, self.coreachable_type_env)
        self.coreachable_refinements.append(inv)
