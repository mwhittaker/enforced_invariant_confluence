from typing import List, Optional, Set
from textwrap import wrap

import z3

from ..ast import Invariant
from .. import ast
from ..checker import Checker, Decision
from ..eval import eval_invariant
from ..typecheck import typecheck_invariant
from ..z3_.compile import (compile_venv_satisfies_invs,
                           compile_venv_doesnt_satisfy_invs)
from ..z3_.fresh_name import FreshName
from ..z3_.version_env import VersionEnv
from ..z3_.z3_util import scoped
from .arbitrary_start_interactive_checker import (
    ArbitraryStartInteractiveChecker)

def _wrap_print(s: str) -> None:
    print('\n'.join(wrap(s, 80)))

class BufferedChecker(ArbitraryStartInteractiveChecker):
    def __init__(self, *args, **kwargs):
        ArbitraryStartInteractiveChecker.__init__(self, *args, **kwargs)
        self.decision: Optional[Decision] = None

    def check(self) -> Decision:
        self.decision = ArbitraryStartInteractiveChecker.check(self)
        return self.decision

class Stratum:
    def __init__(self, parent: 'StratifiedChecker', name: str) -> None:
        self.parent = parent
        self.name = name
        self.transactions: List[str] = []
        self.invariants: List[Invariant] = []
        self.checker: Optional[BufferedChecker] = None

    def __str__(self) -> str:
        strings: List[str] = []

        strings.append('Transactions')
        for txn in self.transactions:
            strings.append(f'  {txn}')

        strings.append('Invariants')
        for inv in self.invariants:
            strings.append(f'  {inv}')

        return '\n'.join(strings)

    def __repr__(self) -> str:
        return str(self)

    def add_transaction(self, txn: str) -> None:
        if txn not in self.parent.transactions:
            txns = ', '.join(self.parent.transactions)
            m = (f'Transaction {txn} is not registered. The registered ' +
                 f'transactions are: {txns}.')
            raise ValueError(m)

        if txn not in self.transactions:
            self.transactions.append(txn)

    def add_invariant(self, inv: Invariant) -> None:
        inv = typecheck_invariant(inv, self.parent.type_env)
        self.invariants.append(inv)

class StratifiedChecker(Checker):
    def __init__(self, verbose: bool = True) -> None:
        Checker.__init__(self)

        self.verbose = verbose
        self.solver = z3.Solver()
        self.fresh = FreshName()
        self.strata: List[Stratum] = []
        self.strata_checkers_created = False

    def __str__(self) -> str:
        strings = ['Strata']
        for stratum in self.strata:
            strings += [f'  {stratum.name}']
        return '\n'.join([Checker.__str__(self)] + strings)

    def _invs_implies_invs(self,
                           lhs: List[Invariant],
                           rhs: List[Invariant]) \
                           -> Optional[bool]:
        with scoped(self.solver):
            venv = VersionEnv('invs_implies_invs')
            tenv = self.type_env
            fresh = self.fresh
            zss = compile_venv_satisfies_invs(lhs, venv, tenv, fresh)
            zss |= compile_venv_doesnt_satisfy_invs(rhs, venv, tenv, fresh)
            self.solver.add(list(zss))
            result = self.solver.check()
            if result == z3.unknown:
                return None
            elif result == z3.unsat:
                return True
            else:
                assert result == z3.sat, None
                return False

    def _and(self, invs: List[Invariant]) -> Invariant:
        inv = ast.coerce(True)
        for i in invs:
            inv = ast.EBoolAnd(inv, i)
        inv = typecheck_invariant(inv, self.type_env)
        return inv

    def _or(self, invs: List[Invariant]) -> Invariant:
        inv = ast.coerce(False)
        for i in invs:
            inv = ast.EBoolOr(inv, i)
        inv = typecheck_invariant(inv, self.type_env)
        return inv

    def stratum(self, name: str) -> Stratum:
        s = Stratum(self, name)
        self.strata.append(s)
        return s

    def check(self) -> Decision:
        # Check that there is at least one stratum.
        if len(self.strata) == 0:
            _wrap_print('Create strata with the stratum() method before ' +
                        'calling check().')
            return Decision.UNKNOWN

        # Check each stratum's checker.
        if self.strata_checkers_created:
            decisions = set(stratum.checker.decision for stratum in self.strata)
            if decisions == {Decision.YES}:
                return Decision.YES
            elif Decision.NO in decisions:
                return Decision.NO
            else:
                assert Decision.UNKNOWN in decisions, decisions
                return Decision.UNKNOWN

        # Check that the start state satisfies the invariant.
        invs = list(self.invariants.values())
        if not all(eval_invariant(inv, self.s0_vals) for inv in invs):
            return Decision.NO

        # Check that each stratum's invariant is a subset of the invariant.
        for i, stratum in enumerate(self.strata):
            result = self._invs_implies_invs(stratum.invariants, invs)
            if result is None:
                print('Z3 got stuck!')
                return Decision.UNKNOWN
            elif not result:
                m = f'Stratum {i} invariant is not a subset of the invariant.'
                print(m)
                return Decision.UNKNOWN

        # Check that the invariant is a subset of the union of all the
        # stratum's invariants.
        strata_invs = [self._and(stratum.invariants) for stratum in self.strata]
        strata_inv = self._or(strata_invs)
        result = self._invs_implies_invs(invs, [strata_inv])
        if result is None:
            print('Z3 got stuck!')
            return Decision.UNKNOWN
        elif not result:
            _wrap_print(f'The invariant is not a subset of the union of ' +
                        f'all stratum\'s invariants')
            return Decision.UNKNOWN

        # Create checkers for each stratum.
        for i, stratum in enumerate(self.strata):
            # TODO(mwhittaker): Think about whether we can just copy over our
            # internal state into the checker instead of having to call all the
            # methods again.
            checker = BufferedChecker(self.verbose)
            for name, crdt in self.crdt_env.items():
                if isinstance(crdt, ast.CIntMax):
                    checker.int_max(name, None)
                elif isinstance(crdt, ast.CIntMin):
                    checker.int_min(name, None)
                elif isinstance(crdt, ast.CBoolOr):
                    checker.bool_or(name, None)
                elif isinstance(crdt, ast.CBoolOr):
                    checker.bool_or(name, None)
                elif isinstance(crdt, ast.CBoolAnd):
                    checker.bool_and(name, None)
                elif isinstance(crdt, ast.CTuple2):
                    checker.tuple2(name, crdt.a, crdt.b, None)
                elif isinstance(crdt, ast.CSetUnion):
                    checker.set_union(name, crdt.a, None)
                elif isinstance(crdt, ast.CSetIntersect):
                    checker.set_intersect(name, crdt.a, None)
                elif isinstance(crdt, ast.CMap):
                    checker.map(name, crdt.k, crdt.v, None)
                elif isinstance(crdt, ast.COption):
                    checker.option(name, crdt.a, None)
                else:
                    raise ValueError(f'Unrecognized CRDT {crdt}.')
            for name in stratum.transactions:
                checker.add_transaction(name, self.transactions[name])
            for j, inv in enumerate(stratum.invariants):
                checker.add_invariant(f'stratum_{i}_{j}', inv)
            stratum.checker = checker

        self.strata_checkers_created = True
        _wrap_print('For each stratum s, use s.checker to determine ' +
                    'whether or not the stratum s is ' +
                    'invariant-confluent. If all checkers return yes, ' +
                    'then the object is stratified invariant confluent. ' +
                    'If any checker returns no, then the object is not ' +
                    'stratified invariant confluent. Otherwise, we ' +
                    'cannot determine whether this object is invariant ' +
                    'confluent. Call check() at any time figure out ' +
                    'whether the object is stratified invariant confluent.')
        return Decision.UNKNOWN
