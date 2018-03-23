from typing import Dict, Tuple, Set
from textwrap import wrap

from .. import ast
from .. import typecheck
from ..ast import Coercible, Crdt, EVar, Invariant, Transaction, Type
from ..checker import Checker, Decision
from ..envs import CrdtEnv, ExprEnv, TypeEnv, ValEnv
from ..eval import eval_expr

def _wrap_print(s: str) -> None:
    print('\n'.join(wrap(s, 80)))

class ArbitraryStartChecker(Checker):
    """
    TODO(mwhittaker): Document.
    """
    def __str__(self):
        strings = []

        strings.append('State')
        for name in self.crdt_env:
            strings.append(f'  {name}: {self.crdt_env[name]}')

        strings += ['Invariants']
        for (name, inv) in self.invariants.items():
            strings.append(f'  {name} == {inv}')

        strings += ['Transactions']
        for (name, txn) in self.transactions.items():
            strings.append(f'  def {name}():')
            for s in txn:
                strings.append(f'    {s}')

        return '\n'.join(strings)

    def __repr__(self):
        return str(self)

    def _warn_if_not_none(self, val: Coercible) -> None:
        if val is not None:
            _wrap_print(f'WARNING: You have provided a start value {val} to ' +
                        f'an ArbitraryStartChecker, but an ' +
                        f'ArbitraryStartChecker does not use a start value; ' +
                        f'it considers an arbitrary start state.')

    def _register_var_no_start_state(self, name: str, crdt: Crdt) -> EVar:
        # Ensure that variable names are unique.
        assert name not in self.crdt_env, (name, self.crdt_env)
        assert name not in self.type_env, (name, self.type_env)

        typ = crdt.to_type()
        self.crdt_env[name] = crdt
        self.type_env[name] = typ

        var = ast.EVar(name)
        var.typ = typ
        return var

    def int_max(self, name: str, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CIntMax())

    def int_min(self, name: str, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CIntMin())

    def bool_or(self, name: str, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CBoolOr())

    def bool_and(self, name: str, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CBoolAnd())

    def tuple2(self, name: str, a: Crdt, b: Crdt, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CTuple2(a, b))

    def set_union(self, name: str, a: Type, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CSetUnion(a))

    def set_intersect(self, name: str, a: Type, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CSetIntersect(a))

    def map(self, name: str, a: Type, b: Crdt, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.CMap(a, b))

    def option(self, name: str, a: Crdt, val: Coercible) -> EVar:
        self._warn_if_not_none(val)
        return self._register_var_no_start_state(name, ast.COption(a))

    def add_transaction(self, name: str, txn: Transaction) -> None:
        assert name not in self.transactions, (name, self.transactions)
        txn = typecheck.typecheck_txn(txn, self.type_env)
        self.transactions[name] = txn

    def add_invariant(self, name: str, inv: Invariant) -> None:
        assert name not in self.invariants, (name, self.invariants)
        inv = typecheck.typecheck_invariant(inv, self.type_env)
        self.invariants[name] = inv
