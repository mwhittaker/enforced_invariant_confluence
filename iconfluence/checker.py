from enum import Enum
from typing import Any, Dict, Optional, Set

from . import ast
from . import typecheck
from .ast import Coercible, Crdt, Expr, Invariant, Transaction, Type
from .envs import CrdtEnv, TypeEnv, ValEnv
from .eval import eval_expr

class Decision(Enum):
    YES = "yes"
    NO = "no"
    UNKNOWN = "unknown"

class Checker:
    def __init__(self):
        self.crdt_env: CrdtEnv = dict()
        self.type_env: TypeEnv = dict()
        self.start_state: ValEnv = dict()
        self.transactions: Dict[str, Transaction] = dict()
        self.invariants: Dict[str, Invariant] = dict()

    def __str__(self):
       strings = []

       strings.append('State')
       for name in self.crdt_env:
           e = self.start_state[name]
           strings.append(f'  {name}: {self.crdt_env[name]} = {e}')

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

    def _register_var(self,
                      name: str,
                      crdt: Crdt,
                      coercible: Coercible) \
                      -> ast.EVar:
        # Ensure that variable names are unique.
        assert name not in self.crdt_env, (name, self.crdt_env)
        assert name not in self.type_env, (name, self.type_env)
        assert name not in self.start_state, (name, self.start_state)

        # Ensure that our initial start state is well-typed.
        typ = crdt.to_type()
        e = ast.coerce(coercible)
        e = typecheck.typecheck_expr(e, {})
        typecheck.assert_type_eq(e.typ, typ, e, e)

        self.crdt_env[name] = crdt
        self.type_env[name] = typ
        self.start_state[name] = eval_expr(e, {})
        return ast.EVar(name)

    # TODO(mwhittaker): Right now, temporary variables are joined together and
    # included when checking for properties like commutativity. Think about
    # whether this is right.

    def int_max(self, name: str, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CIntMax(), val)

    def int_min(self, name: str, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CIntMin(), val)

    def bool_or(self, name: str, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CBoolOr(), val)

    def bool_and(self, name: str, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CBoolAnd(), val)

    def tuple2(self, name: str, a: Crdt, b: Crdt, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CTuple2(a, b), val)

    def set_union(self, name: str, a: Type, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CSetUnion(a), val)

    def set_intersect(self, name: str, a: Type, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CSetIntersect(a), val)

    def map(self, name: str, a: Type, b: Crdt, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.CMap(a, b), val)

    def option(self, name: str, a: Crdt, val: Coercible) -> ast.EVar:
        return self._register_var(name, ast.COption(a), val)

    def add_transaction(self, name: str, txn: Transaction) -> None:
        assert name not in self.transactions, (name, self.transactions)
        txn = typecheck.typecheck_txn(txn, self.type_env)
        self.transactions[name] = txn

    def add_invariant(self, name: str, inv: Invariant) -> None:
        assert name not in self.invariants, (name, self.invariants)
        inv = typecheck.typecheck_invariant(inv, self.type_env)
        self.invariants[name] = inv

    def check_iconfluence(self) -> Decision:
        raise NotImplementedError()
