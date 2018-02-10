from enum import Enum
from typing import Dict, Optional

from . import ast
from . import typecheck

CrdtEnv = Dict[str, ast.Crdt]
TypeEnv = Dict[str, ast.Type]

class Decision(Enum):
    YES = "yes"
    NO = "no"
    UNKNOWN = "unknown"

class Checker:
    def __init__(self):
        self.crdt_env: CrdtEnv = dict()
        self.type_env: TypeEnv = dict()
        self.transactions: Dict[str, ast.Transaction] = dict()
        self.invariants: Dict[str, ast.Invariant] = dict()

    def _register_var(self, name: str, crdt: ast.Crdt) -> ast.EVar:
        assert name not in self.crdt_env
        assert name not in self.type_env
        self.crdt_env[name] = crdt
        self.type_env[name] = self.crdt_env[name].to_type()
        return ast.EVar(name)

    def _typecheck(self) -> None:
        for inv in self.invariants.values():
            typecheck._typecheck_invariant(inv, self.type_env)

        for txn in self.transactions.values():
            typecheck._typecheck_txn(txn, self.type_env)

    # TODO(mwhittaker): Right now, temporary variables are joined together and
    # included when checking for properties like commutativity. Think about
    # whether this is right.

    def int_max(self, name: str) -> ast.EVar:
        return self._register_var(name, ast.CIntMax())

    def int_min(self, name: str) -> ast.EVar:
        return self._register_var(name, ast.CIntMin())

    def bool_or(self, name: str) -> ast.EVar:
        return self._register_var(name, ast.CBoolOr())

    def bool_and(self, name: str) -> ast.EVar:
        return self._register_var(name, ast.CBoolAnd())

    def tuple2(self, name: str, a: ast.Crdt, b: ast.Crdt) -> ast.EVar:
        return self._register_var(name, ast.CTuple2(a, b))

    def set_union(self, name: str, a: ast.Crdt) -> ast.EVar:
        return self._register_var(name, ast.CSetUnion(a))

    def set_intersect(self, name: str, a: ast.Crdt) -> ast.EVar:
        return self._register_var(name, ast.CSetIntersect(a))

    def add_transaction(self, name: str, txn: ast.Transaction) -> None:
        assert name not in self.transactions
        self.transactions[name] = txn

    def add_invariant(self, name: str, inv: ast.Invariant) -> None:
        assert name not in self.invariants
        self.invariants[name] = inv

    def check_iconfluence(self) -> Decision:
        raise NotImplementedError()
