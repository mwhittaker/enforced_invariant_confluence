from enum import Enum
from typing import Dict, Optional

from . import ast

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

    def _register_var(self, name: str, crdt: ast.Crdt) -> ast.EVar:
        assert name not in self.crdt_env
        assert name not in self.type_env
        self.crdt_env[name] = ast.CIntMax()
        self.type_env[name] = self.crdt_env[name].to_type()
        return ast.EVar(name)

    def int_max(self, name: str) -> ast.EVar:
        return self._register_var(name, ast.CIntMax())

    def int_min(self, name: str) -> ast.EVar:
        self._register_var(name, ast.CIntMin())

    def bool_or(self, name: str) -> ast.EVar:
        self._register_var(name, ast.CBoolOr())

    def bool_and(self, name: str) -> ast.EVar:
        self._register_var(name, ast.CBoolAnd())

    def tuple2(self, name: str, a: ast.Crdt, b: ast.Crdt) -> ast.EVar:
        self._register_var(name, ast.CTuple2(a, b))

    def set_union(self, name: str, a: ast.Crdt) -> ast.EVar:
        self._register_var(name, ast.CSetUnion(a))

    def set_intersect(self, name: str, a: ast.Crdt) -> ast.EVar:
        self._register_var(name, ast.CSetIntersect(a))

    def add_transaction(self, txn: ast.Transaction):
        raise NotImplementedError()

    def add_invariant(self, txn: ast.Expr):
        raise NotImplementedError()

    def check_iconfluence(self) -> Decision:
        raise NotImplementedError()
