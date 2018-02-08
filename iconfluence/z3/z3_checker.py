from ..checker import Checker, Decision
from .. import ast

class Z3Checker(Checker):
    def add_transaction(self, txn: ast.Transaction):
        raise NotImplementedError()

    def add_invariant(self, txn: ast.Expr):
        raise NotImplementedError()

    def check_iconfluence(self) -> Decision:
        raise NotImplementedError()
