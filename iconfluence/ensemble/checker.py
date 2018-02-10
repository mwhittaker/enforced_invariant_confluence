from typing import List

from .. import ast
from .. import checker

class EnsembleChecker(checker.Checker):
    def __init__(self, checkers: List[checker.Checker]) -> None:
        assert len(checkers) > 0
        self.checkers = checkers

    def int_max(self, name: str) -> ast.EVar:
        xs = [checker.int_max(name) for checker in self.checkers]
        return xs[0]

    def int_min(self, name: str) -> ast.EVar:
        xs = [checker.int_min(name) for checker in self.checkers]
        return xs[0]

    def bool_or(self, name: str) -> ast.EVar:
        xs = [checker.bool_or(name) for checker in self.checkers]
        return xs[0]

    def bool_and(self, name: str) -> ast.EVar:
        xs = [checker.bool_and(name) for checker in self.checkers]
        return xs[0]

    def tuple2(self, name: str, a: ast.Crdt, b: ast.Crdt) -> ast.EVar:
        xs = [checker.tuple2(name, a, b) for checker in self.checkers]
        return xs[0]

    def set_union(self, name: str, a: ast.Crdt) -> ast.EVar:
        xs = [checker.set_union(name, a) for checker in self.checkers]
        return xs[0]

    def set_intersect(self, name: str, a: ast.Crdt) -> ast.EVar:
        xs = [checker.set_intersect(name, a) for checker in self.checkers]
        return xs[0]

    def add_transaction(self, name: str, txn: ast.Transaction) -> None:
        for checker in self.checkers:
            checker.add_transaction(name, txn)

    def add_invariant(self, name: str, inv: ast.Invariant) -> None:
        for checker in self.checkers:
            checker.add_invariant(name, inv)

    def check_iconfluence(self) -> checker.Decision:
        decisions = [checker.check_iconfluence() for checker in self.checkers]
        if checker.Decision.YES in decisions:
            assert checker.Decision.NO not in decisions
            return checker.Decision.YES
        if checker.Decision.NO in decisions:
            assert checker.Decision.YES not in decisions
            return checker.Decision.NO
        else:
            assert set(decisions) == {checker.Decision.UNKNOWN}
            return checker.Decision.UNKNOWN
