from typing import Callable, List, TypeVar

from .. import ast
from .. import checker

A = TypeVar('A')

class EnsembleChecker(checker.Checker):
    def __init__(self, checkers: List[checker.Checker]) -> None:
        assert len(checkers) > 0
        self.checkers = checkers

    def _apply(self, f: Callable[[checker.Checker], A]) -> A:
        xs = {f(checker) for checker in self.checkers}
        assert len(xs) == 1, xs
        return list(xs)[0]

    def int_max(self, name: str) -> ast.EVar:
        return self._apply(lambda checker: checker.int_max(name))

    def int_min(self, name: str) -> ast.EVar:
        return self._apply(lambda checker: checker.int_min(name))

    def bool_or(self, name: str) -> ast.EVar:
        return self._apply(lambda checker: checker.bool_or(name))

    def bool_and(self, name: str) -> ast.EVar:
        return self._apply(lambda checker: checker.bool_and(name))

    def tuple2(self, name: str, a: ast.Crdt, b: ast.Crdt) -> ast.EVar:
        return self._apply(lambda checker: checker.tuple2(name, a, b))

    def set_union(self, name: str, a: ast.Type) -> ast.EVar:
        return self._apply(lambda checker: checker.set_union(name, a))

    def set_intersect(self, name: str, a: ast.Type) -> ast.EVar:
        return self._apply(lambda checker: checker.set_intersect(name, a))

    def option(self, name: str, a: ast.Crdt) -> ast.EVar:
        return self._apply(lambda checker: checker.option(name, a))

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
