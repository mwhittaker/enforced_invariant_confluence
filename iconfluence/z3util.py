from contextlib import contextmanager

from z3 import Solver

@contextmanager
def scoped(solver: Solver) -> None:
    solver.push()
    yield
    solver.pop()
