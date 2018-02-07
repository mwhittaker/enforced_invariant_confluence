from contextlib import contextmanager
from typing import Generator

from z3 import Solver

@contextmanager
def scoped(solver: Solver) -> Generator:
    solver.push()
    yield
    solver.pop()
