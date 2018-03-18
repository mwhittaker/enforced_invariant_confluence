from contextlib import contextmanager
from typing import Generator

import z3

@contextmanager
def scoped(solver: z3.Solver) -> Generator:
    solver.push()
    yield
    solver.pop()
