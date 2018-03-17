from contextlib import contextmanager
from typing import Generator

import z3

from ..checker import Decision

@contextmanager
def scoped(solver: z3.Solver) -> Generator:
    solver.push()
    yield
    solver.pop()

def result_to_decision(result: z3.CheckSatResult) -> Decision:
    if result == z3.sat:
        return Decision.NO
    elif result == z3.unsat:
        return Decision.YES
    elif result == z3.unknown:
        return Decision.UNKNOWN
    else:
        raise ValueError(f'Unkown result {result}.')
