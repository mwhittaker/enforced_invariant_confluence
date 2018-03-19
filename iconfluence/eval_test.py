from typing import Any, Dict, List, Tuple
import unittest

from .ast import *
from .envs import TypeEnv, ValEnv
from .eval import *
from .typecheck import typecheck_expr

class TestEval(unittest.TestCase):
    def test_eval_expr(self) -> None:
        venv: ValEnv = {'x': 42}
        tenv: TypeEnv = {'x': TInt()}
        tests: List[Tuple[Expr, Any]] = [
            (EVar('x'), 42),
            (coerce(1), 1),
            (coerce(True), True),
            (coerce((1, True)), (1, True)),
            (EEmptySet(TInt()), set()),
            (EEmptyMap(TInt(), TBool()), dict()),
            (coerce({1: True}), {1: True}),
            (ENone(TInt()), None),
            (ESome(1), 1),
            (EBoolNot(False), True),
            (coerce((1, True)).first(), 1),
            (coerce((1, True)).second(), True),
            (ESome(1).is_none(), False),
            (ESome(1).is_some(), True),
            (ESome(1).unwrap(), 1),
            (coerce(1) + 1, 2),
            (coerce(1) - 1, 0),
            (coerce(1) * 1, 1),
            (EIntMin(1, 2), 1),
            (EIntMax(1, 2), 2),
            (coerce(True) | False, True),
            (coerce(True) & False, False),
            (coerce(True) >> False, False),
            (coerce({1, 2}).union({3, 4}), {1, 2, 3, 4}),
            (coerce({1, 2}).intersect({3, 4}), set()),
            (coerce({1, 2}).diff({3, 4}), {1, 2}),
            (coerce({1, 2}).subseteq({3, 4}), False),
            (coerce({1, 2}).contains(3), False),
            (coerce({1: True}).contains_key(3), False),
            (coerce({1: True})[1], True),
            (coerce(1).eq(1), True),
            (coerce(1).ne(1), False),
            (coerce(1) <= 1, True),
            (coerce(1) < 1, False),
            (coerce(1) >= 1, True),
            (coerce(1) > 1, False),
            (EMapSet({1: True}, 1, False), {1: False}),
            (EIf(True, 1, 2), 1),
        ]
        for e, expected in tests:
            e = typecheck_expr(e, tenv)
            self.assertEqual(eval_expr(e, venv), expected, e)

    #  TODO(mwhittaker): Unit test other eval functions.

if __name__ == '__main__':
    unittest.main()
