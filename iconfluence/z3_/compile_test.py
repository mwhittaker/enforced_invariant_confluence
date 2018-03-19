from typing import Dict, List, Tuple
import unittest

import z3

from ..ast import *
from ..typecheck import typecheck_expr
from .compile import *
from .fresh_name import FreshName
from .version_env import VersionEnv

class TestCompile(unittest.TestCase):
    def test_compile_type(self) -> None:
        # Option.
        Option = compile_type(TOption(TInt()))
        self.assertEqual(Option.name(), 'Option[Int]')
        self.assertEqual(Option.num_constructors(), 2)
        none = Option.constructor(0)
        self.assertEqual(none.name(), 'Option[Int].none')
        self.assertEqual(none.arity(), 0)
        some = Option.constructor(1)
        self.assertEqual(some.name(), 'Option[Int].some')
        self.assertEqual(some.arity(), 1)
        self.assertEqual(some.domain(0), z3.IntSort())

        # Tuple2
        Tuple2 = compile_type(TTuple2(TInt(), TBool()))
        self.assertEqual(Tuple2.name(), 'Tuple2[Int, Bool]')
        self.assertEqual(Tuple2.num_constructors(), 1)
        tuple2 = Tuple2.constructor(0)
        self.assertEqual(tuple2.name(), 'Tuple2[Int, Bool].tuple2')
        self.assertEqual(tuple2.arity(), 2)
        self.assertEqual(tuple2.domain(0), z3.IntSort())
        self.assertEqual(tuple2.domain(1), z3.BoolSort())

        # Basic types.
        tests: List[Tuple[Type, z3.SortRef]] = [
            (TInt(), z3.IntSort()),
            (TBool(), z3.BoolSort()),
            (TSet(TInt()), z3.ArraySort(z3.IntSort(), z3.BoolSort())),
            (TMap(TBool(), TInt()), z3.ArraySort(z3.BoolSort(), Option)),
        ]
        for typ, sort in tests:
            self.assertEqual(compile_type(typ), sort, typ)

    def test_compile_expr(self) -> None:
        # TODO(mwhittaker): Implement more than simple smoke tests.
        venv = VersionEnv()
        tenv: TypeEnv = {'x': TInt()}
        fresh = FreshName()
        exprs: List[Expr] = [
            EVar('x'),
            coerce(1),
            coerce(True),
            coerce((1, True)),
            EEmptySet(TInt()),
            EEmptyMap(TInt(), TBool()),
            coerce({1: True}),
            ENone(TInt()),
            ESome(1),
            EBoolNot(False),
            coerce((1, True)).first(),
            coerce((1, True)).second(),
            ESome(1).is_none(),
            ESome(1).is_some(),
            ESome(1).unwrap(),
            coerce(1) + 1,
            coerce(1) - 1,
            coerce(1) * 1,
            EIntMin(1, 2),
            EIntMax(1, 2),
            coerce(True) | False,
            coerce(True) & False,
            coerce(True) >> False,
            coerce({1, 2}).union({3, 4}),
            coerce({1, 2}).intersect({3, 4}),
            coerce({1, 2}).diff({3, 4}),
            coerce({1, 2}).subseteq({3, 4}),
            coerce({1, 2}).contains(3),
            coerce({1: True}).contains_key(3),
            coerce({1: True})[1],
            coerce(1).eq(1),
            coerce(1).ne(1),
            coerce(1) <= 1,
            coerce(1) < 1,
            coerce(1) >= 1,
            coerce(1) > 1,
            EMapSet({1: True}, 1, False),
            EIf(True, 1, 2),
        ]
        for e in exprs:
            e = typecheck_expr(e, tenv)
            compile_expr(e, venv, tenv, fresh)

    #  TODO(mwhittaker): Unit test other compilation functions.

if __name__ == '__main__':
    unittest.main()
