from typing import Dict, List, Tuple
import unittest

import z3

from . import checker
from .. import ast
from ..typecheck import typecheck_expr
from .fresh_name import FreshName
from .version_env import VersionEnv

Int = ast.TInt
Bool = ast.TBool
Pair = ast.TTuple2
Set = ast.TSet

class TestChecker(unittest.TestCase):
    def assert_z3_expr_equal(self, x: z3.ExprRef, y: z3.ExprRef) -> None:
        # Note that `x == y` returns a z3 expression comparing x and y.
        # `x.eq(y)` checks whether x and y are structurally the same.
        self.assertTrue(x.eq(y), f'{x} != {y}.')

    def assert_z3_exprs_equal(self,
                              xs: List[z3.ExprRef],
                              ys: List[z3.ExprRef]) \
                              -> None:
        self.assertEqual(len(xs), len(ys))
        for x, y in zip(xs, ys):
            self.assert_z3_expr_equal(x, y)

    def test_type_to_string(self) -> None:
        test_cases: List[Tuple[ast.Type, str]] = [
            (Int(), 'Int'),
            (Bool(), 'Bool'),
            (Pair(Int(), Int()), 'Tuple2[Int, Int]'),
            (Pair(Int(), Bool()), 'Tuple2[Int, Bool]'),
            (Set(Int()), 'Set[Int]'),
            (Set(Pair(Set(Bool()), Pair(Int(), Int()))),
             'Set[Tuple2[Set[Bool], Tuple2[Int, Int]]]'),
        ]
        for typ, s in test_cases:
            self.assertEqual(s, checker._type_to_string(typ))

    def test_type_to_z3(self) -> None:
        test_cases: List[Tuple[ast.Type, z3.SortRef]] = [
            (Int(), z3.IntSort()),
            (Bool(), z3.BoolSort()),
            (Set(Int()), z3.ArraySort(z3.IntSort(), z3.BoolSort())),
        ]

        for typ, sort in test_cases:
            self.assertEqual(sort, checker._type_to_z3(typ))

        # Unit testing TTuple2 is a little bit tricky, since TTuple2 is
        # converted into a user-defined datatype.
        z3_tuple = checker._type_to_z3(Pair(Int(), Bool()))
        self.assertEqual(z3_tuple.name(), 'Tuple2[Int, Bool]')
        self.assertEqual(z3_tuple.num_constructors(), 1)
        self.assertEqual(z3_tuple.constructor(0).name(), 'tuple2')
        self.assertEqual(z3_tuple.constructor(0).arity(), 2)
        self.assertEqual(z3_tuple.accessor(0, 0).name(), 'a')
        self.assertEqual(z3_tuple.accessor(0, 0).range(), z3.IntSort())
        self.assertEqual(z3_tuple.accessor(0, 1).name(), 'b')
        self.assertEqual(z3_tuple.accessor(0, 1).range(), z3.BoolSort())

    def test_expr_to_z3(self) -> None:
        TupleIntBool = checker._type_to_z3(Pair(Int(), Bool()))

        x_one = ast.EInt(1)
        x_two = ast.EInt(2)
        x_true = ast.EBool(True)
        x_false = ast.EBool(False)
        x_tuple = ast.ETuple2(x_one, x_true)
        x_set = ast.ESet({x_one})

        z3_one = z3.Int(1)
        z3_two = z3.Int(2)
        z3_true = z3.Bool(True)
        z3_false = z3.Bool(False)
        z3_tuple = TupleIntBool.tuple2(z3_one, z3_true)
        z3_set0 = z3.Const('_fresh_name_0',
                          z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        z3_set0 = z3.Store(z3_set0, z3_one, z3_true)
        z4_set0 = z3.Const('_fresh_name_1',
                          z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        z3_set1 = z3.Store(z4_set0, z3_one, z3_true)

        and_ = z3.And(z3_true, z3_true).decl()
        or_ = z3.Or(z3_true, z3_true).decl()
        not_ = z3.Not(z3_true).decl()

        var_free_test_cases: List[Tuple[ast.Expr, z3.ExprRef]] = [
            (x_one, z3_one),
            (x_true, z3_true),
            (x_tuple, z3_tuple),
            (x_set, z3_set0),
            (x_tuple[0], TupleIntBool.a(z3_tuple)),
            (x_tuple[1], TupleIntBool.b(z3_tuple)),
            (x_one + x_two, z3_one + z3_two),
            (x_one - x_two, z3_one - z3_two),
            (x_one * x_two, z3_one * z3_two),
            (x_true | x_false, z3.Or(z3_true, z3_false)),
            (x_true & x_false, z3.And(z3_true, z3_false)),
            (x_true >> x_false, z3.Implies(z3_true, z3_false)),
            (x_set.union(x_set), z3.Map(or_, z3_set0, z3_set1)),
            (x_set.intersect(x_set), z3.Map(and_, z3_set0, z3_set1)),
            (x_set.diff(x_set), z3.Map(and_, z3_set0, z3.Map(not_, z3_set1))),
            (x_one.eq(x_two), z3_one == z3_two),
            (x_one.ne(x_two), z3_one != z3_two),
            (x_one < x_two, z3_one < z3_two),
            (x_one <= x_two, z3_one <= z3_two),
            (x_one > x_two, z3_one > z3_two),
            (x_one >= x_two, z3_one >= z3_two),
        ]

        for e, expected in var_free_test_cases:
            venv = VersionEnv(frozenset())
            tenv: Dict[str, ast.Type] = dict()
            fresh = FreshName()

            e = typecheck_expr(e, tenv)
            z3_es, z3_e = checker._expr_to_z3(e, venv, tenv, fresh)
            self.assertEqual(len(z3_es), 0)
            self.assert_z3_expr_equal(z3_e, expected)

if __name__ == '__main__':
    unittest.main()
