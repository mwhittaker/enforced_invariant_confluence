from typing import Dict, List, Tuple
import unittest

import z3

from . import z3_checker
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
        self.assertEqual(len(xs), len(ys), f'{xs} != {ys}')
        for x, y in zip(xs, ys):
            self.assert_z3_expr_equal(x, y)

    def test_type_to_z3(self) -> None:
        test_cases: List[Tuple[ast.Type, z3.SortRef]] = [
            (Int(), z3.IntSort()),
            (Bool(), z3.BoolSort()),
            (Set(Int()), z3.ArraySort(z3.IntSort(), z3.BoolSort())),
        ]

        for typ, sort in test_cases:
            self.assertEqual(sort, z3_checker._type_to_z3(typ))

        # Unit testing TTuple2 is a little bit tricky, since TTuple2 is
        # converted into a user-defined datatype.
        z3_tuple = z3_checker._type_to_z3(Pair(Int(), Bool()))
        self.assertEqual(z3_tuple.name(), 'Tuple2[Int, Bool]')
        self.assertEqual(z3_tuple.num_constructors(), 1)
        self.assertEqual(z3_tuple.constructor(0).name(),
                         'Tuple2[Int, Bool].tuple2')
        self.assertEqual(z3_tuple.constructor(0).arity(), 2)
        self.assertEqual(z3_tuple.accessor(0, 0).name(), 'Tuple2[Int, Bool].a')
        self.assertEqual(z3_tuple.accessor(0, 0).range(), z3.IntSort())
        self.assertEqual(z3_tuple.accessor(0, 1).name(), 'Tuple2[Int, Bool].b')
        self.assertEqual(z3_tuple.accessor(0, 1).range(), z3.BoolSort())

    def test_expr_to_z3(self) -> None:
        TupleIntBool = z3_checker._type_to_z3(Pair(Int(), Bool()))

        x_one = ast.EInt(1)
        x_two = ast.EInt(2)
        x_true = ast.EBool(True)
        x_false = ast.EBool(False)
        x_tuple = ast.ETuple2(x_one, x_true)
        x_set = ast.ESet({x_one})

        z3_one = z3.IntVal(1)
        z3_two = z3.IntVal(2)
        z3_true = z3.BoolVal(True)
        z3_false = z3.BoolVal(False)
        z3_tuple = TupleIntBool.constructor(0)(z3_one, z3_true)
        z3_set0 = z3.Const('foo_0', z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        z3_set0 = z3.Store(z3_set0, z3_one, z3_true)
        z3_set1 = z3.Const('foo_1', z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        z3_set1 = z3.Store(z3_set1, z3_one, z3_true)
        z3_set2 = z3.Const('foo_2', z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        z3_set2 = z3.Store(z3_set2, z3_one, z3_true)
        z3_set3 = z3.Const('foo_3', z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        z3_set3 = z3.Store(z3_set3, z3_one, z3_true)

        and_ = z3.And(z3_true, z3_true).decl()
        or_ = z3.Or(z3_true, z3_true).decl()
        not_ = z3.Not(z3_true).decl()

        no_var_no_set_test_cases: List[Tuple[ast.Expr, z3.ExprRef]] = [
            (x_one, z3_one),
            (x_true, z3_true),
            (x_tuple, z3_tuple),
            (x_tuple.first(), TupleIntBool.accessor(0, 0)(z3_tuple)),
            (x_tuple.second(), TupleIntBool.accessor(0, 1)(z3_tuple)),
            (x_one + x_two, z3_one + z3_two),
            (x_one - x_two, z3_one - z3_two),
            (x_one * x_two, z3_one * z3_two),
            (x_true | x_false, z3.Or(z3_true, z3_false)),
            (x_true & x_false, z3.And(z3_true, z3_false)),
            (x_true >> x_false, z3.Implies(z3_true, z3_false)),
            (x_one.eq(x_two), z3_one == z3_two),
            (x_one.ne(x_two), z3_one != z3_two),
            (x_one < x_two, z3_one < z3_two),
            (x_one <= x_two, z3_one <= z3_two),
            (x_one > x_two, z3_one > z3_two),
            (x_one >= x_two, z3_one >= z3_two),
        ]

        for e, expected in no_var_no_set_test_cases:
            venv = VersionEnv(frozenset())
            tenv: Dict[str, ast.Type] = dict()
            fresh = FreshName('foo')

            e = typecheck_expr(e, tenv)
            z3_es, z3_e = z3_checker._expr_to_z3(e, venv, tenv, fresh)
            self.assertEqual(len(z3_es), 0)
            self.assert_z3_expr_equal(z3_e, expected)


        foo1_int = z3.Int('foo_1')
        foo3_int = z3.Int('foo_3')
        foo0_set = z3.Const('foo_0', z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        foo2_set = z3.Const('foo_2', z3.ArraySort(z3.IntSort(), z3.BoolSort()))
        forall_1 = z3.ForAll(
            foo1_int,
            z3.Select(foo0_set, foo1_int) == z3.BoolVal(False))
        forall_2 = z3.ForAll(
            foo3_int,
            z3.Select(foo2_set, foo3_int) == z3.BoolVal(False))

        set_test_cases: List[Tuple[ast.Expr, List[z3.ExprRef], z3.ExprRef]] = [
            (x_set,
             [forall_1],
             z3_set0),
            (x_set.union(x_set),
             [forall_1, forall_2],
             z3.Map(or_, z3_set0, z3_set2)),
            (x_set.intersect(x_set),
             [forall_1, forall_2],
             z3.Map(and_, z3_set0, z3_set2)),
            (x_set.diff(x_set),
             [forall_1, forall_2],
             z3.Map(and_, z3_set0, z3.Map(not_, z3_set2))),
            (x_set.contains(x_one),
             [forall_1],
             z3.Select(z3_set0, z3_one)),
        ]

        for e, expected_z3_es, expected_z3_e in set_test_cases:
            venv = VersionEnv(frozenset())
            tenv = dict()
            fresh = FreshName('foo')

            e = typecheck_expr(e, tenv)
            z3_es, z3_e = z3_checker._expr_to_z3(e, venv, tenv, fresh)
            self.assert_z3_exprs_equal(z3_es, expected_z3_es)
            self.assert_z3_expr_equal(z3_e, expected_z3_e)

        x = ast.EVar('x')
        y = ast.EVar('y')
        var_test_cases: List[Tuple[ast.Expr, z3.ExprRef]] = [
            (x, z3.Int('x')),
            (y, z3.Bool('y')),
            ((x + x >= x) | y,
             z3.Or(z3.Int('x') + z3.Int('x') >= z3.Int('x'), z3.Bool('y'))),
        ]

        for e, expected in var_test_cases:
            venv = VersionEnv(frozenset({'x', 'y'}))
            tenv = {'x': Int(), 'y': Bool()}
            fresh = FreshName()

            e = typecheck_expr(e, tenv)
            z3_es, z3_e = z3_checker._expr_to_z3(e, venv, tenv, fresh)
            self.assertEqual(len(z3_es), 0)
            self.assert_z3_expr_equal(z3_e, expected)

    def test_stmt_to_z3(self) -> None:
        x = ast.EVar('x')
        y = ast.EVar('y')
        z3_x = z3.Int('x')
        z3_y = z3.Int('y')
        z3_x1 = z3.Int('x_foo_1')
        z3_x2 = z3.Int('x_foo_2')
        stmt = x.assign((x + y) * x)
        venv = VersionEnv(frozenset({'x', 'y'}), suffix='foo')
        tenv: Dict[str, ast.Type] = {'x': Int(), 'y': Int()}
        fresh = FreshName()

        es, new_venv = z3_checker._stmt_to_z3(stmt, venv, tenv, fresh)
        self.assertEqual(len(es), 1)
        self.assert_z3_expr_equal(es[0], z3_x1 == (z3_x + z3_y) * z3_x)
        self.assertEqual(venv.get_name('x'), 'x')
        self.assertEqual(venv.get_name('y'), 'y')
        self.assertEqual(new_venv.get_name('x'), 'x_foo_1')
        self.assertEqual(new_venv.get_name('y'), 'y')

        es, new_venv = z3_checker._stmt_to_z3(stmt, new_venv, tenv, fresh)
        self.assertEqual(len(es), 1)
        self.assert_z3_expr_equal(es[0], z3_x2 == (z3_x1 + z3_y) * z3_x1)
        self.assertEqual(new_venv.get_name('x'), 'x_foo_2')
        self.assertEqual(new_venv.get_name('y'), 'y')

if __name__ == '__main__':
    unittest.main()
