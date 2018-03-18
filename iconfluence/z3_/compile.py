from typing import cast, Any, Callable, Dict, List, Optional, Union, Tuple
from functools import lru_cache

from orderedset import OrderedSet
import z3

from .. import ast
from .. import checker
from .. import typecheck
from ..envs import CrdtEnv, TypeEnv
from .fresh_name import FreshName
from .version_env import VersionEnv
from .z3_util import scoped

@lru_cache()
def compile_type(typ: ast.Type) -> z3.SortRef:
    """
    Compile a type into a z3 sort. Primitive types like ints and bools are
    compiled directly into primitive z3 types. More complex types like arrays,
    maps, and options compile to a combination of arrays and algebraic data
    types.

    >>> compile_type(ast.TInt())
    Int
    >>> compile_type(ast.TBool())
    Bool

    Note that this function is memoized to avoid redundantly registering the
    same datatype with z3 multiple times.
    """
    if isinstance(typ, ast.TInt):
        return z3.IntSort()
    elif isinstance(typ, ast.TBool):
        return z3.BoolSort()
    elif isinstance(typ, ast.TTuple2):
        a = compile_type(typ.a)
        b = compile_type(typ.b)
        Tuple2 = z3.Datatype(str(typ))
        Tuple2.declare(f'{typ}.tuple2', (f'{typ}.a', a), (f'{typ}.b', b))
        return Tuple2.create()
    elif isinstance(typ, ast.TSet):
        return z3.ArraySort(compile_type(typ.a), z3.BoolSort())
    elif isinstance(typ, ast.TMap):
        key_sort = compile_type(typ.a)
        val_sort = compile_type(ast.TOption(typ.b))
        return z3.ArraySort(key_sort, val_sort)
    elif isinstance(typ, ast.TOption):
        Option = z3.Datatype(str(typ))
        Option.declare(f'{typ}.none')
        Option.declare(f'{typ}.some', (f'{typ}.x',  compile_type(typ.a)))
        return Option.create()
    else:
        raise ValueError(f'Unkown type {typ}.')

class Tuple2Sort:
    """
    A wrapper around the Tuple2 z3 sort that compile_type generates.

    >>> # Tuple2[Int, Bool]
    >>> typ = ast.TTuple2(ast.TInt(), ast.TBool())
    >>> sort = Tuple2Sort(compile_type(typ))
    >>> tuple2 = sort.tuple2(z3.IntVal(1), z3.BoolVal(True))
    >>> tuple2
    Tuple2[Int, Bool].tuple2(1, True)
    >>> z3.simplify(sort.a(tuple2))
    1
    >>> z3.simplify(sort.b(tuple2))
    True
    """
    def __init__(self, sort: z3.DatatypeSortRef) -> None:
        self.sort = sort

    def tuple2(self, a: z3.ExprRef, b: z3.ExprRef) -> z3.ExprRef:
        return self.sort.constructor(0)(a, b)

    def a(self, t: z3.ExprRef) -> z3.ExprRef:
        return self.sort.accessor(0, 0)(t)

    def b(self, t: z3.ExprRef) -> z3.ExprRef:
        return self.sort.accessor(0, 1)(t)

class OptionSort:
    """
    A wrapper around the Option z3 sort that compile_type generates.

    >>> # Option[Int]
    >>> typ = ast.TOption(ast.TInt())
    >>> sort = OptionSort(compile_type(typ))
    >>> sort.none()
    Option[Int].none
    >>> o = sort.some(z3.IntVal(1))
    >>> o
    Option[Int].some(1)
    >>> z3.simplify(sort.x(o))
    1
    """
    def __init__(self, sort: z3.DatatypeSortRef) -> None:
        self.sort = sort

    def is_none(self, o: z3.ExprRef) -> z3.ExprRef:
        return self.sort.recognizer(0)(o)

    def none(self) -> z3.ExprRef:
        return self.sort.constructor(0)()

    def is_some(self, o: z3.ExprRef) -> z3.ExprRef:
        return self.sort.recognizer(1)(o)

    def some(self, x: z3.ExprRef) -> z3.ExprRef:
        return self.sort.constructor(1)(x)

    def x(self, o: z3.ExprRef) -> z3.ExprRef:
        return self.sort.accessor(1, 0)(o)

def compile_var(x: ast.EVar, venv: VersionEnv, tenv: TypeEnv) -> z3.ExprRef:
    """
    TODO: Document.
    """
    assert x.x in tenv, (x.x, tenv)
    return z3.Const(venv.get_name(x.x), compile_type(tenv[x.x]))

@lru_cache()
def _compile_empty_set(typ: ast.TSet) -> Tuple[OrderedSet, z3.ExprRef]:
    """
    `_compile_empty_set(t)` compiles an empty set of type t. This function is
    seperated from `compile_expr` to reduce the number of compiled empty sets
    (which are quite frequent). It is memoized to avoid redundantly computing
    the same empty set.
    """
    set_sort = compile_type(typ)
    empty = z3.Const(f'{typ}.empty_set', set_sort)
    x = z3.Const(f'{typ}.empty_set_x', set_sort.domain())
    forall = z3.ForAll(x, z3.Select(empty, x) == z3.BoolVal(False))
    return OrderedSet([forall]), empty

@lru_cache()
def _compile_empty_map(typ: ast.TMap) -> Tuple[OrderedSet, z3.ExprRef]:
    """
    _compile_empty_map works like _compile_empty_set but for empty maps instead
    of empty sets.
    """
    map_sort = compile_type(typ)
    option_sort = OptionSort(map_sort.range())
    empty = z3.Const(f'{typ}.empty_map', map_sort)
    k = z3.Const(f'{typ}.empty_set_k', map_sort.domain())
    forall = z3.ForAll(k, z3.Select(empty, k) == option_sort.none())
    return OrderedSet([forall]), empty

def compile_expr(e: ast.Expr,
                 venv: VersionEnv,
                 tenv: TypeEnv,
                 fresh: FreshName) \
                 -> Tuple[OrderedSet, z3.ExprRef]:
    """
    Consider the expression `EInt(1) + EInt(2)`. This expressions compiles
    quite naturally to the z3 expression `IntVal(1) + IntVal(2)`. However, this
    is not the only way to compile the expression. We could also generate the
    following code:

        (declare-const lhs Int)
        (declare-const rhs Int)
        (assert (= lhs 1))
        (assert (= rhs 2))

    and return the expression `Int('lhs') + Int('rhs')`. compile_expr compiles
    an expression into a pair (ss, e) where ss is an ordered set of boolean
    expressions (e.g. `(= lhs 1)`) and e is the compiled expressions (e.g.
    `Int('lhs') + Int('rhs')`).

    >>> venv = VersionEnv()
    >>> tenv = {}
    >>> fresh = FreshName()
    >>> e = ast.EInt(1) + ast.EInt(2)
    >>> e = typecheck.typecheck_expr(e, tenv)
    >>> ss, e = compile_expr(e, venv, tenv, fresh)
    >>> ss
    OrderedSet()
    >>> e
    1 + 2
    """
    def compile_expr_(e: ast.Expr) -> Tuple[OrderedSet, z3.ExprRef]:
        return compile_expr(e, venv, tenv, fresh)

    def map1(e: ast.Expr,
             f: Callable[[z3.ExprRef], z3.ExprRef]) \
             -> Tuple[OrderedSet, z3.ExprRef]:
        zss, ze = compile_expr_(e)
        return zss, f(ze)

    def map2(lhs: ast.Expr,
             rhs: ast.Expr,
             f: Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]) \
             -> Tuple[OrderedSet, z3.ExprRef]:
        lhs_zss, lhs_ze = compile_expr_(lhs)
        rhs_zss, rhs_ze = compile_expr_(rhs)
        return lhs_zss | rhs_zss, f(lhs_ze, rhs_ze)

    def map3(a: ast.Expr,
             b: ast.Expr,
             c: ast.Expr,
             f: Callable[[z3.ExprRef, z3.ExprRef, z3.ExprRef], z3.ExprRef]) \
             -> Tuple[OrderedSet, z3.ExprRef]:
        a_zss, a_ze = compile_expr_(a)
        b_zss, b_ze = compile_expr_(b)
        c_zss, c_ze = compile_expr_(c)
        return a_zss | b_zss | c_zss, f(a_ze, b_ze, c_ze)

    if isinstance(e, ast.EVar):
        return OrderedSet([]), compile_var(e, venv, tenv)
    elif isinstance(e, ast.EInt):
        return OrderedSet([]), z3.IntVal(e.x)
    elif isinstance(e, ast.EBool):
        return OrderedSet([]), z3.BoolVal(e.x)
    elif isinstance(e, ast.ETuple2):
        Tuple2 = Tuple2Sort(compile_type(e.typ))
        return map2(e.a, e.b, Tuple2.tuple2)
    elif isinstance(e, ast.EEmptySet):
        # TODO(mwhittaker): We should make sure that the empty set forall can
        # be pulled out of any other foralls. It doens't need to be nested.
        set_typ = ast.TSet(e.t)
        return _compile_empty_set(set_typ)
    elif isinstance(e, ast.ESet):
        set_typ = cast(ast.TSet, e.typ)
        zss, ze = _compile_empty_set(set_typ)
        for x in sorted(e.xs):
            zss_, ze_ = compile_expr_(x)
            zss |= zss_
            ze = z3.Store(ze, ze_, z3.BoolVal(True))
        return zss, ze
    elif isinstance(e, ast.EEmptyMap):
        map_typ = ast.TMap(e.k, e.v)
        return _compile_empty_map(map_typ)
    elif isinstance(e, ast.EMap):
        map_typ = cast(ast.TMap, e.typ)
        map_sort = compile_type(map_typ)
        Option = OptionSort(map_sort.range())

        zss, ze = _compile_empty_map(map_typ)
        for k, v in sorted(e.kvs.items()):
            k_zss, k_ze = compile_expr_(k)
            v_zss, v_ze = compile_expr_(v)
            zss |= (k_zss | v_zss)
            ze = z3.Store(ze, k_ze, Option.some(v_ze))
        return zss, ze
    elif isinstance(e, ast.ENone):
        Option = OptionSort(compile_type(e.typ))
        return OrderedSet([]), Option.none()
    elif isinstance(e, ast.ESome):
        Option = OptionSort(compile_type(e.typ))
        return map1(e.x, Option.some)
    elif isinstance(e, ast.ETuple2First):
        Tuple2 = Tuple2Sort(compile_type(e.x.typ))
        return map1(e.x, Tuple2.a)
    elif isinstance(e, ast.ETuple2Second):
        Tuple2 = Tuple2Sort(compile_type(e.x.typ))
        return map1(e.x, Tuple2.b)
    elif isinstance(e, ast.EOptionIsNone):
        Option = OptionSort(compile_type(e.x.typ))
        return map1(e.x, Option.is_none)
    elif isinstance(e, ast.EOptionIsSome):
        Option = OptionSort(compile_type(e.x.typ))
        return map1(e.x, Option.is_some)
    elif isinstance(e, ast.EOptionUnwrap):
        Option = OptionSort(compile_type(e.x.typ))
        return map1(e.x, Option.x)
    elif isinstance(e, ast.EIntAdd):
        return map2(e.lhs, e.rhs, lambda l, r: l + r)
    elif isinstance(e, ast.EIntSub):
        return map2(e.lhs, e.rhs, lambda l, r: l - r)
    elif isinstance(e, ast.EIntMul):
        return map2(e.lhs, e.rhs, lambda l, r: l * r)
    elif isinstance(e, ast.EIntMin):
        return compile_expr_(ast.EIf(e.lhs <= e.rhs, e.lhs, e.rhs))
    elif isinstance(e, ast.EIntMax):
        return compile_expr_(ast.EIf(e.lhs >= e.rhs, e.lhs, e.rhs))
    elif isinstance(e, ast.EBoolOr):
        return map2(e.lhs, e.rhs, z3.Or)
    elif isinstance(e, ast.EBoolAnd):
        return map2(e.lhs, e.rhs, z3.And)
    elif isinstance(e, ast.EBoolImpl):
        return map2(e.lhs, e.rhs, z3.Implies)
    elif isinstance(e, ast.ESetUnion):
        or_ = z3.Or(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return map2(e.lhs, e.rhs, lambda l, r: z3.Map(or_, l, r))
    elif isinstance(e, ast.ESetIntersect):
        and_ = z3.And(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return map2(e.lhs, e.rhs, lambda l, r: z3.Map(and_, l, r))
    elif isinstance(e, ast.ESetDiff):
        not_ = z3.Not(z3.BoolVal(True)).decl()
        and_ = z3.And(z3.BoolVal(True), z3.BoolVal(True)).decl()
        f = lambda l, r: z3.Map(and_, l, z3.Map(not_, r))
        return map2(e.lhs, e.rhs, f)
    elif isinstance(e, ast.ESetSubsetEq):
        set_typ = cast(ast.TSet, e.lhs.typ)
        empty = typecheck.typecheck_expr(ast.EEmptySet(set_typ.a), {})
        return compile_expr_((e.lhs.diff(e.rhs)).eq(empty))
    elif isinstance(e, ast.ESetContains):
        return map2(e.lhs, e.rhs, z3.Select)
    elif isinstance(e, ast.EMapContainsKey):
        typ = cast(ast.TMap, e.lhs.typ)
        Option = OptionSort(compile_type(ast.TOption(typ.b)))
        return map2(e.lhs, e.rhs, lambda l, r: Option.is_some(z3.Select(l, r)))
    elif isinstance(e, ast.EMapGet):
        typ = cast(ast.TMap, e.lhs.typ)
        Option = OptionSort(compile_type(ast.TOption(typ.b)))
        return map2(e.lhs, e.rhs, lambda l, r: Option.x(z3.Select(l, r)))
    elif isinstance(e, ast.EEq):
        return map2(e.lhs, e.rhs, lambda l, r: l == r)
    elif isinstance(e, ast.ENe):
        return map2(e.lhs, e.rhs, lambda l, r: l != r)
    elif isinstance(e, ast.EIntLt):
        return map2(e.lhs, e.rhs, lambda l, r: l < r)
    elif isinstance(e, ast.EIntLe):
        return map2(e.lhs, e.rhs, lambda l, r: l <= r)
    elif isinstance(e, ast.EIntGt):
        return map2(e.lhs, e.rhs, lambda l, r: l > r)
    elif isinstance(e, ast.EIntGe):
        return map2(e.lhs, e.rhs, lambda l, r: l >= r)
    elif isinstance(e, ast.EMapSet):
        typ = cast(ast.TMap, e.typ)
        Option = OptionSort(compile_type(ast.TOption(typ.b)))
        return map3(e.a, e.b, e.c,
                    lambda a, b, c: z3.Store(a, b, Option.some(c)))
    elif isinstance(e, ast.EIf):
        return map3(e.a, e.b, e.c, z3.If)
    else:
        raise ValueError(f'Unkown expression {e}.')

def compile_stmt(stmt: ast.Stmt,
                 venv: VersionEnv,
                 tenv: TypeEnv,
                 fresh: FreshName) \
                 -> Tuple[OrderedSet, VersionEnv]:
    """
    TODO(mwhittaker): Document.
    """
    if isinstance(stmt, ast.SAssign):
        zss, ze = compile_expr(stmt.e, venv, tenv, fresh)
        venv = venv.assign(stmt.x.x)
        x = compile_var(stmt.x, venv, tenv)
        return zss | OrderedSet([x == ze]), venv
    else:
        raise ValueError(f'Unkown statement {stmt}.')

def compile_txn(txn: ast.Transaction,
                venv: VersionEnv,
                tenv: TypeEnv,
                fresh: FreshName) \
                -> Tuple[OrderedSet, VersionEnv]:
    """
    compile_txn compiles a transaction into a series of z3 boolean expressions
    and an updated version environment. It's best explained through an example.

    >>> x = ast.EVar('x')
    >>> y = ast.EVar('y')
    >>> z = ast.EVar('z')
    >>> txn = [
    ...     x.assign(1),
    ...     y.assign(x + 2),
    ...     z.assign(y * 2),
    ...     x.assign(z + z),
    ... ]
    >>> tenv = {v: ast.TInt() for v in ['x', 'y', 'z']}
    >>> venv = VersionEnv()
    >>> fresh = FreshName()
    >>> txn = [typecheck.typecheck_stmt(s, tenv) for s in txn]
    >>> ss, _ = compile_txn(txn, venv, tenv, fresh)
    >>> for s in ss:
    ...     print(s)
    1 == x_1
    y_1 == x_1 + 2
    z_1 == y_1*2
    x_2 == z_1 + z_1
    """
    zss: OrderedSet = OrderedSet([])
    for s in txn:
        s_zss, venv = compile_stmt(s, venv, tenv, fresh)
        zss |= s_zss
    return zss, venv

def _compile_z3_join(lhs: z3.ExprRef,
                     rhs: z3.ExprRef,
                     crdt: ast.Crdt,
                     fresh: FreshName) \
                     -> Tuple[OrderedSet, z3.ExprRef]:
    """
    TODO(mwhittaker): Document.
    """
    if isinstance(crdt, ast.CIntMax):
        return OrderedSet(), z3.If(lhs >= rhs, lhs, rhs)
    elif isinstance(crdt, ast.CIntMin):
        return OrderedSet(), z3.If(lhs <= rhs, lhs, rhs)
    elif isinstance(crdt, ast.CBoolOr):
        return OrderedSet(), z3.Or(lhs, rhs)
    elif isinstance(crdt, ast.CBoolAnd):
        return OrderedSet(), z3.And(lhs, rhs)
    elif isinstance(crdt, ast.CTuple2):
        Tuple2 = Tuple2Sort(compile_type(crdt.to_type()))
        a = Tuple2.a
        b = Tuple2.b
        a_zss, a_ze = _compile_z3_join(a(lhs), a(rhs), crdt.a, fresh)
        b_zss, b_ze = _compile_z3_join(b(lhs), b(rhs), crdt.b, fresh)
        return a_zss | b_zss, Tuple2.tuple2(a_ze, b_ze)
    elif isinstance(crdt, ast.CSetUnion):
        or_ = z3.Or(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return OrderedSet(), z3.Map(or_, lhs, rhs)
    elif isinstance(crdt, ast.CSetIntersect):
        and_ = z3.And(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return OrderedSet(), z3.Map(and_, lhs, rhs)
    elif isinstance(crdt, ast.CMap):
        typ = cast(ast.TMap, crdt.to_type())
        Option = compile_type(ast.TOption(typ.b))

        # TODO(mwhittaker): This function only has to be declared and foralled
        # once per type, not once per join.
        x = z3.Const(fresh.get(), Option)
        y = z3.Const(fresh.get(), Option)
        j_zss, j_ze = _compile_z3_join(x, y, ast.COption(crdt.b), fresh)
        f = z3.Function(fresh.get(), Option, Option, Option)
        forall = z3.ForAll([x, y], z3.And(*j_zss, f(x, y) == j_ze))
        return OrderedSet([forall]), z3.Map(f, lhs, rhs)
    elif isinstance(crdt, ast.COption):
        Option = OptionSort(compile_type(crdt.to_type()))
        x = Option.x
        j_zss, j_ze = _compile_z3_join(x(lhs), x(rhs), crdt.a, fresh)
        return (j_zss,
                z3.If(Option.is_none(lhs), rhs,
                z3.If(Option.is_none(rhs), lhs,
                Option.some(j_ze))))
    else:
        raise ValueError(f'Unkown CRDT {crdt}.')




# def _compile_join_expr(lhs: ast.Expr,
#                        rhs: ast.Expr,
#                        crdt: ast.Crdt,
#                        venv: VersionEnv,
#                        tenv: TypeEnv,
#                        fresh: FreshName) \
#                        -> Tuple[OrderedSet, z3.ExprRef]:
#     def _cje(lhs: ast.Expr,
#              rhs: ast.Expr,
#              crdt: ast.Crdt) \
#              -> Tuple[OrderedSet, z3.ExprRef]:
#         return _compile_join_expr(lhs, rhs, crdt, venv, tenv, fresh)
#
#     if isinstance(crdt, ast.CIntMax):
#         e: ast.Expr = ast.EIntMax(lhs, rhs)
#         e = typecheck.typecheck_expr(e, tenv)
#         return compile_expr(e, venv, tenv, fresh)
#     elif isinstance(crdt, ast.CIntMin):
#         e = typecheck.typecheck_expr(ast.EIntMin(lhs, rhs), tenv)
#         return compile_expr(e, venv, tenv, fresh)
#     elif isinstance(crdt, ast.CBoolOr):
#         e = typecheck.typecheck_expr(ast.EBoolOr(lhs, rhs), tenv)
#         return compile_expr(e, venv, tenv, fresh)
#     elif isinstance(crdt, ast.CBoolAnd):
#         e = typecheck.typecheck_expr(ast.EBoolAnd(lhs, rhs), tenv)
#         e = typecheck.typecheck_expr(e, tenv)
#         return compile_expr(e, venv, tenv, fresh)
#     elif isinstance(crdt, ast.CTuple2):
#         lhs_a = typecheck.typecheck_expr(lhs.first(), tenv)
#         lhs_b = typecheck.typecheck_expr(lhs.second(), tenv)
#         rhs_a = typecheck.typecheck_expr(rhs.first(), tenv)
#         rhs_b = typecheck.typecheck_expr(rhs.second(), tenv)
#         a_zss, a_ze = _cje(lhs_a, rhs_a, crdt.a)
#         b_zss, b_ze = _cje(lhs_b, rhs_b, crdt.b)
#
#         Tuple2 = Tuple2Sort(crdt.to_type())
#         return a_zss | b_zss, Tuple2.tuple2(a_ze, b_ze)
#     elif isinstance(crdt, ast.CSetUnion):
#         e = typecheck.typecheck_expr(lhs.union(rhs), tenv)
#         return compile_expr(e, venv, tenv, fresh)
#     elif isinstance(crdt, ast.CSetIntersect):
#         e = typecheck.typecheck_expr(lhs.intersect(rhs), tenv)
#         return compile_expr(e, venv, tenv, fresh)
#     elif isinstance(crdt, ast.CMap):
#
#         # Compile lhs and rhs.
#         lhs_zss, lhs_ze = compile_expr(lhs, venv, tenv, fresh)
#         rhs_zss, rhs_ze = compile_expr(rhs, venv, tenv, fresh)
#
#         # TODO(mwhittaker): This function only has to be declared and foralled
#         # once per type, not once per join.
#         typ = cast(ast.TMap, crdt.to_type())
#         Option = compile_type(ast.TOption(typ.b))
#         f = z3.Function(fresh.get(), Option, Option, Option)
#         x = z3.Const(fresh.get(), Option)
#         y = z3.Const(fresh.get(), Option)
#
#         _cje
#         zss, ze = _cje(x, y, crdt.a)
#
#         j_es, j = _compile_z3_join(ast.COption(crdt.b), x, y, fresh)
#
#         forall = z3.ForAll([x, y], z3.And(*j_es, f(x, y) == j))
#
#         return OrderedSet([forall]), z3.Map(f, lhs, rhs)
#     elif isinstance(crdt, ast.COption):
#         # Compile lhs and rhs.
#         lhs_zss, lhs_ze = compile_expr(lhs, venv, tenv, fresh)
#         rhs_zss, rhs_ze = compile_expr(rhs, venv, tenv, fresh)
#
#         # Compile lhs.unwrap() join rhs.unwrap().
#         lhs_e = typecheck.typecheck_expr(lhs.unwrap(), tenv)
#         rhs_e = typecheck.typecheck_expr(rhs.unwrap(), tenv)
#         zss, ze = _cje(lhs_e, rhs_e, crdt.a)
#
#         # Glue everything together.
#         Option = OptionSort(crdt.to_type())
#         ze = z3.If(Option.is_none(lhs_ze), rhs_ze,
#              z3.If(Option.is_none(rhs_ze), lhs_ze,
#              Option.some(ze)))
#         return lhs_zss | rhs_zss | zss, ze
#     else:
#         raise ValueError(f'Unkown CRDT {crdt}.')

def compile_join(lhs_venv: VersionEnv,
                 rhs_venv: VersionEnv,
                 joined_venv: VersionEnv,
                 cenv: CrdtEnv,
                 tenv: TypeEnv,
                 fresh: FreshName) \
                 -> Tuple[OrderedSet, VersionEnv]:
    """
    """
    assert cenv.keys() == tenv.keys(), (cenv, tenv)

    zss = OrderedSet()
    for (v, crdt) in cenv.items():
        x = typecheck.typecheck_expr(ast.EVar(v), tenv)
        x = cast(ast.EVar, x)

        lhs_ze = compile_var(x, lhs_venv, tenv)
        rhs_ze = compile_var(x, rhs_venv, tenv)
        v_zss, v_ze = _compile_z3_join(lhs_ze, rhs_ze, crdt, fresh)

        joined_venv = joined_venv.assign(v)
        zss |= v_zss
        zss.add(compile_var(x, joined_venv, tenv) == v_ze)

    return zss, joined_venv
