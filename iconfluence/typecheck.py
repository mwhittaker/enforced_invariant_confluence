from typing import cast, Dict, Optional, Union
from copy import deepcopy

from . import ast

TypeEnv = Dict[str, ast.Type]

class _TypecheckException(Exception):
    pass

def _assert(b: bool, msg: str) -> None:
    if not b:
        raise _TypecheckException(msg)

def assert_type_eq(typ: ast.Type,
                   expected: ast.Type,
                   sube: ast.Expr,
                   e: Union[ast.Expr, ast.Stmt]) \
                   -> None:
    msg = (f"Expected '{sube}' to have type {expected} in '{e}', " +
           f"but it had type {typ}.")
    _assert(typ == expected, msg)

def assert_type_uniform(typ_a: ast.Type,
                        typ_b: ast.Type,
                        sub_a: ast.Expr,
                        sub_b: ast.Expr,
                        e: ast.Expr) \
                        -> None:
    msg = (f"Expected '{sub_a}' and '{sub_b}' to have the same type in " +
           f"'{e}', but '{sub_a}' had type '{typ_a}' and {sub_b} had type " +
           f"{typ_b}.")
    _assert(typ_a == typ_b, msg)

def assert_type_instance(typ: ast.Type,
                         expected: type,
                         sube: ast.Expr,
                         e: ast.Expr) \
                         -> None:
    msg = (f"Expected '{sube}' to have type {expected.__name__} in '{e}', " +
           f"but it had type {typ}.")
    _assert(isinstance(typ, expected), msg)

def _typecheck_expr(e: ast.Expr, env: Dict[str, ast.Type]) -> ast.Expr:
    if isinstance(e, ast.EVar):
        _assert(e.x in env, f'Unbound variable {e.x}.')
        e.typ = env[e.x]
    elif isinstance(e, ast.EInt):
        e.typ = ast.TInt()
    elif isinstance(e, ast.EBool):
        e.typ = ast.TBool()
    elif isinstance(e, ast.ETuple2):
        _typecheck_expr(e.a, env)
        _typecheck_expr(e.b, env)
        e.typ = ast.TTuple2(e.a.typ, e.b.typ)
    elif isinstance(e, ast.EEmptySet):
        e.typ = ast.TSet(e.t)
    elif isinstance(e, ast.ESet):
        _assert(len(e.xs) >= 0, 'Illegal empty set found.')
        types = {_typecheck_expr(x, env).typ for x in e.xs}
        _assert(len(types) == 1, f'Illegal set with multiple types: {types}.')
        e.typ = ast.TSet(list(types)[0])
    elif isinstance(e, ast.EEmptyMap):
        e.typ = ast.TMap(e.k, e.v)
    elif isinstance(e, ast.EMap):
        _assert(len(e.kvs) >= 0, 'Illegal empty map found.')
        key_types = {_typecheck_expr(k, env).typ for k in e.kvs.keys()}
        value_types = {_typecheck_expr(v, env).typ for v in e.kvs.values()}
        _assert(len(key_types) == 1,
                f'Illegal map with multiple key types: {key_types}.')
        _assert(len(value_types) == 1,
                f'Illegal map with multiple value types: {value_types}.')
        e.typ = ast.TMap(list(key_types)[0], list(value_types)[0])
    elif isinstance(e, ast.ENone):
        e.typ = ast.TOption(e.t)
    elif isinstance(e, ast.ESome):
        typ = _typecheck_expr(e.x, env).typ
        e.typ = ast.TOption(typ)
    elif isinstance(e, ast.ETuple2First):
        typ = _typecheck_expr(e.x, env).typ
        assert_type_instance(typ, ast.TTuple2, e.x, e)
        e.typ = cast(ast.TTuple2, typ).a
    elif isinstance(e, ast.ETuple2Second):
        typ = _typecheck_expr(e.x, env).typ
        assert_type_instance(typ, ast.TTuple2, e.x, e)
        e.typ = cast(ast.TTuple2, typ).b
    elif (isinstance(e, ast.EOptionIsNone) or
          isinstance(e, ast.EOptionIsSome)):
        typ = _typecheck_expr(e.x, env).typ
        assert_type_instance(typ, ast.TOption, e.x, e)
        e.typ = ast.TBool()
    elif isinstance(e, ast.EOptionUnwrap):
        typ = _typecheck_expr(e.x, env).typ
        assert_type_instance(typ, ast.TOption, e.x, e)
        e.typ = cast(ast.TOption, typ).a
    elif (isinstance(e, ast.EIntAdd) or
          isinstance(e, ast.EIntSub) or
          isinstance(e, ast.EIntMul) or
          isinstance(e, ast.EIntMin) or
          isinstance(e, ast.EIntMax)):
        assert_type_eq(_typecheck_expr(e.lhs, env).typ, ast.TInt(), e.lhs, e)
        assert_type_eq(_typecheck_expr(e.rhs, env).typ, ast.TInt(), e.rhs, e)
        e.typ = ast.TInt()
    elif (isinstance(e, ast.EBoolOr) or
          isinstance(e, ast.EBoolAnd) or
          isinstance(e, ast.EBoolImpl)):
        assert_type_eq(_typecheck_expr(e.lhs, env).typ, ast.TBool(), e.lhs, e)
        assert_type_eq(_typecheck_expr(e.rhs, env).typ, ast.TBool(), e.rhs, e)
        e.typ = ast.TBool()
    elif (isinstance(e, ast.ESetUnion) or
          isinstance(e, ast.ESetIntersect) or
          isinstance(e, ast.ESetDiff)):
        lhs = e.lhs
        rhs = e.rhs
        assert_type_instance(_typecheck_expr(lhs, env).typ, ast.TSet, lhs, e)
        assert_type_instance(_typecheck_expr(rhs, env).typ, ast.TSet, rhs, e)
        assert_type_uniform(lhs.typ, rhs.typ, lhs, rhs, e)
        e.typ = lhs.typ
    elif isinstance(e, ast.ESetSubsetEq):
        lhs = e.lhs
        rhs = e.rhs
        assert_type_instance(_typecheck_expr(lhs, env).typ, ast.TSet, lhs, e)
        assert_type_instance(_typecheck_expr(rhs, env).typ, ast.TSet, rhs, e)
        assert_type_uniform(lhs.typ, rhs.typ, lhs, rhs, e)
        e.typ = ast.TBool()
    elif isinstance(e, ast.ESetContains):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        assert_type_instance(lhs_typ, ast.TSet, e.lhs, e)
        lhs_typ = cast(ast.TSet, lhs_typ)
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        assert_type_eq(rhs_typ, lhs_typ.a, e.rhs, e)
        e.typ = ast.TBool()
    elif isinstance(e, ast.EMapContainsKey):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        assert_type_instance(lhs_typ, ast.TMap, e.lhs, e)
        lhs_typ = cast(ast.TMap, lhs_typ)
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        assert_type_eq(rhs_typ, lhs_typ.a, e.rhs, e)
        e.typ = ast.TBool()
    elif isinstance(e, ast.EMapGet):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        assert_type_instance(lhs_typ, ast.TMap, e.lhs, e)
        lhs_typ = cast(ast.TMap, lhs_typ)
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        assert_type_eq(rhs_typ, lhs_typ.a, e.rhs, e)
        e.typ = lhs_typ.b
    elif (isinstance(e, ast.EEq) or isinstance(e, ast.ENe)):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        assert_type_uniform(lhs_typ, rhs_typ, e.lhs, e.rhs, e)
        e.typ = ast.TBool()
    elif (isinstance(e, ast.EIntLt) or
          isinstance(e, ast.EIntLe) or
          isinstance(e, ast.EIntGt) or
          isinstance(e, ast.EIntGe)):
        assert_type_eq(_typecheck_expr(e.lhs, env).typ, ast.TInt(), e.lhs, e)
        assert_type_eq(_typecheck_expr(e.rhs, env).typ, ast.TInt(), e.rhs, e)
        e.typ = ast.TBool()
    elif isinstance(e, ast.EMapSet):
        map_typ = _typecheck_expr(e.a, env).typ
        assert_type_instance(map_typ, ast.TMap, e.a, e)
        map_typ = cast(ast.TMap, map_typ)
        k_typ = _typecheck_expr(e.b, env).typ
        assert_type_eq(k_typ, map_typ.a, e.b, e)
        v_typ = _typecheck_expr(e.c, env).typ
        assert_type_eq(v_typ, map_typ.b, e.c, e)
        e.typ = map_typ
    elif isinstance(e, ast.EIf):
        b_typ = _typecheck_expr(e.a, env).typ
        if_typ = _typecheck_expr(e.b, env).typ
        else_typ = _typecheck_expr(e.c, env).typ
        assert_type_eq(b_typ, ast.TBool(), e.a, e)
        assert_type_uniform(if_typ, else_typ, e.b, e.c, e)
        e.typ = if_typ
    else:
        raise ValueError(f'Unkown expression {e}.')

    return e

def typecheck_expr(e: ast.Expr, env: TypeEnv) -> ast.Expr:
    e_copy = deepcopy(e)
    return _typecheck_expr(e_copy, env)

def _typecheck_stmt(s: ast.Stmt, env: TypeEnv) -> ast.Stmt:
    if isinstance(s, ast.SAssign):
        _assert(s.x.x in env, f'Unbound variable {s.x}.')
        _typecheck_expr(s.e, env)
        assert_type_eq(s.e.typ, env[s.x.x], s.e, s)
        return s
    else:
        raise ValueError(f'Unkown statement {s}.')

    return s

def typecheck_stmt(s: ast.Stmt, env: TypeEnv) -> ast.Stmt:
    s_copy = deepcopy(s)
    return _typecheck_stmt(s_copy, env)

def _typecheck_txn(txn: ast.Transaction, env: TypeEnv) -> ast.Transaction:
    for s in txn:
        _typecheck_stmt(s, env)
    return txn

def typecheck_txn(txn: ast.Transaction, env: TypeEnv) -> ast.Transaction:
    txn_copy = deepcopy(txn)
    return _typecheck_txn(txn_copy, env)

def _typecheck_invariant(inv: ast.Invariant, env: TypeEnv) -> ast.Invariant:
    inv = _typecheck_expr(inv, env)
    assert_type_eq(inv.typ, ast.TBool(), inv, inv)
    return inv

def typecheck_invariant(inv: ast.Invariant, env: TypeEnv) -> ast.Invariant:
    inv = typecheck_expr(inv, env)
    assert_type_eq(inv.typ, ast.TBool(), inv, inv)
    return inv
