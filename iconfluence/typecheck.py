from typing import cast, Dict, Optional, Union
from copy import deepcopy

from . import ast

TypeEnv = Dict[str, ast.Type]

class _TypecheckException(Exception):
    pass

def _assert(b: bool, msg: str) -> None:
    if not b:
        raise _TypecheckException(msg)

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
    elif isinstance(e, ast.ESet):
        _assert(len(e.xs) >= 0, 'Illegal empty set found.')
        types = {_typecheck_expr(x, env).typ for x in e.xs}
        _assert(len(types) == 1, f'Set with multiple types: {types}.')
        e.typ = ast.TSet(list(types)[0])
    elif isinstance(e, ast.EMap):
        _assert(len(e.kvs) >= 0, 'Illegal empty map found.')
        key_types = {_typecheck_expr(k, env).typ for k in e.kvs.keys()}
        value_types = {_typecheck_expr(v, env).typ for v in e.kvs.values()}
        _assert(len(key_types) == 1,
                f'Map with multiple key types: {key_types}.')
        _assert(len(value_types) == 1,
                f'Map with multiple value types: {value_types}.')
        e.typ = ast.TMap(list(key_types)[0], list(value_types)[0])
    elif isinstance(e, ast.ENone):
        e.typ = ast.TOption(e.t)
    elif isinstance(e, ast.ESome):
        typ = _typecheck_expr(e.x, env).typ
        e.typ = ast.TOption(typ)
    elif isinstance(e, ast.ETuple2First):
        typ = _typecheck_expr(e.x, env).typ
        _assert(isinstance(typ, ast.TTuple2), f'Invalid argument {e}.')
        e.typ = cast(ast.TTuple2, typ).a
    elif isinstance(e, ast.ETuple2Second):
        typ = _typecheck_expr(e.x, env).typ
        _assert(isinstance(typ, ast.TTuple2), f'Invalid argument {e}.')
        e.typ = cast(ast.TTuple2, typ).b
    elif (isinstance(e, ast.EOptionIsNone) or
          isinstance(e, ast.EOptionIsSome)):
        typ = _typecheck_expr(e.x, env).typ
        _assert(isinstance(typ, ast.TOption), 'Ill typed operand {e.x}.')
        e.typ = ast.TBool()
    elif isinstance(e, ast.EOptionUnwrap):
        typ = _typecheck_expr(e.x, env).typ
        _assert(isinstance(typ, ast.TOption), 'Ill typed operand {e.x}.')
        e.typ = cast(ast.TOption, typ).a
    elif (isinstance(e, ast.EIntAdd) or
          isinstance(e, ast.EIntSub) or
          isinstance(e, ast.EIntMul)):
        _assert(_typecheck_expr(e.lhs, env).typ == ast.TInt(),
                f'Ill typed operand {e.lhs}.')
        _assert(_typecheck_expr(e.rhs, env).typ == ast.TInt(),
                f'Ill typed operand {e.rhs}.')
        e.typ = ast.TInt()
    elif (isinstance(e, ast.EBoolOr) or
          isinstance(e, ast.EBoolAnd) or
          isinstance(e, ast.EBoolImpl)):
        _assert(_typecheck_expr(e.lhs, env).typ == ast.TBool(),
                f'Ill typed operand {e.lhs}.')
        _assert(_typecheck_expr(e.rhs, env).typ == ast.TBool(),
                f'Ill typed operand {e.rhs}.')
        e.typ = ast.TBool()
    elif (isinstance(e, ast.ESetUnion) or
          isinstance(e, ast.ESetIntersect) or
          isinstance(e, ast.ESetDiff)):
        _assert(isinstance(_typecheck_expr(e.lhs, env).typ, ast.TSet),
                f'Ill typed operand {e.lhs}.')
        _assert(isinstance(_typecheck_expr(e.rhs, env).typ, ast.TSet),
                f'Ill typed operand {e.rhs}.')
        _assert(e.lhs.typ == e.rhs.typ,
                f'Mismatched types {e.lhs.typ} and {e.rhs.typ}.')
        e.typ = e.lhs.typ
    elif isinstance(e, ast.ESetContains):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        _assert(isinstance(lhs_typ, ast.TSet), f'Ill typed operand {e.lhs}.')
        lhs_typ = cast(ast.TSet, lhs_typ)
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        _assert(lhs_typ.a == rhs_typ, f'Ill typed operand {e.rhs}.')
        e.typ = ast.TBool()
    elif isinstance(e, ast.EMapContainsKey):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        _assert(isinstance(lhs_typ, ast.TMap), f'Ill typed operand {e.lhs}.')
        lhs_typ = cast(ast.TMap, lhs_typ)
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        _assert(lhs_typ.a == rhs_typ, f'Ill typed operand {e.rhs}.')
        e.typ = ast.TBool()
    elif isinstance(e, ast.EMapGet):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        _assert(isinstance(lhs_typ, ast.TMap), f'Ill typed operand {e.lhs}.')
        lhs_typ = cast(ast.TMap, lhs_typ)
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        _assert(lhs_typ.a == rhs_typ, f'Ill typed operand {e.rhs}.')
        e.typ = lhs_typ.b
    elif (isinstance(e, ast.EEq) or isinstance(e, ast.ENe)):
        lhs_typ = _typecheck_expr(e.lhs, env).typ
        rhs_typ = _typecheck_expr(e.rhs, env).typ
        _assert(lhs_typ == rhs_typ,
                f'Mismatched types {e.lhs.typ} and {e.rhs.typ}.')
        e.typ = ast.TBool()
    elif (isinstance(e, ast.EIntLt) or
          isinstance(e, ast.EIntLe) or
          isinstance(e, ast.EIntGt) or
          isinstance(e, ast.EIntGe)):
        _assert(_typecheck_expr(e.lhs, env).typ == ast.TInt(),
                f'Ill typed operand {e.lhs}.')
        _assert(_typecheck_expr(e.rhs, env).typ == ast.TInt(),
                f'Ill typed operand {e.rhs}.')
        e.typ = ast.TBool()
    elif isinstance(e, ast.EMapSet):
        map_typ = _typecheck_expr(e.a, env).typ
        _assert(isinstance(map_typ, ast.TMap), f'Ill typed operand {e.a}.')
        map_typ = cast(ast.TMap, map_typ)
        k_typ = _typecheck_expr(e.b, env).typ
        _assert(map_typ.a == k_typ, f'Ill typed operand {e.b}.')
        v_typ = _typecheck_expr(e.c, env).typ
        _assert(map_typ.b == v_typ, f'Ill typed operand {e.c}.')
        e.typ = map_typ
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
    return _typecheck_expr(inv, env)

def typecheck_invariant(inv: ast.Invariant, env: TypeEnv) -> ast.Invariant:
    return typecheck_expr(inv, env)
