from copy import deepcopy
from typing import Any, Dict

from . import ast
from .envs import CrdtEnv, ValEnv

def eval_expr(e: ast.Expr, env: ValEnv) -> Any:
    """
    >>> from .typecheck import typecheck_expr
    >>> from .ast import *
    >>> tenv = {'x': TInt()}
    >>> venv = {'x': 2}
    >>> e = EIntAdd(EInt(1), EVar('x'))
    >>> e = typecheck_expr(e, tenv)
    >>> print(e)
    (1 + x)
    >>> eval_expr(e, venv)
    3
    """
    if isinstance(e, ast.EVar):
        assert e.x in env, (e.x, env)
        return env[e.x]
    elif isinstance(e, ast.EInt):
        return e.x
    elif isinstance(e, ast.EBool):
        return e.x
    elif isinstance(e, ast.ETuple2):
        return (eval_expr(e.a, env), eval_expr(e.b, env))
    elif isinstance(e, ast.EEmptySet):
        return set()
    elif isinstance(e, ast.ESet):
        return {eval_expr(x, env) for x in e.xs}
    elif isinstance(e, ast.EEmptyMap):
        return dict()
    elif isinstance(e, ast.EMap):
        return {eval_expr(k, env): eval_expr(v, env) for k, v in e.kvs.items()}
    elif isinstance(e, ast.ENone):
        return None
    elif isinstance(e, ast.ESome):
        return eval_expr(e.x, env)
    elif isinstance(e, ast.EBoolNot):
        return not eval_expr(e.x, env)
    elif isinstance(e, ast.ETuple2First):
        return eval_expr(e.x, env)[0]
    elif isinstance(e, ast.ETuple2Second):
        return eval_expr(e.x, env)[1]
    elif isinstance(e, ast.EOptionIsNone):
        return eval_expr(e.x, env) is None
    elif isinstance(e, ast.EOptionIsSome):
        return eval_expr(e.x, env) is not None
    elif isinstance(e, ast.EOptionUnwrap):
        x = eval_expr(e.x, env)
        assert x is not None
        return x
    elif isinstance(e, ast.EIntAdd):
        return eval_expr(e.lhs, env) + eval_expr(e.rhs, env)
    elif isinstance(e, ast.EIntSub):
        return eval_expr(e.lhs, env) - eval_expr(e.rhs, env)
    elif isinstance(e, ast.EIntMul):
        return eval_expr(e.lhs, env) * eval_expr(e.rhs, env)
    elif isinstance(e, ast.EIntMin):
        return min(eval_expr(e.lhs, env), eval_expr(e.rhs, env))
    elif isinstance(e, ast.EIntMax):
        return max(eval_expr(e.lhs, env), eval_expr(e.rhs, env))
    elif isinstance(e, ast.EBoolOr):
        return eval_expr(e.lhs, env) or eval_expr(e.rhs, env)
    elif isinstance(e, ast.EBoolAnd):
        return eval_expr(e.lhs, env) and eval_expr(e.rhs, env)
    elif isinstance(e, ast.EBoolImpl):
        return not eval_expr(e.lhs, env) or eval_expr(e.rhs, env)
    elif isinstance(e, ast.ESetUnion):
        return eval_expr(e.lhs, env).union(eval_expr(e.rhs, env))
    elif isinstance(e, ast.ESetIntersect):
        return eval_expr(e.lhs, env).intersection(eval_expr(e.rhs, env))
    elif isinstance(e, ast.ESetDiff):
        return eval_expr(e.lhs, env).difference(eval_expr(e.rhs, env))
    elif isinstance(e, ast.ESetSubsetEq):
        return eval_expr(e.lhs, env).issubset(eval_expr(e.rhs, env))
    elif isinstance(e, ast.ESetContains):
        return eval_expr(e.rhs, env) in eval_expr(e.lhs, env)
    elif isinstance(e, ast.EMapContainsKey):
        return eval_expr(e.rhs, env) in eval_expr(e.lhs, env)
    elif isinstance(e, ast.EMapGet):
        return eval_expr(e.lhs, env)[eval_expr]
    elif isinstance(e, ast.EEq):
        return eval_expr(e.lhs, env) == (eval_expr(e.rhs, env))
    elif isinstance(e, ast.ENe):
        return eval_expr(e.lhs, env) != (eval_expr(e.rhs, env))
    elif isinstance(e, ast.EIntLt):
        return eval_expr(e.lhs, env) < (eval_expr(e.rhs, env))
    elif isinstance(e, ast.EIntLe):
        return eval_expr(e.lhs, env) <= (eval_expr(e.rhs, env))
    elif isinstance(e, ast.EIntGt):
        return eval_expr(e.lhs, env) > (eval_expr(e.rhs, env))
    elif isinstance(e, ast.EIntGe):
        return eval_expr(e.lhs, env) >= (eval_expr(e.rhs, env))
    elif isinstance(e, ast.EIntGe):
        return eval_expr(e.lhs, env) >= (eval_expr(e.rhs, env))
    elif isinstance(e, ast.EMapSet):
        m = eval_expr(e.a, env)
        m[eval_expr(e.b, env)] = eval_expr(e.c, env)
        return m
    elif isinstance(e, ast.EIf):
        b = eval_expr(e.a, env)
        if b:
            return eval_expr(e.b, env)
        else:
            return eval_expr(e.c, env)
    else:
        raise ValueError(f'Unkown expression {e}.')

def eval_stmt(s: ast.Stmt, env: ValEnv) -> ValEnv:
    if (isinstance(s, ast.SAssign)):
        assert s.x.x in env, (s.x, env)
        new_env = deepcopy(env)
        new_env[s.x.x] = eval_expr(s.e, env)
        return new_env
    else:
        raise ValueError(f'Unkown statement {s}.')

def eval_txn(txn: ast.Transaction, env: ValEnv) -> ValEnv:
    for s in txn:
        env = eval_stmt(s, env)
    return env

def eval_invariant(inv: ast.Invariant, env: ValEnv) -> ValEnv:
    return eval_expr(inv, env)

def _eval_join_vals(lhs: Any, rhs: Any, crdt: ast.Crdt) -> Any:
    if isinstance(crdt, ast.CIntMax):
        return max(lhs, rhs)
    elif isinstance(crdt, ast.CIntMin):
        return min(lhs, rhs)
    elif isinstance(crdt, ast.CBoolOr):
        return lhs or rhs
    elif isinstance(crdt, ast.CBoolAnd):
        return lhs and rhs
    elif isinstance(crdt, ast.CTuple2):
        a = _eval_join_vals(lhs[0], rhs[0], crdt.a)
        b = _eval_join_vals(lhs[1], rhs[1], crdt.b)
        return (a, b)
    elif isinstance(crdt, ast.CSetUnion):
        return lhs.union(rhs)
    elif isinstance(crdt, ast.CSetIntersect):
        return lhs.intersect(rhs)
    elif isinstance(crdt, ast.CMap):
        joined = lhs.copy()
        for k in rhs:
            if k in joined:
                joined[k] = _eval_join_vals(lhs[k], rhs[k], crdt.b)
            else:
                joined[k] = rhs[k]
        return joined
    elif isinstance(crdt, ast.COption):
        if lhs is None:
            return rhs
        if rhs is None:
            return lhs
        else:
            return _eval_join_vals(lhs, rhs, crdt.a)
    else:
        raise ValueError(f'Unrecognized CRDT {crdt}.')

def eval_join(lhs: ValEnv, rhs: ValEnv, cenv: CrdtEnv) -> ValEnv:
    assert lhs.keys() == rhs.keys() == cenv.keys(), (lhs, rhs, cenv)
    joined_env: ValEnv = dict()
    for v in lhs:
        joined_env[v] = _eval_join_vals(lhs[v], rhs[v], cenv[v])
    return joined_env
