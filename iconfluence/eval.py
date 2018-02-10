from copy import deepcopy
from typing import Any, Dict

from . import ast

ValEnv = Dict[str, Any]

def eval_expr(e: ast.Expr, env: ValEnv) -> Any:
    if isinstance(e, ast.EVar):
        assert e.x in env, (e.x, env)
        return env[e.x]
    elif isinstance(e, ast.EInt):
        return e.x
    elif isinstance(e, ast.EBool):
        return e.x
    elif isinstance(e, ast.ETuple2):
        return (e.a, e.b)
    elif isinstance(e, ast.ESet):
        return {eval_expr(x, env) for x in e.xs}
    elif isinstance(e, ast.ETuple2First):
        return eval_expr(e, env)[0]
    elif isinstance(e, ast.ETuple2Second):
        return eval_expr(e, env)[1]
    elif isinstance(e, ast.EIntAdd):
        return eval_expr(e.lhs, env) + eval_expr(e.rhs, env)
    elif isinstance(e, ast.EIntSub):
        return eval_expr(e.lhs, env) - eval_expr(e.rhs, env)
    elif isinstance(e, ast.EIntMul):
        return eval_expr(e.lhs, env) * eval_expr(e.rhs, env)
    elif isinstance(e, ast.EBoolOr):
        return eval_expr(e.lhs, env) or eval_expr(e.rhs, env)
    elif isinstance(e, ast.EBoolAnd):
        return eval_expr(e.lhs, env) and eval_expr(e.rhs, env)
    elif isinstance(e, ast.EBoolImpl):
        return not eval_expr(e.lhs, env) or eval_expr(e.rhs, env)
    elif isinstance(e, ast.EBoolImpl):
        return not eval_expr(e.lhs, env) or eval_expr(e.rhs, env)
    elif isinstance(e, ast.ESetUnion):
        return eval_expr(e.lhs, env).union(eval_expr(e.rhs, env))
    elif isinstance(e, ast.ESetIntersect):
        return eval_expr(e.lhs, env).intersection(eval_expr(e.rhs, env))
    elif isinstance(e, ast.ESetDiff):
        return eval_expr(e.lhs, env).difference(eval_expr(e.rhs, env))
    elif isinstance(e, ast.ESetContains):
        return eval_expr(e.rhs, env) in eval_expr(e.lhs, env)
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
