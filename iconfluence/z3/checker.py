from typing import Any, Callable, Dict, List, Tuple
from functools import lru_cache

import z3

from .. import checker
from .. import ast
from .fresh_name import FreshName
from .version_env import VersionEnv
from .z3util import scoped

TypeEnv = Dict[str, ast.Type]

def _type_to_string(typ: ast.Type) -> str:
    if isinstance(typ, ast.TInt):
        return 'Int'
    elif isinstance(typ, ast.TBool):
        return 'Bool'
    elif isinstance(typ, ast.TTuple2):
        return f'Tuple2[{_type_to_string(typ.a)}, {_type_to_string(typ.b)}]'
    elif isinstance(typ, ast.TSet):
        return f'Set[{_type_to_string(typ.a)}]'
    else:
        raise ValueError(f'Unkown type {typ}.')

# Note we memoize this function to try and avoid registering the same datatype
# with z3 multiple times.
@lru_cache()
def _type_to_z3(typ: ast.Type) -> z3.SortRef:
    if isinstance(typ, ast.TInt):
        return z3.IntSort()
    elif isinstance(typ, ast.TBool):
        return z3.BoolSort()
    elif isinstance(typ, ast.TTuple2):
        a = _type_to_z3(typ.a)
        b = _type_to_z3(typ.b)
        Tuple2 = z3.Datatype(_type_to_string(typ))
        Tuple2.declare('tuple2', ('a', a), ('b', b))
        return Tuple2.create()
    elif isinstance(typ, ast.TSet):
        return z3.ArraySort(_type_to_z3(typ.a), z3.BoolSort())
    else:
        raise ValueError(f'Unkown type {typ}.')

def _expr_to_z3(e: ast.Expr,
                venv: VersionEnv,
                tenv: TypeEnv,
                fresh: FreshName) \
                -> Tuple[List[z3.ExprRef], z3.ExprRef]:
    def to_z3(e_: ast.Expr) -> Tuple[List[z3.ExprRef], z3.ExprRef]:
        return _expr_to_z3(e_, venv, tenv, fresh)

    def flat_app(lhs: ast.Expr,
                 rhs: ast.Expr,
                 f: Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]) \
                 -> Tuple[List[z3.ExprRef], z3.ExprRef]:
        es_lhs, lhs_z3 = to_z3(lhs)
        es_rhs, rhs_z3 = to_z3(rhs)
        return es_lhs + es_rhs, f(lhs_z3, rhs_z3)

    if isinstance(e, ast.EVar):
        assert e.x in tenv, (e.x, tenv)
        return [], z3.Const(e.x, _type_to_z3(tenv[e.x]))
    elif isinstance(e, ast.EInt):
        return [], z3.Int(e.x)
    elif isinstance(e, ast.EBool):
        return [], z3.Bool(e.x)
    elif isinstance(e, ast.ETuple2):
        Tuple2 = _type_to_z3(e.typ)
        return flat_app(e.a, e.b, lambda a, b: Tuple2.tuple2(a, b))
    elif isinstance(e, ast.ESet):
        es = []
        xs = z3.Const(fresh.get(), _type_to_z3(e.typ))
        for x in e.xs:
            x_es, x_z3 = to_z3(x)
            es += x_es
            xs = z3.Store(xs, x_z3, z3.Bool(True))
        return es, xs
    elif isinstance(e, ast.ETuple2First):
        Tuple2 = _type_to_z3(e.x.typ)
        t_es, t = to_z3(e.x)
        return t_es, Tuple2.a(t)
    elif isinstance(e, ast.ETuple2Second):
        Tuple2 = _type_to_z3(e.x.typ)
        t_es, t = to_z3(e.x)
        return t_es, Tuple2.b(t)
    elif isinstance(e, ast.EIntAdd):
        return flat_app(e.lhs, e.rhs, lambda l, r: l + r)
    elif isinstance(e, ast.EIntSub):
        return flat_app(e.lhs, e.rhs, lambda l, r: l - r)
    elif isinstance(e, ast.EIntMul):
        return flat_app(e.lhs, e.rhs, lambda l, r: l * r)
    elif isinstance(e, ast.EBoolOr):
        return flat_app(e.lhs, e.rhs, lambda l, r: z3.Or(l, r))
    elif isinstance(e, ast.EBoolAnd):
        return flat_app(e.lhs, e.rhs, lambda l, r: z3.And(l, r))
    elif isinstance(e, ast.EBoolImpl):
        return flat_app(e.lhs, e.rhs, lambda l, r: z3.Implies(l, r))
    elif isinstance(e, ast.ESetUnion):
        f = z3.Or(z3.Bool(True), z3.Bool(True)).decl()
        return flat_app(e.lhs, e.rhs, lambda l, r: z3.Map(f, l, r))
    elif isinstance(e, ast.ESetIntersect):
        f = z3.And(z3.Bool(True), z3.Bool(True)).decl()
        return flat_app(e.lhs, e.rhs, lambda l, r: z3.Map(f, l, r))
    elif isinstance(e, ast.ESetDiff):
        not_ = z3.Not(z3.Bool(True)).decl()
        and_ = z3.And(z3.Bool(True), z3.Bool(True)).decl()
        f = lambda l, r: z3.Map(and_, l, z3.Map(not_, r))
        return flat_app(e.lhs, e.rhs, f)
    elif isinstance(e, ast.EEq):
        return flat_app(e.lhs, e.rhs, lambda l, r: l == r)
    elif isinstance(e, ast.ENe):
        return flat_app(e.lhs, e.rhs, lambda l, r: l != r)
    elif isinstance(e, ast.EIntLt):
        return flat_app(e.lhs, e.rhs, lambda l, r: l < r)
    elif isinstance(e, ast.EIntLe):
        return flat_app(e.lhs, e.rhs, lambda l, r: l <= r)
    elif isinstance(e, ast.EIntGt):
        return flat_app(e.lhs, e.rhs, lambda l, r: l > r)
    elif isinstance(e, ast.EIntGe):
        return flat_app(e.lhs, e.rhs, lambda l, r: l >= r)
    else:
        raise ValueError(f'Unkown expression {e}.')


# env again
# expr to z3
# stmt to z3
# txn to z3

# need to compile expressoins into a set of statements potentially, with the
# vars of the variables returned or captured by env or something like that

# array literals will be challenging; need to compile to a bunch of stores
# pairs will be challenging

# multiple datatypes will make this harder

class Checker(checker.Checker):
    def check_iconfluence(self) -> checker.Decision:
        self._typecheck()

        solver = z3.Solver()
        for _, inv in self.invariants.items():
            print(f'inv = {inv}')
            with scoped(solver):
                es, e = _expr_to_z3(inv, VersionEnv(frozenset()), self.type_env, FreshName())
                for e_ in es:
                    print(f'e = {e_}')
                    solver.add(e_)
                print(f'e = {e}')
                solver.add(e)
                print(solver.sexpr())

        raise NotImplementedError()
