from typing import Any, Callable, Dict, List, Tuple
from functools import lru_cache

import z3
from termcolor import colored

from .. import checker
from .. import ast
from .fresh_name import FreshName
from .version_env import VersionEnv
from .z3util import scoped

CrdtEnv = Dict[str, ast.Crdt]
TypeEnv = Dict[str, ast.Type]

def _red(s: str) -> str:
    return colored(s, 'red')

def _green(s: str) -> str:
    return colored(s, 'green')

def _cyan(s: str) -> str:
    return colored(s, 'cyan')

def _result_to_decision(result: z3.CheckSatResult) -> checker.Decision:
    if result == z3.sat:
        return checker.Decision.NO
    elif result == z3.unsat:
        return checker.Decision.YES
    elif result == z3.unknown:
        return checker.Decision.UNKNOWN
    else:
        raise ValueError(f'Unkown result {result}.')

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

# We memoize this function to avoid redundantly registering the same dataype
# with z3 multiple times
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

def _var_to_z3(x: ast.EVar, venv: VersionEnv, tenv: TypeEnv) -> z3.ExprRef:
    assert x.x in tenv, (x.x, tenv)
    return z3.Const(venv.get_name(x.x), _type_to_z3(tenv[x.x]))

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
        return [], _var_to_z3(e, venv, tenv)
    elif isinstance(e, ast.EInt):
        return [], z3.Int(e.x)
    elif isinstance(e, ast.EBool):
        return [], z3.Bool(e.x)
    elif isinstance(e, ast.ETuple2):
        Tuple2 = _type_to_z3(e.typ)
        return flat_app(e.a, e.b, lambda a, b: Tuple2.tuple2(a, b))
    elif isinstance(e, ast.ESet):
        es: List[z3.ExprRef] = []
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

def _stmt_to_z3(stmt: ast.Stmt,
                venv: VersionEnv,
                tenv: TypeEnv,
                fresh: FreshName) \
                -> Tuple[List[z3.ExprRef], VersionEnv]:
    if isinstance(stmt, ast.SAssign):
        es, e = _expr_to_z3(stmt.e, venv, tenv, fresh)
        venv = venv.assign(stmt.x.x)
        x = _var_to_z3(stmt.x, venv, tenv)
        return es + [x == e], venv
    else:
        raise ValueError(f'Unkown statement {stmt}.')

def _txn_to_z3(txn: ast.Transaction,
               venv: VersionEnv,
               tenv: TypeEnv,
               fresh: FreshName) \
               -> Tuple[List[z3.ExprRef], VersionEnv]:
    es: List[z3.ExprRef] = []
    for s in txn:
        s_es, venv = _stmt_to_z3(s, venv, tenv, fresh)
        es += s_es
    return es, venv

def _apply_txn(solver: z3.Solver,
               txn: ast.Transaction,
               venv: VersionEnv,
               tenv: TypeEnv,
               fresh: FreshName) \
               -> VersionEnv:
    es, venv = _txn_to_z3(txn, venv, tenv, fresh)
    for e in es:
        solver.add(e)
    return venv

def _join_to_z3(crdt: ast.Crdt,
                lhs: ast.Expr,
                lhs_venv: VersionEnv,
                rhs: ast.Expr,
                rhs_venv: VersionEnv,
                tenv: TypeEnv,
                fresh: FreshName) \
                -> Tuple[List[z3.ExprRef], z3.ExprRef]:
    def flat_app(lhs: ast.Expr,
                 rhs: ast.Expr,
                 f: Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]) \
                 -> Tuple[List[z3.ExprRef], z3.ExprRef]:
        lhs_z3s, lhs_z3 = _expr_to_z3(lhs, lhs_venv, tenv, fresh)
        rhs_z3s, rhs_z3 = _expr_to_z3(rhs, rhs_venv, tenv, fresh)
        return lhs_z3s + rhs_z3s, f(lhs_z3, rhs_z3)

    if isinstance(crdt, ast.CIntMax):
        return flat_app(lhs, rhs, lambda l, r: z3.If(l >= r, l, r))
    elif isinstance(crdt, ast.CIntMin):
        return flat_app(lhs, rhs, lambda l, r: z3.If(l <= r, l, r))
    elif isinstance(crdt, ast.CBoolOr):
        return flat_app(lhs, rhs, lambda l, r: z3.Or(l, r))
    elif isinstance(crdt, ast.CBoolAnd):
        return flat_app(lhs, rhs, lambda l, r: z3.And(l, r))
    elif isinstance(crdt, ast.CTuple2):
        a_z3s, a_z3 = _join_to_z3(
            crdt.a,
            ast.ETuple2First(lhs),
            lhs_venv,
            ast.ETuple2First(rhs),
            rhs_venv,
            tenv,
            fresh)
        b_z3s, b_z3 = _join_to_z3(
            crdt.b,
            ast.ETuple2Second(lhs),
            lhs_venv,
            ast.ETuple2Second(rhs),
            rhs_venv,
            tenv,
            fresh)
        return a_z3s + b_z3s, _type_to_z3(crdt.to_type()).tuple2(a_z3, b_z3)
    elif isinstance(crdt, ast.CSetUnion):
        or_ = z3.Or(z3.Bool(True), z3.Bool(True)).decl()
        return flat_app(lhs, rhs, lambda l, r: z3.Map(or_, l, r))
    elif isinstance(crdt, ast.CSetIntersect):
        and_ = z3.And(z3.Bool(True), z3.Bool(True)).decl()
        return flat_app(lhs, rhs, lambda l, r: z3.Map(and_, l, r))
    else:
        raise ValueError(f'Unkown CRDT {crdt}.')

class Z3Checker(checker.Checker):
    def __init__(self, verbose: int = 0) -> None:
        checker.Checker.__init__(self)
        self.verbose = verbose

    def _vlog(self, s: str) -> None:
        # TODO(mwhittaker): Maybe use a logger instead of just printing.
        if self.verbose >= 1:
            print(s, end='')

    def _vvlog(self, s: str) -> None:
        # TODO(mwhittaker): Maybe use a logger instead of just printing.
        if self.verbose >= 2:
            print(s, end='')

    def _vlogline(self, s: str) -> None:
        self._vlog(s + '\n')

    def _vvlogline(self, s: str) -> None:
        self._vvlog(s + '\n')

    def _get_fresh_venv(self) -> VersionEnv:
        return VersionEnv(frozenset(self.type_env.keys()))

    def _venvs_equal(self, venv1: VersionEnv, venv2: VersionEnv) -> z3.ExprRef:
        conjuncts: List[z3.ExprRef] = []
        for x in self.type_env.keys():
            var = ast.EVar(x)
            x_1 = _var_to_z3(var, venv1, self.type_env)
            x_2 = _var_to_z3(var, venv2, self.type_env)
            conjuncts.append(x_1 == x_2)
        return z3.And(*conjuncts)

    def _venv_satisfies_invariants(self,
                                   venv: VersionEnv,
                                   fresh: FreshName) \
                                   -> Tuple[List[z3.ExprRef], z3.ExprRef]:
        es: List[z3.ExprRef] = []
        conjuncts: List[z3.ExprRef] = []
        for inv in self.invariants.values():
            inv_es, inv_e = _expr_to_z3(inv, venv, self.type_env, fresh)
            es += inv_es
            conjuncts.append(inv_e)
        return es, z3.And(*conjuncts)

    def _join_venvs(self,
                    solver: z3.Solver,
                    venv: VersionEnv,
                    venv1: VersionEnv,
                    venv2: VersionEnv,
                    fresh: FreshName) \
                    -> VersionEnv:
        for x in self.type_env.keys():
            es, e = _join_to_z3(
                self.crdt_env[x],
                ast.EVar(x),
                venv1,
                ast.EVar(x),
                venv2,
                self.type_env,
                fresh)
            for e_ in es:
                solver.add(e_)
            venv = venv.assign(x)
            solver.add(_var_to_z3(ast.EVar(x), venv, self.type_env) == e)
        return venv

    def _operations_commute(self,
                            solver: z3.Solver,
                            fresh: FreshName) \
                            -> checker.Decision:
        for t_name, t in self.transactions.items():
            for u_name, u in self.transactions.items():
                if t_name <= u_name:
                    continue

                with scoped(solver):
                    tenv = self.type_env
                    venv = self._get_fresh_venv()
                    t_venv = venv.with_suffix(f'{t_name}')
                    t_venv = _apply_txn(solver, t, t_venv, tenv, fresh)
                    u_venv = venv.with_suffix(f'{u_name}')
                    u_venv = _apply_txn(solver, u, u_venv, tenv, fresh)
                    tu_venv = u_venv.with_suffix(f'{t_name}_{u_name}')
                    tu_venv = _apply_txn(solver, t, tu_venv, tenv, fresh)
                    ut_venv = t_venv.with_suffix(f'{u_name}_{t_name}')
                    ut_venv = _apply_txn(solver, u, ut_venv, tenv, fresh)
                    solver.add(z3.Not(self._venvs_equal(tu_venv, ut_venv)))

                    # TODO(mwhittaker): Print out the transactions that don't
                    # commute along with an example showing that they don't
                    # commute.
                    self._vvlog(solver.sexpr())
                    decision = _result_to_decision(solver.check())
                    msg = f'{t_name} and {u_name} commute = {decision}'
                    self._vlogline(_red(msg))
                    if decision != checker.Decision.YES:
                        return decision
        return checker.Decision.YES

    def _join_is_apply(self,
                       solver: z3.Solver,
                       fresh: FreshName) \
                       -> checker.Decision:
        for t_name, t in self.transactions.items():
            for u_name, u in self.transactions.items():
                if t_name < u_name:
                    continue

                with scoped(solver):
                    tenv = self.type_env
                    venv = self._get_fresh_venv()
                    t_venv = venv.with_suffix(f'{t_name}')
                    t_venv = _apply_txn(solver, t, t_venv, tenv, fresh)
                    u_venv = venv.with_suffix(f'{u_name}')
                    u_venv = _apply_txn(solver, u, u_venv, tenv, fresh)
                    tu_venv = u_venv.with_suffix(f'{t_name}_{u_name}')
                    tu_venv = _apply_txn(solver, t, tu_venv, tenv, fresh)
                    joined_venv = venv.with_suffix(f'{t_name}_joined_{u_name}')
                    joined_venv = self._join_venvs(solver, joined_venv,
                                                   t_venv, u_venv, fresh)
                    solver.add(z3.Not(self._venvs_equal(tu_venv, joined_venv)))

                    # TODO(mwhittaker): Eliminate boilerplate.
                    self._vvlog(solver.sexpr())
                    decision = _result_to_decision(solver.check())
                    msg = f'{t_name} and {u_name} join is apply = {decision}'
                    self._vlogline(_green(msg))
                    if decision != checker.Decision.YES:
                        return decision
        return checker.Decision.YES

    def _one_di_confluent(self, solver: z3.Solver, fresh: FreshName) -> checker.Decision:
        # TODO(mwhittaker): We can turn this into a single call to z3 using
        # something like:
        #
        #   (assert (= x_t_1 ...))
        #   (assert (= x_u_1 ...))
        #   (assert (= x_v_1 ...))
        #   (assert (or (= x_left x_t_1) (= x_left x_u_1) (= x_left x_v_1)))
        #
        # It's unclear whether this would be better though.
        for t_name, t in self.transactions.items():
            for u_name, u in self.transactions.items():
                if t_name < u_name:
                    continue

                with scoped(solver):
                    tenv = self.type_env
                    venv = self._get_fresh_venv()
                    t_venv = venv.with_suffix(f'{t_name}')
                    t_venv = _apply_txn(solver, t, t_venv, tenv, fresh)
                    u_venv = venv.with_suffix(f'{u_name}')
                    u_venv = _apply_txn(solver, u, u_venv, tenv, fresh)
                    joined_venv = venv.with_suffix(f'{t_name}_joined_{u_name}')
                    joined_venv = self._join_venvs(solver, joined_venv,
                                                   t_venv, u_venv, fresh)

                    vsi = self._venv_satisfies_invariants
                    original_es, original_i = vsi(venv, fresh)
                    t_es, t_i = vsi(t_venv, fresh)
                    u_es, u_i = vsi(u_venv, fresh)
                    joined_es, joined_i = vsi(joined_venv, fresh)
                    solver.add(original_es)
                    solver.add(t_es)
                    solver.add(u_es)
                    solver.add(joined_es)
                    solver.add(original_i)
                    solver.add(t_i)
                    solver.add(u_i)
                    solver.add(z3.Not(joined_i))

                    # TODO(mwhittaker): Eliminate boilerplate.
                    self._vvlog(solver.sexpr())
                    decision = _result_to_decision(solver.check())
                    msg = f'{t_name} and {u_name} 1-DI-confluent = {decision}'
                    self._vlogline(_cyan(msg))
                    if decision != checker.Decision.YES:
                        return decision
        return checker.Decision.YES

    def check_iconfluence(self) -> checker.Decision:
        self._typecheck()
        if len(self.invariants) == 0:
            self._vlogline('There are no invariants, we are trivially iconfluent!')
            return checker.Decision.YES

        solver = z3.Solver()
        fresh = FreshName()
        operations_commute = self._operations_commute(solver, fresh)
        join_is_apply = self._join_is_apply(solver, fresh)
        one_di_confluent = self._one_di_confluent(solver, fresh)
        self._vlogline(_red(  f'operations_commute = {operations_commute}'))
        self._vlogline(_cyan( f'join_is_apply      = {join_is_apply}'))
        self._vlogline(_green(f'one_di_confluent   = {one_di_confluent}'))

        yes = checker.Decision.YES
        no = checker.Decision.NO
        unknown = checker.Decision.UNKNOWN
        if (operations_commute == yes and
            join_is_apply == yes and
            one_di_confluent == yes):
            return yes
        elif one_di_confluent == no:
            return no
        else:
            return unknown

        raise NotImplementedError()