from typing import cast, Any, Callable, Dict, List, Optional, Tuple
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
        Tuple2 = z3.Datatype(str(typ))
        Tuple2.declare(f'{typ}.tuple2', (f'{typ}.a', a), (f'{typ}.b', b))
        return Tuple2.create()
    elif isinstance(typ, ast.TSet):
        return z3.ArraySort(_type_to_z3(typ.a), z3.BoolSort())
    elif isinstance(typ, ast.TMap):
        key_sort = _type_to_z3(typ.a)
        val_sort = _type_to_z3(ast.TOption(typ.b))
        return z3.ArraySort(key_sort, val_sort)
    elif isinstance(typ, ast.TOption):
        Option = z3.Datatype(str(typ))
        Option.declare(f'{typ}.none')
        Option.declare(f'{typ}.some', (f'{typ}.x',  _type_to_z3(typ.a)))
        return Option.create()
    else:
        raise ValueError(f'Unkown type {typ}.')

def _tuple2_tuple2(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.constructor(0)

def _tuple2_a(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.accessor(0, 0)

def _tuple2_b(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.accessor(0, 1)

def _option_none(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.constructor(0)

def _option_some(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.constructor(1)

def _option_x(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.accessor(1, 0)

def _option_is_none(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.recognizer(0)

def _option_is_some(dt: z3.DatatypeSortRef) -> z3.FuncDeclRef:
    return dt.recognizer(1)

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

    def flat_app2(lhs: ast.Expr,
                  rhs: ast.Expr,
                  f: Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]) \
                  -> Tuple[List[z3.ExprRef], z3.ExprRef]:
        es_lhs, lhs_z3 = to_z3(lhs)
        es_rhs, rhs_z3 = to_z3(rhs)
        return es_lhs + es_rhs, f(lhs_z3, rhs_z3)

    def flat_app3(a: ast.Expr,
                  b: ast.Expr,
                  c: ast.Expr,
                  f: Callable[[z3.ExprRef, z3.ExprRef, z3.ExprRef],
                               z3.ExprRef]) \
                  -> Tuple[List[z3.ExprRef], z3.ExprRef]:
        a_z3s, a_z3 = to_z3(a)
        b_z3s, b_z3 = to_z3(b)
        c_z3s, c_z3 = to_z3(c)
        return a_z3s + b_z3s + c_z3s, f(a_z3, b_z3, c_z3)

    if isinstance(e, ast.EVar):
        return [], _var_to_z3(e, venv, tenv)
    elif isinstance(e, ast.EInt):
        return [], z3.IntVal(e.x)
    elif isinstance(e, ast.EBool):
        return [], z3.BoolVal(e.x)
    elif isinstance(e, ast.ETuple2):
        Tuple2 = _type_to_z3(e.typ)
        tuple2 = _tuple2_tuple2(Tuple2)
        return flat_app2(e.a, e.b, lambda a, b: tuple2(a, b))
    elif isinstance(e, ast.EEmptySet):
        xs = z3.Const(fresh.get(), _type_to_z3(e.typ))
        x = z3.Const(fresh.get(), _type_to_z3(cast(ast.TSet, e.typ).a))
        es = [z3.ForAll(x, z3.Select(xs, x) == z3.BoolVal(False))]
        return es, xs
    elif isinstance(e, ast.ESet):
        xs = z3.Const(fresh.get(), _type_to_z3(e.typ))
        x = z3.Const(fresh.get(), _type_to_z3(cast(ast.TSet, e.typ).a))
        es = [z3.ForAll(x, z3.Select(xs, x) == z3.BoolVal(False))]
        for x in e.xs:
            x_es, x_z3 = to_z3(x)
            es += x_es
            xs = z3.Store(xs, x_z3, z3.BoolVal(True))
        return es, xs
    elif isinstance(e, ast.EMap):
        typ = cast(ast.TMap, e.typ)
        kvs = z3.Const(fresh.get(), _type_to_z3(typ))
        k = z3.Const(fresh.get(), _type_to_z3(typ.a))
        Option = _type_to_z3(ast.TOption(typ.b))
        es = [z3.ForAll(k, z3.Select(kvs, k) == _option_none(Option)())]
        for k, v in e.kvs.items():
            k_es, k_z3 = to_z3(k)
            v_es, v_z3 = to_z3(v)
            es += (k_es + v_es)
            kvs = z3.Store(kvs, k_z3, _option_some(Option)(v_z3))
        return es, kvs
    elif isinstance(e, ast.ENone):
        Option = _type_to_z3(e.typ)
        return [], _option_none(Option)()
    elif isinstance(e, ast.ESome):
        Option = _type_to_z3(e.typ)
        z3_es, z3_e = to_z3(e.x)
        return z3_es, _option_some(Option)(z3_e)
    elif isinstance(e, ast.ETuple2First):
        Tuple2 = _type_to_z3(e.x.typ)
        t_es, t = to_z3(e.x)
        return t_es, _tuple2_a(Tuple2)(t)
    elif isinstance(e, ast.ETuple2Second):
        Tuple2 = _type_to_z3(e.x.typ)
        t_es, t = to_z3(e.x)
        return t_es, _tuple2_b(Tuple2)(t)
    elif isinstance(e, ast.EOptionIsNone):
        Option = _type_to_z3(e.x.typ)
        z3_es, z3_e = to_z3(e.x)
        return z3_es, _option_is_none(Option)(z3_e)
    elif isinstance(e, ast.EOptionIsSome):
        Option = _type_to_z3(e.x.typ)
        z3_es, z3_e = to_z3(e.x)
        return z3_es, _option_is_some(Option)(z3_e)
    elif isinstance(e, ast.EOptionUnwrap):
        Option = _type_to_z3(e.x.typ)
        z3_es, z3_e = to_z3(e.x)
        return z3_es, _option_x(Option)(z3_e)
    elif isinstance(e, ast.EIntAdd):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l + r)
    elif isinstance(e, ast.EIntSub):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l - r)
    elif isinstance(e, ast.EIntMul):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l * r)
    elif isinstance(e, ast.EBoolOr):
        return flat_app2(e.lhs, e.rhs, lambda l, r: z3.Or(l, r))
    elif isinstance(e, ast.EBoolAnd):
        return flat_app2(e.lhs, e.rhs, lambda l, r: z3.And(l, r))
    elif isinstance(e, ast.EBoolImpl):
        return flat_app2(e.lhs, e.rhs, lambda l, r: z3.Implies(l, r))
    elif isinstance(e, ast.ESetUnion):
        f = z3.Or(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return flat_app2(e.lhs, e.rhs, lambda l, r: z3.Map(f, l, r))
    elif isinstance(e, ast.ESetIntersect):
        f = z3.And(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return flat_app2(e.lhs, e.rhs, lambda l, r: z3.Map(f, l, r))
    elif isinstance(e, ast.ESetDiff):
        not_ = z3.Not(z3.BoolVal(True)).decl()
        and_ = z3.And(z3.BoolVal(True), z3.BoolVal(True)).decl()
        f = lambda l, r: z3.Map(and_, l, z3.Map(not_, r))
        return flat_app2(e.lhs, e.rhs, f)
    elif isinstance(e, ast.ESetContains):
        return flat_app2(e.lhs, e.rhs, lambda l, r: z3.Select(l, r))
    elif isinstance(e, ast.EMapContainsKey):
        typ = cast(ast.TMap, e.lhs.typ)
        Option = _type_to_z3(ast.TOption(typ.b))
        return flat_app2(e.lhs, e.rhs,
                        lambda l, r: _option_is_none(Option)(z3.Select(l, r)))
    elif isinstance(e, ast.EMapGet):
        typ = cast(ast.TMap, e.lhs.typ)
        Option = _type_to_z3(ast.TOption(typ.b))
        x = _option_x(Option)
        return flat_app2(e.lhs, e.rhs, lambda l, r: x(z3.Select(l, r)))
    elif isinstance(e, ast.EEq):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l == r)
    elif isinstance(e, ast.ENe):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l != r)
    elif isinstance(e, ast.EIntLt):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l < r)
    elif isinstance(e, ast.EIntLe):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l <= r)
    elif isinstance(e, ast.EIntGt):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l > r)
    elif isinstance(e, ast.EIntGe):
        return flat_app2(e.lhs, e.rhs, lambda l, r: l >= r)
    elif isinstance(e, ast.EMapSet):
        typ = cast(ast.TMap, e.typ)
        Option = _type_to_z3(ast.TOption(typ.b))
        some = _option_some(Option)
        return flat_app3(e.a, e.b, e.c,
                         lambda a, b, c: z3.Store(a, b, some(c)))
    elif isinstance(e, ast.EIf):
        return flat_app3(e.a, e.b, e.c, z3.If)
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

def _join_z3_to_z3(crdt: ast.Crdt,
                   lhs: z3.ExprRef,
                   rhs: z3.ExprRef,
                   fresh: FreshName) \
                   -> Tuple[List[z3.ExprRef], z3.ExprRef]:
    if isinstance(crdt, ast.CIntMax):
        return [], z3.If(lhs >= rhs, lhs, rhs)
    elif isinstance(crdt, ast.CIntMin):
        return [], z3.If(lhs <= rhs, lhs, rhs)
    elif isinstance(crdt, ast.CBoolOr):
        return [], z3.Or(lhs, rhs)
    elif isinstance(crdt, ast.CBoolAnd):
        return [], z3.And(lhs, rhs)
    elif isinstance(crdt, ast.CTuple2):
        Tuple2 = _type_to_z3(crdt.to_type())
        get_a = _tuple2_a(Tuple2)
        get_b = _tuple2_b(Tuple2)
        tuple2 = _tuple2_tuple2(Tuple2)

        a_es, a = _join_z3_to_z3(crdt.a, get_a(lhs), get_a(rhs), fresh)
        b_es, b = _join_z3_to_z3(crdt.b, get_b(lhs), get_b(rhs), fresh)
        return a_es + b_es, tuple2(a, b)
    elif isinstance(crdt, ast.CSetUnion):
        or_ = z3.Or(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return [], z3.Map(or_, lhs, rhs)
    elif isinstance(crdt, ast.CSetIntersect):
        and_ = z3.And(z3.BoolVal(True), z3.BoolVal(True)).decl()
        return [], z3.Map(and_, lhs, rhs)
    elif isinstance(crdt, ast.CMap):
        typ = cast(ast.TMap, crdt.to_type())
        Option = _type_to_z3(ast.TOption(typ.b))
        f = z3.Function(fresh.get(), Option, Option, Option)

        # TODO(mwhittaker): This function only has to be declared and foralled
        # once per type, not once per join.
        x = z3.Const(fresh.get(), Option)
        y = z3.Const(fresh.get(), Option)
        j_es, j = _join_z3_to_z3(ast.COption(crdt.b), x, y, fresh)
        forall = z3.ForAll([x, y], z3.And(*j_es, f(x, y) == j))

        return [forall], z3.Map(f, lhs, rhs)
    elif isinstance(crdt, ast.COption):
        Option = _type_to_z3(crdt.to_type())
        x = _option_x(Option)
        is_none = _option_is_none(Option)
        some = _option_some(Option)

        j_es, j = _join_z3_to_z3(crdt.a, x(lhs), x(rhs), fresh)
        return (j_es,
                z3.If(is_none(lhs), rhs,
                z3.If(is_none(rhs), lhs,
                some(j))))
    else:
        raise ValueError(f'Unkown CRDT {crdt}.')

def _join_to_z3(crdt: ast.Crdt,
                lhs: ast.Expr,
                lhs_venv: VersionEnv,
                rhs: ast.Expr,
                rhs_venv: VersionEnv,
                tenv: TypeEnv,
                fresh: FreshName) \
                -> Tuple[List[z3.ExprRef], z3.ExprRef]:
    lhs_z3_es, lhs_z3_e = _expr_to_z3(lhs, lhs_venv, tenv, fresh)
    rhs_z3_es, rhs_z3_e = _expr_to_z3(rhs, rhs_venv, tenv, fresh)
    joined_es, joined_e = _join_z3_to_z3(crdt, lhs_z3_e, rhs_z3_e, fresh)
    return lhs_z3_es + rhs_z3_es + joined_es, joined_e

class Z3Checker(checker.Checker):
    def __init__(self, verbose: int = 0, timeout: Optional[int] = None) -> None:
        checker.Checker.__init__(self)
        self.verbose = verbose
        self.timeout = timeout

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
            var.typ = self.type_env[x]
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
            v = ast.EVar(x)
            v.typ = self.type_env[x]
            es, e = _join_to_z3(self.crdt_env[x], v, venv1, v, venv2,
                                self.type_env, fresh)
            for e_ in es:
                solver.add(e_)
            venv = venv.assign(x)
            solver.add(_var_to_z3(v, venv, self.type_env) == e)
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
        if self.timeout is not None:
            solver.set('timeout', self.timeout)

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
