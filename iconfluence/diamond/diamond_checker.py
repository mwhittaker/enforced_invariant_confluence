from typing import Set, Tuple, cast

from colored import attr, fg
from orderedset import OrderedSet
import z3

from .. import ast
from ..ast import Crdt, Expr, Stmt, SJoinAssign, Transaction
from ..checker import Checker, Decision
from ..envs import ValEnv
from ..eval import eval_invariant
from ..z3_.compile import compile_expr, compile_join, compile_txn
from ..z3_.fresh_name import FreshName
from ..z3_.model import model_to_state
from ..z3_.version_env import VersionEnv
from ..z3_.z3_util import scoped

class DiamondChecker(Checker):
    """
    Consider a state-based object O = (S, join), a start state s0, a set of
    transactions T, and an invariant I. T is (s0, T, I)-confluent if the
    following criteria are met:

        1. O is a semillatice.
        2. Every t in T is of the form t(s) = s join s' where s' is some state
           in S.
        3. For every pair of transactions t, u and for every state s, if I(s)
           and I(t(s)) and I(u(s)), then I(t(s) join u(s)).
        4. I(s0)

    The DiamondChecker checks if these criteria are met. The third criterion is
    called diamond-invariant-confluence, hence the name DiamondChecker.
    """
    def __init__(self, verbose: bool = False) -> None:
        Checker.__init__(self)
        self.verbose = verbose
        self.fresh = FreshName()

    def _debug(self, s: str) -> None:
        if self.verbose:
            print(s)

    def _state_satisfies_invs(self, state: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, state) for inv in invs)

    def _var_free_expr(self, e: Expr) -> bool:
        if isinstance(e, ast.EVar):
            return False
        elif (isinstance(e, ast.EInt) or
              isinstance(e, ast.EBool) or
              isinstance(e, ast.EEmptySet) or
              isinstance(e, ast.EEmptyMap) or
              isinstance(e, ast.ENone)):
            return True
        elif isinstance(e, ast.ETuple2):
            return self._var_free_expr(e.a) and self._var_free_expr(e.b)
        elif isinstance(e, ast.ESet):
            return all(self._var_free_expr(x) for x in e.xs)
        elif isinstance(e, ast.EMap):
            return all(self._var_free_expr(k) and self._var_free_expr(v)
                       for k, v in e.kvs.items())
        elif isinstance(e, ast.ESome):
            return self._var_free_expr(e.x)
        elif isinstance(e, ast.EUnaryOp):
            return self._var_free_expr(e.x)
        elif isinstance(e, ast.EBinaryOp):
            return all(self._var_free_expr(sube) for sube in [e.lhs, e.rhs])
        elif isinstance(e, ast.ETernaryOp):
            return all(self._var_free_expr(sube) for sube in [e.a, e.b, e.c])
        else:
            raise ValueError(f'Unkown expression {e}.')

    def _var_free_join(self, stmt: Stmt) -> bool:
        if isinstance(stmt, SJoinAssign):
            return self._var_free_expr(stmt.e)
        else:
            return False

    def _has_bottom(self, crdt: Crdt) -> bool:
        if (isinstance(crdt, ast.CIntMax) or
            isinstance(crdt, ast.CIntMin) or
            isinstance(crdt, ast.CSetIntersect)):
            return False
        elif (isinstance(crdt, ast.CBoolOr) or
            isinstance(crdt, ast.CBoolAnd) or
            isinstance(crdt, ast.CSetUnion) or
            isinstance(crdt, ast.COption) or
            isinstance(crdt, ast.CMap)):
            return True
        elif isinstance(crdt, ast.CTuple2):
            return self._has_bottom(crdt.a) and self._has_bottom(crdt.b)
        else:
            raise ValueError(f'Unrecognized crdt {crdt}.')

    def _txn_is_constant_join(self, txn: Transaction) -> bool:
        """
        `_txn_is_constant_join(txn)` checks that transaction txn is of the form
        txn(s) = s join s' for some constant state s' in S. In order for txn to
        be a constant join, it must satisfy the following criteria:

            1. Every statement is a join_assign of the form x.join_assign(e)
               where e is a variable-free expression.
            2. Every variable x must appear in at least one statement, unless
               the CRDT of x has a bottom element. If x has a bottom, then it's
               okay for it to not appear in a statement, because it's
               equivalent to joining with bottom.

        For example, given the variables x: IntMax, y: SetUnion, and z:
        SetUnion, this is a constant join transaction:

            x.join_assign(1)
            y.join_assign({2})
            y.join_assign({3}) # Duplicate joins are permitted (but useless).
            # z is missing, but SetUnion has a bottom element, so that's okay.

        This is not:

            # x is missing and IntMax doesn't have a bottom element.
            y.join_assign({x}) # {x} is not a variable-free expression.
            z.join_assign({2}) # This is okay.
        """
        vs = set(self.crdt_env.keys())

        vs_seen: Set[str] = set()
        for s in txn:
            if not self._var_free_join(s):
                return False
            s = cast(ast.SJoinAssign, s)
            vs_seen.add(s.x.x)

        for v in vs - vs_seen:
            crdt = self.crdt_env[v]
            if not self._has_bottom(crdt):
                return False

        return True

    def _compile_expr(self,
                      e: Expr,
                      venv: VersionEnv) -> Tuple[OrderedSet, z3.ExprRef]:
        return compile_expr(e, venv, self.type_env, self.fresh)

    # TODO(mwhittaker): Replace with implementation in compile.
    def _venv_satisfies_inv(self, venv: VersionEnv) -> OrderedSet:
        zss = OrderedSet()
        for inv in self.invariants.values():
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zss.add(inv_ze)
        return zss

    # TODO(mwhittaker): Replace with implementation in compile.
    def _venv_doesnt_satisfy_inv(self, venv: VersionEnv) -> OrderedSet:
        zss = OrderedSet()
        zes = OrderedSet()
        for inv in self.invariants.values():
            inv_zss, inv_ze = self._compile_expr(inv, venv)
            zss |= inv_zss
            zes.add(inv_ze)
        zss.add(z3.Not(z3.And(list(zes))))
        return zss

    def _model_to_state(self, model: z3.ModelRef, venv: VersionEnv) -> ValEnv:
        names = {venv.get_name(name): name for name in self.type_env}
        state = model_to_state(model, set(names.keys()))
        for versioned_name, name in names.items():
            state[name] = state[versioned_name]
            del state[versioned_name]
        return state

    def _diamond_iconfluent(self) -> bool:
        solver = z3.Solver()
        tenv = self.type_env
        cenv = self.crdt_env
        fresh = self.fresh

        txns = list(self.transactions.items())
        for i, (t_name, t) in enumerate(txns):
            for (u_name, u) in txns[i + 1:]:
                with scoped(solver):
                    s_venv = VersionEnv('s')
                    s_zss = self._venv_satisfies_inv(s_venv)

                    t_venv = s_venv.with_suffix('t')
                    t_zss, t_venv = compile_txn(t, t_venv, tenv, cenv, fresh)
                    t_zss |= self._venv_satisfies_inv(t_venv)

                    u_venv = s_venv.with_suffix('u')
                    u_zss, u_venv = compile_txn(u, u_venv, tenv, cenv, fresh)
                    u_zss |= self._venv_satisfies_inv(u_venv)

                    join_venv = VersionEnv('join')
                    join_zss, join_venv = compile_join(
                        t_venv, u_venv, join_venv, cenv, tenv, fresh)
                    join_zss |= self._venv_doesnt_satisfy_inv(join_venv)

                    solver.add(list(s_zss | t_zss | u_zss | join_zss))
                    s = f'{t_name} join {u_name}'
                    self._debug(s)
                    self._debug('=' * len(s))
                    self._debug(f'{fg(206)}{solver.sexpr()}{attr(0)}')

                    result = solver.check()
                    if result == z3.unknown:
                        self._debug("Z3 got stuck!")
                        return False
                    elif result == z3.sat:
                        if self.verbose:
                            model = solver.model()
                            s_state = self._model_to_state(model, s_venv)
                            t_state = self._model_to_state(model, t_venv)
                            u_state = self._model_to_state(model, u_venv)
                            join_state = self._model_to_state(model, join_venv)
                            self._debug('Counterexample found.')
                            self._debug('')
                            self._debug(f'  s    = {s_state}')
                            self._debug(f'  t    = {t_state}')
                            self._debug(f'  u    = {u_state}')
                            self._debug(f'  join = {join_state}')
                        return False
        return True

    def _check(self) -> Decision:
        # Criterion 1 is enforced automatically because the only available
        # datatypes are CRDTs.

        # Check criterion 4.
        if not self._state_satisfies_invs(self.s0_vals):
            s0 = self.s0_vals
            self._debug(f'Initial state {s0} didn\'t satisfy invariant.')
            return Decision.NO

        # Check criterion 2.
        for name, txn in self.transactions.items():
            if not self._txn_is_constant_join(txn):
                self._debug(f'Transaction {name} is not a constant join.')
                return Decision.UNKNOWN

        # Check criterion 3.
        if self._diamond_iconfluent():
            return Decision.YES

        return Decision.UNKNOWN
