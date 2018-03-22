from typing import Set, cast

from .. import ast
from ..ast import Crdt, Expr, Stmt, SJoinAssign, Transaction
from ..checker import Checker, Decision
from ..envs import ValEnv
from ..eval import eval_invariant

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

    def check_iconfluence(self) -> Decision:
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
        # TODO: Check one i confluence

        return Decision.UNKNOWN
