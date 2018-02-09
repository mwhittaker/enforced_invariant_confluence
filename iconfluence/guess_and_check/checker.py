from typing import Any, Dict
import random

from .. import checker
from .. import eval
from .. import ast

CrdtEnv = Dict[str, ast.Crdt]
ValEnv = Dict[str, Any]

class _NothingFoundException(Exception):
    pass

class GuessAndCheckChecker(checker.Checker):
    def _satisfies_invariants(self, env: ValEnv):
        return all(eval.eval_invariant(inv, env)
                   for inv in self.invariants.values())

    def _join(self, crdt: ast.Crdt, lhs: Any, rhs: Any) -> Any:
        if isinstance(crdt, ast.CIntMax):
            return max(lhs, rhs)
        elif isinstance(crdt, ast.CIntMin):
            return min(lhs, rhs)
        elif isinstance(crdt, ast.CBoolOr):
            return lhs or rhs
        elif isinstance(crdt, ast.CBoolAnd):
            return lhs and rhs
        elif isinstance(crdt, ast.CTuple2):
            a = self._join(crdt.a, lhs[0], rhs[0])
            b = self._join(crdt.b, lhs[1], rhs[1])
            return (a, b)
        elif isinstance(crdt, ast.CSetUnion):
            return lhs.union(rhs)
        elif isinstance(crdt, ast.CSetIntersect):
            return lhs.intersect(rhs)

    def _join_envs(self, val_env1: ValEnv, val_env2: ValEnv) -> ValEnv:
        env: ValEnv = {}
        for x, crdt in self.crdt_env.items():
            assert x in val_env1, (x, val_env1)
            assert x in val_env2, (x, val_env2)
            env[x] = self._join(crdt, val_env1[x], val_env2[x])
        return env

    def _random_value(self, typ: ast.Type) -> Any:
        if isinstance(typ, ast.TInt):
            return random.randint(8, 10)
        elif isinstance(typ, ast.TBool):
            return random.randint(0, 1) == 0
        elif isinstance(typ, ast.TTuple2):
            return (self._random_value(typ.a), self._random_value(typ.b))
        elif isinstance(typ, ast.TSet):
            cardinality = random.randint(1, 10)
            return {self._random_value(typ.a) for _ in range(cardinality)}
        else:
            raise ValueError(f'Unrecognized type {typ}.')

    def _random_env(self) -> ValEnv:
        return {x: self._random_value(t) for (x, t) in self.type_env.items()}

    def _random_txn(self) -> ast.Transaction:
        names = list(self.transactions.keys())
        return self.transactions[random.choice(names)]

    def _random_invariant_env(self) -> ValEnv:
        for _ in range(10000):
            env = self._random_env()
            if self._satisfies_invariants(env):
                return env
        raise _NothingFoundException()

    def _apply_random_invariant_txn(self, env: ValEnv) -> ValEnv:
        for _ in range(10000):
            txn = self._random_txn()
            env = eval.eval_txn(txn, env)
            if self._satisfies_invariants(env):
                return env
        raise _NothingFoundException()

    def check_iconfluence(self) -> checker.Decision:
        try:
            self._typecheck()
            for _ in range(100):
                env = self._random_invariant_env()
                env1 = self._apply_random_invariant_txn(env)
                env2 = self._apply_random_invariant_txn(env)
                env_joined = self._join_envs(env1, env2)
                if not self._satisfies_invariants(env_joined):
                    return checker.Decision.NO
            return checker.Decision.UNKNOWN
        except _NothingFoundException:
            return checker.Decision.UNKNOWN
