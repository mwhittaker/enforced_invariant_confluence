from typing import Dict, List, Set
import random

from ..ast import Invariant, Transaction
from ..envs import CrdtEnv, ValEnv
from ..eval import eval_invariant, eval_join, eval_txn

class NothingFoundException(Exception):
    pass

class StateExplorer:
    def __init__(self,
                 crdt_env: CrdtEnv,
                 s0: ValEnv,
                 invariants: Dict[str, Invariant],
                 transactions: Dict[str, Transaction]) \
                 -> None:
        self.crdt_env = crdt_env
        self.states: List[ValEnv] = [s0]
        self.invariants = invariants
        self.transactions = transactions

    def _flip_coin(self) -> bool:
        return random.choice([True, False])

    def _random_state(self) -> ValEnv:
        weights = range(len(self.states), 0, -1)
        return random.choices(self.states, weights=weights, k=1)[0]

    def _state_satisfies_invs(self, s: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, s) for inv in invs)

    def _explore_state(self) -> ValEnv:
        join = self._flip_coin()
        if join:
            lhs = self._random_state()
            rhs = self._random_state()
            return eval_join(lhs, rhs, self.crdt_env)
        else:
            s = self._random_state()
            txns = list(self.transactions.values())
            random.shuffle(txns)
            for txn in txns:
                s_new = eval_txn(txn, s)
                if self._state_satisfies_invs(s_new):
                    return s_new
            return self._explore_state()

    def _explore_new_state(self) -> ValEnv:
        # TODO(mwhittaker): This is a naive way to generate random states. We
        # might be recalculating the same states again and again. A smarter way
        # would be to prioritize recently found states over older states, for
        # example.
        max_iterations = 10 * 1000
        for _ in range(max_iterations):
            s = self._explore_state()
            if s not in self.states:
                return s
        msg = f'New state not found after {max_iterations} iterations.'
        raise NothingFoundException(msg)

    def explore_one(self) -> ValEnv:
        s = self._explore_new_state()
        self.states.append(s)
        return s

    def explore(self, n: int = 1) -> None:
        assert(n >= 1)
        for _ in range(n):
            self.explore_one()
