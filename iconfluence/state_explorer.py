from typing import Dict, List, Set
import random

from .ast import Invariant, Transaction
from .envs import CrdtEnv, ValEnv
from .eval import eval_invariant, eval_join, eval_txn

class StateExplorer:
    """
    Given a start state, a set of transactions, and an invariant, a
    StateExplorer will randomly explore the set of states reachable from the
    start state.
    """
    # TODO(mwhittaker): We currently use a pretty naive approach to state
    # exploration. There are likely smarter ways to explore the state space.
    # For example, we may want to heavily prioritize recently discovered points
    # when selecting random points to join.

    def __init__(self,
                 crdt_env: CrdtEnv,
                 s0: ValEnv,
                 invariants: Dict[str, Invariant],
                 transactions: Dict[str, Transaction],
                 max_iters_per_state: int = 100) \
                 -> None:
        self.crdt_env = crdt_env
        self.invariants = invariants
        self.transactions = transactions

        # TODO(mwhittaker): States are not hashable, so we cannot store them in
        # a set. Instead, we store them in a list. This slows down things quite
        # a bit. Switch to frozendicts or something like that.
        self.states: List[ValEnv] = [s0]

        # If we want to explore n states, we try n * max_iters_per_state times
        # before giving up. For example, if max_iters_per_state = 10 and we
        # want to find 5 new states, we try to find 5 states across 50 steps.
        self.max_iters_per_state = max_iters_per_state

    def _flip_coin(self) -> bool:
        return random.choice([True, False])

    def _random_state(self) -> ValEnv:
        # Prioritize recently discovered states.
        weights = range(len(self.states), 0, -1)
        return random.choices(self.states, weights=weights, k=1)[0]

    def _state_satisfies_invs(self, s: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, s) for inv in invs)

    def _explore(self) -> List[ValEnv]:
        join = self._flip_coin()
        if join:
            lhs = self._random_state()
            rhs = self._random_state()
            return [eval_join(lhs, rhs, self.crdt_env)]
        else:
            s = self._random_state()
            states: List[ValEnv] = []
            for txn in self.transactions.values():
                s_new = eval_txn(txn, s, self.crdt_env)
                if self._state_satisfies_invs(s_new):
                    states.append(s_new)
            return states

    def explore(self, n: int = 1) -> None:
        """
        Explore approximately n states. This function might find more or fewer
        states, but will try to find approximately n states.
        """
        assert n >= 1, n

        num_found = 0
        for _ in range(n * self.max_iters_per_state):
            states = self._explore()
            for s in states:
                if s not in self.states:
                    self.states.append(s)
                    num_found += 1
            if num_found >= n:
                return

    def add(self, state: ValEnv) -> None:
        """Add a reachable state."""
        if state not in self.states:
            self.states.append(state)
