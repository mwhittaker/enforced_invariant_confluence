from typing import Any, Dict

from .. import ast
from .. import checker
from ..envs import CrdtEnv, ValEnv
from ..eval import eval_invariant
from ..state_explorer import StateExplorer

class GuessAndCheckChecker(checker.Checker):
    """
    A GuessAndCheckChecker randomly generates reachable states. If one of the
    reachable states does not satisfy the invariant, then it concludes that the
    object is not invariant confluent. If it cannot find a reachable state that
    doesn't satisfy the invariant, then it gives up and returns UNKNOWN.
    """
    def __init__(self, num_states: int = 100, verbose: bool = False) -> None:
        checker.Checker.__init__(self, verbose)
        self.num_states = num_states
        self.verbose = verbose
        self.state_explorer = StateExplorer(self.crdt_env, self.s0_vals,
                                            self.invariants, self.transactions)

    def _state_satisfies_invs(self, state: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, state) for inv in invs)

    def _check(self) -> checker.Decision:
        if self.verbose:
            print(f'Exploring {self.num_states} states...')
        self.state_explorer.explore(self.num_states)
        for state in self.state_explorer.states:
            if not self._state_satisfies_invs(state):
                if self.verbose:
                    print(f'State {state} does not satisfy the invariant.')
                return checker.Decision.NO
        return checker.Decision.UNKNOWN
