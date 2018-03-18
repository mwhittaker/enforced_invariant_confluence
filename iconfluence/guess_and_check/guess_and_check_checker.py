from typing import Any, Dict

from .. import ast
from .. import checker
from ..envs import CrdtEnv, ValEnv
from ..eval import eval_invariant
from .state_explorer import NothingFoundException, StateExplorer

class GuessAndCheckChecker(checker.Checker):
    """
    A GuessAndCheckChecker randomly generates reachable states. If one of the
    reachable states does not satisfy the invariant, then it concludes that the
    object is not invariant confluent. If it cannot find a reachable state that
    doesn't satisfy the invariant, then it gives up and returns UNKNOWN.
    """
    def __init__(self, max_iterations: int = 100) -> None:
        checker.Checker.__init__(self)
        self.max_iterations = max_iterations
        self.state_explorer = StateExplorer(self.crdt_env, self.s0_vals,
                                            self.invariants, self.transactions)

    def check_iconfluence(self) -> checker.Decision:
        try:
            for _ in range(self.max_iterations):
                s = self.state_explorer.explore_one()
                invs = self.invariants.values()
                if not all(eval_invariant(inv, s) for inv in invs):
                    return checker.Decision.NO
            return checker.Decision.UNKNOWN
        except NothingFoundException:
            return checker.Decision.UNKNOWN
