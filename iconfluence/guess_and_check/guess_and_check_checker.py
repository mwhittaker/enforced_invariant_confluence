from typing import Any, Dict

from .. import ast
from .. import checker
from ..eval import eval_invariant
from .state_explorer import NothingFoundException, StateExplorer

CrdtEnv = Dict[str, ast.Crdt]
ValEnv = Dict[str, Any]

class GuessAndCheckChecker(checker.Checker):
    def __init__(self, max_iterations: int = 100) -> None:
        checker.Checker.__init__(self)
        self.max_iterations = max_iterations
        self.state_explorer = StateExplorer(self.crdt_env, self.s0_vals,
                                            self.invariants, self.transactions)

    def _env_satisfies_invs(self, s: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, s) for inv in invs)

    def check_iconfluence(self) -> checker.Decision:
        try:
            for _ in range(self.max_iterations):
                s = self.state_explorer.explore_one()
                if not self._env_satisfies_invs(s):
                    return checker.Decision.NO
            return checker.Decision.UNKNOWN
        except NothingFoundException:
            return checker.Decision.UNKNOWN
