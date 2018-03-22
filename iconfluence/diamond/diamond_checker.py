from ..checker import Checker, Decision

from ..eval import eval_invariant
from ..envs import ValEnv


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

    def _check_state_satisfies_invs(self, state: ValEnv) -> bool:
        invs = self.invariants.values()
        return all(eval_invariant(inv, state) for inv in invs)

    def check_iconfluence(self) -> Decision:
        if not self._check_state_satisfies_invs(self.s0_vals):
            return Decision.NO

        # TODO: check than all txns are of the form s join st
        # TODO: Check one i confluence
        return Decision.YES
