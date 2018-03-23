from typing import List, Set

from ..ast import Invariant
from ..checker import Checker, Decision
from ..typecheck import typecheck_invariant

class Stratum:
    def __init__(self, checker: 'StratifiedChecker') -> None:
        self.checker = checker
        self.transactions: List[str] = []
        self.invariants: List[Invariant] = []

    def __str__(self) -> str:
        strings: List[str] = []

        strings.append('Transactions')
        for txn in self.transactions:
            strings.append(f'  {txn}')

        strings.append('Invariants')
        for inv in self.invariants:
            strings.append(f'  {inv}')

        return '\n'.join(strings)

    def __repr__(self) -> str:
        return str(self)

    def add_transaction(self, txn: str) -> None:
        if txn not in self.checker.transactions:
            txns = ', '.join(self.checker.transactions)
            m = (f'Transaction {txn} is not registered. The registered ' +
                 f'transactions are: {txns}.')
            raise ValueError(m)

        if txn not in self.transactions:
            self.transactions.append(txn)

    def add_invariant(self, inv: Invariant) -> None:
        inv = typecheck_invariant(inv, self.checker.type_env)
        self.invariants.append(inv)

class StratifiedChecker(Checker):
    def __init__(self, verbose: bool = True) -> None:
        Checker.__init__(self)
        self.strata: List[Stratum] = []

    def stratum(self) -> Stratum:
        s = Stratum(self)
        self.strata.append(s)
        return s

    def check(self) -> Decision:
        # check I(s_0)
        # for each stratum check that th invariant implies the main invariant
        # check that the invariant implies the union of all invariants for each stratum,
        # check I-closure for each stratum
        #   get counter-example
        #   no reachability needed; just say don't know otherwise
        # if iclosed -> yes; otherwise
        pass
