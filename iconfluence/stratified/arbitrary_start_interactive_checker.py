from enum import Enum
from textwrap import wrap
from typing import List, Optional, Tuple

import z3

from ..ast import Invariant
from ..checker import Checker, Decision
from ..envs import ValEnv
from ..z3_.fresh_name import FreshName
from .arbitrary_start_checker import ArbitraryStartChecker

class Label(Enum):
    COREACHABLE = "coreachable"
    COUNREACHABLE = "counreachable"

def _wrap_print(s: str) -> None:
    print('\n'.join(wrap(s, 80)))

class ArbitraryStartInteractiveChecker(ArbitraryStartChecker):
    """
    TODO(mwhittaker): Document.
    """
    def __init__(self, verbose: bool = False) -> None:
        self.verbose = verbose
        self.solver = z3.Solver()
        self.fresh = FreshName()
        self.coreachable_refinements: List[Invariant] = []

        # Counterexamples.
        self.lhs: Optional[ValEnv] = None
        self.rhs: Optional[ValEnv] = None
        self.label: Optional[Label] = None
        self.counreachable_states: List[Tuple[ValEnv, ValEnv]] = []

    def __str__(self) -> str:
        return 'TODO'

    def __repr__(self) -> str:
        return str(self)

    def coreachable(self) -> None:
        self.label = Label.COREACHABLE

    def counreachable(self) -> None:
        self.label = Label.COUNREACHABLE

    def check(self) -> Decision:
        if self.lhs is not None:
            assert self.rhs is not None, self.rhs
            if self.label is None:
                m = ('You have not labelled whether lhs and rhs are ' +
                     'coreachable or counreachable. Please call the ' +
                     'coreachable() or counreachable() methods to label them.')
                _wrap_print(m)
                return Decision.UNKNOWN

        if self.lhs is not None:
            assert self.rhs is not None and self.label is not None
            if self.label == Label.COREACHABLE:
                return Decision.NO

            self.counreachable_states.append((self.lhs, self.rhs))
            # TODO(mwhittaker): Automatically refine coreachability.
            self.lhs = None
            self.rhs = None
            self.label = None

        # TODO(mwhittaker):
        #   - check if i-refined-closed
        #   - if closed: return True
        #   - if yes: return true
        #   - if not: record counter_examples and present them to the user
        #   - label as co rechable or not; auto updated refinements if so
        #   - if reachable: return no
        raise NotImplementedError()
