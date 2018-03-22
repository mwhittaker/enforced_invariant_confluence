from iconfluence import *

from .parser import get_checker

"""
Our state based object is a pair (X, Y) of two add-only sets.  Our start state
is X = Y = {}. Our transactions can add anything to X and Y. Our invariant is
that X is a subset of Y or Y is a subset of X. O is not invariant-confluent.

Run with

    PYTHONPATH=. python -i -m examples.subsets
"""

checker = get_checker()
X = checker.set_union('X', TInt(), EEmptySet(TInt()))
Y = checker.set_union('Y', TInt(), EEmptySet(TInt()))
checker.add_invariant('subsets', X.subseteq(Y) | Y.subseteq(X))
for i in range(6):
    checker.add_transaction(f'X_add_{i}', [X.join_assign({i})])
    checker.add_transaction(f'Y_add_{i}', [Y.join_assign({i})])
