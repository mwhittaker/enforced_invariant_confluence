from iconfluence import *

from .parser import get_checker

"""
Our state based object is a pair (X, Y) of two 2P-sets: X = (XA - XR) and Y =
(YA - YR). Our start state is X = ({1, 2}, {}) and Y = ({1, 2, 3, 4}, {}). Our
transactions can remove something from X and add something to Y. Our invariant
is that X is a subset of Y. O is invariant-confluent but not I-closed.

Run with

    PYTHONPATH=. python -i -m examples.foreign_key
"""

checker = get_checker()
XA = checker.set_union('XA', TInt(), EEmptySet(TInt()))
XR = checker.set_union('XR', TInt(), EEmptySet(TInt()))
YA = checker.set_union('YA', TInt(), EEmptySet(TInt()))
YR = checker.set_union('YR', TInt(), EEmptySet(TInt()))

# Invariant.
checker.add_invariant(
    'X_subset_Y',
    XA.diff(XR).subseteq(YA.diff(YR)))

# Transactions.
for i in range(5):
    checker.add_transaction(f'X_sub_{i}', [XR.join_assign({i})])
    checker.add_transaction(f'Y_add_{i}', [YA.join_assign({i})])

# checker.refine_invariant(XA.eq({1, 2}))
# checker.refine_invariant(YR.eq(EEmptySet(TInt())))
