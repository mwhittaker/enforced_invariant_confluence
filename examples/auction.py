
from iconfluence import *

"""
Auction example from [1]. Our object is a pair (bids, winning_bid) of a set bid
of integers and an optional integer winning_bid. Our start state is ({}, None).
We have transactions to place a bid and a transaction to close the bid. Our
invariant is that if the bid is closed, the winning bid is the maximum of the
bids. This example is NOT invariant-confluent.

Run with

    PYTHONPATH=. python -i examples/auction.py

[1]: https://scholar.google.com/scholar?cluster=16043456868654348168
"""

checker = InteractiveChecker(verbose=False)
bids = checker.set_union('bids', TInt(), EEmptySet(TInt()))
winning_bid = checker.option('winning_bid', CIntMax(), ENone(TInt()))
checker.add_invariant(
    'winning_bid_is_max',
    winning_bid.is_some() >> winning_bid.unwrap().eq(ESetMax(bids)))
checker.add_transaction('close', [
    winning_bid.assign(ESome(ESetMax(bids)))
])
for i in range(5):
    checker.add_transaction(f'bid_{i}', [bids.assign(bids.union({i}))])
