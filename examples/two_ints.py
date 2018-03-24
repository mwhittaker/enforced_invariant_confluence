from iconfluence import *

from .parser import get_checker

"""
Our state based object is a pair (x, y) of two int maxes. We have one
transaction that increments x and one that decrements y. We start off in state
(0, 0). Our invariant is xy <= 0. O is invariant-confluent, but it is not
invariant-closed.

Run with

    PYTHONPATH=. python -i -m examples.two_ints
"""

# You can change the start state to something like (-10, 10) to become not
# invariant-confluent. Then, the stratified invariant confluent checker can be
# used to prove that things are stratified invariant-confluent.
checker = get_checker()
x = checker.int_max('x', 0)
y = checker.int_max('y', 0)
checker.add_invariant('xy_leq_0', x * y <= 0)
checker.add_transaction('x_inc', [x.assign(x + 1)])
checker.add_transaction('y_dec', [y.assign(y - 1)])

if isinstance(checker, StratifiedChecker):
    quad4 = checker.stratum('quad4')
    quad4.add_invariant((x >= 0) & (y <= 0))
    quad4.add_transaction('x_inc')
    quad4.add_transaction('y_dec')

    quad1 = checker.stratum('quad1')
    quad1.add_invariant((x <= 0) & (y >= 0))
    quad1.add_transaction('x_inc')
    quad1.add_transaction('y_dec')
