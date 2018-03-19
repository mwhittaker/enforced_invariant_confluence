from iconfluence import *

"""
Our state based object is a pair (x, y) of two int maxes. We have one
transaction that increments x and one that decrements y. We start off in state
(0, 0). Our invariant is xy <= 0. O is invariant-confluent, but it is not
invariant-closed.

Run with

    PYTHONPATH=. python -i examples/two_ints.py
"""

checker = InteractiveChecker(verbose=False)
x = checker.int_max('x', 0)
y = checker.int_max('y', 0)
checker.add_invariant('xy_leq_0', x * y <= 0)
checker.add_transaction('x_inc', [x.assign(x + 1)])
checker.add_transaction('y_dec', [y.assign(y - 1)])
