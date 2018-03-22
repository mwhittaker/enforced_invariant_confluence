from iconfluence import *

from .parser import get_checker

"""
Our state based object is a G-Counter x = (x0, x1, x2) (representing a bank
balance) replicated across three replicas.Our start state is x = (0, 0, 0).
Our transactions can only add to x. Our invariant is that x is non-negative.
This object is invariant-closed and invariant-confluent.

Run with

    PYTHONPATH=. python -i examples/bank_deposit_only.py
"""

checker = get_checker()
x0 = checker.int_max('x0', 0)
x1 = checker.int_max('x1', 0)
x2 = checker.int_max('x2', 0)
checker.add_invariant('x0_geq_0', x0 >= 0)
checker.add_invariant('x1_geq_0', x1 >= 0)
checker.add_invariant('x2_geq_0', x2 >= 0)
checker.add_invariant('x_geq_0', (x0 + x1 + x2) >= 0)
for i in range(10):
    checker.add_transaction(f'x0_inc_{i}', [x0.assign(x0 + i)])
    checker.add_transaction(f'x1_inc_{i}', [x1.assign(x1 + i)])
    checker.add_transaction(f'x2_inc_{i}', [x2.assign(x2 + i)])
