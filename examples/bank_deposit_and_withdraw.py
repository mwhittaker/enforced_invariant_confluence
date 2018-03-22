from iconfluence import *

from .parser import get_checker

"""
Our state based object is a PN-Counter x (representing a bank balance)
replicated across three replicas. x is implemented as two G-Counters p = (p0,
p1, p2) and m = (m0, m1, m2). Our start state is p = (0, 0, 0), m = (0, 0, 0).
Our transactions can add and subtract from x. Our invariant is that x is
non-negative. This object is NOT invariant-confluent.

Run with

    PYTHONPATH=. python -i examples/bank_deposit_and_withdraw.py
"""

checker = get_checker()
p0 = checker.int_max('p0', 0)
p1 = checker.int_max('p1', 0)
p2 = checker.int_max('p2', 0)
m0 = checker.int_max('m0', 0)
m1 = checker.int_max('m1', 0)
m2 = checker.int_max('m2', 0)
checker.add_invariant('p0_geq_0', p0 >= 0)
checker.add_invariant('p1_geq_0', p1 >= 0)
checker.add_invariant('p2_geq_0', p2 >= 0)
checker.add_invariant('m0_geq_0', m0 >= 0)
checker.add_invariant('m1_geq_0', m1 >= 0)
checker.add_invariant('m2_geq_0', m2 >= 0)
checker.add_invariant('x_geq_0', ((p0 + p1 + p2) - (m0 + m1 + m2)) >= 0)
for i in range(10):
    checker.add_transaction(f'x0_inc_{i}', [p0.assign(p0 + i)])
    checker.add_transaction(f'x1_inc_{i}', [p1.assign(p1 + i)])
    checker.add_transaction(f'x2_inc_{i}', [p2.assign(p2 + i)])
    checker.add_transaction(f'x0_dec_{i}', [m0.assign(m0 + i)])
    checker.add_transaction(f'x1_dec_{i}', [m1.assign(m1 + i)])
    checker.add_transaction(f'x2_dec_{i}', [m2.assign(m2 + i)])
