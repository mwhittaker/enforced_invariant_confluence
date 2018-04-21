from iconfluence import *

from .parser import get_checker

"""
Our state based object is a PN-Counter x (representing a bank balance)
replicated across three replicas. x is implemented as two G-Counters p = (p0,
p1, p2) and m = (m0, m1, m2). Our start state is p = (0, 0, 0), m = (0, 0, 0).
Our transactions can add and subtract from x. Our invariant is that x is
non-negative. This object is NOT invariant-confluent.

Run with

    PYTHONPATH=. python -i -m examples.bank_deposit_and_withdraw
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

checker.add_transaction('x0_inc', [p0.assign(p0 + 1)])
checker.add_transaction('x1_inc', [p1.assign(p1 + 1)])
checker.add_transaction('x2_inc', [p2.assign(p2 + 1)])
checker.add_transaction('x0_dec', [m0.assign(m0 + 1)])
checker.add_transaction('x1_dec', [m1.assign(m1 + 1)])
checker.add_transaction('x2_dec', [m2.assign(m2 + 1)])

if isinstance(checker, StratifiedChecker):
    def add_base_invariants(stratum: Stratum) -> None:
        stratum.add_invariant(p0 >= 0)
        stratum.add_invariant(p1 >= 0)
        stratum.add_invariant(p2 >= 0)
        stratum.add_invariant(m0 >= 0)
        stratum.add_invariant(m1 >= 0)
        stratum.add_invariant(m2 >= 0)
        stratum.add_invariant(((p0 + p1 + p2) - (m0 + m1 + m2)) >= 0)

    escrowed = checker.stratum('escrowed')
    add_base_invariants(escrowed)
    for p in [p0, p1, p2]:
        escrowed.add_invariant(p >= 10)
    for m in [m0, m1, m2]:
        escrowed.add_invariant(m <= 10)
    for t in ['x0_inc', 'x1_inc', 'x2_inc', 'x0_dec', 'x1_dec', 'x2_dec']:
        escrowed.add_transaction(t)

    otherwise = checker.stratum('otherwise')
    add_base_invariants(otherwise)
    for t in ['x0_inc', 'x1_inc', 'x2_inc']:
        otherwise.add_transaction(t)

checker.check()

if isinstance(checker, StratifiedChecker):
    m0_lhs, m0_rhs = otherwise.checker.split(m0)
    m1_lhs, m1_rhs = otherwise.checker.split(m1)
    m2_lhs, m2_rhs = otherwise.checker.split(m2)
    otherwise.checker.refine_coreachable(m0_lhs.eq(m0_rhs))
    otherwise.checker.refine_coreachable(m1_lhs.eq(m1_rhs))
    otherwise.checker.refine_coreachable(m2_lhs.eq(m2_rhs))
