from iconfluence import *

from .parser import get_checker

checker = get_checker()
x = checker.int_max('x', 0)
y = checker.int_max('y', 0)
z = checker.int_max('z', 0)
checker.add_invariant('x_geq_0', x >= 0)
checker.add_invariant('y_geq_0', y >= 0)
checker.add_invariant('z_geq_0', z >= 0)
checker.add_invariant('x_plus_y_eq_z', (x + y).eq(z))
for i in range(10):
    checker.add_transaction(f'x_inc_{i}', [x.assign(x + i)])
    checker.add_transaction(f'y_inc_{i}', [y.assign(y + i)])
    checker.add_transaction(f'z_inc_{i}', [z.assign(z + i)])
