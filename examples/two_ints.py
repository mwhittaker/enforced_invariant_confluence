from iconfluence import *

checker = InteractiveChecker()
x = checker.int_max('x', 0)
y = checker.int_max('y', 0)
checker.add_invariant('xy_leq_0', x * y <= 0)
checker.add_transaction('x_inc', [x.assign(x + 1)])
checker.add_transaction('y_dec', [y.assign(y - 1)])
