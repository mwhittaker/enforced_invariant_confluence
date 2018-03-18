from iconfluence import *

checker = InteractiveChecker()
x = checker.option('x', CIntMax(), ENone(TInt()))
y = checker.option('y', CIntMax(), ENone(TInt()))
checker.add_invariant('xy_leq_0',
    (x.is_some() & y.is_some()) >> (x.unwrap() * y.unwrap() <= 0))
checker.add_transaction('x_zero_or_inc', [
    x.assign(EIf(x.is_none(), ESome(0), ESome(x.unwrap() + 1)))
])
checker.add_transaction('y_zero_or_dec', [
    y.assign(EIf(y.is_none(), ESome(0), ESome(y.unwrap() - 1)))
])
