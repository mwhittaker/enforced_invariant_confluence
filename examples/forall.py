from iconfluence import *

from .parser import get_checker

checker = get_checker()
xs = checker.set_union('xs', TInt(), EEmptySet(TInt()))
kvs = checker.map('kvs', TInt(), CIntMax(), EEmptyMap(TInt(), TInt()))

x = EVar('x')
k = EVar('k')
checker.add_invariant('x_leq_10', xs.forall(x, x <= 10))
checker.add_invariant('k_leq_10', kvs.forall_keys(k, k <= 10))
checker.add_invariant('v_leq_10', kvs.forall_keys(k, kvs[k] <= 10))

for i in range(20):
    checker.add_transaction(f'x_add_{i}', [xs.assign(xs.union({i}))])
    checker.add_transaction(f'kvs_add_{i}', [kvs.assign(kvs.set(i, i))])
