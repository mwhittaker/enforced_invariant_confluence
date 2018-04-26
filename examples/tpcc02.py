from iconfluence import *

from .parser import get_checker

checker = get_checker()
d_next_o_id = checker.int_max('d_next_o_id', 0)
order_ids = checker.set_union('order_ids', TInt(), ESet({-1}))
orders = checker.map('orders', TInt(), CTop(TBool()), EEmptyMap(TInt(), TOption(TBool())))

x = EVar('x')
k = EVar('k')
checker.add_invariant('sequential',
    (d_next_o_id - 1).eq(ESetMax(order_ids)))
checker.add_invariant('order_ids_init',
    order_ids.contains(-1))
checker.add_invariant('continuous',
    order_ids.forall(x,
        EIf(x.eq(ESetMax(order_ids)), EBool(True), order_ids.contains(x + 1))))
checker.add_invariant('geq_-1',
    order_ids.forall(x, x >= -1))
checker.add_invariant('orders_and_order_ids_1',
    order_ids.forall(x, EIf(x.ne(-1), orders.contains_key(x), EBool(True))))
checker.add_invariant('orders_and_order_ids_2',
    orders.forall_keys(k, order_ids.contains(k)))
checker.add_invariant('orders_and_order_ids_3',
    EBoolNot(orders.contains_key(-1)))
checker.add_invariant('unique',
    orders.forall_keys(k, orders[k].is_some()))
checker.add_invariant('simple_example',
    EBoolNot(order_ids.contains(2)))

for b in [True, False]:
    checker.add_transaction(f'order_{b}', [
        orders.assign(orders.set(d_next_o_id, ESome(b))),
        order_ids.assign(order_ids.union({d_next_o_id})),
        d_next_o_id.assign(d_next_o_id + 1),
    ])
