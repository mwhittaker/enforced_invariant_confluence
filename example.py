from typing import Callable, Dict

from iconfluence import *

def iconfluent_example(checker: Checker) -> Decision:
    x = checker.int_max('x')
    y = checker.int_max('y')
    tmp = checker.int_max('tmp')

    checker.add_transaction('incr', [
        x.assign(x + 1),
        y.assign(y + 1),
    ])
    checker.add_transaction('swap', [
        tmp.assign(x),
        x.assign(y),
        y.assign(tmp),
    ])

    checker.add_invariant('x_eq_y', x.eq(y))

    return checker.check_iconfluence()

def not_iconfluent_example(checker: Checker) -> Decision:
    x = checker.int_min('x')
    y = checker.int_max('y')
    checker.add_transaction('decr_x', [x.assign(x - 2)])
    checker.add_transaction('incr_y', [y.assign(y + 2)])
    checker.add_invariant('x_ge_y', x >= y)
    return checker.check_iconfluence()

def all_datatypes_example(checker: Checker) -> Decision:
    x_int_max = checker.int_max('x_int_max')
    y_int_max = checker.int_max('y_int_max')
    x_int_min = checker.int_min('x_int_min')
    y_int_min = checker.int_min('y_int_min')
    x_bool_or = checker.bool_or('x_bool_or')
    y_bool_or = checker.bool_or('y_bool_or')
    x_bool_and = checker.bool_and('x_bool_and')
    y_bool_and = checker.bool_and('y_bool_and')
    x_set_union = checker.set_union('x_set_union', TInt())
    y_set_union = checker.set_union('y_set_union', TInt())
    x_set_intersect = checker.set_intersect('x_set_intersect', TInt())
    y_set_intersect = checker.set_intersect('y_set_intersect', TInt())
    x_tuple2 = checker.tuple2('x_tuple2', CIntMax(), CIntMin())
    y_tuple2 = checker.tuple2('y_tuple2', CIntMax(), CIntMin())
    x_option = checker.option('x_option', CIntMax())
    y_option = checker.option('y_option', CIntMax())

    checker.add_transaction('t1', [
        x_int_max.assign(((y_int_max + 1) * 2) - 3),
        x_int_min.assign(((y_int_min + 1) * 2) - 3),
        x_int_min.assign(EIf(y_int_max >= x_int_max, y_int_max, x_int_max)),
        x_bool_or.assign(((y_bool_or & True) | False) >> True),
        x_bool_and.assign(((y_bool_and & True) | False) >> True),
        x_set_union.assign(
            y_set_union.intersect({1, 2}).union({3, 4}).diff({5, 6})),
        x_set_intersect.assign(
            y_set_intersect.intersect({1, 2}).union({3, 4}).diff({5, 6})),
        x_tuple2.assign(ETuple2(y_tuple2.first() + y_tuple2.second(), 2)),
        x_option.assign(ENone(CIntMax().to_type())),
        y_option.assign(ESome(2)),
        x_option.assign(ESome(y_option.unwrap())),
    ])

    checker.add_invariant('inv0', x_int_max >= y_int_max)
    checker.add_invariant('inv1', x_int_max > y_int_max)
    checker.add_invariant('inv2', x_int_max <= y_int_max)
    checker.add_invariant('inv3', x_int_max < y_int_max)
    checker.add_invariant('inv4', x_int_max.eq(y_int_max))
    checker.add_invariant('inv5', x_int_max.ne(y_int_max))
    checker.add_invariant('inv6', x_int_min >= y_int_min)
    checker.add_invariant('inv7', x_int_min > y_int_min)
    checker.add_invariant('inv8', x_int_min <= y_int_min)
    checker.add_invariant('inv9', x_int_min < y_int_min)
    checker.add_invariant('inv10', x_int_min.eq(y_int_min))
    checker.add_invariant('inv11', x_int_min.ne(y_int_min))
    checker.add_invariant('inv12', x_bool_or.eq(y_bool_or))
    checker.add_invariant('inv13', x_bool_or.ne(y_bool_or))
    checker.add_invariant('inv14', x_bool_and.eq(y_bool_and))
    checker.add_invariant('inv15', x_bool_and.ne(y_bool_and))
    checker.add_invariant('inv16', x_set_union.contains(1))
    checker.add_invariant('inv17', y_set_union.contains(1))
    checker.add_invariant('inv18', x_set_intersect.contains(1))
    checker.add_invariant('inv19', y_set_intersect.contains(1))
    checker.add_invariant('inv20', x_tuple2.eq(y_tuple2))
    checker.add_invariant('inv21', x_option.is_none())
    checker.add_invariant('inv22', x_option.is_some())
    checker.add_invariant('inv23', x_option.eq(y_option))
    checker.add_invariant('inv24', x_option.ne(y_option))

    return checker.check_iconfluence()

def vacuously_iconfluent(checker: Checker) -> Decision:
    x = checker.int_max('x')
    y = checker.int_max('y')
    checker.add_transaction('x_gets_y', [x.assign(y)])
    checker.add_transaction('y_gets_x', [y.assign(x)])
    checker.add_invariant('false', EBool(False))
    return checker.check_iconfluence()

def simple_set_unions(checker: Checker) -> Decision:
    xs = checker.set_union('xs', TInt())
    ys = checker.set_union('ys', TInt())
    checker.add_transaction('union_xs', [xs.assign(xs.union(ys))])
    checker.add_transaction('union_ys', [ys.assign(ys.union(xs))])
    checker.add_invariant(
        'some_subset',
        xs.intersect(ys).eq(xs) | xs.intersect(ys).eq(ys))
    return checker.check_iconfluence()

def map_example(checker: Checker) -> Decision:
    x = checker.int_max('x')
    y = checker.int_max('y')
    xs = checker.map('xs', TInt(), CIntMax())
    ys = checker.map('ys', TInt(), CIntMax())
    checker.add_transaction('set_xs', [
        xs.assign(xs.set(x, x)),
        xs.assign(xs.set(1, 1)),
    ])
    checker.add_transaction('set_ys', [
        ys.assign(ys.set(y, y)),
        ys.assign(ys.set(1, 1)),
    ])
    checker.add_invariant('literal_contains_key',
        EMap({1: 1, 2: 2}).contains_key(1))
    checker.add_invariant('contains_key', xs.contains_key(1))
    checker.add_invariant('get', xs[1].eq(1))
    return checker.check_iconfluence()

def nested_map_example(checker: Checker) -> Decision:
    x = checker.int_max('x')
    y = checker.int_max('y')
    xs = checker.map('xs', TInt(), CMap(TInt(), CIntMax()))
    ys = checker.map('ys', TInt(), CMap(TInt(), CIntMax()))
    checker.add_transaction('set_xs', [
        xs.assign(xs.set(x, {x: x})),
        xs.assign(xs.set(1, {1: 1})),
    ])
    checker.add_transaction('set_ys', [
        ys.assign(ys.set(y, {y: y})),
        ys.assign(ys.set(1, {1: 1})),
    ])
    checker.add_invariant('contains_key', xs.contains_key(1))
    checker.add_invariant('get', xs[1].eq({1: 1}))
    return checker.check_iconfluence()

def main() -> None:
    GACC = GuessAndCheckChecker
    Z3C = Z3Checker
    checkers: Dict[str, Callable[[], Checker]] = {
        'guess_and_check': GACC,
        'z3': lambda: Z3C(verbose=1, timeout=1*1000),
        'ensemble': lambda: EnsembleChecker([GACC(), Z3C(timeout=1*1000)]),
    }

    examples: Dict[str, Callable[[Checker], Decision]] = {
        'all_datatypes_example': all_datatypes_example,
        'iconfluent_example': iconfluent_example,
        'map_example': map_example,
        'nested_map_example': nested_map_example,
        'not_iconfluent_example': not_iconfluent_example,
        'simple_set_unions': simple_set_unions,
        'vacuously_iconfluent': vacuously_iconfluent,
    }

    for name, checker in checkers.items():
        msg = f'# {name} checker #'
        print('#' * len(msg))
        print(msg)
        print('#' * len(msg))

        for f_name, f in sorted(examples.items()):
            print(f'Checking {f_name}')
            print(f(checker()))
            print()

if __name__ == '__main__':
    main()
