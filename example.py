from typing import Callable, Dict

from iconfluence import *

def iconfluent_example(checker: Checker) -> None:
    # Variable declaration.
    x = checker.int_max('x')
    y = checker.int_max('y')
    tmp = checker.int_max('tmp')

    # Transactions.
    checker.add_transaction('incr', [
        x.assign(x + 1),
        y.assign(y + 1),
    ])
    checker.add_transaction('swap', [
        tmp.assign(x),
        x.assign(y),
        y.assign(tmp),
    ])

    one = EInt(1)
    xs = ESet({one})
    ys = ESet({one})

    # Invariants.
    checker.add_invariant('x_eq_y', x.eq(y))

    # This should always print UNKNOWN or YES.
    print(checker.check_iconfluence())

def not_iconfluent_example(checker: Checker) -> None:
    # Variable declaration.
    x = checker.int_min('x')
    y = checker.int_max('y')

    # Transactions.
    checker.add_transaction('decr_x', [
        x.assign(x - 2),
    ])
    checker.add_transaction('incr_y', [
        y.assign(y + 2),
    ])

    # Invariants.
    checker.add_invariant('x_ge_y', x >= y)

    # This should always print UNKNOWN or NO.
    print(checker.check_iconfluence())

def all_datatypes_example(checker: Checker) -> None:
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

    checker.add_transaction('t1', [
        x_int_max.assign(((y_int_max + 1) * 2) - 3),
        x_int_min.assign(((y_int_min + 1) * 2) - 3),
        x_bool_or.assign(((y_bool_or & True) | False) >> True),
        x_bool_and.assign(((y_bool_and & True) | False) >> True),
        x_set_union.assign(
            y_set_union.intersect({1, 2}).union({3, 4}).diff({5, 6})),
        x_set_intersect.assign(
            y_set_intersect.intersect({1, 2}).union({3, 4}).diff({5, 6})),
        x_tuple2.assign(ETuple2(y_tuple2[0] + y_tuple2[1], 2)),
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

    print(checker.check_iconfluence())

def main() -> None:
    GACC = GuessAndCheckChecker
    Z3C = Z3Checker
    checkers: Dict[str, Callable[[], Checker]] = {
        'guess_and_check': GACC,
        'z3': lambda: Z3C(verbose=1),
        'ensemble': lambda: EnsembleChecker([GACC(), Z3C()]),
    }

    examples: Dict[str, Callable[[Checker], None]] = {
        'iconfluent_example': iconfluent_example,
        'not_iconfluent_example': not_iconfluent_example,
        'all_datatypes_example': all_datatypes_example,
    }

    for name, checker in checkers.items():
        msg = f'# {name} checker #'
        print('#' * len(msg))
        print(msg)
        print('#' * len(msg))

        for f_name, f in sorted(examples.items()):
            print(f'Checking {f_name}')
            f(checker())
            print()

if __name__ == '__main__':
    main()
