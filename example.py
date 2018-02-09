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

def main() -> None:
    checkers: Dict[str, Callable[[], Checker]] = {
        'guess_and_check': GuessAndCheckChecker,
        'z3': lambda: Z3Checker(verbose=True),
    }
    for name, checker in checkers.items():
        print(f'Running {name} checker.')
        iconfluent_example(checker())
        not_iconfluent_example(checker())

if __name__ == '__main__':
    main()
