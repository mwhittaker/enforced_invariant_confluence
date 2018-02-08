# import iconfluence
from iconfluence.guess_and_check.checker import Checker

def iconfluent_example() -> None:
    checker = Checker()

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

    # Invariants.
    checker.add_invariant('x_eq_y', x.eq(y))

    # This should always print UNKNOWN or YES.
    print(checker.check_iconfluence())

def not_iconfluent_example() -> None:
    checker = Checker()

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
    iconfluent_example()
    not_iconfluent_example()

if __name__ == '__main__':
    main()
