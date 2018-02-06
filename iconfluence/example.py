from z3 import *








x = MaxIntLattice()
y = SetUnionLattice(IntSort())
z = MapLattice(IntSort(), PairSort(IntSort(), RealSort()))

tmp = x + y
x = tmp + y
y = tmp + x

x >= y

1. Commutativity
assert((>= x y))

2. Join is apply

3. 1-liconfluent

4. 1-replayable


def txn():
    x = x + 1
    y = y + 2
    tmp = x + 1
    z = tmp + 2

oracle = Oracle()
oracle.add_transaction(x = x + 1, name="")
oracle.add_transaction(y = y + 2, name="")
oracle.add_transaction(y = y.interesect(z), name="foo")
oracle.add_transaction(z = z || z)
oracle.add_invariant(x > 0)
oracle.add_invariant(z.forall(lambda x: x > 2))


class Pair:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def __add__(self, other):
        return Pair(self.x + other.x, self.y + other.y)

    def __eq__(self, other):
        return And(self.x == other.x, self.y == other.y)

def main():
    x_1 = Int('x_1')
    y_1 = Real('y_1')
    p_1 = Pair(x_1, y_1)

    x_2 = Int('x_2')
    y_2 = Real('y_2')
    p_2 = Pair(x_2, y_2)

    s = Solver()
    s.add(x_1 > y_2)
    s.add(p_1 == p_2)
    s.check()
    print(s.model())

if __name__ == '__main__':
    main()
