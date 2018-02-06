from z3 import Array, BoolSort

from .lattice import Lattice

class SetUnionLattice(Lattice):
    def __init__(self, name: str, sort):
        self.xs = Array(name, sort, BoolSort())

    def __eq__(self, other):
        return Map(self.eq, self, other)
