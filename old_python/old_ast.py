from typing import Tuple

import z3

from .env import Env

class Expr:
    def to_z3(self, env: Env) -> z3.ExprRef:
        raise NotImplementedError()

class Predicate:
    def to_z3(self, env: Env) -> z3.BoolRef:
        raise NotImplementedError()

class Assign:
    def to_z3(self, env: Env) -> Tuple[z3.BoolRef, Env]:
        raise NotImplementedError()

class And(Predicate):
    def __init__(self, lhs: Predicate, rhs: Predicate) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return z3.And(self.lhs.to_z3(env), self.rhs.to_z3(env))

class Or(Predicate):
    def __init__(self, lhs: Predicate, rhs: Predicate) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return z3.Or(self.lhs.to_z3(env), self.rhs.to_z3(env))

class Not(Predicate):
    def _init__(self, p: Predicate) -> None:
        self.p = p

    def to_z3(self, env: Env) -> z3.BoolRef:
        return z3.Not(self.p.to_z3(env))
