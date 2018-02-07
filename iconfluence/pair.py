from typing import Tuple

import z3

from . import ast
from .env import Env

class Expr(ast.Expr):
    # TODO: Add operator overloads.
    def join(self, other: Expr) -> 'Join':
        return Join(self, other)

class Const(Expr):
    def __init__(self, k: int) -> None:
        self.k = k

    def to_z3(self, env: Env) -> z3.ExprRef:
        return z3.Const(self.k, z3.IntSort())

class Var(Expr):
    def __init__(self, v: str, ?, ?) -> None:
        self.v = v

    def pair(self, env: Env) -> z3.ExprRef:
        return z3.Const(env.get_name(self.v), z3.IntSort())

class Add(Expr):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.ExprRef:
        return self.lhs.to_z3(env) + self.rhs.to_z3(env)

class Sub(Expr):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.ExprRef:
        return self.lhs.to_z3(env) - self.rhs.to_z3(env)

class Mul(Expr):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.ExprRef:
        return self.lhs.to_z3(env) * self.rhs.to_z3(env)

class Join(Expr):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.ExprRef:
        lhs = self.lhs.to_z3(env)
        rhs = self.rhs.to_z3(env)
        return z3.If(lhs >= rhs, lhs, rhs)

class Predicate(ast.Predicate):
    pass

class Eq(Predicate):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return self.lhs.to_z3(env) == self.rhs.to_z3(env)

class Ne(Predicate):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return self.lhs.to_z3(env) != self.rhs.to_z3(env)

class Lt(Predicate):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return self.lhs.to_z3(env) < self.rhs.to_z3(env)

class Le(Predicate):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return self.lhs.to_z3(env) <= self.rhs.to_z3(env)

class Gt(Predicate):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return self.lhs.to_z3(env) > self.rhs.to_z3(env)

class Ge(Predicate):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = lhs
        self.rhs = rhs

    def to_z3(self, env: Env) -> z3.BoolRef:
        return self.lhs.to_z3(env) >= self.rhs.to_z3(env)

class Assign(ast.Assign):
    def __init__(self, v: Var, e: Expr) -> None:
        self.v = v
        self.e = e

    def to_z3(self, env: Env) -> Tuple[z3.BoolRef, Env]:
        expr = self.e.to_z3(env)
        env = env.assign(self.v.v)
        bexpr = z3.Int(env.get_name(self.v.v)) == expr
        return (bexpr, env)

def to_z3_predicate():
    pass
