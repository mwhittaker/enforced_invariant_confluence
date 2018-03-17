from typing import Any, Dict, List, Set, Union

class AstNode:
    def __eq__(self, other) -> bool:
        if isinstance(self, other.__class__):
            return self.__dict__ == other.__dict__
        return NotImplemented

    def __hash__(self) -> int:
        return hash(tuple(sorted(self.__dict__.items())))

    def __repr__(self) -> str:
        d = self.__dict__
        fields = ", ".join(f'{k}={repr(v)}' for (k, v) in sorted(d.items()))
        return f'{self.__class__.__name__}({fields})'

    def __str__(self) -> str:
        return self.__repr__()

# Types ########################################################################
class Type(AstNode):
    pass

class TInt(Type):
    def __str__(self) -> str:
        return 'Int'

class TBool(Type):
    def __str__(self) -> str:
        return 'Bool'

class TTuple2(Type):
    def __init__(self, a: Type, b: Type) -> None:
        self.a = a
        self.b = b

    def __str__(self) -> str:
        return f'Tuple2[{self.a}, {self.b}]'

class TSet(Type):
    def __init__(self, a: Type) -> None:
        self.a = a

    def __str__(self) -> str:
        return f'Set[{self.a}]'

class TOption(Type):
    def __init__(self, a: Type) -> None:
        self.a = a

    def __str__(self) -> str:
        return f'Option[{self.a}]'

class TMap(Type):
    def __init__(self, a: Type, b: Type) -> None:
        self.a = a
        self.b = b

    def __str__(self) -> str:
        return f'Map[{self.a}, {self.b}]'

# CRDTs ########################################################################
class Crdt(AstNode):
    def to_type(self) -> Type:
        raise NotImplementedError()

class CIntMax(Crdt):
    def to_type(self) -> Type:
        return TInt()

class CIntMin(Crdt):
    def to_type(self) -> Type:
        return TInt()

class CBoolOr(Crdt):
    def to_type(self) -> Type:
        return TBool()

class CBoolAnd(Crdt):
    def to_type(self) -> Type:
        return TBool()

class CTuple2(Crdt):
    def __init__(self, a: Crdt, b: Crdt) -> None:
        self.a = a
        self.b = b

    def to_type(self) -> Type:
        return TTuple2(self.a.to_type(), self.b.to_type())

class CSetUnion(Crdt):
    def __init__(self, a: Type) -> None:
        self.a = a

    def to_type(self) -> Type:
        return TSet(self.a)

class CSetIntersect(Crdt):
    def __init__(self, a: Type) -> None:
        self.a = a

    def to_type(self) -> Type:
        return TSet(self.a)

class COption(Crdt):
    def __init__(self, a: Crdt) -> None:
        self.a = a

    def to_type(self) -> Type:
        return TOption(self.a.to_type())

class CMap(Crdt):
    def __init__(self, a: Type, b: Crdt) -> None:
        self.a = a
        self.b = b

    def to_type(self) -> Type:
        return TMap(self.a, self.b.to_type())

# Expressions ##################################################################
Coercible = Union[bool, int, tuple, set, dict, 'Expr']

def coerce(x: Coercible) -> 'Expr':
    # Note that isinstance(True, int) is true, so we have to check for
    # bools before we check for ints.
    if isinstance(x, bool):
        return EBool(x)
    elif isinstance(x, int):
        return EInt(x)
    elif isinstance(x, tuple) and len(x) == 2:
        return ETuple2(coerce(x[0]), coerce(x[1]))
    elif isinstance(x, set):
        return ESet({coerce(e) for e in x})
    elif isinstance(x, dict):
        return EMap({coerce(k): coerce(v) for k, v in x.items()})
    elif isinstance(x, Expr):
        return x
    else:
        raise ValueError(f'Unrecognized expression {x}.')

class Expr(AstNode):
    def __init__(self) -> None:
        self.typ: Type = None

    def is_none(self) -> 'Expr':
        return EOptionIsNone(self)

    def is_some(self) -> 'Expr':
        return EOptionIsSome(self)

    def unwrap(self) -> 'Expr':
        return EOptionUnwrap(self)

    def __add__(self, rhs: Coercible) -> 'Expr':
        return EIntAdd(self, coerce(rhs))

    def __radd__(self, lhs: Coercible) -> 'Expr':
        return coerce(lhs) + self

    def __sub__(self, rhs: Coercible) -> 'Expr':
        return EIntSub(self, coerce(rhs))

    def __rsub__(self, lhs: Coercible) -> 'Expr':
        return coerce(lhs) - self

    def __mul__(self, rhs: Coercible) -> 'Expr':
        return EIntMul(self, coerce(rhs))

    def __rmul__(self, lhs: Coercible) -> 'Expr':
        return coerce(lhs) * self

    def __and__(self, rhs: Coercible) -> 'Expr':
        return EBoolAnd(self, coerce(rhs))

    def __rand__(self, lhs: Coercible) -> 'Expr':
        return coerce(lhs) * self

    def __or__(self, rhs: Coercible) -> 'Expr':
        return EBoolOr(self, coerce(rhs))

    def __ror__(self, lhs: Coercible) -> 'Expr':
        return coerce(lhs) | self

    def __rshift__(self, rhs: Coercible) -> 'Expr':
        return EBoolImpl(self, coerce(rhs))

    def __rrshift__(self, lhs: Coercible) -> 'Expr':
        return coerce(lhs) | self

    def first(self) -> 'Expr':
        return ETuple2First(self)

    def second(self) -> 'Expr':
        return ETuple2Second(self)

    def union(self, lhs: Coercible) -> 'Expr':
        return ESetUnion(self, coerce(lhs))

    def intersect(self, lhs: Coercible) -> 'Expr':
        return ESetIntersect(self, coerce(lhs))

    def diff(self, lhs: Coercible) -> 'Expr':
        return ESetDiff(self, coerce(lhs))

    def subseteq(self, lhs: Coercible) -> 'Expr':
        return ESetSubsetEq(self, coerce(lhs))

    def contains(self, x: Coercible) -> 'Expr':
        return ESetContains(self, coerce(x))

    def contains_key(self, x: Coercible) -> 'Expr':
        return EMapContainsKey(self, coerce(x))

    def __getitem__(self, x: Coercible) -> 'Expr':
        return EMapGet(self, coerce(x))

    def set(self, k: Coercible, v: Coercible) -> 'Expr':
        return EMapSet(self, k, v)

    def eq(self, lhs: Coercible) -> 'Expr':
        return EEq(self, coerce(lhs))

    def ne(self, lhs: Coercible) -> 'Expr':
        return ENe(self, coerce(lhs))

    def __lt__(self, lhs: Coercible) -> 'Expr':
        return EIntLt(self, coerce(lhs))

    def __le__(self, lhs: Coercible) -> 'Expr':
        return EIntLe(self, coerce(lhs))

    def __gt__(self, lhs: Coercible) -> 'Expr':
        return EIntGt(self, coerce(lhs))

    def __ge__(self, lhs: Coercible) -> 'Expr':
        return EIntGe(self, coerce(lhs))

class EVar(Expr):
    def __init__(self, x: str) -> None:
        self.x = x

    def assign(self, e: Coercible) -> 'SAssign':
        return SAssign(self, coerce(e))

    def __str__(self) -> str:
        return self.x

class EInt(Expr):
    def __init__(self, x: int) -> None:
        self.x = x

    def __str__(self) -> str:
        return str(self.x)

class EBool(Expr):
    def __init__(self, b: bool) -> None:
        self.x = b

    def __str__(self) -> str:
        return str(self.x)

class ETuple2(Expr):
    def __init__(self, a: Coercible, b: Coercible) -> None:
        self.a = coerce(a)
        self.b = coerce(b)

    def __str__(self) -> str:
        return f'({self.a}, {self.b})'

class EEmptySet(Expr):
    def __init__(self, t: Type) -> None:
        self.t = t

    def __str__(self) -> str:
        return '{}'

class ESet(Expr):
    def __init__(self, xs: Set[Coercible]) -> None:
        self.xs = {coerce(x) for x in xs}

    def __str__(self) -> str:
        return '{' + ', '.join(str(x) for x in self.xs) + '}'

class ENone(Expr):
    def __init__(self, t: Type) -> None:
        self.t = t

    def __str__(self) -> str:
        return 'None'

class ESome(Expr):
    def __init__(self, x: Coercible) -> None:
        self.x = coerce(x)

    def __str__(self) -> str:
        return f'Some({self.x})'

class EEmptyMap(Expr):
    def __init__(self, k: Type, v: Type) -> None:
        self.k = k
        self.v = v

class EMap(Expr):
    def __init__(self, kvs: Dict[Coercible, Coercible]) -> None:
        self.kvs = {coerce(k): coerce(v) for k, v in kvs.items()}

    def __str__(self) -> str:
        return '{' + ', '.join(f'{k}: {v}' for k, v in self.kvs.items()) + '}'

class EUnaryOp(Expr):
    def __init__(self, x: Coercible) -> None:
        self.x = coerce(x)

class ETuple2First(EUnaryOp):
    def __str__(self) -> str:
        return f'({self.x}).first()'

class ETuple2Second(EUnaryOp):
    def __str__(self) -> str:
        return f'({self.x}).second()'

class EOptionIsNone(EUnaryOp):
    def __str__(self) -> str:
        return f'({self.x} is None)'

class EOptionIsSome(EUnaryOp):
    def __str__(self) -> str:
        return f'({self.x} is not None)'

class EOptionUnwrap(EUnaryOp):
    def __str__(self) -> str:
        return f'({self.x}.unwrap())'

class EBinaryOp(Expr):
    def __init__(self, lhs: Coercible, rhs: Coercible) -> None:
        self.lhs = coerce(lhs)
        self.rhs = coerce(rhs)

class EIntAdd(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} + {self.rhs})'

class EIntSub(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} - {self.rhs})'

class EIntMul(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} * {self.rhs})'

class EBoolAnd(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} & {self.rhs})'

class EBoolOr(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} | {self.rhs})'

class EBoolImpl(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} >> {self.rhs})'

class ESetUnion(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} union {self.rhs})'

class ESetIntersect(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} intersect {self.rhs})'

class ESetDiff(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} diff {self.rhs})'

class ESetSubsetEq(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} subseteq {self.rhs})'

class ESetContains(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.rhs} in {self.lhs})'

class EMapContainsKey(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.rhs} in {self.lhs})'

class EMapGet(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs}[{self.rhs}])'

class EEq(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} == {self.rhs})'

class ENe(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} != {self.rhs})'

class EIntLt(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} < {self.rhs})'

class EIntLe(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} <= {self.rhs})'

class EIntGt(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} > {self.rhs})'

class EIntGe(EBinaryOp):
    def __str__(self) -> str:
        return f'({self.lhs} >= {self.rhs})'

class ETernaryOp(Expr):
    def __init__(self, a: Coercible, b: Coercible, c: Coercible) -> None:
        self.a = coerce(a)
        self.b = coerce(b)
        self.c = coerce(c)

class EMapSet(ETernaryOp):
    def __str__(self) -> str:
        return f'({self.a}[{self.b}] <- {self.c})'

class EIf(ETernaryOp):
    def __str__(self) -> str:
        return f'(if ({self.a}) then {self.b} else {self.c})'

# Statements ###################################################################
class Stmt(AstNode):
    pass

class SAssign(Stmt):
    def __init__(self, x: EVar, e: Coercible) -> None:
        self.x = x
        self.e = coerce(e)

    def __str__(self) -> str:
        return f'{self.x} := {self.e}'

# Transactions #################################################################
Transaction = List[Stmt]

# Invariants ###################################################################
Invariant = Expr
