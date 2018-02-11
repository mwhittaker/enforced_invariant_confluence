from typing import Any, List, Set, Union

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
        return f'Tuple2[{str(self.a)}, {str(self.b)}]'

class TSet(Type):
    def __init__(self, a: Type) -> None:
        self.a = a

    def __str__(self) -> str:
        return f'Set[{str(self.a)}]'

class TOption(Type):
    def __init__(self, a: Type) -> None:
        self.a = a

    def __str__(self) -> str:
        return f'Option[{str(self.a)}]'

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

# Expressions ##################################################################
Coercible = Union[bool, int, tuple, set, 'Expr']

def _coerce(x: Coercible) -> 'Expr':
    # Note that isinstance(True, int) is true, so we have to check for
    # bools before we check for ints.
    if isinstance(x, bool):
        return EBool(x)
    elif isinstance(x, int):
        return EInt(x)
    elif isinstance(x, tuple) and len(x) == 2:
        return ETuple2(_coerce(x[0]), _coerce(x[1]))
    elif isinstance(x, set):
        return ESet({_coerce(e) for e in x})
    elif isinstance(x, Expr):
        return x
    else:
        raise ValueError(f'Unrecognized expression {x}.')

class Expr(AstNode):
    def __init__(self) -> None:
        self.typ: Type = None

    def __getitem__(self, i: int) -> 'Expr':
        if i == 0:
            return ETuple2First(self)
        elif i == 1:
            return ETuple2Second(self)
        else:
            raise ValueError(f'Unsupported index {i}.')

    def is_none(self) -> 'Expr':
        return EOptionIsNone(self)

    def is_some(self) -> 'Expr':
        return EOptionIsSome(self)

    def unwrap(self) -> 'Expr':
        return EOptionUnwrap(self)

    def __add__(self, rhs: Coercible) -> 'Expr':
        return EIntAdd(self, _coerce(rhs))

    def __radd__(self, lhs: Coercible) -> 'Expr':
        return _coerce(lhs) + self

    def __sub__(self, rhs: Coercible) -> 'Expr':
        return EIntSub(self, _coerce(rhs))

    def __rsub__(self, lhs: Coercible) -> 'Expr':
        return _coerce(lhs) - self

    def __mul__(self, rhs: Coercible) -> 'Expr':
        return EIntMul(self, _coerce(rhs))

    def __rmul__(self, lhs: Coercible) -> 'Expr':
        return _coerce(lhs) * self

    def __and__(self, rhs: Coercible) -> 'Expr':
        return EBoolAnd(self, _coerce(rhs))

    def __rand__(self, lhs: Coercible) -> 'Expr':
        return _coerce(lhs) * self

    def __or__(self, rhs: Coercible) -> 'Expr':
        return EBoolOr(self, _coerce(rhs))

    def __ror__(self, lhs: Coercible) -> 'Expr':
        return _coerce(lhs) | self

    def __rshift__(self, rhs: Coercible) -> 'Expr':
        return EBoolImpl(self, _coerce(rhs))

    def __rrshift__(self, lhs: Coercible) -> 'Expr':
        return _coerce(lhs) | self

    def union(self, lhs: Coercible) -> 'Expr':
        return ESetUnion(self, _coerce(lhs))

    def intersect(self, lhs: Coercible) -> 'Expr':
        return ESetIntersect(self, _coerce(lhs))

    def diff(self, lhs: Coercible) -> 'Expr':
        return ESetDiff(self, _coerce(lhs))

    def contains(self, x: Coercible) -> 'Expr':
        return ESetContains(self, _coerce(x))

    def eq(self, lhs: Coercible) -> 'Expr':
        return EEq(self, _coerce(lhs))

    def ne(self, lhs: Coercible) -> 'Expr':
        return ENe(self, _coerce(lhs))

    def __lt__(self, lhs: Coercible) -> 'Expr':
        return EIntLt(self, _coerce(lhs))

    def __le__(self, lhs: Coercible) -> 'Expr':
        return EIntLe(self, _coerce(lhs))

    def __gt__(self, lhs: Coercible) -> 'Expr':
        return EIntGt(self, _coerce(lhs))

    def __ge__(self, lhs: Coercible) -> 'Expr':
        return EIntGe(self, _coerce(lhs))

class EVar(Expr):
    def __init__(self, x: str) -> None:
        self.x = x

    def assign(self, e: Coercible) -> 'SAssign':
        return SAssign(self, _coerce(e))

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
        self.a = _coerce(a)
        self.b = _coerce(b)

    def __str__(self) -> str:
        return f'({str(self.a)}, {str(self.b)})'

class ESet(Expr):
    def __init__(self, xs: Set[Coercible]) -> None:
        self.xs = {_coerce(x) for x in xs}

    def __str__(self) -> str:
        return '{' + ', '.join(str(x) for x in self.xs) + '}'

class ENone(Expr):
    def __init__(self, t: Type) -> None:
        self.t = t

    def __str__(self) -> str:
        return 'None'

class ESome(Expr):
    def __init__(self, x: Coercible) -> None:
        self.x = _coerce(x)

    def __str__(self) -> str:
        return f'Some({str(self.x)})'

class EUnaryOp(Expr):
    def __init__(self, x: Coercible) -> None:
        self.x = _coerce(x)

class ETuple2First(EUnaryOp):
    def __str__(self) -> str:
        return f'({str(self.x)})[0]'

class ETuple2Second(EUnaryOp):
    def __str__(self) -> str:
        return f'({str(self.x)})[1]'

class EOptionIsNone(EUnaryOp):
    def __str__(self) -> str:
        return f'({str(self.x)} is None)'

class EOptionIsSome(EUnaryOp):
    def __str__(self) -> str:
        return f'({str(self.x)} is not None)'

class EOptionUnwrap(EUnaryOp):
    def __str__(self) -> str:
        return f'({str(self.x)}.unwrap())'

class EBinaryOp(Expr):
    def __init__(self, lhs: Coercible, rhs: Coercible) -> None:
        self.lhs = _coerce(lhs)
        self.rhs = _coerce(rhs)

class EIntAdd(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} + {str(self.rhs)})'

class EIntSub(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} - {str(self.rhs)})'

class EIntMul(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} * {str(self.rhs)})'

class EBoolAnd(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} & {str(self.rhs)})'

class EBoolOr(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} | {str(self.rhs)})'

class EBoolImpl(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} >> {str(self.rhs)})'

class ESetUnion(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} union {str(self.rhs)})'

class ESetIntersect(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} intersect {str(self.rhs)})'

class ESetDiff(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} diff {str(self.rhs)})'

class ESetContains(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.rhs)} in {str(self.lhs)})'

class EEq(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} == {str(self.rhs)})'

class ENe(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} != {str(self.rhs)})'

class EIntLt(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} < {str(self.rhs)})'

class EIntLe(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} <= {str(self.rhs)})'

class EIntGt(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} > {str(self.rhs)})'

class EIntGe(EBinaryOp):
    def __str__(self) -> str:
        return f'({str(self.lhs)} >= {str(self.rhs)})'

# Statements ###################################################################
class Stmt(AstNode):
    pass

class SAssign(Stmt):
    def __init__(self, x: EVar, e: Coercible) -> None:
        self.x = x
        self.e = _coerce(e)

# Transactions #################################################################
Transaction = List[Stmt]

# Invariants ###################################################################
Invariant = Expr
