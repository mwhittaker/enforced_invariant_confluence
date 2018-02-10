from typing import Any, List, Set

class AstNode:
    def __eq__(self, other) -> bool:
        if isinstance(self, other.__class__):
            return self.__dict__ == other.__dict__
        return NotImplemented

    def __hash__(self) -> int:
        return hash(tuple(sorted(self.__dict__.items())))

    def __repr__(self) -> str:
        d = self.__dict__
        fields = ", ".join(f'{k}={v}' for (k, v) in sorted(d.items()))
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

class TMap(Type):
    def __init__(self, a: Type, b: Type) -> None:
        self.a = a
        self.b = b

    def __str__(self) -> str:
        return f'Map[{str(self.a)}, {str(self.b)}]'

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
    def __init__(self, a: Crdt) -> None:
        self.a = a

    def to_type(self) -> Type:
        return TSet(self.a.to_type())

class CSetIntersect(Crdt):
    def __init__(self, a: Crdt) -> None:
        self.a = a

    def to_type(self) -> Type:
        return TSet(self.a.to_type())

class CMap(Crdt):
    def __init__(self, a: Type, b: Crdt) -> None:
        self.a = a
        self.b = b

    def to_type(self) -> Type:
        return TMap(self.a, self.b.to_type())

# Expressions ##################################################################
class Expr(AstNode):
    def __init__(self) -> None:
        self.typ: Type = None

    def _coerce(self, x: Any) -> 'Expr':
        # Note that isinstance(True, int) is true, so we have to check for
        # bools before we check for ints.
        if isinstance(x, bool):
            return EBool(x)
        elif isinstance(x, int):
            return EInt(x)
        elif isinstance(x, tuple) and len(x) == 2:
            return ETuple2(self._coerce(x[0]), self._coerce(x[1]))
        elif isinstance(x, set):
            return ESet({self._coerce(e) for e in x})
        elif isinstance(x, Expr):
            return x
        else:
            raise ValueError(f'Unrecognized expression {x}.')

    def __getitem__(self, i: int) -> 'Expr':
        if i == 0:
            return ETuple2First(self)
        elif i == 1:
            return ETuple2Second(self)
        else:
            raise ValueError(f'Unsupported index {i}.')

    def __add__(self, rhs: Any) -> 'Expr':
        return EIntAdd(self, self._coerce(rhs))

    def __radd__(self, lhs: Any) -> 'Expr':
        return self._coerce(lhs) + self

    def __sub__(self, rhs: Any) -> 'Expr':
        return EIntSub(self, self._coerce(rhs))

    def __rsub__(self, lhs: Any) -> 'Expr':
        return self._coerce(lhs) - self

    def __mul__(self, rhs: Any) -> 'Expr':
        return EIntMul(self, self._coerce(rhs))

    def __rmul__(self, lhs: Any) -> 'Expr':
        return self._coerce(lhs) * self

    def __and__(self, rhs: Any) -> 'Expr':
        return EBoolAnd(self, self._coerce(rhs))

    def __rand__(self, lhs: Any) -> 'Expr':
        return self._coerce(lhs) * self

    def __or__(self, rhs: Any) -> 'Expr':
        return EBoolOr(self, self._coerce(rhs))

    def __ror__(self, lhs: Any) -> 'Expr':
        return self._coerce(lhs) | self

    def __rshift__(self, rhs: Any) -> 'Expr':
        return EBoolImpl(self, self._coerce(rhs))

    def __rrshift__(self, lhs: Any) -> 'Expr':
        return self._coerce(lhs) | self

    def union(self, lhs: Any) -> 'Expr':
        return ESetUnion(self, self._coerce(lhs))

    def intersect(self, lhs: Any) -> 'Expr':
        return ESetIntersect(self, self._coerce(lhs))

    def diff(self, lhs: Any) -> 'Expr':
        return ESetDiff(self, self._coerce(lhs))

    def contains(self, x: Any) -> 'Expr':
        return ESetContains(self, self._coerce(x))

    def eq(self, lhs: Any) -> 'Expr':
        return EEq(self, self._coerce(lhs))

    def ne(self, lhs: Any) -> 'Expr':
        return ENe(self, self._coerce(lhs))

    def __lt__(self, lhs: Any) -> 'Expr':
        return EIntLt(self, self._coerce(lhs))

    def __le__(self, lhs: Any) -> 'Expr':
        return EIntLe(self, self._coerce(lhs))

    def __gt__(self, lhs: Any) -> 'Expr':
        return EIntGt(self, self._coerce(lhs))

    def __ge__(self, lhs: Any) -> 'Expr':
        return EIntGe(self, self._coerce(lhs))

class EVar(Expr):
    def __init__(self, x: str) -> None:
        self.x = x

    def assign(self, e: Expr) -> 'SAssign':
        return SAssign(self, e)

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
    def __init__(self, a: Expr, b: Expr) -> None:
        self.a = self._coerce(a)
        self.b = self._coerce(b)

    def __str__(self) -> str:
        return f'({str(self.a)}, {str(self.b)})'

class ESet(Expr):
    def __init__(self, xs: Set[Expr]) -> None:
        self.xs = {self._coerce(x) for x in xs}

    def __str__(self) -> str:
        return '{' + ', '.join(str(x) for x in self.xs) + '}'

class EUnaryOp(Expr):
    def __init__(self, x: Expr) -> None:
        self.x = self._coerce(x)

class ETuple2First(EUnaryOp):
    def __str__(self) -> str:
        return f'({str(self.x)})[0]'

class ETuple2Second(EUnaryOp):
    def __str__(self) -> str:
        return f'({str(self.x)})[1]'

class EBinaryOp(Expr):
    def __init__(self, lhs: Expr, rhs: Expr) -> None:
        self.lhs = self._coerce(lhs)
        self.rhs = self._coerce(rhs)

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

class EMapGet(EBinaryOp):
    def __str__(self) -> str:
        return f'{str(self.lhs)}[{str(self.rhs)})]'

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

class ETernaryOp(Expr):
    def __init__(self, a: Expr, b: Expr, c: Expr) -> None:
        self.a = self._coerce(a)
        self.b = self._coerce(b)
        self.c = self._coerce(c)

class EMapSet(ETernaryOp):
    def __str__(self) -> str:
        return f'({str(self.a)}[{str(self.b)}] <- {str(self.c)})'

# Statements ###################################################################
class Stmt(AstNode):
    pass

class SAssign(Stmt):
    def __init__(self, x: EVar, e: Expr) -> None:
        self.x = x
        self.e = e

# Transactions #################################################################
Transaction = List[Stmt]

# Invariants ###################################################################
Invariant = Expr
