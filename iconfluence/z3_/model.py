from typing import Any, Dict, Optional, Set, TypeVar, Union

import z3

from .. import ast
from ..envs import ValEnv
from .compile import sort_to_type

A = TypeVar('A')
B = TypeVar('B')

class InfiniteSet:
    """
    An InfiniteSet is a possibly infinite set modeled by a simple if-then-else
    function. For example, the function

        def f(x):
            if x in [1, 2, 3]:
                return True
            elif x in [4, 5]:
                return False
            else:
                return False

    represents the finite set {1, 2, 3} whereas the function

        def f(x):
            if x in [1, 2, 3]:
                return True
            elif x in [4, 5]:
                return False
            else:
                return True

    represents the set {..., -1, 0, 1, 2, 3, 6, 7, 8, ...}.

    >>> x = InfiniteSet({1, 2, 3}, {4, 5}, False)
    >>> x.finite()
    True
    >>> x.get()
    {1, 2, 3}
    >>> [i in x for i in range(1, 8)]
    [True, True, True, False, False, False, False]

    >>> x = InfiniteSet({1, 2, 3}, {4, 5}, True)
    >>> x.finite()
    False
    >>> [i in x for i in range(1, 8)]
    [True, True, True, False, False, True, True]
    """
    def __init__(self, in_: Set[A], not_in_: Set[A], else_: bool) -> None:
        assert len(in_ & not_in_) == 0, (in_, not_in_)
        self.in_ = in_
        self.not_in_ = not_in_
        self.else_ = else_

    def __str__(self) -> str:
        return f'InfiniteSet({self.in_}, {self.not_in_}, {self.else_}))'

    def __repr__(self) -> str:
        return str(self)

    def __contains__(self, x: A) -> bool:
        if x in self.in_:
            return True
        elif x in self.not_in_:
            return False
        elif self.finite():
            return False
        else:
            return True

    def get(self) -> Set[A]:
        assert self.finite()
        return self.in_ - self.not_in_

    def finite(self) -> bool:
        return self.else_ == False


class InfiniteMap:
    """
    An InfiniteMap is a possibly infinite map modeled by a simple if-then-else
    function. For example, the function

        def f(x):
            if x == 1:
                return 'one'
            elif x == 4:
                return 'four'
            else:
                return None

    represents the finite map {1: 'one', 4: 'four'} whereas the function

        def f(x):
            if x == 1:
                return 'one'
            elif x == 4:
                return 'four'
            else:
                return '?'

    represents the map {..., 0:'?', 1:'one', 2:'?', 3:'?', 4:'four', ...}.

    >>> x = InfiniteMap({1: 'one', 4: 'four'}, None)
    >>> x.finite()
    True
    >>> x.get()
    {1: 'one', 4: 'four'}
    >>> [x[i] for i in range(1, 8)]
    ['one', None, None, 'four', None, None, None]

    >>> x = InfiniteMap({1: 'one', 4: 'four'}, '?')
    >>> x.finite()
    False
    >>> [x[i] for i in range(1, 8)]
    ['one', '?', '?', 'four', '?', '?', '?']
    """
    def __init__(self, d: Dict[A, B], default: Optional[B]) -> None:
        self.d = d
        self.default = default

    def __str__(self) -> str:
        return f'InfiniteMap({self.d}, {self.default})'

    def __repr__(self) -> str:
        return str(self)

    def __contains__(self, x: A) -> bool:
        if x in self.d or self.default is not None:
            return True
        else:
            return False

    def __getitem__(self, k: A) -> Optional[B]:
        if k in self.d:
            return self.d[k]
        else:
            return self.default

    def get(self) -> Dict[A, B]:
        assert self.finite()
        return self.d

    def finite(self) -> bool:
        return self.default is None


ModelValue = Union[z3.FuncInterp, z3.ExprRef]
def _translate_model_value(v: ModelValue, model: z3.ModelRef) -> Any:
    def translate(v: ModelValue) -> Any:
        return _translate_model_value(v, model)

    if isinstance(v, z3.IntNumRef):
        return v.as_long()
    elif isinstance(v, z3.BoolRef):
        assert str(v) in ["True", "False"]
        if str(v) == "True":
            return True
        else:
            return False
    elif isinstance(v, z3.DatatypeRef):
        typ = sort_to_type(v.sort())
        if isinstance(typ, ast.TTuple2):
            a, b = v.children()
            return (translate(a), translate(b))
        elif isinstance(typ, ast.TOption):
            if len(v.children()) == 0:
                return None
            else:
                return translate(v.children()[0])
        else:
            raise ValueError(f'Unknown datatype {typ}.')
    elif isinstance(v, z3.FuncInterp):
        if v.else_value().sort() == z3.BoolSort():
            # v is a set.
            in_: Set[Any] = set()
            not_in_: Set[Any] = set()

            # The last value of v.as_list() is the else_value.
            for x, in_v in v.as_list()[:-1]:
                x = translate(x)
                if in_v == z3.BoolVal(True):
                    in_.add(x)
                else:
                    assert in_v == z3.BoolVal(False), in_v
                    not_in_.add(x)
            return InfiniteSet(in_, not_in_, v.else_value())
        else:
            # v is a map.
            d: Dict[Any, Any] = dict()

            # The last value of v.as_list() is the else_value.
            for key, val in v.as_list()[:-1]:
                key = translate(key)
                val = translate(val)
                assert key not in d, (key, d)
                d[key] = val
            return InfiniteMap(d, v.else_value())
    elif isinstance(v, z3.ArrayRef):
        assert v.decl().name() == 'as-array', v.decl().name()
        assert len(v.decl().params()) == 1, v.decl.params()
        return translate(model[v.decl().params()[0]])
    else:
        raise ValueError(f'Unknown model value {v} of type {type(v)}.')

def model_to_state(m: z3.ModelRef, vs: Set[str]) -> ValEnv:
    state: ValEnv = dict()
    for x in m:
        if x.name() in vs:
            assert x.name() not in state, (x, state)
            state[x.name()] = _translate_model_value(m[x], m)
    return state
