from typing import Dict, Tuple

from .. import ast
from .. import typecheck
from ..ast import Coercible, Crdt, Invariant, Transaction, Type
from ..checker import Decision
from ..envs import CrdtEnv, ExprEnv, TypeEnv, ValEnv
from ..eval import eval_expr

VarTriple = Tuple[ast.EVar, ast.EVar, ast.EVar]

def _wrap_string_lhs(s: str) -> str:
    """
    >>> _wrap_string_lhs('foo')
    'foo_lhs'
    """
    return s + '_lhs'

def _wrap_string_rhs(s: str) -> str:
    """
    >>> _wrap_string_rhs('foo')
    'foo_rhs'
    """
    return s + '_rhs'

def _unwrap_string_lhs(s: str) -> str:
    """
    >>> _unwrap_string_lhs('foo_lhs')
    'foo'
    """
    assert s[-4:] == '_lhs', s
    return s[:-4]

def _unwrap_string_rhs(s: str) -> str:
    """
    >>> _unwrap_string_rhs('foo_rhs')
    'foo'
    """
    assert s[-4:] == '_rhs', s
    return s[:-4]

def _wrap_var_lhs(v: ast.EVar) -> ast.EVar:
    """
    >>> x = ast.EVar('x')
    >>> x.typ = ast.TInt()
    >>> repr(_wrap_var_lhs(x))
    "EVar(typ=TInt(), x='x_lhs')"
    """
    v_wrapped = ast.EVar(_wrap_string_lhs(v.x))
    v_wrapped.typ = v.typ
    return v_wrapped

def _wrap_var_rhs(v: ast.EVar) -> ast.EVar:
    """
    >>> x = ast.EVar('x')
    >>> x.typ = ast.TInt()
    >>> repr(_wrap_var_rhs(x))
    "EVar(typ=TInt(), x='x_rhs')"
    """
    v_wrapped = ast.EVar(_wrap_string_rhs(v.x))
    v_wrapped.typ = v.typ
    return v_wrapped

def _unwrap_var_lhs(v: ast.EVar) -> ast.EVar:
    """
    >>> x = ast.EVar('x_lhs')
    >>> x.typ = ast.TInt()
    >>> repr(_unwrap_var_lhs(x))
    "EVar(typ=TInt(), x='x')"
    """
    v_unwrapped = ast.EVar(_unwrap_string_lhs(v.x))
    v_unwrapped.typ = v.typ
    return v_unwrapped

def _unwrap_var_rhs(v: ast.EVar) -> ast.EVar:
    """
    >>> x = ast.EVar('x_rhs')
    >>> x.typ = ast.TInt()
    >>> repr(_unwrap_var_rhs(x))
    "EVar(typ=TInt(), x='x')"
    """
    v_unwrapped = ast.EVar(_unwrap_string_rhs(v.x))
    v_unwrapped.typ = v.typ
    return v_unwrapped

class ArbitraryStartChecker:
    """
    TODO(mwhittaker): Document.
    """
    def __init__(self):
        self.crdt_env: CrdtEnv = dict()
        self.type_env: TypeEnv = dict()
        self.transactions: Dict[str, Transaction] = dict()
        self.invariants: Dict[str, Invariant] = dict()

    def __str__(self):
        strings = []

        strings.append('State')
        for name in self.crdt_env:
            strings.append(f'  {name}: {self.crdt_env[name]}')

        strings += ['Invariants']
        for (name, inv) in self.invariants.items():
            strings.append(f'  {name} == {inv}')

        strings += ['Transactions']
        for (name, txn) in self.transactions.items():
            strings.append(f'  def {name}():')
            for s in txn:
                strings.append(f'    {s}')

        return '\n'.join(strings)

    def __repr__(self):
        return str(self)

    def _register_var(self, name: str, crdt: Crdt) -> VarTriple:
        # Ensure that variable names are unique.
        assert name not in self.crdt_env, (name, self.crdt_env)
        assert name not in self.type_env, (name, self.type_env)

        typ = crdt.to_type()
        self.crdt_env[name] = crdt
        self.type_env[name] = typ

        var = ast.EVar(name)
        var.typ = typ
        return var, _wrap_var_lhs(var), _wrap_var_rhs(var)

    # TODO(mwhittaker): Right now, temporary variables are joined together and
    # included when checking for properties like commutativity. Think about
    # whether this is right.

    def int_max(self, name: str) -> VarTriple:
        return self._register_var(name, ast.CIntMax())

    def int_min(self, name: str) -> VarTriple:
        return self._register_var(name, ast.CIntMin())

    def bool_or(self, name: str) -> VarTriple:
        return self._register_var(name, ast.CBoolOr())

    def bool_and(self, name: str) -> VarTriple:
        return self._register_var(name, ast.CBoolAnd())

    def tuple2(self, name: str, a: Crdt, b: Crdt) -> VarTriple:
        return self._register_var(name, ast.CTuple2(a, b))

    def set_union(self, name: str, a: Type) -> VarTriple:
        return self._register_var(name, ast.CSetUnion(a))

    def set_intersect(self, name: str, a: Type) -> VarTriple:
        return self._register_var(name, ast.CSetIntersect(a))

    def map(self, name: str, a: Type, b: Crdt) -> VarTriple:
        return self._register_var(name, ast.CMap(a, b))

    def option(self, name: str, a: Crdt) -> VarTriple:
        return self._register_var(name, ast.COption(a))

    def add_transaction(self, name: str, txn: Transaction) -> None:
        assert name not in self.transactions, (name, self.transactions)
        txn = typecheck.typecheck_txn(txn, self.type_env)
        self.transactions[name] = txn

    def add_invariant(self, name: str, inv: Invariant) -> None:
        assert name not in self.invariants, (name, self.invariants)
        inv = typecheck.typecheck_invariant(inv, self.type_env)
        self.invariants[name] = inv

    def check(self) -> Decision:
        raise NotImplementedError()
