from typing import Any, Dict

from .ast import Crdt, Expr, Type

CrdtEnv = Dict[str, Crdt]
TypeEnv = Dict[str, Type]
ValEnv = Dict[str, Any]
ExprEnv = Dict[str, Expr]
