from typing import Any, Dict

import z3

from .ast import Crdt, Expr, Type

CrdtEnv = Dict[str, Crdt]
TypeEnv = Dict[str, Type]
ValEnv = Dict[str, Any]
ExprEnv = Dict[str, Expr]
Z3ExprEnv = Dict[str, z3.ExprRef]
