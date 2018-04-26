from iconfluence import *

from .parser import get_checker

"""
This example doesn't have any significance except for the fact that it uses
every datatype. This is useful to debug the Z3 code generation and model
extraction.

    PYTHONPATH=. python -i -m examples.all_datatypes
"""

checker = get_checker()
int_max = checker.int_max('int_max', 0)
int_min = checker.int_min('int_min', 0)
bool_or = checker.bool_or('bool_or', False)
bool_and = checker.bool_and('bool_and', True)
tuple2 = checker.tuple2('tuple2', CIntMax(), CSetUnion(TInt()), (1, {1, 2}))
set_union = checker.set_union('set_union', TInt(), {1})
set_intersect = checker.set_intersect('set_intersect', TInt(), {1})
map = checker.map('map', TInt(), CIntMax(), {1: 42})
option = checker.option('option', CIntMax(), ENone(TInt()))
top = checker.top('top', TInt(), ENone(TInt()))
checker.add_invariant('dummy', int_max - int_min <= 10)
