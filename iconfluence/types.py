from enum import Enum

# Note this can't be in ast because of a cyclic dep.
class Type(Enum):
    MAX_INT = "max_int"

# and then CRDTs?
# Int
# Bool
# Set[T]
# Map[A, B]
# Tuple0[]
# Tuple1[A]
# Tuple2[A, B]
# Tuple3[A, B, C]
# Tuple4[A, B, C, D]
# Tuple5[A, B, C, D, E]
# Tuple6[A, B, C, D, E, F]


