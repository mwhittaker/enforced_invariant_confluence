from enum import Enum

# Note this can't be in ast because of a cyclic dep.
class Type(Enum):
    MAX_INT = "max_int"
