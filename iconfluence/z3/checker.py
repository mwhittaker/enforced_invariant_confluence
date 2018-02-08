from .. import checker
from .. import ast

class Checker(checker.Checker):
    def check_iconfluence(self) -> checker.Decision:
        raise NotImplementedError()
