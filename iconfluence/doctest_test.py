import unittest
import doctest

from . import ast
from . import eval

def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(ast))
    tests.addTests(doctest.DocTestSuite(eval))
    return tests

