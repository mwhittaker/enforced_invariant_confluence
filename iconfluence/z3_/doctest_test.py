import unittest
import doctest

from . import compile
from . import model

def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(compile))
    tests.addTests(doctest.DocTestSuite(model))
    return tests

