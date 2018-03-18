import unittest
import doctest

from . import eval

def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(eval))
    return tests

