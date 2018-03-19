import unittest
import doctest

from . import compile

def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(compile))
    return tests

