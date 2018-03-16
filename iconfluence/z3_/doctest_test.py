import unittest
import doctest

from . import compile
from . import version_env

def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(compile))
    tests.addTests(doctest.DocTestSuite(version_env))
    return tests

