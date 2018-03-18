import unittest
import doctest

from . import interactive_checker

def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(interactive_checker))
    return tests

