import unittest
import doctest

from . import arbitrary_start_checker

def load_tests(loader, tests, ignore):
    tests.addTests(doctest.DocTestSuite(arbitrary_start_checker))
    return tests

