import os
import unittest


# A base class just in case we need any shared functionality like finding test files
class ParserTestBase(unittest.TestCase):
    TESTS_DIR = os.path.abspath(os.path.dirname(__file__))
    TEST_ASSETS_ROOT = os.path.join(TESTS_DIR, "assets")
