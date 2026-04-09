import sys
import typing
import unittest

from data_types import Asset, FoundationalType, TimeCode, Token, type_hint
from data_types.tests import harness


class TestAssetInvalid(unittest.TestCase):
    def test_assert(self):
        with self.assertRaises(ValueError):
            Asset("\u0000")


class TestAssetEmpty(unittest.TestCase):
    def setUp(self):
        self.value = Asset()

    def test_eq(self):
        self.assertEqual(self.value, "")
        self.assertEqual(self.value, self.value)

    def test_str(self):
        self.assertEqual(str(self.value), "")

    def test_exercise_repr(self):
        repr(self.value)


class TestTokenEmpty(unittest.TestCase):
    def setUp(self):
        self.value = Token()

    def test_is(self):
        self.assertIs(self.value, Token())
        self.assertIs(self.value, Token(""))

    def test_equal(self):
        self.assertEqual(self.value, Token())
        self.assertEqual(self.value, Token(""))


class TestTokenNonempty(unittest.TestCase):
    def setUp(self):
        self.values = [Token("hello"), Token("world")]

    def test_is(self):
        for value in self.values:
            with self.subTest(value):
                self.assertIsNotNone(value)
                self.assertIs(value, Token(str(value)))
                self.assertIsNot(value, Token(str(value)[:-1]))
                self.assertIsNot(value, Token(f"{str(value)}_suffix"))

    def test_equal(self):
        for value in self.values:
            with self.subTest(value):
                self.assertEqual(value, Token(str(value)))
                self.assertNotEqual(value, Token(str(value)[:-1]))
                self.assertNotEqual(value, Token(f"{str(value)}_suffix"))

    def test_hash(self):
        for value in self.values:
            with self.subTest(value):
                self.assertEqual(hash(value), hash(Token(str(value))))

    def test_exercise_repr(self):
        for value in self.values:
            with self.subTest(value):
                repr(value)


class TestTimeCodeDefault(unittest.TestCase):
    def setUp(self):
        self.value = TimeCode()

    def test_str(self):
        self.assertEqual(str(self.value), "<Default>")

    def test_equal(self):
        self.assertEqual(self.value, TimeCode())
        self.assertNotEqual(self.value, TimeCode(0.0))

    def test_hash(self):
        self.assertEqual(hash(self.value), hash(TimeCode()))

    def test_less(self):
        self.assertLessEqual(self.value, TimeCode())
        self.assertLess(self.value, TimeCode(sys.float_info.min))
        self.assertLess(self.value, TimeCode(0.0))

    def test_exercise_repr(self):
        repr(self.value)


class TestTimeCodeNonDefault(unittest.TestCase):
    def setUp(self):
        self.values = [TimeCode(0.0), TimeCode(-100.0), TimeCode(100.0)]

    def test_str(self):
        for value in self.values:
            with self.subTest(value):
                self.assertEqual(str(value), str(float(value)))

    def test_equal(self):
        for value in self.values:
            with self.subTest(value):
                self.assertEqual(value, TimeCode(float(value)))
                self.assertNotEqual(value, TimeCode())
                self.assertNotEqual(value, TimeCode(float(value) + 1.0))
                self.assertNotEqual(value, TimeCode(float(value) - 1.0))

    def test_hash(self):
        for value in self.values:
            with self.subTest(value):
                self.assertEqual(hash(value), hash(TimeCode(float(value))))

    def test_less(self):
        for value in self.values:
            with self.subTest(value):
                self.assertLessEqual(value, TimeCode(float(value)))
                self.assertLess(value, TimeCode(float(value) + 1.0))
                self.assertGreater(value, TimeCode())


class TestFoundationalDataTypes(harness.TestFoundationalDataTypes):
    """Extracts foundational data type from annotated union type: FoundationalType"""

    def setUp(self):
        super().setUp()
        self._name_alias_cache = {}
        self._alias_role_cache = {}

        for data_type in typing.get_args(FoundationalType):
            if (hint := type_hint(data_type)) is None:
                raise TypeError("All foundational data types should have a hint.")
            if hint.name in self._name_alias_cache:
                raise ValueError(f"Type name {hint.name} appears multiple times in FoundationalType hint")
            self._name_alias_cache[hint.name] = tuple(a.alias for a in hint.aliases)
            for alias in hint.aliases:
                if alias.alias in self._alias_role_cache:
                    raise ValueError("Alias names should be unique")
                self._alias_role_cache[alias.alias] = alias.role.value

    def get_named_types(self) -> set[str]:
        return set(self._name_alias_cache.keys())

    def get_aliases_for_type_name(self, type_name: str) -> tuple[str, ...]:
        return self._name_alias_cache[type_name]

    def get_role_for_alias(self, alias: str) -> str | None:
        return self._alias_role_cache.get(alias, None)


if __name__ == "__main__":
    unittest.main()
