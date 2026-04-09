import abc
import dataclasses
import itertools
import json
import pathlib
import unittest


@dataclasses.dataclass(frozen=True, kw_only=True, eq=True)
class ReduceChainCase:
    description: str
    chain: list
    combined_reduced: dict


class TestReduceChain(unittest.TestCase):
    @abc.abstractmethod
    def combine_and_reduce(self, chain: dict) -> dict:
        pass

    def _run_test_from_json(self, test_path: pathlib.Path):
        with self.subTest(test_path=test_path), open(test_path) as test_file:
            cases = json.load(test_file)
            self.assertIsInstance(cases, list)
            self.assertTrue(cases)
            for index, case_data in enumerate(cases):
                with self.subTest(index=index):
                    case = ReduceChainCase(**case_data)
                    with self.subTest(description=case.description):
                        self.assertEqual(self.combine_and_reduce(case.chain), case.combined_reduced)

    def test_inert_only(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/inert_only.json")

    def test_explicit_only(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/explicit_only.json")

    def test_composable_only(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/composable_only.json")

    def test_append_over_explicit(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/append_over_explicit.json")

    def test_prepend_over_explicit(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/prepend_over_explicit.json")

    def test_delete_over_explicit(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/delete_over_explicit.json")

    def test_prepend_over_composable(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/prepend_over_composable.json")

    def test_append_over_composable(self):
        self._run_test_from_json(pathlib.Path(__file__).parent / "./combine_chain/append_over_composable.json")


class TestFoundationalDataTypes(unittest.TestCase):
    """Ensure that all supported foundational types are supported"""

    def setUp(self):
        with open(pathlib.Path(__file__).parent / "./foundational_data_types.json") as test_file:
            self._test_info = json.load(test_file)

    @abc.abstractmethod
    def get_named_types(self) -> set[str]:
        """Return the normative name of all foundational data types."""
        pass

    @abc.abstractmethod
    def get_aliases_for_type_name(self, type_name: str) -> tuple[str, ...]:
        """Return the normative name of all semantic aliases for a type name

        ie. float3 -> ("color3f", "point3f", "normal3f", "vector3f", "texCoord3f")
        """
        pass

    @abc.abstractmethod
    def get_role_for_alias(self, alias_name: str) -> str | None:
        """Return the normative role of a semantic alias.

        ie. color3f -> color
            float3 -> None"""
        pass

    def test_named_types(self):
        named_types: set[str] = self.get_named_types()
        self.assertSetEqual(self.get_named_types(), set(self._test_info["named_types"]))

    def test_semantic_aliases(self):
        aliases: set[tuple[str, str, str]] = set(
            itertools.chain(
                *(
                    tuple((a, t, self.get_role_for_alias(a)) for a in self.get_aliases_for_type_name(t))
                    for t in self.get_named_types()
                )
            )
        )
        self.assertSetEqual(aliases, set(tuple(e) for e in self._test_info["semantic_aliases"]))
