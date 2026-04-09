import json
import pathlib
import unittest


class TestObjectPath(unittest.TestCase):
    def setUp(self):
        with open(pathlib.Path(__file__).parent / "specialized_types.json") as f:
            json_data = json.load(f)
            self._valid_path_strings = json_data["ObjectPath"]["valid"]
            self._invalid_path_strings = json_data["ObjectPath"]["invalid"]

    def make_valid_object_path(self, path_string: str) -> bool:
        raise NotImplementedError("TestObjectPath implementations require make_valid_object_path")

    def make_invalid_object_path(self, path_string: str) -> bool:
        raise NotImplementedError("TestObjectPath implementations require make_invalid_object_path")

    def test_valid(self):
        for path in self._valid_path_strings:
            with self.subTest(path):
                self.assertTrue(self.make_valid_object_path(path))

    def test_invalid(self):
        for path in self._invalid_path_strings:
            with self.subTest(path):
                self.assertTrue(self.make_invalid_object_path(path))


class TestReferenceOrPayload(unittest.TestCase):
    def setUp(self):
        with open(pathlib.Path(__file__).parent / "specialized_types.json") as f:
            json_data = json.load(f)
            self._valid_targets = json_data["ReferenceOrPayload"]["valid"]
            self._invalid_targets = json_data["ReferenceOrPayload"]["invalid"]

    def make_valid_reference(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        raise NotImplementedError("TestReferenceOrPayload implementations require make_valid_reference")

    def make_valid_payload(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        raise NotImplementedError("TestReferenceOrPayload implementations require make_valid_payload")

    def make_invalid_reference(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        raise NotImplementedError("TestReferenceOrPayload implementations require make_invalid_reference")

    def make_invalid_payload(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        raise NotImplementedError("TestReferenceOrPayload implementations require make_invalid_payload")

    def test_valid_reference(self):
        for target in self._valid_targets:
            target["retiming"] = tuple[float, float](target["retiming"]) if target["retiming"] is not None else None
            with self.subTest(**target):
                self.assertTrue(self.make_valid_reference(**target))

    def test_valid_payload(self):
        for target in self._valid_targets:
            target["retiming"] = tuple[float, float](target["retiming"]) if target["retiming"] is not None else None
            with self.subTest(**target):
                self.assertTrue(self.make_valid_payload(**target))

    def test_invalid_reference(self):
        for target in self._invalid_targets:
            target["retiming"] = tuple[float, float](target["retiming"]) if target["retiming"] is not None else None
            with self.subTest(**target):
                self.assertTrue(self.make_invalid_reference(**target))

    def test_invalid_payload(self):
        for target in self._invalid_targets:
            target["retiming"] = tuple[float, float](target["retiming"]) if target["retiming"] is not None else None
            with self.subTest(**target):
                self.assertTrue(self.make_invalid_payload(**target))
