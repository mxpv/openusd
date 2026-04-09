import abc
import unittest

import data_types
from file_formats import specialized_types
from file_formats.tests import harness


class TestObjectPath(harness.TestObjectPath):
    def make_valid_object_path(self, path_string: str) -> bool:
        return specialized_types.ObjectPath.from_str(path_string)

    def make_invalid_object_path(self, path_string: str) -> bool:
        try:
            specialized_types.ObjectPath.from_str(path_string)
            return False
        except ValueError:
            return True

    # Additional test cases for reference implementation
    def test_exercise_repr(self):
        repr(specialized_types.ObjectPath.from_str("/hello/world"))
        repr(specialized_types.ObjectPath.from_str("/hello.world"))

    def test_roundtrip_str(self):
        self.assertEqual(str(specialized_types.ObjectPath.from_str("/hello/world")), "/hello/world")
        self.assertEqual(str(specialized_types.ObjectPath.from_str("/hello.world")), "/hello.world")


class TestReferenceOrPayload(harness.TestReferenceOrPayload):
    @abc.abstractmethod
    def make_valid_reference(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        match (asset, prim):
            case (str(a), None):
                target = data_types.Asset(a)
            case (None, str(p)):
                target = specialized_types.ObjectPath.from_str(p)
            case (str(a), str(p)):
                target = (data_types.Asset(a), specialized_types.ObjectPath.from_str(p))
            case _:
                raise TypeError("target must be Asset, ObjectPath, or Asset, ObjectPath pair")
        return bool(
            specialized_types.Reference(target, specialized_types.Retiming(*retiming) if retiming is not None else None)
        )

    @abc.abstractmethod
    def make_valid_payload(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        match (asset, prim):
            case (str(a), None):
                target = data_types.Asset(asset)
            case (None, str(p)):
                target = specialized_types.ObjectPath.from_str(prim)
            case (str(a), str(p)):
                target = (data_types.Asset(asset), specialized_types.ObjectPath.from_str(prim))
            case _:
                raise TypeError("target must be Asset, ObjectPath, or Asset, ObjectPath pair")
        return bool(
            specialized_types.Payload(target, specialized_types.Retiming(*retiming) if retiming is not None else None)
        )

    @abc.abstractmethod
    def make_invalid_reference(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        try:
            print(self.make_valid_reference(asset, prim, retiming))
        except (ValueError, TypeError):
            return True
        return False

    @abc.abstractmethod
    def make_invalid_payload(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        try:
            self.make_valid_payload(asset, prim, retiming)
        except (ValueError, TypeError):
            return True
        return False


if __name__ == "__main__":
    unittest.main()
