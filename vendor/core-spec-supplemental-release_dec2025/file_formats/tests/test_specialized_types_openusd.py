import unittest

from pxr import Sdf

from . import harness


class TestObjectPath(harness.TestObjectPath):
    def make_valid_object_path(self, path_string: str) -> bool:
        path = Sdf.Path(path_string)
        return path.IsAbsolutePath() and (path.IsPrimPath() or path.IsPropertyPath())

    def make_invalid_object_path(self, path_string: str) -> bool:
        return not self.make_valid_object_path(path_string)


class TestReferenceOrPayload(harness.TestReferenceOrPayload):
    def make_valid_reference(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        layer_offset = Sdf.LayerOffset(*retiming) if retiming is not None else Sdf.LayerOffset()
        match (asset, prim):
            case (str(a), None):
                reference = Sdf.Reference(a, layerOffset=layer_offset)
            case (None, str(p)):
                reference = Sdf.Reference("", p, layerOffset=layer_offset)
            case (str(a), str(p)):
                reference = Sdf.Reference(a, p, layerOffset=layer_offset)
            case _:
                raise TypeError("target must be Asset, ObjectPath, or Asset, ObjectPath pair")
        return reference.primPath.isEmpty or reference.primPath.IsPrimPath()

    def make_valid_payload(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        layer_offset = Sdf.LayerOffset(*retiming) if retiming is not None else Sdf.LayerOffset()
        match (asset, prim):
            case (str(a), None):
                payload = Sdf.Reference(asset, layerOffset=layer_offset)
            case (None, str(p)):
                payload = Sdf.Reference("", p, layerOffset=layer_offset)
            case (str(a), str(p)):
                payload = Sdf.Reference(a, p, layerOffset=layer_offset)
            case _:
                raise TypeError("target must be Asset, ObjectPath, or Asset, ObjectPath pair")
        return payload.primPath.isEmpty or payload.primPath.IsPrimPath()

    def make_invalid_reference(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        try:
            return not self.make_valid_reference(asset, prim, retiming)
        except (ValueError, TypeError):
            return True
        return False

    def make_invalid_payload(self, asset: str | None, prim: str | None, retiming: tuple[float, float] | None) -> bool:
        try:
            return not self.make_valid_payload(asset, prim, retiming)
        except (ValueError, TypeError):
            return True
        return False


if __name__ == "__main__":
    unittest.main()
