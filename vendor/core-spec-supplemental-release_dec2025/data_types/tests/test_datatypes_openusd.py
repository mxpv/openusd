import unittest

from pxr import Sdf

from data_types.tests import harness


class TestFoundationalDataTypes(harness.TestFoundationalDataTypes):
    """Primarily uses Sdf.ValueTypeNames as the source of truth for discovering foundational data types.

    Since listops and dictionaries are not considered value types for the purposes of scene description, but are valid
    types for extension metadata, they are added to the set of value types.
    """

    # These types are not yet supported in this repo
    EXCLUDED_VALUE_TYPE_NAMES = ("pathExpression", "pathExpression[]")

    def setUp(self):
        super().setUp()
        self._named_types = set()
        self._semantic_aliases = set()

        # Listops are not considered named value types in OpenUSD, so we create the aliases here.
        self._listop_types = {
            "listop<int>": Sdf.IntListOp,
            "listop<int64>": Sdf.Int64ListOp,
            "listop<uint>": Sdf.UIntListOp,
            "listop<uint64>": Sdf.UInt64ListOp,
            "listop<token>": Sdf.TokenListOp,
            "listop<string>": Sdf.StringListOp,
        }

        for value_type_name_identifier in (
            t for t in dir(Sdf.ValueTypeNames) if (not t.startswith("__") and t not in ("Find",))
        ):
            value_type_name = getattr(Sdf.ValueTypeNames, value_type_name_identifier)
            if value_type_name in self.EXCLUDED_VALUE_TYPE_NAMES:
                continue
            if value_type_name.role:
                self._semantic_aliases.add(value_type_name)
            else:
                self._named_types.add(value_type_name)

    def get_named_types(self) -> set[str]:
        return set(str(t) for t in self._named_types).union(self._listop_types.keys()).union(("dictionary",))

    def get_aliases_for_type_name(self, type_name: str) -> tuple[str, ...]:
        if type_name in ("dictionary", *self._listop_types):
            return tuple()
        named_type = next((value_type for value_type in self._named_types if str(value_type) == type_name), None)
        if named_type is None:
            raise ValueError(f"Unknown type name: '{type_name}'")
        return tuple(str(a) for a in self._semantic_aliases if a.type == named_type.type)

    def get_role_for_alias(self, alias: str) -> str | None:
        alias_value_type = next((value_type for value_type in self._semantic_aliases if str(value_type) == alias), None)
        if alias_value_type is None:
            return None
        match alias_value_type.role:
            case "":
                return None
            case "TextureCoordinate":
                return "texCoord"
            case "Color":
                return "color"
            case "Point":
                return "point"
            case "Normal":
                return "normal"
            case "Vector":
                return "vector"
            case "Frame":
                return "frame"
            case "Group":
                return "group"
            case _:
                raise ValueError(f"Unknown Role: {alias_value_type.role}")


if __name__ == "__main__":
    unittest.main()
