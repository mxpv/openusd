import typing

import data_types
import file_formats.parsers.binary.binary_parser
from file_formats import fields, spec_path
from file_formats.format import Format, SpecInfo


def _form_enum_to_form_flags(form: file_formats.parsers.binary.binary_parser.SpecForm) -> spec_path.SpecFormFlags:
    match form:
        case file_formats.parsers.binary.binary_parser.SpecForm.Attribute:
            return spec_path.SpecFormFlags.Attribute
        case file_formats.parsers.binary.binary_parser.SpecForm.Prim:
            return spec_path.SpecFormFlags.Prim
        case file_formats.parsers.binary.binary_parser.SpecForm.PseudoRoot:
            return spec_path.SpecFormFlags.Layer
        case file_formats.parsers.binary.binary_parser.SpecForm.Relationship:
            return spec_path.SpecFormFlags.Relationship
        case file_formats.parsers.binary.binary_parser.SpecForm.Variant:
            return spec_path.SpecFormFlags.Variant
        case file_formats.parsers.binary.binary_parser.SpecForm.VariantSet:
            return spec_path.SpecFormFlags.VariantSet
        case _:
            raise ValueError(f"Spec Form {form.name} is unsupported.")


class CrateFormat(Format):
    """Implements crate file format (usdc) reader"""

    def __init__(self, reader: typing.BinaryIO):
        """Initializes a new CrateFormat reader."""
        self._parser = file_formats.parsers.binary.binary_parser.BinaryParser(reader)
        self._scene = self._parser.build_scene()

    def read_spec_info(self, path: spec_path.SpecPath) -> SpecInfo | None:
        path_str = str(path)
        if path_str not in self._scene:
            return None

        spec_data = self._scene[path_str]
        # Remap the properties field to propertyChildren
        return SpecInfo(
            _form_enum_to_form_flags(spec_data.form),
            frozenset(
                data_types.Token(name) if name != "properties" else data_types.Token("propertyChildren")
                for name in spec_data.fields
            ),
        )

    def read_fields(
        self, path: spec_path.SpecPath, query: set[data_types.Token]
    ) -> dict[data_types.Token : fields.CoreTypes]:
        path_str = str(path)
        if path_str not in self._scene:
            raise ValueError(f"The spec at the specified path '{path}' does not exist!")

        spec_data = self._scene[path_str]
        result = {}
        for field_name in query:
            field_definition = fields.FieldRegistry()[field_name]
            form = _form_enum_to_form_flags(spec_data.form)
            if form not in field_definition.forms:
                raise ValueError(
                    f"Field '{field_name}' cannot be read at '{path}' because '{form}' is not in set of "
                    f"registered forms '{field_definition.forms}'"
                )
            crate_lookup_name = (
                str(field_name) if field_name is not data_types.Token("propertyChildren") else "properties"
            )
            if crate_lookup_name not in spec_data:
                if form in field_definition.required_forms:
                    raise ValueError(
                        f"Field '{field_name}' cannot be read at '{path}' but is required to provide a value."
                    )
                result[field_name] = field_definition.acquire_fallback()
            else:
                value_rep = spec_data[crate_lookup_name]
                value_rep.process()
                result[field_name] = value_rep.value
        return result


if __name__ == "__main__":
    with open("file_formats/tests/assets/binary/ball.maya.usdc", mode="rb") as reader:
        crate_reader = CrateFormat(reader)
        for path in crate_reader.traverse_descendants(spec_path.SpecPath()):
            print(path, crate_reader.read_spec_info(path))
