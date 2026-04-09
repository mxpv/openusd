import abc
import copy
import dataclasses
import typing

import data_types
from file_formats import fields, spec_path, specialized_types


@dataclasses.dataclass(frozen=True)
class SpecInfo:
    """Returns necessary information about a spec to make field requests

    It's necessary to report the form because the path is not sufficient to
    disambiguate between relationships and properties."""

    form: spec_path.SpecFormFlags
    authored_field_names: frozenset[data_types.Token]


class Format(abc.ABC):
    """A format provides an interface for reading information about specs and associated metadata field values"""

    @abc.abstractmethod
    def read_spec_info(self, path: spec_path.SpecPath) -> SpecInfo | None:
        """Implementations should retrieve information about a spec authored at `path`.

        Return None if no spec exists at path"""
        pass

    @abc.abstractmethod
    def read_fields(
        self, path: spec_path.SpecPath, query: set[data_types.Token]
    ) -> dict[data_types.Token : fields.CoreTypes]:
        """Implementations should acquire authored values for a set of fields at `path` or their fallbacks if unauthored.

        If the form of the spec authored at `path` is not in the field definition's allowed forms, an exception should
        be raised.
        If an "authored" value for required field does not exist, an exception should be raised in lieu of acquiring
        a fallback value.
        """
        pass

    def missing_required_fields(self, path: spec_path.SpecPath) -> frozenset[data_types.Token]:
        """Return fields that are required but not authored for the spec at path

        Missing requried fields suggest a format implementation error as formats are required to provide an authored
        value for all required fields.
        """
        spec_info = self.read_spec_info(path)
        required_field_names = set(f.name for f in fields.FieldRegistry().required_fields_by_form(spec_info.form))
        return required_field_names.difference(spec_info.authored_field_names)

    def unregistered_fields(self, path: spec_path.SpecPath) -> frozenset[data_types.Token]:
        """Return fields that are not known to the FieldRegistry for the spec at path

        Unregistered fields suggest that format is storing extension fields that are not known to this
        implementation's FieldRegistry.
        """
        spec_info = self.read_spec_info(path)
        registered_field_names = set(f.name for f in fields.FieldRegistry().fields_by_form(spec_info.form))
        return spec_info.authored_field_names.difference(registered_field_names)

    def traverse_descendants(
        self,
        path: spec_path.SpecPath,
        forms: spec_path.SpecFormFlags = (
            spec_path.SpecFormFlags.Prim
            | spec_path.SpecFormFlags.VariantSet
            | spec_path.SpecFormFlags.Variant
            | spec_path.SpecFormFlags.Property
        ),
    ):
        """Depth first traversal of all descendants matching a set of form flags.

        Note that traversal based on form flags is pruning. Setting
        (forms=spec_path.SpecFormFlags.Prim | spec_path.SpecFormFlags.Property) will not traverse Prim and Property
        descendants of VariantSpecs.
        """
        for child in self.list_children(path, forms):
            yield child
            for descendant in self.traverse_descendants(child, forms):
                yield descendant

    def list_children(
        self,
        path: spec_path.SpecPath,
        forms: spec_path.SpecFormFlags = (
            spec_path.SpecFormFlags.Prim
            | spec_path.SpecFormFlags.VariantSet
            | spec_path.SpecFormFlags.Variant
            | spec_path.SpecFormFlags.Property
        ),
    ) -> list[spec_path.SpecPath]:
        """Default implementation of list_children that relies on expicitly queries of a spec's children fields.

        Formats may be able to provide a more optimized code path but contents and ordering of the result should not
        change."""
        if (spec_info := self.read_spec_info(path)) is None:
            raise ValueError(f"Spec at '{path}' does not exist")

        if spec_info.form & spec_path.SpecFormFlags.Property:
            # Properties cannot have children, so we can early exit
            return list()

        read_fields = set()

        # A pedantic implementation might consult the FieldRegistry instead of assuming that the fallback value is
        # known to be empty.
        if list_prim_children := (
            spec_path.SpecFormFlags.Prim in forms and data_types.Token("primChildren") in spec_info.authored_field_names
        ):
            read_fields.add(data_types.Token("primChildren"))
        if list_variant_set_children := (
            spec_path.SpecFormFlags.VariantSet in forms
            and data_types.Token("variantSetChildren") in spec_info.authored_field_names
        ):
            read_fields.add(data_types.Token("variantSetChildren"))
        if list_variant_children := (
            spec_path.SpecFormFlags.Variant in forms
            and data_types.Token("variantChildren") in spec_info.authored_field_names
        ):
            read_fields.add(data_types.Token("variantChildren"))
        if list_property_children := (
            spec_path.SpecFormFlags.Property & forms
            and data_types.Token("propertyChildren") in spec_info.authored_field_names
        ):
            read_fields.add(data_types.Token("propertyChildren"))

        child_fields = self.read_fields(path, read_fields)

        children: list[spec_path.SpecPath] = list[spec_path.SpecPath]()
        if list_prim_children:
            children.extend(
                path + [spec_path.SpecPathElement.Prim(child)]
                for child in child_fields[data_types.Token("primChildren")]
            )
        if list_variant_set_children:
            children.extend(
                path + [spec_path.SpecPathElement.VariantSet(child)]
                for child in child_fields[data_types.Token("vaiantSetChildren")]
            )
        if list_variant_children:
            children.extend(
                path + [spec_path.SpecPathElement.Variant(child)]
                for child in child_fields[data_types.Token("vaiantChildren")]
            )
        if list_property_children:
            # If only Attribute or only Relationship are selected, additional work is required to check the form of the
            # the child.
            children.extend(
                (child_path := (path + [spec_path.SpecPathElement.Property(child)]))
                for child in child_fields[data_types.Token("propertyChildren")]
                if (spec_path.SpecFormFlags.Property in forms or self.read_spec_info(child_path).form & forms)
            )
        return children


class AnonymousFormat(Format):
    def __init__(self):
        layer_spec_path = spec_path.SpecPath.absolute_root()
        self._spec_fields_by_path = {
            # TODO: Acquiring allowed and required by spec form should be a feature of the Registry
            layer_spec_path: {
                field.name: field.acquire_fallback()
                for field in fields.FieldRegistry().values()
                if spec_path.SpecFormFlags.Layer in field.required_forms
            }
        }

        # This is mostly a reflection of information captured in the spec_path.SpecPath, but spec_path.SpecPath does not disambiguatate
        # between relationship and attribute. An additional hint is required.
        self._spec_form_by_path = {layer_spec_path: spec_path.SpecFormFlags.Layer}

    def read_spec_info(self, path: spec_path.SpecPath) -> SpecInfo | None:
        if path not in self._spec_fields_by_path:
            return None
        return SpecInfo(self._spec_form_by_path[path], self._spec_fields_by_path[path].keys())

    def read_fields(self, path: spec_path.SpecPath, query: set[data_types.Token]):
        result = {}
        for field_name in query:
            field_definition = fields.FieldRegistry()[field_name]
            form = self._spec_form_by_path[path]
            if form not in field_definition.forms:
                raise ValueError(
                    "Field '{field_name}' cannot be read at '{path}' because '{form}' is not in set of "
                    "registered forms '{field_definition.forms}'"
                )
            if field_name not in self._spec_fields_by_path[path]:
                if form in field_definition.required_forms:
                    raise ValueError(
                        "Field '{field_name}' cannot be read at '{path}' but is required to provide a value."
                    )
                else:
                    result[field_name] = field_definition.acquire_fallback()
            else:
                result[field_name] = self._spec_fields_by_path[path][field_name]
        return result

    def insert(
        self,
        parent: spec_path.SpecPath,
        form: spec_path.SpecFormFlags,
        name: data_types.Token,
        values: dict[data_types.Token, fields.CoreTypes],
    ):
        """Interface to add valid specs into an anonymous layer."""
        if parent not in self._spec_fields_by_path:
            raise KeyError(f"{parent} does not exist")
        if spec_path.SpecFormFlags.Property in form:
            raise ValueError("SpecForm must be either Attribute or Relationship, not Property")

        # For the purposes of path construction, Attributes and Relationships get reduced to Properties
        path_form = spec_path.SpecFormFlags.Proprety if (form & spec_path.SpecFormFlags.Property) else form

        # spec_path.SpecPath and spec_path.SpecPathElement pre-verify that names and hierarchy of allowed children are valid so these
        # won't be rechecked downstream.
        path = parent + [spec_path.SpecPathElement(path_form, name)]
        if path in self._spec_fields_by_path:
            raise KeyError(f"Spec already exists at {path}")

        # Ensure that all fields are registered
        registered_field_names = set(f.name for f in fields.FieldRegistry().fields_by_form(form))
        if unregistered_field_names := set(values.keys()).difference(registered_field_names):
            raise ValueError(f"Cannot create spec with unregistered fields: {unregistered_field_names}")

        # Ensure that all required fields are present when creating a new spec
        required_field_names = set(f.name for f in fields.FieldRegistry().required_fields_by_form(form))
        if missing_required_field_names := (required_field_names.difference(values.keys())):
            raise ValueError(f"Cannot create spec without required fields: {missing_required_field_names}")

        # Ensure that all fields match the field definitions data type and passes the verifier
        for field_name, field_value in values.items():
            field_definition = fields.FieldRegistry()[field_name]
            # TODO: Create an interface for matching types in the field definition
            if not isinstance(
                field_value,
                field_definition.data_type.__origin__
                if typing.get_origin(field_definition.data_type) is typing.Annotated
                else field_definition.data_type,
            ):
                raise TypeError(f"{field_value} does not match {field_definition.data_type}")
            if field_definition.verifier and not field_definition.verifier(field_value):
                raise ValueError(f"{field_value} does not match field verifier {field_value}")

        # TODO: Verify that the `typeName`` agrees with the value of the `default` and `timeSamples` field for
        # attributes

        # Create a deepcopy of the values in the dictionary
        verified_values = copy.deepcopy(values)

        # It's the format's responsibility to keep the spec's hierarchy fields up to date.
        match form:
            case spec_path.SpecFormFlags.Prim:
                children_token = data_types.Token("primChildren")
            case spec_path.SpecFormFlags.VariantSet:
                children_token = data_types.Token("variantSetChildren")
            case spec_path.SpecFormFlags.Variant:
                children_token = data_types.Token("variantChildren")
            case spec_path.SpecFormFlags.Attribute | flags.SpecFormFlags.Relationship:
                children_token = data_types.Token("propertyChildren")
            case _:
                raise ValueError(f"Cannot insert child with form {form}")
        if children_token not in self._spec_fields_by_path[parent]:
            self._spec_fields_by_path[parent][children_token] = []

        if bool(name in self._spec_fields_by_path[parent][children_token]) != bool(path in self._spec_fields_by_path):
            raise KeyError("Anonymous layer hierarchy is in inconsistent state.")

        # If these raise an exception, the layer could end up in an inconsistent state.
        self._spec_fields_by_path[parent][children_token].append(name)
        self._spec_fields_by_path[path] = verified_values
        self._spec_form_by_path[path] = form


if __name__ == "__main__":
    anonymous_format = AnonymousFormat()
    anonymous_format.insert(
        spec_path.SpecPath.absolute_root(),
        spec_path.SpecFormFlags.Prim,
        data_types.Token("World"),
        values={
            data_types.Token("typeName"): data_types.Token("Xform"),
            data_types.Token("specifier"): specialized_types.Specifier.Def,
        },
    )
    print(children := anonymous_format.list_children(spec_path.SpecPath.absolute_root()))
    print(spec_info := anonymous_format.read_spec_info(children[0]))
    print(anonymous_format.read_fields(children[0], spec_info.authored_field_names))
