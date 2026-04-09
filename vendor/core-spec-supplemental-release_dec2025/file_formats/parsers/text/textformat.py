import json

from data_types import *
from file_formats.fields import *
from file_formats.format import *
from file_formats.spec_path import SpecFormFlags, SpecPath
from file_formats.specialized_types import *


class SpecData:
    """
    Defines a container for metadata fields
    applied to a particular spec path.
    """

    def __init__(self, path: SpecPath, form: SpecFormFlags):
        """
        Initializes a new Spec instance.
        """
        self._name = path
        self._path = path
        self._form = form
        self._metadata_fields = {}

    def has_field(self, field_name: Token) -> bool:
        """
        Retrieves whether or not the metadata field was authored on the spec.
        """
        return field_name in self._metadata_fields

    def read_field(self, field_name: Token) -> fields.CoreTypes:
        """
        Reads the data authored on the field with the given name.
        If the field is not authored, this will result in an error.
        """
        if field_name not in self._metadata_fields:
            raise ValueError(f"No value has been authored for field {str(field_name)}!")

        return self._metadata_fields[field_name]

    def write_field(self, field_name: Token, value: fields.CoreTypes):
        """
        Writes the metadata field value with the given field name
        to the spec data.
        """
        self._metadata_fields[field_name] = value

    def json_encode(self) -> dict[str, typing.Any]:
        """
        Retrieves a json representation of the spec.
        """
        return json.dumps(self, cls=SpecDataEncoder)

    @property
    def path(self) -> str:
        """
        Retrieves the path associated with the spec.
        """
        return self._path

    @path.setter
    def path(self, value):
        """
        Sets the path of associated with the spec.
        """
        self._path = value

    @property
    def name(self) -> str:
        """
        Retrieves the name associated with the spec.
        """
        return self._name


class SpecDataEncoder(json.JSONEncoder):
    """
    Specialization of JSON encoder for specs.
    """

    def default(self, val):
        if isinstance(val, SpecData):
            metadata_fields = {}
            for token in val._metadata_fields:
                metadata_fields.update({str(token): val._metadata_fields[token]})

            return {val.path: metadata_fields}
        elif isinstance(val, Retiming):
            return {"offset": val.offset, "scale": val.scale}
        elif isinstance(val, (Asset.__origin__, ObjectPath, Token.__origin__)):
            return str(val)
        elif isinstance(val, listop.ListOp):
            listop_dict = {}
            if val.explicit_items is not None and len(val.explicit_items) > 0:
                listop_dict.update({"explicit": list(val.explicit_items)})
            if len(val.appended_items) > 0:
                listop_dict.update({"append": list(val.appended_items)})
            if len(val.prepended_items) > 0:
                listop_dict.update({"prepend": list(val.prepended_items)})
            if len(val.deleted_items) > 0:
                listop_dict.update({"delete": list(val.deleted_items)})

            return listop_dict
        elif isinstance(val, listop.UniqueList):
            values = [v for v in val]
            return values
        elif isinstance(val, ValueBlockSentinel):
            return None
        elif isinstance(val, (Reference, Payload)):
            ref_payload = {}
            if isinstance(val.target, ObjectPath):
                ref_payload.update({"path": str(val.target)})
            elif isinstance(val.target, typing.Tuple):
                ref_payload.update({"asset": str(val.target[0])})
                ref_payload.update({"path": str(val.target[1])})
            else:
                ref_payload.update({"asset": str(val.target)})

            if val.retiming is not None:
                ref_payload.update({"layerOffset": val.retiming})

            return ref_payload
        elif isinstance(val, (Specifier, Variability)):
            return val.name.lower()
        elif isinstance(val, DefaultValue):
            return val.value
        elif isinstance(val, Relocate):
            return {val.source: val.target}
        elif isinstance(val, Spline):
            jsonValue = {"curveType": val.curve_type.value}
            if val.pre_extrapolation is None:
                jsonValue.update({"preExtrapolation": None})
            else:
                jsonValue.update(
                    {
                        "preExtrapolation": {
                            "mode": val.pre_extrapolation.mode.value,
                            "slope": val.pre_extrapolation.slope,
                        }
                    }
                )
            if val.post_extrapolation is None:
                jsonValue.update({"postExtrapolation": None})
            else:
                jsonValue.update(
                    {
                        "postExtrapolation": {
                            "mode": val.post_extrapolation.mode.value,
                            "slope": val.post_extrapolation.slope,
                        }
                    }
                )
            if val.loop_parameters is None:
                jsonValue.update({"loopParameters": None})
            else:
                jsonValue.update(
                    {
                        "loopParameters": {
                            "protoStart": val.loop_parameters.proto_start,
                            "protoEnd": val.loop_parameters.proto_end,
                            "numPreLoops": val.loop_parameters.num_pre_loops,
                            "numPostLoops": val.loop_parameters.num_post_loops,
                            "valueOffset": val.loop_parameters.value_offset,
                        }
                    }
                )

            knot_data = []
            for knot in val.knots:
                knot_data.append(
                    {
                        "time": knot.time,
                        "value": knot.value,
                        "preValue": knot.pre_value,
                        "preTangentSlope": knot.pre_tan_slope,
                        "preTangentWidth": knot.pre_tan_width,
                        "postTangentSlope": knot.post_tan_slope,
                        "postTangentWidth": knot.post_tan_width,
                        "nextInterpolationMode": knot.next_interp_mode.value,
                    }
                )

            jsonValue.update({"knots": knot_data})

            custom_data = {}
            for key, value in val.knot_custom_data.items():
                custom_data.update({str(key): value})

            jsonValue.update({"knotCustomData": custom_data})

            return jsonValue

        return super().default(val)


class TextFormat(Format):
    """
    Defines a format for holding data read from a
    text file format in usda.
    """

    def __init__(self):
        """
        Initializes a new TextFormat instance.
        """
        self._spec_data = {}

    def add_spec(self, path: SpecPath, spec_data: SpecData):
        """
        Adds a new spec to the format data.
        """
        if path in self._spec_data:
            raise ValueError(f"A spec with the given path {str(path)} already exists!")

        self._spec_data[path] = spec_data

    def has_spec(self, path: SpecPath) -> bool:
        """
        Returns whether or not the format instance
        contains a spec at the given path.
        """
        return path in self._spec_data

    def read_spec_info(self, path: SpecPath) -> SpecInfo | None:
        """
        Returns information about the spec data instance
        associated with the given path.  If no spec data exists
        for the given path, this method returns None.
        """
        if path not in self._spec_data:
            return None

        spec_data = self._spec_data[path]
        authored_field_names = []
        for key in spec_data._metadata_fields:
            authored_field_names.append(key)

        return SpecInfo(spec_data._form, authored_field_names)

    def read_field(self, path: SpecPath, field_name: data_types.Token) -> fields.CoreTypes:
        """
        Reads a single field value from the data at the specified path.
        """
        result = self.read_fields(path, [field_name])
        return result[field_name]

    def read_fields(self, path: SpecPath, query: set[data_types.Token]) -> dict[data_types.Token : fields.CoreTypes]:
        """
        Reads the values for a set of fields specified by the given query.
        If no spec is present with the given path, an error is returned.
        If a key is specified in the query set that isn't authored,
        a KeyError is raised.
        """
        if path not in self._spec_data:
            raise ValueError(f"The spec at the specified path {str(path)} does not exist!")

        spec = self._spec_data[path]

        result = {}
        for field_name in query:
            field_definition = fields.FieldRegistry()[field_name]
            form = spec.form
            if form not in field_definition.forms:
                raise ValueError(
                    "Field '{field_name}' cannot be read at '{path}' because '{form}' is not in set of "
                    "registered forms '{field_definition.forms}'"
                )
            if not spec.has_field(field_name):
                if form in field_definition.required_forms:
                    raise ValueError(
                        "Field '{field_name}' cannot be read at '{path}' but is required to provide a value."
                    )
                else:
                    result[field_name] = field_definition.acquire_fallback()
            else:
                result[field_name] = spec.read_field(field_name)
        return result

    def write_field(self, path: SpecPath, field_name: Token, value: fields.CoreTypes):
        """
        Writes the given value for the given field name to the spec data
        associated with the given path.
        """
        # must have added the spec prior to writing to it
        if path not in self._spec_data:
            raise ValueError(f"A spec with the given path {str(path)} does not exist!")

        self._spec_data[path].write_field(field_name, value)
