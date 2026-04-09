import dataclasses
import json
import os.path
import pprint
import typing
import warnings
from dataclasses import dataclass

from file_formats.parsers.binary import data_sizes
from file_formats.parsers.binary.compression import LZ4, IntegerArray
from file_formats.parsers.binary.constants import ENDIAN
from file_formats.parsers.binary.exceptions import *
from file_formats.parsers.binary.types import SpecForm
from file_formats.parsers.binary.values import ValueRep


@dataclass
class _Spec:
    """A Spec in an SDF Document is a mapping of indices between a path and a set of fields, along with a spec form"""

    path_index: int
    fieldset_index: int
    form: SpecForm


@dataclass
class SpecData:
    """Represents the data of a spec as its form and fields."""

    form: SpecForm
    fields: dict[str, ValueRep]

    def __repr__(self):
        return f"({self.form}, {self.fields})"

    def __getitem__(self, item):
        return self.fields.__getitem__(item)

    def __contains__(self, item):
        return self.fields.__contains__(item)


class Scene(dict):
    """A scene is a dictionary representation of paths and their respective spec data"""

    def to_usda(self):
        from .usda_display import USDADisplayPrinter

        return USDADisplayPrinter(self)

    def add_spec(self, path, form, fields):
        spec = SpecData(form, fields)
        self[path] = spec
        return spec

    def __str__(self):
        return str(self.to_usda())


class BinaryParser:
    """Parse a given crate file. Call build_scene after initializing the class to run the actual layer builds"""

    def __init__(self, reader: typing.BinaryIO):
        self._reader = reader
        self.version = [0, 0, 0]
        self.tokens = []
        self.strings = []
        self.fields = []
        self.field_sets = []
        self.paths = []
        self.specs = []

        self.parse()

    def parse(self):
        """We parse the Crate file from the head of the file to find the preamble describing each section.
        From there, each section is parsed in their own method"""

        # Crate must start with file format header
        filetype = self._reader.read(data_sizes.HEADER_SIZE).decode("utf-8")
        if filetype != "PXR-USDC":
            raise FileFormatException("File should start with PXR-USDC")

        # There are 8 bytes total for version information
        major = self.get_int(data_sizes.UINT8)
        minor = self.get_int(data_sizes.UINT8)
        patch = self.get_int(data_sizes.UINT8)
        reserved = self.get_int(data_sizes.UINT64 - (3 * data_sizes.UINT8))

        self.version = [major, minor, patch]
        if reserved != 0:
            warnings.warn("Reserved bytes after version should be empty")

        # We are only documenting up to 0.12.0, but 0.7.0 is similar enough while having a lot of test data
        if major != 0 or minor < 7 or minor > 12 or patch != 0:
            raise FileFormatException(f"Unsupported USDC version: {self.version}")

        # Following the version information is teh offset to the table of contents
        toc_offset = self.get_int()
        reserved = self.get_int()

        if reserved != 0:
            warnings.warn("Reserved bytes after TOC offset should be empty")

        self._reader.seek(toc_offset)

        # Read in the table of contents sections
        toc_dict = {}
        num_sections = self.get_int()
        for i in range(num_sections):
            # Section title is 16 bytes long and null terminated UTF-8 string
            name = self._reader.read(data_sizes.TOC_SECTION_TITLE).decode("utf-8").split("\x00")[0]
            offset = self.get_int()
            size = self.get_int()

            toc_dict[name] = [offset, size]

        # Check if the file ends with the table of contents
        cursor = self._reader.tell()
        self._reader.seek(0, os.SEEK_END)
        if cursor != self._reader.tell():
            # Technically not an issue, but still a concern
            warnings.warn("Table of Contents isn't at the end of the file.")

        # Now parse each of the known sections in order
        if tokens := toc_dict.get("TOKENS"):
            self.parse_tokens_section(tokens[0], tokens[1])
            if not self.tokens:
                # A file without Tokens is considered completely empty
                return

        if tokens := toc_dict.get("STRINGS"):
            self.parse_strings_section(tokens[0], tokens[1])

        if tokens := toc_dict.get("FIELDS"):
            self.parse_fields_section(tokens[0], tokens[1])

        if tokens := toc_dict.get("FIELDSETS"):
            self.parse_field_sets_section(tokens[0], tokens[1])

        if tokens := toc_dict.get("PATHS"):
            self.parse_paths_section(tokens[0], tokens[1])

        if tokens := toc_dict.get("SPECS"):
            self.parse_specs_section(tokens[0], tokens[1])

    def parse_tokens_section(self, offset, size):
        """Tokens are the building block for all subsequent sections
        They are stored as a compressed list of strings, separated by a null terminator.
        """

        if not size:
            warnings.warn("File has no tokens")
            return

        self._reader.seek(offset)

        num_tokens = self.get_int()
        uncompressed = self.get_int()
        compressed = self.get_int()
        data = self._reader.read(compressed)
        decompressed = LZ4.DecompressFromBuffer(data, uncompressed).decode("utf-8")
        # Token list is null delimited and null terminated
        self.tokens = decompressed.split("\0")[:-1]

        if len(self.tokens) != num_tokens:
            raise RuntimeError(f"TOKEN count doesn't match up. Found {len(self.tokens)} but expected {num_tokens} ")

    def parse_strings_section(self, offset, size):
        """Strings are stored as a consecutive index to the tokens found earlier"""
        if not size:
            warnings.warn("File has no strings")
            return
        self._reader.seek(offset)
        num_strings = self.get_int()

        for i in range(num_strings):
            index = self.get_int(data_sizes.INDEX)
            self.strings.append(self.tokens[index])

        if len(self.strings) != num_strings:
            raise RuntimeError(f"STRINGS count doesn't match up. Found {len(self.strings)} but expected {num_strings} ")

    def parse_fields_section(self, offset, size):
        """Fields are a mapping of a Token name to a value representation.
        Fields make up metadata and values on any path in a crate document.
        """
        if not size:
            warnings.warn("File has no strings")
            return

        self._reader.seek(offset)

        num_fields = self.get_int()
        indices = self.get_int_array(num_fields)

        reps = []
        reps_size = self.get_int()

        uncompressed_size = num_fields * data_sizes.VALUE_REP
        data = self._reader.read(reps_size)

        rep_data = LZ4.DecompressFromBuffer(data, uncompressed_size)

        for i in range(0, len(rep_data), data_sizes.VALUE_REP):
            rep = ValueRep(rep_data[i : i + data_sizes.VALUE_REP], self._reader, self)
            reps.append(rep)

        for i in range(num_fields):
            self.fields.append([indices[i], reps[i]])

        if len(self.fields) != num_fields:
            raise RuntimeError(f"FIELDS count doesn't match up. Found {len(self.fields)} but expected {num_fields} ")

    def parse_field_sets_section(self, offset, size):
        """Field Sets allow fields to be grouped together when represented together.
        They are a contiguous array of indices into the fields section, with groupings denoted by a
        negative or max int value.
        However, they are referenced by their index into the original contiguous array so are not split here.
        """
        if not size:
            warnings.warn("File has no field sets")
            return
        self._reader.seek(offset)

        num_field_sets = self.get_int()
        self.field_sets = self.get_int_array(num_field_sets)

        if len(self.field_sets) != num_field_sets:
            raise RuntimeError(
                f"FIELDSETS count doesn't match up. Found {len(self.field_sets)} but expected {num_field_sets} "
            )

    def parse_paths_section(self, offset, size):
        """Paths are constructed using the path building algorithm.
        The section consists of three index arrays representing the path index, an element token index and a jump index.
        """
        if not size:
            warnings.warn("File has no paths")
            return
        self._reader.seek(offset)
        num_paths = self.get_int()
        self.paths = [None] * num_paths

        num_encoded_paths = self.get_int()

        compressed_buffer_size = LZ4.GetCompressedIntBufferSize(num_encoded_paths)
        output_size = LZ4.GetUncompressedBufferSize(compressed_buffer_size)

        path_indices = self.get_int_array(num_encoded_paths, output_size)
        element_token_indices = self.get_int_array(num_encoded_paths, output_size)
        jumps = self.get_int_array(num_encoded_paths, output_size)

        if (
            not self.build_decompressed_paths(path_indices, element_token_indices, jumps, 0, "")
            or len(self.paths) != num_paths
        ):
            raise RuntimeError("Failed to process path")

        if len(self.paths) != num_paths:
            raise RuntimeError(f"PATHS count doesn't match up. Found {len(self.paths)} but expected {num_paths} ")

    def parse_specs_section(self, offset, size):
        """Specs are the bit in the crate file that combine the other sections into meaningful relationships.
        A spec consists of a path, a field set and a form, which are all represented by index matched arrays.
        The field set index points to a given point in the field set contiguous array and continues till the first
        delimiter found.
        """
        if not size:
            warnings.warn("File has no specs")
            return
        self._reader.seek(offset)
        num_specs = self.get_int()

        compressed_buffer_size = LZ4.GetCompressedIntBufferSize(num_specs)
        output_size = LZ4.GetUncompressedBufferSize(compressed_buffer_size)

        path_indices = self.get_int_array(num_specs, output_size)
        fieldset_indices = self.get_int_array(num_specs, output_size)
        forms = self.get_int_array(num_specs, output_size)

        for path_index, fieldset_index, form in zip(path_indices, fieldset_indices, forms):
            self.specs.append(_Spec(path_index, fieldset_index, SpecForm(form)))

        if len(self.specs) != num_specs:
            raise RuntimeError(f"SPECS count doesn't match up. Found {len(self.specs)} but expected {num_specs} ")

    def build_scene(self, output=None, print_output=False) -> dict[str, SpecData]:
        """A scene is built by traversing the specs and associating them with its corresponding data.
        For this implementation, we populate a dictionary with the found spec paths, its form and fields.
        """
        scene = Scene()
        for i, spec in enumerate(self.specs):
            path = self.paths[spec.path_index]
            field_set = []
            # Each Spec Field Set Index must point to the start of a group.
            # The group continues to the first zero delimiter
            for fs in self.field_sets[spec.fieldset_index :]:
                if fs < 0:  # Delimited
                    break
                field_set.append(fs)

            fields = {}
            for field in field_set:
                name, value = self.fields[field]
                name = self.tokens[name]
                fields[name] = value
                try:
                    value.process()
                except Exception as e:
                    print(f"Failed to process: {name}")
                    raise e

            if path in scene:
                raise RuntimeError(f"Non-unique path: {path}")
            scene[path] = SpecData(spec.form, fields)

        if print_output:
            pprint.pprint(scene)

        if output:
            with open(output, "w") as fp:
                json.dump(scene, fp, cls=CrateEncoder, indent=2)

        return scene

    # Utility Methods

    def build_decompressed_paths(
        self,
        path_indices,
        element_token_indices,
        jumps,
        start_index,
        parent_path,
    ):
        """Paths are built from a recursive algorithm.
        Warning: the current implementation may go too deep for Python for very large hierarchies.

        Starting from the PseudoRoot at /, the algorithm takes the following steps:

        The algorithm continues until it hits a leaf node.

        It does the following steps:

        1. Get the target index of this path from the path indices array
        2. Get the token by looking up the element token at the current iteration index.
           A positive value denotes it's a prim path, while a negative value denotes it's a property path.
        3. It looks at the jump array at this iteration index to discern how to find where to jump in the array
           to start populating any children or siblings.

        The recursion ends when you hit an entry without siblings or children.
        """
        first_iteration = True  # Python has no do-while
        has_child = False
        has_sibling = False

        while first_iteration or (has_child or has_sibling):
            first_iteration = False

            if not parent_path:
                # Root Node: Assume a single root
                parent_path = "/"
                index = path_indices[start_index]
                self.paths[index] = parent_path
            else:
                index = path_indices[start_index]
                token_index = element_token_indices[start_index]
                is_prim_property_path = token_index < 0

                token_index = abs(token_index)
                element_token = self.tokens[token_index]

                path = ("." if is_prim_property_path else "/").join(
                    [parent_path if parent_path != "/" else "", element_token]
                )
                self.paths[index] = path

            has_child = (jumps[start_index] > 0) or (jumps[start_index] == -1)
            has_sibling = jumps[start_index] >= 0

            if has_child:
                if has_sibling:
                    sibling_index = start_index + jumps[start_index]
                    if not self.build_decompressed_paths(
                        path_indices,
                        element_token_indices,
                        jumps,
                        sibling_index,
                        parent_path,
                    ):
                        return False

                index = path_indices[start_index]
                parent_path = self.paths[index]

            start_index += 1

        return True

    def get_int(self, size=data_sizes.UINT64, signed=False, endianness=ENDIAN):
        """A convenience method for reading integers of various sizes"""
        return int.from_bytes(self._reader.read(size), endianness, signed=signed)

    def get_int_array(self, count, uncompressed_size=None, size=data_sizes.UINT32):
        """A convenience method for reading a contiguous array of integers.
        These arrays are always compressed with LZ4 compression as described in the corresponding module
        """
        compressed_size = self.get_int()
        uncompressed = uncompressed_size or LZ4.GetCompressedIntBufferSize(count, size=size)

        data = self._reader.read(compressed_size)
        data = LZ4.DecompressFromBuffer(data, uncompressed)
        result = IntegerArray(count, data, size=size)

        return result


class CrateEncoder(json.JSONEncoder):
    """Used to allow Values to have custom serialization"""

    def default(self, o):
        if hasattr(o, "to_dict"):
            return o.to_dict()
        if isinstance(o, SpecData):
            return (o.form.name, o.fields)
        if dataclasses.is_dataclass(o):
            return dataclasses.asdict(o)
        return super().default(o)
