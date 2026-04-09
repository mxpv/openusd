import enum
import struct
import warnings
import weakref

import data_types
from data_types.listop import ListOp, UniqueList
from file_formats.parsers.binary import data_sizes
from file_formats.parsers.binary.compression import LZ4, IntegerArray
from file_formats.parsers.binary.constants import ENDIAN
from file_formats.parsers.binary.splines import Spline
from file_formats.parsers.binary.types import (
    ListOpHeader,
    Permission,
    Specifier,
    ValueType,
    Variability,
)
from file_formats.specialized_types import ObjectPath, Payload, Reference, Retiming


class ValueRep:
    """Value Reps are a representation of data to infer a value from a packing friendly form.
    A Value Rep consists of two header bytes and 6 payload bytes.
    The payload may include an inlined value or a reference to a value elsewhere.
    """

    def __init__(self, data=None, filehandle=None, parser=None):
        self.data = data
        self.int_value = data
        if self.data:
            if isinstance(self.data, int):
                self.data = self.data.to_bytes(data_sizes.VALUE_REP, ENDIAN)
            else:
                self.int_value = int.from_bytes(self.data, ENDIAN, signed=False)

        self.type = ValueType.Unknown
        self.flags = None
        self.payload = None

        self.is_array = False
        self.is_inlined = False
        self.is_compressed = False

        self.filehandle = None
        self.parser = None
        self.position = 0
        if filehandle:
            self.filehandle = filehandle
            self.position = filehandle.tell()
        if parser:
            try:
                self.parser = weakref.proxy(parser)
            except TypeError:
                self.parser = parser
        self.value = None

        self._is_processed = False

        if self.data:
            self.pre_process()

    def __repr__(self):
        if not self._is_processed:
            return f"{self.type.name}: Unprocessed"
        return f"{self.type.name}:{' _ ' if self.value is None else self.value}"

    def pre_process(self):
        """Read the header bytes and split out the payload"""
        *self.payload, self.type, self.flags = self.data
        self.payload = bytearray(self.payload)
        self.type = ValueType(self.type)
        self.is_array = bool(self.flags & (1 << 7))
        self.is_inlined = bool(self.flags & (1 << 6))
        self.is_compressed = bool(self.flags & (1 << 5))

    def process(self):
        """For every known data type, we delegate to a given processing method"""
        if self._is_processed:
            return

        match self.type:
            case ValueType.Unknown:
                raise RuntimeError("Unknown type detected")
            case ValueType.ValueBlock:
                pass
            case ValueType.Bool:
                value = self.parse_integer()
                self.value = [bool(i) for i in value] if self.is_array else bool(value)
            case ValueType.UChar:
                self.value = self.parse_integer()
            case ValueType.Int:
                self.value = self.parse_integer(size=data_sizes.INT32, signed=True)
            case ValueType.UInt:
                self.value = self.parse_integer(size=data_sizes.UINT32, signed=False)
            case ValueType.Int64:
                self.value = self.parse_integer(size=data_sizes.INT64, signed=True)
            case ValueType.UInt64:
                self.value = self.parse_integer(size=data_sizes.UINT64, signed=False)
            case ValueType.Half | ValueType.Float | ValueType.Double | ValueType.TimeCode:
                self.value = self.parse_float(self.type)
            case ValueType.String:
                self.value = self.parse_string()
            case ValueType.AssetPath | ValueType.PathExpression:
                self.value = self.parse_asset_path()
            case ValueType.Token:
                self.value = self.parse_token()
            case ValueType.Dictionary:
                self.value = self.parse_dictionary()
            case (
                ValueType.PathVector
                | ValueType.TokenVector
                | ValueType.DoubleVector
                | ValueType.StringVector
                | ValueType.LayerOffsetVector
            ):
                self.value = self.parse_vector_array()
            case ValueType.Specifier:
                value = self.parse_integer(size=data_sizes.UINT32, signed=True)
                self.value = Specifier(value)
            case ValueType.Variability:
                value = self.parse_integer(size=data_sizes.UINT32, signed=True)
                self.value = Variability(value)
            case ValueType.Permission:
                value = self.parse_integer(size=data_sizes.UINT32, signed=True)
                self.value = Permission(value)
            case (
                ValueType.Quatd
                | ValueType.Quatf
                | ValueType.Quath
                | ValueType.Vec2d
                | ValueType.Vec2f
                | ValueType.Vec2h
                | ValueType.Vec2i
                | ValueType.Vec3d
                | ValueType.Vec3f
                | ValueType.Vec3h
                | ValueType.Vec3i
                | ValueType.Vec4d
                | ValueType.Vec4f
                | ValueType.Vec4h
                | ValueType.Vec4i
                | ValueType.Matrix2d
                | ValueType.Matrix3d
                | ValueType.Matrix4d
            ):
                self.value = self.parse_complex_mathematical()
            case (
                ValueType.TokenListOp
                | ValueType.StringListOp
                | ValueType.PathListOp
                | ValueType.ReferenceListOp
                | ValueType.PayloadListOp
                | ValueType.IntListOp
                | ValueType.Int64ListOp
                | ValueType.UIntListOp
                | ValueType.UInt64ListOp
                | ValueType.UnregisteredValueListOp
            ):
                self.value = self.parse_list_ops()
            case ValueType.TimeSamples:
                self.value = self.parse_timesamples()
            case ValueType.Value:
                self.value = self.parse_value_at_offset().value
            case ValueType.UnregisteredValue:
                self.value = self.parse_unregistered_value()
            case ValueType.Payload:
                self.value = self.parse_payload()
            case ValueType.VariantSelectionMap:
                self.value = self.parse_variant_selection_map()
            case ValueType.Relocates:
                self.value = self.parse_relocates_map()
            case ValueType.Spline:
                self.value = self.parse_splines()
            case _:
                raise NotImplementedError(self.type.name, "is unsupported")

        self._is_processed = True

    def go_to_payload_offset(self):
        """Convenience method to go to an offset within the files as defined by the payload"""
        offset = int.from_bytes(self.payload, byteorder=ENDIAN, signed=False)
        if not offset:
            return False

        self.filehandle.seek(offset)
        return offset

    def read_int(self, size=data_sizes.UINT64, signed=False, endianness=ENDIAN):
        """Convenience method to read an integer of a known size from the buffer at the current point in the file"""
        return int.from_bytes(self.filehandle.read(size), endianness, signed=signed)

    def read_compressed_int_array(self, count, size=data_sizes.UINT32):
        """Convenience method to get an integer array and decompress it"""
        compressed_size = self.read_int()
        uncompressed = LZ4.GetCompressedIntBufferSize(count, size=size)

        data = self.filehandle.read(compressed_size)
        data = IntegerArray(count, LZ4.DecompressFromBuffer(data, uncompressed), size=size)

        return data

    def parse_integer(self, size=data_sizes.UINT8, signed=False):
        """Reads value representations that can be represented as an integer."""
        if self.is_inlined:
            return int.from_bytes(self.payload[: min(size, data_sizes.UINT32)], ENDIAN, signed=signed)

        values = []
        if not self.go_to_payload_offset():
            return values  # empty

        if not self.is_array:
            return int.from_bytes(self.filehandle.read(size), ENDIAN, signed=signed)

        num_elements = self.read_int()
        if self.is_compressed:
            values = self.read_compressed_int_array(num_elements, size=size)
        else:
            data = self.filehandle.read(num_elements * size)
            for i in range(num_elements):
                start = i * size
                end = start + size
                block = data[start:end]
                values.append(int.from_bytes(block, ENDIAN, signed=signed))

        if not len(values) == num_elements:
            raise RuntimeError(f"Mismatch in array size. Expected {num_elements} but got {len(values)}")
        return values

    def parse_float(self, value_type):
        """Reads value representations that can be represented as singular floating precision types"""
        if value_type in (ValueType.Double, ValueType.TimeCode):
            size = data_sizes.DOUBLE
            element_format = "d"
        elif value_type == ValueType.Half:
            size = data_sizes.HALF
            element_format = "h"
        else:
            size = data_sizes.FLOAT
            element_format = "f"

        data = bytearray()
        if self.is_inlined:
            # Inlined doubles are read as floats
            if size > data_sizes.FLOAT:
                size = data_sizes.FLOAT
                element_format = "f"
            data = self.payload[:size]
        else:
            offset = self.go_to_payload_offset()

        if not self.is_inlined and not self.is_array:
            data = self.filehandle.read(size)

        if data:
            value = struct.unpack(element_format, data)[0]
            if value_type == ValueType.Half:
                value = ValueRep.convert_half_to_float(value)
            return value

        values = []
        num_elements = self.read_int()
        if not self.is_compressed:
            data = self.filehandle.read(size * num_elements)
            for i in range(num_elements):
                start = i * size
                end = start + size
                block = data[start:end]
                val = struct.unpack(element_format, block)[0]
                if value_type == ValueType.Half:
                    val = ValueRep.convert_half_to_float(val)
                values.append(val)

            return values

        # Compressed floats can use one of two methods, either as an integer array or a look up table
        compression_type = self.filehandle.read(data_sizes.CHAR).decode("utf-8")
        if compression_type == "i":
            values = self.read_compressed_int_array(num_elements, size=size)
            return values
        elif compression_type == "t":
            lut_count = self.read_int(data_sizes.INT32)
            luts_buffer = self.filehandle.read(size * lut_count)
            luts = []
            for i in range(lut_count):
                start = i * size
                end = start + size
                val = struct.unpack(element_format, luts_buffer[start:end])[0]
                if value_type == ValueType.Half:
                    val = ValueRep.convert_half_to_float(val)
                luts.append(val)

            indices = self.read_compressed_int_array(num_elements)
            for i in indices:
                values.append(luts[i])
        else:
            raise RuntimeError(f"Unsupported Float Array Compression: {compression_type}")

    def parse_string(self):
        value = self.parse_integer(data_sizes.INDEX)
        if self.is_array:
            value = [self.parser.strings[i] for i in value]
        else:
            value = self.parser.strings[value]

        return value

    def parse_asset_path(self):
        """Asset paths can refer to either a string or token depending on if its inlined or not"""
        value = self.parse_integer(data_sizes.INDEX)
        if self.is_array:
            value = [self.parser.strings[i] for i in value]
        elif self.is_inlined:
            value = self.parser.tokens[value]
        else:
            value = self.parser.strings[value]

        return value

    def parse_token(self):
        value = self.parse_integer(data_sizes.INDEX)
        if self.is_array:
            value = [self.parser.tokens[i] for i in value]
        else:
            value = self.parser.tokens[value]

        return value

    def parse_dictionary(self, target_offset=None):
        """Dictionaries are a map of a key to an offset value representation"""
        if target_offset:
            self.filehandle.seek(target_offset)
        else:
            self.go_to_payload_offset()

        if self.is_inlined:
            num_items = int.from_bytes(self.payload, byteorder=ENDIAN, signed=False)
        else:
            num_items = self.read_int()
        values = {}
        for i in range(num_items):
            key = self.read_int(data_sizes.INDEX)
            key = self.parser.strings[key]

            seek_from = self.filehandle.tell()
            offset = self.read_int() + seek_from
            self.filehandle.seek(offset)

            rep = self.read_int()
            current = self.filehandle.tell()

            rep = ValueRep(rep, self.filehandle, self.parser)
            rep.process()
            values[key] = rep

            self.filehandle.seek(current)

        return values

    def parse_vector_array(self):
        """Parses vectors, as in arrays of known types."""
        if self.is_inlined:
            raise RuntimeError("Vector Arrays cannot be inlined")

        self.go_to_payload_offset()
        num_elements = self.read_int()
        size = data_sizes.INDEX
        if self.type == ValueType.DoubleVector:
            size = data_sizes.DOUBLE
        elif self.type == ValueType.LayerOffsetVector:
            size = data_sizes.LAYER_OFFSET

        values = []
        for i in range(num_elements):
            data = self.filehandle.read(size)
            if self.type == ValueType.DoubleVector:
                value = struct.unpack("d", data)[0]
            elif self.type == ValueType.LayerOffsetVector:
                value = Retiming(
                    struct.unpack("d", data[: data_sizes.DOUBLE])[0],
                    struct.unpack("d", data[data_sizes.DOUBLE :])[0],
                )
            else:
                value = int.from_bytes(data, ENDIAN, signed=False)

            values.append(value)

        # Not an index based array
        if size != data_sizes.INDEX:
            return values

        lookup = self.parser.tokens
        if self.type == ValueType.PathVector:
            lookup = self.parser.paths
        elif self.type == ValueType.StringVector:
            lookup = self.parser.strings

        values = [lookup[i] for i in values]
        return values

    def parse_complex_mathematical(self):
        """Parses mathematical objects such as vectors, quaternions and matrices."""
        type_name = self.type.name
        diagonal = 0
        element_format = type_name[-1]
        if type_name.startswith("Quat"):
            element_count = 4
        elif type_name.startswith("Vec"):
            element_count = int("".join([d for d in type_name if d.isdigit()]))
        elif type_name.startswith("Matrix"):
            element_count = int("".join([d for d in type_name if d.isdigit()]))
            diagonal = element_count
            element_count = element_count * element_count
        else:
            raise RuntimeError(f"Unknown mathematical type: {type_name}")

        if element_format == "d":
            element_size = data_sizes.DOUBLE
            value_type = ValueType.Double
        elif element_format == "f":
            element_size = data_sizes.FLOAT
            value_type = ValueType.Float
        elif element_format == "h":
            element_size = data_sizes.HALF
            value_type = ValueType.Half
        elif element_format == "i":
            element_size = data_sizes.INT32
            value_type = ValueType.Int
        else:
            raise RuntimeError(f"Unknown format type: {element_format}")

        values = []
        if self.is_inlined:
            element_size = 1
            if value_type == ValueType.Half and element_count == 2:
                element_size = 2

            to_read = diagonal or element_count

            for i in range(to_read):
                if i * element_size + 1 >= len(self.payload):
                    raise RuntimeError("Inlined payload is smaller than expected for the number of elements.")

                # Read element_size bytes
                value_bytes = self.payload[i * element_size : i * element_size + element_size]

                # Handle endianness
                int_value = int.from_bytes(value_bytes, byteorder=ENDIAN, signed=False)

                # vec2h need special handling stored as 2-byte inlined values
                if value_type == ValueType.Half and element_count == 2:
                    # Convert half to float
                    float_value = ValueRep.convert_half_to_float(int_value)
                    values.append(float_value)
                elif value_type == ValueType.Int:
                    values.append(int_value)
                else:
                    values.append(float(int_value))

            if diagonal:
                matrix = self.make_empty_matrix(diagonal)
                for i in range(diagonal):
                    matrix[i][i] = values[i]

                return matrix

            return values

        offset = self.go_to_payload_offset()
        if self.is_array and not offset:
            return values

        num_elements = 1
        if self.is_array:
            num_elements = self.read_int()

        for _ in range(num_elements):
            element = []
            for _ in range(element_count):
                bytes = self.filehandle.read(element_size)
                val = struct.unpack(element_format, bytes)[0]
                if element_size == data_sizes.HALF:
                    val = ValueRep.convert_half_to_float(val)
                element.append(val)

            if diagonal:
                element = list(self.convert_to_matrix(element, diagonal))

            values.append(element)

        if not self.is_array:
            return values[0]
        return values

    def make_empty_matrix(self, size):
        """Convenience method to create an empty matrix"""
        matrix = []
        for _ in range(size):
            row = []
            for _ in range(size):
                row.append(0.0)
            matrix.append(row)

        return matrix

    def convert_to_matrix(self, values, width):
        """Convenience method to convert an array of values to a matrix representation of a given width"""
        for i in range(0, len(values), width):
            yield values[i : i + width]

    def parse_list_ops(self):
        """Parses all the types of list ops. List ops are specified in a specific set of sub lists"""
        _ = self.go_to_payload_offset()
        header = ListOpHeader(self.read_int(data_sizes.FLAG_BYTE))

        explicit_items = None
        added_items_to_discard = []
        prepended_items = []
        appended_items = []
        deleted_items = []

        if header.add_explicit:
            explicit_items = self.parse_list_op_items()
        elif header.make_explicit:
            # Explicit but with no items means empty explicit list
            explicit_items = []

        if header.add_items:
            # add operation is deprecated; read to advance file pointer but may be discarded
            added_items_to_discard = self.parse_list_op_items()

        if header.prepend_items:
            prepended_items = self.parse_list_op_items()

        if header.append_items:
            appended_items = self.parse_list_op_items()

        if header.delete_items:
            deleted_items = self.parse_list_op_items()

        if header.reorder_items:
            # reorder operation is deprecated; read to advance file pointer but discard
            warnings.warn("ListOp 'reorder' operation is deprecated (discarding)")
            self.parse_list_op_items()

        # The add operation is commonly used in simple test cases even though it's been deprecated.
        # Apply a non-portable mapping from 'add' to 'append' when it is the only composable operation specified.
        if added_items_to_discard:
            if not any((prepended_items, deleted_items, appended_items)):
                warnings.warn("ListOp 'add' operation is deprecated. Elements will be mapped to 'append'.")
                appended_items = added_items_to_discard
            else:
                warnings.warn(
                    "ListOp 'add' operation is deprecated. Elements could not be mapped to 'append' and "
                    "will be discarded."
                )

        return (
            ListOp(explicit_items=UniqueList(explicit_items))
            if explicit_items is not None
            else ListOp(
                prepended_items=UniqueList(prepended_items),
                appended_items=UniqueList(appended_items),
                deleted_items=UniqueList(deleted_items),
            )
        )

    def parse_list_op_items(self):
        """List ops contain arrays of items of varied types stored as contiguous arrays"""
        num_elements = self.read_int()

        match self.type:
            case ValueType.TokenListOp | ValueType.PathListOp | ValueType.StringListOp:
                element_size = data_sizes.INDEX
            case ValueType.ReferenceListOp:
                element_size = data_sizes.REFERENCE
            case ValueType.PayloadListOp:
                element_size = data_sizes.PAYLOAD
            case ValueType.IntListOp | ValueType.UIntListOp:
                element_size = data_sizes.INT32
            case ValueType.Int64ListOp | ValueType.UInt64ListOp:
                element_size = data_sizes.UINT64
            case ValueType.UnregisteredValueListOp:
                element_size = data_sizes.VALUE_REP
            case _:
                raise NotImplementedError(f"{self.type.name} is not supported yet")

        elements = []
        for i in range(num_elements):
            elements.append(self.filehandle.read(element_size))

        match self.type:
            case ValueType.TokenListOp:
                return [self.parser.tokens[int.from_bytes(e, ENDIAN, signed=False)] for e in elements]
            case ValueType.PathListOp:
                return [self.parser.paths[int.from_bytes(e, ENDIAN, signed=False)] for e in elements]
            case ValueType.StringListOp:
                return [self.parser.strings[int.from_bytes(e, ENDIAN, signed=False)] for e in elements]
            case ValueType.IntListOp | ValueType.Int64ListOp:
                return [int.from_bytes(e, ENDIAN, signed=True) for e in elements]
            case ValueType.UIntListOp | ValueType.UInt64ListOp:
                return [int.from_bytes(e, ENDIAN, signed=False) for e in elements]
            case ValueType.PayloadListOp | ValueType.ReferenceListOp:
                return [self.parse_reference(e) for e in elements]
            case ValueType.UnregisteredValueListOp:
                values = [ValueRep(e, self.filehandle, self.parser) for e in elements]
                [v.process() for v in values]
                return values
            case _:
                raise NotImplementedError(f"{self.type.name} is not supported yet")

    def parse_reference(self, data):
        """References and payloads store data as an asset path index, a prim path index and a layer offset as two doubles"""
        asset_path_index = int.from_bytes(data[: data_sizes.INDEX], ENDIAN, signed=False)
        prim_path_index = int.from_bytes(data[data_sizes.INDEX : data_sizes.INDEX * 2], ENDIAN, signed=False)
        layer_offset_data = data[data_sizes.INDEX * 2 : data_sizes.PAYLOAD]

        asset_path = self.parser.strings[asset_path_index]
        prim_path = self.parser.paths[prim_path_index]

        if not (asset_path or prim_path):
            # Note: making crate error when a reference has neither an asset or prim
            # path diverges from current OpenUSD behavior.  OpenUSD does no validation
            # to ensure that at least one of the two is present.  Instead it will create
            # a reference, and use the "standard" behavior if the asset path is empty -
            # ie, use the layer stack where the reference is authored - and "standard"
            # behavior if the prim path is empty - ie, use the default prim of the layer
            # stack's root layer.

            raise ValueError("Reference has no asset or prim path")

        layer_offset = Retiming(
            struct.unpack("d", layer_offset_data[: data_sizes.DOUBLE])[0],
            struct.unpack("d", layer_offset_data[data_sizes.DOUBLE :])[0],
        )

        # NOTE: if we were going to process the customData dict, we would find it at:
        #
        #       metadata_offset = int.from_bytes(
        #          data[data_sizes.PAYLOAD : data_sizes.PAYLOAD + data_sizes.VALUE_REP],
        #          ENDIAN,
        #          signed=False,
        #      )
        #
        # ...but we can ignore it as it's vestigial

        # Determine target based on what's present
        if asset_path and prim_path:
            target = (data_types.Asset(asset_path), ObjectPath.from_str(prim_path))
        elif asset_path:
            target = data_types.Asset(asset_path)
        else:
            target = ObjectPath.from_str(prim_path)

        # Use Payload for payload types, Reference for reference types
        if self.type in (ValueType.Payload, ValueType.PayloadListOp):
            return Payload(target, layer_offset)
        else:
            return Reference(target, layer_offset)

    def parse_timesamples(self):
        """Timesamples are a dictionary of timecode values to a value representations"""
        offset = self.go_to_payload_offset()

        timecodes_offset = self.read_int()

        # Seek to Timecodes
        self.filehandle.seek(offset + timecodes_offset)
        timecodes_data = self.filehandle.read(data_sizes.INT64)
        timecodes_rep = ValueRep(timecodes_data, self.filehandle, self.parser)

        current_offset = self.filehandle.tell()
        values_offset = self.read_int()

        # Defer processing till after we query things
        timecodes_rep.process()

        # Seek to values
        self.filehandle.seek(current_offset + values_offset)
        num_values = self.read_int()
        values = []
        for i in range(num_values):
            data = self.filehandle.read(data_sizes.DOUBLE)
            rep = ValueRep(data, self.filehandle, self.parser)
            values.append((timecodes_rep.value[i], rep))

        for _, v in values:
            v.process()

        return values

    def parse_value_at_offset(self, target_offset=None):
        """A value is pointer to another value representation"""
        if target_offset:
            self.filehandle.seek(target_offset)
        else:
            self.go_to_payload_offset()
        data = self.filehandle.read(data_sizes.INT64)
        rep = ValueRep(data, self.filehandle, self.parser)
        rep.process()
        return rep

    def parse_payload(self):
        """Payloads are a specialized form of a reference"""
        offset = self.go_to_payload_offset()
        if not offset:
            return None
        data = self.filehandle.read(data_sizes.PAYLOAD)
        return self.parse_reference(data)

    def parse_unregistered_value(self):
        offset = self.go_to_payload_offset()
        local_offset = self.read_int()
        rep = self.parse_value_at_offset(target_offset=offset + local_offset)
        return rep

    def parse_variant_selection_map(self):
        """Variant selection maps are a contiguous array of key,value pairs where both point to a string"""
        _ = self.go_to_payload_offset()

        num_variants = self.read_int()
        variants = {}
        for i in range(num_variants):
            key = self.parser.strings[self.read_int(data_sizes.INDEX)]
            value = self.parser.strings[self.read_int(data_sizes.INDEX)]

            variants.setdefault(key, []).append(value)

        return variants

    def to_dict(self):
        """Convenience method to convert this value representation to a dictionary"""
        if isinstance(self.value, enum.Enum):
            val = self.value.name
        else:
            val = self.value
        return self.type.name, val

    @staticmethod
    def convert_half_to_float(val):
        """Convenience method to convert a half precision float to a standard precision float"""
        shifted_exp = 0x7C00 << 13

        output = (val & 0x7FFF) << 13  # Exponent/mantissa bits
        exponent = shifted_exp & output  # Just the exponent
        output += (127 - 15) << 23

        # Handle exponent special cases
        if exponent == shifted_exp:  # Inf/Nan
            output += (128 - 16) << 23
        elif exponent == 0:  # Denormalized
            output += 1 << 23

            out_float = output.to_bytes(data_sizes.FLOAT, ENDIAN, signed=False)
            out_float = struct.unpack("f", out_float)[0]

            magic = (113 << 23).to_bytes(data_sizes.FLOAT, ENDIAN, signed=False)
            magic = struct.unpack("f", magic)[0]
            out_float -= magic

            # Renormalize
            out_bytes = bytearray(struct.pack("f", out_float))
            output = int.from_bytes(out_bytes, ENDIAN, signed=False)

        output = output | (val & 0x8000) << 16  # Sign Bit
        output = output.to_bytes(data_sizes.FLOAT, ENDIAN, signed=False)
        output = struct.unpack("f", output)[0]

        return output

    @staticmethod
    def convert_float_to_half(val):
        """Convenience method to convert a standard precision float value to half precision representation"""
        # Convert float to raw bits
        f = struct.unpack("<I", struct.pack("<f", val))[0]

        # Extract sign, exponent, and mantissa
        sign = (f >> 31) & 0x1
        exp = (f >> 23) & 0xFF
        mantissa = f & 0x007FFFFF

        if exp == 255:  # NaN or Inf
            if mantissa != 0:
                # NaN
                mantissa = 512  # half NaN representation
            exp = 31
        elif exp > 127 + 15:  # Overflow to Inf
            exp = 31
            mantissa = 0
        elif exp < 127 - 14:  # Underflow to zero or denormalized
            if exp < 127 - 24:  # Too small, becomes zero
                exp = 0
                mantissa = 0
            else:
                # Denormalized number
                mantissa = (mantissa | 0x00800000) >> (1 + (127 - 14 - exp))
                exp = 0
        else:
            # Normalized number
            exp = exp - 127 + 15

        # Assemble the half-float bits
        half = (sign << 15) | (exp << 10) | (mantissa >> 13)
        return half

    def parse_relocates_map(self):
        """
        Constructs a relocation map. Relocation maps are stored as a contiguous pair of key,value indices into paths
        """
        values = {}
        if not self.go_to_payload_offset():
            return []

        value = self.read_int(size=data_sizes.UINT64)
        for i in range(value):
            k = self.read_int(size=data_sizes.INDEX)
            v = self.read_int(size=data_sizes.INDEX)

            k = self.parser.paths[k]
            v = self.parser.paths[v]

            values[k] = v

        return values

    def parse_splines(self):
        """Splines are fairly complex, so we read the array of spline elements and then combine them into
        a buffer passed to the Spline parser. Additionally, Splines may also have custom data after that is defined as
        a contiguous set of key,value pairs where the key is a timecode, and the value is a dictionary at that timecode
        """
        self.go_to_payload_offset()
        num_spline_elements = self.read_int()
        spline_data = []
        for i in range(num_spline_elements):
            spline_data.append(self.read_int(size=data_sizes.UINT8))

        num_custom_data = self.read_int()
        custom_data = {}
        for i in range(num_custom_data):
            key = self.filehandle.read(data_sizes.DOUBLE)
            key = struct.unpack("d", key)[0]

            current_pos = self.filehandle.tell()
            value = self.parse_dictionary(target_offset=current_pos)
            self.filehandle.seek(current_pos + data_sizes.UINT64)

            custom_data[key] = value

        return Spline(spline_data, custom_data)
