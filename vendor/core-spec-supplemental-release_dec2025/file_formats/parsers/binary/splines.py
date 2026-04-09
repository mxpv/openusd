import dataclasses
import enum
import pprint
import struct

from file_formats.parsers.binary import data_sizes


class CurveType(enum.IntEnum):
    Bezier = 0
    Hermite = 1

    def __str__(self):
        return self.name


class InterpolationMode(enum.IntEnum):
    Block = 0
    Held = 1
    Linear = 2
    Curve = 3

    def __str__(self):
        return self.name


class ExtrapolationMode(enum.IntEnum):
    Block = 0
    Held = 1
    Linear = 2
    Sloped = 3
    LoopRepeat = 4
    LoopReset = 5
    LoopOscillate = 6

    def __str__(self):
        return self.name


class CurveDataType(enum.IntEnum):
    Unspecified = 0
    Double = 1
    Float = 2
    Half = 3

    def get_type_identifier(self):
        if self == self.Float:
            return "f"
        elif self == self.Half:
            raise NotImplementedError("Cannot parse half yet")

        return "d"

    def __str__(self):
        return self.name


@dataclasses.dataclass
class LoopParameters:
    looping: bool = False
    proto_start: float = 0
    proto_end: float = 0
    num_pre_loops: int = 0
    num_post_loops: int = 0
    value_offset: float = 0


@dataclasses.dataclass
class Knot:
    dual_valued: bool = False
    next_interp: InterpolationMode = InterpolationMode.Block
    curve_type: CurveType = CurveType.Bezier
    pre_tan_maya_form: bool = False
    post_tan_maya_form: bool = False
    time: float = 0
    value: float = 0
    pre_value: float = 0
    pre_tan_width: float = 0
    post_tan_width: float = 0
    pre_tan_slope: float = 0
    post_tan_slope: float = 0


class Spline:
    """Splines are a fairly complex data type composed of several smaller data types.
    As such, its split out into its own parser and given a data buffer to parse."""

    def __init__(self, data, custom_data):
        self.custom_data = custom_data

        self.version = 0
        self.data_type: CurveDataType = CurveDataType.Unspecified
        self.timed_value: bool = False
        self.curve_type: CurveType = CurveType.Bezier
        self.pre_extrapolation_mode: ExtrapolationMode = ExtrapolationMode.Block
        self.post_extrapolation_mode: ExtrapolationMode = ExtrapolationMode.Block
        self.pre_extrapolation_slope: float = 0
        self.post_extrapolation_slope: float = 0
        self.loop_parameters: LoopParameters = LoopParameters()
        self.knots: list[Knot] = []

        self.parse(data)

    def parse(self, data):
        """Splines are versioned, so we check the header early to delegate the parsing to a specific versioned parser"""
        if not data:
            return
        data = bytearray(data)
        # Read First Header Byte
        header_byte, data = self.get_bytes(data)
        self.version = header_byte & 0x0F
        if self.version == 1:
            return self.parse_v1(header_byte, data)
        else:
            raise RuntimeError(f"Unsupported version of splines: {self.version}")

    def parse_v1(self, header_byte, data):
        """We handle the parsing of version 1 of splines here"""

        # The first header byte includes various data bits that are important to further parsing
        self.data_type = data_type = CurveDataType((header_byte & 0x30) >> 4)
        self.timed_value = header_byte & 0x40

        self.curve_type = CurveType((header_byte & 0x80) >> 7)

        # Read Second Header Byte to learn about the extrapolation and loop modes of the curve
        header_byte, data = self.get_bytes(data)
        pre_extrapolation = ExtrapolationMode(header_byte & 0x07)
        self.pre_extrapolation = pre_extrapolation
        if pre_extrapolation == ExtrapolationMode.Sloped:
            self.pre_extrapolation_slope, data = self.parse_bytes(data, "d")

        post_extrapolation = ExtrapolationMode((header_byte & 0x18) >> 3)
        self.post_extrapolation = post_extrapolation
        if post_extrapolation == ExtrapolationMode.Sloped:
            self.post_extrapolation_slope, data = self.parse_bytes(data, "d")

        self.loop_parameters.looping = has_loops = bool(header_byte & 0x40)
        if has_loops:
            self.loop_parameters.proto_start, data = self.parse_bytes(data, "d")
            self.loop_parameters.proto_end, data = self.parse_bytes(data, "d")
            self.loop_parameters.num_pre_loops, data = self.parse_bytes(data, "i")  # probably change to unsigned
            self.loop_parameters.num_post_loops, data = self.parse_bytes(data, "i")  # probably change to unsigned
            self.loop_parameters.value_offset, data = self.parse_bytes(data, "d")

        if data_type == CurveDataType.Unspecified:
            return

        knots_remaining, data = self.parse_bytes(data, "I")
        while knots_remaining:
            knot = Knot()
            self.knots.append(knot)
            knots_remaining -= 1

            flag_byte, data = self.get_bytes(data)
            knot.dual_valued = dual_valued = bool(flag_byte & 0x01)
            knot.next_interp = InterpolationMode((flag_byte & 0x06) >> 1)
            knot.curve_type = CurveType((flag_byte & 0x08) >> 3)

            knot.pre_tan_maya_form = bool(flag_byte & 0x10)
            knot.post_tan_maya_form = bool(flag_byte & 0x20)
            knot.time, data = self.parse_bytes(data, "d")
            knot.value, data = self.parse_bytes(data, data_type.get_type_identifier())

            if dual_valued:
                knot.pre_value, data = self.parse_bytes(data, data_type.get_type_identifier())

            if self.curve_type != CurveType.Hermite:
                knot.pre_tan_width, data = self.parse_bytes(data, "d")
                knot.post_tan_width, data = self.parse_bytes(data, "d")

            knot.pre_tan_slope, data = self.parse_bytes(data, data_type.get_type_identifier())
            knot.post_tan_slope, data = self.parse_bytes(data, data_type.get_type_identifier())

    @staticmethod
    def get_bytes(data, count=data_sizes.FLAG_BYTE):
        """Convenience method to get bytes from the buffer"""
        to_parse, data = data[:count], data[count:]
        if count == 1:
            to_parse = to_parse[0]
        else:
            to_parse = bytes(to_parse)
        return to_parse, data

    def parse_bytes(self, data, data_type):
        """Convenience method to parse some bytes into a given output type"""
        size = None
        if data_type == "d":
            size = data_sizes.DOUBLE
        elif data_type in ("i", "I"):
            size = data_sizes.INT32
        else:
            raise RuntimeError("Unsupported data type")
        post_bytes, data = self.get_bytes(data, size)
        post_value = struct.unpack(data_type, post_bytes)
        if not post_value:
            raise RuntimeError("Failed to parse data")

        return post_value[0], data

    def __repr__(self):
        return pprint.pformat(self.to_dict())

    def to_dict(self):
        return {
            "knots": self.knots,
            "custom_data": self.custom_data,
            "version": self.version,
            "data_type": self.data_type,
            "timed_value": self.timed_value,
            "curve_type": self.curve_type,
            "pre_extrapolation_mode": self.pre_extrapolation_mode,
            "pre_extrapolation_slope": self.pre_extrapolation_slope,
            "post_extrapolation_mode": self.post_extrapolation_mode,
            "post_extrapolation_slope": self.post_extrapolation_slope,
            "loop_parameters": self.loop_parameters,
        }
