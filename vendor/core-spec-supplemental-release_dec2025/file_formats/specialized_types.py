import collections
import dataclasses
import enum
import itertools
import typing

import data_types
import file_formats.verifiers


class ValueBlockSentinel:
    """State for the `default` or individual `timeSamples` to block weaker user opinions in value resolution."""

    __instance = None

    def __new__(cls, *args, **kwargs):
        if cls.__instance is None:
            cls.__instance = super().__new__(cls)
        return cls.__instance

    def __deepcopy__(self) -> typing.Self:
        return self

    def __copy__(self, memo) -> typing.Self:
        return self

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}()"

    def __str__(self) -> str:
        return "<ValueBlock>"


class ObjectPath:
    """Implementation of the necessary subset of the path grammar to represent paths to composed objects."""

    def __init__(self, prim_parts: typing.Sequence[data_types.Token], property_part: data_types.Token | None = None):
        self._prim_parts = tuple(prim_parts)
        self._property_part = property_part

        if not self._prim_parts:
            raise ValueError("At least one prim element is required to identify an object.")
        if not all(file_formats.verifiers.IdentifierVerifier(p) for p in self._prim_parts):
            raise ValueError(f"Prim names {self._prim_parts} should match: {file_formats.verifiers.IdentifierVerifier}")
        if self._property_part is not None and not file_formats.verifiers.PropertyNameVerifier(self._property_part):
            raise ValueError(
                f"Property name {self._property_part} should match {file_formats.verifiers.PropertyNameVerifier}"
            )

    def __hash__(self) -> int:
        return hash((self._prim_parts, self._property_part))

    def __eq__(self, other: typing.Self) -> bool:
        return self._prim_parts == other._prim_parts and self._property_part == other._property_part

    def __str__(self) -> str:
        prim_part_str = "/".join(("", *(str(p) for p in self._prim_parts)))
        return f"{prim_part_str}.{self._property_part}" if self._property_part else prim_part_str

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}(f{repr(self._prim_parts)}, {repr(self._property_part)})"

    @property
    def targets_prim(self) -> bool:
        return not self.targets_property

    @property
    def targets_property(self) -> bool:
        return bool(self._property_part)

    @classmethod
    def from_str(cls, value: str) -> typing.Self:
        """Construct an ObjectPath from an absolute text representation of the path."""
        prim_part, _, property_part = value.partition(".")
        if not prim_part.startswith("/"):
            raise ValueError("`from_str` requires an absolute path. Consider `join` for relative paths.")
        tokenized_prim_part = prim_part.split("/")[1:]
        return ObjectPath((data_types.Token(p) for p in tokenized_prim_part), data_types.Token(property_part) or None)

    def join(self, value: str) -> typing.Self:
        """Construct a new ObjectPath with the from a relative text representation of the path.

        If called on an absolute path, returns the same result as if `from_str` has been called.
        """
        if self.targets_property:
            raise ValueError("ObjectPath targeting a property cannot be joined")
        if value.startswith("/"):
            return self.from_str(value)
        ancestors_to_remove = len(
            list(itertools.takewhile(lambda substr: substr == tuple("../"), itertools.batched(value, n=3)))
        )
        relative_prim_part, _, property_part = value[ancestors_to_remove * len("../") :].partition(".")
        tokenized_relative_prim_part = relative_prim_part.split("/") if relative_prim_part else []
        if ancestors_to_remove == 0:
            without_ancestors = self._prim_parts
        elif ancestors_to_remove > len(self._prim_parts):
            raise ValueError("Relative path would remove too many ancestors")
        else:
            without_ancestors = self._prim_parts[:-ancestors_to_remove]
        return ObjectPath(
            (*without_ancestors, *(data_types.Token(p) for p in tokenized_relative_prim_part)),
            data_types.Token(property_part) or None,
        )


@dataclasses.dataclass(frozen=True)
class Retiming:
    """Retiming is used to apply time offsets during value resolution when resolving external assets"""

    offset: data_types.Double = data_types.Double(0.0)
    scale: data_types.Double = data_types.Double(1.0)

    def __add__(self, other: typing.Self) -> typing.Self:
        return Retiming(
            (self.offset * other.scale) + other.offset,
            self.scale * other.scale,
        )

    def apply(self, frame: float) -> float:
        return (frame * self.scale) + self.offset


@dataclasses.dataclass(frozen=True)
class Relocate:
    """Specifies a source and target as used by the layer spec `layerRelocates` field"""

    source: ObjectPath
    target: ObjectPath | None

    def __post_init__(self):
        if not self.source.targets_prim:
            raise ValueError("Source must target prim path.")
        if self.target and not self.target.targets_prim:
            raise ValueError("Authored target must target prim path.")


@dataclasses.dataclass(frozen=True)
class Reference:
    """Specifies a reference target as used by the prim spec `references` field

    Provides hashing and equality for listop support.
    """

    target: data_types.Asset | ObjectPath | tuple[data_types.Asset, ObjectPath]
    retiming: Retiming = dataclasses.field(default_factory=Retiming)

    def __post_init__(self):
        if not isinstance(self.target, data_types.Asset.__origin__):
            if isinstance(self.target, ObjectPath):
                target_path = self.target
            else:
                target_path = self.target[1]
            if not target_path.targets_prim:
                raise ValueError("Target object path must target prim.")


@dataclasses.dataclass(frozen=True)
class Payload:
    """Specifies a payload target as used by the prim spec `references` field

    Provides hashing and equality for listop support.
    """

    target: data_types.Asset | ObjectPath | tuple[data_types.Asset, ObjectPath]
    retiming: Retiming = dataclasses.field(default_factory=Retiming)

    def __post_init__(self):
        if not isinstance(self.target, data_types.Asset.__origin__):
            if isinstance(self.target, ObjectPath):
                target_path = self.target
            else:
                target_path = self.target[1]
            if not target_path.targets_prim:
                raise ValueError("Target object path must target prim.")


class Variability(enum.StrEnum):
    """Specialized type for the `variability` field"""

    Varying = "varying"
    Uniform = "uniform"

    def __str__(self):
        return str(self.value)


class Specifier(enum.StrEnum):
    """Specialized type for the `specifier` field"""

    Def = "def"
    Over = "over"
    Class = "class"


# Types that may participate in attribute value resolution as specified by the `default` and `timeSamples` fields
# Does not include `opaque` foundational type since its attributes may not take on any value other than
# ValueBlock.
ValueType: typing.TypeAlias = (
    data_types.ScalarType
    | data_types.ScalarArrayType
    | data_types.Utf8TextType
    | data_types.Utf8TextArrayType
    | data_types.DimensionedType
    | data_types.DimensionedArrayType
)


class DefaultValue:
    """Wraps any type authorable to the `default` field

    May take on an empty state that is unserializable to the `default` field."""

    __slots__ = "_value"

    def __init__(self, value: ValueType | ValueBlockSentinel | None = None):
        self._value = value

    def __str__(self) -> str:
        return str(self._value) if self._value is not None else "<Empty>"

    def __repr__(self) -> str:
        return (
            f"{type(self).__qualname__}({repr(self._value)})"
            if self._value is not None
            else f"{type(self).__qualname__}()"
        )

    @property
    def value(self) -> ValueType | ValueBlockSentinel | None:
        """Returns the stored value or None if no value is stored

        Note that python None and the textual scene description `None` are not the same."""
        return self._value

    @property
    def empty(self) -> bool:
        """Returns whether or not a value is stored"""
        return self._value is None


class TimeSampleMap(collections.abc.Mapping[data_types.Double, ValueType | ValueBlockSentinel]):
    """Mapping of double precision times to values at those times.

    Individual time samples may be assigned the ValueBlockSentinel.

    While this TimeSampleMap may be heterogenous, every time sample must be of the same type (or a ValueBlock) to agree
    with an attribute's `typeName` field."""

    __slots__ = "_time_samples"

    def __init__(self, samples: typing.Mapping[data_types.Double, ValueType | ValueBlockSentinel] | None = None):
        self._time_samples = (
            {time: copy.copy(samples[time]) for time in sorted(samples.keys())} if samples is not None else {}
        )

    def __getitem__(self, time: data_types.Double) -> ValueType | ValueBlockSentinel:
        return self._time_samples[time]

    def __len__(self) -> int:
        return len(self._time_samples)

    def __iter__(self) -> data_types.Double:
        for time in self._time_samples:
            yield time

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}({repr(self._time_samples)})"

    def __str__(self) -> str:
        return str(str(self._time_samples))


VariantSelectionMap: typing.TypeAlias = dict[str, str]


class SplineCurveType(enum.StrEnum):
    Bezier = "bezier"
    Hermite = "hermite"


class SplineExtrapolationMode(enum.StrEnum):
    NoneMode = "none"
    Held = "held"
    Linear = "linear"
    Sloped = "sloped"
    Looprepeat = "looprepeat"
    Loopreset = "loopreset"
    Looposcillate = "looposcillate"


class SplineInterpMode(enum.StrEnum):
    NoneMode = "none"
    Held = "held"
    Linear = "linear"
    Curve = "curve"


@dataclasses.dataclass(frozen=True)
class SplineExtrapolation:
    mode: SplineExtrapolationMode = SplineExtrapolationMode.Held
    slope: float = 0.0

    def __str__(self) -> str:
        return f"{self.mode} {self.slope}"


@dataclasses.dataclass(frozen=True)
class SplineLoopParameters:
    proto_start: float = 0.0
    proto_end: float = 0.0
    num_pre_loops: int = 0
    num_post_loops: int = 0
    value_offset: float = 0.0

    def __str__(self) -> str:
        return f"{self.proto_start} {self.proto_end} {self.num_pre_loops} {self.num_post_loops} {self.value_offset}"


@dataclasses.dataclass(frozen=True)
class SplineKnot:
    time: float = 0.0
    pre_tan_width: float = 0.0
    post_tan_width: float = 0.0
    value: float = 0.0
    pre_value: float = 0.0
    pre_tan_slope: float = 0.0
    post_tan_slope: float = 0.0
    next_interp_mode: SplineInterpMode = SplineInterpMode.Held

    def __str__(self) -> str:
        return (
            f"{self.time}: {self.pre_tan_width} {self.post_tan_width} {self.next_interp_mode} "
            f"{self.value} {self.pre_value} {self.pre_tan_slope} {self.post_tan_slope}"
        )


@dataclasses.dataclass(frozen=True)
class Spline:
    curve_type: SplineCurveType = SplineCurveType.Bezier
    pre_extrapolation: SplineExtrapolation = None
    post_extrapolation: SplineExtrapolation = None
    loop_parameters: SplineLoopParameters = None
    knots: list[SplineKnot] = dataclasses.field(default_factory=list)
    knot_custom_data: dict[str, typing.Any] = dataclasses.field(default_factory=dict)

    def __str__(self) -> str:
        return (
            f"{self.curve_type}, {self.pre_extrapolation}, {self.post_extrapolation}, "
            f"{self.loop_parameters}, [{', '.join(self.knots)}], {self.knot_custom_data}"
        )


if __name__ == "__main__":
    print(ObjectPath.from_str("/hello/world"))
    print(ObjectPath.from_str("/hello/world").join(".attr"))
    print(ObjectPath.from_str("/hello/world").join("prim"))
    print(ObjectPath.from_str("/hello/world").join("../mars"))
    # Note the accent mark on 'buondì' to exercise Unicode support.
    print(ObjectPath.from_str("/hello/world").join("../../buondì/terra"))
    print(hash(Reference(ObjectPath.from_str("/hello/world"))))
    print(Reference(ObjectPath.from_str("/hello/world")) == Reference(ObjectPath.from_str("/hello/world")))
    print(hash(Payload(ObjectPath.from_str("/hello/world"))))
    print(repr(Spline()))
    print(Spline())
