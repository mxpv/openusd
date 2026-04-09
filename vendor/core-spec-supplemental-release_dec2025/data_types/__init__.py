import collections
import ctypes
import dataclasses
import enum
import functools
import re
import typing

import data_types.listop


@functools.total_ordering
class Asset:
    """Unicode string that may not contain control code characters designed to store an asset path"""

    __slots__ = ("_value",)
    _CONTROL_CODE_PATTERN = re.compile(r"[\u0000-\u001F\u0080-\u009f]")

    def __init__(self, value: str = ""):
        if first_match := re.search(self._CONTROL_CODE_PATTERN, value):
            raise ValueError(f"Control codes are not an allowed 'Asset' value: Found at {first_match.span}")
        self._value = value

    def __hash__(self) -> bool:
        return hash(self._value)

    def __str__(self) -> str:
        return self._value

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}({repr(self._value)})"

    def __eq__(self, other: typing.Self) -> bool:
        return self._value == str(other)

    def __lt__(self, other: typing.Self) -> bool:
        return self._value < str(other)


@functools.total_ordering
class Token:
    """String with amortized constant time hashing and equality comparison.

    All tokens are immortal in the reference implementation, but this is not a requirement."""

    __slots__ = ("__hash", "__value")
    __registry = {}

    def __new__(cls, value: str = ""):
        if value not in cls.__registry:
            cls.__registry[value] = super().__new__(cls)
        return cls.__registry[value]

    def __init__(self, value: str = ""):
        if not hasattr(self, "__value"):
            self.__value = value
        if not hasattr(self, "__hash"):
            self.__hash = hash(self.__value)

    def __copy__(self) -> typing.Self:
        return self

    def __deepcopy__(self, memo) -> typing.Self:
        return self

    def __bool__(self) -> bool:
        return bool(self.__value)

    def __hash__(self) -> bool:
        return self.__hash

    def __str__(self) -> str:
        return str(self.__value)

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}({repr(self.__value)})" if self.__value else f"{type(self).__qualname__}()"

    def __eq__(self, other: typing.Self) -> bool:
        return self is other

    def __lt__(self, other: typing.Self) -> bool:
        return self.__value < other.__value


@functools.total_ordering
class TimeCode:
    __slots__ = ("_value",)

    def __init__(self, value: float | None = None):
        self._value = value

    def __repr__(self) -> str:
        return (
            f"{type(self).__qualname__}({repr(self._value)})"
            if self._value is not None
            else f"{type(self).__qualname__}()"
        )

    def __str__(self) -> str:
        return str(self._value) if self._value is not None else "<Default>"

    def __float__(self) -> float:
        return float(self._value)

    def __eq__(self, other: typing.Self) -> bool:
        return self._value == other._value

    def __hash__(self) -> int:
        return hash(self._value)

    def __lt__(self, other: typing.Self) -> bool:
        if other._value is None:
            return False
        elif self._value is None:
            return True
        return float(self._value) < float(other)


class Quaternion(typing.NamedTuple):
    i: float
    j: float
    k: float
    r: float


class SemanticRole(enum.StrEnum):
    Color = "color"
    Normal = "normal"
    Point = "point"
    Vector = "vector"
    Frame = "frame"
    TextureCoord = "texCoord"
    Group = "group"


@dataclasses.dataclass(frozen=True)
class SemanticAlias:
    alias: str
    role: SemanticRole


@dataclasses.dataclass(frozen=True)
class CTypeHint:
    """Type annotation that stores ctype equivalent of the underlying data type"""

    ctype: type


@dataclasses.dataclass(frozen=True)
class HalfTypeHint:
    """Type annotation indicating the underyling type is a half float which doesn't have a corresponding ctype"""

    size: int = 1


class Utf8TextTypeHint:
    """Type annotation sentinel that the underlying type is string-like and can be encoded to utf-8 after converting to a string."""


class TimeCodeTypeHint:
    """Type annotation sentinel that the underyling type is a TimeCode"""


@dataclasses.dataclass(frozen=True)
class ValueHint:
    """Foundational value type definition of values and elements"""

    name: str
    hint: CTypeHint | HalfTypeHint | Utf8TextTypeHint | TimeCodeTypeHint
    aliases: tuple[SemanticAlias, ...] = tuple()

    def __post_init__(self):
        pattern = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*((\[\])|(⟨⟩))?$")
        if not re.match(pattern, self.name):
            raise ValueError(f"ValueHintName '{self.name}' should conform to {pattern.pattern}")

        counter = collections.Counter(alias.alias for alias in self.aliases)
        if any(v != 1 for v in counter.values()):
            raise ValueError("Semantic alias names must be unique")

    def __str__(self) -> str:
        return str(self.name)

    def alias_names(self) -> tuple[str, ...]:
        for alias in self.aliases:
            yield alias.name

    def role_by_alias_name(self, alias_name: str) -> SemanticRole:
        for alias in aliases:
            if alias.name == alias_name:
                return alias.role


class OpaqueHint:
    @property
    def name(self) -> str:
        return "opaque"

    def __repr__(self) -> str:
        return f"{type(self).__qualname__}()"

    def __str__(self) -> str:
        return str(self.name)

    @property
    def aliases(self) -> tuple[SemanticAlias, ...]:
        return (SemanticAlias("group", SemanticRole.Group),)

    @property
    def alias_names(self) -> tuple[str, ...]:
        return ("group",)

    @property
    def role_by_alias_name(self, alias_name: str) -> SemanticRole:
        match alias_name:
            case "group":
                return SemanticRole.Group
            case _:
                raise ValueError(f"{alias_name} is not a valid semantic alias for {self}.")


@dataclasses.dataclass(frozen=True)
class ArrayHint:
    element_type: ValueHint

    @property
    def name(self) -> str:
        return f"{self.element_type.name}[]"

    @property
    def aliases(self) -> tuple[SemanticAlias, ...]:
        return tuple(SemanticAlias(f"{alias.alias}[]", alias.role) for alias in self.element_type.aliases)

    def role_by_alias_name(self, alias_name: str) -> SemanticRole:
        if not alias_name.endswith("[]"):
            raise ValueError("ArrayHints must end with []")
        for alias in self.element_type.aliases:
            if alias.alias == alias_name[:2]:
                return alias.role
        raise ValueError("No")


@dataclasses.dataclass(frozen=True)
class ListopHint:
    element_type: ValueHint

    def __post_init__(self):
        if self.element_type.aliases:
            raise TypeError("Listop types do not support semantic roles.")

    @property
    def name(self) -> str:
        return f"listop<{self.element_type.name}>"

    @property
    def aliases(self) -> tuple[SemanticAlias, ...]:
        return tuple()

    def role_by_alias_name(self, alias_name: str) -> SemanticRole:
        raise ValueError("Listop types do not support semantic roles.")


@dataclasses.dataclass(frozen=True)
class DictionaryHint:
    name: str

    @property
    def aliases(self) -> tuple[SemanticAlias, ...]:
        return tuple()

    @property
    def role_by_alias_name(self, alias_name: str) -> SemanticRole:
        raise ValueError("Dictionaries do not have type aliases.")


def type_hint(data_type: type) -> ValueHint | ListopHint | DictionaryHint | ArrayHint | OpaqueHint | None:
    return next(
        (
            arg
            for arg in typing.get_args(data_type)
            if isinstance(arg, (ValueHint, ListopHint, DictionaryHint, ArrayHint, OpaqueHint))
        ),
        None,
    )


def type_name(data_type: type) -> str | None:
    return hint.name if (hint := type_hint(data_type)) else None


# def type_name_agrees_with(name: str, data_type: type) -> bool:
#     return (name == type_name(data_type) or (name in a.alias for a.alias in hint.aliases
#             if isinstance(hint := type_hint(data_type), (ValueHint, ListopHint, ArrayHint, OpaqueHint)) else False))


Bool = typing.Annotated[bool, ValueHint("bool", CTypeHint(ctypes.c_bool))]
Int = typing.Annotated[int, ValueHint("int", CTypeHint(ctypes.c_int))]
Int64 = typing.Annotated[int, ValueHint("int64", CTypeHint(ctypes.c_int64))]
UChar = typing.Annotated[int, ValueHint("uchar", CTypeHint(ctypes.c_uint8))]
UInt = typing.Annotated[int, ValueHint("uint", CTypeHint(ctypes.c_uint32))]
UInt64 = typing.Annotated[int, ValueHint("uint64", CTypeHint(ctypes.c_uint64))]
Half = typing.Annotated[float, ValueHint("half", HalfTypeHint())]
Float = typing.Annotated[float, ValueHint("float", CTypeHint(ctypes.c_float))]
Double = typing.Annotated[float, ValueHint("double", CTypeHint(ctypes.c_double))]
# Note that time code gets redefined here to attach type annotations
TimeCode = typing.Annotated[TimeCode, ValueHint("timecode", TimeCodeTypeHint())]

ScalarType: typing.TypeAlias = Bool | Int | Int64 | UChar | UInt | UInt64 | Half | Float | Double | TimeCode

String = typing.Annotated[str, ValueHint("string", Utf8TextTypeHint())]
# Note that asset and token get redefined here to attach type annotations
Asset = typing.Annotated[Asset, ValueHint("asset", Utf8TextTypeHint())]
Token = typing.Annotated[Token, ValueHint("token", Utf8TextTypeHint())]

Utf8TextType = String | Asset | Token

Opaque = typing.Annotated[None, ValueHint("opaque", OpaqueHint, aliases=(SemanticAlias("group", SemanticRole.Group),))]

Half2 = typing.Annotated[
    tuple[(float,) * 2],
    ValueHint("half2", HalfTypeHint(2), aliases=(SemanticAlias("texCoord2h", SemanticRole.TextureCoord),)),
]
Half3 = typing.Annotated[
    tuple[(float,) * 3],
    ValueHint(
        "half3",
        HalfTypeHint(3),
        aliases=(
            SemanticAlias("texCoord3h", SemanticRole.TextureCoord),
            SemanticAlias("color3h", SemanticRole.Color),
            SemanticAlias("point3h", SemanticRole.Point),
            SemanticAlias("normal3h", SemanticRole.Normal),
            SemanticAlias("vector3h", SemanticRole.Vector),
        ),
    ),
]
Half4 = typing.Annotated[
    tuple[(float,) * 4], ValueHint("half4", HalfTypeHint(4), aliases=(SemanticAlias("color4h", SemanticRole.Color),))
]
Float2 = typing.Annotated[
    tuple[(float,) * 2],
    ValueHint(
        "float2", CTypeHint(ctypes.c_float * 2), aliases=(SemanticAlias("texCoord2f", SemanticRole.TextureCoord),)
    ),
]
Float3 = typing.Annotated[
    tuple[(float,) * 3],
    ValueHint(
        "float3",
        CTypeHint(ctypes.c_float * 3),
        aliases=(
            SemanticAlias("texCoord3f", SemanticRole.TextureCoord),
            SemanticAlias("color3f", SemanticRole.Color),
            SemanticAlias("point3f", SemanticRole.Point),
            SemanticAlias("normal3f", SemanticRole.Normal),
            SemanticAlias("vector3f", SemanticRole.Vector),
        ),
    ),
]
Float4 = typing.Annotated[
    tuple[(float,) * 4],
    ValueHint("float4", CTypeHint(ctypes.c_float * 4), aliases=(SemanticAlias("color4f", SemanticRole.Color),)),
]
Double2 = typing.Annotated[
    tuple[(float,) * 2],
    ValueHint(
        "double2", CTypeHint(ctypes.c_double * 2), aliases=(SemanticAlias("texCoord2d", SemanticRole.TextureCoord),)
    ),
]
Double3 = typing.Annotated[
    tuple[(float,) * 3],
    ValueHint(
        "double3",
        CTypeHint(ctypes.c_double * 3),
        aliases=(
            SemanticAlias("texCoord3d", SemanticRole.TextureCoord),
            SemanticAlias("color3d", SemanticRole.Color),
            SemanticAlias("point3d", SemanticRole.Point),
            SemanticAlias("normal3d", SemanticRole.Normal),
            SemanticAlias("vector3d", SemanticRole.Vector),
        ),
    ),
]
Double4 = typing.Annotated[
    tuple[(float,) * 4],
    ValueHint("double4", CTypeHint(ctypes.c_double * 4), aliases=(SemanticAlias("color4d", SemanticRole.Color),)),
]
Int2 = typing.Annotated[tuple[(int,) * 2], ValueHint("int2", CTypeHint(ctypes.c_int * 2))]
Int3 = typing.Annotated[tuple[(int,) * 3], ValueHint("int3", CTypeHint(ctypes.c_int * 3))]
Int4 = typing.Annotated[tuple[(int,) * 4], ValueHint("int4", CTypeHint(ctypes.c_int * 4))]
Matrix2d = typing.Annotated[
    tuple[(tuple[(float,) * 2],) * 2], ValueHint("matrix2d", CTypeHint(ctypes.c_double * 2 * 2))
]
Matrix3d = typing.Annotated[
    tuple[(tuple[(float,) * 3],) * 3], ValueHint("matrix3d", CTypeHint(ctypes.c_double * 3 * 3))
]
Matrix4d = typing.Annotated[
    tuple[(tuple[(float,) * 4],) * 4],
    ValueHint("matrix4d", CTypeHint(ctypes.c_double * 4 * 4), aliases=(SemanticAlias("frame4d", SemanticRole.Frame),)),
]
Quath = typing.Annotated[Quaternion, ValueHint("quath", HalfTypeHint(4))]
Quatf = typing.Annotated[Quaternion, ValueHint("quatf", CTypeHint(ctypes.c_float * 4))]
Quatd = typing.Annotated[Quaternion, ValueHint("quatd", CTypeHint(ctypes.c_double * 4))]

DimensionedType = (
    Half2
    | Half3
    | Half4
    | Float2
    | Float3
    | Float4
    | Double2
    | Double3
    | Double4
    | Matrix2d
    | Matrix3d
    | Matrix4d
    | Quath
    | Quatf
    | Quatd
    | Int2
    | Int3
    | Int4
)

BoolArray = typing.Annotated[list[Bool], ArrayHint(type_hint(Bool))]
IntArray = typing.Annotated[list[Int], ArrayHint(type_hint(Int))]
Int64Array = typing.Annotated[list[Int64], ArrayHint(type_hint(Int64))]
UCharArray = typing.Annotated[list[UChar], ArrayHint(type_hint(UChar))]
UIntArray = typing.Annotated[list[UInt], ArrayHint(type_hint(UInt))]
UInt64Array = typing.Annotated[list[UInt64], ArrayHint(type_hint(UInt64))]
HalfArray = typing.Annotated[list[Half], ArrayHint(type_hint(Half))]
FloatArray = typing.Annotated[list[Float], ArrayHint(type_hint(Float))]
DoubleArray = typing.Annotated[list[Double], ArrayHint(type_hint(Double))]
TimeCodeArray = typing.Annotated[list[TimeCode], ArrayHint(type_hint(TimeCode))]

ScalarArrayType: typing.TypeAlias = (
    BoolArray
    | IntArray
    | Int64Array
    | UCharArray
    | UIntArray
    | UInt64Array
    | HalfArray
    | FloatArray
    | DoubleArray
    | TimeCodeArray
)

StringArray = typing.Annotated[list[String], ArrayHint(type_hint(String))]
AssetArray = typing.Annotated[list[Asset], ArrayHint(type_hint(Asset))]
TokenArray = typing.Annotated[list[Token], ArrayHint(type_hint(Token))]

Utf8TextArrayType = StringArray | AssetArray | TokenArray

Half2Array = typing.Annotated[list[Half2], ArrayHint(type_hint(Half2))]
Half3Array = typing.Annotated[list[Half3], ArrayHint(type_hint(Half3))]
Half4Array = typing.Annotated[list[Half4], ArrayHint(type_hint(Half4))]
Float2Array = typing.Annotated[list[Float2], ArrayHint(type_hint(Float2))]
Float3Array = typing.Annotated[list[Float3], ArrayHint(type_hint(Float3))]
Float4Array = typing.Annotated[list[Float4], ArrayHint(type_hint(Float4))]
Double2Array = typing.Annotated[list[Double2], ArrayHint(type_hint(Double2))]
Double3Array = typing.Annotated[list[Double3], ArrayHint(type_hint(Double3))]
Double4Array = typing.Annotated[list[Double4], ArrayHint(type_hint(Double4))]
Int2Array = typing.Annotated[list[Int2], ArrayHint(type_hint(Int2))]
Int3Array = typing.Annotated[list[Int3], ArrayHint(type_hint(Int3))]
Int4Array = typing.Annotated[list[Int4], ArrayHint(type_hint(Int4))]
Matrix2dArray = typing.Annotated[list[Matrix2d], ArrayHint(type_hint(Matrix2d))]
Matrix3dArray = typing.Annotated[list[Matrix3d], ArrayHint(type_hint(Matrix3d))]
Matrix4dArray = typing.Annotated[list[Matrix4d], ArrayHint(type_hint(Matrix4d))]
QuathArray = typing.Annotated[list[Quath], ArrayHint(type_hint(Quath))]
QuatfArray = typing.Annotated[list[Quatf], ArrayHint(type_hint(Quatf))]
QuatdArray = typing.Annotated[list[Quatd], ArrayHint(type_hint(Quatd))]

DimensionedArrayType = (
    Half2Array
    | Half3Array
    | Half4Array
    | Float2Array
    | Float3Array
    | Float4Array
    | Double2Array
    | Double3Array
    | Double4Array
    | Matrix2dArray
    | Matrix3dArray
    | Matrix4dArray
    | QuathArray
    | QuatfArray
    | QuatdArray
    | Int2Array
    | Int3Array
    | Int4Array
)

Dictionary = typing.Annotated[
    dict[
        String,
        ScalarType
        | Utf8TextType
        | DimensionedType
        | ScalarArrayType
        | Utf8TextArrayType
        | DimensionedArrayType
        | "Dictionary",
    ],
    DictionaryHint("dictionary"),
]

StringListOp = typing.Annotated[data_types.listop.ListOp[String], ListopHint(type_hint(String))]
TokenListOp = typing.Annotated[data_types.listop.ListOp[Token], ListopHint(type_hint(Token))]
IntListOp = typing.Annotated[data_types.listop.ListOp[Int], ListopHint(type_hint(Int))]
Int64ListOp = typing.Annotated[data_types.listop.ListOp[Int64], ListopHint(type_hint(Int64))]
UIntListOp = typing.Annotated[data_types.listop.ListOp[UInt], ListopHint(type_hint(UInt))]
UInt64ListOp = typing.Annotated[data_types.listop.ListOp[UInt64], ListopHint(type_hint(UInt64))]

FoundationalType = (
    ScalarType
    | ScalarArrayType
    | Utf8TextType
    | Utf8TextArrayType
    | DimensionedType
    | DimensionedArrayType
    | Opaque
    | Dictionary
    | StringListOp
    | TokenListOp
    | IntListOp
    | Int64ListOp
    | UIntListOp
    | UInt64ListOp
)

if __name__ == "__main__":
    print(Asset("path/to/asset.usd"))
    print(Asset("uri://path/to/asset.usd"))
    print(Token())
    print(Token("hello"))
    print(TimeCode())
    print(TimeCode(5.0))
    print(SemanticRole.Color)
