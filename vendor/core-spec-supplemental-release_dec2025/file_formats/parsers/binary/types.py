import enum


class SpecForm(enum.IntEnum):
    Unknown = 0
    Attribute = 1
    Connection = 2
    Expression = 3
    Mapper = 4
    MapperArg = 5
    Prim = 6
    PseudoRoot = 7
    Relationship = 8
    RelationshipTarget = 9
    Variant = 10
    VariantSet = 11
    Invalid = 12

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


class ValueType(enum.IntEnum):
    # ⚠️ means that a test doesn't exist in this repo yet
    Unknown = 0  # ⚠️
    Bool = 1
    UChar = 2
    Int = 3
    UInt = 4
    Int64 = 5
    UInt64 = 6
    Half = 7
    Float = 8
    Double = 9
    String = 10
    Token = 11
    AssetPath = 12
    Matrix2d = 13
    Matrix3d = 14
    Matrix4d = 15
    Quatd = 16
    Quatf = 17
    Quath = 18
    Vec2d = 19
    Vec2f = 20
    Vec2h = 21
    Vec2i = 22
    Vec3d = 23
    Vec3f = 24
    Vec3h = 25
    Vec3i = 26
    Vec4d = 27
    Vec4f = 28
    Vec4h = 29
    Vec4i = 30
    Dictionary = 31
    TokenListOp = 32
    StringListOp = 33
    PathListOp = 34
    ReferenceListOp = 35
    IntListOp = 36  # ⚠️
    Int64ListOp = 37  # ⚠️
    UIntListOp = 38  # ⚠️
    UInt64ListOp = 39  # ⚠️
    PathVector = 40
    TokenVector = 41
    Specifier = 42
    Permission = 43
    Variability = 44
    VariantSelectionMap = 45
    TimeSamples = 46
    Payload = 47
    DoubleVector = 48
    LayerOffsetVector = 49
    StringVector = 50
    ValueBlock = 51
    Value = 52
    UnregisteredValue = 53  # ⚠️
    UnregisteredValueListOp = 54  # ⚠️
    PayloadListOp = 55
    TimeCode = 56
    PathExpression = 57
    Relocates = 58
    Spline = 59

    @property
    def supports_array(self):
        return self.value < 31 or self.value > 55

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


class Specifier(enum.IntEnum):
    Def = 0
    Over = 1
    Class = 2

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


class Variability(enum.IntEnum):
    Varying = 0
    Uniform = 1

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


class Permission(enum.IntEnum):
    Public = 0
    Private = 1

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name


class ListOpHeader:
    def __init__(self, data):
        self.make_explicit = bool(data & (1 << 0))
        self.add_explicit = bool(data & (1 << 1))
        self.add_items = bool(data & (1 << 2))
        self.delete_items = bool(data & (1 << 3))
        self.reorder_items = bool(data & (1 << 4))
        self.prepend_items = bool(data & (1 << 5))
        self.append_items = bool(data & (1 << 6))
