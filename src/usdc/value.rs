//! Types read from the usdc file.

use core::fmt;

use anyhow::{Context as _, Result};
use bytemuck::{Pod, Zeroable};
use strum::{Display, EnumCount, FromRepr};

/// Value in file representation.
///
/// Consists of a 2 bytes of type information (type enum value, array bit,
/// and inlined-value bit) and 6 bytes of data.
///
/// If possible, we attempt to store certain values directly in the local data,
/// such as ints, floats, enums, and special-case values of other types (zero
/// vectors, identity matrices, etc).
///
/// For values that aren't stored inline, the 6 data bytes are the offset from
/// the start of the file to the value's location.
#[repr(transparent)]
#[derive(Debug, Default, Copy, Clone, Pod, Zeroable)]
pub struct Value(pub u64);

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "ValueRep {} (ty={}, inlined={}, array={}, compressed={})",
            self.payload(),
            self.ty().unwrap_or_default(),
            self.is_inlined(),
            self.is_array(),
            self.is_compressed()
        )
    }
}

impl Value {
    const ARRAY_BIT: u64 = 1 << 63;
    const INLINED_BIT: u64 = 1 << 62;
    const COMPRESSED_BIT: u64 = 1 << 61;
    const PAYLOAD_MASK: u64 = ((1 << 48) - 1);

    #[inline]
    pub fn ty(self) -> Result<Type> {
        let index = ((self.data() >> 48) & 0xFF) as u32;
        Type::from_repr(index).with_context(|| format!("Unable to parse type enum {}", index))
    }

    #[inline]
    pub fn payload(self) -> u64 {
        self.data() & Self::PAYLOAD_MASK
    }

    #[inline]
    fn data(self) -> u64 {
        self.0
    }

    #[inline]
    pub fn is_compressed(self) -> bool {
        self.data() & Self::COMPRESSED_BIT != 0
    }

    #[inline]
    pub fn is_inlined(self) -> bool {
        self.data() & Self::INLINED_BIT != 0
    }

    pub fn is_array(self) -> bool {
        self.data() & Self::ARRAY_BIT != 0
    }
}

#[repr(u32)]
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, FromRepr, EnumCount, Display)]
pub enum Type {
    #[default]
    Invalid = 0,

    Bool = 1,
    UChar = 2,
    Int = 3,
    Uint = 4,
    Int64 = 5,
    Uint64 = 6,
    Half = 7,
    Float = 8,
    Double = 9,
    String = 10,
    Token = 11,
    AssetPath = 12,
    Quatd = 16,
    Quatf = 17,
    Quath = 18,
    Vec2d = 19,
    Vec2f = 20,
    Vec2h = 21,
    Vec2i = 22,
    Vec3d = 23,
    Vec3f = 24,
    Vec3h = 25,
    Vec3i = 26,
    Vec4d = 27,
    Vec4f = 28,
    Vec4h = 29,
    Vec4i = 30,
    Matrix2d = 13,
    Matrix3d = 14,
    Matrix4d = 15,

    // Non-array types.
    Dictionary = 31,
    TokenListOp = 32,
    StringListOp = 33,
    PathListOp = 34,
    ReferenceListOp = 35,
    IntListOp = 36,
    Int64ListOp = 37,
    UIntListOp = 38,
    UInt64ListOp = 39,
    PathVector = 40,
    TokenVector = 41,
    Specifier = 42,
    Permission = 43,
    Variability = 44,
    VariantSelectionMap = 45,
    TimeSamples = 46,
    Payload = 47,
    DoubleVector = 48,
    LayerOffsetVector = 49,
    StringVector = 50,
    ValueBlock = 51,
    Value = 52,
    UnregisteredValue = 53,
    UnregisteredValueListOp = 54,
    PayloadListOp = 55,

    // These array types appear here since the greatest enumerant value must be last.
    TimeCode = 56,
    PathExpression = 57,
}
