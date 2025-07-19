//! Types read from the usdc file.

use std::{ffi::CStr, fmt};

use anyhow::{Context as _, Result};
use bytemuck::{Pod, Zeroable};
use strum::{Display, EnumCount, FromRepr};

use crate::sdf;

/// Appears at start of file, houses version, file identifier string and offset to TOC.
#[repr(C)]
#[derive(Default, Debug, Clone, Copy, Pod, Zeroable)]
pub struct Bootstrap {
    /// "PXR-USDC"
    pub ident: [u8; 8],
    /// 0: major, 1: minor, 2: patch, rest unused.
    pub version: [u8; 8],
    /// Offset to TOC.
    pub toc_offset: u64,
    /// Unused.
    reserved: [u8; 8],
}

impl From<Bootstrap> for Version {
    fn from(boot: Bootstrap) -> Self {
        version(boot.version[0], boot.version[1], boot.version[2])
    }
}

/// Helper structure to compare file versions.
#[derive(Default, Debug, Copy, Clone, Eq, PartialEq)]
pub struct Version {
    pub major: u8,
    pub minor: u8,
    pub patch: u8,
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

/// Make version helper.
pub const fn version(major: u8, minor: u8, patch: u8) -> Version {
    Version { major, minor, patch }
}

impl Version {
    /// Return true if `other` has the same major version as this, and has a
    /// lesser or same minor version. Patch version irrelevant, since the
    /// versioning scheme specifies that patch level changes are forward-compatible.
    /// See <https://github.com/PixarAnimationStudios/OpenUSD/blob/0b18ad3f840c24eb25e16b795a5b0821cf05126e/pxr/usd/usd/crateFile.h#L547>
    #[inline]
    pub fn can_read(self, file_ver: Version) -> bool {
        file_ver.major == self.major && file_ver.minor <= self.minor
    }

    #[inline]
    pub fn as_u32(self) -> u32 {
        (self.major as u32) << 16 | (self.minor as u32) << 8 | self.patch as u32
    }

    #[inline]
    pub fn is_valid(self) -> bool {
        self.as_u32() != 0
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.as_u32().cmp(&other.as_u32()))
    }
}

/// Max section's name length.
const SECTION_NAME_MAX_LENGTH: usize = 15;

#[repr(C)]
#[derive(Default, Debug, Clone, Copy, Pod, Zeroable)]
pub struct Section {
    /// Section name bytes (e.g. "TOKENS"), use [Section::name] to retrieve as string.
    name: [u8; SECTION_NAME_MAX_LENGTH + 1],
    /// Section start offset.
    pub start: u64,
    /// Section size.
    pub size: u64,
}

impl Section {
    pub const TOKENS: &'static str = "TOKENS";
    pub const STRINGS: &'static str = "STRINGS";
    pub const FIELDS: &'static str = "FIELDS";
    pub const FIELDSETS: &'static str = "FIELDSETS";
    pub const PATHS: &'static str = "PATHS";
    pub const SPECS: &'static str = "SPECS";

    /// Convert array of bytes to a human-readable string.
    pub fn name(&self) -> &str {
        CStr::from_bytes_until_nul(&self.name)
            .unwrap_or_default()
            .to_str()
            .unwrap_or_default()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Field {
    pub token_index: usize,
    pub value_rep: ValueRep,
}

impl Field {
    pub fn new(index: u32, value: u64) -> Self {
        Self {
            token_index: index as usize,
            value_rep: ValueRep(value),
        }
    }
}

/// Spec data loaded from file.
#[derive(Default, Debug, Clone, Copy)]
pub struct Spec {
    pub path_index: usize,
    pub fieldset_index: usize,
    pub spec_type: sdf::SpecType,
}

#[repr(C)]
#[derive(Default, Clone, Copy, Pod, Zeroable)]
pub struct ListOpHeader {
    bits: u8,
}

impl ListOpHeader {
    const IS_EXPLICIT: u8 = 1 << 0;
    const HAS_EXPLICIT_ITEMS: u8 = 1 << 1;
    const HAS_ADDED_ITEMS: u8 = 1 << 2;
    const HAS_DELETED_ITEMS: u8 = 1 << 3;
    const HAS_ORDERED_ITEMS: u8 = 1 << 4;
    const HAS_PREPEND_ITEMS: u8 = 1 << 5;
    const HAS_APPENDED_ITEMS: u8 = 1 << 6;

    #[inline]
    pub fn is_explicit(self) -> bool {
        self.bits & Self::IS_EXPLICIT != 0
    }

    #[inline]
    pub fn has_explicit(self) -> bool {
        self.bits & Self::HAS_EXPLICIT_ITEMS != 0
    }

    #[inline]
    pub fn has_added(self) -> bool {
        self.bits & Self::HAS_ADDED_ITEMS != 0
    }

    #[inline]
    pub fn has_deleted(self) -> bool {
        self.bits & Self::HAS_DELETED_ITEMS != 0
    }

    #[inline]
    pub fn has_ordered(self) -> bool {
        self.bits & Self::HAS_ORDERED_ITEMS != 0
    }

    #[inline]
    pub fn has_prepend(self) -> bool {
        self.bits & Self::HAS_PREPEND_ITEMS != 0
    }

    #[inline]
    pub fn has_appended(self) -> bool {
        self.bits & Self::HAS_APPENDED_ITEMS != 0
    }
}

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
#[derive(Default, Copy, Clone, Pod, Zeroable)]
pub struct ValueRep(pub u64);

impl fmt::Debug for ValueRep {
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

impl ValueRep {
    const ARRAY_BIT: u64 = 1 << 63;
    const INLINED_BIT: u64 = 1 << 62;
    const COMPRESSED_BIT: u64 = 1 << 61;
    const PAYLOAD_MASK: u64 = ((1 << 48) - 1);

    #[inline]
    pub fn ty(self) -> Result<Type> {
        let index = ((self.data() >> 48) & 0xFF) as u32;
        Type::from_repr(index).with_context(|| format!("Unable to parse type enum {index}"))
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
    Uchar = 2,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_cmp() {
        assert_ne!(version(0, 4, 0), version(0, 4, 1));
        assert_eq!(version(0, 4, 0), version(0, 4, 0));
        assert!(version(0, 4, 0) < version(0, 10, 0));
    }

    #[test]
    fn test_is_valid() {
        let version = version(1, 1, 1);
        assert!(version.is_valid());

        let version = Version::default();
        assert!(!version.is_valid());
    }

    #[test]
    fn test_version_from_bootstrap() {
        let mut boot = Bootstrap::default();
        boot.version[0] = 1;
        boot.version[1] = 2;
        boot.version[2] = 3;

        assert_eq!(Version::from(boot), version(1, 2, 3));
    }
}
