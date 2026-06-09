use std::collections::HashMap;

use crate::gf::f16;
use strum::{EnumIs, EnumTryAs, IntoStaticStr};

use crate::gf;
use crate::tf::Token;

use super::*;

/// A type-erased container for scene description data loaded from a USD file.
///
/// This is the Rust equivalent of USD's [`VtValue`](https://openusd.org/dev/api/class_vt_value.html),
/// representing any value that can appear in a scene description layer. Each variant corresponds
/// to a USD data type.
///
/// Vector and matrix variant suffixes indicate the element type:
/// - `d` — `f64` (double)
/// - `f` — `f32` (float)
/// - `h` — `f16` (half)
/// - `i` — `i32` (int)
///
/// Type-safe extraction is supported via [`TryFrom<Value>`] implementations for common Rust
/// types (e.g. `f32`, `String`, `gf::Vec3f`).
#[derive(Debug, Clone, PartialEq, EnumIs, EnumTryAs, IntoStaticStr)]
pub enum Value {
    /// None value, only produced by expressions (not directly assignable).
    None,

    Bool(bool),
    BoolVec(Vec<bool>),

    Uchar(u8),
    UcharVec(Vec<u8>),

    Int(i32),
    IntVec(Vec<i32>),

    Uint(u32),
    UintVec(Vec<u32>),

    Int64(i64),
    Int64Vec(Vec<i64>),

    Uint64(u64),
    Uint64Vec(Vec<u64>),

    Half(f16),
    HalfVec(Vec<f16>),

    Float(f32),
    FloatVec(Vec<f32>),

    Double(f64),
    DoubleVec(Vec<f64>),

    String(String),
    StringVec(Vec<String>),

    Token(Token),
    TokenVec(Vec<Token>),

    AssetPath(AssetPath),
    AssetPathVec(Vec<AssetPath>),

    Quath(gf::Quath),
    Quatf(gf::Quatf),
    Quatd(gf::Quatd),
    QuathVec(Vec<gf::Quath>),
    QuatfVec(Vec<gf::Quatf>),
    QuatdVec(Vec<gf::Quatd>),

    Vec2h(gf::Vec2h),
    Vec2f(gf::Vec2f),
    Vec2d(gf::Vec2d),
    Vec2i(gf::Vec2i),
    Vec2hVec(Vec<gf::Vec2h>),
    Vec2fVec(Vec<gf::Vec2f>),
    Vec2dVec(Vec<gf::Vec2d>),
    Vec2iVec(Vec<gf::Vec2i>),

    Vec3h(gf::Vec3h),
    Vec3f(gf::Vec3f),
    Vec3d(gf::Vec3d),
    Vec3i(gf::Vec3i),
    Vec3hVec(Vec<gf::Vec3h>),
    Vec3fVec(Vec<gf::Vec3f>),
    Vec3dVec(Vec<gf::Vec3d>),
    Vec3iVec(Vec<gf::Vec3i>),

    Vec4h(gf::Vec4h),
    Vec4f(gf::Vec4f),
    Vec4d(gf::Vec4d),
    Vec4i(gf::Vec4i),
    Vec4hVec(Vec<gf::Vec4h>),
    Vec4fVec(Vec<gf::Vec4f>),
    Vec4dVec(Vec<gf::Vec4d>),
    Vec4iVec(Vec<gf::Vec4i>),

    Matrix2d(gf::Mat2d),
    Matrix3d(gf::Mat3d),
    Matrix4d(gf::Matrix4d),
    Matrix2dVec(Vec<gf::Mat2d>),
    Matrix3dVec(Vec<gf::Mat3d>),
    Matrix4dVec(Vec<gf::Matrix4d>),

    Specifier(Specifier),
    Permission(Permission),
    Variability(Variability),

    Dictionary(HashMap<String, Value>),

    TokenListOp(TokenListOp),
    StringListOp(StringListOp),
    PathListOp(PathListOp),
    ReferenceListOp(ReferenceListOp),
    IntListOp(IntListOp),
    Int64ListOp(Int64ListOp),
    UIntListOp(UintListOp),
    UInt64ListOp(Uint64ListOp),
    PayloadListOp(PayloadListOp),

    Payload(Payload),
    PathVec(Vec<Path>),
    /// Layer-level relocates: `(source, target)` path pairs for namespace remapping.
    Relocates(RelocateList),
    VariantSelectionMap(HashMap<String, String>),
    TimeSamples(TimeSampleMap),

    LayerOffsetVec(Vec<LayerOffset>),

    ValueBlock,
    Value,

    /// Heterogeneous array (e.g. spline knots). Each element is a `Value`.
    ValueVec(Vec<Value>),

    UnregisteredValue(String),
    UnregisteredValueListOp(StringListOp),

    TimeCode(f64),
    TimeCodeVec(Vec<f64>),
    PathExpression(String),
}

#[cfg(feature = "serde")]
impl serde::Serialize for Value {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeMap;

        match self {
            Value::None | Value::ValueBlock | Value::Value => serializer.serialize_none(),

            Value::Bool(v) => v.serialize(serializer),
            Value::BoolVec(v) => v.serialize(serializer),
            Value::Uchar(v) => v.serialize(serializer),
            Value::UcharVec(v) => v.serialize(serializer),
            Value::Int(v) => v.serialize(serializer),
            Value::IntVec(v) => v.serialize(serializer),
            Value::Uint(v) => v.serialize(serializer),
            Value::UintVec(v) => v.serialize(serializer),
            Value::Int64(v) => v.serialize(serializer),
            Value::Int64Vec(v) => v.serialize(serializer),
            Value::Uint64(v) => v.serialize(serializer),
            Value::Uint64Vec(v) => v.serialize(serializer),
            Value::Half(v) => v.serialize(serializer),
            Value::HalfVec(v) => v.serialize(serializer),
            Value::Float(v) => v.serialize(serializer),
            Value::FloatVec(v) => v.serialize(serializer),
            Value::Double(v) => v.serialize(serializer),
            Value::DoubleVec(v) => v.serialize(serializer),
            Value::TimeCode(v) => v.serialize(serializer),
            Value::TimeCodeVec(v) => v.serialize(serializer),

            Value::String(v) | Value::PathExpression(v) => v.serialize(serializer),
            Value::Token(v) => v.serialize(serializer),
            Value::AssetPath(v) => v.serialize(serializer),
            Value::StringVec(v) => v.serialize(serializer),
            Value::TokenVec(v) => v.serialize(serializer),
            Value::AssetPathVec(v) => v.serialize(serializer),

            Value::Vec2h(v) => v.serialize(serializer),
            Value::Vec3h(v) => v.serialize(serializer),
            Value::Vec4h(v) => v.serialize(serializer),
            Value::Quath(v) => v.serialize(serializer),
            Value::Vec2f(v) => v.serialize(serializer),
            Value::Vec3f(v) => v.serialize(serializer),
            Value::Vec4f(v) => v.serialize(serializer),
            Value::Quatf(v) => v.serialize(serializer),
            Value::Vec2d(v) => v.serialize(serializer),
            Value::Vec3d(v) => v.serialize(serializer),
            Value::Vec4d(v) => v.serialize(serializer),
            Value::Quatd(v) => v.serialize(serializer),
            Value::Vec2i(v) => v.serialize(serializer),
            Value::Vec3i(v) => v.serialize(serializer),
            Value::Vec4i(v) => v.serialize(serializer),

            Value::Vec2hVec(v) => v.serialize(serializer),
            Value::Vec3hVec(v) => v.serialize(serializer),
            Value::Vec4hVec(v) => v.serialize(serializer),
            Value::QuathVec(v) => v.serialize(serializer),
            Value::Vec2fVec(v) => v.serialize(serializer),
            Value::Vec3fVec(v) => v.serialize(serializer),
            Value::Vec4fVec(v) => v.serialize(serializer),
            Value::QuatfVec(v) => v.serialize(serializer),
            Value::Vec2dVec(v) => v.serialize(serializer),
            Value::Vec3dVec(v) => v.serialize(serializer),
            Value::Vec4dVec(v) => v.serialize(serializer),
            Value::QuatdVec(v) => v.serialize(serializer),
            Value::Vec2iVec(v) => v.serialize(serializer),
            Value::Vec3iVec(v) => v.serialize(serializer),
            Value::Vec4iVec(v) => v.serialize(serializer),

            Value::Matrix2d(m) => m.0.chunks(2).collect::<Vec<_>>().serialize(serializer),
            Value::Matrix3d(m) => m.0.chunks(3).collect::<Vec<_>>().serialize(serializer),
            Value::Matrix4d(m) => m.0.chunks(4).collect::<Vec<_>>().serialize(serializer),
            Value::Matrix2dVec(v) => v
                .iter()
                .map(|m| m.0.chunks(2).collect::<Vec<_>>())
                .collect::<Vec<_>>()
                .serialize(serializer),
            Value::Matrix3dVec(v) => v
                .iter()
                .map(|m| m.0.chunks(3).collect::<Vec<_>>())
                .collect::<Vec<_>>()
                .serialize(serializer),
            Value::Matrix4dVec(v) => v
                .iter()
                .map(|m| m.0.chunks(4).collect::<Vec<_>>())
                .collect::<Vec<_>>()
                .serialize(serializer),

            Value::Specifier(v) => v.serialize(serializer),
            Value::Permission(v) => v.serialize(serializer),
            Value::Variability(v) => v.serialize(serializer),
            Value::Dictionary(v) => v.serialize(serializer),

            Value::TokenListOp(v) | Value::StringListOp(v) => v.serialize(serializer),
            Value::PathListOp(v) => v.serialize(serializer),
            Value::ReferenceListOp(v) => v.serialize(serializer),
            Value::IntListOp(v) => v.serialize(serializer),
            Value::Int64ListOp(v) => v.serialize(serializer),
            Value::UIntListOp(v) => v.serialize(serializer),
            Value::UInt64ListOp(v) => v.serialize(serializer),
            Value::PayloadListOp(v) => v.serialize(serializer),

            Value::Payload(v) => v.serialize(serializer),
            Value::PathVec(v) => v.serialize(serializer),
            Value::Relocates(v) => {
                let mut map = serializer.serialize_map(Some(v.len()))?;
                for (src, tgt) in v {
                    map.serialize_entry(src.as_str(), tgt.as_str())?;
                }
                map.end()
            }
            Value::VariantSelectionMap(v) => v.serialize(serializer),
            Value::LayerOffsetVec(v) => v.serialize(serializer),

            Value::ValueVec(v) => v.serialize(serializer),

            Value::UnregisteredValue(v) => v.serialize(serializer),
            Value::UnregisteredValueListOp(v) => v.serialize(serializer),

            // Time samples serialize as a map with string keys.
            Value::TimeSamples(v) => {
                let mut map = serializer.serialize_map(Some(v.len()))?;
                for (time, value) in v {
                    let key = if time.fract() == 0.0 && time.is_finite() {
                        format!("{}", *time as i64)
                    } else {
                        format!("{time}")
                    };
                    map.serialize_entry(&key, value)?;
                }
                map.end()
            }
        }
    }
}

/// Error returned when a [`Value`] cannot be converted to the requested type.
#[derive(Debug, Clone)]
pub struct ValueConversionError {
    expected: &'static str,
    actual: &'static str,
}

impl ValueConversionError {
    /// Creates a new error from the expected type name and the actual value.
    pub fn new(expected: &'static str, actual: &Value) -> Self {
        Self {
            expected,
            actual: actual.into(),
        }
    }

    /// Returns an `Err` with a new conversion error.
    pub fn err<T>(expected: &'static str, actual: &Value) -> Result<T, Self> {
        Err(Self::new(expected, actual))
    }
}

impl std::fmt::Display for ValueConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "expected {}, got {}", self.expected, self.actual)
    }
}

impl std::error::Error for ValueConversionError {}

// --- Type-safe extraction (TryFrom<Value>) ---
//
// Owned conversions that move data out of Value without cloning.
// Scalar types delegate to the strum-generated `try_as_*()` methods
// (from the EnumTryAs derive). Compound types use manual match arms
// to accept multiple variants.

macro_rules! impl_try_from_value {
    ($target:ty, $method:ident, $label:literal) => {
        impl TryFrom<Value> for $target {
            type Error = ValueConversionError;

            fn try_from(value: Value) -> Result<Self, Self::Error> {
                let tag: &'static str = (&value).into();
                value.$method().ok_or(ValueConversionError {
                    expected: $label,
                    actual: tag,
                })
            }
        }
    };
}

impl_try_from_value!(bool, try_as_bool, "Bool");
impl_try_from_value!(i32, try_as_int, "Int");
impl_try_from_value!(u32, try_as_uint, "Uint");
impl_try_from_value!(i64, try_as_int_64, "Int64");
impl_try_from_value!(u64, try_as_uint_64, "Uint64");
impl_try_from_value!(f32, try_as_float, "Float");
impl_try_from_value!(f64, try_as_double, "Double");
impl_try_from_value!(Specifier, try_as_specifier, "Specifier");
impl_try_from_value!(Variability, try_as_variability, "Variability");
impl_try_from_value!(ReferenceListOp, try_as_reference_list_op, "ReferenceListOp");
impl_try_from_value!(PayloadListOp, try_as_payload_list_op, "PayloadListOp");
impl_try_from_value!(PathListOp, try_as_path_list_op, "PathListOp");

// gf scalar types — trivially unwrap the matching variant.
impl_try_from_value!(gf::Vec2f, try_as_vec_2f, "gf::Vec2f");
impl_try_from_value!(gf::Vec2d, try_as_vec_2d, "gf::Vec2d");
impl_try_from_value!(gf::Vec2i, try_as_vec_2i, "gf::Vec2i");
impl_try_from_value!(gf::Vec2h, try_as_vec_2h, "gf::Vec2h");
impl_try_from_value!(gf::Vec3f, try_as_vec_3f, "gf::Vec3f");
impl_try_from_value!(gf::Vec3d, try_as_vec_3d, "gf::Vec3d");
impl_try_from_value!(gf::Vec3i, try_as_vec_3i, "gf::Vec3i");
impl_try_from_value!(gf::Vec3h, try_as_vec_3h, "gf::Vec3h");
impl_try_from_value!(gf::Vec4f, try_as_vec_4f, "gf::Vec4f");
impl_try_from_value!(gf::Vec4d, try_as_vec_4d, "gf::Vec4d");
impl_try_from_value!(gf::Vec4i, try_as_vec_4i, "gf::Vec4i");
impl_try_from_value!(gf::Vec4h, try_as_vec_4h, "gf::Vec4h");
impl_try_from_value!(gf::Quatf, try_as_quatf, "gf::Quatf");
impl_try_from_value!(gf::Quatd, try_as_quatd, "gf::Quatd");
impl_try_from_value!(gf::Quath, try_as_quath, "gf::Quath");
impl_try_from_value!(gf::Mat2d, try_as_matrix_2d, "gf::Mat2d");
impl_try_from_value!(gf::Mat3d, try_as_matrix_3d, "gf::Mat3d");
impl_try_from_value!(gf::Matrix4d, try_as_matrix_4d, "gf::Matrix4d");

// gf array types.
impl_try_from_value!(Vec<gf::Vec2f>, try_as_vec_2f_vec, "Vec2fVec");
impl_try_from_value!(Vec<gf::Vec2d>, try_as_vec_2d_vec, "Vec2dVec");
impl_try_from_value!(Vec<gf::Vec2i>, try_as_vec_2i_vec, "Vec2iVec");
impl_try_from_value!(Vec<gf::Vec2h>, try_as_vec_2h_vec, "Vec2hVec");
impl_try_from_value!(Vec<gf::Vec3f>, try_as_vec_3f_vec, "Vec3fVec");
impl_try_from_value!(Vec<gf::Vec3d>, try_as_vec_3d_vec, "Vec3dVec");
impl_try_from_value!(Vec<gf::Vec3i>, try_as_vec_3i_vec, "Vec3iVec");
impl_try_from_value!(Vec<gf::Vec3h>, try_as_vec_3h_vec, "Vec3hVec");
impl_try_from_value!(Vec<gf::Vec4f>, try_as_vec_4f_vec, "Vec4fVec");
impl_try_from_value!(Vec<gf::Vec4d>, try_as_vec_4d_vec, "Vec4dVec");
impl_try_from_value!(Vec<gf::Vec4i>, try_as_vec_4i_vec, "Vec4iVec");
impl_try_from_value!(Vec<gf::Vec4h>, try_as_vec_4h_vec, "Vec4hVec");
impl_try_from_value!(Vec<gf::Quatf>, try_as_quatf_vec, "QuatfVec");
impl_try_from_value!(Vec<gf::Quatd>, try_as_quatd_vec, "QuatdVec");
impl_try_from_value!(Vec<gf::Quath>, try_as_quath_vec, "QuathVec");
impl_try_from_value!(Vec<gf::Mat2d>, try_as_matrix_2d_vec, "Matrix2dVec");
impl_try_from_value!(Vec<gf::Mat3d>, try_as_matrix_3d_vec, "Matrix3dVec");
impl_try_from_value!(Vec<gf::Matrix4d>, try_as_matrix_4d_vec, "Matrix4dVec");

impl TryFrom<Value> for String {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::String(v) => Ok(v),
            Value::Token(v) => Ok(v.into()),
            other => ValueConversionError::err("String or Token", &other),
        }
    }
}

impl TryFrom<Value> for Token {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Token(v) => Ok(v),
            other => ValueConversionError::err("Token", &other),
        }
    }
}

impl TryFrom<Value> for AssetPath {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::AssetPath(asset) => Ok(asset),
            other => ValueConversionError::err("AssetPath", &other),
        }
    }
}

impl TryFrom<Value> for Vec<AssetPath> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::AssetPathVec(assets) => Ok(assets),
            other => ValueConversionError::err("AssetPathVec", &other),
        }
    }
}

// Raw array convenience conversions — extract the inner gf type then convert
// via its Into<[T; N]> impl.

impl TryFrom<Value> for [f32; 2] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec2f(v) => Ok(v.into()),
            other => ValueConversionError::err("gf::Vec2f", &other),
        }
    }
}

impl TryFrom<Value> for [f32; 3] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec3f(v) => Ok(v.into()),
            other => ValueConversionError::err("gf::Vec3f", &other),
        }
    }
}

impl TryFrom<Value> for [f32; 4] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec4f(v) => Ok(v.into()),
            Value::Quatf(v) => Ok(v.into()),
            other => ValueConversionError::err("gf::Vec4f or gf::Quatf", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 2] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec2d(v) => Ok(v.into()),
            other => ValueConversionError::err("gf::Vec2d", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 3] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec3d(v) => Ok(v.into()),
            other => ValueConversionError::err("gf::Vec3d", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 4] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec4d(v) => Ok(v.into()),
            Value::Quatd(v) => Ok(v.into()),
            other => ValueConversionError::err("gf::Vec4d or gf::Quatd", &other),
        }
    }
}

impl TryFrom<Value> for Vec<[f32; 2]> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec2fVec(v) => Ok(v.into_iter().map(Into::into).collect()),
            other => ValueConversionError::err("Vec2fVec", &other),
        }
    }
}

impl TryFrom<Value> for Vec<[f32; 3]> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec3fVec(v) => Ok(v.into_iter().map(Into::into).collect()),
            other => ValueConversionError::err("Vec3fVec", &other),
        }
    }
}

impl TryFrom<Value> for Vec<[f32; 4]> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec4fVec(v) => Ok(v.into_iter().map(Into::into).collect()),
            other => ValueConversionError::err("Vec4fVec", &other),
        }
    }
}

impl TryFrom<Value> for Vec<f32> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::FloatVec(v) => Ok(v),
            Value::Vec2f(v) => Ok(<[f32; 2]>::from(v).into()),
            Value::Vec3f(v) => Ok(<[f32; 3]>::from(v).into()),
            Value::Vec4f(v) => Ok(<[f32; 4]>::from(v).into()),
            other => ValueConversionError::err("FloatVec, gf::Vec2f, gf::Vec3f, or gf::Vec4f", &other),
        }
    }
}

impl TryFrom<Value> for Vec<f64> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::DoubleVec(v) => Ok(v),
            Value::Vec2d(v) => Ok(<[f64; 2]>::from(v).into()),
            Value::Vec3d(v) => Ok(<[f64; 3]>::from(v).into()),
            Value::Vec4d(v) => Ok(<[f64; 4]>::from(v).into()),
            other => ValueConversionError::err("DoubleVec, gf::Vec2d, gf::Vec3d, or gf::Vec4d", &other),
        }
    }
}

/// Convert from `&str` to `Value`.
///
/// Used a lot in text parser since all tokens are basically strings.
impl<'a> From<&'a str> for Value {
    fn from(value: &'a str) -> Self {
        Value::String(value.to_string())
    }
}

impl From<AssetPath> for Value {
    fn from(asset: AssetPath) -> Self {
        Value::AssetPath(asset)
    }
}

impl From<Vec<AssetPath>> for Value {
    fn from(assets: Vec<AssetPath>) -> Self {
        Value::AssetPathVec(assets)
    }
}

/// Wrap a value in its `Value` variant, so `impl Into<Value>` sinks (such as
/// [`AttributeMut::set`](crate::sdf::AttributeSpecMut) and the composed
/// `Attribute::set`) accept the bare Rust value: `set(2.5_f64)`,
/// `set(vec![4])`, `set(vec![gf::vec3f(0.0, 0.0, 0.0)])`.
///
/// Only types whose Rust representation maps to exactly one variant get a
/// `From`. The ambiguous ones are omitted so the wrong variant is never picked
/// silently — construct those explicitly:
/// - `gf::Vec4f` / `gf::Vec4d` / `gf::Vec4h` ([`Value::Vec4f`] vs [`Value::Quatf`], etc.),
/// - `Vec<String>` ([`Value::StringVec`] vs [`Value::TokenVec`]).
///
/// An unsuffixed float literal needs a type suffix (`2.5_f64`) to pick between
/// [`Value::Float`] and [`Value::Double`].
macro_rules! impl_from {
    ($t:ty, $variant:ident) => {
        impl From<$t> for Value {
            fn from(v: $t) -> Self {
                Value::$variant(v)
            }
        }
    };
}

// Scalars.
impl_from!(bool, Bool);
impl_from!(u8, Uchar);
impl_from!(i32, Int);
impl_from!(u32, Uint);
impl_from!(i64, Int64);
impl_from!(u64, Uint64);
impl_from!(f16, Half);
impl_from!(f32, Float);
impl_from!(f64, Double);
impl_from!(String, String);
impl_from!(Token, Token);
impl_from!(Vec<Token>, TokenVec);

// gf vector and quaternion types.
impl_from!(gf::Vec2f, Vec2f);
impl_from!(gf::Vec2d, Vec2d);
impl_from!(gf::Vec2i, Vec2i);
impl_from!(gf::Vec2h, Vec2h);
impl_from!(gf::Vec3f, Vec3f);
impl_from!(gf::Vec3d, Vec3d);
impl_from!(gf::Vec3i, Vec3i);
impl_from!(gf::Vec3h, Vec3h);
impl_from!(gf::Vec4f, Vec4f);
impl_from!(gf::Vec4d, Vec4d);
impl_from!(gf::Vec4i, Vec4i);
impl_from!(gf::Vec4h, Vec4h);
impl_from!(gf::Quatf, Quatf);
impl_from!(gf::Quatd, Quatd);
impl_from!(gf::Quath, Quath);
impl_from!(gf::Mat2d, Matrix2d);
impl_from!(gf::Mat3d, Matrix3d);
impl_from!(gf::Matrix4d, Matrix4d);

// Flat scalar arrays.
impl_from!(Vec<bool>, BoolVec);
impl_from!(Vec<u8>, UcharVec);
impl_from!(Vec<i32>, IntVec);
impl_from!(Vec<u32>, UintVec);
impl_from!(Vec<i64>, Int64Vec);
impl_from!(Vec<u64>, Uint64Vec);
impl_from!(Vec<f16>, HalfVec);
impl_from!(Vec<f32>, FloatVec);
impl_from!(Vec<f64>, DoubleVec);

// Arrays of gf vector and quaternion types.
impl_from!(Vec<gf::Vec2f>, Vec2fVec);
impl_from!(Vec<gf::Vec2d>, Vec2dVec);
impl_from!(Vec<gf::Vec2i>, Vec2iVec);
impl_from!(Vec<gf::Vec2h>, Vec2hVec);
impl_from!(Vec<gf::Vec3f>, Vec3fVec);
impl_from!(Vec<gf::Vec3d>, Vec3dVec);
impl_from!(Vec<gf::Vec3i>, Vec3iVec);
impl_from!(Vec<gf::Vec3h>, Vec3hVec);
impl_from!(Vec<gf::Vec4f>, Vec4fVec);
impl_from!(Vec<gf::Vec4d>, Vec4dVec);
impl_from!(Vec<gf::Vec4i>, Vec4iVec);
impl_from!(Vec<gf::Vec4h>, Vec4hVec);
impl_from!(Vec<gf::Quatf>, QuatfVec);
impl_from!(Vec<gf::Quatd>, QuatdVec);
impl_from!(Vec<gf::Quath>, QuathVec);
impl_from!(Vec<gf::Matrix4d>, Matrix4dVec);

// Raw array convenience conversions. Only unambiguous sizes are included:
// [f32; 4] / [f64; 4] / [f16; 4] are omitted (Vec4 vs Quat ambiguity).
impl From<[f32; 2]> for Value {
    fn from(v: [f32; 2]) -> Self {
        Value::Vec2f(v.into())
    }
}
impl From<[f32; 3]> for Value {
    fn from(v: [f32; 3]) -> Self {
        Value::Vec3f(v.into())
    }
}
impl From<[f64; 2]> for Value {
    fn from(v: [f64; 2]) -> Self {
        Value::Vec2d(v.into())
    }
}
impl From<[f64; 3]> for Value {
    fn from(v: [f64; 3]) -> Self {
        Value::Vec3d(v.into())
    }
}
impl From<[i32; 2]> for Value {
    fn from(v: [i32; 2]) -> Self {
        Value::Vec2i(v.into())
    }
}
impl From<[i32; 3]> for Value {
    fn from(v: [i32; 3]) -> Self {
        Value::Vec3i(v.into())
    }
}
impl From<[i32; 4]> for Value {
    fn from(v: [i32; 4]) -> Self {
        Value::Vec4i(v.into())
    }
}
impl From<[f64; 16]> for Value {
    fn from(v: [f64; 16]) -> Self {
        Value::Matrix4d(gf::Matrix4d(v))
    }
}

// Shorthand constructors for the gf vector and quaternion variants,
// mirroring the `gf::vec3f(x, y, z)` free-function convention.
impl Value {
    pub fn vec2f(x: f32, y: f32) -> Self {
        Self::Vec2f(gf::vec2f(x, y))
    }
    pub fn vec3f(x: f32, y: f32, z: f32) -> Self {
        Self::Vec3f(gf::vec3f(x, y, z))
    }
    pub fn vec4f(x: f32, y: f32, z: f32, w: f32) -> Self {
        Self::Vec4f(gf::vec4f(x, y, z, w))
    }
    pub fn vec2d(x: f64, y: f64) -> Self {
        Self::Vec2d(gf::vec2d(x, y))
    }
    pub fn vec3d(x: f64, y: f64, z: f64) -> Self {
        Self::Vec3d(gf::vec3d(x, y, z))
    }
    pub fn vec4d(x: f64, y: f64, z: f64, w: f64) -> Self {
        Self::Vec4d(gf::vec4d(x, y, z, w))
    }
    pub fn vec2i(x: i32, y: i32) -> Self {
        Self::Vec2i(gf::vec2i(x, y))
    }
    pub fn vec3i(x: i32, y: i32, z: i32) -> Self {
        Self::Vec3i(gf::vec3i(x, y, z))
    }
    pub fn vec4i(x: i32, y: i32, z: i32, w: i32) -> Self {
        Self::Vec4i(gf::vec4i(x, y, z, w))
    }
    pub fn vec2h(x: f16, y: f16) -> Self {
        Self::Vec2h(gf::vec2h(x, y))
    }
    pub fn vec3h(x: f16, y: f16, z: f16) -> Self {
        Self::Vec3h(gf::vec3h(x, y, z))
    }
    pub fn vec4h(x: f16, y: f16, z: f16, w: f16) -> Self {
        Self::Vec4h(gf::vec4h(x, y, z, w))
    }
    pub fn quatf(w: f32, x: f32, y: f32, z: f32) -> Self {
        Self::Quatf(gf::quatf(w, x, y, z))
    }
    pub fn quatd(w: f64, x: f64, y: f64, z: f64) -> Self {
        Self::Quatd(gf::quatd(w, x, y, z))
    }
    pub fn quath(w: f16, x: f16, y: f16, z: f16) -> Self {
        Self::Quath(gf::quath(w, x, y, z))
    }

    /// Builds a [`Value::Token`] from any string-like value, so callers need not
    /// name [`Token`] at the construction site (`Value::token("Mesh")`).
    pub fn token(name: impl Into<Token>) -> Self {
        Self::Token(name.into())
    }

    /// Builds a [`Value::TokenVec`] from any iterator of string-like items —
    /// the counterpart of [`Value::token`] for name lists such as
    /// `primChildren` and `allowedTokens`.
    pub fn token_vec(items: impl IntoIterator<Item = impl Into<Token>>) -> Self {
        Self::TokenVec(items.into_iter().map(Into::into).collect())
    }

    /// Borrows the inner string of a string-like scalar — `asset`, `string`,
    /// or `token` — and `None` for any other variant.
    ///
    /// An asset path may be authored as a plain string or token, so reading
    /// one coerces across all three (the borrowing counterpart to the owned
    /// [`TryFrom<Value>`] for [`String`]).
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Value::String(s) => Some(s),
            Value::Token(s) => Some(s.as_str()),
            Value::AssetPath(s) => Some(s.as_str()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is() {
        // Basic sanity checks
        assert!(Value::Bool(true).is_bool());
        assert!(!Value::Bool(true).is_bool_vec());

        assert!(Value::Float(1.44).is_float());
        assert!(!Value::Float(1.44).is_bool());
        assert!(!Value::Float(1.44).is_float_vec());

        assert!(Value::PayloadListOp(Default::default()).is_payload_list_op());
        assert!(Value::UnregisteredValue(String::new()).is_unregistered_value());
    }

    #[test]
    fn try_from_scalars() {
        assert!(bool::try_from(Value::Bool(true)).unwrap());
        assert_eq!(i32::try_from(Value::Int(42)).unwrap(), 42);
        assert_eq!(f32::try_from(Value::Float(1.5)).unwrap(), 1.5);
        assert_eq!(f64::try_from(Value::Double(2.5)).unwrap(), 2.5);
        assert_eq!(String::try_from(Value::String("hello".into())).unwrap(), "hello");
        assert_eq!(String::try_from(Value::Token("tok".into())).unwrap(), "tok");
    }

    #[test]
    fn try_from_gf_types() {
        let v3 = gf::vec3f(1.0, 2.0, 3.0);
        assert_eq!(gf::Vec3f::try_from(Value::Vec3f(v3)).unwrap(), v3);

        let q = gf::quatf(1.0, 0.0, 0.0, 0.0);
        assert_eq!(gf::Quatf::try_from(Value::Quatf(q)).unwrap(), q);

        let m = gf::Matrix4d::IDENTITY;
        assert_eq!(gf::Matrix4d::try_from(Value::Matrix4d(m)).unwrap(), m);
    }

    #[test]
    fn try_from_fixed_arrays() {
        let v = gf::vec2f(1.0, 2.0);
        assert_eq!(<[f32; 2]>::try_from(Value::Vec2f(v)).unwrap(), [1.0, 2.0]);

        let v = gf::vec3f(1.0, 2.0, 3.0);
        assert_eq!(<[f32; 3]>::try_from(Value::Vec3f(v)).unwrap(), [1.0, 2.0, 3.0]);

        let v = gf::vec4f(1.0, 2.0, 3.0, 4.0);
        assert_eq!(<[f32; 4]>::try_from(Value::Vec4f(v)).unwrap(), [1.0, 2.0, 3.0, 4.0]);

        let v = gf::vec3d(1.0, 2.0, 3.0);
        assert_eq!(<[f64; 3]>::try_from(Value::Vec3d(v)).unwrap(), [1.0, 2.0, 3.0]);
    }

    #[test]
    fn try_from_vec() {
        // Vec<f32> accepts any float vector variant.
        assert!(Vec::<f32>::try_from(Value::FloatVec(vec![1.0])).is_ok());
        let v = gf::vec3f(1.0, 2.0, 3.0);
        assert!(Vec::<f32>::try_from(Value::Vec3f(v)).is_ok());

        // Vec<f64> accepts any double vector variant.
        assert!(Vec::<f64>::try_from(Value::DoubleVec(vec![1.0])).is_ok());
        let v = gf::vec2d(1.0, 2.0);
        assert!(Vec::<f64>::try_from(Value::Vec2d(v)).is_ok());
    }

    #[test]
    fn try_from_asset_path() {
        let scalar = AssetPath::try_from(Value::AssetPath("./tex.png".into())).unwrap();
        assert_eq!(scalar, AssetPath::new("./tex.png"));

        let array = Vec::<AssetPath>::try_from(Value::AssetPathVec(vec!["a.png".into(), "b.png".into()])).unwrap();
        assert_eq!(array, vec![AssetPath::new("a.png"), AssetPath::new("b.png")]);

        // A plain string is not an asset path.
        assert!(AssetPath::try_from(Value::String("a.png".into())).is_err());

        // Round-trips back through the authoring `From` impls.
        assert_eq!(Value::from(scalar), Value::AssetPath("./tex.png".into()));
        assert_eq!(
            Value::from(array),
            Value::AssetPathVec(vec!["a.png".into(), "b.png".into()])
        );
    }

    #[test]
    fn try_from_wrong_variant() {
        let err = f32::try_from(Value::Int(1)).unwrap_err();
        assert_eq!(err.to_string(), "expected Float, got Int");

        let err = gf::Vec3f::try_from(Value::Bool(true)).unwrap_err();
        assert_eq!(err.to_string(), "expected gf::Vec3f, got Bool");
    }

    #[test]
    fn from_gf_roundtrip() {
        let v = gf::vec3f(1.0, 2.0, 3.0);
        assert_eq!(Value::from(v), Value::Vec3f(v));

        let m = gf::Matrix4d::IDENTITY;
        assert_eq!(Value::from(m), Value::Matrix4d(m));
    }
}
