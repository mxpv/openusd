use std::collections::HashMap;

use half::f16;
use strum::{EnumIs, EnumTryAs, IntoStaticStr};

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
/// types (e.g. `f32`, `String`, `[f32; 3]`).
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

    Token(String),
    TokenVec(Vec<String>),

    AssetPath(String),

    Quath([f16; 4]),
    Quatf([f32; 4]),
    Quatd([f64; 4]),
    QuathVec(Vec<[f16; 4]>),
    QuatfVec(Vec<[f32; 4]>),
    QuatdVec(Vec<[f64; 4]>),

    Vec2h([f16; 2]),
    Vec2f([f32; 2]),
    Vec2d([f64; 2]),
    Vec2i([i32; 2]),
    Vec2hVec(Vec<[f16; 2]>),
    Vec2fVec(Vec<[f32; 2]>),
    Vec2dVec(Vec<[f64; 2]>),
    Vec2iVec(Vec<[i32; 2]>),

    Vec3h([f16; 3]),
    Vec3f([f32; 3]),
    Vec3d([f64; 3]),
    Vec3i([i32; 3]),
    Vec3hVec(Vec<[f16; 3]>),
    Vec3fVec(Vec<[f32; 3]>),
    Vec3dVec(Vec<[f64; 3]>),
    Vec3iVec(Vec<[i32; 3]>),

    Vec4h([f16; 4]),
    Vec4f([f32; 4]),
    Vec4d([f64; 4]),
    Vec4i([i32; 4]),
    Vec4hVec(Vec<[f16; 4]>),
    Vec4fVec(Vec<[f32; 4]>),
    Vec4dVec(Vec<[f64; 4]>),
    Vec4iVec(Vec<[i32; 4]>),

    Matrix2d([f64; 4]),
    Matrix3d([f64; 9]),
    Matrix4d([f64; 16]),
    Matrix2dVec(Vec<[f64; 4]>),
    Matrix3dVec(Vec<[f64; 9]>),
    Matrix4dVec(Vec<[f64; 16]>),

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
    VariantSelectionMap(HashMap<String, String>),
    TimeSamples(TimeSampleMap),

    LayerOffsetVec(Vec<LayerOffset>),

    ValueBlock,
    Value,

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

            Value::String(v) | Value::Token(v) | Value::AssetPath(v) | Value::PathExpression(v) => {
                v.serialize(serializer)
            }
            Value::StringVec(v) | Value::TokenVec(v) => v.serialize(serializer),

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

            Value::Matrix2d(v) => v.chunks(2).collect::<Vec<_>>().serialize(serializer),
            Value::Matrix3d(v) => v.chunks(3).collect::<Vec<_>>().serialize(serializer),
            Value::Matrix4d(v) => v.chunks(4).collect::<Vec<_>>().serialize(serializer),
            Value::Matrix2dVec(v) => {
                v.iter().map(|m| m.chunks(2).collect::<Vec<_>>()).collect::<Vec<_>>().serialize(serializer)
            }
            Value::Matrix3dVec(v) => {
                v.iter().map(|m| m.chunks(3).collect::<Vec<_>>()).collect::<Vec<_>>().serialize(serializer)
            }
            Value::Matrix4dVec(v) => {
                v.iter().map(|m| m.chunks(4).collect::<Vec<_>>()).collect::<Vec<_>>().serialize(serializer)
            }

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
            Value::VariantSelectionMap(v) => v.serialize(serializer),
            Value::LayerOffsetVec(v) => v.serialize(serializer),

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
impl_try_from_value!(ReferenceListOp, try_as_reference_list_op, "ReferenceListOp");
impl_try_from_value!(PayloadListOp, try_as_payload_list_op, "PayloadListOp");
impl_try_from_value!(PathListOp, try_as_path_list_op, "PathListOp");

impl TryFrom<Value> for String {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::String(v) | Value::Token(v) => Ok(v),
            other => ValueConversionError::err("String or Token", &other),
        }
    }
}

impl TryFrom<Value> for [f32; 2] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec2f(v) => Ok(v),
            other => ValueConversionError::err("Vec2f", &other),
        }
    }
}

impl TryFrom<Value> for [f32; 3] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec3f(v) => Ok(v),
            other => ValueConversionError::err("Vec3f", &other),
        }
    }
}

impl TryFrom<Value> for [f32; 4] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec4f(v) | Value::Quatf(v) => Ok(v),
            other => ValueConversionError::err("Vec4f or Quatf", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 2] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec2d(v) => Ok(v),
            other => ValueConversionError::err("Vec2d", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 3] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec3d(v) => Ok(v),
            other => ValueConversionError::err("Vec3d", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 4] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec4d(v) | Value::Quatd(v) => Ok(v),
            other => ValueConversionError::err("Vec4d or Quatd", &other),
        }
    }
}

impl TryFrom<Value> for Vec<f32> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::FloatVec(v) => Ok(v),
            Value::Vec2f(v) => Ok(v.into()),
            Value::Vec3f(v) => Ok(v.into()),
            Value::Vec4f(v) => Ok(v.into()),
            other => ValueConversionError::err("FloatVec, Vec2f, Vec3f, or Vec4f", &other),
        }
    }
}

impl TryFrom<Value> for Vec<f64> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::DoubleVec(v) => Ok(v),
            Value::Vec2d(v) => Ok(v.into()),
            Value::Vec3d(v) => Ok(v.into()),
            Value::Vec4d(v) => Ok(v.into()),
            other => ValueConversionError::err("DoubleVec, Vec2d, Vec3d, or Vec4d", &other),
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
    fn try_from_fixed_arrays() {
        assert_eq!(<[f32; 2]>::try_from(Value::Vec2f([1.0, 2.0])).unwrap(), [1.0, 2.0]);
        assert_eq!(
            <[f32; 3]>::try_from(Value::Vec3f([1.0, 2.0, 3.0])).unwrap(),
            [1.0, 2.0, 3.0]
        );
        assert_eq!(
            <[f32; 4]>::try_from(Value::Vec4f([1.0, 2.0, 3.0, 4.0])).unwrap(),
            [1.0, 2.0, 3.0, 4.0]
        );
        assert_eq!(
            <[f64; 3]>::try_from(Value::Vec3d([1.0, 2.0, 3.0])).unwrap(),
            [1.0, 2.0, 3.0]
        );
    }

    #[test]
    fn try_from_vec() {
        // Vec<f32> accepts any float vector variant.
        assert!(Vec::<f32>::try_from(Value::FloatVec(vec![1.0])).is_ok());
        assert!(Vec::<f32>::try_from(Value::Vec3f([1.0, 2.0, 3.0])).is_ok());

        // Vec<f64> accepts any double vector variant.
        assert!(Vec::<f64>::try_from(Value::DoubleVec(vec![1.0])).is_ok());
        assert!(Vec::<f64>::try_from(Value::Vec2d([1.0, 2.0])).is_ok());
    }

    #[test]
    fn try_from_wrong_variant() {
        let err = f32::try_from(Value::Int(1)).unwrap_err();
        assert_eq!(err.to_string(), "expected Float, got Int");

        let err = <[f32; 3]>::try_from(Value::Bool(true)).unwrap_err();
        assert_eq!(err.to_string(), "expected Vec3f, got Bool");
    }
}
