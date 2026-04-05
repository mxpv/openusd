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

    Quath(Vec<f16>),
    Quatf(Vec<f32>),
    Quatd(Vec<f64>),

    Vec2h(Vec<f16>),
    Vec2f(Vec<f32>),
    Vec2d(Vec<f64>),
    Vec2i(Vec<i32>),

    Vec3h(Vec<f16>),
    Vec3f(Vec<f32>),
    Vec3d(Vec<f64>),
    Vec3i(Vec<i32>),

    Vec4h(Vec<f16>),
    Vec4f(Vec<f32>),
    Vec4d(Vec<f64>),
    Vec4i(Vec<i32>),

    Matrix2d(Vec<f64>),
    Matrix3d(Vec<f64>),
    Matrix4d(Vec<f64>),

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
    PathVec,
    VariantSelectionMap(HashMap<String, String>),
    TimeSamples(TimeSampleMap),

    LayerOffsetVec(Vec<LayerOffset>),

    ValueBlock,
    Value,

    UnregisteredValue,
    UnregisteredValueListOp,

    TimeCode(f64),
    PathExpression,
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
            Value::Vec2f(v) if v.len() == 2 => Ok([v[0], v[1]]),
            other => ValueConversionError::err("Vec2f", &other),
        }
    }
}

impl TryFrom<Value> for [f32; 3] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec3f(v) if v.len() == 3 => Ok([v[0], v[1], v[2]]),
            other => ValueConversionError::err("Vec3f", &other),
        }
    }
}

impl TryFrom<Value> for [f32; 4] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec4f(v) | Value::Quatf(v) if v.len() == 4 => Ok([v[0], v[1], v[2], v[3]]),
            other => ValueConversionError::err("Vec4f or Quatf", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 2] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec2d(v) if v.len() == 2 => Ok([v[0], v[1]]),
            other => ValueConversionError::err("Vec2d", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 3] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec3d(v) if v.len() == 3 => Ok([v[0], v[1], v[2]]),
            other => ValueConversionError::err("Vec3d", &other),
        }
    }
}

impl TryFrom<Value> for [f64; 4] {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Vec4d(v) | Value::Quatd(v) if v.len() == 4 => Ok([v[0], v[1], v[2], v[3]]),
            other => ValueConversionError::err("Vec4d or Quatd", &other),
        }
    }
}

impl TryFrom<Value> for Vec<f32> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::FloatVec(v) | Value::Vec2f(v) | Value::Vec3f(v) | Value::Vec4f(v) => Ok(v),
            other => ValueConversionError::err("FloatVec, Vec2f, Vec3f, or Vec4f", &other),
        }
    }
}

impl TryFrom<Value> for Vec<f64> {
    type Error = ValueConversionError;

    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::DoubleVec(v) | Value::Vec2d(v) | Value::Vec3d(v) | Value::Vec4d(v) => Ok(v),
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
        assert!(Value::UnregisteredValue.is_unregistered_value());
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
        assert_eq!(<[f32; 2]>::try_from(Value::Vec2f(vec![1.0, 2.0])).unwrap(), [1.0, 2.0]);
        assert_eq!(
            <[f32; 3]>::try_from(Value::Vec3f(vec![1.0, 2.0, 3.0])).unwrap(),
            [1.0, 2.0, 3.0]
        );
        assert_eq!(
            <[f32; 4]>::try_from(Value::Vec4f(vec![1.0, 2.0, 3.0, 4.0])).unwrap(),
            [1.0, 2.0, 3.0, 4.0]
        );
        assert_eq!(
            <[f64; 3]>::try_from(Value::Vec3d(vec![1.0, 2.0, 3.0])).unwrap(),
            [1.0, 2.0, 3.0]
        );
    }

    #[test]
    fn try_from_vec() {
        // Vec<f32> accepts any float vector variant.
        assert!(Vec::<f32>::try_from(Value::FloatVec(vec![1.0])).is_ok());
        assert!(Vec::<f32>::try_from(Value::Vec3f(vec![1.0, 2.0, 3.0])).is_ok());

        // Vec<f64> accepts any double vector variant.
        assert!(Vec::<f64>::try_from(Value::DoubleVec(vec![1.0])).is_ok());
        assert!(Vec::<f64>::try_from(Value::Vec2d(vec![1.0, 2.0])).is_ok());
    }

    #[test]
    fn try_from_wrong_variant() {
        let err = f32::try_from(Value::Int(1)).unwrap_err();
        assert_eq!(err.to_string(), "expected Float, got Int");

        let err = <[f32; 3]>::try_from(Value::Bool(true)).unwrap_err();
        assert_eq!(err.to_string(), "expected Vec3f, got Bool");
    }
}
