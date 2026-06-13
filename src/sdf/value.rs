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
#[derive(Debug, Clone, PartialEq, EnumIs, EnumTryAs, IntoStaticStr, derive_more::From)]
pub enum Value {
    /// None value, only produced by expressions (not directly assignable).
    #[from(skip)]
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

    #[from(skip)]
    ValueBlock,
    #[from(skip)]
    Value,

    /// Heterogeneous array (e.g. spline knots). Each element is a `Value`.
    ValueVec(Vec<Value>),

    #[from(skip)]
    UnregisteredValue(String),
    #[from(skip)]
    UnregisteredValueListOp(StringListOp),

    TimeCode(TimeCode),
    TimeCodeVec(Vec<TimeCode>),
    #[from(skip)]
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

            Value::TokenListOp(v) => v.serialize(serializer),
            Value::StringListOp(v) => v.serialize(serializer),
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

impl Value {
    /// Extracts the payload as `T` if this holds the matching variant, else
    /// `None`. A typed view over the `try_as_*` accessors and the
    /// [`TryFrom<Value>`] impls — e.g. `value.get::<tf::Token>()`. `T = Value`
    /// returns the value unchanged.
    pub fn get<T: TryFrom<Value>>(self) -> Option<T> {
        T::try_from(self).ok()
    }

    /// Whether this value embeds namespace paths that [`remap_paths`](Self::remap_paths)
    /// rewrites — `PathVec`, `PathListOp` (relationship targets, attribute
    /// connections, `inheritPaths`, `specializes`), `Relocates`, and
    /// `ReferenceListOp` / `PayloadListOp` (whose internal entries target this
    /// layer's own namespace). The single source of truth a copy value policy
    /// checks before remapping, so the set of path-bearing variants lives only
    /// here.
    pub fn has_embedded_paths(&self) -> bool {
        matches!(
            self,
            Value::PathVec(_)
                | Value::PathListOp(_)
                | Value::Relocates(_)
                | Value::ReferenceListOp(_)
                | Value::PayloadListOp(_)
        )
    }

    /// Returns a copy of this value with every embedded namespace path rewritten
    /// through `remap`. Paths live in `PathVec`, `PathListOp` (relationship
    /// targets, attribute connections, `inheritPaths`, `specializes`),
    /// `Relocates` (source/target pairs), and the prim paths of internal
    /// (same-layer) `ReferenceListOp` / `PayloadListOp` entries. An external
    /// reference or payload carries its prim path in the referenced layer's
    /// namespace, and an empty prim path is the defaultPrim selector — both
    /// are left untouched; every other value kind is cloned unchanged.
    ///
    /// The path-rewriting core behind [`copy_spec`](crate::sdf::copy_spec),
    /// exposed so callers building a custom copy value policy (flatten, namespace
    /// editing, rename) can remap paths with their own mapping rather than the
    /// default root-to-root prefix swap.
    pub fn remap_paths(&self, remap: impl Fn(&Path) -> Path) -> Value {
        let remap = &remap;
        match self {
            Value::PathVec(paths) => Value::PathVec(paths.iter().map(remap).collect()),
            Value::PathListOp(op) => Value::PathListOp(op.clone().map(|p| remap(&p))),
            Value::Relocates(relocates) => {
                Value::Relocates(relocates.iter().map(|(s, t)| (remap(s), remap(t))).collect())
            }
            Value::ReferenceListOp(op) => Value::ReferenceListOp(op.clone().map(|mut reference| {
                if reference.asset_path.is_empty() && !reference.prim_path.is_empty() {
                    reference.prim_path = remap(&reference.prim_path);
                }
                reference
            })),
            Value::PayloadListOp(op) => Value::PayloadListOp(op.clone().map(|mut payload| {
                if payload.asset_path.is_empty() && !payload.prim_path.is_empty() {
                    payload.prim_path = remap(&payload.prim_path);
                }
                payload
            })),
            other => other.clone(),
        }
    }
}

// Exact extraction: owned conversions that move data out of `Value` without
// cloning, each requiring the exact held variant. They delegate to the
// strum-generated `try_as_*()` methods (from the `EnumTryAs` derive);
// cross-type coercion (`token` → `string`, numeric and vector precision) is
// the separate, opt-in `Value::cast` tier.

macro_rules! impl_try_from_value {
    // Exact: unwrap the matching variant.
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
    // Unwrap the matching variant, then convert each element via `Into` — used
    // by the `gf`-vector-array conversions (`Vec<Vec3f>` → `Vec<[f32; 3]>`).
    ($target:ty, $method:ident, $label:literal, map_into) => {
        impl_try_from_value!($target, $method, $label, |v| v
            .into_iter()
            .map(Into::into)
            .collect());
    };
    // Unwrap the matching variant, then map it through `$transform` — used by
    // the `gf`-vector-to-fixed-array conversions (`Vec3f` → `[f32; 3]`).
    ($target:ty, $method:ident, $label:literal, $transform:expr) => {
        impl TryFrom<Value> for $target {
            type Error = ValueConversionError;

            fn try_from(value: Value) -> Result<Self, Self::Error> {
                let tag: &'static str = (&value).into();
                value.$method().map($transform).ok_or(ValueConversionError {
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

// Single-variant string and asset extraction. Coercing `token` → `string`
// is [`Value::cast`]'s job.
impl_try_from_value!(String, try_as_string, "String");
impl_try_from_value!(Token, try_as_token, "Token");
impl_try_from_value!(Vec<Token>, try_as_token_vec, "TokenVec");
impl_try_from_value!(Vec<String>, try_as_string_vec, "StringVec");
impl_try_from_value!(AssetPath, try_as_asset_path, "AssetPath");
impl_try_from_value!(Vec<AssetPath>, try_as_asset_path_vec, "AssetPathVec");

// List ops, relocations, time samples, and layer offsets — composite payloads
// read through the typed spec accessors.
impl_try_from_value!(TokenListOp, try_as_token_list_op, "TokenListOp");
impl_try_from_value!(RelocateList, try_as_relocates, "Relocates");
impl_try_from_value!(TimeSampleMap, try_as_time_samples, "TimeSamples");
impl_try_from_value!(Vec<LayerOffset>, try_as_layer_offset_vec, "LayerOffsetVec");

// Exact numeric arrays — `float[]` / `double[]`. Flattening a single vector
// into a scalar array is a coercion, so it lives in [`Value::cast`].
impl_try_from_value!(Vec<f32>, try_as_float_vec, "FloatVec");
impl_try_from_value!(Vec<f64>, try_as_double_vec, "DoubleVec");

// `gf` vector/quaternion variants as fixed-size arrays, via the type's `Into`.
// Coercing across element precisions is [`Value::cast`]'s job.
impl_try_from_value!([f32; 2], try_as_vec_2f, "gf::Vec2f", Into::into);
impl_try_from_value!([f32; 3], try_as_vec_3f, "gf::Vec3f", Into::into);
impl_try_from_value!([f32; 4], try_as_vec_4f, "gf::Vec4f", Into::into);
impl_try_from_value!([f64; 2], try_as_vec_2d, "gf::Vec2d", Into::into);
impl_try_from_value!([f64; 3], try_as_vec_3d, "gf::Vec3d", Into::into);
impl_try_from_value!([f64; 4], try_as_vec_4d, "gf::Vec4d", Into::into);

// `gf` vector arrays as arrays of fixed-size arrays.
impl_try_from_value!(Vec<[f32; 2]>, try_as_vec_2f_vec, "Vec2fVec", map_into);
impl_try_from_value!(Vec<[f32; 3]>, try_as_vec_3f_vec, "Vec3fVec", map_into);
impl_try_from_value!(Vec<[f32; 4]>, try_as_vec_4f_vec, "Vec4fVec", map_into);

/// Convert from `&str` to `Value`.
///
/// Used a lot in text parser since all tokens are basically strings.
impl<'a> From<&'a str> for Value {
    fn from(value: &'a str) -> Self {
        Value::String(value.to_string())
    }
}

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

    /// Coerces this value to `T` through the registered casts, mirroring C++
    /// `VtValue::Cast`: numeric scalars cross-convert (range-checked), `string`
    /// ↔ `token`, and same-dimension vectors/quaternions change precision.
    ///
    /// Unlike `T::try_from` / [`Attribute::get`](crate::usd::Attribute::get),
    /// which require the exact held variant, `cast` is the coercing tier — read
    /// the raw value and cast when the authored type may differ from the wanted
    /// one: `attr.get::<Value>()?.map(|v| v.cast::<f32>()).transpose()?`.
    pub fn cast<T: FromValueCast>(self) -> Result<T, CastError> {
        T::cast_from(self)
    }
}

/// A type that [`Value::cast`] can coerce a [`Value`] into — the Rust side of
/// C++ `VtValue`'s registered cast set. Takes the value by move so a
/// same-variant cast (e.g. `StringVec` to `Vec<String>`) reuses its buffer
/// rather than cloning, matching the owned [`TryFrom<Value>`] it complements.
///
/// The implemented targets are demand-driven — the scalar, string/token, and
/// the specific array/vector shapes current callers read. The set is not the
/// full precision×dimension matrix: a missing target (e.g. `cast::<gf::Vec2f>`)
/// is a compile error, signalling "add the impl when a caller needs it" rather
/// than a silent gap. Add new targets here as the need arises.
pub trait FromValueCast: Sized {
    /// Coerces `value` to `Self`, or reports why it cannot.
    fn cast_from(value: Value) -> Result<Self, CastError>;
}

/// Error returned by [`Value::cast`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum CastError {
    /// The held variant has no registered cast to the target type.
    #[error("cannot cast {actual} to {target}")]
    TypeMismatch {
        /// The requested target type.
        target: &'static str,
        /// The actual held variant.
        actual: &'static str,
    },
    /// The numeric value is outside the target type's representable range
    /// (faithful to C++ `numeric_cast`).
    #[error("{actual} value is out of range for {target}")]
    OutOfRange {
        /// The requested target type.
        target: &'static str,
        /// The actual held variant.
        actual: &'static str,
    },
}

impl CastError {
    fn mismatch<T>(actual: &'static str) -> Self {
        Self::TypeMismatch {
            target: std::any::type_name::<T>(),
            actual,
        }
    }

    fn out_of_range<T>(actual: &'static str) -> Self {
        Self::OutOfRange {
            target: std::any::type_name::<T>(),
            actual,
        }
    }
}

/// Range-checked numeric coercion shared by every scalar `FromValueCast` target.
/// `num_traits::NumCast` is `boost::numeric_cast`: it returns `None` when an
/// integer target overflows, which maps to [`CastError::OutOfRange`].
///
/// Narrowing float conversions (`f64` → `f32`/`f16`) are not range-checked by
/// `NumCast` — they saturate to infinity instead of returning `None` — so a
/// finite source that produces a non-finite result is reported as out of range
/// too. An already-infinite source legitimately stays infinite.
fn cast_numeric<T: num_traits::NumCast>(value: Value) -> Result<T, CastError> {
    use num_traits::NumCast;
    let actual: &'static str = (&value).into();
    let src_finite = match &value {
        Value::Half(v) => v.is_finite(),
        Value::Float(v) => v.is_finite(),
        Value::Double(v) => v.is_finite(),
        _ => true,
    };
    let out: T = match value {
        Value::Uchar(v) => NumCast::from(v),
        Value::Int(v) => NumCast::from(v),
        Value::Uint(v) => NumCast::from(v),
        Value::Int64(v) => NumCast::from(v),
        Value::Uint64(v) => NumCast::from(v),
        Value::Half(v) => NumCast::from(v),
        Value::Float(v) => NumCast::from(v),
        Value::Double(v) => NumCast::from(v),
        Value::Bool(v) => NumCast::from(v as u8),
        _ => return Err(CastError::mismatch::<T>(actual)),
    }
    .ok_or_else(|| CastError::out_of_range::<T>(actual))?;
    if src_finite && out.to_f64().is_some_and(|f| !f.is_finite()) {
        return Err(CastError::out_of_range::<T>(actual));
    }
    Ok(out)
}

macro_rules! impl_cast_numeric {
    ($($t:ty),+ $(,)?) => {$(
        impl FromValueCast for $t {
            fn cast_from(value: Value) -> Result<Self, CastError> {
                cast_numeric(value)
            }
        }
    )+};
}

impl_cast_numeric!(u8, i32, u32, i64, u64, f16, f32, f64);

impl FromValueCast for bool {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        match value {
            Value::Bool(b) => Ok(b),
            other => Err(CastError::mismatch::<bool>((&other).into())),
        }
    }
}

impl FromValueCast for String {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        match value {
            Value::String(s) => Ok(s),
            Value::Token(t) => Ok(t.into()),
            Value::AssetPath(a) => Ok(a.authored_path),
            other => Err(CastError::mismatch::<String>((&other).into())),
        }
    }
}

impl FromValueCast for Token {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        match value {
            Value::Token(t) => Ok(t),
            Value::String(s) => Ok(Token::from(s)),
            other => Err(CastError::mismatch::<Token>((&other).into())),
        }
    }
}

impl FromValueCast for Vec<String> {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        match value {
            Value::StringVec(v) => Ok(v),
            Value::TokenVec(v) => Ok(v.into_iter().map(String::from).collect()),
            Value::AssetPathVec(v) => Ok(v.into_iter().map(|a| a.authored_path).collect()),
            other => Err(CastError::mismatch::<Vec<String>>((&other).into())),
        }
    }
}

/// Lifts a `Value`-inspecting helper's `Option` into a cast result, reporting a
/// type mismatch against `R` (the cast's target type) when no conversion applied.
fn require<R, U>(value: &Value, converted: Option<U>) -> Result<U, CastError> {
    converted.ok_or_else(|| CastError::mismatch::<R>(value.into()))
}

/// Widens a 3-component vector (`f`/`d`/`h`/`i`) to `[f64; 3]`. The `f`/`d`
/// arms reuse gf's `Into<[f64; 3]>`; `h`/`i` have no such impl and widen here.
fn vec3_as_f64(value: &Value) -> Option<[f64; 3]> {
    Some(match value {
        Value::Vec3f(v) => (*v).into(),
        Value::Vec3d(v) => (*v).into(),
        Value::Vec3h(v) => [f64::from(v.x), f64::from(v.y), f64::from(v.z)],
        Value::Vec3i(v) => [v.x as f64, v.y as f64, v.z as f64],
        _ => return None,
    })
}

/// Widens a 4-component vector or quaternion to `[f64; 4]`. Quaternions extract
/// in `(w, x, y, z)` order; the `Vec4d`/`Quatf`/`Quatd` arms reuse gf's
/// `Into<[f64; 4]>` (which encodes that order), and the rest widen here.
fn vec4_as_f64(value: &Value) -> Option<[f64; 4]> {
    Some(match value {
        Value::Vec4f(v) => [v.x as f64, v.y as f64, v.z as f64, v.w as f64],
        Value::Vec4d(v) => (*v).into(),
        Value::Vec4h(v) => [f64::from(v.x), f64::from(v.y), f64::from(v.z), f64::from(v.w)],
        Value::Vec4i(v) => [v.x as f64, v.y as f64, v.z as f64, v.w as f64],
        Value::Quatf(q) => (*q).into(),
        Value::Quatd(q) => (*q).into(),
        Value::Quath(q) => [f64::from(q.w), f64::from(q.x), f64::from(q.y), f64::from(q.z)],
        _ => return None,
    })
}

impl FromValueCast for [f64; 3] {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        require::<Self, _>(&value, vec3_as_f64(&value))
    }
}

impl FromValueCast for [f64; 4] {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        require::<Self, _>(&value, vec4_as_f64(&value))
    }
}

impl FromValueCast for [f32; 4] {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        let a = require::<Self, _>(&value, vec4_as_f64(&value))?;
        Ok([a[0] as f32, a[1] as f32, a[2] as f32, a[3] as f32])
    }
}

impl FromValueCast for gf::Vec3f {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        let [x, y, z] = require::<Self, _>(&value, vec3_as_f64(&value))?;
        Ok(gf::vec3f(x as f32, y as f32, z as f32))
    }
}

impl FromValueCast for Vec<f32> {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        match value {
            Value::FloatVec(v) => Ok(v),
            Value::DoubleVec(v) => Ok(v.into_iter().map(|d| d as f32).collect()),
            Value::HalfVec(v) => Ok(v.into_iter().map(f32::from).collect()),
            Value::Vec2f(v) => Ok(vec![v.x, v.y]),
            Value::Vec3f(v) => Ok(vec![v.x, v.y, v.z]),
            Value::Vec4f(v) => Ok(vec![v.x, v.y, v.z, v.w]),
            other => Err(CastError::mismatch::<Vec<f32>>((&other).into())),
        }
    }
}

impl FromValueCast for Vec<gf::Vec3f> {
    fn cast_from(value: Value) -> Result<Self, CastError> {
        match value {
            Value::Vec3fVec(v) => Ok(v),
            Value::Vec3dVec(v) => Ok(v
                .into_iter()
                .map(|d| gf::vec3f(d.x as f32, d.y as f32, d.z as f32))
                .collect()),
            Value::Vec3hVec(v) => Ok(v
                .into_iter()
                .map(|h| gf::vec3f(f32::from(h.x), f32::from(h.y), f32::from(h.z)))
                .collect()),
            other => Err(CastError::mismatch::<Vec<gf::Vec3f>>((&other).into())),
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
    fn remap_paths_rewrites_embedded() {
        let p = |s: &str| crate::sdf::path(s).unwrap();
        let remap = |path: &Path| path.replace_prefix(&p("/A"), &p("/B")).unwrap_or_else(|| path.clone());

        // PathListOp: an in-subtree path re-roots, an outside path is untouched.
        let op = Value::PathListOp(PathListOp::explicit([p("/A/Child"), p("/Other")]));
        let items: Vec<String> = op
            .remap_paths(remap)
            .try_as_path_list_op()
            .unwrap()
            .explicit_items
            .iter()
            .map(|p| p.as_str().to_owned())
            .collect();
        assert_eq!(items, vec!["/B/Child", "/Other"]);

        // PathVec and both endpoints of a Relocates remap.
        let pv = Value::PathVec(vec![p("/A/X")]).remap_paths(remap);
        assert_eq!(pv.try_as_path_vec().unwrap()[0].as_str(), "/B/X");
        let relocates = Value::Relocates(vec![(p("/A/From"), p("/A/To"))]).remap_paths(remap);
        let pairs = relocates.try_as_relocates().unwrap();
        assert_eq!((pairs[0].0.as_str(), pairs[0].1.as_str()), ("/B/From", "/B/To"));

        // A value with no embedded paths is returned unchanged.
        assert_eq!(Value::Int(7).remap_paths(remap), Value::Int(7));
    }

    #[test]
    fn try_from_scalars() {
        assert!(bool::try_from(Value::Bool(true)).unwrap());
        assert_eq!(i32::try_from(Value::Int(42)).unwrap(), 42);
        assert_eq!(f32::try_from(Value::Float(1.5)).unwrap(), 1.5);
        assert_eq!(f64::try_from(Value::Double(2.5)).unwrap(), 2.5);
        assert_eq!(String::try_from(Value::String("hello".into())).unwrap(), "hello");
        // Exact extraction does not coerce a token to a string — that is `cast`.
        assert!(String::try_from(Value::Token("tok".into())).is_err());
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
        // Exact extraction takes the array variant only; flattening a single
        // vector into a scalar array is `cast`, not `try_from`.
        assert_eq!(Vec::<f32>::try_from(Value::FloatVec(vec![1.0])).unwrap(), vec![1.0]);
        assert!(Vec::<f32>::try_from(Value::Vec3f(gf::vec3f(1.0, 2.0, 3.0))).is_err());

        assert_eq!(Vec::<f64>::try_from(Value::DoubleVec(vec![1.0])).unwrap(), vec![1.0]);
        assert!(Vec::<f64>::try_from(Value::Vec2d(gf::vec2d(1.0, 2.0))).is_err());

        // The coercing tier still flattens.
        assert_eq!(
            Value::Vec3f(gf::vec3f(1.0, 2.0, 3.0)).cast::<Vec<f32>>().unwrap(),
            vec![1.0, 2.0, 3.0]
        );
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
    fn cast_numeric_widen_narrow() {
        // Cross-type numeric coercion, both widening and narrowing.
        assert_eq!(Value::Int(42).cast::<f64>().unwrap(), 42.0);
        assert_eq!(Value::Double(2.0).cast::<i32>().unwrap(), 2);
        assert_eq!(Value::Uchar(255).cast::<i32>().unwrap(), 255);
        assert_eq!(Value::Half(f16::from_f32(1.5)).cast::<f32>().unwrap(), 1.5);
    }

    #[test]
    fn cast_out_of_range() {
        // A double beyond i32's range is a range error, not a type error.
        assert!(matches!(
            Value::Double(1e40).cast::<i32>(),
            Err(CastError::OutOfRange { .. })
        ));
        // Narrowing a finite double past f32/f16's range saturates to infinity
        // in `NumCast`; we report it as out of range, not a silent infinity.
        assert!(matches!(
            Value::Double(f64::MAX).cast::<f32>(),
            Err(CastError::OutOfRange { .. })
        ));
        assert!(matches!(
            Value::Float(f32::MAX).cast::<f16>(),
            Err(CastError::OutOfRange { .. })
        ));
        // An already-infinite source stays infinite — that is not an overflow.
        assert_eq!(Value::Double(f64::INFINITY).cast::<f32>().unwrap(), f32::INFINITY);
        // A non-numeric variant is a type mismatch.
        assert!(matches!(
            Value::Bool(true).cast::<gf::Vec3f>(),
            Err(CastError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn cast_string_token() {
        assert_eq!(Value::Token("t".into()).cast::<String>().unwrap(), "t");
        assert_eq!(Value::String("s".into()).cast::<Token>().unwrap(), Token::new("s"));
        assert_eq!(
            Value::TokenVec(vec!["a".into(), "b".into()])
                .cast::<Vec<String>>()
                .unwrap(),
            vec!["a".to_string(), "b".to_string()]
        );
    }

    #[test]
    fn cast_vec_precision() {
        // Same-dimension precision cast: a double vector reads as Vec3f.
        assert_eq!(
            Value::Vec3d(gf::vec3d(1.0, 2.0, 3.0)).cast::<gf::Vec3f>().unwrap(),
            gf::vec3f(1.0, 2.0, 3.0)
        );
        // [f64; 3] widens a float vector.
        assert_eq!(
            Value::Vec3f(gf::vec3f(1.0, 2.0, 3.0)).cast::<[f64; 3]>().unwrap(),
            [1.0, 2.0, 3.0]
        );
    }

    #[test]
    fn cast_quat_wxyz_order() {
        // [f64; 4] from a quaternion is (w, x, y, z).
        let q = gf::quatf(1.0, 2.0, 3.0, 4.0);
        assert_eq!(Value::Quatf(q).cast::<[f64; 4]>().unwrap(), [1.0, 2.0, 3.0, 4.0]);
    }

    #[test]
    fn from_gf_roundtrip() {
        let v = gf::vec3f(1.0, 2.0, 3.0);
        assert_eq!(Value::from(v), Value::Vec3f(v));

        let m = gf::Matrix4d::IDENTITY;
        assert_eq!(Value::from(m), Value::Matrix4d(m));
    }
}
