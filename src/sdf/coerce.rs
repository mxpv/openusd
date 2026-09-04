//! Schema-level value coercion: the conversions an attribute's declared type
//! applies to an authored value of another kind (C++ `VtValue::CastToTypeid`,
//! as `SdfPropertySpec::SetDefaultValue` and `SdfLayer::SetTimeSample` use it).
//!
//! [`allowed`] is the explicit allowlist, mirroring the casts C++ registers in
//! `vt/value.cpp`, `vt/types.cpp`, `sdf/timeCode.cpp` and `sdf/assetPath.cpp`:
//! every pair of numeric scalars, `double` ↔ `timecode`, `string` ↔ `token`,
//! `string` → `asset`, vectors of one dimension across precisions (`i` one
//! way, `h` ↔ `f` ↔ `d`), and arrays of `half` / `float` / `double` or of
//! `h` / `f` / `d` vectors of one dimension. A conversion keeps the value's
//! shape: a scalar stays a scalar, an array an array, a tuple keeps its
//! component count.
//!
//! Quaternions convert across those same three precisions, which C++ does
//! not register — an omission rather than a rule, since a `quatf` is a
//! `quatd`'s value at another precision exactly as a `float3` is a
//! `double3`'s. Authoring an `xformOp:orient` at the precision its asset
//! declares needs it, and routing it here is what range-checks it.
//!
//! Every numeric component and element is range- and finite-checked. That is
//! stricter than C++, which checks only scalar casts and lets compound and
//! array conversions saturate or wrap through their conversion constructors;
//! the divergence is deliberate, so a coerced value never holds an infinity
//! its author did not write.
//!
//! [`FromValueCast`](super::FromValueCast) is the looser, reading-side
//! conversion API; no validation path uses it.

use num_traits::{NumCast, ToPrimitive};

use crate::gf::f16;

use super::value::{
    CastError, Value, ValueKind, cast_numeric, finite_checked, vec2_as_f64, vec3_as_f64, vec4_as_f64, widen,
};
use super::{AssetPath, TimeCode};

impl Value {
    /// Coerces this value to `target`, keeping its shape.
    ///
    /// The exact kind passes through unchanged. A pair the module's allowlist
    /// does not admit is [`CastError::TypeMismatch`]; a component or element
    /// that does not fit the target, or leaves the finite range on the way,
    /// is [`CastError::OutOfRange`].
    pub fn coerce_to_kind(self, target: ValueKind) -> Result<Value, CastError> {
        let source = ValueKind::from(&self);
        if source == target {
            return Ok(self);
        }
        if !allowed(source, target) {
            return Err(mismatch(source, target));
        }
        convert(self, target)
    }
}

/// Whether a value of kind `source` may be coerced to `target`: the
/// allowlist of the module docs in one place, read by
/// [`Value::coerce_to_kind`] and by the pair-matrix test that pins it.
const fn allowed(source: ValueKind, target: ValueKind) -> bool {
    use ValueKind as K;
    matches!(
        (source, target),
        (
            K::Bool | K::Uchar | K::Int | K::Uint | K::Int64 | K::Uint64 | K::Half | K::Float | K::Double,
            K::Bool | K::Uchar | K::Int | K::Uint | K::Int64 | K::Uint64 | K::Half | K::Float | K::Double,
        ) | (K::Double, K::TimeCode)
            | (K::TimeCode, K::Double)
            | (K::String, K::Token | K::AssetPath)
            | (K::Token, K::String)
            | (
                K::Vec2i | K::Vec2h | K::Vec2f | K::Vec2d,
                K::Vec2h | K::Vec2f | K::Vec2d
            )
            | (
                K::Vec3i | K::Vec3h | K::Vec3f | K::Vec3d,
                K::Vec3h | K::Vec3f | K::Vec3d
            )
            | (
                K::Vec4i | K::Vec4h | K::Vec4f | K::Vec4d,
                K::Vec4h | K::Vec4f | K::Vec4d
            )
            | (K::Quath | K::Quatf | K::Quatd, K::Quath | K::Quatf | K::Quatd)
            | (
                K::HalfVec | K::FloatVec | K::DoubleVec,
                K::HalfVec | K::FloatVec | K::DoubleVec
            )
            | (
                K::Vec2hVec | K::Vec2fVec | K::Vec2dVec,
                K::Vec2hVec | K::Vec2fVec | K::Vec2dVec
            )
            | (
                K::Vec3hVec | K::Vec3fVec | K::Vec3dVec,
                K::Vec3hVec | K::Vec3fVec | K::Vec3dVec
            )
            | (
                K::Vec4hVec | K::Vec4fVec | K::Vec4dVec,
                K::Vec4hVec | K::Vec4fVec | K::Vec4dVec
            )
    )
}

/// The conversion for a pair [`allowed`] admits. A pair with no conversion
/// here is a mismatch too, which the pair-matrix test relies on to keep the
/// allowlist and the conversions in step.
///
/// A compound conversion widens every component to `f64` and narrows it to
/// the target, so one range check serves every source and target precision.
// TODO(perf): an array conversion builds an intermediate `f64` array before
// the narrowed one; a single element-wise pass would allocate once. Cold
// path: only a value of another kind than declared reaches it.
fn convert(value: Value, target: ValueKind) -> Result<Value, CastError> {
    use ValueKind as K;
    let source = ValueKind::from(&value);
    let actual: &'static str = source.into();
    let no_conversion = || mismatch(source, target);
    Ok(match (value, target) {
        (value, K::Bool) => Value::Bool(to_bool(&value).ok_or_else(no_conversion)?),
        (Value::TimeCode(t), K::Double) => Value::Double(t.0),
        (value, K::Uchar) => Value::Uchar(cast_numeric(value)?),
        (value, K::Int) => Value::Int(cast_numeric(value)?),
        (value, K::Uint) => Value::Uint(cast_numeric(value)?),
        (value, K::Int64) => Value::Int64(cast_numeric(value)?),
        (value, K::Uint64) => Value::Uint64(cast_numeric(value)?),
        (value, K::Half) => Value::Half(cast_numeric(value)?),
        (value, K::Float) => Value::Float(cast_numeric(value)?),
        (value, K::Double) => Value::Double(cast_numeric(value)?),
        (value, K::TimeCode) => Value::TimeCode(TimeCode(cast_numeric(value)?)),

        (Value::Token(t), K::String) => Value::String(t.into()),
        (Value::String(s), K::Token) => Value::token(s),
        (Value::String(s), K::AssetPath) => Value::AssetPath(AssetPath::new(s)),

        (value, K::Vec2h) => Value::Vec2h(vector::<f16, _, 2>(vec2_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec2f) => Value::Vec2f(vector::<f32, _, 2>(vec2_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec2d) => Value::Vec2d(vector::<f64, _, 2>(vec2_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec3h) => Value::Vec3h(vector::<f16, _, 3>(vec3_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec3f) => Value::Vec3f(vector::<f32, _, 3>(vec3_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec3d) => Value::Vec3d(vector::<f64, _, 3>(vec3_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec4h) => Value::Vec4h(vector::<f16, _, 4>(vec4_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec4f) => Value::Vec4f(vector::<f32, _, 4>(vec4_as_f64(&value), actual, no_conversion)?),
        (value, K::Vec4d) => Value::Vec4d(vector::<f64, _, 4>(vec4_as_f64(&value), actual, no_conversion)?),

        // `vec4_as_f64` reads a quaternion in `(w, x, y, z)` order, which is
        // the order `From<[T; 4]>` builds one from.
        (value, K::Quath) => Value::Quath(vector::<f16, _, 4>(vec4_as_f64(&value), actual, no_conversion)?),
        (value, K::Quatf) => Value::Quatf(vector::<f32, _, 4>(vec4_as_f64(&value), actual, no_conversion)?),
        (value, K::Quatd) => Value::Quatd(vector::<f64, _, 4>(vec4_as_f64(&value), actual, no_conversion)?),

        (value, K::HalfVec) => Value::HalfVec(array::<f16>(scalar_array(value), actual, no_conversion)?),
        (value, K::FloatVec) => Value::FloatVec(array::<f32>(scalar_array(value), actual, no_conversion)?),
        (value, K::DoubleVec) => Value::DoubleVec(array::<f64>(scalar_array(value), actual, no_conversion)?),

        (value, K::Vec2hVec) => Value::Vec2hVec(vector_array::<f16, _, 2>(vec2_array(value), actual, no_conversion)?),
        (value, K::Vec2fVec) => Value::Vec2fVec(vector_array::<f32, _, 2>(vec2_array(value), actual, no_conversion)?),
        (value, K::Vec2dVec) => Value::Vec2dVec(vector_array::<f64, _, 2>(vec2_array(value), actual, no_conversion)?),
        (value, K::Vec3hVec) => Value::Vec3hVec(vector_array::<f16, _, 3>(vec3_array(value), actual, no_conversion)?),
        (value, K::Vec3fVec) => Value::Vec3fVec(vector_array::<f32, _, 3>(vec3_array(value), actual, no_conversion)?),
        (value, K::Vec3dVec) => Value::Vec3dVec(vector_array::<f64, _, 3>(vec3_array(value), actual, no_conversion)?),
        (value, K::Vec4hVec) => Value::Vec4hVec(vector_array::<f16, _, 4>(vec4_array(value), actual, no_conversion)?),
        (value, K::Vec4fVec) => Value::Vec4fVec(vector_array::<f32, _, 4>(vec4_array(value), actual, no_conversion)?),
        (value, K::Vec4dVec) => Value::Vec4dVec(vector_array::<f64, _, 4>(vec4_array(value), actual, no_conversion)?),

        _ => return Err(no_conversion()),
    })
}

fn mismatch(source: ValueKind, target: ValueKind) -> CastError {
    CastError::TypeMismatch {
        target: target.into(),
        actual: source.into(),
    }
}

/// C++ `static_cast<bool>`: anything but a zero is `true`, so NaN and the
/// infinities are `true` and both zeros are `false`.
fn to_bool(value: &Value) -> Option<bool> {
    Some(match value {
        Value::Bool(b) => *b,
        Value::Uchar(v) => *v != 0,
        Value::Int(v) => *v != 0,
        Value::Uint(v) => *v != 0,
        Value::Int64(v) => *v != 0,
        Value::Uint64(v) => *v != 0,
        Value::Half(v) => *v != f16::ZERO,
        Value::Float(v) => *v != 0.0,
        Value::Double(v) => *v != 0.0,
        _ => return None,
    })
}

/// Narrows one `f64` component to `T` with the scalar rules: a value the
/// target cannot hold, or one that turns non-finite on the way, is out of
/// range. The `f64` intermediate is lossless for every source the allowlist
/// admits (`i32`, `f16`, `f32`, `f64`).
fn narrow<T: NumCast + ToPrimitive>(value: f64, actual: &'static str) -> Result<T, CastError> {
    finite_checked(NumCast::from(value), value.is_finite(), actual)
}

fn narrow_array<T, const N: usize>(components: [f64; N], actual: &'static str) -> Result<[T; N], CastError>
where
    T: NumCast + ToPrimitive + Copy + Default,
{
    let mut out = [T::default(); N];
    for (slot, component) in out.iter_mut().zip(components) {
        *slot = narrow(component, actual)?;
    }
    Ok(out)
}

/// A vector of dimension `N` narrowed from `components`, or the pair's
/// mismatch when the source was not a vector of that dimension.
fn vector<T, V, const N: usize>(
    components: Option<[f64; N]>,
    actual: &'static str,
    no_conversion: impl FnOnce() -> CastError,
) -> Result<V, CastError>
where
    T: NumCast + ToPrimitive + Copy + Default,
    V: From<[T; N]>,
{
    narrow_array(components.ok_or_else(no_conversion)?, actual).map(V::from)
}

/// A scalar array narrowed from `elements`, or the pair's mismatch when the
/// source was not a floating-point array.
fn array<T: NumCast + ToPrimitive>(
    elements: Option<Vec<f64>>,
    actual: &'static str,
    no_conversion: impl FnOnce() -> CastError,
) -> Result<Vec<T>, CastError> {
    elements
        .ok_or_else(no_conversion)?
        .into_iter()
        .map(|v| narrow(v, actual))
        .collect()
}

/// A vector array of dimension `N` narrowed from `elements`, or the pair's
/// mismatch when the source was not a vector array of that dimension.
fn vector_array<T, V, const N: usize>(
    elements: Option<Vec<[f64; N]>>,
    actual: &'static str,
    no_conversion: impl FnOnce() -> CastError,
) -> Result<Vec<V>, CastError>
where
    T: NumCast + ToPrimitive + Copy + Default,
    V: From<[T; N]>,
{
    elements
        .ok_or_else(no_conversion)?
        .into_iter()
        .map(|e| narrow_array::<T, N>(e, actual).map(V::from))
        .collect()
}

/// The `f64` component arrays of a vector-array value of a dimension. Integer
/// vector arrays are not a source, as in C++.
macro_rules! vec_array {
    ($name:ident, $n:literal, $h:ident, $f:ident, $d:ident) => {
        fn $name(value: Value) -> Option<Vec<[f64; $n]>> {
            Some(match value {
                Value::$h(v) => v.into_iter().map(|e| widen(<[f16; $n]>::from(e))).collect(),
                Value::$f(v) => v.into_iter().map(|e| widen(<[f32; $n]>::from(e))).collect(),
                Value::$d(v) => v.into_iter().map(<[f64; $n]>::from).collect(),
                _ => return None,
            })
        }
    };
}

vec_array!(vec2_array, 2, Vec2hVec, Vec2fVec, Vec2dVec);
vec_array!(vec3_array, 3, Vec3hVec, Vec3fVec, Vec3dVec);
vec_array!(vec4_array, 4, Vec4hVec, Vec4fVec, Vec4dVec);

/// The `f64` elements of a floating-point scalar array.
fn scalar_array(value: Value) -> Option<Vec<f64>> {
    Some(match value {
        Value::HalfVec(v) => v.into_iter().map(Into::into).collect(),
        Value::FloatVec(v) => v.into_iter().map(Into::into).collect(),
        Value::DoubleVec(v) => v,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use strum::IntoEnumIterator;

    use crate::gf;

    use super::*;

    /// The attribute kinds: 32 scalar kinds and their array twins, plus
    /// `Opaque`. Each kind's default is inside every target's range, so a
    /// conversion the allowlist admits succeeds on it.
    fn attribute_kinds() -> Vec<(ValueKind, Value)> {
        ValueKind::iter()
            .filter_map(|kind| kind.default_value().map(|value| (kind, value)))
            .collect()
    }

    #[test]
    fn coerce_kind_matrix() {
        let kinds = attribute_kinds();
        assert_eq!(kinds.len(), 65, "every attribute kind has a default");
        for (source, sample) in &kinds {
            for (target, _) in &kinds {
                let result = sample.clone().coerce_to_kind(*target);
                let expected = source == target || allowed(*source, *target);
                assert_eq!(result.is_ok(), expected, "{source} -> {target}: {result:?}");
                if let Ok(value) = result {
                    assert_eq!(
                        ValueKind::from(&value),
                        *target,
                        "{source} -> {target} lands in the target kind"
                    );
                }
            }
        }
    }

    #[test]
    fn coerce_kind_quat() {
        let one = f16::from_f32(1.0);
        assert_eq!(
            Value::Quatf(gf::Quatf::IDENTITY).coerce_to_kind(ValueKind::Quatd),
            Ok(Value::Quatd(gf::Quatd::IDENTITY))
        );
        assert_eq!(
            Value::Quatd(gf::Quatd::IDENTITY).coerce_to_kind(ValueKind::Quath),
            Ok(Value::Quath(gf::Quath::IDENTITY))
        );
        assert_eq!(
            Value::Quath(gf::Quath::IDENTITY).coerce_to_kind(ValueKind::Quatf),
            Ok(Value::Quatf(gf::Quatf::IDENTITY))
        );
        assert_eq!(one.to_f32(), 1.0, "the identity's real part survives the narrowing");
        // Nothing normalizes an authored quaternion, so a component out of
        // the target's range is reported rather than saturated.
        assert!(matches!(
            Value::Quatf(gf::Quatf {
                w: 70000.0,
                x: 0.0,
                y: 0.0,
                z: 0.0
            })
            .coerce_to_kind(ValueKind::Quath),
            Err(CastError::OutOfRange { .. })
        ));
        assert!(matches!(
            Value::vec4f(1.0, 0.0, 0.0, 0.0).coerce_to_kind(ValueKind::Quatf),
            Err(CastError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn coerce_kind_numeric() {
        assert_eq!(Value::Int(3).coerce_to_kind(ValueKind::Float), Ok(Value::Float(3.0)));
        assert_eq!(Value::Double(2.5).coerce_to_kind(ValueKind::Int), Ok(Value::Int(2)));
        assert_eq!(
            Value::Double(2.5).coerce_to_kind(ValueKind::TimeCode),
            Ok(Value::TimeCode(TimeCode(2.5)))
        );
        assert_eq!(
            Value::TimeCode(TimeCode(4.0)).coerce_to_kind(ValueKind::Double),
            Ok(Value::Double(4.0))
        );
        assert!(matches!(
            Value::Int(-1).coerce_to_kind(ValueKind::Uint),
            Err(CastError::OutOfRange { .. })
        ));
        assert!(matches!(
            Value::Int(1).coerce_to_kind(ValueKind::TimeCode),
            Err(CastError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn coerce_kind_vec_precision() {
        assert_eq!(
            Value::vec3d(1.5, 2.5, 3.5).coerce_to_kind(ValueKind::Vec3f),
            Ok(Value::vec3f(1.5, 2.5, 3.5))
        );
        let one = f16::from_f32(1.0);
        assert_eq!(
            Value::vec3i(1, 1, 1).coerce_to_kind(ValueKind::Vec3h),
            Ok(Value::vec3h(one, one, one))
        );
        assert!(matches!(
            Value::vec3f(1.0, 2.0, 3.0).coerce_to_kind(ValueKind::Vec3i),
            Err(CastError::TypeMismatch { .. })
        ));
        assert_eq!(
            Value::String("s".into()).coerce_to_kind(ValueKind::Token),
            Ok(Value::token("s"))
        );
        assert_eq!(
            Value::String("a".into()).coerce_to_kind(ValueKind::AssetPath),
            Ok(Value::AssetPath(AssetPath::new("a")))
        );
        assert!(matches!(
            Value::AssetPath(AssetPath::new("a")).coerce_to_kind(ValueKind::String),
            Err(CastError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn coerce_kind_elementwise() {
        assert_eq!(
            Value::DoubleVec(vec![1.5, 2.5]).coerce_to_kind(ValueKind::FloatVec),
            Ok(Value::FloatVec(vec![1.5, 2.5]))
        );
        let one = f16::from_f32(1.0);
        assert_eq!(
            Value::Vec3dVec(vec![gf::vec3d(1.0, 1.0, 1.0)]).coerce_to_kind(ValueKind::Vec3hVec),
            Ok(Value::Vec3hVec(vec![gf::vec3h(one, one, one)]))
        );
        assert!(matches!(
            Value::IntVec(vec![1]).coerce_to_kind(ValueKind::FloatVec),
            Err(CastError::TypeMismatch { .. })
        ));
        assert!(matches!(
            Value::Vec3iVec(vec![gf::vec3i(1, 1, 1)]).coerce_to_kind(ValueKind::Vec3fVec),
            Err(CastError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn coerce_kind_keeps_shape() {
        assert!(matches!(
            Value::vec3f(1.0, 2.0, 3.0).coerce_to_kind(ValueKind::FloatVec),
            Err(CastError::TypeMismatch { .. })
        ));
        assert!(matches!(
            Value::Float(1.0).coerce_to_kind(ValueKind::FloatVec),
            Err(CastError::TypeMismatch { .. })
        ));
        assert!(matches!(
            Value::vec3f(1.0, 2.0, 3.0).coerce_to_kind(ValueKind::Vec4f),
            Err(CastError::TypeMismatch { .. })
        ));
        assert!(matches!(
            Value::FloatVec(vec![1.0]).coerce_to_kind(ValueKind::Float),
            Err(CastError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn coerce_kind_bool() {
        let to_bool = |v: Value| v.coerce_to_kind(ValueKind::Bool);
        assert_eq!(to_bool(Value::Int(-3)), Ok(Value::Bool(true)));
        assert_eq!(to_bool(Value::Double(2.5)), Ok(Value::Bool(true)));
        assert_eq!(to_bool(Value::Double(0.0)), Ok(Value::Bool(false)));
        assert_eq!(to_bool(Value::Double(-0.0)), Ok(Value::Bool(false)));
        assert_eq!(to_bool(Value::Float(f32::NAN)), Ok(Value::Bool(true)));
        assert_eq!(to_bool(Value::Double(f64::INFINITY)), Ok(Value::Bool(true)));
        assert_eq!(to_bool(Value::Double(f64::NEG_INFINITY)), Ok(Value::Bool(true)));
        assert_eq!(to_bool(Value::Half(f16::ZERO)), Ok(Value::Bool(false)));
        assert_eq!(Value::Bool(true).coerce_to_kind(ValueKind::Int), Ok(Value::Int(1)));
        assert_eq!(Value::Bool(false).coerce_to_kind(ValueKind::Int), Ok(Value::Int(0)));
    }

    #[test]
    fn vec_cast_overflow() {
        assert!(matches!(
            Value::vec3i(1_000_000, 0, 0).coerce_to_kind(ValueKind::Vec3h),
            Err(CastError::OutOfRange { .. })
        ));
        assert!(Value::vec3i(1_000, 0, 0).coerce_to_kind(ValueKind::Vec3h).is_ok());
    }

    #[test]
    fn array_cast_overflow() {
        assert!(matches!(
            Value::DoubleVec(vec![1.0, 1e300]).coerce_to_kind(ValueKind::FloatVec),
            Err(CastError::OutOfRange { .. })
        ));
        assert_eq!(
            Value::DoubleVec(vec![1.5, 2.0]).coerce_to_kind(ValueKind::FloatVec),
            Ok(Value::FloatVec(vec![1.5, 2.0]))
        );
    }
}
