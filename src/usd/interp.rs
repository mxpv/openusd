//! Stage-level time-sample interpolation.
//!
//! Implements §12.5 of the AOUSD Core Specification — the universal
//! evaluator that turns a sorted `Vec<(timeCode, Value)>` and a
//! query time into a single resolved [`Value`]. Mirrors the C++
//! `UsdAttribute::Get(time)` surface: one entry point, one set of
//! type-aware rules, used by every consumer that wants a value at a
//! specific point in time.
//!
//! Two stage-level modes exist (spec §12.5):
//!
//! - [`InterpolationType::Held`]: the value of the nearest *previous*
//!   authored sample. Held at both ends (queries before the first
//!   sample return the first value; queries after the last return
//!   the last).
//! - [`InterpolationType::Linear`]: component-wise lerp for the
//!   numeric, matrix, and vector types in AOUSD §12.5.2 and their
//!   `VtArray` variants. Quaternion types (`Quath` / `Quatf` /
//!   `Quatd`) interpolate via spherical linear interpolation per
//!   the spec. Past the last sample, or for types that don't support
//!   linear (e.g. tokens, strings, arrays whose bracketing lengths
//!   differ), behaviour falls back to held.
//!
//! When the bracketing samples include a [`Value::ValueBlock`] or
//! [`Value::None`], evaluation returns `None` — the spec semantics
//! for a "blocked" sample.

use crate::gf;
use crate::sdf::Value;

/// Stage-level interpolation mode for time-sampled attributes.
///
/// Per AOUSD §12.5: when no mode is specified at the stage level,
/// the default is [`InterpolationType::Linear`]. C++ OpenUSD ships
/// the equivalent default through `UsdStage::SetInterpolationType`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InterpolationType {
    /// Held interpolation — value of the nearest previous authored
    /// sample, held at both ends.
    Held,
    /// Linear interpolation for spec-supported types; held otherwise.
    #[default]
    Linear,
}

/// Evaluate a sorted `(timeCode, Value)` sample list at `time` under
/// the requested interpolation `mode`.
///
/// `samples` MUST be sorted ascending by time code — `usdc` and
/// `usda` readers both produce them in that order. Returns `None`
/// when the list is empty or when the bracketing samples encode a
/// blocked value (`Value::ValueBlock` / `Value::None`).
pub fn evaluate(samples: &[(f64, Value)], time: f64, mode: InterpolationType) -> Option<Value> {
    if samples.is_empty() {
        return None;
    }
    let (first_t, first_v) = &samples[0];
    if time <= *first_t {
        return clean(first_v.clone());
    }
    let (last_t, last_v) = samples.last().unwrap();
    if time >= *last_t {
        return clean(last_v.clone());
    }

    // `samples` is sorted; locate the bracketing pair.
    let idx = samples.binary_search_by(|(t, _)| t.partial_cmp(&time).unwrap_or(std::cmp::Ordering::Equal));
    let (lo, hi) = match idx {
        Ok(i) => return clean(samples[i].1.clone()),
        Err(i) => (i - 1, i),
    };
    let (t_lo, v_lo) = &samples[lo];
    let (t_hi, v_hi) = &samples[hi];

    // Blocked-sample fallthrough applies regardless of mode.
    if is_blocked(v_lo) || is_blocked(v_hi) {
        return None;
    }

    match mode {
        InterpolationType::Held => clean(v_lo.clone()),
        InterpolationType::Linear => {
            let t = (time - t_lo) / (t_hi - t_lo);
            lerp_value(v_lo, v_hi, t).or_else(|| clean(v_lo.clone()))
        }
    }
}

fn is_blocked(v: &Value) -> bool {
    matches!(v, Value::ValueBlock | Value::None)
}

/// Filter out blocked sentinels at the read boundary so callers can
/// treat the return shape as "Some(real value) or no value".
fn clean(v: Value) -> Option<Value> {
    if is_blocked(&v) {
        None
    } else {
        Some(v)
    }
}

/// Component-wise lerp between two authored samples. Returns `None`
/// when `(a, b)` aren't the same linear-interpolatable type — the
/// caller then falls back to held. The local alias `V` avoids
/// `use Value::*` (which would shadow `Option::None` with the
/// `Value::None` variant in `match` arms).
///
/// `t` is f64 throughout; f32-sample paths narrow once at the call
/// site so we don't double-cast f64 → f32 → f64.
fn lerp_value(a: &Value, b: &Value, t: f64) -> Option<Value> {
    use crate::sdf::Value as V;
    let t32 = t as f32;
    Some(match (a, b) {
        (V::Half(x), V::Half(y)) => V::Half(gf::lerp_half(*x, *y, t32)),
        (V::Float(x), V::Float(y)) => V::Float(gf::lerp(*x, *y, t32)),
        (V::Double(x), V::Double(y)) => V::Double(gf::lerp(*x, *y, t)),
        (V::TimeCode(x), V::TimeCode(y)) => V::TimeCode(gf::lerp(x.0, y.0, t).into()),

        (V::Matrix2d(x), V::Matrix2d(y)) => V::Matrix2d(x.lerp(*y, t)),
        (V::Matrix3d(x), V::Matrix3d(y)) => V::Matrix3d(x.lerp(*y, t)),
        (V::Matrix4d(x), V::Matrix4d(y)) => V::Matrix4d(x.lerp(*y, t)),

        (V::Vec2h(x), V::Vec2h(y)) => V::Vec2h(x.lerp(*y, t32)),
        (V::Vec2f(x), V::Vec2f(y)) => V::Vec2f(x.lerp(*y, t32)),
        (V::Vec2d(x), V::Vec2d(y)) => V::Vec2d(x.lerp(*y, t)),
        (V::Vec3h(x), V::Vec3h(y)) => V::Vec3h(x.lerp(*y, t32)),
        (V::Vec3f(x), V::Vec3f(y)) => V::Vec3f(x.lerp(*y, t32)),
        (V::Vec3d(x), V::Vec3d(y)) => V::Vec3d(x.lerp(*y, t)),
        (V::Vec4h(x), V::Vec4h(y)) => V::Vec4h(x.lerp(*y, t32)),
        (V::Vec4f(x), V::Vec4f(y)) => V::Vec4f(x.lerp(*y, t32)),
        (V::Vec4d(x), V::Vec4d(y)) => V::Vec4d(x.lerp(*y, t)),

        (V::Quath(x), V::Quath(y)) => V::Quath(x.slerp(*y, t)),
        (V::Quatf(x), V::Quatf(y)) => V::Quatf(x.slerp(*y, t)),
        (V::Quatd(x), V::Quatd(y)) => V::Quatd(x.slerp(*y, t)),

        // Array (VtArray) variants. Per C++: bracketing samples must
        // agree on length, otherwise fall back to held.
        (V::HalfVec(x), V::HalfVec(y)) if x.len() == y.len() => {
            V::HalfVec(x.iter().zip(y).map(|(a, b)| gf::lerp_half(*a, *b, t32)).collect())
        }
        (V::FloatVec(x), V::FloatVec(y)) if x.len() == y.len() => {
            V::FloatVec(x.iter().zip(y).map(|(a, b)| gf::lerp(*a, *b, t32)).collect())
        }
        (V::DoubleVec(x), V::DoubleVec(y)) if x.len() == y.len() => {
            V::DoubleVec(x.iter().zip(y).map(|(a, b)| gf::lerp(*a, *b, t)).collect())
        }
        (V::TimeCodeVec(x), V::TimeCodeVec(y)) if x.len() == y.len() => {
            V::TimeCodeVec(x.iter().zip(y).map(|(a, b)| gf::lerp(a.0, b.0, t).into()).collect())
        }

        (V::Matrix2dVec(x), V::Matrix2dVec(y)) if x.len() == y.len() => {
            V::Matrix2dVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t)).collect())
        }
        (V::Matrix3dVec(x), V::Matrix3dVec(y)) if x.len() == y.len() => {
            V::Matrix3dVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t)).collect())
        }
        (V::Matrix4dVec(x), V::Matrix4dVec(y)) if x.len() == y.len() => {
            V::Matrix4dVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t)).collect())
        }

        (V::Vec2hVec(x), V::Vec2hVec(y)) if x.len() == y.len() => {
            V::Vec2hVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t32)).collect())
        }
        (V::Vec2fVec(x), V::Vec2fVec(y)) if x.len() == y.len() => {
            V::Vec2fVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t32)).collect())
        }
        (V::Vec2dVec(x), V::Vec2dVec(y)) if x.len() == y.len() => {
            V::Vec2dVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t)).collect())
        }
        (V::Vec3hVec(x), V::Vec3hVec(y)) if x.len() == y.len() => {
            V::Vec3hVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t32)).collect())
        }
        (V::Vec3fVec(x), V::Vec3fVec(y)) if x.len() == y.len() => {
            V::Vec3fVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t32)).collect())
        }
        (V::Vec3dVec(x), V::Vec3dVec(y)) if x.len() == y.len() => {
            V::Vec3dVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t)).collect())
        }
        (V::Vec4hVec(x), V::Vec4hVec(y)) if x.len() == y.len() => {
            V::Vec4hVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t32)).collect())
        }
        (V::Vec4fVec(x), V::Vec4fVec(y)) if x.len() == y.len() => {
            V::Vec4fVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t32)).collect())
        }
        (V::Vec4dVec(x), V::Vec4dVec(y)) if x.len() == y.len() => {
            V::Vec4dVec(x.iter().zip(y).map(|(a, b)| a.lerp(*b, t)).collect())
        }

        (V::QuathVec(x), V::QuathVec(y)) if x.len() == y.len() => {
            V::QuathVec(x.iter().zip(y).map(|(a, b)| a.slerp(*b, t)).collect())
        }
        (V::QuatfVec(x), V::QuatfVec(y)) if x.len() == y.len() => {
            V::QuatfVec(x.iter().zip(y).map(|(a, b)| a.slerp(*b, t)).collect())
        }
        (V::QuatdVec(x), V::QuatdVec(y)) if x.len() == y.len() => {
            V::QuatdVec(x.iter().zip(y).map(|(a, b)| a.slerp(*b, t)).collect())
        }

        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn samples_f64(pairs: &[(f64, f64)]) -> Vec<(f64, Value)> {
        pairs.iter().map(|(t, v)| (*t, Value::Double(*v))).collect()
    }

    #[test]
    fn empty_samples_return_none() {
        assert!(evaluate(&[], 0.0, InterpolationType::Linear).is_none());
        assert!(evaluate(&[], 0.0, InterpolationType::Held).is_none());
    }

    #[test]
    fn before_first_clamps_to_first() {
        let s = samples_f64(&[(10.0, 1.0), (20.0, 2.0)]);
        assert_eq!(evaluate(&s, 0.0, InterpolationType::Linear), Some(Value::Double(1.0)));
        assert_eq!(evaluate(&s, 0.0, InterpolationType::Held), Some(Value::Double(1.0)));
    }

    #[test]
    fn after_last_clamps_to_last() {
        let s = samples_f64(&[(10.0, 1.0), (20.0, 2.0)]);
        assert_eq!(evaluate(&s, 100.0, InterpolationType::Linear), Some(Value::Double(2.0)));
        assert_eq!(evaluate(&s, 100.0, InterpolationType::Held), Some(Value::Double(2.0)));
    }

    #[test]
    fn linear_double_lerps() {
        let s = samples_f64(&[(0.0, 0.0), (10.0, 20.0)]);
        assert_eq!(evaluate(&s, 5.0, InterpolationType::Linear), Some(Value::Double(10.0)));
    }

    #[test]
    fn held_returns_previous_sample() {
        let s = samples_f64(&[(0.0, 0.0), (10.0, 20.0)]);
        // At t=5 in Held mode, we get the value at t=0.
        assert_eq!(evaluate(&s, 5.0, InterpolationType::Held), Some(Value::Double(0.0)));
    }

    #[test]
    fn linear_unsupported_type_falls_back_to_held() {
        // String is not in the linear-supported set per §12.5.2.
        let s = vec![(0.0, Value::String("a".into())), (10.0, Value::String("b".into()))];
        assert_eq!(
            evaluate(&s, 5.0, InterpolationType::Linear),
            Some(Value::String("a".into()))
        );
    }

    #[test]
    fn linear_blocked_sample_returns_none() {
        let s = vec![(0.0, Value::Double(1.0)), (10.0, Value::ValueBlock)];
        assert_eq!(evaluate(&s, 5.0, InterpolationType::Linear), None);
        // At t == 10 exactly, the sample IS the block — return None.
        assert_eq!(evaluate(&s, 10.0, InterpolationType::Linear), None);
    }

    #[test]
    fn linear_vec3f_lerps_componentwise() {
        let s = vec![
            (0.0, Value::vec3f(0.0_f32, 0.0, 0.0)),
            (10.0, Value::vec3f(10.0_f32, 20.0, 30.0)),
        ];
        assert_eq!(
            evaluate(&s, 5.0, InterpolationType::Linear),
            Some(Value::vec3f(5.0_f32, 10.0, 15.0))
        );
    }

    #[test]
    fn linear_matrix4d_lerps_componentwise() {
        let mut a = [0.0f64; 16];
        let mut b = [0.0f64; 16];
        a[0] = 1.0;
        b[0] = 3.0;
        let s = vec![
            (0.0, Value::Matrix4d(gf::Matrix4d(a))),
            (10.0, Value::Matrix4d(gf::Matrix4d(b))),
        ];
        let out = evaluate(&s, 5.0, InterpolationType::Linear).unwrap();
        if let Value::Matrix4d(m) = out {
            assert!((m[(0, 0)] - 2.0).abs() < 1e-9);
        } else {
            panic!("expected Matrix4d, got {out:?}");
        }
    }

    #[test]
    fn linear_vec3f_array_lerps_per_element() {
        let s = vec![
            (
                0.0,
                Value::Vec3fVec(vec![gf::vec3f(0.0, 0.0, 0.0), gf::vec3f(10.0, 0.0, 0.0)]),
            ),
            (
                10.0,
                Value::Vec3fVec(vec![gf::vec3f(10.0, 0.0, 0.0), gf::vec3f(10.0, 20.0, 0.0)]),
            ),
        ];
        let out = evaluate(&s, 5.0, InterpolationType::Linear).unwrap();
        assert_eq!(
            out,
            Value::Vec3fVec(vec![gf::vec3f(5.0, 0.0, 0.0), gf::vec3f(10.0, 10.0, 0.0)])
        );
    }

    #[test]
    fn linear_quatf_array_slerps_per_element() {
        let s = vec![
            (0.0, Value::QuatfVec(vec![gf::quatf(1.0, 0.0, 0.0, 0.0)])),
            (10.0, Value::QuatfVec(vec![gf::quatf(0.0, 1.0, 0.0, 0.0)])),
        ];
        let out = evaluate(&s, 5.0, InterpolationType::Linear).unwrap();
        if let Value::QuatfVec(v) = out {
            let expected_w = std::f32::consts::FRAC_PI_4.cos();
            let expected_x = std::f32::consts::FRAC_PI_4.sin();
            assert!((v[0].w - expected_w).abs() < 1e-5);
            assert!((v[0].x - expected_x).abs() < 1e-5);
        } else {
            panic!("expected QuatfVec, got {out:?}");
        }
    }

    #[test]
    fn linear_array_length_mismatch_falls_back_to_held() {
        // Spec: when bracketing arrays differ in length, linear is
        // undefined; behaviour matches Held (return the previous sample).
        let s = vec![
            (0.0, Value::FloatVec(vec![1.0, 2.0, 3.0])),
            (10.0, Value::FloatVec(vec![4.0, 5.0])),
        ];
        let out = evaluate(&s, 5.0, InterpolationType::Linear).unwrap();
        assert_eq!(out, Value::FloatVec(vec![1.0, 2.0, 3.0]));
    }

    #[test]
    fn middle_bracket() {
        // Three samples means binary_search_by lands inside the list
        // rather than at an edge. At t=15 the bracketing pair is the
        // middle one (10→20), so we expect 25.0 (midpoint of 20 and 30).
        let s = samples_f64(&[(0.0, 0.0), (10.0, 20.0), (20.0, 30.0)]);
        assert_eq!(evaluate(&s, 15.0, InterpolationType::Linear), Some(Value::Double(25.0)));
        // And held mode returns the lower bracket of that pair.
        assert_eq!(evaluate(&s, 15.0, InterpolationType::Held), Some(Value::Double(20.0)));
    }

    #[test]
    fn exact_time_hit() {
        // Querying at an interior sample time hits binary_search_by's
        // `Ok(i)` branch — should return that sample exactly, not lerp.
        let s = samples_f64(&[(0.0, 0.0), (10.0, 20.0), (20.0, 30.0)]);
        assert_eq!(evaluate(&s, 10.0, InterpolationType::Linear), Some(Value::Double(20.0)));
        assert_eq!(evaluate(&s, 10.0, InterpolationType::Held), Some(Value::Double(20.0)));
    }
}
