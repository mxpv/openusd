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
        (V::Half(x), V::Half(y)) => V::Half(half::f16::from_f32(lerp_f32(x.to_f32(), y.to_f32(), t32))),
        (V::Float(x), V::Float(y)) => V::Float(lerp_f32(*x, *y, t32)),
        (V::Double(x), V::Double(y)) => V::Double(lerp_f64(*x, *y, t)),
        (V::TimeCode(x), V::TimeCode(y)) => V::TimeCode(lerp_f64(*x, *y, t)),

        (V::Matrix2d(x), V::Matrix2d(y)) => V::Matrix2d(lerp_array_f64::<4>(x, y, t)),
        (V::Matrix3d(x), V::Matrix3d(y)) => V::Matrix3d(lerp_array_f64::<9>(x, y, t)),
        (V::Matrix4d(x), V::Matrix4d(y)) => V::Matrix4d(lerp_array_f64::<16>(x, y, t)),

        (V::Vec2h(x), V::Vec2h(y)) => V::Vec2h(lerp_half_array::<2>(x, y, t32)),
        (V::Vec2f(x), V::Vec2f(y)) => V::Vec2f(lerp_array_f32::<2>(x, y, t32)),
        (V::Vec2d(x), V::Vec2d(y)) => V::Vec2d(lerp_array_f64::<2>(x, y, t)),
        (V::Vec3h(x), V::Vec3h(y)) => V::Vec3h(lerp_half_array::<3>(x, y, t32)),
        (V::Vec3f(x), V::Vec3f(y)) => V::Vec3f(lerp_array_f32::<3>(x, y, t32)),
        (V::Vec3d(x), V::Vec3d(y)) => V::Vec3d(lerp_array_f64::<3>(x, y, t)),
        (V::Vec4h(x), V::Vec4h(y)) => V::Vec4h(lerp_half_array::<4>(x, y, t32)),
        (V::Vec4f(x), V::Vec4f(y)) => V::Vec4f(lerp_array_f32::<4>(x, y, t32)),
        (V::Vec4d(x), V::Vec4d(y)) => V::Vec4d(lerp_array_f64::<4>(x, y, t)),

        (V::Quath(x), V::Quath(y)) => V::Quath(slerp_half(x, y, t)),
        (V::Quatf(x), V::Quatf(y)) => V::Quatf(slerp_quatf(x, y, t)),
        (V::Quatd(x), V::Quatd(y)) => V::Quatd(slerp_quatd(x, y, t)),

        // Array (VtArray) variants. Per C++: bracketing samples must
        // agree on length, otherwise fall back to held.
        (V::HalfVec(x), V::HalfVec(y)) if x.len() == y.len() => V::HalfVec(
            x.iter()
                .zip(y)
                .map(|(a, b)| half::f16::from_f32(lerp_f32(a.to_f32(), b.to_f32(), t32)))
                .collect(),
        ),
        (V::FloatVec(x), V::FloatVec(y)) if x.len() == y.len() => {
            V::FloatVec(x.iter().zip(y).map(|(a, b)| lerp_f32(*a, *b, t32)).collect())
        }
        (V::DoubleVec(x), V::DoubleVec(y)) if x.len() == y.len() => {
            V::DoubleVec(x.iter().zip(y).map(|(a, b)| lerp_f64(*a, *b, t)).collect())
        }
        (V::TimeCodeVec(x), V::TimeCodeVec(y)) if x.len() == y.len() => {
            V::TimeCodeVec(x.iter().zip(y).map(|(a, b)| lerp_f64(*a, *b, t)).collect())
        }

        (V::Matrix2dVec(x), V::Matrix2dVec(y)) if x.len() == y.len() => {
            V::Matrix2dVec(x.iter().zip(y).map(|(a, b)| lerp_array_f64::<4>(a, b, t)).collect())
        }
        (V::Matrix3dVec(x), V::Matrix3dVec(y)) if x.len() == y.len() => {
            V::Matrix3dVec(x.iter().zip(y).map(|(a, b)| lerp_array_f64::<9>(a, b, t)).collect())
        }
        (V::Matrix4dVec(x), V::Matrix4dVec(y)) if x.len() == y.len() => {
            V::Matrix4dVec(x.iter().zip(y).map(|(a, b)| lerp_array_f64::<16>(a, b, t)).collect())
        }

        (V::Vec2hVec(x), V::Vec2hVec(y)) if x.len() == y.len() => {
            V::Vec2hVec(x.iter().zip(y).map(|(a, b)| lerp_half_array::<2>(a, b, t32)).collect())
        }
        (V::Vec2fVec(x), V::Vec2fVec(y)) if x.len() == y.len() => {
            V::Vec2fVec(x.iter().zip(y).map(|(a, b)| lerp_array_f32::<2>(a, b, t32)).collect())
        }
        (V::Vec2dVec(x), V::Vec2dVec(y)) if x.len() == y.len() => {
            V::Vec2dVec(x.iter().zip(y).map(|(a, b)| lerp_array_f64::<2>(a, b, t)).collect())
        }
        (V::Vec3hVec(x), V::Vec3hVec(y)) if x.len() == y.len() => {
            V::Vec3hVec(x.iter().zip(y).map(|(a, b)| lerp_half_array::<3>(a, b, t32)).collect())
        }
        (V::Vec3fVec(x), V::Vec3fVec(y)) if x.len() == y.len() => {
            V::Vec3fVec(x.iter().zip(y).map(|(a, b)| lerp_array_f32::<3>(a, b, t32)).collect())
        }
        (V::Vec3dVec(x), V::Vec3dVec(y)) if x.len() == y.len() => {
            V::Vec3dVec(x.iter().zip(y).map(|(a, b)| lerp_array_f64::<3>(a, b, t)).collect())
        }
        (V::Vec4hVec(x), V::Vec4hVec(y)) if x.len() == y.len() => {
            V::Vec4hVec(x.iter().zip(y).map(|(a, b)| lerp_half_array::<4>(a, b, t32)).collect())
        }
        (V::Vec4fVec(x), V::Vec4fVec(y)) if x.len() == y.len() => {
            V::Vec4fVec(x.iter().zip(y).map(|(a, b)| lerp_array_f32::<4>(a, b, t32)).collect())
        }
        (V::Vec4dVec(x), V::Vec4dVec(y)) if x.len() == y.len() => {
            V::Vec4dVec(x.iter().zip(y).map(|(a, b)| lerp_array_f64::<4>(a, b, t)).collect())
        }

        (V::QuathVec(x), V::QuathVec(y)) if x.len() == y.len() => {
            V::QuathVec(x.iter().zip(y).map(|(a, b)| slerp_half(a, b, t)).collect())
        }
        (V::QuatfVec(x), V::QuatfVec(y)) if x.len() == y.len() => {
            V::QuatfVec(x.iter().zip(y).map(|(a, b)| slerp_quatf(a, b, t)).collect())
        }
        (V::QuatdVec(x), V::QuatdVec(y)) if x.len() == y.len() => {
            V::QuatdVec(x.iter().zip(y).map(|(a, b)| slerp_quatd(a, b, t)).collect())
        }

        _ => return None,
    })
}

fn lerp_f32(a: f32, b: f32, t: f32) -> f32 {
    a + (b - a) * t
}

fn lerp_f64(a: f64, b: f64, t: f64) -> f64 {
    a + (b - a) * t
}

fn lerp_array_f32<const N: usize>(a: &[f32; N], b: &[f32; N], t: f32) -> [f32; N] {
    let mut out = [0.0f32; N];
    for i in 0..N {
        out[i] = lerp_f32(a[i], b[i], t);
    }
    out
}

fn lerp_array_f64<const N: usize>(a: &[f64; N], b: &[f64; N], t: f64) -> [f64; N] {
    let mut out = [0.0f64; N];
    for i in 0..N {
        out[i] = lerp_f64(a[i], b[i], t);
    }
    out
}

fn lerp_half_array<const N: usize>(a: &[half::f16; N], b: &[half::f16; N], t: f32) -> [half::f16; N] {
    let mut out = [half::f16::ZERO; N];
    for i in 0..N {
        out[i] = half::f16::from_f32(lerp_f32(a[i].to_f32(), b[i].to_f32(), t));
    }
    out
}

// ──────────────────────────────────────────────────────────────────
// Quaternion slerp — spec §12.5.2 mandates slerp for quat types.
// USD's quaternion layout is (w, x, y, z) per the textual encoding;
// the slerp math below treats element [0] as the real part.
// ──────────────────────────────────────────────────────────────────

fn slerp_quatf(a: &[f32; 4], b: &[f32; 4], t: f64) -> [f32; 4] {
    let aa = [a[0] as f64, a[1] as f64, a[2] as f64, a[3] as f64];
    let bb = [b[0] as f64, b[1] as f64, b[2] as f64, b[3] as f64];
    let out = slerp_f64(&aa, &bb, t);
    [out[0] as f32, out[1] as f32, out[2] as f32, out[3] as f32]
}

fn slerp_quatd(a: &[f64; 4], b: &[f64; 4], t: f64) -> [f64; 4] {
    slerp_f64(a, b, t)
}

fn slerp_half(a: &[half::f16; 4], b: &[half::f16; 4], t: f64) -> [half::f16; 4] {
    let aa = [
        a[0].to_f32() as f64,
        a[1].to_f32() as f64,
        a[2].to_f32() as f64,
        a[3].to_f32() as f64,
    ];
    let bb = [
        b[0].to_f32() as f64,
        b[1].to_f32() as f64,
        b[2].to_f32() as f64,
        b[3].to_f32() as f64,
    ];
    let out = slerp_f64(&aa, &bb, t);
    [
        half::f16::from_f32(out[0] as f32),
        half::f16::from_f32(out[1] as f32),
        half::f16::from_f32(out[2] as f32),
        half::f16::from_f32(out[3] as f32),
    ]
}

/// Quaternion slerp in `(w, x, y, z)` order. Chooses the
/// shorter great-circle arc, and falls back to nlerp when the two
/// quaternions are within numerical noise of each other to avoid
/// the sin(0)/0 singularity.
fn slerp_f64(a: &[f64; 4], b: &[f64; 4], t: f64) -> [f64; 4] {
    let mut dot = a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3];
    let sign = if dot < 0.0 { -1.0 } else { 1.0 };
    dot = dot.abs();
    if dot > 0.9995 {
        // Quaternions are colinear — lerp + normalise is stable and
        // visually indistinguishable from slerp at this range.
        return normalise_quat(&[
            a[0] + (sign * b[0] - a[0]) * t,
            a[1] + (sign * b[1] - a[1]) * t,
            a[2] + (sign * b[2] - a[2]) * t,
            a[3] + (sign * b[3] - a[3]) * t,
        ]);
    }
    let theta = dot.acos();
    let sin_theta = theta.sin();
    let s_a = ((1.0 - t) * theta).sin() / sin_theta;
    let s_b = (t * theta).sin() / sin_theta * sign;
    [
        a[0] * s_a + b[0] * s_b,
        a[1] * s_a + b[1] * s_b,
        a[2] * s_a + b[2] * s_b,
        a[3] * s_a + b[3] * s_b,
    ]
}

fn normalise_quat(q: &[f64; 4]) -> [f64; 4] {
    let mag = (q[0] * q[0] + q[1] * q[1] + q[2] * q[2] + q[3] * q[3]).sqrt();
    if mag == 0.0 {
        return [1.0, 0.0, 0.0, 0.0];
    }
    [q[0] / mag, q[1] / mag, q[2] / mag, q[3] / mag]
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
            (0.0, Value::Vec3f([0.0, 0.0, 0.0])),
            (10.0, Value::Vec3f([10.0, 20.0, 30.0])),
        ];
        assert_eq!(
            evaluate(&s, 5.0, InterpolationType::Linear),
            Some(Value::Vec3f([5.0, 10.0, 15.0]))
        );
    }

    #[test]
    fn linear_matrix4d_lerps_componentwise() {
        let mut a = [0.0f64; 16];
        let mut b = [0.0f64; 16];
        a[0] = 1.0;
        b[0] = 3.0;
        let s = vec![(0.0, Value::Matrix4d(a)), (10.0, Value::Matrix4d(b))];
        let out = evaluate(&s, 5.0, InterpolationType::Linear).unwrap();
        if let Value::Matrix4d(m) = out {
            assert!((m[0] - 2.0).abs() < 1e-9);
        } else {
            panic!("expected Matrix4d, got {out:?}");
        }
    }

    #[test]
    fn slerp_quatf_90deg_at_t_half() {
        // Identity → 180° about +X. At t=0.5 the result should be a
        // 90° rotation about +X: (w=cos(45°), x=sin(45°), 0, 0).
        let id = [1.0f32, 0.0, 0.0, 0.0];
        let half_turn = [0.0f32, 1.0, 0.0, 0.0];
        let out = slerp_quatf(&id, &half_turn, 0.5);
        let expected_w = (std::f32::consts::FRAC_PI_4).cos();
        let expected_x = (std::f32::consts::FRAC_PI_4).sin();
        assert!(
            (out[0] - expected_w).abs() < 1e-5,
            "w: got {} expected {}",
            out[0],
            expected_w
        );
        assert!(
            (out[1] - expected_x).abs() < 1e-5,
            "x: got {} expected {}",
            out[1],
            expected_x
        );
        assert!(out[2].abs() < 1e-5);
        assert!(out[3].abs() < 1e-5);
    }

    #[test]
    fn linear_vec3f_array_lerps_per_element() {
        let s = vec![
            (0.0, Value::Vec3fVec(vec![[0.0, 0.0, 0.0], [10.0, 0.0, 0.0]])),
            (10.0, Value::Vec3fVec(vec![[10.0, 0.0, 0.0], [10.0, 20.0, 0.0]])),
        ];
        let out = evaluate(&s, 5.0, InterpolationType::Linear).unwrap();
        assert_eq!(out, Value::Vec3fVec(vec![[5.0, 0.0, 0.0], [10.0, 10.0, 0.0]]));
    }

    #[test]
    fn linear_quatf_array_slerps_per_element() {
        let s = vec![
            (0.0, Value::QuatfVec(vec![[1.0, 0.0, 0.0, 0.0]])),
            (10.0, Value::QuatfVec(vec![[0.0, 1.0, 0.0, 0.0]])),
        ];
        let out = evaluate(&s, 5.0, InterpolationType::Linear).unwrap();
        if let Value::QuatfVec(v) = out {
            let expected_w = std::f32::consts::FRAC_PI_4.cos();
            let expected_x = std::f32::consts::FRAC_PI_4.sin();
            assert!((v[0][0] - expected_w).abs() < 1e-5);
            assert!((v[0][1] - expected_x).abs() < 1e-5);
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

    #[test]
    fn slerp_takes_shorter_arc_when_dot_is_negative() {
        // q and -q represent the same rotation; slerp should detect
        // the sign flip and produce a result close to identity, not
        // the long way around.
        let id = [1.0f64, 0.0, 0.0, 0.0];
        let neg_id = [-1.0f64, 0.0, 0.0, 0.0];
        let out = slerp_f64(&id, &neg_id, 0.5);
        // Result should still represent identity (up to sign).
        assert!((out[0].abs() - 1.0).abs() < 1e-9);
    }
}
