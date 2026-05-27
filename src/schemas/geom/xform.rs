//! `UsdGeomXformable` — the `xformOpOrder` mechanism.
//!
//! USD prims that are `Xformable` carry their local transform as an
//! ordered stack of operations rather than a single matrix. The
//! `xformOpOrder` token array names the operations to apply, in
//! order: the first entry is the *most local* (innermost in the
//! matrix product), the last is outermost. Each named op is its own
//! attribute under the `xformOp:` namespace.
//!
//! This module composes that stack into a single 4×4 local-to-parent
//! matrix, honouring two special tokens:
//!
//! - `!invert!<op>` — invert the op's value before composing.
//! - `!resetXformStack!` — the prim's local transform does NOT
//!   inherit from its parent. Surfaced separately via
//!   [`resets_xform_stack`].
//!
//! Per-op values flow through [`Stage::value_at`], so any xformOp
//! authored with `timeSamples` interpolates per AOUSD §12.5 (linear
//! by default, with slerp on `xformOp:orient`).

use anyhow::Result;

use crate::math::{mat4_inverse, mat4_mul, IDENTITY_MAT4};
use crate::sdf::{Path, Value};
use crate::usd::Stage;

const XFORM_OP_ORDER: &str = "xformOpOrder";
const TOKEN_INVERT_PREFIX: &str = "!invert!";
const TOKEN_RESET_XFORM_STACK: &str = "!resetXformStack!";
const XFORM_OP_NAMESPACE: &str = "xformOp:";

/// Read `xformOpOrder` on `prim` and flatten any list-op authoring
/// (some URDF→USD exporters emit `prepend xformOpOrder = [...]`
/// rather than a plain token vec). Returns `None` when no
/// `xformOpOrder` is authored.
pub fn read_xform_op_order(stage: &Stage, prim: &Path) -> Result<Option<Vec<String>>> {
    let attr = prim.append_property(XFORM_OP_ORDER)?;
    let raw = stage.field::<Value>(attr, "default")?;
    Ok(match raw {
        Some(Value::TokenVec(v) | Value::StringVec(v)) => Some(v),
        Some(Value::TokenListOp(op)) => Some(op.flatten()),
        Some(Value::StringListOp(op)) => Some(op.flatten()),
        _ => None,
    })
}

/// `true` when `prim` opts out of inheriting its parent's transform
/// by listing the `!resetXformStack!` sentinel as the first entry
/// of `xformOpOrder`. Per Pixar's docs the sentinel is only
/// meaningful at index 0; this reader checks accordingly.
pub fn resets_xform_stack(stage: &Stage, prim: &Path) -> Result<bool> {
    Ok(matches!(
        read_xform_op_order(stage, prim)?.as_deref().and_then(|s| s.first()),
        Some(s) if s == TOKEN_RESET_XFORM_STACK
    ))
}

/// Compose `xformOpOrder` into a single local-to-parent 4×4 matrix
/// at `time`. Returns [`IDENTITY_MAT4`] when the prim has no
/// `xformOpOrder` authored (the spec default — the prim's local
/// transform is identity).
///
/// `!invert!` ops contribute the inverse of the underlying value.
/// `!resetXformStack!` is skipped here; callers honour it via
/// [`resets_xform_stack`] when chaining to a parent's transform.
///
/// Op values are read through [`Stage::value_at`] so per-op
/// `timeSamples` interpolate per AOUSD §12.5.
///
/// `!resetXformStack!` is only meaningful as the first entry per the
/// UsdGeomXformable spec. A non-leading occurrence is malformed
/// authoring and surfaces as an error rather than being silently
/// skipped.
pub fn compute_local_to_parent_transform(stage: &Stage, prim: &Path, time: f64) -> Result<[f64; 16]> {
    let Some(order) = read_xform_op_order(stage, prim)? else {
        return Ok(IDENTITY_MAT4);
    };
    let mut m = IDENTITY_MAT4;
    for (i, op_name) in order.iter().enumerate() {
        if op_name == TOKEN_RESET_XFORM_STACK {
            if i == 0 {
                continue;
            }
            anyhow::bail!(
                "xformOpOrder on `{}`: `!resetXformStack!` is only valid at index 0, found at index {}",
                prim.as_str(),
                i,
            );
        }
        let op = build_op_matrix(stage, prim, op_name, time)?;
        // In USD's row-vector convention, the first listed op is the
        // most local — applied first to a point. With `v_out = v_in · M`
        // that means the cumulative matrix grows on the right:
        //   M = op1 · op2 · op3 · …
        m = mat4_mul(&m, &op);
    }
    Ok(m)
}

/// Build the 4×4 contribution of a single xformOp.
///
/// `op_name` is one entry from `xformOpOrder` — possibly with the
/// `!invert!` prefix. The remainder must be a fully-namespaced
/// `xformOp:…` attribute name as authored on the prim; that's how
/// `xformOpOrder` entries are spelled per the USD spec. The op's
/// kind (translate / scale / orient / rotateAXIS / rotateEULER /
/// transform) is parsed from the segment between `xformOp:` and the
/// first `:` suffix.
fn build_op_matrix(stage: &Stage, prim: &Path, op_name: &str, time: f64) -> Result<[f64; 16]> {
    let (inverted, base) = match op_name.strip_prefix(TOKEN_INVERT_PREFIX) {
        Some(stripped) => (true, stripped),
        None => (false, op_name),
    };

    let attr = prim.append_property(base)?;
    let raw = stage.value_at(attr, time)?;
    let Some(raw) = raw else {
        return Ok(IDENTITY_MAT4);
    };

    // Extract the op kind: strip the `xformOp:` namespace, then keep
    // everything before the first additional `:` (which is an
    // authoring-time suffix like `:scalePivot`).
    let after_ns = base.strip_prefix(XFORM_OP_NAMESPACE).unwrap_or(base);
    let kind = after_ns.split(':').next().unwrap_or(after_ns);

    let m = match kind {
        "translate" => translate_matrix(value_to_vec3f(&raw).unwrap_or([0.0, 0.0, 0.0])),
        "translateX" => translate_matrix([value_to_scalar_f32(&raw).unwrap_or(0.0), 0.0, 0.0]),
        "translateY" => translate_matrix([0.0, value_to_scalar_f32(&raw).unwrap_or(0.0), 0.0]),
        "translateZ" => translate_matrix([0.0, 0.0, value_to_scalar_f32(&raw).unwrap_or(0.0)]),
        "scale" => scale_matrix(value_to_vec3f(&raw).unwrap_or([1.0, 1.0, 1.0])),
        "scaleX" => scale_matrix([value_to_scalar_f32(&raw).unwrap_or(1.0), 1.0, 1.0]),
        "scaleY" => scale_matrix([1.0, value_to_scalar_f32(&raw).unwrap_or(1.0), 1.0]),
        "scaleZ" => scale_matrix([1.0, 1.0, value_to_scalar_f32(&raw).unwrap_or(1.0)]),
        "orient" => quat_to_matrix(value_to_quat_wxyz(&raw).unwrap_or([1.0, 0.0, 0.0, 0.0])),
        // Rotation ops are kept in f64 end-to-end. xformOp:rotateX etc.
        // can be authored as either `float` or `double` per the
        // UsdGeomXformOp precision system; reading via f32 would
        // silently truncate the double-authored case before the trig
        // math runs.
        "rotateX" => rotate_x_matrix(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateY" => rotate_y_matrix(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateZ" => rotate_z_matrix(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateXYZ" | "rotateYXZ" | "rotateZXY" | "rotateXZY" | "rotateYZX" | "rotateZYX" => {
            let v = value_to_vec3_f64(&raw).unwrap_or([0.0, 0.0, 0.0]);
            let rx = rotate_x_matrix(v[0].to_radians());
            let ry = rotate_y_matrix(v[1].to_radians());
            let rz = rotate_z_matrix(v[2].to_radians());
            // Apply axes in the order spelled by `kind` — `rotateXYZ`
            // means apply X first, then Y, then Z (per the Pixar spec).
            // In row-vector composition that's `Rx · Ry · Rz`.
            match kind {
                "rotateXYZ" => mat4_mul(&rx, &mat4_mul(&ry, &rz)),
                "rotateYXZ" => mat4_mul(&ry, &mat4_mul(&rx, &rz)),
                "rotateZXY" => mat4_mul(&rz, &mat4_mul(&rx, &ry)),
                "rotateXZY" => mat4_mul(&rx, &mat4_mul(&rz, &ry)),
                "rotateYZX" => mat4_mul(&ry, &mat4_mul(&rz, &rx)),
                "rotateZYX" => mat4_mul(&rz, &mat4_mul(&ry, &rx)),
                _ => unreachable!("kind guard above"),
            }
        }
        "transform" => match raw {
            Value::Matrix4d(m) => m,
            _ => IDENTITY_MAT4,
        },
        _ => IDENTITY_MAT4,
    };

    if inverted {
        mat4_inverse(&m).ok_or_else(|| anyhow::anyhow!("xformOp `{op_name}` matrix is singular and cannot be inverted"))
    } else {
        Ok(m)
    }
}

// ────────────────────────────────────────────────────────────────────────
// Row-major rotation / translation / scale builders.
// ────────────────────────────────────────────────────────────────────────

fn translate_matrix(t: [f32; 3]) -> [f64; 16] {
    let mut m = IDENTITY_MAT4;
    m[12] = t[0] as f64;
    m[13] = t[1] as f64;
    m[14] = t[2] as f64;
    m
}

fn scale_matrix(s: [f32; 3]) -> [f64; 16] {
    let mut m = IDENTITY_MAT4;
    m[0] = s[0] as f64;
    m[5] = s[1] as f64;
    m[10] = s[2] as f64;
    m
}

fn rotate_x_matrix(rad: f64) -> [f64; 16] {
    let (s, c) = rad.sin_cos();
    let mut m = IDENTITY_MAT4;
    m[5] = c;
    m[6] = s;
    m[9] = -s;
    m[10] = c;
    m
}

fn rotate_y_matrix(rad: f64) -> [f64; 16] {
    let (s, c) = rad.sin_cos();
    let mut m = IDENTITY_MAT4;
    m[0] = c;
    m[2] = -s;
    m[8] = s;
    m[10] = c;
    m
}

fn rotate_z_matrix(rad: f64) -> [f64; 16] {
    let (s, c) = rad.sin_cos();
    let mut m = IDENTITY_MAT4;
    m[0] = c;
    m[1] = s;
    m[4] = -s;
    m[5] = c;
    m
}

/// Convert a `(w, x, y, z)` quaternion to a row-major 4×4 rotation.
fn quat_to_matrix(q: [f32; 4]) -> [f64; 16] {
    let w = q[0] as f64;
    let x = q[1] as f64;
    let y = q[2] as f64;
    let z = q[3] as f64;
    let xx = x * x;
    let yy = y * y;
    let zz = z * z;
    let xy = x * y;
    let xz = x * z;
    let yz = y * z;
    let wx = w * x;
    let wy = w * y;
    let wz = w * z;
    [
        1.0 - 2.0 * (yy + zz),
        2.0 * (xy + wz),
        2.0 * (xz - wy),
        0.0,
        2.0 * (xy - wz),
        1.0 - 2.0 * (xx + zz),
        2.0 * (yz + wx),
        0.0,
        2.0 * (xz + wy),
        2.0 * (yz - wx),
        1.0 - 2.0 * (xx + yy),
        0.0,
        0.0,
        0.0,
        0.0,
        1.0,
    ]
}

fn value_to_vec3f(v: &Value) -> Option<[f32; 3]> {
    match v {
        Value::Vec3f(a) => Some(*a),
        Value::Vec3d(a) => Some([a[0] as f32, a[1] as f32, a[2] as f32]),
        Value::Vec3h(a) => Some([a[0].to_f32(), a[1].to_f32(), a[2].to_f32()]),
        _ => None,
    }
}

fn value_to_scalar_f32(v: &Value) -> Option<f32> {
    match v {
        Value::Float(f) => Some(*f),
        Value::Double(d) => Some(*d as f32),
        Value::Half(h) => Some(h.to_f32()),
        Value::Int(i) => Some(*i as f32),
        Value::Int64(i) => Some(*i as f32),
        _ => None,
    }
}

fn value_to_scalar_f64(v: &Value) -> Option<f64> {
    match v {
        Value::Double(d) => Some(*d),
        Value::Float(f) => Some(*f as f64),
        Value::Half(h) => Some(h.to_f32() as f64),
        Value::Int(i) => Some(*i as f64),
        Value::Int64(i) => Some(*i as f64),
        _ => None,
    }
}

fn value_to_vec3_f64(v: &Value) -> Option<[f64; 3]> {
    match v {
        Value::Vec3d(a) => Some(*a),
        Value::Vec3f(a) => Some([a[0] as f64, a[1] as f64, a[2] as f64]),
        Value::Vec3h(a) => Some([a[0].to_f32() as f64, a[1].to_f32() as f64, a[2].to_f32() as f64]),
        _ => None,
    }
}

fn value_to_quat_wxyz(v: &Value) -> Option<[f32; 4]> {
    match v {
        Value::Quatf(q) => Some(*q),
        Value::Quatd(q) => Some([q[0] as f32, q[1] as f32, q[2] as f32, q[3] as f32]),
        Value::Quath(q) => Some([q[0].to_f32(), q[1].to_f32(), q[2].to_f32(), q[3].to_f32()]),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::mat4_transform_point;

    #[test]
    fn translate_matrix_layout_matches_row_major() {
        let m = translate_matrix([5.0, -2.0, 7.0]);
        assert_eq!(&m[12..15], &[5.0, -2.0, 7.0]);
        let p = mat4_transform_point(&m, [1.0, 1.0, 1.0]);
        assert_eq!(p, [6.0, -1.0, 8.0]);
    }

    #[test]
    fn rotate_z_takes_x_to_y() {
        let m = rotate_z_matrix(std::f64::consts::FRAC_PI_2);
        let p = mat4_transform_point(&m, [1.0, 0.0, 0.0]);
        assert!((p[0]).abs() < 1e-6, "x: {}", p[0]);
        assert!((p[1] - 1.0).abs() < 1e-6, "y: {}", p[1]);
        assert!((p[2]).abs() < 1e-6);
    }

    #[test]
    fn rotate_y_takes_x_to_neg_z() {
        let m = rotate_y_matrix(std::f64::consts::FRAC_PI_2);
        let p = mat4_transform_point(&m, [1.0, 0.0, 0.0]);
        assert!((p[0]).abs() < 1e-6);
        assert!((p[1]).abs() < 1e-6);
        assert!((p[2] + 1.0).abs() < 1e-6, "z: {}", p[2]);
    }

    #[test]
    fn rotate_x_takes_y_to_z() {
        let m = rotate_x_matrix(std::f64::consts::FRAC_PI_2);
        let p = mat4_transform_point(&m, [0.0, 1.0, 0.0]);
        assert!((p[0]).abs() < 1e-6);
        assert!((p[1]).abs() < 1e-6);
        assert!((p[2] - 1.0).abs() < 1e-6, "z: {}", p[2]);
    }

    #[test]
    fn identity_quat_to_matrix_is_identity() {
        assert_eq!(quat_to_matrix([1.0, 0.0, 0.0, 0.0]), IDENTITY_MAT4);
    }

    #[test]
    fn quat_90_about_z_takes_x_to_y() {
        // q = (cos(45°), 0, 0, sin(45°)) = 90° about +Z.
        let h = std::f32::consts::FRAC_PI_4;
        let m = quat_to_matrix([h.cos(), 0.0, 0.0, h.sin()]);
        let p = mat4_transform_point(&m, [1.0, 0.0, 0.0]);
        assert!((p[0]).abs() < 1e-5);
        assert!((p[1] - 1.0).abs() < 1e-5);
        assert!((p[2]).abs() < 1e-5);
    }

    #[test]
    fn scale_matrix_layout_matches_row_major() {
        let m = scale_matrix([2.0, 3.0, 4.0]);
        let p = mat4_transform_point(&m, [1.0, 1.0, 1.0]);
        assert_eq!(p, [2.0, 3.0, 4.0]);
    }
}
