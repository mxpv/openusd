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

use crate::math::{
    mat4_from_quat, mat4_inverse, mat4_mul, mat4_rotation_x, mat4_rotation_y, mat4_rotation_z, mat4_scale,
    mat4_translation, IDENTITY_MAT4,
};
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
/// `!resetXformStack!` is only meaningful at index 0; the leading
/// sentinel is skipped here (callers honour it via
/// [`resets_xform_stack`]), while a non-leading occurrence surfaces
/// as an error rather than being silently dropped.
///
/// Op values are read through [`Stage::value_at`] so per-op
/// `timeSamples` interpolate per AOUSD §12.5.
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
        "translate" => mat4_translation(value_to_vec3_f64(&raw).unwrap_or([0.0, 0.0, 0.0])),
        "translateX" => mat4_translation([value_to_scalar_f64(&raw).unwrap_or(0.0), 0.0, 0.0]),
        "translateY" => mat4_translation([0.0, value_to_scalar_f64(&raw).unwrap_or(0.0), 0.0]),
        "translateZ" => mat4_translation([0.0, 0.0, value_to_scalar_f64(&raw).unwrap_or(0.0)]),
        "scale" => mat4_scale(value_to_vec3_f64(&raw).unwrap_or([1.0, 1.0, 1.0])),
        "scaleX" => mat4_scale([value_to_scalar_f64(&raw).unwrap_or(1.0), 1.0, 1.0]),
        "scaleY" => mat4_scale([1.0, value_to_scalar_f64(&raw).unwrap_or(1.0), 1.0]),
        "scaleZ" => mat4_scale([1.0, 1.0, value_to_scalar_f64(&raw).unwrap_or(1.0)]),
        "orient" => mat4_from_quat(value_to_quat_wxyz(&raw).unwrap_or([1.0, 0.0, 0.0, 0.0])),
        // Rotation ops are kept in f64 end-to-end. xformOp:rotateX etc.
        // can be authored as either `float` or `double` per the
        // UsdGeomXformOp precision system; reading via f32 would
        // silently truncate the double-authored case before the trig
        // math runs.
        "rotateX" => mat4_rotation_x(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateY" => mat4_rotation_y(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateZ" => mat4_rotation_z(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateXYZ" | "rotateYXZ" | "rotateZXY" | "rotateXZY" | "rotateYZX" | "rotateZYX" => {
            let v = value_to_vec3_f64(&raw).unwrap_or([0.0, 0.0, 0.0]);
            let rx = mat4_rotation_x(v[0].to_radians());
            let ry = mat4_rotation_y(v[1].to_radians());
            let rz = mat4_rotation_z(v[2].to_radians());
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

fn value_to_quat_wxyz(v: &Value) -> Option<[f64; 4]> {
    match v {
        Value::Quatd(q) => Some(*q),
        Value::Quatf(q) => Some([q[0] as f64, q[1] as f64, q[2] as f64, q[3] as f64]),
        Value::Quath(q) => Some([
            q[0].to_f32() as f64,
            q[1].to_f32() as f64,
            q[2].to_f32() as f64,
            q[3].to_f32() as f64,
        ]),
        _ => None,
    }
}
