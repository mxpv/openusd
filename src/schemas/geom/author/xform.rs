//! `UsdGeomXformable` authoring — the `xformOpOrder` mechanism.
//!
//! Mirrors the reader in [`super::super::xform`]. Each setter writes
//! a single `xformOp:<kind>` attribute *and* appends its full
//! namespaced name to the prim's `xformOpOrder` token array, so the
//! reader recovers the same authored stack.
//!
//! Per Pixar's spec, the order of entries in `xformOpOrder` matches
//! the order ops are applied. The setters here preserve insertion
//! order — call `set_translate` then `set_rotate_y` then `set_scale`
//! to get the canonical T·R·S stack.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

const A_XFORM_OP_ORDER: &str = "xformOpOrder";
const NS_XFORM_OP: &str = "xformOp:";

/// Reset the `xformOpOrder` to the given sequence verbatim — replaces
/// any prior ordering. Useful when an importer wants exact control
/// over the stack rather than relying on the per-op append behaviour
/// of the [`set_*`] helpers below.
pub fn set_xform_op_order<I, S>(stage: &Stage, prim: &Path, order: I) -> Result<()>
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    let tokens: Vec<String> = order.into_iter().map(Into::into).collect();
    let attr = prim.append_property(A_XFORM_OP_ORDER)?;
    stage
        .create_attribute(attr, "token[]")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::TokenVec(tokens))?;
    Ok(())
}

/// Author `xformOp:translate` (`double3`) and append it to
/// `xformOpOrder`. The full op name is `xformOp:translate`.
pub fn set_translate(stage: &Stage, prim: &Path, value: [f64; 3]) -> Result<()> {
    let op = "translate";
    author_xform_op(stage, prim, op, "double3", Value::Vec3d(value))?;
    append_op(stage, prim, op)
}

/// Author `xformOp:scale` (`float3`) and append it to `xformOpOrder`.
pub fn set_scale(stage: &Stage, prim: &Path, value: [f32; 3]) -> Result<()> {
    let op = "scale";
    author_xform_op(stage, prim, op, "float3", Value::Vec3f(value))?;
    append_op(stage, prim, op)
}

/// Author `xformOp:rotateX` in degrees and append it to `xformOpOrder`.
pub fn set_rotate_x(stage: &Stage, prim: &Path, degrees: f32) -> Result<()> {
    set_rotate_single(stage, prim, "rotateX", degrees)
}

/// Author `xformOp:rotateY` in degrees and append it to `xformOpOrder`.
pub fn set_rotate_y(stage: &Stage, prim: &Path, degrees: f32) -> Result<()> {
    set_rotate_single(stage, prim, "rotateY", degrees)
}

/// Author `xformOp:rotateZ` in degrees and append it to `xformOpOrder`.
pub fn set_rotate_z(stage: &Stage, prim: &Path, degrees: f32) -> Result<()> {
    set_rotate_single(stage, prim, "rotateZ", degrees)
}

/// Author `xformOp:rotateXYZ` (Euler angles in degrees, applied X →
/// Y → Z per Pixar's C++ source) and append it to `xformOpOrder`.
pub fn set_rotate_xyz(stage: &Stage, prim: &Path, degrees: [f32; 3]) -> Result<()> {
    let op = "rotateXYZ";
    author_xform_op(stage, prim, op, "float3", Value::Vec3f(degrees))?;
    append_op(stage, prim, op)
}

/// Author `xformOp:orient` (`quatf`, `(w, x, y, z)`) and append it to
/// `xformOpOrder`.
pub fn set_orient(stage: &Stage, prim: &Path, quat_wxyz: [f32; 4]) -> Result<()> {
    let op = "orient";
    author_xform_op(stage, prim, op, "quatf", Value::Quatf(quat_wxyz))?;
    append_op(stage, prim, op)
}

/// Author `xformOp:transform` (`matrix4d`, row-major flattened) and
/// append it to `xformOpOrder`. Useful for authoring an exact 4×4
/// matrix that doesn't decompose cleanly into T·R·S.
pub fn set_transform(stage: &Stage, prim: &Path, matrix: [f64; 16]) -> Result<()> {
    let op = "transform";
    author_xform_op(stage, prim, op, "matrix4d", Value::Matrix4d(matrix))?;
    append_op(stage, prim, op)
}

// ── internals ──────────────────────────────────────────────────────

fn set_rotate_single(stage: &Stage, prim: &Path, op: &str, degrees: f32) -> Result<()> {
    author_xform_op(stage, prim, op, "float", Value::Float(degrees))?;
    append_op(stage, prim, op)
}

/// Author a single `xformOp:<kind>` attribute with the given type +
/// value. Does NOT touch `xformOpOrder` — that's the caller's job.
fn author_xform_op(stage: &Stage, prim: &Path, kind: &str, type_name: &str, value: Value) -> Result<()> {
    let attr_path = prim.append_property(&format!("{NS_XFORM_OP}{kind}"))?;
    stage
        .create_attribute(attr_path, type_name)?
        .set_custom(false)?
        .set(value)?;
    Ok(())
}

/// Append `xformOp:<kind>` to `xformOpOrder`. Successive `set_*` calls
/// compose without clobbering each other; the generic ordered-token-stack
/// logic lives on [`Prim::append_to_uniform_token_array`].
fn append_op(stage: &Stage, prim: &Path, kind: &str) -> Result<()> {
    Prim::new(stage, prim.clone()).append_to_uniform_token_array(A_XFORM_OP_ORDER, format!("{NS_XFORM_OP}{kind}"))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::geom::read_xform_op_order;
    use crate::sdf;

    #[test]
    fn translate_appears_in_xform_op_order() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/X")?.set_type_name("Xform")?;
        set_translate(&stage, &sdf::path("/X")?, [1.0, 2.0, 3.0])?;

        let order = read_xform_op_order(&stage, &sdf::path("/X")?)?.expect("authored");
        assert_eq!(order, vec!["xformOp:translate".to_string()]);

        match stage.field::<sdf::Value>("/X.xformOp:translate", sdf::FieldKey::Default)? {
            Some(sdf::Value::Vec3d(v)) => assert_eq!(v, [1.0, 2.0, 3.0]),
            other => panic!("expected Vec3d, got {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn trs_stack_preserves_insertion_order() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/X")?.set_type_name("Xform")?;
        set_translate(&stage, &sdf::path("/X")?, [1.0, 2.0, 3.0])?;
        set_rotate_y(&stage, &sdf::path("/X")?, 90.0)?;
        set_scale(&stage, &sdf::path("/X")?, [2.0, 2.0, 2.0])?;

        let order = read_xform_op_order(&stage, &sdf::path("/X")?)?.expect("authored");
        assert_eq!(
            order,
            vec![
                "xformOp:translate".to_string(),
                "xformOp:rotateY".to_string(),
                "xformOp:scale".to_string(),
            ],
        );
        Ok(())
    }

    #[test]
    fn re_authoring_same_op_does_not_duplicate_order() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/X")?.set_type_name("Xform")?;
        set_translate(&stage, &sdf::path("/X")?, [1.0, 0.0, 0.0])?;
        set_translate(&stage, &sdf::path("/X")?, [2.0, 0.0, 0.0])?;

        let order = read_xform_op_order(&stage, &sdf::path("/X")?)?.expect("authored");
        assert_eq!(order, vec!["xformOp:translate".to_string()]);
        Ok(())
    }

    #[test]
    fn rotate_xyz_authors_float3() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/X")?.set_type_name("Xform")?;
        set_rotate_xyz(&stage, &sdf::path("/X")?, [30.0, 45.0, 60.0])?;

        match stage.field::<sdf::Value>("/X.xformOp:rotateXYZ", sdf::FieldKey::Default)? {
            Some(sdf::Value::Vec3f(v)) => assert_eq!(v, [30.0, 45.0, 60.0]),
            other => panic!("expected Vec3f for rotateXYZ, got {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn orient_writes_quatf() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/X")?.set_type_name("Xform")?;
        set_orient(&stage, &sdf::path("/X")?, [1.0, 0.0, 0.0, 0.0])?;

        match stage.field::<sdf::Value>("/X.xformOp:orient", sdf::FieldKey::Default)? {
            Some(sdf::Value::Quatf(q)) => assert_eq!(q, [1.0, 0.0, 0.0, 0.0]),
            other => panic!("expected Quatf for orient, got {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn transform_op_writes_matrix4d() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/X")?.set_type_name("Xform")?;
        let m = [
            1.0, 0.0, 0.0, 0.0, //
            0.0, 1.0, 0.0, 0.0, //
            0.0, 0.0, 1.0, 0.0, //
            5.0, 0.0, 0.0, 1.0,
        ];
        set_transform(&stage, &sdf::path("/X")?, m)?;

        match stage.field::<sdf::Value>("/X.xformOp:transform", sdf::FieldKey::Default)? {
            Some(sdf::Value::Matrix4d(value)) => assert_eq!(value[12], 5.0),
            other => panic!("expected Matrix4d, got {other:?}"),
        }
        Ok(())
    }
}
