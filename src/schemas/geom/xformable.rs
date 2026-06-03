//! `UsdGeomXformable` — transformable prims and the `xformOpOrder` stack.
//!
//! An `Xformable` prim carries its local transform as an ordered stack of
//! `xformOp:*` attributes named by `xformOpOrder`: the first entry is the
//! most local (innermost in the matrix product), the last outermost. Two
//! sentinels are honored — `!invert!<op>` inverts an op's value, and a
//! leading `!resetXformStack!` opts the prim out of inheriting its parent
//! transform (surfaced via [`Xformable::resets_xform_stack`]). Per-op values
//! flow through [`crate::usd::Stage::value_at`], so time-sampled ops
//! interpolate per AOUSD §12.5.

use anyhow::Result;

use crate::math::{
    mat4_from_quat, mat4_inverse, mat4_mul, mat4_rotation_x, mat4_rotation_y, mat4_rotation_z, mat4_scale,
    mat4_translation, IDENTITY_MAT4,
};
use crate::sdf;
use crate::usd::{Attribute, Prim};

use super::tokens as tok;
use super::Imageable;

const TOKEN_INVERT_PREFIX: &str = "!invert!";
const TOKEN_RESET_XFORM_STACK: &str = "!resetXformStack!";
const NS_XFORM_OP: &str = "xformOp:";

/// A prim that carries a transform stack (C++ `UsdGeomXformable`). Inherits
/// [`Imageable`].
///
/// Reader methods compose the authored `xformOp:*` stack; the `set_*` setters
/// author one op and append it to `xformOpOrder`, so successive calls build
/// the canonical T·R·S ordering. Setters consume `self` and return it, so
/// they chain (`xform.set_translate(t)?.set_rotate_y(d)?`).
pub trait Xformable: Imageable {
    /// `xformOpOrder` attribute handle (C++ `GetXformOpOrderAttr`).
    fn xform_op_order_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_XFORM_OP_ORDER)
    }

    /// Author the `xformOpOrder` attribute (`uniform token[]`), returning its
    /// handle (C++ `CreateXformOpOrderAttr`).
    fn create_xform_op_order_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_XFORM_OP_ORDER, "token[]")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }

    /// The authored `xformOpOrder` token list, flattening any list-op
    /// authoring. `None` when unauthored (C++ `GetXformOpOrderAttr().Get`).
    fn xform_op_order(&self) -> Result<Option<Vec<String>>> {
        let attr = self.prim().path().append_property(tok::A_XFORM_OP_ORDER)?;
        Ok(match self.prim().stage().field::<sdf::Value>(attr, "default")? {
            Some(sdf::Value::TokenVec(v) | sdf::Value::StringVec(v)) => Some(v),
            Some(sdf::Value::TokenListOp(op)) => Some(op.flatten()),
            Some(sdf::Value::StringListOp(op)) => Some(op.flatten()),
            _ => None,
        })
    }

    /// `true` when the prim lists `!resetXformStack!` as the first entry of
    /// `xformOpOrder`, opting out of inheriting its parent transform
    /// (C++ `GetResetXformStack`).
    fn resets_xform_stack(&self) -> Result<bool> {
        Ok(matches!(
            self.xform_op_order()?.as_deref().and_then(|s| s.first()),
            Some(s) if s == TOKEN_RESET_XFORM_STACK
        ))
    }

    /// Compose `xformOpOrder` into a single local-to-parent 4×4 matrix at
    /// `time` (row-major flattened). [`IDENTITY_MAT4`] when no stack is
    /// authored. Mirrors C++ `ComputeLocalToParentTransform`.
    fn local_to_parent_transform(&self, time: f64) -> Result<[f64; 16]> {
        let Some(order) = self.xform_op_order()? else {
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
                    self.prim().path().as_str(),
                    i,
                );
            }
            // Row-vector convention: the first listed op is most local
            // (applied first to a point), so the cumulative matrix grows on
            // the right.
            m = mat4_mul(&m, &build_op_matrix(self.prim(), op_name, time)?);
        }
        Ok(m)
    }

    /// Replace `xformOpOrder` with `order` verbatim (C++
    /// `SetXformOpOrderAttr`-style), rather than the per-op append the
    /// `set_*` helpers do.
    fn set_xform_op_order<I, S>(self, order: I) -> Result<Self>
    where
        Self: Sized,
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = order.into_iter().map(Into::into).collect();
        self.prim()
            .create_attribute(tok::A_XFORM_OP_ORDER, "token[]")?
            .set_variability(sdf::Variability::Uniform)?
            .set_custom(false)?
            .set(sdf::Value::TokenVec(tokens))?;
        Ok(self)
    }

    /// Author `xformOp:translate` (`double3`) and append it to the stack.
    fn set_translate(self, value: [f64; 3]) -> Result<Self>
    where
        Self: Sized,
    {
        author_xform_op(self.prim(), "translate", "double3", sdf::Value::Vec3d(value))?;
        append_op(self.prim(), "translate")?;
        Ok(self)
    }

    /// Author `xformOp:scale` (`float3`) and append it to the stack.
    fn set_scale(self, value: [f32; 3]) -> Result<Self>
    where
        Self: Sized,
    {
        author_xform_op(self.prim(), "scale", "float3", sdf::Value::Vec3f(value))?;
        append_op(self.prim(), "scale")?;
        Ok(self)
    }

    /// Author `xformOp:rotateX` in degrees and append it to the stack.
    fn set_rotate_x(self, degrees: f32) -> Result<Self>
    where
        Self: Sized,
    {
        self.set_rotate_single("rotateX", degrees)
    }

    /// Author `xformOp:rotateY` in degrees and append it to the stack.
    fn set_rotate_y(self, degrees: f32) -> Result<Self>
    where
        Self: Sized,
    {
        self.set_rotate_single("rotateY", degrees)
    }

    /// Author `xformOp:rotateZ` in degrees and append it to the stack.
    fn set_rotate_z(self, degrees: f32) -> Result<Self>
    where
        Self: Sized,
    {
        self.set_rotate_single("rotateZ", degrees)
    }

    /// Author `xformOp:rotateXYZ` (Euler degrees, applied X → Y → Z) and
    /// append it to the stack.
    fn set_rotate_xyz(self, degrees: [f32; 3]) -> Result<Self>
    where
        Self: Sized,
    {
        author_xform_op(self.prim(), "rotateXYZ", "float3", sdf::Value::Vec3f(degrees))?;
        append_op(self.prim(), "rotateXYZ")?;
        Ok(self)
    }

    /// Author `xformOp:orient` (`quatf`, `(w, x, y, z)`) and append it.
    fn set_orient(self, quat_wxyz: [f32; 4]) -> Result<Self>
    where
        Self: Sized,
    {
        author_xform_op(self.prim(), "orient", "quatf", sdf::Value::Quatf(quat_wxyz))?;
        append_op(self.prim(), "orient")?;
        Ok(self)
    }

    /// Author `xformOp:transform` (`matrix4d`, row-major flattened) and
    /// append it — for an exact 4×4 that does not decompose into T·R·S.
    fn set_transform(self, matrix: [f64; 16]) -> Result<Self>
    where
        Self: Sized,
    {
        author_xform_op(self.prim(), "transform", "matrix4d", sdf::Value::Matrix4d(matrix))?;
        append_op(self.prim(), "transform")?;
        Ok(self)
    }

    /// Shared body for the single-axis rotate setters.
    fn set_rotate_single(self, op: &str, degrees: f32) -> Result<Self>
    where
        Self: Sized,
    {
        author_xform_op(self.prim(), op, "float", sdf::Value::Float(degrees))?;
        append_op(self.prim(), op)?;
        Ok(self)
    }
}

/// Build the 4×4 contribution of a single xformOp (possibly `!invert!`-ed).
fn build_op_matrix(prim: &Prim, op_name: &str, time: f64) -> Result<[f64; 16]> {
    let (inverted, base) = match op_name.strip_prefix(TOKEN_INVERT_PREFIX) {
        Some(stripped) => (true, stripped),
        None => (false, op_name),
    };

    let attr = prim.path().append_property(base)?;
    let Some(raw) = prim.stage().value_at(attr, time)? else {
        return Ok(IDENTITY_MAT4);
    };

    let after_ns = base.strip_prefix(NS_XFORM_OP).unwrap_or(base);
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
        // Rotation ops stay in f64 end-to-end; xformOp:rotate* may be authored
        // as `float` or `double` per the precision system, and reading via f32
        // would truncate the double-authored case before the trig math runs.
        "rotateX" => mat4_rotation_x(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateY" => mat4_rotation_y(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateZ" => mat4_rotation_z(value_to_scalar_f64(&raw).unwrap_or(0.0).to_radians()),
        "rotateXYZ" | "rotateYXZ" | "rotateZXY" | "rotateXZY" | "rotateYZX" | "rotateZYX" => {
            let v = value_to_vec3_f64(&raw).unwrap_or([0.0, 0.0, 0.0]);
            let rx = mat4_rotation_x(v[0].to_radians());
            let ry = mat4_rotation_y(v[1].to_radians());
            let rz = mat4_rotation_z(v[2].to_radians());
            // Apply axes in the order spelled by `kind` (row-vector product).
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
            sdf::Value::Matrix4d(m) => m,
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

/// Author a single `xformOp:<kind>` attribute (does not touch `xformOpOrder`).
fn author_xform_op(prim: &Prim, kind: &str, type_name: &str, value: sdf::Value) -> Result<()> {
    prim.create_attribute(&format!("{NS_XFORM_OP}{kind}"), type_name)?
        .set_custom(false)?
        .set(value)?;
    Ok(())
}

/// Append `xformOp:<kind>` to `xformOpOrder`, de-duplicating re-authored ops.
fn append_op(prim: &Prim, kind: &str) -> Result<()> {
    prim.append_to_uniform_token_array(tok::A_XFORM_OP_ORDER, format!("{NS_XFORM_OP}{kind}"))?;
    Ok(())
}

fn value_to_scalar_f64(v: &sdf::Value) -> Option<f64> {
    match v {
        sdf::Value::Double(d) => Some(*d),
        sdf::Value::Float(f) => Some(*f as f64),
        sdf::Value::Half(h) => Some(h.to_f32() as f64),
        sdf::Value::Int(i) => Some(*i as f64),
        sdf::Value::Int64(i) => Some(*i as f64),
        _ => None,
    }
}

fn value_to_vec3_f64(v: &sdf::Value) -> Option<[f64; 3]> {
    match v {
        sdf::Value::Vec3d(a) => Some(*a),
        sdf::Value::Vec3f(a) => Some([a[0] as f64, a[1] as f64, a[2] as f64]),
        sdf::Value::Vec3h(a) => Some([a[0].to_f32() as f64, a[1].to_f32() as f64, a[2].to_f32() as f64]),
        _ => None,
    }
}

fn value_to_quat_wxyz(v: &sdf::Value) -> Option<[f64; 4]> {
    match v {
        sdf::Value::Quatd(q) => Some(*q),
        sdf::Value::Quatf(q) => Some([q[0] as f64, q[1] as f64, q[2] as f64, q[3] as f64]),
        sdf::Value::Quath(q) => Some([
            q[0].to_f32() as f64,
            q[1].to_f32() as f64,
            q[2].to_f32() as f64,
            q[3].to_f32() as f64,
        ]),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::Xformable;
    use crate::schemas::geom::Xform;
    use crate::sdf;
    use crate::usd::Stage;
    use anyhow::Result;

    #[test]
    fn translate_appears_in_order() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let x = Xform::define(&stage, "/X")?.set_translate([1.0, 2.0, 3.0])?;
        assert_eq!(x.xform_op_order()?, Some(vec!["xformOp:translate".to_string()]));
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:translate", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3d([1.0, 2.0, 3.0]))
        );
        Ok(())
    }

    #[test]
    fn trs_preserves_insertion_order() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate([1.0, 2.0, 3.0])?
            .set_rotate_y(90.0)?
            .set_scale([2.0, 2.0, 2.0])?;
        assert_eq!(
            x.xform_op_order()?,
            Some(vec![
                "xformOp:translate".to_string(),
                "xformOp:rotateY".to_string(),
                "xformOp:scale".to_string(),
            ])
        );
        Ok(())
    }

    #[test]
    fn re_authoring_op_does_not_duplicate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let x = Xform::define(&stage, "/X")?
            .set_translate([1.0, 0.0, 0.0])?
            .set_translate([2.0, 0.0, 0.0])?;
        assert_eq!(x.xform_op_order()?, Some(vec!["xformOp:translate".to_string()]));
        Ok(())
    }

    #[test]
    fn rotate_xyz_authors_float3() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Xform::define(&stage, "/X")?.set_rotate_xyz([30.0, 45.0, 60.0])?;
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:rotateXYZ", sdf::FieldKey::Default)?,
            Some(sdf::Value::Vec3f([30.0, 45.0, 60.0]))
        );
        Ok(())
    }

    #[test]
    fn orient_writes_quatf() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Xform::define(&stage, "/X")?.set_orient([1.0, 0.0, 0.0, 0.0])?;
        assert_eq!(
            stage.field::<sdf::Value>("/X.xformOp:orient", sdf::FieldKey::Default)?,
            Some(sdf::Value::Quatf([1.0, 0.0, 0.0, 0.0]))
        );
        Ok(())
    }

    #[test]
    fn transform_writes_matrix4d() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let m = [
            1.0, 0.0, 0.0, 0.0, //
            0.0, 1.0, 0.0, 0.0, //
            0.0, 0.0, 1.0, 0.0, //
            5.0, 0.0, 0.0, 1.0,
        ];
        Xform::define(&stage, "/X")?.set_transform(m)?;
        match stage.field::<sdf::Value>("/X.xformOp:transform", sdf::FieldKey::Default)? {
            Some(sdf::Value::Matrix4d(v)) => assert_eq!(v[12], 5.0),
            other => panic!("expected Matrix4d, got {other:?}"),
        }
        Ok(())
    }
}
