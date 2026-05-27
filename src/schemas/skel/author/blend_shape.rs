//! `BlendShape` prim authoring.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::skel::tokens::{A_NORMAL_OFFSETS, A_OFFSETS, A_POINT_INDICES, T_BLEND_SHAPE};

/// Author a `def BlendShape` prim at `path`. Returns a chainable
/// [`BlendShapeAuthor`] for setting the spec-defined uniform arrays:
///
/// - `offsets` (uniform vector3f[]) — required position offsets
/// - `normalOffsets` (uniform vector3f[]) — required normal offsets
/// - `pointIndices` (uniform int[]) — **optional** sparse mapping; when
///   authored, restricts `offsets` / `normalOffsets` to the listed
///   point indices on the bound mesh.
///
/// Inbetween shapes (`inbetweens:NAME` with `weight` metadata) are
/// authored separately via [`BlendShapeAuthor::add_inbetween`] in a
/// follow-up commit.
pub fn define_blend_shape<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<BlendShapeAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_BLEND_SHAPE)?;
    Ok(BlendShapeAuthor { prim })
}

/// Chainable BlendShape authoring handle.
pub struct BlendShapeAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> BlendShapeAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `offsets` — required position offsets. Adding these to the
    /// base pose produces the target shape.
    pub fn set_offsets(self, values: Vec<[f32; 3]>) -> Result<Self> {
        author_uniform_vec3f_array(self.prim.stage(), self.prim.path(), A_OFFSETS, values)?;
        Ok(self)
    }

    /// Set `normalOffsets` — required normal offsets paired with
    /// [`Self::set_offsets`].
    pub fn set_normal_offsets(self, values: Vec<[f32; 3]>) -> Result<Self> {
        author_uniform_vec3f_array(self.prim.stage(), self.prim.path(), A_NORMAL_OFFSETS, values)?;
        Ok(self)
    }

    /// Set `pointIndices` — optional sparse mapping. When authored,
    /// `offsets[i]` / `normalOffsets[i]` apply to the bound mesh point
    /// at `pointIndices[i]`. Per spec, the lengths of `pointIndices`
    /// and `offsets` must match when authored.
    pub fn set_point_indices(self, indices: Vec<i32>) -> Result<Self> {
        let attr_path = self.prim.path().append_property(A_POINT_INDICES)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "int[]")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::IntVec(indices))?;
        Ok(self)
    }
}

fn author_uniform_vec3f_array(stage: &Stage, prim: &Path, name: &str, values: Vec<[f32; 3]>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "vector3f[]")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Vec3fVec(values))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn define_blend_shape_writes_required_arrays() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_blend_shape(&stage, sdf::path("/Smile")?)?
            .set_offsets(vec![[0.0, 0.1, 0.0], [0.0, 0.2, 0.0]])?
            .set_normal_offsets(vec![[0.0, 1.0, 0.0], [0.0, 1.0, 0.0]])?;

        let prim = sdf::path("/Smile")?;
        assert_eq!(stage.type_name(&prim)?.as_deref(), Some(T_BLEND_SHAPE));

        match stage.field::<sdf::Value>("/Smile.offsets", sdf::FieldKey::Default)? {
            Some(sdf::Value::Vec3fVec(v)) => assert_eq!(v, vec![[0.0, 0.1, 0.0], [0.0, 0.2, 0.0]]),
            other => panic!("expected Vec3fVec for offsets, got {other:?}"),
        }
        match stage.field::<sdf::Value>("/Smile.normalOffsets", sdf::FieldKey::Default)? {
            Some(sdf::Value::Vec3fVec(v)) => assert_eq!(v.len(), 2),
            other => panic!("expected Vec3fVec for normalOffsets, got {other:?}"),
        }
        assert_eq!(
            stage.field::<sdf::Value>("/Smile.offsets", sdf::FieldKey::Variability)?,
            Some(sdf::Value::Variability(sdf::Variability::Uniform)),
        );
        Ok(())
    }

    #[test]
    fn point_indices_are_optional() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_blend_shape(&stage, sdf::path("/Smile")?)?
            .set_offsets(vec![[0.0, 0.1, 0.0]])?
            .set_normal_offsets(vec![[0.0, 1.0, 0.0]])?;

        // pointIndices unauthored — no attribute spec at all.
        assert!(stage
            .field::<sdf::Value>("/Smile.pointIndices", sdf::FieldKey::Default)?
            .is_none());

        // Now set pointIndices and confirm it lands.
        define_blend_shape(&stage, sdf::path("/SmileSparse")?)?
            .set_offsets(vec![[0.0, 0.1, 0.0]])?
            .set_normal_offsets(vec![[0.0, 1.0, 0.0]])?
            .set_point_indices(vec![3])?;

        match stage.field::<sdf::Value>("/SmileSparse.pointIndices", sdf::FieldKey::Default)? {
            Some(sdf::Value::IntVec(v)) => assert_eq!(v, vec![3]),
            other => panic!("expected IntVec for pointIndices, got {other:?}"),
        }
        Ok(())
    }
}
