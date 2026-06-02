//! `SkelAnimation` prim authoring.

use anyhow::Result;
use half::f16;

use crate::sdf::{Path, Value};
use crate::usd::{Prim, Stage};

use crate::schemas::skel::tokens::{
    A_BLEND_SHAPES, A_BLEND_SHAPE_WEIGHTS, A_JOINTS, A_ROTATIONS, A_SCALES, A_TRANSLATIONS, T_SKEL_ANIMATION,
};

use super::common::{author_uniform_token_array, varying_attribute};

/// Author a `def SkelAnimation` prim at `path`. Returns a chainable
/// [`SkelAnimationAuthor`] for setting the spec-defined attributes:
///
/// - `joints` (uniform token[])
/// - `translations` (float3[]) — time-sampleable
/// - `rotations` (quatf[]) — time-sampleable
/// - `scales` (half3[]) — 16-bit per spec; time-sampleable
/// - `blendShapes` (uniform token[])
/// - `blendShapeWeights` (float[]) — time-sampleable
pub fn define_skel_animation(stage: &Stage, path: impl Into<Path>) -> Result<SkelAnimationAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_SKEL_ANIMATION)?;
    Ok(SkelAnimationAuthor { prim })
}

/// Chainable SkelAnimation authoring handle.
pub struct SkelAnimationAuthor {
    prim: Prim,
}

impl SkelAnimationAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `joints` — uniform token[]. Each token identifies a joint
    /// the corresponding component in `translations` / `rotations` /
    /// `scales` applies to.
    pub fn set_joints<I, S>(self, joints: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = joints.into_iter().map(Into::into).collect();
        author_uniform_token_array(self.prim.stage(), self.prim.path(), A_JOINTS, tokens)?;
        Ok(self)
    }

    /// Set `blendShapes` — uniform token[]. Each token must appear in
    /// `skel:blendShapes` on the bound SkelBindingAPI.
    pub fn set_blend_shapes<I, S>(self, blend_shapes: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = blend_shapes.into_iter().map(Into::into).collect();
        author_uniform_token_array(self.prim.stage(), self.prim.path(), A_BLEND_SHAPES, tokens)?;
        Ok(self)
    }

    /// Set the default value of `translations`. Per spec, joint-local
    /// translations; array length matches `joints`.
    pub fn set_translations(self, values: Vec<[f32; 3]>) -> Result<Self> {
        varying_attribute(self.prim.stage(), self.prim.path(), A_TRANSLATIONS, "float3[]")?
            .set(Value::Vec3fVec(values))?;
        Ok(self)
    }

    /// Set a time sample of `translations` at `time`.
    pub fn set_translations_at(self, time: f64, values: Vec<[f32; 3]>) -> Result<Self> {
        varying_attribute(self.prim.stage(), self.prim.path(), A_TRANSLATIONS, "float3[]")?
            .set_at(time, Value::Vec3fVec(values))?;
        Ok(self)
    }

    /// Set the default value of `rotations` — unit quaternions in USD's
    /// `(w, x, y, z)` order. Array length matches `joints`.
    pub fn set_rotations(self, values: Vec<[f32; 4]>) -> Result<Self> {
        varying_attribute(self.prim.stage(), self.prim.path(), A_ROTATIONS, "quatf[]")?.set(Value::QuatfVec(values))?;
        Ok(self)
    }

    /// Set a time sample of `rotations` at `time`.
    pub fn set_rotations_at(self, time: f64, values: Vec<[f32; 4]>) -> Result<Self> {
        varying_attribute(self.prim.stage(), self.prim.path(), A_ROTATIONS, "quatf[]")?
            .set_at(time, Value::QuatfVec(values))?;
        Ok(self)
    }

    /// Set the default value of `scales`. Per spec, stored as **half3** —
    /// each component widens to f16. Callers pass f32 for convenience;
    /// the helper handles the precision conversion.
    pub fn set_scales(self, values: Vec<[f32; 3]>) -> Result<Self> {
        let halves = values.into_iter().map(scale_to_half3).collect();
        varying_attribute(self.prim.stage(), self.prim.path(), A_SCALES, "half3[]")?.set(Value::Vec3hVec(halves))?;
        Ok(self)
    }

    /// Set a time sample of `scales` at `time` — see [`Self::set_scales`].
    pub fn set_scales_at(self, time: f64, values: Vec<[f32; 3]>) -> Result<Self> {
        let halves = values.into_iter().map(scale_to_half3).collect();
        varying_attribute(self.prim.stage(), self.prim.path(), A_SCALES, "half3[]")?
            .set_at(time, Value::Vec3hVec(halves))?;
        Ok(self)
    }

    /// Set the default value of `blendShapeWeights`. Per spec, must
    /// be the same length as `blendShapes`.
    pub fn set_blend_shape_weights(self, values: Vec<f32>) -> Result<Self> {
        varying_attribute(self.prim.stage(), self.prim.path(), A_BLEND_SHAPE_WEIGHTS, "float[]")?
            .set(Value::FloatVec(values))?;
        Ok(self)
    }

    /// Set a time sample of `blendShapeWeights` at `time`.
    pub fn set_blend_shape_weights_at(self, time: f64, values: Vec<f32>) -> Result<Self> {
        varying_attribute(self.prim.stage(), self.prim.path(), A_BLEND_SHAPE_WEIGHTS, "float[]")?
            .set_at(time, Value::FloatVec(values))?;
        Ok(self)
    }
}

fn scale_to_half3(v: [f32; 3]) -> [f16; 3] {
    [f16::from_f32(v[0]), f16::from_f32(v[1]), f16::from_f32(v[2])]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn define_skel_animation_authors_typed_prim_with_joints_and_blend_shapes() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_skel_animation(&stage, sdf::path("/Anim")?)?
            .set_joints(["Root", "Root/Hip"])?
            .set_blend_shapes(["smile", "frown"])?;

        let anim = sdf::path("/Anim")?;
        assert_eq!(stage.type_name(&anim)?.as_deref(), Some(T_SKEL_ANIMATION));
        assert_eq!(
            stage.field::<sdf::Value>("/Anim.joints", sdf::FieldKey::Default)?,
            Some(sdf::Value::TokenVec(vec!["Root".into(), "Root/Hip".into()])),
        );
        assert_eq!(
            stage.field::<sdf::Value>("/Anim.blendShapes", sdf::FieldKey::Default)?,
            Some(sdf::Value::TokenVec(vec!["smile".into(), "frown".into()])),
        );
        Ok(())
    }

    #[test]
    fn default_pose_round_trips_translations_rotations_scales() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_skel_animation(&stage, sdf::path("/Anim")?)?
            .set_joints(["A", "B"])?
            .set_translations(vec![[0.0, 1.0, 0.0], [1.0, 0.0, 0.0]])?
            .set_rotations(vec![[1.0, 0.0, 0.0, 0.0], [0.707, 0.0, 0.0, 0.707]])?
            .set_scales(vec![[1.0, 1.0, 1.0], [2.0, 2.0, 2.0]])?;

        let t = stage.field::<sdf::Value>("/Anim.translations", sdf::FieldKey::Default)?;
        match t {
            Some(sdf::Value::Vec3fVec(v)) => assert_eq!(v, vec![[0.0, 1.0, 0.0], [1.0, 0.0, 0.0]]),
            other => panic!("expected Vec3fVec, got {other:?}"),
        }

        let r = stage.field::<sdf::Value>("/Anim.rotations", sdf::FieldKey::Default)?;
        match r {
            Some(sdf::Value::QuatfVec(v)) => {
                assert_eq!(v[0], [1.0, 0.0, 0.0, 0.0]);
                assert!((v[1][0] - 0.707).abs() < 1e-3);
            }
            other => panic!("expected QuatfVec, got {other:?}"),
        }

        // scales widened to half3 per spec.
        let s = stage.field::<sdf::Value>("/Anim.scales", sdf::FieldKey::Default)?;
        match s {
            Some(sdf::Value::Vec3hVec(v)) => {
                assert_eq!(v.len(), 2);
                assert!((v[0][0].to_f32() - 1.0).abs() < 1e-3);
                assert!((v[1][0].to_f32() - 2.0).abs() < 1e-3);
            }
            other => panic!("expected Vec3hVec (half3) for scales per spec, got {other:?}"),
        }
        Ok(())
    }

    #[test]
    fn time_sampled_translations_and_blendshape_weights_landed() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_skel_animation(&stage, sdf::path("/Anim")?)?
            .set_joints(["A"])?
            .set_blend_shapes(["smile"])?
            .set_translations_at(0.0, vec![[0.0, 0.0, 0.0]])?
            .set_translations_at(10.0, vec![[1.0, 0.0, 0.0]])?
            .set_blend_shape_weights_at(0.0, vec![0.0])?
            .set_blend_shape_weights_at(10.0, vec![1.0])?;

        let samples = stage.time_samples("/Anim.translations")?.expect("translations samples");
        assert_eq!(samples.len(), 2);
        match samples.iter().find(|(t, _)| *t == 0.0) {
            Some((_, sdf::Value::Vec3fVec(v))) => assert_eq!(v, &vec![[0.0, 0.0, 0.0]]),
            other => panic!("expected Vec3fVec at t=0, got {other:?}"),
        }

        let bsw = stage.time_samples("/Anim.blendShapeWeights")?.expect("bsw samples");
        assert_eq!(bsw.len(), 2);
        Ok(())
    }
}
