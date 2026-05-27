//! `SkelBindingAPI` authoring.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::skel::tokens::{
    API_SKEL_BINDING, A_GEOM_BIND_TRANSFORM, A_JOINT_INDICES, A_JOINT_WEIGHTS, A_SKEL_BLEND_SHAPES, A_SKEL_JOINTS,
    A_SKINNING_METHOD, META_ELEMENT_SIZE, META_INTERPOLATION, REL_SKEL_ANIMATION_SOURCE, REL_SKEL_BLEND_SHAPE_TARGETS,
    REL_SKEL_SKELETON,
};
use crate::schemas::skel::types::{InfluenceInterpolation, SkinningMethod};

/// Apply `SkelBindingAPI` to the prim at `path` (existing prim spec
/// required — typically a skinnable Mesh under a SkelRoot subtree)
/// and return a chainable [`SkelBindingAuthor`].
///
/// Authors `apiSchemas += ["SkelBindingAPI"]` via
/// [`Prim::add_applied_schema`], then offers setters for the 9
/// attributes / relationships defined by Pixar's
/// `usdSkel/schema.usda`:
///
/// Relationships:
/// - `skel:skeleton` — bound Skeleton
/// - `skel:animationSource` — bound SkelAnimation
/// - `skel:blendShapeTargets` — ordered targets to BlendShape prims
///
/// Attributes:
/// - `primvars:skel:skinningMethod` (uniform token, allowedTokens =
///   `classicLinear` / `dualQuaternion`)
/// - `primvars:skel:geomBindTransform` (matrix4d singleton)
/// - `skel:joints` (uniform token[], joint-name subset)
/// - `primvars:skel:jointIndices` (int[] primvar with
///   `elementSize` + `interpolation` metadata)
/// - `primvars:skel:jointWeights` (float[] primvar with
///   `elementSize` + `interpolation` metadata)
/// - `skel:blendShapes` (uniform token[])
pub fn apply_skel_binding<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<SkelBindingAuthor<'s>> {
    let prim = stage.override_prim(path)?.add_applied_schema(API_SKEL_BINDING)?;
    Ok(SkelBindingAuthor { prim })
}

/// Chainable SkelBindingAPI authoring handle.
pub struct SkelBindingAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> SkelBindingAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Author `skel:skeleton` — relationship target to the bound Skeleton prim.
    pub fn set_skeleton(self, skeleton: impl Into<Path>) -> Result<Self> {
        let rel_path = self.prim.path().append_property(REL_SKEL_SKELETON)?;
        self.prim
            .stage()
            .create_relationship(rel_path)?
            .set_custom(false)?
            .set_targets([skeleton.into()])?;
        Ok(self)
    }

    /// Author `skel:animationSource` — relationship target to the bound SkelAnimation prim.
    pub fn set_animation_source(self, anim: impl Into<Path>) -> Result<Self> {
        let rel_path = self.prim.path().append_property(REL_SKEL_ANIMATION_SOURCE)?;
        self.prim
            .stage()
            .create_relationship(rel_path)?
            .set_custom(false)?
            .set_targets([anim.into()])?;
        Ok(self)
    }

    /// Author `skel:blendShapeTargets` — ordered list of relationship
    /// targets to BlendShape prims, paired by index with
    /// [`Self::set_blend_shapes`].
    pub fn set_blend_shape_targets<I, P>(self, targets: I) -> Result<Self>
    where
        I: IntoIterator<Item = P>,
        P: Into<Path>,
    {
        let rel_path = self.prim.path().append_property(REL_SKEL_BLEND_SHAPE_TARGETS)?;
        let paths: Vec<Path> = targets.into_iter().map(Into::into).collect();
        self.prim
            .stage()
            .create_relationship(rel_path)?
            .set_custom(false)?
            .set_targets(paths)?;
        Ok(self)
    }

    /// Author `primvars:skel:skinningMethod` — uniform token with
    /// allowedTokens `classicLinear` / `dualQuaternion`. The
    /// [`SkinningMethod`] enum enforces the spec's allowed values at
    /// the type level.
    pub fn set_skinning_method(self, method: SkinningMethod) -> Result<Self> {
        let attr_path = self.prim.path().append_property(A_SKINNING_METHOD)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "token")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::Token(method.as_token().to_string()))?;
        Ok(self)
    }

    /// Author `primvars:skel:geomBindTransform` — singleton matrix4d
    /// recording the bind-time world transform of the prim.
    pub fn set_geom_bind_transform(self, transform: [f64; 16]) -> Result<Self> {
        let attr_path = self.prim.path().append_property(A_GEOM_BIND_TRANSFORM)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "matrix4d")?
            .set_custom(false)?
            .set(Value::Matrix4d(transform))?;
        Ok(self)
    }

    /// Author `skel:joints` — uniform token[] joint subset. When
    /// authored, `primvars:skel:jointIndices` index into this list
    /// instead of the bound Skeleton's `joints`.
    pub fn set_joints<I, S>(self, joints: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = joints.into_iter().map(Into::into).collect();
        let attr_path = self.prim.path().append_property(A_SKEL_JOINTS)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "token[]")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::TokenVec(tokens))?;
        Ok(self)
    }

    /// Author `primvars:skel:jointIndices` — int[] primvar. Per spec,
    /// the primvar carries `elementSize` (joint influences per point)
    /// and `interpolation` (`constant` / `vertex`).
    pub fn set_joint_indices(
        self,
        indices: Vec<i32>,
        element_size: i32,
        interpolation: InfluenceInterpolation,
    ) -> Result<Self> {
        let attr_path = self.prim.path().append_property(A_JOINT_INDICES)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "int[]")?
            .set_custom(false)?
            .set(Value::IntVec(indices))?
            .set_metadata(META_ELEMENT_SIZE, Value::Int(element_size))?
            .set_metadata(META_INTERPOLATION, Value::Token(interpolation.as_token().to_string()))?;
        Ok(self)
    }

    /// Author `primvars:skel:jointWeights` — float[] primvar. Same
    /// `elementSize` + `interpolation` metadata as
    /// [`Self::set_joint_indices`]; per spec the two primvars must
    /// match in length, interpolation, and elementSize.
    pub fn set_joint_weights(
        self,
        weights: Vec<f32>,
        element_size: i32,
        interpolation: InfluenceInterpolation,
    ) -> Result<Self> {
        let attr_path = self.prim.path().append_property(A_JOINT_WEIGHTS)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "float[]")?
            .set_custom(false)?
            .set(Value::FloatVec(weights))?
            .set_metadata(META_ELEMENT_SIZE, Value::Int(element_size))?
            .set_metadata(META_INTERPOLATION, Value::Token(interpolation.as_token().to_string()))?;
        Ok(self)
    }

    /// Author `skel:blendShapes` — uniform token[] mapping animation
    /// blend-shape names to entries in [`Self::set_blend_shape_targets`].
    pub fn set_blend_shapes<I, S>(self, blend_shapes: I) -> Result<Self>
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        let tokens: Vec<String> = blend_shapes.into_iter().map(Into::into).collect();
        let attr_path = self.prim.path().append_property(A_SKEL_BLEND_SHAPES)?;
        self.prim
            .stage()
            .create_attribute(attr_path, "token[]")?
            .set_variability(Variability::Uniform)?
            .set_custom(false)?
            .set(Value::TokenVec(tokens))?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    fn identity() -> [f64; 16] {
        let mut m = [0.0; 16];
        m[0] = 1.0;
        m[5] = 1.0;
        m[10] = 1.0;
        m[15] = 1.0;
        m
    }

    #[test]
    fn apply_skel_binding_adds_api_to_prim() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        // Mesh must exist before applying the API.
        stage.define_prim("/Body")?.set_type_name("Mesh")?;
        apply_skel_binding(&stage, sdf::path("/Body")?)?;

        let api = stage.api_schemas(&sdf::path("/Body")?)?;
        assert!(api.iter().any(|s| s == "SkelBindingAPI"));
        Ok(())
    }

    #[test]
    fn full_binding_roundtrip_via_reader() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        // Build a minimal scene: Skeleton + SkelAnimation + BlendShape +
        // skinnable mesh with SkelBindingAPI.
        stage.define_prim("/World/Body")?.set_type_name("Mesh")?;
        apply_skel_binding(&stage, sdf::path("/World/Body")?)?
            .set_skeleton(sdf::path("/World/Rig")?)?
            .set_animation_source(sdf::path("/World/Anim")?)?
            .set_skinning_method(SkinningMethod::ClassicLinear)?
            .set_geom_bind_transform(identity())?
            .set_joints(["Root/Hip", "Root/Hip/Knee"])?
            .set_joint_indices(vec![0, 1, 0, 1], 2, InfluenceInterpolation::Vertex)?
            .set_joint_weights(vec![1.0, 0.0, 0.5, 0.5], 2, InfluenceInterpolation::Vertex)?
            .set_blend_shapes(["smile"])?
            .set_blend_shape_targets([sdf::path("/World/Smile")?])?;

        // Read it back via the existing reader and verify every field.
        let bind = crate::schemas::skel::read_skel_binding(&stage, &sdf::path("/World/Body")?)?
            .expect("SkelBindingAPI authored");

        assert_eq!(bind.path, "/World/Body");
        assert_eq!(bind.skeleton.as_deref(), Some("/World/Rig"));
        assert_eq!(bind.animation_source.as_deref(), Some("/World/Anim"));
        assert_eq!(bind.skinning_method, SkinningMethod::ClassicLinear);
        assert!(bind.geom_bind_transform.is_some());
        assert_eq!(
            bind.joint_subset,
            vec!["Root/Hip".to_string(), "Root/Hip/Knee".to_string()]
        );
        assert_eq!(bind.joint_indices, vec![0, 1, 0, 1]);
        assert_eq!(bind.joint_weights, vec![1.0, 0.0, 0.5, 0.5]);
        assert_eq!(bind.elements_per_element, 2);
        assert_eq!(bind.interpolation, InfluenceInterpolation::Vertex);
        assert_eq!(bind.blend_shapes, vec!["smile".to_string()]);
        assert_eq!(bind.blend_shape_targets, vec!["/World/Smile".to_string()]);
        Ok(())
    }

    #[test]
    fn skinning_method_dual_quaternion_authored() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim("/Body")?.set_type_name("Mesh")?;
        apply_skel_binding(&stage, sdf::path("/Body")?)?.set_skinning_method(SkinningMethod::DualQuaternion)?;

        match stage.field::<sdf::Value>("/Body.primvars:skel:skinningMethod", sdf::FieldKey::Default)? {
            Some(sdf::Value::Token(t)) => assert_eq!(t, "dualQuaternion"),
            other => panic!("expected dualQuaternion token, got {other:?}"),
        }
        Ok(())
    }
}
