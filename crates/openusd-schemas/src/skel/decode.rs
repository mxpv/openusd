//! What a `UsdSkel` view's properties decode to.
//!
//! A skeleton's joints are a `token[]` of paths that the object model reads as
//! a topology; a blend shape's inbetweens are prims beneath it. These are the
//! readers the rest of the family is built on, over the generated views.

use openusd::Result;
use openusd::gf;
use openusd::sdf::{self, Value};
use openusd::tf;
use openusd::usd::{Attribute, SchemaBase, Stage};

use super::tokens;
use super::{
    Animation, AnimationSchema, BindingAPI, BlendShape, BlendShapeSchema, InfluenceInterpolation, Skeleton,
    SkeletonSchema, SkinningMethod,
};

/// The namespace an inbetween shape is authored under (C++'s own
/// `inbetweensPrefix`), which names no property and so has no token. The
/// primvar metadata beside it does: `interpolation` and `elementSize` are
/// `usdGeom`'s, which this family builds on.
pub const INBETWEENS_NAMESPACE: &str = "inbetweens:";
impl Skeleton {
    /// Decoded `joints` token array (empty when unauthored).
    pub fn joints(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `bindTransforms` as row-major 4×4 matrices.
    pub fn bind_transforms(&self) -> Result<Vec<gf::Matrix4d>> {
        mat4_vec(&self.bind_transforms_attr())
    }

    /// Decoded `restTransforms` as row-major 4×4 matrices.
    pub fn rest_transforms(&self) -> Result<Vec<gf::Matrix4d>> {
        mat4_vec(&self.rest_transforms_attr())
    }

    /// Parent index of each joint, recovered from the path encoding:
    /// `joints[i] = "A/B"` ⇒ parent is the index of `"A"`; a joint with no
    /// `/` is a root and gets `None`.
    pub fn joint_parent_indices(&self) -> Result<Vec<Option<usize>>> {
        let joints = self.joints()?;
        let by_path = super::topology::joint_index_map(&joints);
        Ok(joints
            .iter()
            .map(|p| p.rsplit_once('/').and_then(|(parent, _)| by_path.get(parent).copied()))
            .collect())
    }

    /// Last path segment of each joint — the bone's display name (the full
    /// path verbatim when the joint has no `/`).
    pub fn joint_short_names(&self) -> Result<Vec<String>> {
        Ok(self
            .joints()?
            .iter()
            .map(|p| p.rsplit_once('/').map_or(p.as_str(), |(_, n)| n).to_string())
            .collect())
    }

    /// Map an animation's `joints` to indices in this skeleton's `joints` (by
    /// exact path match) — the animation's ordering need not match the
    /// skeleton's. C++ `UsdSkelAnimMapper` builds the same correspondence.
    pub fn map_anim_joints(&self, anim_joints: &[String]) -> Result<Vec<Option<usize>>> {
        let joints = self.joints()?;
        let by_path = super::topology::joint_index_map(&joints);
        Ok(anim_joints.iter().map(|p| by_path.get(p.as_str()).copied()).collect())
    }
}

impl Animation {
    /// Decoded `joints` token array.
    pub fn joints(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `blendShapes` token array.
    pub fn blend_shapes(&self) -> Result<Vec<String>> {
        Ok(self.blend_shapes_attr().cast()?.unwrap_or_default())
    }
}

/// One in-between shape authored on a [`BlendShape`] (C++
/// `UsdSkelInbetweenShape`). Spec: `0 < weight < 1`; the endpoints (rest at 0,
/// the primary shape at 1) are implicit and not authored as inbetweens.
#[derive(Debug, Clone, PartialEq)]
pub struct Inbetween {
    /// Inbetween name — the segment after `inbetweens:`.
    pub name: String,
    /// `weight` metadata. Required by spec; `None` flags malformed authoring.
    pub weight: Option<f32>,
    /// Position offsets, parallel to the parent's `pointIndices` layout.
    pub offsets: Vec<gf::Vec3f>,
    /// Optional `inbetweens:<name>:normalOffsets`. Empty when unauthored.
    pub normal_offsets: Vec<gf::Vec3f>,
}

/// Per-vertex position / normal offsets defining a deformation target (C++
/// `UsdSkelBlendShape`), optionally with inbetween shapes. Sparse via
/// `pointIndices` (`offsets[i]` applies to vertex `pointIndices[i]`), dense
/// when `pointIndices` is empty.
impl BlendShape {
    /// Decoded `offsets`.
    pub fn offsets(&self) -> Result<Vec<gf::Vec3f>> {
        Ok(self.offsets_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `normalOffsets`.
    pub fn normal_offsets(&self) -> Result<Vec<gf::Vec3f>> {
        Ok(self.normal_offsets_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `pointIndices`.
    pub fn point_indices(&self) -> Result<Vec<i32>> {
        Ok(match self.point_indices_attr().get::<Value>()? {
            Some(Value::IntVec(v)) => v,
            _ => Vec::new(),
        })
    }

    /// The authored `inbetweens:<name>` shapes, in authoring order (C++
    /// `UsdSkelBlendShape::GetInbetweens`). Each carries its `weight` metadata,
    /// `offsets`, and optional `inbetweens:<name>:normalOffsets`.
    pub fn inbetweens(&self) -> Result<Vec<Inbetween>> {
        let mut out = Vec::new();
        let props = self.stage().prim(self.path().clone())?.authored_property_names()?;
        for name in &props {
            let Some(rest) = name.strip_prefix(INBETWEENS_NAMESPACE) else {
                continue;
            };
            // Skip the per-inbetween `normalOffsets` siblings — folded into the
            // inbetween that names them.
            if rest.contains(':') {
                continue;
            }
            let attr = self.attribute(name);
            let offsets = attr.cast()?.unwrap_or_default();
            let weight = match attr.get_metadata::<Value>(tokens::WEIGHT)? {
                Some(Value::Float(f)) => Some(f),
                Some(Value::Double(d)) => Some(d as f32),
                _ => None,
            };
            let normal_offsets_name = format!("{INBETWEENS_NAMESPACE}{rest}:{}", tokens::NORMAL_OFFSETS);
            let normal_offsets = if props.iter().any(|n| n.as_str() == normal_offsets_name) {
                self.attribute(&normal_offsets_name).cast()?.unwrap_or_default()
            } else {
                Vec::new()
            };
            out.push(Inbetween {
                name: rest.to_string(),
                weight,
                offsets,
                normal_offsets,
            });
        }
        Ok(out)
    }
}

impl BindingAPI {
    /// The `skel:skeleton` target authored directly on this prim (C++
    /// `GetSkeleton`), or `None` when only inherited.
    pub fn skeleton(&self) -> Result<Option<sdf::Path>> {
        Ok(self.skeleton_rel().targets()?.into_iter().next())
    }

    /// The `skel:animationSource` target authored directly on this prim
    /// (C++ `GetAnimationSource`), or `None` when only inherited.
    pub fn animation_source(&self) -> Result<Option<sdf::Path>> {
        Ok(self.animation_source_rel().targets()?.into_iter().next())
    }

    /// Resolve the inherited `skel:skeleton` by walking this prim and its
    /// ancestors for the nearest authored binding (C++
    /// `UsdSkelBindingAPI::GetInheritedSkeleton` via `UsdSkelCache`).
    pub fn inherited_skeleton(&self) -> Result<Option<sdf::Path>> {
        inherited_rel(self.stage(), self.path(), tokens::SKEL_SKELETON)
    }

    /// Resolve the inherited `skel:animationSource`; same rules as
    /// [`Self::inherited_skeleton`].
    pub fn inherited_animation_source(&self) -> Result<Option<sdf::Path>> {
        inherited_rel(self.stage(), self.path(), tokens::SKEL_ANIMATION_SOURCE)
    }

    /// Decoded `primvars:skel:jointIndices`.
    pub fn joint_indices(&self) -> Result<Vec<i32>> {
        Ok(match self.joint_indices_attr().get::<Value>()? {
            Some(Value::IntVec(v)) => v,
            _ => Vec::new(),
        })
    }

    /// Decoded `primvars:skel:jointWeights` (doubles widened to `f32`).
    pub fn joint_weights(&self) -> Result<Vec<f32>> {
        Ok(match self.joint_weights_attr().get::<Value>()? {
            Some(Value::FloatVec(v)) => v,
            Some(Value::DoubleVec(v)) => v.into_iter().map(|d| d as f32).collect(),
            _ => Vec::new(),
        })
    }

    /// Decoded `skel:joints` subset (empty when unauthored).
    pub fn joint_subset(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `skel:blendShapes`.
    pub fn blend_shapes(&self) -> Result<Vec<String>> {
        Ok(self.blend_shapes_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `skel:blendShapeTargets` prim paths.
    pub fn blend_shape_targets(&self) -> Result<Vec<sdf::Path>> {
        self.blend_shape_targets_rel().targets()
    }

    /// Decoded `primvars:skel:geomBindTransform`; `None` when unauthored (the
    /// spec default is the identity matrix).
    pub fn geom_bind_transform(&self) -> Result<Option<gf::Matrix4d>> {
        Ok(match self.geom_bind_transform_attr().get::<Value>()? {
            Some(Value::Matrix4d(m)) => Some(m),
            _ => None,
        })
    }

    /// Decoded `primvars:skel:skinningMethod`; defaults to
    /// [`SkinningMethod::ClassicLinear`].
    pub fn skinning_method(&self) -> Result<SkinningMethod> {
        Ok(self.skinning_method_attr().get::<SkinningMethod>()?.unwrap_or_default())
    }

    /// `elementSize` on the joint-influence primvars — the number of
    /// `(joint, weight)` pairs per element; defaults to 1.
    pub fn elements_per_element(&self) -> Result<i32> {
        Ok(
            match self
                .joint_indices_attr()
                .get_metadata::<Value>(crate::geom::tokens::ELEMENT_SIZE)?
            {
                Some(Value::Int(n)) => n,
                Some(Value::Int64(n)) => n as i32,
                _ => 1,
            },
        )
    }

    /// Authored `interpolation` on the joint-influence primvars; defaults to
    /// [`InfluenceInterpolation::Vertex`].
    pub fn interpolation(&self) -> Result<InfluenceInterpolation> {
        Ok(self
            .joint_indices_attr()
            .get_metadata::<InfluenceInterpolation>(crate::geom::tokens::INTERPOLATION)?
            .unwrap_or_default())
    }
}

/// Decode a `matrix4d[]` attribute (empty when unauthored).
fn mat4_vec(attr: &Attribute) -> Result<Vec<gf::Matrix4d>> {
    Ok(match attr.get::<Value>()? {
        Some(Value::Matrix4dVec(v)) => v,
        _ => Vec::new(),
    })
}

/// Walk `prim` and its ancestors for the nearest authored `rel_name` target.
/// `skel:skeleton` / `skel:animationSource` inherit down namespace regardless
/// of where `BindingAPI` is formally applied.
fn inherited_rel(stage: &Stage, prim: &sdf::Path, rel_name: impl Into<tf::Token>) -> Result<Option<sdf::Path>> {
    let rel_name = rel_name.into();
    let mut cur = prim.clone();
    loop {
        let rel = cur.append_property(&rel_name)?;
        if let Some(target) = stage.relationship(rel)?.targets()?.into_iter().next() {
            return Ok(Some(target));
        }
        match cur.parent() {
            Some(p) if !cur.is_abs_root() => cur = p,
            _ => return Ok(None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use openusd::Result;

    use crate::skel::{BindingAPI, BlendShape};

    #[test]
    fn binding_roundtrip_and_inheritance() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        // Skeleton bound on the root; influences on the mesh. An API schema is
        // applied to a prim, so both exist before it is.
        stage.define_prim("/Char")?;
        stage.define_prim("/Char/Body")?;
        let root = BindingAPI::apply(&stage.prim("/Char")?)?;
        root.create_skeleton_rel()?.add_target("/Char/Rig")?;

        let body = BindingAPI::apply(&stage.prim("/Char/Body")?)?;
        body.create_joint_indices_attr()?.set(Value::IntVec(vec![0, 1]))?;
        body.create_joint_weights_attr()?.set(Value::FloatVec(vec![1.0, 1.0]))?;
        body.create_skinning_method_attr()?.set(SkinningMethod::ClassicLinear)?;

        let body = BindingAPI::get(&stage, "/Char/Body")?.expect("BindingAPI");
        assert!(body.skeleton()?.is_none()); // not authored directly
        assert_eq!(
            body.inherited_skeleton()?.map(|p| p.as_str().to_string()),
            Some("/Char/Rig".to_string())
        );
        assert_eq!(body.joint_indices()?, vec![0, 1]);
        assert_eq!(body.joint_weights()?, vec![1.0, 1.0]);
        assert_eq!(body.elements_per_element()?, 1);
        assert_eq!(body.interpolation()?, InfluenceInterpolation::Vertex);
        assert_eq!(body.skinning_method()?, SkinningMethod::ClassicLinear);
        Ok(())
    }

    #[test]
    fn blend_shape_inbetween() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let bs = BlendShape::define(&stage, "/Smile")?;
        bs.create_offsets_attr()?
            .set(Value::Vec3fVec(vec![[0.0_f32, 0.1, 0.0].into()]))?;
        bs.create_point_indices_attr()?.set(Value::IntVec(vec![0]))?;
        // Author an inbetween at weight 0.5.
        let inb = bs
            .create_attribute("inbetweens:half", "vector3f[]")?
            .set_custom(false)?;
        inb.set(Value::Vec3fVec(vec![[0.0_f32, 0.04, 0.0].into()]))?
            .set_metadata(tokens::WEIGHT, Value::Float(0.5))?;

        let bs = BlendShape::get(&stage, "/Smile")?.expect("BlendShape");
        assert_eq!(bs.offsets()?, vec![gf::vec3f(0.0, 0.1, 0.0)]);
        assert_eq!(bs.point_indices()?, vec![0]);
        let inbetweens = bs.inbetweens()?;
        assert_eq!(inbetweens.len(), 1);
        assert_eq!(inbetweens[0].name, "half");
        assert_eq!(inbetweens[0].weight, Some(0.5));
        assert_eq!(inbetweens[0].offsets, vec![gf::vec3f(0.0, 0.04, 0.0)]);
        Ok(())
    }
}
