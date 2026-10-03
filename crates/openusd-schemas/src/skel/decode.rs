//! What a `UsdSkel` view's properties decode to.
//!
//! A skeleton's joints are a `token[]` of paths that the object model reads as
//! a topology; a blend shape's inbetweens are prims beneath it. These are the
//! readers the rest of the family is built on, over the generated views.

use openusd::Result;
use openusd::gf;
use openusd::sdf::{self, Value};
use openusd::tf;
use openusd::usd::{SchemaBase, Stage};

use super::tokens;
use super::{Animation, AnimationSchema, BindingAPI, BlendShape, InfluenceInterpolation, Skeleton, SkeletonSchema};
use crate::geom::Primvar;

/// The namespace an inbetween shape is authored under (C++'s own
/// `inbetweensPrefix`), which names no property and so has no token. The
/// primvar metadata beside it does: `interpolation` and `elementSize` are
/// `usdGeom`'s, which this family builds on.
pub const INBETWEENS_NAMESPACE: &str = "inbetweens:";
impl Skeleton {
    /// The `joints` paths as text, which the topology is read from; empty when
    /// unauthored.
    pub fn joint_paths(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// Parent index of each joint, recovered from the path encoding:
    /// `joints[i] = "A/B"` ⇒ parent is the index of `"A"`; a joint with no
    /// `/` is a root and gets `None`.
    pub fn joint_parent_indices(&self) -> Result<Vec<Option<usize>>> {
        let joints = self.joint_paths()?;
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
            .joint_paths()?
            .iter()
            .map(|p| p.rsplit_once('/').map_or(p.as_str(), |(_, n)| n).to_string())
            .collect())
    }

    /// Map an animation's `joints` to indices in this skeleton's `joints` (by
    /// exact path match) — the animation's ordering need not match the
    /// skeleton's. C++ `UsdSkelAnimMapper` builds the same correspondence.
    pub fn map_anim_joints(&self, anim_joints: &[String]) -> Result<Vec<Option<usize>>> {
        let joints = self.joint_paths()?;
        let by_path = super::topology::joint_index_map(&joints);
        Ok(anim_joints.iter().map(|p| by_path.get(p.as_str()).copied()).collect())
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

    /// Decoded `skel:joints` subset (empty when unauthored).
    pub fn joint_subset(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `skel:blendShapeTargets` prim paths.
    pub fn blend_shape_targets(&self) -> Result<Vec<sdf::Path>> {
        self.blend_shape_targets_rel().targets()
    }

    /// `elementSize` on the joint-influence primvars — the number of
    /// `(joint, weight)` pairs per element; 1 where none is authored.
    pub fn elements_per_element(&self) -> Result<i32> {
        Primvar::new(self.joint_indices_attr()).element_size()
    }

    /// `interpolation` on the joint-influence primvars, which is
    /// [`InfluenceInterpolation::Constant`] where none is authored, as it is
    /// for every primvar.
    pub fn interpolation(&self) -> Result<InfluenceInterpolation> {
        Ok(self
            .joint_indices_attr()
            .get_metadata::<InfluenceInterpolation>(crate::geom::tokens::INTERPOLATION)?
            .unwrap_or_default())
    }
}

impl Animation {
    /// The `joints` paths as text, in the order the animation's arrays list
    /// them; empty when unauthored.
    pub fn joint_paths(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }
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
    use crate::skel::{BlendShapeSchema, SkinningMethod};

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
        assert_eq!(body.joint_indices()?, Some(vec![0, 1]));
        assert_eq!(body.joint_weights()?, Some(vec![1.0, 1.0]));
        assert_eq!(body.skinning_method()?, Some(SkinningMethod::ClassicLinear));
        Ok(())
    }

    /// The joint influences are primvars, so with nothing authored they are
    /// constant and one value per element, and the authored metadata reads
    /// back.
    #[test]
    fn unauthored_interpolation_constant() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        stage.define_prim("/Body")?;
        let body = BindingAPI::apply(&stage.prim("/Body")?)?;
        let indices = body.create_joint_indices_attr()?.set(Value::IntVec(vec![0, 1]))?;
        assert_eq!(body.interpolation()?, InfluenceInterpolation::Constant);
        assert_eq!(body.elements_per_element()?, 1);

        indices
            .set_metadata(crate::geom::tokens::INTERPOLATION, InfluenceInterpolation::Vertex)?
            .set_metadata(crate::geom::tokens::ELEMENT_SIZE, Value::Int(2))?;
        assert_eq!(body.interpolation()?, InfluenceInterpolation::Vertex);
        assert_eq!(body.elements_per_element()?, 2);
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
        bs.attribute_builder("inbetweens:half", "vector3f[]")
            .custom(false)
            .set(Value::Vec3fVec(vec![[0.0_f32, 0.04, 0.0].into()]))
            .build()?
            .set_metadata(tokens::WEIGHT, Value::Float(0.5))?;

        let bs = BlendShape::get(&stage, "/Smile")?.expect("BlendShape");
        assert_eq!(bs.offsets()?, Some(vec![gf::vec3f(0.0, 0.1, 0.0)]));
        assert_eq!(bs.point_indices()?, Some(vec![0]));
        let inbetweens = bs.inbetweens()?;
        assert_eq!(inbetweens.len(), 1);
        assert_eq!(inbetweens[0].name, "half");
        assert_eq!(inbetweens[0].weight, Some(0.5));
        assert_eq!(inbetweens[0].offsets, vec![gf::vec3f(0.0, 0.04, 0.0)]);
        Ok(())
    }
}
