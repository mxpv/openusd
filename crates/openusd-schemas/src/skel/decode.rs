//! What a `UsdSkel` view's properties decode to.
//!
//! A skeleton's joints are a `token[]` of paths that the object model reads as
//! a topology; a blend shape's inbetweens are prims beneath it. These are the
//! readers the rest of the family is built on, over the generated views.

use openusd::Result;
use openusd::gf;
use openusd::sdf::{self, Value};
use openusd::usd::{Prim, Relationship, SchemaBase};

use super::tokens;
use super::{Animation, AnimationSchema, BindingAPI, BlendShape, Skeleton, SkeletonSchema};
use crate::geom;

/// The namespace an inbetween shape is authored under (C++'s own
/// `inbetweensPrefix`), which names no property and so has no token. The
/// primvar metadata beside it does: `interpolation` and `elementSize` are
/// `usdGeom`'s, which this family builds on.
pub const INBETWEENS_NAMESPACE: &str = "inbetweens:";

/// What a binding relationship (`skel:skeleton`, `skel:animationSource`)
/// authors on one prim (C++ `UsdSkelBindingAPI::GetSkeleton` and
/// `GetAnimationSource`). `Unauthored` is their `false` answer.
pub(super) enum Bound<T> {
    /// The relationship authors no targets. An ancestor's binding reaches the
    /// prim.
    Unauthored,
    /// The relationship authors targets, and binds the prim its first target
    /// names where that is a valid `T`. An empty target list, or a target that
    /// is not a `T`, binds nothing and still overrides an ancestor's binding.
    Authored(Option<T>),
}

impl<T> Bound<T> {
    /// The bound `T`, or `None` where the relationship binds nothing.
    fn into_bound(self) -> Option<T> {
        match self {
            Bound::Unauthored => None,
            Bound::Authored(bound) => bound,
        }
    }
}
impl Skeleton {
    /// The `joints` paths as text, which the topology is read from; empty when
    /// unauthored.
    pub fn joint_paths(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// Parent index of each joint, the nearest ancestor path among the
    /// joints as [`Topology::from_joint_paths`](super::Topology::from_joint_paths)
    /// reads it; a root gets `None`. The indices are not validated: a parent
    /// may follow its child where the joints are misordered (see
    /// [`Topology::validate`](super::Topology::validate)).
    pub fn joint_parent_indices(&self) -> Result<Vec<Option<usize>>> {
        let topology = super::Topology::from_joint_paths(&self.joint_paths()?);
        Ok((0..topology.joint_count()).map(|i| topology.parent(i)).collect())
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
            let weight = match attr.metadata::<Value>(tokens::WEIGHT)? {
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
    /// The skeleton `skel:skeleton` binds on this prim itself (C++
    /// `GetSkeleton`): `None` when nothing is authored here, when the authored
    /// target list is empty, or when its first target is not a valid
    /// [`Skeleton`].
    pub fn skeleton(&self) -> Result<Option<Skeleton>> {
        Ok(self.bound_skeleton()?.into_bound())
    }

    /// The animation `skel:animationSource` binds on this prim itself (C++
    /// `GetAnimationSource`), under the same rules as
    /// [`skeleton`](Self::skeleton).
    pub fn animation_source(&self) -> Result<Option<Animation>> {
        Ok(self.bound_animation_source()?.into_bound())
    }

    /// The skeleton bound on the nearest of this prim and its ancestors that
    /// carries `BindingAPI` and authors `skel:skeleton` (C++
    /// `GetInheritedSkeleton`). An authored binding that names no valid
    /// skeleton stops the walk and answers `None`.
    pub fn inherited_skeleton(&self) -> Result<Option<Skeleton>> {
        inherited(self, BindingAPI::bound_skeleton)
    }

    /// The animation bound on the nearest of this prim and its ancestors that
    /// carries `BindingAPI` and authors `skel:animationSource` (C++
    /// `GetInheritedAnimationSource`), under the same rules as
    /// [`inherited_skeleton`](Self::inherited_skeleton).
    pub fn inherited_animation_source(&self) -> Result<Option<Animation>> {
        inherited(self, BindingAPI::bound_animation_source)
    }

    /// The `skel:skeleton` binding authored on this prim.
    pub(super) fn bound_skeleton(&self) -> Result<Bound<Skeleton>> {
        bound(&self.skeleton_rel(), Skeleton::from_prim)
    }

    /// The `skel:animationSource` binding authored on this prim.
    fn bound_animation_source(&self) -> Result<Bound<Animation>> {
        bound(&self.animation_source_rel(), Animation::from_prim)
    }

    /// Decoded `skel:joints` subset (empty when unauthored).
    pub fn joint_subset(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// Decoded `skel:blendShapeTargets` prim paths.
    pub fn blend_shape_targets(&self) -> Result<Vec<sdf::Path>> {
        self.blend_shape_targets_rel().targets()
    }
}

impl Animation {
    /// The `joints` paths as text, in the order the animation's arrays list
    /// them; empty when unauthored.
    pub fn joint_paths(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }
}

/// The binding `rel` authors, its first forwarded target viewed through `view`
/// (C++ `_GetFirstTargetPrimForRel`).
fn bound<T>(rel: &Relationship, view: fn(Prim) -> Result<Option<T>>) -> Result<Bound<T>> {
    if !rel.has_authored_targets()? {
        return Ok(Bound::Unauthored);
    }
    let Some(target) = rel.forwarded_targets()?.into_iter().next().filter(sdf::Path::is_prim) else {
        return Ok(Bound::Authored(None));
    };
    let prim = rel.stage().prim(target)?;
    Ok(Bound::Authored(if prim.is_valid()? { view(prim)? } else { None }))
}

/// The binding `bound` reads off the nearest of `binding`'s prim and its
/// ancestors that carries `BindingAPI` and authors one.
fn inherited<T>(binding: &BindingAPI, bound: fn(&BindingAPI) -> Result<Bound<T>>) -> Result<Option<T>> {
    let found = geom::nearest(binding.stage(), binding.path(), BindingAPI::from_prim, |ancestor| {
        Ok(match bound(ancestor)? {
            Bound::Authored(found) => Some(found),
            Bound::Unauthored => None,
        })
    })?;
    Ok(found.flatten())
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
        Skeleton::define(&stage, "/Char/Rig")?;
        let root = BindingAPI::apply(&stage.prim("/Char")?)?;
        root.create_skeleton_rel()?.add_target("/Char/Rig")?;

        let body = BindingAPI::apply(&stage.prim("/Char/Body")?)?;
        body.create_joint_indices_attr()?.set(Value::IntVec(vec![0, 1]))?;
        body.create_joint_weights_attr()?.set(Value::FloatVec(vec![1.0, 1.0]))?;
        body.create_skinning_method_attr()?.set(SkinningMethod::ClassicLinear)?;

        let body = BindingAPI::get(&stage, "/Char/Body")?.expect("BindingAPI");
        assert!(body.skeleton()?.is_none()); // not authored directly
        assert_eq!(
            body.inherited_skeleton()?.map(|s| s.path().clone()),
            Some(sdf::path("/Char/Rig")?)
        );
        assert_eq!(body.joint_indices()?, Some(vec![0, 1]));
        assert_eq!(body.joint_weights()?, Some(vec![1.0, 1.0]));
        assert_eq!(body.skinning_method()?, Some(SkinningMethod::ClassicLinear));
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
