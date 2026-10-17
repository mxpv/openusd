//! What a `UsdSkel` view's properties decode to.
//!
//! A skeleton's joints are a `token[]` of paths that the object model reads as
//! a topology; a binding's skeleton and animation are relationship targets
//! inherited down namespace. These are the readers the rest of the family is
//! built on, over the generated views.

use openusd::Result;
use openusd::sdf;
use openusd::usd::{Prim, Relationship, SchemaBase};

use super::{Animation, AnimationSchema, BindingAPI, Skeleton, SkeletonSchema};
use crate::geom;

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
    /// The active animation the skeleton binds, inherited down namespace to
    /// the Skeleton prim ([`BindingAPI::inherited_animation_source`]; C++
    /// `UsdSkelCache` binds no animation from an inactive prim).
    pub fn animation_source(&self) -> Result<Option<Animation>> {
        match BindingAPI::from_prim_unchecked(self.prim().clone()).inherited_animation_source()? {
            Some(anim) if anim.is_active()? => Ok(Some(anim)),
            _ => Ok(None),
        }
    }

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
    use openusd::Result;
    use openusd::sdf::Value;

    use super::*;
    use crate::skel::{BindingAPI, SkinningMethod};

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
}
