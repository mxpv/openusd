//! What a `UsdSkel` view's properties decode to, and the helpers that author
//! them.
//!
//! A skeleton's joints are a `token[]` of paths that the object model reads as
//! a topology; a binding's skeleton and animation are relationship targets
//! inherited down namespace. These are the readers the rest of the family is
//! built on, over the generated views.

use openusd::usd::{Prim, Relationship, SchemaBase, TimeCode};
use openusd::{Result, gf, sdf};

use super::anim_query::transform_components;
use super::skinning::{decompose_transforms, make_transforms};
use super::{Animation, AnimationSchema, BindingAPI, Root, Skeleton, SkeletonSchema, tokens};
use crate::SchemaError;
use crate::geom::{self, Interpolation, Primvar, PrimvarBuilder, PrimvarsAPI};

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

    /// `primvars:skel:jointIndices` as a primvar (C++
    /// `GetJointIndicesPrimvar`).
    pub fn joint_indices_primvar(&self) -> Primvar {
        Primvar::new(self.joint_indices_attr())
    }

    /// `primvars:skel:jointWeights` as a primvar (C++
    /// `GetJointWeightsPrimvar`).
    pub fn joint_weights_primvar(&self) -> Primvar {
        Primvar::new(self.joint_weights_attr())
    }

    /// Author `primvars:skel:jointIndices` as an `int[]` primvar (C++
    /// `CreateJointIndicesPrimvar`), with `constant` interpolation where
    /// `constant` is set and `vertex` otherwise. `element_size`, where given,
    /// is the number of influences on each point; below one it fails with
    /// [`SchemaError::InvalidElementSize`].
    pub fn create_joint_indices_primvar(
        &self,
        constant: bool,
        element_size: impl Into<Option<i32>>,
    ) -> Result<Primvar, SchemaError> {
        let primvars = PrimvarsAPI::from_prim_unchecked(self.prim().clone());
        let builder = primvars.primvar_builder(tokens::PRIMVARS_SKEL_JOINT_INDICES, sdf::ValueTypeName::INT_ARRAY);
        influences(builder, constant, element_size.into()).build()
    }

    /// Author `primvars:skel:jointWeights` as a `float[]` primvar (C++
    /// `CreateJointWeightsPrimvar`), with the interpolation and element size
    /// [`create_joint_indices_primvar`](Self::create_joint_indices_primvar)
    /// takes.
    pub fn create_joint_weights_primvar(
        &self,
        constant: bool,
        element_size: impl Into<Option<i32>>,
    ) -> Result<Primvar, SchemaError> {
        let primvars = PrimvarsAPI::from_prim_unchecked(self.prim().clone());
        let builder = primvars.primvar_builder(tokens::PRIMVARS_SKEL_JOINT_WEIGHTS, sdf::ValueTypeName::FLOAT_ARRAY);
        influences(builder, constant, element_size.into()).build()
    }

    /// Bind the whole prim to the joint at index `joint` of `skel:joints`
    /// with `weight` (C++ `SetRigidJointInfluence`): both influence primvars
    /// constant, of element size one, holding the one index and weight. The
    /// two primvars are authored in one transaction.
    ///
    /// A `joint` above `i32::MAX` is [`SchemaError::JointIndexOverflow`], and
    /// authors nothing. C++ authors the primvars before it rejects a negative
    /// index.
    pub fn set_rigid_joint_influence(&self, joint: usize, weight: f32) -> Result<(), SchemaError> {
        let index = i32::try_from(joint).map_err(|_| SchemaError::JointIndexOverflow {
            prim: self.path().clone(),
            joint,
        })?;
        self.stage().edit(|edit| {
            let prim = edit.prim(self.path().clone())?;
            let indices = PrimvarBuilder::in_edit(
                &prim,
                tokens::PRIMVARS_SKEL_JOINT_INDICES,
                sdf::ValueTypeName::INT_ARRAY,
            );
            influences(indices, true, Some(1))
                .set(sdf::Value::IntVec((vec![index]).into()))
                .build()?;
            let weights = PrimvarBuilder::in_edit(
                &prim,
                tokens::PRIMVARS_SKEL_JOINT_WEIGHTS,
                sdf::ValueTypeName::FLOAT_ARRAY,
            );
            influences(weights, true, Some(1))
                .set(sdf::Value::FloatVec((vec![weight]).into()))
                .build()?;
            Ok::<_, SchemaError>(())
        })
    }
}

impl Animation {
    /// The `joints` paths as text, in the order the animation's arrays list
    /// them; empty when unauthored.
    pub fn joint_paths(&self) -> Result<Vec<String>> {
        Ok(self.joints_attr().cast()?.unwrap_or_default())
    }

    /// The joint-local transforms at `time`, `None` being the default time,
    /// made from `translations`, `rotations` and `scales` (C++
    /// `GetTransforms`). `None` when one of the three holds no value at
    /// `time`, or they differ in length.
    pub fn transforms(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<Vec<gf::Mat4d>>> {
        Ok(transform_components(self, time.into())?
            .and_then(|(translations, rotations, scales)| make_transforms(&translations, &rotations, &scales)))
    }

    /// Author `xforms` at `time`, `None` being the default time, as the
    /// `translations`, `rotations` and `scales` they decompose into (C++
    /// `SetTransforms`). The three are authored in one transaction, the
    /// scales rounded to `half3`.
    ///
    /// `false`, with nothing authored, when one of `xforms` does not
    /// decompose ([`decompose_transform`](super::skinning::decompose_transform)).
    pub fn set_transforms(&self, xforms: &[gf::Mat4d], time: impl Into<Option<TimeCode>>) -> Result<bool, SchemaError> {
        let Some((translations, rotations, scales)) = decompose_transforms(xforms) else {
            return Ok(false);
        };
        let half = gf::f16::from_f32;
        let scales = scales
            .into_iter()
            .map(|scale| gf::vec3h(half(scale.x), half(scale.y), half(scale.z)))
            .collect();
        let time = time.into();
        self.stage().edit(|edit| -> Result<(), SchemaError> {
            let components = [
                self.translations_attr_builder()
                    .set_at(sdf::Value::Vec3fVec(translations.into()), time),
                self.rotations_attr_builder()
                    .set_at(sdf::Value::QuatfVec(rotations.into()), time),
                self.scales_attr_builder().set_at(sdf::Value::Vec3hVec(scales), time),
            ];
            for component in components {
                component.in_edit(edit).build()?;
            }
            Ok(())
        })?;
        Ok(true)
    }
}

impl Root {
    /// `prim` itself where it is a `Root`, else its nearest `Root` ancestor
    /// (C++ `UsdSkelRoot::Find`).
    pub fn find(prim: &Prim) -> Result<Option<Root>> {
        geom::nearest(prim.stage(), prim.path(), Root::from_prim, |root| {
            Ok(Some(root.clone()))
        })
    }
}

/// `builder` with the interpolation and element size of a joint influence
/// primvar: `constant` or `vertex`, and `element_size` where one is given.
fn influences(builder: PrimvarBuilder<'_>, constant: bool, element_size: Option<i32>) -> PrimvarBuilder<'_> {
    let builder = builder.interpolation(match constant {
        true => Interpolation::Constant,
        false => Interpolation::Vertex,
    });
    match element_size {
        Some(element_size) => builder.element_size(element_size),
        None => builder,
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
        body.create_joint_indices_attr()?
            .set(Value::IntVec((vec![0, 1]).into()))?;
        body.create_joint_weights_attr()?
            .set(Value::FloatVec((vec![1.0, 1.0]).into()))?;
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
