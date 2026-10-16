//! Per-mesh skinning resolver — the static (time-independent) data
//! every skinning pipeline needs for one skinnable prim.
//!
//! Mirrors the static surface of Pixar's `UsdSkelSkinningQuery`. The
//! caller still owns the per-frame joint pose (in the bound
//! skeleton's joint order); this object handles the per-mesh details:
//!
//! - Remapping the skeleton-order skinning transforms through the
//!   mesh's `skel:joints` subset (when authored) via
//!   [`super::AnimMapper`].
//! - Telling skinning code whether the binding is rigid or per-vertex.
//! - Holding the `geomBindTransform` and `skinningMethod` so the
//!   caller doesn't have to re-read them per frame.
//! - Driving the [`super::skinning`] math against the right inputs.

use std::borrow::Cow;

use openusd::usd::Attribute;
use openusd::{Error, Result, gf, sdf};

use super::anim_mapper::AnimMapper;
use super::binding::SkelBinding;
use super::skinning::{has_shape, skin_normals, skin_points, skin_transform};
use super::{InfluenceInterpolation, SkinningMethod};
use crate::SchemaError;
use crate::geom::{self, Primvar};

/// Resolver bundle for one skinnable prim.
///
/// Build with [`SkinningResolver::new`] from a [`SkelBinding`], which also
/// pre-computes the joint-subset remapping ([`AnimMapper`]) from the bound
/// skeleton's joint order. After construction the resolver is read-only and
/// can be reused across frames.
#[derive(Debug, Clone)]
pub struct SkinningResolver {
    prim: sdf::Path,
    joint_indices: Vec<i32>,
    joint_weights: Vec<f32>,
    /// The interpolation and `elementSize` the joint-influence primvars share,
    /// or `None` when they are not bound consistently.
    influences: Option<(InfluenceInterpolation, usize)>,
    skinning_method: SkinningMethod,
    /// Mapper from the bound skeleton's joint order into the mesh's effective
    /// joint order. Identity (with `is_identity() == true`) when `skel:joints`
    /// isn't authored. Its `target_len()` is the effective mesh-side joint
    /// count (`skel:joints.len()` when a subset was authored, else the
    /// skeleton's joint count).
    mapper: AnimMapper,
    /// Cached `geomBindTransform`. Spec default = identity.
    geom_bind_transform: gf::Mat4d,
}

impl SkinningResolver {
    /// Build a resolver from the binding properties `binding` resolved for its
    /// prim. The joint influences count only when both primvars are bound, with
    /// equal positive `elementSize` and equal `constant` or `vertex`
    /// interpolation (C++ `UsdSkelSkinningQuery`'s constructor).
    pub fn new(binding: &SkelBinding) -> Result<Self, SchemaError> {
        let properties = &binding.properties;
        // TODO(perf): every prim bound to one skeleton re-reads its joint order.
        let skeleton_joint_order = binding.skeleton.joint_paths()?;
        let joint_subset: Option<Vec<String>> = properties.joints.as_ref().map(Attribute::cast).transpose()?.flatten();
        // No subset authored → skinning transforms feed straight through; an
        // identity mapper keeps callers on one code path. An authored empty
        // subset maps no joints.
        let mapper = AnimMapper::new(
            &skeleton_joint_order,
            joint_subset.as_ref().unwrap_or(&skeleton_joint_order),
        );
        let indices = properties.joint_indices.clone().map(Primvar::new);
        let weights = properties.joint_weights.clone().map(Primvar::new);
        Ok(Self {
            prim: binding.prim.path().clone(),
            joint_indices: match &indices {
                Some(indices) => indices.flattened::<Vec<i32>>(None)?.unwrap_or_default(),
                None => Vec::new(),
            },
            joint_weights: match &weights {
                Some(weights) => joint_weights(weights)?,
                None => Vec::new(),
            },
            influences: influences(indices.as_ref(), weights.as_ref())?,
            skinning_method: value(properties.skinning_method.as_ref())?.unwrap_or_default(),
            mapper,
            geom_bind_transform: value(properties.geom_bind_transform.as_ref())?.unwrap_or(gf::Mat4d::IDENTITY),
        })
    }

    /// Borrow the path of the skinned prim.
    pub fn prim(&self) -> &sdf::Path {
        &self.prim
    }

    /// `true` unless the joint influences are bound with `vertex`
    /// interpolation (C++ `IsRigidlyDeformed`): every point shares one set of
    /// influences, and the prim can be skinned by a single 4×4 (see
    /// [`rigid_transform`](Self::rigid_transform)). A prim without joint
    /// influences is rigid too, and skins through none of the methods here.
    pub fn is_rigidly_deformed(&self) -> bool {
        self.influences
            .is_none_or(|(interpolation, _)| interpolation == InfluenceInterpolation::Constant)
    }

    /// Number of `(joint, weight)` pairs per skinned element. For per-vertex
    /// bindings, "element" is a vertex; for rigid bindings, the count applies
    /// to the mesh as a whole.
    pub fn influences_per_component(&self) -> usize {
        self.influences.map_or(1, |(_, element_size)| element_size)
    }

    /// `true` when the prim's joint influences are bound and their primvar
    /// metadata is consistent (C++ `HasJointInfluences`).
    pub fn has_joint_influences(&self) -> bool {
        self.influences.is_some()
    }

    /// Effective joint order length on the mesh side. Equal to the bound
    /// `Skeleton.joints` count when `skel:joints` isn't authored; otherwise the
    /// `skel:joints` length.
    pub fn joint_order_len(&self) -> usize {
        self.mapper.target_len()
    }

    /// Cached `geomBindTransform` — identity when unauthored.
    pub fn geom_bind_transform(&self) -> gf::Mat4d {
        self.geom_bind_transform
    }

    /// Authored skinning method. Spec default is
    /// [`SkinningMethod::ClassicLinear`]. The skinning methods answer `None`
    /// for `dualQuaternion`, which is not ported yet.
    pub fn skinning_method(&self) -> SkinningMethod {
        self.skinning_method
    }

    /// Remap skinning transforms from the bound skeleton's joint order into the
    /// mesh's effective order. A copy when no `skel:joints` subset was
    /// authored. Missing joints (a target joint that isn't in the bound
    /// skeleton — rare but legal) get [`gf::Mat4d::IDENTITY`]. `None` unless
    /// `skel_skinning_xforms` holds one transform per skeleton joint.
    pub fn remap_transforms(&self, skel_skinning_xforms: &[gf::Mat4d]) -> Option<Vec<gf::Mat4d>> {
        let mut mesh_xforms = vec![gf::Mat4d::IDENTITY; self.mapper.target_len()];
        self.mapper
            .remap_into(skel_skinning_xforms, &mut mesh_xforms)
            .then_some(mesh_xforms)
    }

    /// Skin `points` through this binding's joint influences, using
    /// `skel_skinning_xforms` in the bound skeleton's joint order (C++
    /// `ComputeSkinnedPoints`). Constant influences apply to every point.
    ///
    /// `None` where the influences cannot skin `points`: they are not bound,
    /// their arrays do not fit `points`, or an index names no joint. `None`
    /// also when `skel_skinning_xforms` holds other than one transform per
    /// skeleton joint, and for a `dualQuaternion` skinning method.
    pub fn skinned_points(&self, points: &[gf::Vec3f], skel_skinning_xforms: &[gf::Mat4d]) -> Option<Vec<gf::Vec3f>> {
        let mesh_xforms = self.remap_transforms(skel_skinning_xforms)?;
        let (indices, weights) = self.varying_influences(points.len())?;
        skin_points(
            self.skinning_method,
            points,
            &indices,
            &weights,
            self.influences_per_component(),
            self.geom_bind_transform,
            &mesh_xforms,
        )
    }

    /// Skin `normals` through the same influences as
    /// [`skinned_points`](Self::skinned_points), under the same conditions
    /// (C++ `ComputeSkinnedNormals`), through the inverse-transpose of each
    /// transform. Each result is normalised.
    pub fn skinned_normals(&self, normals: &[gf::Vec3f], skel_skinning_xforms: &[gf::Mat4d]) -> Option<Vec<gf::Vec3f>> {
        let mesh_xforms = self.remap_transforms(skel_skinning_xforms)?;
        let (indices, weights) = self.varying_influences(normals.len())?;
        skin_normals(
            self.skinning_method,
            normals,
            &indices,
            &weights,
            self.influences_per_component(),
            self.geom_bind_transform,
            &mesh_xforms,
        )
    }

    /// The single 4×4 to apply to a rigidly deformed prim's local-to-world
    /// transform (C++ `ComputeSkinnedTransform`).
    ///
    /// `None` for a prim whose influences are not constant, not bound, sized to
    /// other than one element, or name a joint that does not exist, when
    /// `skel_skinning_xforms` holds other than one transform per skeleton
    /// joint, and for a `dualQuaternion` skinning method. The transform is
    /// skinned as [`skin_transform_lbs`](super::skinning::skin_transform_lbs)
    /// describes.
    pub fn rigid_transform(&self, skel_skinning_xforms: &[gf::Mat4d]) -> Option<gf::Mat4d> {
        let (InfluenceInterpolation::Constant, _) = self.joint_influences()? else {
            return None;
        };
        let mesh_xforms = self.remap_transforms(skel_skinning_xforms)?;
        skin_transform(
            self.skinning_method,
            &self.joint_indices,
            &self.joint_weights,
            self.geom_bind_transform,
            &mesh_xforms,
        )
    }

    /// The bound influences, where their arrays agree in length, hold whole
    /// elements, and hold exactly one element when constant (C++
    /// `ComputeJointInfluences`).
    fn joint_influences(&self) -> Option<(InfluenceInterpolation, usize)> {
        let (interpolation, element_size) = self.influences?;
        let len = self.joint_indices.len();
        let fits = len == self.joint_weights.len()
            && has_shape(len, element_size)
            && (interpolation == InfluenceInterpolation::Vertex || len == element_size);
        fits.then_some((interpolation, element_size))
    }

    /// The joint indices and weights for `count` points, with constant
    /// influences repeated for each point (C++
    /// `ComputeVaryingJointInfluences`), or `None` where they do not fit.
    fn varying_influences(&self, count: usize) -> Option<Influences<'_>> {
        match self.joint_influences()? {
            // TODO(perf): constant influences skin every point through one
            // blended transform; expanding them repeats the same blend per
            // point.
            (InfluenceInterpolation::Constant, _) => Some((
                Cow::Owned(self.joint_indices.repeat(count)),
                Cow::Owned(self.joint_weights.repeat(count)),
            )),
            (InfluenceInterpolation::Vertex, element_size) => (self.joint_indices.len() == count * element_size)
                .then_some((
                    Cow::Borrowed(&self.joint_indices[..]),
                    Cow::Borrowed(&self.joint_weights[..]),
                )),
        }
    }
}

/// Joint indices and weights, one run of `elementSize` pairs per point.
type Influences<'a> = (Cow<'a, [i32]>, Cow<'a, [f32]>);

/// The interpolation and `elementSize` the joint-influence primvars share, or
/// `None` when either is unbound or the two disagree, the element size is not
/// positive, or the interpolation is neither `constant` nor `vertex`.
fn influences(indices: Option<&Primvar>, weights: Option<&Primvar>) -> Result<Option<(InfluenceInterpolation, usize)>> {
    let (Some(indices), Some(weights)) = (indices, weights) else {
        return Ok(None);
    };
    let element_size = indices.element_size()?;
    if element_size <= 0 || element_size != weights.element_size()? {
        return Ok(None);
    }
    let interpolation = interpolation_of(indices)?;
    if interpolation != interpolation_of(weights)? {
        return Ok(None);
    }
    Ok(interpolation.map(|interpolation| (interpolation, element_size as usize)))
}

/// The influence interpolation the `interpolation` metadata on `primvar` names,
/// `constant` where none is authored, and `None` for any other token (C++
/// `UsdGeomPrimvar::GetInterpolation`, which answers the authored token).
fn interpolation_of(primvar: &Primvar) -> Result<Option<InfluenceInterpolation>> {
    Ok(
        match primvar
            .attribute()
            .metadata::<sdf::Value>(geom::tokens::INTERPOLATION)?
        {
            None => Some(InfluenceInterpolation::Constant),
            Some(sdf::Value::Token(token)) => InfluenceInterpolation::from_token(token),
            Some(_) => None,
        },
    )
}

/// The value `attribute` holds, where it is bound and holds one.
fn value<T>(attribute: Option<&Attribute>) -> Result<Option<T>>
where
    T: sdf::FromValue,
    T::Error: Into<Error>,
{
    Ok(attribute.map(Attribute::get).transpose()?.flatten())
}

/// The joint weights `weights` holds, flattened through its indices, and empty
/// when unauthored. The schema declares `float[]`. Weights authored as
/// `double[]` are narrowed to `f32`.
fn joint_weights(weights: &Primvar) -> Result<Vec<f32>, SchemaError> {
    Ok(match weights.flattened::<sdf::Value>(None)? {
        Some(sdf::Value::FloatVec(weights)) => weights,
        Some(sdf::Value::DoubleVec(weights)) => weights.into_iter().map(|weight| weight as f32).collect(),
        _ => Vec::new(),
    })
}
