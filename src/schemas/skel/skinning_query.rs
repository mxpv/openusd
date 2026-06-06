//! Per-mesh skinning resolver — the static (time-independent) data
//! every skinning pipeline needs for one prim carrying
//! `SkelBindingAPI`.
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

use anyhow::Result;

use crate::gf;
use crate::usd::SchemaBase;

use super::anim_mapper::AnimMapper;
use super::schema::SkelBindingAPI;
use super::skinning::{rigid_skinning_transform, skin_normals_lbs, skin_points_lbs};
use super::{InfluenceInterpolation, SkinningMethod};

/// Resolver bundle for one skinnable prim.
///
/// Build with [`SkinningResolver::from_binding`], passing the bound skeleton's
/// joint order so the joint-subset remapping ([`AnimMapper`]) can be
/// pre-computed. After construction the resolver is read-only and can be reused
/// across frames.
#[derive(Debug, Clone)]
pub struct SkinningResolver {
    prim: String,
    joint_indices: Vec<i32>,
    joint_weights: Vec<f32>,
    interpolation: InfluenceInterpolation,
    skinning_method: SkinningMethod,
    elements_per_element: i32,
    /// Mapper from the bound skeleton's joint order into the mesh's effective
    /// joint order. Identity (with `is_identity() == true`) when `skel:joints`
    /// isn't authored. Its `target_len()` is the effective mesh-side joint
    /// count (`skel:joints.len()` when a subset was authored, else the
    /// skeleton's joint count).
    mapper: AnimMapper,
    /// Cached `geomBindTransform`. Spec default = identity.
    geom_bind_transform: gf::Matrix4d,
}

impl SkinningResolver {
    /// Build a resolver from `binding`. `skeleton_joint_order` is the bound
    /// `Skeleton.joints` array, used to derive the skeleton→mesh joint remap
    /// when `skel:joints` is authored.
    pub fn from_binding(binding: &SkelBindingAPI, skeleton_joint_order: &[String]) -> Result<Self> {
        let joint_subset = binding.joint_subset()?;
        // No subset authored → skinning transforms feed straight through; an
        // identity mapper keeps callers on one code path.
        let mapper = if joint_subset.is_empty() {
            AnimMapper::new(skeleton_joint_order, skeleton_joint_order)
        } else {
            AnimMapper::new(skeleton_joint_order, &joint_subset)
        };
        Ok(Self {
            prim: binding.path().as_str().to_string(),
            joint_indices: binding.joint_indices()?,
            joint_weights: binding.joint_weights()?,
            interpolation: binding.interpolation()?,
            skinning_method: binding.skinning_method()?,
            elements_per_element: binding.elements_per_element()?,
            mapper,
            geom_bind_transform: binding.geom_bind_transform()?.unwrap_or(gf::Matrix4d::IDENTITY),
        })
    }

    /// Borrow the prim path the binding came from.
    pub fn prim(&self) -> &str {
        &self.prim
    }

    /// `true` when this prim is authored with `constant` interpolation — every
    /// vertex shares the same joint influences and the mesh can be skinned by a
    /// single 4×4 (see [`compute_rigid_transform`](Self::compute_rigid_transform)).
    pub fn is_rigidly_deformed(&self) -> bool {
        self.interpolation == InfluenceInterpolation::Constant
    }

    /// Number of `(joint, weight)` pairs per skinned element. For per-vertex
    /// bindings, "element" is a vertex; for rigid bindings, the count applies
    /// to the mesh as a whole.
    pub fn num_influences_per_component(&self) -> usize {
        self.elements_per_element.max(1) as usize
    }

    /// `true` if joint influences and weights were authored (i.e. skinning is
    /// actually meaningful for this prim).
    pub fn has_joint_influences(&self) -> bool {
        !self.joint_indices.is_empty() && !self.joint_weights.is_empty()
    }

    /// Effective joint order length on the mesh side. Equal to the bound
    /// `Skeleton.joints` count when `skel:joints` isn't authored; otherwise the
    /// `skel:joints` length.
    pub fn joint_order_len(&self) -> usize {
        self.mapper.target_len()
    }

    /// Cached `geomBindTransform` — identity when unauthored.
    pub fn geom_bind_transform(&self) -> gf::Matrix4d {
        self.geom_bind_transform
    }

    /// Authored skinning method. Spec default is
    /// [`SkinningMethod::ClassicLinear`]; consumers without dual-quaternion
    /// support typically fall back to classic LBS even when the prim authors
    /// `dualQuaternion`.
    pub fn skinning_method(&self) -> SkinningMethod {
        self.skinning_method
    }

    /// Remap skinning transforms from the bound skeleton's joint order into the
    /// mesh's effective order. No-op when no `skel:joints` subset was authored.
    ///
    /// Walks the pre-computed mapper indices once with no intermediate buffers,
    /// so this is cheap to call per frame. Missing joints (a target joint that
    /// isn't in the bound skeleton — rare but legal) get [`gf::Matrix4d::IDENTITY`].
    pub fn remap_skinning_xforms(&self, skel_skinning_xforms: &[gf::Matrix4d]) -> Vec<gf::Matrix4d> {
        if self.mapper.is_identity() {
            return skel_skinning_xforms.to_vec();
        }
        (0..self.mapper.target_len())
            .map(|t| match self.mapper.source_index(t) {
                Some(i) => skel_skinning_xforms[i],
                None => gf::Matrix4d::IDENTITY,
            })
            .collect()
    }

    /// Skin `points` through this binding's per-vertex influences, using
    /// `skel_skinning_xforms` (in the bound skeleton's joint order; this method
    /// handles the remap to mesh order).
    ///
    /// Panics when called on a rigidly-deformed binding — use
    /// [`compute_rigid_transform`](Self::compute_rigid_transform) for that case.
    pub fn compute_skinned_points(
        &self,
        points: &[gf::Vec3f],
        skel_skinning_xforms: &[gf::Matrix4d],
    ) -> Vec<gf::Vec3f> {
        assert!(
            !self.is_rigidly_deformed(),
            "compute_skinned_points called on rigidly-deformed binding"
        );
        let mesh_xforms = self.remap_skinning_xforms(skel_skinning_xforms);
        skin_points_lbs(
            points,
            &self.joint_indices,
            &self.joint_weights,
            self.num_influences_per_component(),
            self.geom_bind_transform,
            &mesh_xforms,
        )
    }

    /// Skin normals through the same per-vertex influences as
    /// [`compute_skinned_points`](Self::compute_skinned_points). Normalises each
    /// result; see [`super::skinning::skin_normals_lbs`] for the caveat about
    /// inverse-transpose under non-uniform scale.
    pub fn compute_skinned_normals(
        &self,
        normals: &[gf::Vec3f],
        skel_skinning_xforms: &[gf::Matrix4d],
    ) -> Vec<gf::Vec3f> {
        assert!(
            !self.is_rigidly_deformed(),
            "compute_skinned_normals called on rigidly-deformed binding"
        );
        let mesh_xforms = self.remap_skinning_xforms(skel_skinning_xforms);
        skin_normals_lbs(
            normals,
            &self.joint_indices,
            &self.joint_weights,
            self.num_influences_per_component(),
            self.geom_bind_transform,
            &mesh_xforms,
        )
    }

    /// Compute the single 4×4 that should be applied to a rigidly-deformed
    /// mesh's local-to-world transform.
    ///
    /// Panics when called on a per-vertex binding — use
    /// [`compute_skinned_points`](Self::compute_skinned_points) /
    /// [`compute_skinned_normals`](Self::compute_skinned_normals) there.
    pub fn compute_rigid_transform(&self, skel_skinning_xforms: &[gf::Matrix4d]) -> gf::Matrix4d {
        assert!(
            self.is_rigidly_deformed(),
            "compute_rigid_transform called on per-vertex binding"
        );
        let mesh_xforms = self.remap_skinning_xforms(skel_skinning_xforms);
        rigid_skinning_transform(
            &self.joint_indices,
            &self.joint_weights,
            self.num_influences_per_component(),
            self.geom_bind_transform,
            &mesh_xforms,
        )
    }
}
