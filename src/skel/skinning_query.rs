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

use super::anim_mapper::AnimMapper;
use super::skinning::{rigid_skinning_transform, skin_normals_lbs, skin_points_lbs, IDENTITY_MAT4};
use super::types::{InfluenceInterpolation, ReadSkelBinding, SkinningMethod};

/// Resolver bundle for one skinnable prim.
///
/// Build with [`SkinningResolver::new`], passing the bound skeleton's
/// joint order so the joint-subset remapping ([`AnimMapper`]) can be
/// pre-computed. After construction the resolver is read-only and
/// can be reused across frames.
#[derive(Debug, Clone)]
pub struct SkinningResolver {
    binding: ReadSkelBinding,
    /// Mapper from the bound skeleton's joint order into the mesh's
    /// effective joint order. Identity (with `is_identity() == true`)
    /// when `skel:joints` isn't authored.
    mapper: AnimMapper,
    /// Effective mesh-side joint count — `binding.joint_subset.len()`
    /// when a subset was authored, otherwise the skeleton's joint
    /// count.
    num_mesh_joints: usize,
    /// Cached `geomBindTransform`. Spec default = identity.
    geom_bind_transform: [f64; 16],
}

impl SkinningResolver {
    /// Build a resolver for `binding`. `skeleton_joint_order` is the
    /// bound `Skeleton.joints` array, used to derive the
    /// skeleton→mesh joint remap when `skel:joints` is authored.
    pub fn new(binding: ReadSkelBinding, skeleton_joint_order: &[String]) -> Self {
        let mapper = if binding.joint_subset.is_empty() {
            // No subset authored — skinning transforms feed straight
            // through. Pre-build an identity mapper so callers always
            // hit the same code path.
            AnimMapper::new(skeleton_joint_order, skeleton_joint_order)
        } else {
            AnimMapper::new(skeleton_joint_order, &binding.joint_subset)
        };
        let num_mesh_joints = if binding.joint_subset.is_empty() {
            skeleton_joint_order.len()
        } else {
            binding.joint_subset.len()
        };
        let geom_bind_transform = binding.geom_bind_transform.unwrap_or(IDENTITY_MAT4);
        Self {
            binding,
            mapper,
            num_mesh_joints,
            geom_bind_transform,
        }
    }

    /// Borrow the underlying `SkelBindingAPI` data.
    pub fn binding(&self) -> &ReadSkelBinding {
        &self.binding
    }

    /// Borrow the prim path the binding came from.
    pub fn prim(&self) -> &str {
        &self.binding.path
    }

    /// `true` when this prim is authored with `constant` interpolation
    /// — every vertex shares the same joint influences and the mesh
    /// can be skinned by a single 4×4 (see [`compute_rigid_transform`]).
    pub fn is_rigidly_deformed(&self) -> bool {
        self.binding.interpolation == InfluenceInterpolation::Constant
    }

    /// Number of `(joint, weight)` pairs per skinned element. For
    /// per-vertex bindings, "element" is a vertex; for rigid bindings,
    /// the count applies to the mesh as a whole.
    pub fn num_influences_per_component(&self) -> usize {
        self.binding.elements_per_element.max(1) as usize
    }

    /// `true` if joint influences and weights were authored (i.e.
    /// skinning is actually meaningful for this prim).
    pub fn has_joint_influences(&self) -> bool {
        !self.binding.joint_indices.is_empty() && !self.binding.joint_weights.is_empty()
    }

    /// Effective joint order on the mesh side. Equal to the bound
    /// `Skeleton.joints` when `skel:joints` isn't authored; otherwise
    /// equal to `skel:joints`.
    pub fn joint_order_len(&self) -> usize {
        self.num_mesh_joints
    }

    /// Cached `geomBindTransform` — identity when unauthored.
    pub fn geom_bind_transform(&self) -> &[f64; 16] {
        &self.geom_bind_transform
    }

    /// Authored skinning method. Spec default is
    /// [`SkinningMethod::ClassicLinear`]; consumers without dual-
    /// quaternion support typically fall back to classic LBS even
    /// when the prim authors `dualQuaternion`.
    pub fn skinning_method(&self) -> SkinningMethod {
        self.binding.skinning_method
    }

    /// Remap skinning transforms from the bound skeleton's joint
    /// order into the mesh's effective order. No-op when no
    /// `skel:joints` subset was authored.
    ///
    /// Walks the pre-computed mapper indices once with no
    /// intermediate buffers, so this is cheap to call per frame.
    /// Missing joints (a target joint that isn't in the bound
    /// skeleton — rare but legal) get [`IDENTITY_MAT4`].
    pub fn remap_skinning_xforms(&self, skel_skinning_xforms: &[[f64; 16]]) -> Vec<[f64; 16]> {
        if self.mapper.is_identity() {
            return skel_skinning_xforms.to_vec();
        }
        (0..self.mapper.target_len())
            .map(|t| match self.mapper.source_index(t) {
                Some(i) => skel_skinning_xforms[i],
                None => IDENTITY_MAT4,
            })
            .collect()
    }

    /// Skin `points` through this binding's per-vertex influences,
    /// using `skel_skinning_xforms` (in the bound skeleton's joint
    /// order; this method handles the remap to mesh order).
    ///
    /// Panics when called on a rigidly-deformed binding — use
    /// [`compute_rigid_transform`] for that case.
    pub fn compute_skinned_points(&self, points: &[[f32; 3]], skel_skinning_xforms: &[[f64; 16]]) -> Vec<[f32; 3]> {
        assert!(
            !self.is_rigidly_deformed(),
            "compute_skinned_points called on rigidly-deformed binding"
        );
        let mesh_xforms = self.remap_skinning_xforms(skel_skinning_xforms);
        skin_points_lbs(
            points,
            &self.binding.joint_indices,
            &self.binding.joint_weights,
            self.num_influences_per_component(),
            &self.geom_bind_transform,
            &mesh_xforms,
        )
    }

    /// Skin normals through the same per-vertex influences as
    /// [`compute_skinned_points`]. Normalises each result; see
    /// [`super::skinning::skin_normals_lbs`] for the caveat about
    /// inverse-transpose under non-uniform scale.
    pub fn compute_skinned_normals(&self, normals: &[[f32; 3]], skel_skinning_xforms: &[[f64; 16]]) -> Vec<[f32; 3]> {
        assert!(
            !self.is_rigidly_deformed(),
            "compute_skinned_normals called on rigidly-deformed binding"
        );
        let mesh_xforms = self.remap_skinning_xforms(skel_skinning_xforms);
        skin_normals_lbs(
            normals,
            &self.binding.joint_indices,
            &self.binding.joint_weights,
            self.num_influences_per_component(),
            &self.geom_bind_transform,
            &mesh_xforms,
        )
    }

    /// Compute the single 4×4 that should be applied to a
    /// rigidly-deformed mesh's local-to-world transform.
    ///
    /// Panics when called on a per-vertex binding — use
    /// [`compute_skinned_points`] / [`compute_skinned_normals`] there.
    pub fn compute_rigid_transform(&self, skel_skinning_xforms: &[[f64; 16]]) -> [f64; 16] {
        assert!(
            self.is_rigidly_deformed(),
            "compute_rigid_transform called on per-vertex binding"
        );
        let mesh_xforms = self.remap_skinning_xforms(skel_skinning_xforms);
        rigid_skinning_transform(
            &self.binding.joint_indices,
            &self.binding.joint_weights,
            self.num_influences_per_component(),
            &self.geom_bind_transform,
            &mesh_xforms,
        )
    }
}
