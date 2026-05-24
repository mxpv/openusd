//! Decoded structs and enums returned by [`super::read`] functions.

use super::tokens::*;

/// `primvars:skel:skinningMethod` token values from `UsdSkelBindingAPI`.
///
/// The default when unauthored is [`SkinningMethod::ClassicLinear`] —
/// standard linear blend skinning. [`SkinningMethod::DualQuaternion`]
/// is the only other Pixar-defined value; consumers without DQ support
/// typically fall back to classic LBS.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SkinningMethod {
    #[default]
    ClassicLinear,
    DualQuaternion,
}

impl SkinningMethod {
    pub fn as_token(self) -> &'static str {
        match self {
            SkinningMethod::ClassicLinear => SKINNING_METHOD_CLASSIC_LINEAR,
            SkinningMethod::DualQuaternion => SKINNING_METHOD_DUAL_QUATERNION,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            SKINNING_METHOD_CLASSIC_LINEAR => SkinningMethod::ClassicLinear,
            SKINNING_METHOD_DUAL_QUATERNION => SkinningMethod::DualQuaternion,
            _ => return None,
        })
    }
}

/// Authored interpolation on the joint-influence primvars.
///
/// `Constant` encodes rigid skinning (one set of weights for the whole
/// prim). `Vertex` is per-point weights, the normal skinned case.
/// `Vertex` is the unauthored default — the only interpolation that
/// generally makes sense for per-vertex influence lists, and what
/// every UsdSkel example uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InfluenceInterpolation {
    Constant,
    #[default]
    Vertex,
}

impl InfluenceInterpolation {
    pub fn as_token(self) -> &'static str {
        match self {
            InfluenceInterpolation::Constant => INTERP_CONSTANT,
            InfluenceInterpolation::Vertex => INTERP_VERTEX,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            INTERP_CONSTANT => InfluenceInterpolation::Constant,
            INTERP_VERTEX => InfluenceInterpolation::Vertex,
            _ => return None,
        })
    }
}

/// Decoded `UsdSkelRoot` prim — the scope marker beneath which
/// skeletal processing applies.
///
/// `extent` is the authored bounding box on the SkelRoot (a `Boundable`).
/// USD recommends authoring it explicitly so consumers can avoid
/// computing skinned bounds at runtime; this reader does not synthesise
/// one when missing.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadSkelRoot {
    pub path: String,
    /// `extent` — `[min, max]` corners in the SkelRoot's local space.
    /// `None` when unauthored.
    pub extent: Option<[[f32; 3]; 2]>,
}

/// Decoded `UsdSkelSkeleton` prim.
///
/// `joints[i]` is the SdfPath-encoded name of joint `i`; parent links
/// are derived from the path encoding (see
/// [`ReadSkeleton::joint_parent_indices`]).
///
/// Index alignment is strict: `bind_transforms[i]` and
/// `rest_transforms[i]` correspond to `joints[i]`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadSkeleton {
    pub path: String,
    /// `joints` token array — path-encoded joint hierarchy.
    /// Example: `["Root", "Root/Hip", "Root/Hip/Knee"]`.
    pub joints: Vec<String>,
    /// `bindTransforms` — per-joint bind pose in *world space*.
    /// Row-major flattened 4×4. Empty when unauthored.
    pub bind_transforms: Vec<[f64; 16]>,
    /// `restTransforms` — per-joint rest pose in *joint-local space*
    /// (parent-relative). Row-major flattened 4×4. Empty when
    /// unauthored.
    pub rest_transforms: Vec<[f64; 16]>,
}

impl ReadSkeleton {
    /// Recover the parent index of each joint from the path encoding.
    /// `joints[i] = "A/B"` ⇒ parent is the index of `"A"`; a joint with
    /// no `/` is a root and gets `None`.
    pub fn joint_parent_indices(&self) -> Vec<Option<usize>> {
        let by_path: std::collections::HashMap<&str, usize> =
            self.joints.iter().enumerate().map(|(i, p)| (p.as_str(), i)).collect();
        self.joints
            .iter()
            .map(|p| {
                p.rsplit_once('/')
                    .map(|(parent, _)| parent)
                    .and_then(|parent_path| by_path.get(parent_path).copied())
            })
            .collect()
    }

    /// Last segment of each joint path — the bone's display name.
    /// Returns the full path verbatim if the joint has no `/`.
    pub fn joint_short_names(&self) -> Vec<&str> {
        self.joints
            .iter()
            .map(|p| p.rsplit_once('/').map(|(_, n)| n).unwrap_or(p.as_str()))
            .collect()
    }

    /// Map an animation's `joints` list to indices in this Skeleton's
    /// `joints` (by exact path match). Used to remap SkelAnimation data
    /// onto skeleton joint indices — the animation's ordering need not
    /// match the skeleton's.
    pub fn map_anim_joints(&self, anim_joints: &[String]) -> Vec<Option<usize>> {
        let by_path: std::collections::HashMap<&str, usize> =
            self.joints.iter().enumerate().map(|(i, p)| (p.as_str(), i)).collect();
        anim_joints.iter().map(|p| by_path.get(p.as_str()).copied()).collect()
    }
}

/// Decoded `UsdSkelAnimation` prim. Per-frame arrays live on
/// [`ReadSkelAnimation::translations`] / `rotations` / `scales` and
/// must each be the same length as `joints` (uniform sized rows).
///
/// `blend_shape_weights[t]` is parallel to `blend_shapes`.
///
/// Time samples are returned in their authored ordering (ascending
/// time-code). When an attribute carries only a `default` value
/// instead of `timeSamples`, the reader synthesises a single entry at
/// `t = 0.0` so consumers can treat both shapes uniformly.
#[derive(Debug, Clone, Default)]
pub struct ReadSkelAnimation {
    pub path: String,
    /// `joints` — the animation's own joint ordering. Does NOT have
    /// to match the bound Skeleton's `joints`; consumers remap by
    /// name via [`ReadSkeleton::map_anim_joints`].
    pub joints: Vec<String>,
    /// `blendShapes` — names of the blend shapes whose weights are
    /// animated.
    pub blend_shapes: Vec<String>,
    /// Per-time `translations` — flat per-joint `(x, y, z)` rows.
    /// Inner Vec length matches `joints.len()`.
    pub translations: Vec<(f64, Vec<[f32; 3]>)>,
    /// Per-time `rotations` — quaternions in USD's `(w, x, y, z)`
    /// order. Inner Vec length matches `joints.len()`.
    pub rotations: Vec<(f64, Vec<[f32; 4]>)>,
    /// Per-time `scales` — Pixar's schema authors `half3[]`; the
    /// reader widens to `f32` so consumers don't need the half crate.
    /// Inner Vec length matches `joints.len()`.
    pub scales: Vec<(f64, Vec<[f32; 3]>)>,
    /// Per-time `blendShapeWeights` — inner Vec length matches
    /// `blend_shapes.len()`.
    pub blend_shape_weights: Vec<(f64, Vec<f32>)>,
}

/// One in-between authored on a [`ReadBlendShape`].
///
/// Spec: `0 < weight < 1`. Endpoint weights are implicit — rest pose
/// at 0 and the primary BlendShape at 1, neither of which can be
/// authored as an inbetween. The reader surfaces whatever was authored
/// without enforcing the bound; callers that want strict spec
/// behaviour should filter.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadInbetween {
    /// Inbetween name — last segment of the `inbetweens:<name>`
    /// attribute path.
    pub name: String,
    /// `weight` metadata authored on the attribute. Required by spec;
    /// `None` indicates malformed authoring (we still return the entry
    /// so callers can warn).
    pub weight: Option<f32>,
    /// Inbetween position offsets. Parallel to the parent
    /// `BlendShape.pointIndices` layout.
    pub offsets: Vec<[f32; 3]>,
    /// Optional `normalOffsets`-style sibling, authored on the
    /// inbetween via `inbetweens:<name>:normalOffsets`. Empty when
    /// unauthored.
    pub normal_offsets: Vec<[f32; 3]>,
}

/// Decoded `UsdSkelBlendShape` prim.
///
/// Sparse via `point_indices` — `offsets[i]` applies to the mesh
/// vertex at `point_indices[i]`. Dense when `point_indices` is empty
/// (offsets[i] applies to vertex i).
#[derive(Debug, Clone, Default)]
pub struct ReadBlendShape {
    pub path: String,
    /// Required `offsets` (`vector3f[]`). One entry per affected
    /// vertex.
    pub offsets: Vec<[f32; 3]>,
    /// Optional `normalOffsets` (`vector3f[]`). Same length as
    /// `offsets`. Empty when unauthored.
    pub normal_offsets: Vec<[f32; 3]>,
    /// Optional `pointIndices` (`int[]`). Maps `offsets[i]` to the
    /// vertex it deforms. Empty for dense blend shapes.
    pub point_indices: Vec<i32>,
    /// Authored inbetween shapes (`inbetweens:<name>`). Empty when
    /// none. The reader does not sort by weight — preserve authoring
    /// order so the caller can mirror the source layer's spelling.
    pub inbetweens: Vec<ReadInbetween>,
}

/// Decoded `SkelBindingAPI` on a skinnable prim (typically a Mesh).
///
/// `skel:skeleton` and `skel:animationSource` are inheritable down
/// namespace — see [`super::read::read_inherited_skeleton`] and
/// [`super::read::read_inherited_animation_source`] for ancestor-walk
/// resolution.
#[derive(Debug, Clone, Default)]
pub struct ReadSkelBinding {
    /// Prim path of the skinned geometry.
    pub path: String,
    /// `skel:skeleton` rel target authored directly on this prim.
    /// `None` when the binding is inherited from an ancestor.
    pub skeleton: Option<String>,
    /// `skel:animationSource` rel target authored directly on this
    /// prim. `None` when inherited.
    pub animation_source: Option<String>,
    /// `primvars:skel:jointIndices` values.
    pub joint_indices: Vec<i32>,
    /// `primvars:skel:jointWeights` values. Parallel to
    /// `joint_indices`.
    pub joint_weights: Vec<f32>,
    /// `elementSize` on the joint-influence primvars — number of
    /// `(joint, weight)` pairs per element. Defaults to 1 when
    /// unauthored.
    pub elements_per_element: i32,
    /// Authored interpolation on the joint-influence primvars
    /// (`vertex` / `constant`). Defaults to `Vertex` when unauthored,
    /// which is the only interpolation that makes sense for a
    /// per-vertex influence list — UsdSkel restricts authored values
    /// to `vertex` or `constant`.
    pub interpolation: InfluenceInterpolation,
    /// `skel:joints` — optional per-mesh subset / reordering of the
    /// bound Skeleton's joints. When present, `joint_indices` index
    /// into this list, NOT into the Skeleton's `joints`.
    pub joint_subset: Vec<String>,
    /// `skel:blendShapes` — names of the blend shapes this mesh uses.
    /// Parallel-indexed to [`Self::blend_shape_targets`].
    pub blend_shapes: Vec<String>,
    /// `skel:blendShapeTargets` (rel) — absolute prim paths of the
    /// BlendShape prims, one per [`Self::blend_shapes`] entry.
    pub blend_shape_targets: Vec<String>,
    /// `primvars:skel:geomBindTransform` — bind-time world-space
    /// transform of the skinned primitive. Row-major flattened 4×4.
    /// `None` when unauthored — the spec default is the identity
    /// matrix.
    pub geom_bind_transform: Option<[f64; 16]>,
    /// `primvars:skel:skinningMethod`. Default is
    /// [`SkinningMethod::ClassicLinear`].
    pub skinning_method: SkinningMethod,
}

/// Result of [`super::read::find_skel_prims`] — a single-pass stage
/// walk that returns categorised path lists. Saves callers from
/// re-walking the stage for each schema family.
#[derive(Debug, Clone, Default)]
pub struct SkelPrims {
    pub skel_roots: Vec<String>,
    pub skeletons: Vec<String>,
    pub animations: Vec<String>,
    pub blend_shapes: Vec<String>,
    /// Prims with `SkelBindingAPI` applied (typically Meshes).
    pub bindings: Vec<String>,
}
