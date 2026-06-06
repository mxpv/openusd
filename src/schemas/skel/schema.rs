//! The UsdSkel prim and applied-API views.
//!
//! [`SkelRoot`] and [`Skeleton`] are [`geom::Boundable`](crate::schemas::geom::Boundable) prims;
//! [`SkelAnimation`] and [`BlendShape`] are plain typed prims; [`SkelBindingAPI`]
//! is the single-apply API wiring skinnable geometry to a skeleton.
//!
//! The decoded getters (`joints()`, `bind_transforms()`, …) own the numeric
//! coercion the toolkit needs: matrices are row-major flattened `[f64; 16]`,
//! quaternions stay in USD's `(w, x, y, z)` order, and half-precision storage
//! is widened to `f32`.

use anyhow::Result;

use crate::sdf::{self, Value, Variability};
use crate::usd::{Attribute, Prim, Relationship, Stage};

use super::impl_skel_schema;
use super::tokens as tok;
use super::{InfluenceInterpolation, SkinningMethod};
use crate::schemas::common::{get_typed, get_with_api};

/// The enclosing scope beneath which skeletal posing and skinning apply (C++
/// `UsdSkelRoot`) — a [`geom::Boundable`](crate::schemas::geom::Boundable) prim. USD recommends authoring its
/// `extent` (via the inherited [`extent_attr`](crate::schemas::geom::Boundable::extent_attr))
/// so consumers can avoid computing skinned bounds at runtime.
#[derive(Clone, derive_more::Deref)]
pub struct SkelRoot(Prim);

impl SkelRoot {
    /// Author a `def SkelRoot` prim at `path` (C++ `UsdSkelRoot::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SKEL_ROOT)?))
    }

    /// Wrap `path` as a `SkelRoot` if it is typed `SkelRoot`
    /// (C++ `UsdSkelRoot::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SKEL_ROOT).map(|o| o.map(Self))
    }
}

impl_skel_schema!(boundable SkelRoot);

/// A skeleton: joint topology plus bind and rest poses (C++ `UsdSkelSkeleton`),
/// a [`geom::Boundable`](crate::schemas::geom::Boundable) prim. `joints[i]` is the path-encoded name of joint
/// `i`; `bind_transforms[i]` / `rest_transforms[i]` align with it.
#[derive(Clone, derive_more::Deref)]
pub struct Skeleton(Prim);

impl Skeleton {
    /// Author a `def Skeleton` prim at `path` (C++ `UsdSkelSkeleton::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SKELETON)?))
    }

    /// Wrap `path` as a `Skeleton` if it is typed `Skeleton`
    /// (C++ `UsdSkelSkeleton::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SKELETON).map(|o| o.map(Self))
    }

    /// The path-encoded joint hierarchy, e.g. `["Root", "Root/Hip"]`.
    /// C++ `UsdSkelSkeleton::GetJointsAttr`.
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?` (a
    /// [`sdf::Value::TokenVec`]).
    pub fn joints_attr(&self) -> Attribute {
        self.attribute(tok::A_JOINTS)
    }

    /// Author `joints` (`uniform token[]`) (C++ `CreateJointsAttr`).
    pub fn create_joints_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_JOINTS, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Optional per-joint display names (C++ `GetJointNamesAttr`).
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn joint_names_attr(&self) -> Attribute {
        self.attribute(tok::A_JOINT_NAMES)
    }

    /// Author `jointNames` (`uniform token[]`) (C++ `CreateJointNamesAttr`).
    pub fn create_joint_names_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_JOINT_NAMES, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Per-joint bind pose in world space (C++ `GetBindTransformsAttr`).
    ///
    /// Type `uniform matrix4d[]`. Fetch with `get::<sdf::Value>()?` (a
    /// [`sdf::Value::Matrix4dVec`]).
    pub fn bind_transforms_attr(&self) -> Attribute {
        self.attribute(tok::A_BIND_TRANSFORMS)
    }

    /// Author `bindTransforms` (`uniform matrix4d[]`)
    /// (C++ `CreateBindTransformsAttr`).
    pub fn create_bind_transforms_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_BIND_TRANSFORMS, "matrix4d[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Per-joint rest pose in joint-local (parent-relative) space
    /// (C++ `GetRestTransformsAttr`).
    ///
    /// Type `uniform matrix4d[]`. Fetch with `get::<sdf::Value>()?` (a
    /// [`sdf::Value::Matrix4dVec`]).
    pub fn rest_transforms_attr(&self) -> Attribute {
        self.attribute(tok::A_REST_TRANSFORMS)
    }

    /// Author `restTransforms` (`uniform matrix4d[]`)
    /// (C++ `CreateRestTransformsAttr`).
    pub fn create_rest_transforms_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_REST_TRANSFORMS, "matrix4d[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Decoded `joints` token array (empty when unauthored).
    pub fn joints(&self) -> Result<Vec<String>> {
        token_vec(&self.joints_attr())
    }

    /// Decoded `bindTransforms` as row-major flattened 4×4 matrices.
    pub fn bind_transforms(&self) -> Result<Vec<[f64; 16]>> {
        mat4_vec(&self.bind_transforms_attr())
    }

    /// Decoded `restTransforms` as row-major flattened 4×4 matrices.
    pub fn rest_transforms(&self) -> Result<Vec<[f64; 16]>> {
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
            .map(|p| p.rsplit_once('/').map(|(_, n)| n).unwrap_or(p).to_string())
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

impl_skel_schema!(boundable Skeleton);

/// Time-sampled joint transforms and blend-shape weights (C++
/// `UsdSkelAnimation`). The per-frame arrays are read through
/// [`SkelAnimQuery`](super::SkelAnimQuery), which evaluates them at a stage
/// time; this view exposes the attribute handles and the static ordering.
#[derive(Clone, derive_more::Deref)]
pub struct SkelAnimation(Prim);

impl SkelAnimation {
    /// Author a `def SkelAnimation` prim at `path`
    /// (C++ `UsdSkelAnimation::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_SKEL_ANIMATION)?))
    }

    /// Wrap `path` as a `SkelAnimation` if it is typed `SkelAnimation`
    /// (C++ `UsdSkelAnimation::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_SKEL_ANIMATION).map(|o| o.map(Self))
    }

    /// The animation's own joint ordering (need not match the bound
    /// skeleton's). C++ `UsdSkelAnimation::GetJointsAttr`.
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn joints_attr(&self) -> Attribute {
        self.attribute(tok::A_JOINTS)
    }

    /// Author `joints` (`uniform token[]`) (C++ `CreateJointsAttr`).
    pub fn create_joints_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_JOINTS, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Names of the blend shapes whose weights are animated.
    /// C++ `UsdSkelAnimation::GetBlendShapesAttr`.
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn blend_shapes_attr(&self) -> Attribute {
        self.attribute(tok::A_BLEND_SHAPES)
    }

    /// Author `blendShapes` (`uniform token[]`) (C++ `CreateBlendShapesAttr`).
    pub fn create_blend_shapes_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_BLEND_SHAPES, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Per-joint translations (C++ `GetTranslationsAttr`). Time-sampled.
    ///
    /// Type `float3[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn translations_attr(&self) -> Attribute {
        self.attribute(tok::A_TRANSLATIONS)
    }

    /// Author `translations` (`float3[]`) (C++ `CreateTranslationsAttr`).
    pub fn create_translations_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_TRANSLATIONS, "float3[]")?
            .set_custom(false)?)
    }

    /// Per-joint rotations as quaternions in `(w, x, y, z)` order
    /// (C++ `GetRotationsAttr`). Time-sampled.
    ///
    /// Type `quatf[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn rotations_attr(&self) -> Attribute {
        self.attribute(tok::A_ROTATIONS)
    }

    /// Author `rotations` (`quatf[]`) (C++ `CreateRotationsAttr`).
    pub fn create_rotations_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_ROTATIONS, "quatf[]")?.set_custom(false)?)
    }

    /// Per-joint scales (C++ `GetScalesAttr`, authored `half3[]`). Time-sampled.
    ///
    /// Type `half3[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn scales_attr(&self) -> Attribute {
        self.attribute(tok::A_SCALES)
    }

    /// Author `scales` (`half3[]`) (C++ `CreateScalesAttr`).
    pub fn create_scales_attr(&self) -> Result<Attribute> {
        Ok(self.create_attribute(tok::A_SCALES, "half3[]")?.set_custom(false)?)
    }

    /// Per-blend-shape weights, parallel to `blendShapes` (C++
    /// `GetBlendShapeWeightsAttr`). Time-sampled.
    ///
    /// Type `float[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn blend_shape_weights_attr(&self) -> Attribute {
        self.attribute(tok::A_BLEND_SHAPE_WEIGHTS)
    }

    /// Author `blendShapeWeights` (`float[]`)
    /// (C++ `CreateBlendShapeWeightsAttr`).
    pub fn create_blend_shape_weights_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_BLEND_SHAPE_WEIGHTS, "float[]")?
            .set_custom(false)?)
    }

    /// Decoded `joints` token array.
    pub fn joints(&self) -> Result<Vec<String>> {
        token_vec(&self.joints_attr())
    }

    /// Decoded `blendShapes` token array.
    pub fn blend_shapes(&self) -> Result<Vec<String>> {
        token_vec(&self.blend_shapes_attr())
    }
}

impl_skel_schema!(typed SkelAnimation);

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
    pub offsets: Vec<[f32; 3]>,
    /// Optional `inbetweens:<name>:normalOffsets`. Empty when unauthored.
    pub normal_offsets: Vec<[f32; 3]>,
}

/// Per-vertex position / normal offsets defining a deformation target (C++
/// `UsdSkelBlendShape`), optionally with inbetween shapes. Sparse via
/// `pointIndices` (`offsets[i]` applies to vertex `pointIndices[i]`), dense
/// when `pointIndices` is empty.
#[derive(Clone, derive_more::Deref)]
pub struct BlendShape(Prim);

impl BlendShape {
    /// Author a `def BlendShape` prim at `path`
    /// (C++ `UsdSkelBlendShape::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_BLEND_SHAPE)?))
    }

    /// Wrap `path` as a `BlendShape` if it is typed `BlendShape`
    /// (C++ `UsdSkelBlendShape::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_BLEND_SHAPE).map(|o| o.map(Self))
    }

    /// Required per-vertex position offsets (C++ `GetOffsetsAttr`).
    ///
    /// Type `uniform vector3f[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn offsets_attr(&self) -> Attribute {
        self.attribute(tok::A_OFFSETS)
    }

    /// Author `offsets` (`uniform vector3f[]`) (C++ `CreateOffsetsAttr`).
    pub fn create_offsets_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_OFFSETS, "vector3f[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Optional per-vertex normal offsets, same length as `offsets`
    /// (C++ `GetNormalOffsetsAttr`).
    ///
    /// Type `uniform vector3f[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn normal_offsets_attr(&self) -> Attribute {
        self.attribute(tok::A_NORMAL_OFFSETS)
    }

    /// Author `normalOffsets` (`uniform vector3f[]`)
    /// (C++ `CreateNormalOffsetsAttr`).
    pub fn create_normal_offsets_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_NORMAL_OFFSETS, "vector3f[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Optional point indices mapping `offsets[i]` to the vertex it deforms;
    /// empty for dense blend shapes (C++ `GetPointIndicesAttr`).
    ///
    /// Type `uniform int[]`. Fetch with `get::<sdf::Value>()?` (an
    /// [`sdf::Value::IntVec`]).
    pub fn point_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_POINT_INDICES)
    }

    /// Author `pointIndices` (`uniform int[]`) (C++ `CreatePointIndicesAttr`).
    pub fn create_point_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_POINT_INDICES, "int[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Decoded `offsets`.
    pub fn offsets(&self) -> Result<Vec<[f32; 3]>> {
        vec3f_vec(&self.offsets_attr())
    }

    /// Decoded `normalOffsets`.
    pub fn normal_offsets(&self) -> Result<Vec<[f32; 3]>> {
        vec3f_vec(&self.normal_offsets_attr())
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
        let props = self.stage().prim_at(self.path().clone()).property_names()?;
        for name in &props {
            let Some(rest) = name.strip_prefix(tok::NS_INBETWEENS) else {
                continue;
            };
            // Skip the per-inbetween `normalOffsets` siblings — folded into the
            // inbetween that names them.
            if rest.contains(':') {
                continue;
            }
            let attr = self.attribute(name);
            let offsets = vec3f_vec(&attr)?;
            let weight = match attr.get_metadata::<Value>(tok::META_WEIGHT)? {
                Some(Value::Float(f)) => Some(f),
                Some(Value::Double(d)) => Some(d as f32),
                _ => None,
            };
            let normal_offsets_name = format!("{}{rest}:{}", tok::NS_INBETWEENS, tok::A_NORMAL_OFFSETS);
            let normal_offsets = if props.iter().any(|n| n == &normal_offsets_name) {
                vec3f_vec(&self.attribute(&normal_offsets_name))?
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

impl_skel_schema!(typed BlendShape);

/// Binds skinnable geometry to a skeleton (C++ `UsdSkelBindingAPI`,
/// single-apply): joint influences, blend shapes, the `skel:skeleton` /
/// `skel:animationSource` relationships, and the bind transform / skinning
/// method. `skel:skeleton` and `skel:animationSource` are inheritable down
/// namespace; [`Self::inherited_skeleton`] / [`Self::inherited_animation_source`]
/// resolve the nearest-ancestor binding.
#[derive(Clone, derive_more::Deref)]
pub struct SkelBindingAPI(Prim);

impl SkelBindingAPI {
    /// Apply `SkelBindingAPI` to the prim at `path`
    /// (C++ `UsdSkelBindingAPI::Apply`). The prim is opened as `over`.
    pub fn apply(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(
            stage.override_prim(path)?.add_applied_schema(tok::API_SKEL_BINDING)?,
        ))
    }

    /// Wrap `path` as a `SkelBindingAPI` if it carries `SkelBindingAPI`
    /// (C++ `UsdSkelBindingAPI::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_with_api(stage, path, &[tok::API_SKEL_BINDING]).map(|o| o.map(Self))
    }

    /// The `skel:skeleton` relationship (C++ `GetSkeletonRel`).
    pub fn skeleton_rel(&self) -> Relationship {
        self.relationship(tok::REL_SKEL_SKELETON)
    }

    /// Author the `skel:skeleton` relationship (C++ `CreateSkeletonRel`).
    pub fn create_skeleton_rel(&self) -> Result<Relationship> {
        Ok(self.create_relationship(tok::REL_SKEL_SKELETON)?.set_custom(false)?)
    }

    /// The `skel:animationSource` relationship (C++ `GetAnimationSourceRel`).
    pub fn animation_source_rel(&self) -> Relationship {
        self.relationship(tok::REL_SKEL_ANIMATION_SOURCE)
    }

    /// Author the `skel:animationSource` relationship
    /// (C++ `CreateAnimationSourceRel`).
    pub fn create_animation_source_rel(&self) -> Result<Relationship> {
        Ok(self
            .create_relationship(tok::REL_SKEL_ANIMATION_SOURCE)?
            .set_custom(false)?)
    }

    /// The `skel:blendShapeTargets` relationship — the BlendShape prims, one
    /// per `skel:blendShapes` entry (C++ `GetBlendShapeTargetsRel`).
    pub fn blend_shape_targets_rel(&self) -> Relationship {
        self.relationship(tok::REL_SKEL_BLEND_SHAPE_TARGETS)
    }

    /// Author the `skel:blendShapeTargets` relationship
    /// (C++ `CreateBlendShapeTargetsRel`).
    pub fn create_blend_shape_targets_rel(&self) -> Result<Relationship> {
        Ok(self
            .create_relationship(tok::REL_SKEL_BLEND_SHAPE_TARGETS)?
            .set_custom(false)?)
    }

    /// Per-influence joint indices, indexing the bound skeleton's joints (or
    /// `skel:joints` when authored). C++ `GetJointIndicesAttr`.
    ///
    /// Type `int[]`. Fetch with `get::<sdf::Value>()?` (an
    /// [`sdf::Value::IntVec`]).
    pub fn joint_indices_attr(&self) -> Attribute {
        self.attribute(tok::A_JOINT_INDICES)
    }

    /// Author `primvars:skel:jointIndices` (`int[]`)
    /// (C++ `CreateJointIndicesAttr`).
    pub fn create_joint_indices_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_JOINT_INDICES, "int[]")?
            .set_custom(false)?)
    }

    /// Per-influence joint weights, parallel to `jointIndices`
    /// (C++ `GetJointWeightsAttr`).
    ///
    /// Type `float[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn joint_weights_attr(&self) -> Attribute {
        self.attribute(tok::A_JOINT_WEIGHTS)
    }

    /// Author `primvars:skel:jointWeights` (`float[]`)
    /// (C++ `CreateJointWeightsAttr`).
    pub fn create_joint_weights_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_JOINT_WEIGHTS, "float[]")?
            .set_custom(false)?)
    }

    /// Optional per-mesh subset / reordering of the bound skeleton's joints;
    /// when present, `jointIndices` index into this list (C++ `GetJointsAttr`).
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn joints_attr(&self) -> Attribute {
        self.attribute(tok::A_SKEL_JOINTS)
    }

    /// Author `skel:joints` (`uniform token[]`) (C++ `CreateJointsAttr`).
    pub fn create_joints_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SKEL_JOINTS, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Names of the blend shapes this mesh uses, parallel to
    /// `blendShapeTargets` (C++ `GetBlendShapesAttr`).
    ///
    /// Type `uniform token[]`. Fetch with `get::<sdf::Value>()?`.
    pub fn blend_shapes_attr(&self) -> Attribute {
        self.attribute(tok::A_SKEL_BLEND_SHAPES)
    }

    /// Author `skel:blendShapes` (`uniform token[]`)
    /// (C++ `CreateBlendShapesAttr`).
    pub fn create_blend_shapes_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SKEL_BLEND_SHAPES, "token[]")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

    /// Bind-time world-space transform of the skinned primitive; spec default
    /// is the identity (C++ `GetGeomBindTransformAttr`).
    ///
    /// Type `matrix4d`. Fetch with `get::<[f64; 16]>()?`.
    pub fn geom_bind_transform_attr(&self) -> Attribute {
        self.attribute(tok::A_GEOM_BIND_TRANSFORM)
    }

    /// Author `primvars:skel:geomBindTransform` (`matrix4d`)
    /// (C++ `CreateGeomBindTransformAttr`).
    pub fn create_geom_bind_transform_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_GEOM_BIND_TRANSFORM, "matrix4d")?
            .set_custom(false)?)
    }

    /// How the bound joints deform the mesh (`classicLinear` / `dualQuaternion`).
    /// C++ `GetSkinningMethodAttr`.
    ///
    /// Type `uniform token`. Fetch with
    /// `get::<`[`SkinningMethod`](super::SkinningMethod)`>()?`.
    pub fn skinning_method_attr(&self) -> Attribute {
        self.attribute(tok::A_SKINNING_METHOD)
    }

    /// Author `primvars:skel:skinningMethod` (`uniform token`)
    /// (C++ `CreateSkinningMethodAttr`).
    pub fn create_skinning_method_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_SKINNING_METHOD, "token")?
            .set_custom(false)?
            .set_variability(Variability::Uniform)?)
    }

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
        inherited_rel(self.stage(), self.path(), tok::REL_SKEL_SKELETON)
    }

    /// Resolve the inherited `skel:animationSource`; same rules as
    /// [`Self::inherited_skeleton`].
    pub fn inherited_animation_source(&self) -> Result<Option<sdf::Path>> {
        inherited_rel(self.stage(), self.path(), tok::REL_SKEL_ANIMATION_SOURCE)
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
        token_vec(&self.joints_attr())
    }

    /// Decoded `skel:blendShapes`.
    pub fn blend_shapes(&self) -> Result<Vec<String>> {
        token_vec(&self.blend_shapes_attr())
    }

    /// Decoded `skel:blendShapeTargets` prim paths.
    pub fn blend_shape_targets(&self) -> Result<Vec<sdf::Path>> {
        self.blend_shape_targets_rel().targets()
    }

    /// Decoded `primvars:skel:geomBindTransform`; `None` when unauthored (the
    /// spec default is the identity matrix).
    pub fn geom_bind_transform(&self) -> Result<Option<[f64; 16]>> {
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
                .get_metadata::<Value>(tok::META_ELEMENT_SIZE)?
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
            .get_metadata::<InfluenceInterpolation>(tok::META_INTERPOLATION)?
            .unwrap_or_default())
    }
}

impl_skel_schema!(single_api SkelBindingAPI);

/// Walk `prim` and its ancestors for the nearest authored `rel_name` target.
/// `skel:skeleton` / `skel:animationSource` inherit down namespace regardless
/// of where `SkelBindingAPI` is formally applied.
fn inherited_rel(stage: &Stage, prim: &sdf::Path, rel_name: &str) -> Result<Option<sdf::Path>> {
    let mut cur = prim.clone();
    loop {
        let rel = cur.append_property(rel_name)?;
        if let Some(target) = stage.relationship_at(rel).targets()?.into_iter().next() {
            return Ok(Some(target));
        }
        match cur.parent() {
            Some(p) if !cur.is_abs_root() => cur = p,
            _ => return Ok(None),
        }
    }
}

/// Decode a `token[]` / `string[]` attribute (empty when unauthored).
fn token_vec(attr: &Attribute) -> Result<Vec<String>> {
    Ok(match attr.get::<Value>()? {
        Some(Value::TokenVec(v) | Value::StringVec(v)) => v,
        _ => Vec::new(),
    })
}

/// Decode a `matrix4d[]` attribute (empty when unauthored).
fn mat4_vec(attr: &Attribute) -> Result<Vec<[f64; 16]>> {
    Ok(match attr.get::<Value>()? {
        Some(Value::Matrix4dVec(v)) => v,
        _ => Vec::new(),
    })
}

/// Decode a `vector3f[]` attribute, widening `double` / `half` storage to
/// `f32` (empty when unauthored).
fn vec3f_vec(attr: &Attribute) -> Result<Vec<[f32; 3]>> {
    Ok(match attr.get::<Value>()? {
        Some(Value::Vec3fVec(v)) => v,
        Some(Value::Vec3dVec(v)) => v.into_iter().map(|a| [a[0] as f32, a[1] as f32, a[2] as f32]).collect(),
        Some(Value::Vec3hVec(v)) => v
            .into_iter()
            .map(|a| [a[0].to_f32(), a[1].to_f32(), a[2].to_f32()])
            .collect(),
        _ => Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::geom::Boundable;

    #[test]
    fn skeleton_roundtrip_and_topology() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let skel = Skeleton::define(&stage, "/Rig")?;
        skel.create_joints_attr()?.set(Value::TokenVec(vec![
            "Root".into(),
            "Root/Hip".into(),
            "Root/Hip/Knee".into(),
        ]))?;

        let skel = Skeleton::get(&stage, "/Rig")?.expect("Skeleton");
        assert_eq!(skel.joints()?, vec!["Root", "Root/Hip", "Root/Hip/Knee"]);
        assert_eq!(skel.joint_parent_indices()?, vec![None, Some(0), Some(1)]);
        assert_eq!(skel.joint_short_names()?, vec!["Root", "Hip", "Knee"]);
        assert_eq!(skel.map_anim_joints(&["Root/Hip".to_string()])?, vec![Some(1)]);
        Ok(())
    }

    #[test]
    fn skel_root_is_boundable() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let root = SkelRoot::define(&stage, "/Char")?;
        root.create_extent_attr()?
            .set(Value::Vec3fVec(vec![[-1.0, 0.0, -1.0], [1.0, 2.0, 1.0]]))?;
        let root = SkelRoot::get(&stage, "/Char")?.expect("SkelRoot");
        assert_eq!(
            root.extent_attr().get::<Value>()?.and_then(|v| v.try_as_vec_3f_vec()),
            Some(vec![[-1.0, 0.0, -1.0], [1.0, 2.0, 1.0]])
        );
        Ok(())
    }

    #[test]
    fn binding_roundtrip_and_inheritance() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        // Skeleton bound on the root; influences on the mesh.
        let root = SkelBindingAPI::apply(&stage, "/Char")?;
        root.create_skeleton_rel()?.add_target(sdf::path("/Char/Rig")?)?;

        let body = SkelBindingAPI::apply(&stage, "/Char/Body")?;
        body.create_joint_indices_attr()?.set(Value::IntVec(vec![0, 1]))?;
        body.create_joint_weights_attr()?.set(Value::FloatVec(vec![1.0, 1.0]))?;
        body.create_skinning_method_attr()?.set(SkinningMethod::ClassicLinear)?;

        let body = SkelBindingAPI::get(&stage, "/Char/Body")?.expect("SkelBindingAPI");
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
        let stage = Stage::builder().in_memory("anon.usda")?;
        let bs = BlendShape::define(&stage, "/Smile")?;
        bs.create_offsets_attr()?.set(Value::Vec3fVec(vec![[0.0, 0.1, 0.0]]))?;
        bs.create_point_indices_attr()?.set(Value::IntVec(vec![0]))?;
        // Author an inbetween at weight 0.5.
        let inb = bs
            .create_attribute("inbetweens:half", "vector3f[]")?
            .set_custom(false)?;
        inb.set(Value::Vec3fVec(vec![[0.0, 0.04, 0.0]]))?
            .set_metadata(tok::META_WEIGHT, Value::Float(0.5))?;

        let bs = BlendShape::get(&stage, "/Smile")?.expect("BlendShape");
        assert_eq!(bs.offsets()?, vec![[0.0, 0.1, 0.0]]);
        assert_eq!(bs.point_indices()?, vec![0]);
        let inbetweens = bs.inbetweens()?;
        assert_eq!(inbetweens.len(), 1);
        assert_eq!(inbetweens[0].name, "half");
        assert_eq!(inbetweens[0].weight, Some(0.5));
        assert_eq!(inbetweens[0].offsets, vec![[0.0, 0.04, 0.0]]);
        Ok(())
    }
}
