//! A skinnable prim's resolved binding, skinned at any time (C++
//! `UsdSkelSkinningQuery`).
//!
//! The query holds the binding properties the prim resolves, inherited or its
//! own, and reads the joint influences and the geom bind transform at
//! whatever time it is asked for. What it decides at construction is a
//! snapshot: which properties are bound, the skinning method, the influence
//! interpolation and element size, and the joint and blend-shape mappers
//! built from `skel:joints`, `skel:blendShapes` and the bound skeleton's and
//! animation's orders. After an edit to any of those, build a new query.

use openusd::usd::{Attribute, Prim, Relationship, TimeCode};
use openusd::{Result, gf, sdf};

use super::anim_mapper::AnimMapper;
use super::binding::BindingProperties;
use super::skeleton_query::SkeletonQuery;
use super::skinning::{Pose, PrimPose, has_shape, joints_extent};
use super::{InfluenceInterpolation, SkinningMethod};
use crate::SchemaError;
use crate::geom::{BoundableSchema, Primvar};

/// Joint indices and weights, one run of
/// [`SkinningQuery::influences_per_component`] pairs per point. Answered by
/// [`SkinningQuery::joint_influences`].
pub type JointInfluences = (Vec<i32>, Vec<f32>);

/// One skinnable prim's resolved binding.
///
/// A [`Cache`](super::Cache) builds one for each skinnable prim it populates
/// ([`Cache::skinning_query`](super::Cache::skinning_query)).
#[derive(Debug, Clone)]
pub struct SkinningQuery {
    prim: Prim,
    joint_indices: Option<Primvar>,
    joint_weights: Option<Primvar>,
    geom_bind_transform: Option<Attribute>,
    blend_shape_targets: Option<Relationship>,
    /// The skinning method, or `None` for a token that names no method this
    /// crate knows.
    skinning_method: Option<SkinningMethod>,
    /// The interpolation and `elementSize` the joint-influence primvars share,
    /// or `None` when they are not bound consistently.
    influences: Option<(InfluenceInterpolation, usize)>,
    /// The number of joints of the bound skeleton, zero without one.
    skeleton_joints: usize,
    /// `skel:joints` and the mapping from the skeleton's joint order onto it,
    /// where `skel:joints` is authored.
    joints: Option<(Vec<String>, AnimMapper)>,
    /// `skel:blendShapes` and the mapping from the animation's blend-shape
    /// order onto it, where `skel:blendShapes` is authored.
    blend_shapes: Option<(Vec<String>, AnimMapper)>,
}

impl SkinningQuery {
    /// The query over the binding `properties` resolved for `prim` (C++
    /// `UsdSkelSkinningQuery`'s constructor). `skeleton` is the query of the
    /// skeleton bound to `prim`, for its joint order and its animation's
    /// blend-shape order, where that skeleton has one; without it both orders
    /// are empty, as C++ passes them, so a joint subset maps no joints and
    /// the blend-shape mapper maps nothing from the animation.
    ///
    /// The joint influences count only when both primvars are bound, with
    /// equal positive `elementSize` and equal `constant` or `vertex`
    /// interpolation. The skinning method is read once, at the default time,
    /// as C++ reads it.
    pub(super) fn new(
        prim: Prim,
        properties: &BindingProperties,
        skeleton: Option<&SkeletonQuery>,
    ) -> Result<Self, SchemaError> {
        let skeleton_joints = skeleton.map_or(&[][..], SkeletonQuery::joint_order);
        let anim_blend_shapes = skeleton
            .and_then(SkeletonQuery::anim_query)
            .map_or(&[][..], |anim| anim.blend_shape_order());
        let joint_indices = properties.joint_indices.clone().map(Primvar::new);
        let joint_weights = properties.joint_weights.clone().map(Primvar::new);
        Ok(Self {
            prim,
            influences: influences(joint_indices.as_ref(), joint_weights.as_ref())?,
            joint_indices,
            joint_weights,
            geom_bind_transform: properties.geom_bind_transform.clone(),
            blend_shape_targets: properties.blend_shape_targets.clone(),
            skinning_method: skinning_method(properties.skinning_method.as_ref())?,
            skeleton_joints: skeleton_joints.len(),
            joints: order(properties.joints.as_ref(), skeleton_joints)?,
            blend_shapes: order(properties.blend_shapes.as_ref(), anim_blend_shapes)?,
        })
    }

    /// The skinned prim.
    pub fn prim(&self) -> &Prim {
        &self.prim
    }

    /// `true` when the prim's joint influences are bound and their primvar
    /// metadata is consistent (C++ `HasJointInfluences`).
    pub fn has_joint_influences(&self) -> bool {
        self.influences.is_some()
    }

    /// `true` when the prim binds blend shapes: `skel:blendShapes` and
    /// `skel:blendShapeTargets` are both authored (C++ `HasBlendShapes`).
    pub fn has_blend_shapes(&self) -> bool {
        self.blend_shapes.is_some() && self.blend_shape_targets.is_some()
    }

    /// The interpolation of the joint influences: `constant` where they are
    /// not bound consistently, as for any primvar without one (C++
    /// `GetInterpolation`).
    pub fn interpolation(&self) -> InfluenceInterpolation {
        self.influences
            .map_or(InfluenceInterpolation::Constant, |(interpolation, _)| interpolation)
    }

    /// `true` unless the joint influences are bound with `vertex`
    /// interpolation (C++ `IsRigidlyDeformed`): every point shares one set of
    /// influences, and the prim can be skinned by a single 4×4 (see
    /// [`skinned_transform`](Self::skinned_transform)). A prim without joint
    /// influences is rigid too, and skins through none of the methods here.
    pub fn is_rigidly_deformed(&self) -> bool {
        self.interpolation() == InfluenceInterpolation::Constant
    }

    /// Number of `(joint, weight)` pairs per skinned element (C++
    /// `GetNumInfluencesPerComponent`). For per-vertex bindings, "element" is
    /// a vertex; for rigid bindings, the count applies to the mesh as a whole.
    pub fn influences_per_component(&self) -> usize {
        self.influences.map_or(1, |(_, element_size)| element_size)
    }

    /// The skinning method `primvars:skel:skinningMethod` names (C++
    /// `GetSkinningMethod`). An unauthored method, or a value that is not a
    /// token, is `classicLinear`, as C++ falls back. `None` for a token that
    /// names no method this crate knows, for which the skinning methods
    /// answer `None`.
    pub fn skinning_method(&self) -> Option<SkinningMethod> {
        self.skinning_method
    }

    /// The geom bind transform at `time`, `None` being the default time, and
    /// the identity where it is unbound (C++ `GetGeomBindTransform`).
    pub fn geom_bind_transform(&self, time: impl Into<Option<TimeCode>>) -> Result<gf::Mat4d> {
        // TODO(perf): a geom bind transform that is not time-varying could be
        // read once.
        let time = time.into();
        Ok(self
            .geom_bind_transform
            .as_ref()
            .map(|transform| transform.get_at(time))
            .transpose()?
            .flatten()
            .unwrap_or(gf::Mat4d::IDENTITY))
    }

    /// `skel:joints`, where it is authored (C++ `GetJointOrder`).
    pub fn joint_order(&self) -> Option<&[String]> {
        self.joints.as_ref().map(|(names, _)| names.as_slice())
    }

    /// The mapping from the skeleton's joint order onto `skel:joints`, where
    /// `skel:joints` is authored (C++ `GetJointMapper`).
    pub fn joint_mapper(&self) -> Option<&AnimMapper> {
        self.joints.as_ref().map(|(_, mapper)| mapper)
    }

    /// `skel:blendShapes`, where it is authored (C++ `GetBlendShapeOrder`).
    pub fn blend_shape_order(&self) -> Option<&[String]> {
        self.blend_shapes.as_ref().map(|(names, _)| names.as_slice())
    }

    /// The mapping from the bound animation's blend-shape order onto
    /// `skel:blendShapes`, where `skel:blendShapes` is authored (C++
    /// `GetBlendShapeMapper`). It remaps the animation's weights into the
    /// order of `skel:blendShapeTargets`.
    pub fn blend_shape_mapper(&self) -> Option<&AnimMapper> {
        self.blend_shapes.as_ref().map(|(_, mapper)| mapper)
    }

    /// `skel:blendShapeTargets`, where it authors targets on the prim (C++
    /// `GetBlendShapeTargetsRel`).
    pub fn blend_shape_targets(&self) -> Option<&Relationship> {
        self.blend_shape_targets.as_ref()
    }

    /// Every time at which the joint influences or the geom bind transform
    /// are authored, ascending and without repeats (C++ `GetTimeSamples`).
    pub fn time_samples(&self) -> Result<Vec<f64>> {
        self.time_samples_in(f64::NEG_INFINITY..=f64::INFINITY)
    }

    /// The [`time_samples`](Self::time_samples) within `interval` (C++
    /// `GetTimeSamplesInInterval`). An indexed influence primvar contributes
    /// its indices' samples too.
    pub fn time_samples_in(&self, interval: impl Into<gf::Interval>) -> Result<Vec<f64>> {
        let mut attributes = Vec::new();
        for primvar in [&self.joint_indices, &self.joint_weights].into_iter().flatten() {
            attributes.extend(primvar.sampled_attributes()?);
        }
        attributes.extend(self.geom_bind_transform.clone());
        Attribute::unioned_time_samples_in(&attributes, interval)
    }

    /// The joint indices and weights at `time`, flattened through their
    /// primvar indices (C++ `ComputeJointInfluences`). `None` when the
    /// influences are not bound consistently, either has no value at `time`,
    /// or their arrays differ in length, do not split into runs of
    /// [`influences_per_component`](Self::influences_per_component), or hold
    /// other than one run when constant.
    pub fn joint_influences(&self, time: impl Into<Option<TimeCode>>) -> Result<Option<JointInfluences>, SchemaError> {
        // TODO(perf): influences that are not time-varying could be read and
        // flattened once; skinning points and then normals reads them twice.
        let (Some((interpolation, element_size)), Some(indices), Some(weights)) =
            (self.influences, &self.joint_indices, &self.joint_weights)
        else {
            return Ok(None);
        };
        let time = time.into();
        let (Some(indices), Some(weights)) = (indices.flattened::<Vec<i32>>(time)?, joint_weights(weights, time)?)
        else {
            return Ok(None);
        };
        let fits = indices.len() == weights.len()
            && has_shape(indices.len(), element_size)
            && (interpolation == InfluenceInterpolation::Vertex || indices.len() == element_size);
        Ok(fits.then_some((indices, weights)))
    }

    /// The joint influences at `time` for `count` points, constant influences
    /// repeated for each point (C++ `ComputeVaryingJointInfluences`). `None`
    /// where [`joint_influences`](Self::joint_influences) is, or when vertex
    /// influences hold other than one run per point.
    pub fn varying_joint_influences(
        &self,
        count: usize,
        time: impl Into<Option<TimeCode>>,
    ) -> Result<Option<JointInfluences>, SchemaError> {
        let Some((indices, weights)) = self.joint_influences(time)? else {
            return Ok(None);
        };
        Ok(if self.is_rigidly_deformed() {
            // TODO(perf): constant influences skin every point through one
            // blended transform, the one `skinned_transform` answers;
            // repeating them repeats the same blend per point.
            Some((indices.repeat(count), weights.repeat(count)))
        } else {
            (indices.len() == count * self.influences_per_component()).then_some((indices, weights))
        })
    }

    /// Skin `points` at `time` through the joint influences and `pose`, the
    /// skinning transforms in the bound skeleton's joint order (C++
    /// `ComputeSkinnedPoints`). Constant influences apply to every point.
    ///
    /// C++ takes the skinning transforms as an array. A [`Pose`] also keeps
    /// what each skinning method derives from them, made once for every prim
    /// skinned through it.
    ///
    /// `None` where [`varying_joint_influences`](Self::varying_joint_influences)
    /// is, when `pose` holds other than one transform per skeleton joint,
    /// when an influence names no joint, and for an unknown skinning method.
    pub fn skinned_points(
        &self,
        pose: &Pose,
        points: &[gf::Vec3f],
        time: impl Into<Option<TimeCode>>,
    ) -> Result<Option<Vec<gf::Vec3f>>, SchemaError> {
        self.skin_elements(PrimPose::skin_points, pose, points, time.into())
    }

    /// Skin `normals` at `time` through the same influences as
    /// [`skinned_points`](Self::skinned_points), under the same conditions
    /// (C++ `ComputeSkinnedNormals`), through the inverse-transpose of each
    /// transform. Each result is normalised.
    pub fn skinned_normals(
        &self,
        pose: &Pose,
        normals: &[gf::Vec3f],
        time: impl Into<Option<TimeCode>>,
    ) -> Result<Option<Vec<gf::Vec3f>>, SchemaError> {
        self.skin_elements(PrimPose::skin_normals, pose, normals, time.into())
    }

    /// The single 4×4 to apply to a rigidly deformed prim's local-to-world
    /// transform at `time` through `pose` (C++ `ComputeSkinnedTransform`),
    /// skinned as [`skin_transform`](super::skinning::skin_transform)
    /// describes for the skinning method.
    ///
    /// `None` for a prim whose influences are not constant, where
    /// [`joint_influences`](Self::joint_influences) is, when `pose` holds
    /// other than one transform per skeleton joint, when an influence names
    /// no joint, and for an unknown skinning method.
    /// A joint of `skel:joints` the skeleton lacks takes the identity, where
    /// C++ leaves the skeleton's transform at that index.
    pub fn skinned_transform(
        &self,
        pose: &Pose,
        time: impl Into<Option<TimeCode>>,
    ) -> Result<Option<gf::Mat4d>, SchemaError> {
        if !self.is_rigidly_deformed() {
            return Ok(None);
        }
        let time = time.into();
        let (Some(method), Some(pose)) = (self.skinning_method, self.prim_pose(pose)) else {
            return Ok(None);
        };
        let Some((indices, weights)) = self.joint_influences(time)? else {
            return Ok(None);
        };
        Ok(pose.skin_transform(method, &indices, &weights, self.geom_bind_transform(time)?))
    }

    /// How far the skinned prim may reach past its skeleton's joints at
    /// rest (C++ `ComputeExtentsPadding`): the largest distance, on any axis,
    /// by which `boundable`'s extent carried through the geom bind transform
    /// lies outside the box around `rest_skel_xforms`' pivots. Both are read
    /// at the earliest time. Zero where `boundable` authors no extent, where
    /// the prim lies within the joints' box, and for no joints, where C++
    /// pads by the width of an empty range.
    pub fn extents_padding(&self, rest_skel_xforms: &[gf::Mat4d], boundable: &impl BoundableSchema) -> Result<f32> {
        let Some(extent) = boundable.extent_at(TimeCode::EARLIEST)? else {
            return Ok(0.0);
        };
        let ([min, max], Some([joints_min, joints_max])) =
            (extent.as_slice(), joints_extent(rest_skel_xforms, 0.0, None))
        else {
            return Ok(0.0);
        };
        let prim = gf::Range3d::from([*min, *max]).transformed(self.geom_bind_transform(TimeCode::EARLIEST)?);
        let (prim_min, prim_max) = (prim.min().to_f32(), prim.max().to_f32());
        let below = joints_min - prim_min;
        let above = prim_max - joints_max;
        Ok([below.x, below.y, below.z, above.x, above.y, above.z]
            .into_iter()
            .fold(0.0, f32::max))
    }

    /// Skin `elements`, points or normals, at `time` through `skin` with the
    /// influences varying over them.
    fn skin_elements<'a>(
        &'a self,
        skin: SkinFn<'a>,
        pose: &'a Pose,
        elements: &[gf::Vec3f],
        time: Option<TimeCode>,
    ) -> Result<Option<Vec<gf::Vec3f>>, SchemaError> {
        let (Some(method), Some(pose)) = (self.skinning_method, self.prim_pose(pose)) else {
            return Ok(None);
        };
        let Some((indices, weights)) = self.varying_joint_influences(elements.len(), time)? else {
            return Ok(None);
        };
        Ok(skin(
            &pose,
            method,
            elements,
            &indices,
            &weights,
            self.influences_per_component(),
            self.geom_bind_transform(time)?,
        ))
    }

    /// `pose` in the order of `skel:joints`, where it is authored. A joint of
    /// `skel:joints` the skeleton lacks takes the identity. `None` unless
    /// `pose` holds one transform per skeleton joint.
    fn prim_pose<'a>(&'a self, pose: &'a Pose) -> Option<PrimPose<'a>> {
        if pose.xforms().len() != self.skeleton_joints {
            return None;
        }
        PrimPose::new(pose, self.joints.as_ref().map(|(_, mapper)| mapper))
    }
}

/// [`PrimPose::skin_points`] or [`PrimPose::skin_normals`].
type SkinFn<'a> =
    fn(&PrimPose<'a>, SkinningMethod, &[gf::Vec3f], &[i32], &[f32], usize, gf::Mat4d) -> Option<Vec<gf::Vec3f>>;

/// The skinning method `attribute` names, `classicLinear` where it is unbound
/// or holds no token, and `None` for a token that names no method.
fn skinning_method(attribute: Option<&Attribute>) -> Result<Option<SkinningMethod>> {
    Ok(
        match attribute.map(Attribute::get::<sdf::Value>).transpose()?.flatten() {
            Some(sdf::Value::Token(token)) => SkinningMethod::from_token(token),
            _ => Some(SkinningMethod::ClassicLinear),
        },
    )
}

/// The names `attribute` holds, where it is bound and holds them, with the
/// mapping from `source` onto them.
fn order(attribute: Option<&Attribute>, source: &[String]) -> Result<Option<(Vec<String>, AnimMapper)>> {
    Ok(attribute
        .map(Attribute::cast)
        .transpose()?
        .flatten()
        .map(|names: Vec<String>| {
            let mapper = AnimMapper::new(source, &names);
            (names, mapper)
        }))
}

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
    let interpolation = indices.interpolation_token()?;
    if interpolation != weights.interpolation_token()? {
        return Ok(None);
    }
    Ok(InfluenceInterpolation::from_token(interpolation).map(|interpolation| (interpolation, element_size as usize)))
}

/// The joint weights `weights` holds at `time`, flattened through its
/// indices, where it holds an array of weights. The schema declares
/// `float[]`. Weights authored as `double[]` are narrowed to `f32`.
fn joint_weights(weights: &Primvar, time: Option<TimeCode>) -> Result<Option<Vec<f32>>, SchemaError> {
    Ok(match weights.flattened::<sdf::Value>(time)? {
        Some(sdf::Value::FloatVec(weights)) => Some(weights),
        Some(sdf::Value::DoubleVec(weights)) => Some(weights.into_iter().map(|weight| weight as f32).collect()),
        _ => None,
    })
}
