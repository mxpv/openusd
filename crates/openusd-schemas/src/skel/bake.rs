//! Baking skinning and blend shapes into plain geometry (C++
//! `UsdSkelBakeSkinning`).
//!
//! [`bake_skinning`] computes the deformed `points` and `normals` of each
//! prim a [`Binding`] skins, and the skinned transform of each prim bound
//! rigidly, at every time its skeleton and its inputs are sampled. It writes
//! them into a layer as time samples and turns the binding's [`Root`] into an
//! `Xform`, so the prims then draw posed with no UsdSkel evaluation.
//! [`bake_roots`] bakes every binding beneath some roots into the edit
//! target's layer.

use std::cmp::Ordering;
use std::collections::HashSet;

use bitflags::bitflags;
use openusd::usd::{self, Attribute, EditTarget, Prim, PrimPredicate, SchemaBase, StageAuthoringError, TimeCode};
use openusd::{gf, sdf, tf};

use super::skinning::normal_transform;
use super::{
    AnimationSchema, Binding, BindingAPI, BlendShapeQuery, Cache, Pose, Root, SkeletonQuery, SkeletonSchema,
    SkinningQuery, SubShapeWeight,
};
use crate::SchemaError;
use crate::geom::{
    self, BBoxCache, Extent, Interpolation, Mesh, MeshSchema, ModelAPI, PointBased, PointBasedExt, PointBasedSchema,
    Purpose, XformCache, XformOpKind, Xformable,
};

bitflags! {
    /// The deformations a skinning bake applies (C++
    /// `UsdSkelBakeSkinningParms::DeformationFlags`).
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Deform: u8 {
        /// Skin `points` through the joints.
        const POINTS_WITH_SKINNING = 1 << 0;
        /// Skin `normals` through the joints.
        const NORMALS_WITH_SKINNING = 1 << 1;
        /// Skin the transform of a prim with constant joint influences.
        const XFORM_WITH_SKINNING = 1 << 2;
        /// Apply blend shapes to `points`.
        const POINTS_WITH_BLEND_SHAPES = 1 << 3;
        /// Apply blend shapes to `normals`.
        const NORMALS_WITH_BLEND_SHAPES = 1 << 4;
        /// Every joint skinning deformation.
        const SKINNING = Self::POINTS_WITH_SKINNING.bits()
            | Self::NORMALS_WITH_SKINNING.bits()
            | Self::XFORM_WITH_SKINNING.bits();
        /// Every blend-shape deformation.
        const BLEND_SHAPES = Self::POINTS_WITH_BLEND_SHAPES.bits() | Self::NORMALS_WITH_BLEND_SHAPES.bits();
        /// Every deformation.
        const ALL = Self::SKINNING.bits() | Self::BLEND_SHAPES.bits();
        /// The deformations that write `points`.
        const MODIFIES_POINTS = Self::POINTS_WITH_SKINNING.bits() | Self::POINTS_WITH_BLEND_SHAPES.bits();
        /// The deformations that write `normals`.
        const MODIFIES_NORMALS = Self::NORMALS_WITH_SKINNING.bits() | Self::NORMALS_WITH_BLEND_SHAPES.bits();
        /// The deformations that write the transform.
        const MODIFIES_XFORM = Self::XFORM_WITH_SKINNING.bits();
    }
}

/// How a skinning bake runs (C++ `UsdSkelBakeSkinningParms`, without the
/// bindings and layers [`bake_skinning`] takes beside it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BakeOptions {
    /// The deformations to bake.
    pub deform: Deform,
    /// Whether a point-based prim whose points are baked gets an `extent`
    /// baked from them. Without it the bake leaves every `extent` alone.
    pub update_extents: bool,
    /// Whether each model above a baked prim that has an `extentsHint` gets
    /// it recomputed. Without it the bake leaves every hint alone.
    pub update_extent_hints: bool,
    /// Whether every layer the bake wrote to is saved once the bake is done.
    pub save_layers: bool,
}

impl Default for BakeOptions {
    /// Every deformation, extents and extents hints updated, and the layers
    /// saved, as C++ defaults.
    fn default() -> Self {
        Self {
            deform: Deform::ALL,
            update_extents: true,
            update_extent_hints: true,
            save_layers: true,
        }
    }
}

/// Bake every binding beneath `roots` over `interval` into the layer of the
/// stage's edit target, with the default [`BakeOptions`] but for
/// [`save_layers`](BakeOptions::save_layers), which is off (C++
/// `UsdSkelBakeSkinning` over a `UsdSkelRoot` or a `UsdPrimRange`). The
/// bindings are found as [`Cache::skel_bindings`] finds them with
/// [`PrimPredicate::DEFAULT`], which leaves out instance proxies. A prim that
/// two of the roots reach, one nested in the other, bakes once, where C++
/// bakes it for each.
///
/// An instanced root is [`SchemaError::BakeInstanced`], roots of more than
/// one stage are [`SchemaError::BakeStages`], and the rest fails as
/// [`bake_skinning`] does. Each check runs before anything is written.
pub fn bake_roots(roots: &[Root], interval: impl Into<gf::Interval>) -> Result<(), SchemaError> {
    let Some(first) = roots.first() else {
        return Ok(());
    };
    let stage = first.stage();
    for root in roots {
        if root.stage() != stage {
            return Err(SchemaError::BakeStages {
                prim: root.path().clone(),
            });
        }
        if is_instanced(root.prim())? {
            return Err(SchemaError::BakeInstanced {
                prim: root.path().clone(),
            });
        }
    }
    let mut cache = Cache::new();
    let mut bindings = Vec::new();
    let mut seen = HashSet::new();
    for root in roots {
        cache.populate(root, PrimPredicate::DEFAULT)?;
        for mut binding in cache.skel_bindings(root, PrimPredicate::DEFAULT)? {
            binding
                .skinning_targets
                .retain(|target| seen.insert(target.prim().clone()));
            if !binding.skinning_targets.is_empty() {
                bindings.push(binding);
            }
        }
    }
    let target = stage.edit_target();
    let paired: Vec<_> = bindings
        .into_iter()
        .map(|binding| (binding, target.layer_identifier()))
        .collect();
    let options = BakeOptions {
        save_layers: false,
        ..BakeOptions::default()
    };
    bake_skinning(&paired, &options, interval)
}

/// Bake each binding's skinned prims into the layer paired with it, over
/// `interval` (C++ `UsdSkelBakeSkinning`).
///
/// Each prim takes the deformations `options` allows and it supports:
///
/// - With constant joint influences, the skinned transform: authored as
///   `xformOp:transform`, the only op in `xformOpOrder`, placing the prim in
///   its parent's space. A prim that resets the transform stack keeps the
///   reset first in the order, where C++ drops it while it still computes the
///   transform as if the parent were the identity. The prim's old ops stay,
///   out of the order.
/// - Otherwise, joint skinning of `points`, where they are authored, and of
///   `normals`, where they are authored with `vertex` or `varying`
///   interpolation, or `faceVarying` on a `Mesh` that authors
///   `faceVertexIndices`. The result is carried from skeleton space into the
///   prim's own.
/// - Blend shapes, before skinning, on `points` and on normals that are not
///   face-varying, where the skeleton's animation authors blend-shape weights,
///   whether or not the prim is bound rigidly.
///
/// The skeleton skins only where it poses: through an animation that maps
/// onto its joints, or its authored `restTransforms`.
///
/// Each skeleton bakes at every time within `interval` at which its
/// animation, its world transform, or one of its prims' inputs is sampled:
/// the rest points and normals, `faceVertexIndices`, the joint influences,
/// the geom bind transform, and the world transform of the prim, or of its
/// parent where the transform bakes. The world transform's times come from
/// each ancestor up to one that resets the transform stack, where C++ takes
/// the prim's own once for each ancestor. Where those inputs are sampled at
/// more than one time, the skeleton also bakes at each of the stage's
/// playback frames within `interval` and between the first and last of them,
/// the frames running from the start to the end time code
/// `timeCodesPerSecond / framesPerSecond` apart; and where none of those
/// times lies within `interval`, at its closed finite bounds. C++ takes the
/// playback frames only between the first and last time within `interval`,
/// adds a frame past the end time code, and bakes a skeleton whose samples all
/// lie outside `interval` at the default time. A skeleton whose inputs are not
/// sampled bakes at the default time alone.
///
/// Every output goes to the binding's layer at the prim's stage path, the
/// prim's spec created as `over` where the layer holds none. Its time
/// samples in that layer are replaced, and its default too where it bakes at
/// the default time. Each sample is keyed at the layer time that composes to
/// the stage time it was computed for, where C++ writes the stage time
/// unchanged. An output with no value at any time is left alone, where C++
/// clears its samples. A `Mesh` whose points bake gets its `extent` too,
/// where [`BakeOptions::update_extents`] is set. The nearest [`Root`] of
/// each skinned prim becomes `def Xform` in the binding's layer, where C++
/// converts only the first skinned prim's. Nothing else changes: the binding
/// properties, the skeleton and the animation stay.
///
/// Everything is read and checked before a single transaction writes every
/// layer, so a failure leaves the stage untouched. A binding whose skeleton
/// has no [`SkeletonQuery`], and a prim with nothing to bake, are skipped. A
/// prim that cannot be deformed at a time, its influences out of range say,
/// gets no sample there.
///
/// Two stages follow, each reading what the stages before it committed and
/// writing in one transaction of its own:
///
/// - With [`BakeOptions::update_extents`], each other point-based prim whose
///   points baked gets its `extent` from its type's extent function at each
///   time they baked, into the binding's layer, keyed and replaced as the
///   other outputs are. C++ authors these through the stage's edit target,
///   and clears their default too.
/// - With [`BakeOptions::update_extent_hints`], each model at or above a
///   baked prim whose `extentsHint` is defined gets the hint a [`BBoxCache`]
///   computes at every time a skeleton of its prims baked. The hint is
///   authored through the stage's edit target, as C++ authors it, its
///   namespace mapping and time offset included, and its old value and
///   samples there are cleared first. Without updated extents, a deformed
///   prim that authors an `extent` is bounded by the one it had.
///
/// Fails, before anything is written:
///
/// - [`SchemaError::BakeInstanced`] for a skinned prim that is an instance or
///   an instance proxy;
/// - [`SchemaError::BakeStages`] for bindings of more than one stage;
/// - [`SchemaError::BakeLayer`] for a layer outside the stage's root layer
///   stack;
/// - [`SchemaError::BakeSpecType`] for an output whose layer holds a spec of
///   another type, `extent` among them, where C++ skips that output.
///
/// With [`BakeOptions::save_layers`], each layer the bindings name is saved
/// last, and so is the edit target's layer where a hint was authored there,
/// where C++ saves only the bindings' layers. A layer that fails to save,
/// an anonymous one among them, fails the bake with its export error, the
/// layers saved before it staying saved.
///
/// Fails after the geometry committed, with [`SchemaError::BakeExtents`]
/// where the extents stage fails and leaves every extent of the other
/// prims as it was, and with [`SchemaError::BakeExtentHints`] where the
/// hint stage fails and leaves every hint as it was.
pub fn bake_skinning(
    bindings: &[(Binding, &str)],
    options: &BakeOptions,
    interval: impl Into<gf::Interval>,
) -> Result<(), SchemaError> {
    let interval = interval.into();
    let Some((first, _)) = bindings.first() else {
        return Ok(());
    };
    let stage = first.skeleton().stage().clone();
    let mut xforms = XformCache::new(None);
    let mut layers: Vec<EditTarget> = Vec::new();
    let mut skels = Vec::new();
    let mut roots = Vec::new();
    for (binding, layer) in bindings {
        if *binding.skeleton().stage() != stage {
            return Err(SchemaError::BakeStages {
                prim: binding.skeleton().path().clone(),
            });
        }
        for target in binding.skinning_targets() {
            let prim = target.prim();
            if *prim.stage() != stage {
                return Err(SchemaError::BakeStages {
                    prim: prim.path().clone(),
                });
            }
            if is_instanced(prim)? {
                return Err(SchemaError::BakeInstanced {
                    prim: prim.path().clone(),
                });
            }
        }
        let target = stage
            .edit_target_for_local_layer(layer)
            .ok_or_else(|| SchemaError::BakeLayer {
                layer: (*layer).to_owned(),
            })?;
        // Bindings commonly share a layer, and `batch_edit` takes each once.
        let known = layers
            .iter()
            .position(|known| known.layer_identifier() == target.layer_identifier());
        let layer = known.unwrap_or_else(|| {
            layers.push(target);
            layers.len() - 1
        });

        if binding.skinning_targets().is_empty() {
            continue;
        }
        // Nested roots whose prims share a skeleton share a binding.
        for target in binding.skinning_targets() {
            if let Some(root) = Root::find(target.prim())? {
                let root = (root.path().clone(), layer);
                if !roots.contains(&root) {
                    roots.push(root);
                }
            }
        }
        let Some(query) = SkeletonQuery::new(binding.skeleton())? else {
            continue;
        };
        let skel = SkelAdapter::new(query, binding.skinning_targets(), layer, options, &mut xforms)?;
        if !skel.prims.is_empty() {
            skels.push(skel);
        }
    }

    let playback = playback_times(&stage, interval);
    // TODO(rayon): each skeleton and its prims bake independently of the
    // others, and so do the prims of one skeleton at one time, once the
    // transform cache is read for them first.
    let mut followups = Vec::new();
    for skel in &mut skels {
        let times = bake_times(skel.time_samples(&mut xforms)?, &playback, interval);
        for &time in &times {
            xforms.set_time(time);
            let frame = skel.frame(time, &mut xforms)?;
            for prim in &mut skel.prims {
                prim.bake(&frame, time, &mut xforms)?;
            }
        }
        for prim in &skel.prims {
            followups.push(Followup::new(prim, &times, options)?);
        }
    }
    for followup in followups.iter().filter(|followup| !followup.extent_times.is_empty()) {
        let attribute = followup.prim.path().append_property(geom::tokens::EXTENT)?;
        let layer = layers[followup.layer].layer_identifier();
        check_type(&stage, layer, &attribute, &sdf::ValueTypeName::FLOAT3_ARRAY)?;
    }

    // TODO(perf): every output is held until the one transaction below; a
    // bake that writes as it goes needs the inputs it reads kept apart from
    // what it has written, and each output's old samples cleared only once.
    let mut writes = Vec::new();
    for prim in skels.into_iter().flat_map(|skel| skel.prims) {
        let (layer, path) = (prim.layer, prim.query.prim().path().clone());
        for (name, type_name, variability, values) in prim.into_outputs() {
            if values.is_empty() {
                continue;
            }
            let attribute = path.append_property(name.as_str())?;
            check_type(&stage, layers[layer].layer_identifier(), &attribute, &type_name)?;
            writes.push(Write {
                layer,
                attribute,
                type_name,
                variability,
                values,
            });
        }
    }
    let identifiers: Vec<&str> = layers.iter().map(EditTarget::layer_identifier).collect();
    stage.batch_edit(&identifiers, |edits| {
        for write in writes {
            let layer = write.layer;
            write.apply(&mut edits[layer], &layers[layer])?;
        }
        for (root, layer) in &roots {
            sdf::PrimSpec::new(
                edits[*layer].data_mut(),
                root.clone(),
                sdf::Specifier::Def,
                geom::tokens::XFORM,
            )?;
        }
        Ok(())
    })?;

    bake_extents(&stage, &layers, &followups).map_err(|err| SchemaError::BakeExtents(Box::new(err)))?;
    let mut saves: Vec<String> = layers.iter().map(|layer| layer.layer_identifier().to_owned()).collect();
    if options.update_extent_hints {
        let target = stage.edit_target();
        let hinted =
            bake_extent_hints(&stage, &followups).map_err(|err| SchemaError::BakeExtentHints(Box::new(err)))?;
        if hinted && !saves.iter().any(|layer| layer == target.layer_identifier()) {
            saves.push(target.layer_identifier().to_owned());
        }
    }
    if options.save_layers {
        // TODO(rayon): each layer saves independently of the others.
        for identifier in &saves {
            if let Some(mut layer) = stage.layer_mut(identifier) {
                layer.save().map_err(openusd::Error::from)?;
            }
        }
    }
    Ok(())
}

/// One skeleton a bake poses, and the prims it deforms (C++ `_SkelAdapter`).
struct SkelAdapter<'a> {
    query: SkeletonQuery,
    prims: Vec<PrimAdapter<'a>>,
    /// Whether a prim skins through its pose, which needs its world
    /// transform too.
    needs_pose: bool,
    /// Whether a prim applies its blend-shape weights.
    needs_weights: bool,
}

/// What a skeleton holds at one time.
struct Frame {
    pose: Option<Pose>,
    weights: Option<Vec<f32>>,
    /// The skeleton's local-to-world transform.
    world: gf::Mat4d,
}

impl<'a> SkelAdapter<'a> {
    /// The adapter for `query`'s skeleton over the prims of `targets` that
    /// have something to bake into `layer`.
    fn new(
        query: SkeletonQuery,
        targets: &'a [SkinningQuery],
        layer: usize,
        options: &BakeOptions,
        xforms: &mut XformCache,
    ) -> Result<Self, SchemaError> {
        let anim = query.anim_query();
        let mapped = anim.is_some() && query.mapper().is_some_and(|mapper| !mapper.is_null());
        let skel = Skel {
            poses: options.deform.intersects(Deform::SKINNING)
                && (mapped || query.skeleton().rest_transforms_attr().has_authored_value()?),
            weighs: options.deform.intersects(Deform::BLEND_SHAPES)
                && match anim {
                    Some(anim) => anim.animation().blend_shape_weights_attr().has_authored_value()?,
                    None => false,
                },
        };
        let mut prims = Vec::new();
        for target in targets {
            if let Some(prim) = PrimAdapter::new(target, skel, layer, options, xforms)? {
                prims.push(prim);
            }
        }
        Ok(Self {
            needs_pose: prims.iter().any(|prim| prim.flags.intersects(Deform::SKINNING)),
            needs_weights: prims.iter().any(|prim| prim.flags.intersects(Deform::BLEND_SHAPES)),
            query,
            prims,
        })
    }

    /// Every time at which what the skeleton bakes from is sampled: its
    /// animation's joint transforms and blend-shape weights, its world
    /// transform, and its prims' inputs.
    fn time_samples(&self, xforms: &mut XformCache) -> Result<Vec<f64>, SchemaError> {
        let mut times = Vec::new();
        if let Some(anim) = self.query.anim_query() {
            if self.needs_pose {
                times.extend(anim.joint_transform_time_samples()?);
            }
            if self.needs_weights {
                times.extend(anim.blend_shape_weight_time_samples()?);
            }
        }
        if self.needs_pose {
            times.extend(xforms.world_time_samples_in(self.query.skeleton().prim(), ..)?);
        }
        for prim in &self.prims {
            prim.extend_time_samples(&mut times, xforms)?;
        }
        Ok(times)
    }

    /// The pose, the blend-shape weights and the world transform at `time`,
    /// each where a prim needs it.
    fn frame(&self, time: Option<TimeCode>, xforms: &mut XformCache) -> Result<Frame, SchemaError> {
        let (pose, world) = if self.needs_pose {
            (
                self.query.skinning_transforms(time)?.map(Pose::from),
                xforms.local_to_world_transform(self.query.skeleton().prim())?,
            )
        } else {
            (None, gf::Mat4d::IDENTITY)
        };
        let weights = match (self.needs_weights, self.query.anim_query()) {
            (true, Some(anim)) => anim.blend_shape_weights(time)?,
            _ => None,
        };
        Ok(Frame { pose, weights, world })
    }
}

/// What a skeleton can give its prims.
#[derive(Clone, Copy)]
struct Skel {
    /// Whether it poses: through an animation that maps onto its joints, or
    /// its authored `restTransforms`.
    poses: bool,
    /// Whether its animation authors blend-shape weights.
    weighs: bool,
}

/// One prim a bake deforms, how, and what it has baked (C++
/// `_SkinningAdapter`).
struct PrimAdapter<'a> {
    query: &'a SkinningQuery,
    /// The index of the layer it bakes into.
    layer: usize,
    /// The deformations it takes.
    flags: Deform,
    /// The rest `points`, where it bakes them.
    points: Option<Attribute>,
    /// The rest `normals`, where it bakes them, with the `faceVertexIndices`
    /// face-varying normals read their points through.
    normals: Option<(Attribute, Option<Attribute>)>,
    blend_shapes: Option<BlendShapes>,
    /// Whether it bakes an `extent` from its points.
    extent: bool,
    /// Whether it resets the transform stack, which places its baked
    /// transform in world space.
    resets: bool,
    baked: Baked,
}

/// A prim's blend shapes, laid out once.
struct BlendShapes {
    query: BlendShapeQuery,
    point_indices: Vec<Vec<i32>>,
    point_offsets: Vec<Vec<gf::Vec3f>>,
    normal_offsets: Vec<Vec<gf::Vec3f>>,
}

/// What a prim has baked, each value with the time it was baked at.
#[derive(Default)]
struct Baked {
    points: Vec<(Option<TimeCode>, Vec<gf::Vec3f>)>,
    normals: Vec<(Option<TimeCode>, Vec<gf::Vec3f>)>,
    extents: Vec<(Option<TimeCode>, Extent)>,
    xforms: Vec<(Option<TimeCode>, gf::Mat4d)>,
}

impl<'a> PrimAdapter<'a> {
    /// The adapter for `query`'s prim, or `None` when it has nothing to bake
    /// from what `skel` gives.
    fn new(
        query: &'a SkinningQuery,
        skel: Skel,
        layer: usize,
        options: &BakeOptions,
        xforms: &mut XformCache,
    ) -> Result<Option<Self>, SchemaError> {
        let prim = query.prim();
        let deform = options.deform;
        let point_based = PointBased::from_prim(prim.clone())?;
        let (mut points, mut normals) = (None, None);
        if let Some(point_based) = &point_based {
            if deform.intersects(Deform::MODIFIES_POINTS) {
                let attr = point_based.points_attr();
                if attr.has_authored_value()? {
                    points = Some(attr);
                }
            }
            if deform.intersects(Deform::MODIFIES_NORMALS) {
                let attr = point_based.normals_attr();
                let interpolation = point_based.normals_interpolation()?;
                if interpolation == Interpolation::FaceVarying
                    && let Some(mesh) = Mesh::from_prim(prim.clone())?
                {
                    let indices = mesh.face_vertex_indices_attr();
                    if attr.has_authored_value()? && indices.has_authored_value()? {
                        normals = Some((attr, Some(indices)));
                    }
                } else if attr.has_authored_value()?
                    && matches!(interpolation, Interpolation::Vertex | Interpolation::Varying)
                {
                    normals = Some((attr, None));
                }
            }
        }

        let mut flags = Deform::empty();
        if deform.intersects(Deform::SKINNING) && query.has_joint_influences() && skel.poses {
            if query.is_rigidly_deformed() {
                let xformable = point_based.is_some() || Xformable::from_prim(prim.clone())?.is_some();
                if xformable && deform.contains(Deform::XFORM_WITH_SKINNING) {
                    flags |= Deform::XFORM_WITH_SKINNING;
                }
            } else if point_based.is_some() {
                if deform.contains(Deform::POINTS_WITH_SKINNING) && points.is_some() {
                    flags |= Deform::POINTS_WITH_SKINNING;
                }
                if deform.contains(Deform::NORMALS_WITH_SKINNING) && normals.is_some() {
                    flags |= Deform::NORMALS_WITH_SKINNING;
                }
            }
        }

        let mut blend_shapes = None;
        if deform.intersects(Deform::BLEND_SHAPES)
            && skel.weighs
            && point_based.is_some()
            && query.has_blend_shapes()
            && (points.is_some() || normals.is_some())
        {
            let shapes = BlendShapeQuery::new(&BindingAPI::from_prim_unchecked(prim.clone()))?;
            let mut point_offsets = Vec::new();
            if deform.contains(Deform::POINTS_WITH_BLEND_SHAPES) && points.is_some() {
                point_offsets = shapes.sub_shape_point_offsets()?;
                if point_offsets.iter().any(|offsets| !offsets.is_empty()) {
                    flags |= Deform::POINTS_WITH_BLEND_SHAPES;
                }
            }
            // A blend shape has no face-varying normal offsets.
            let mut normal_offsets = Vec::new();
            if deform.contains(Deform::NORMALS_WITH_BLEND_SHAPES) && matches!(normals, Some((_, None))) {
                normal_offsets = shapes.sub_shape_normal_offsets()?;
                if normal_offsets.iter().any(|offsets| !offsets.is_empty()) {
                    flags |= Deform::NORMALS_WITH_BLEND_SHAPES;
                }
            }
            if flags.intersects(Deform::BLEND_SHAPES) {
                blend_shapes = Some(BlendShapes {
                    point_indices: shapes.blend_shape_point_indices()?,
                    query: shapes,
                    point_offsets,
                    normal_offsets,
                });
            }
        }

        if flags.is_empty() {
            return Ok(None);
        }
        let extent = options.update_extents
            && flags.intersects(Deform::MODIFIES_POINTS)
            && Mesh::from_prim(prim.clone())?.is_some();
        Ok(Some(Self {
            query,
            layer,
            flags,
            points: points.filter(|_| flags.intersects(Deform::MODIFIES_POINTS)),
            normals: normals.filter(|_| flags.intersects(Deform::MODIFIES_NORMALS)),
            blend_shapes,
            extent,
            resets: flags.contains(Deform::XFORM_WITH_SKINNING) && xforms.resets_xform_stack(prim)?,
            baked: Baked::default(),
        }))
    }

    /// Add every time at which the prim's inputs are sampled.
    fn extend_time_samples(&self, times: &mut Vec<f64>, xforms: &mut XformCache) -> Result<(), SchemaError> {
        if let Some(points) = &self.points {
            times.extend(points.time_samples_in(..)?);
        }
        if let Some((normals, face_vertex_indices)) = &self.normals {
            times.extend(normals.time_samples_in(..)?);
            if let Some(indices) = face_vertex_indices {
                times.extend(indices.time_samples_in(..)?);
            }
        }
        if self.flags.intersects(Deform::SKINNING) {
            times.extend(self.query.time_samples()?);
        }
        let prim = self.query.prim();
        if self
            .flags
            .intersects(Deform::POINTS_WITH_SKINNING | Deform::NORMALS_WITH_SKINNING)
        {
            times.extend(xforms.world_time_samples_in(prim, ..)?);
        }
        if self.flags.contains(Deform::XFORM_WITH_SKINNING)
            && !self.resets
            && let Some(parent) = prim.parent()
        {
            times.extend(xforms.world_time_samples_in(&parent, ..)?);
        }
        Ok(())
    }

    /// Bake the prim at `time` through its skeleton's `frame`: blend shapes,
    /// then skinning carried into the prim's space (C++
    /// `_SkinningAdapter::Update`).
    // TODO(perf): every input is read anew at each time, the joint influences
    // up to three times; C++ reads an input once where it does not vary
    // (`_Task`), and keeps an unvarying pose.
    fn bake(&mut self, frame: &Frame, time: Option<TimeCode>, xforms: &mut XformCache) -> Result<(), SchemaError> {
        let rest = |attr: Option<&Attribute>| -> Result<Option<Vec<gf::Vec3f>>, SchemaError> {
            Ok(attr.map(|attr| attr.get_at(time)).transpose()?.flatten())
        };
        let rest_points = rest(self.points.as_ref())?;
        let rest_normals = rest(self.normals.as_ref().map(|(normals, _)| normals))?;
        let (mut points, mut normals) = (None, None);

        if let (Some(shapes), Some(weights)) = (&self.blend_shapes, &frame.weights)
            && let Some(weights) = self.sub_shape_weights(shapes, weights)
        {
            if self.flags.contains(Deform::POINTS_WITH_BLEND_SHAPES) {
                points = rest_points.as_deref().and_then(|rest| {
                    BlendShapeQuery::deformed_points(&weights, &shapes.point_indices, &shapes.point_offsets, rest)
                });
            }
            if self.flags.contains(Deform::NORMALS_WITH_BLEND_SHAPES) {
                normals = rest_normals.as_deref().and_then(|rest| {
                    BlendShapeQuery::deformed_normals(&weights, &shapes.point_indices, &shapes.normal_offsets, rest)
                });
            }
        }

        // A pose or influences missing at this time leave the blend shapes
        // as they are; a skinning that fails leaves nothing, as in C++.
        if self.flags.intersects(Deform::SKINNING)
            && let Some(pose) = &frame.pose
            && self.query.joint_influences(time)?.is_some()
        {
            let prim = self.query.prim();
            if self.flags.contains(Deform::XFORM_WITH_SKINNING) {
                // The skinned transform is in skeleton space:
                // `skelSkinned · skelLocalToWorld · inverse(parentToWorld)`
                // places it in the parent's.
                let parent = match self.resets {
                    true => gf::Mat4d::IDENTITY,
                    false => xforms.parent_to_world_transform(prim)?,
                };
                if let Some(skinned) = self.query.skinned_transform(pose, time)? {
                    self.baked
                        .xforms
                        .push((time, skinned * frame.world * parent.inverse_or_max()));
                }
            } else {
                // `skelSkinned · skelLocalToWorld · inverse(primLocalToWorld)`
                // places the skinned points in the prim's space.
                let to_prim = frame.world * xforms.local_to_world_transform(prim)?.inverse_or_max();
                if self.flags.contains(Deform::POINTS_WITH_SKINNING) {
                    points = match points.or(rest_points) {
                        Some(base) => self.query.skinned_points(pose, &base, time)?.map(|skinned| {
                            skinned
                                .into_iter()
                                .map(|point| to_prim.transform(point.into()).to_f32())
                                .collect()
                        }),
                        None => None,
                    };
                }
                if self.flags.contains(Deform::NORMALS_WITH_SKINNING) {
                    let face_vertex_indices = self.normals.as_ref().and_then(|(_, indices)| indices.as_ref());
                    let skinned = match (normals.or(rest_normals), face_vertex_indices) {
                        (Some(base), Some(attr)) => match attr.get_at::<Vec<i32>>(time)? {
                            Some(indices) => self.query.skinned_face_varying_normals(pose, &base, &indices, time)?,
                            None => None,
                        },
                        (Some(base), None) => self.query.skinned_normals(pose, &base, time)?,
                        (None, _) => None,
                    };
                    // Not renormalized, as in C++.
                    let to_prim = normal_transform(to_prim);
                    normals = skinned.map(|skinned| {
                        skinned
                            .into_iter()
                            .map(|normal| to_prim.transform(normal.into()).to_f32())
                            .collect()
                    });
                }
            }
        }

        if let Some(points) = points {
            if self.extent {
                self.baked.extents.push((time, PointBased::extent_from(&points, None)));
            }
            self.baked.points.push((time, points));
        }
        if let Some(normals) = normals {
            self.baked.normals.push((time, normals));
        }
        Ok(())
    }

    /// The sub-shape weights the skeleton's `weights` apply to the prim's
    /// blend shapes, through the prim's `skel:blendShapes` order.
    fn sub_shape_weights(&self, shapes: &BlendShapes, weights: &[f32]) -> Option<Vec<SubShapeWeight>> {
        let mapper = self.query.blend_shape_mapper()?;
        let mut remapped = vec![0.0; mapper.target_len()];
        mapper.remap_into(weights, &mut remapped).then_some(())?;
        shapes.query.sub_shape_weights(&remapped)
    }

    /// The attributes the prim bakes, each with its type, its variability
    /// and its values.
    fn into_outputs(self) -> Vec<(tf::Token, sdf::ValueTypeName, sdf::Variability, Values)> {
        let varying = sdf::Variability::Varying;
        let mut outputs = Vec::new();
        let Baked {
            points,
            normals,
            extents,
            xforms,
        } = self.baked;
        if self.flags.intersects(Deform::MODIFIES_POINTS) {
            let points = points
                .into_iter()
                .map(|(time, points)| (time, sdf::Value::Vec3fVec(points)));
            outputs.push((
                tf::Token::new(geom::tokens::POINTS),
                sdf::ValueTypeName::POINT3F_ARRAY,
                varying,
                points.collect(),
            ));
        }
        if self.flags.intersects(Deform::MODIFIES_NORMALS) {
            let normals = normals
                .into_iter()
                .map(|(time, normals)| (time, sdf::Value::Vec3fVec(normals)));
            outputs.push((
                tf::Token::new(geom::tokens::NORMALS),
                sdf::ValueTypeName::NORMAL3F_ARRAY,
                varying,
                normals.collect(),
            ));
        }
        if self.extent {
            let extents = extents
                .into_iter()
                .map(|(time, extent)| (time, sdf::Value::Vec3fVec(extent.to_vec())));
            outputs.push((
                tf::Token::new(geom::tokens::EXTENT),
                sdf::ValueTypeName::FLOAT3_ARRAY,
                varying,
                extents.collect(),
            ));
        }
        if self.flags.contains(Deform::XFORM_WITH_SKINNING) && !xforms.is_empty() {
            let op = XformOpKind::Transform.op_name(None, false);
            let order = match self.resets {
                true => vec![tf::Token::new(geom::TOKEN_RESET_XFORM_STACK), op.clone()],
                false => vec![op.clone()],
            };
            let xforms = xforms
                .into_iter()
                .map(|(time, xform)| (time, sdf::Value::Matrix4d(xform)));
            outputs.push((op, sdf::ValueTypeName::MATRIX4D, varying, xforms.collect()));
            outputs.push((
                tf::Token::new(geom::tokens::XFORM_OP_ORDER),
                sdf::ValueTypeName::TOKEN_ARRAY,
                sdf::Variability::Uniform,
                vec![(None, sdf::Value::TokenVec(order))],
            ));
        }
        outputs
    }
}

/// One output's values, each with the time it was baked at.
type Values = Vec<(Option<TimeCode>, sdf::Value)>;

/// One attribute the bake writes.
struct Write {
    /// The index of the layer it goes to.
    layer: usize,
    attribute: sdf::Path,
    type_name: sdf::ValueTypeName,
    variability: sdf::Variability,
    values: Values,
}

impl Write {
    /// Write the values into `edit`, the layer `target` names: the spec found
    /// or created, its old samples replaced, its default set where a value was
    /// baked at the default time.
    fn apply(self, edit: &mut sdf::LayerEdit<'_>, target: &EditTarget) -> Result<(), StageAuthoringError> {
        let mut spec = if edit.attribute(&self.attribute)?.is_some() {
            edit.attribute_mut(&self.attribute)?
                .expect("an attribute spec is there")
        } else {
            sdf::AttributeSpec::new(
                edit.data_mut(),
                self.attribute.clone(),
                self.type_name,
                self.variability,
                false,
            )?
        };
        let (defaults, samples): (Vec<_>, Vec<_>) = self.values.into_iter().partition(|(time, _)| time.is_none());
        spec.set_time_samples(
            samples
                .into_iter()
                .filter_map(|(time, value)| time.map(|time| (target.map_to_spec_time(time.value()), value))),
        )?;
        if let Some((_, value)) = defaults.into_iter().next() {
            spec.set_default(value)?;
        }
        Ok(())
    }
}

/// What the extents and extents-hint stages need of one baked prim.
struct Followup {
    prim: Prim,
    /// The index of the layer it bakes into.
    layer: usize,
    /// The times its points baked at, where its extent is computed from them
    /// once they commit: a point-based prim other than a `Mesh`, with
    /// [`BakeOptions::update_extents`] set.
    extent_times: Vec<Option<TimeCode>>,
    /// The times its skeleton baked at.
    times: Vec<Option<TimeCode>>,
}

impl Followup {
    /// The followup of `prim`, whose skeleton baked at `times`.
    fn new(prim: &PrimAdapter<'_>, times: &[Option<TimeCode>], options: &BakeOptions) -> Result<Self, SchemaError> {
        let query_prim = prim.query.prim();
        let post_extent = options.update_extents
            && prim.flags.intersects(Deform::MODIFIES_POINTS)
            && Mesh::from_prim(query_prim.clone())?.is_none();
        let extent_times = match post_extent {
            true => prim.baked.points.iter().map(|(time, _)| *time).collect(),
            false => Vec::new(),
        };
        Ok(Self {
            prim: query_prim.clone(),
            layer: prim.layer,
            extent_times,
            times: times.to_vec(),
        })
    }
}

/// Bake the extent of each prim in `followups` that takes one after the
/// geometry commits, computed by its type's extent function from its baked
/// points at each time they baked, into its layer among `layers` in one
/// transaction (C++ `_PostUpdateExtents`). A time at which the function
/// computes no extent gets no sample.
fn bake_extents(stage: &usd::Stage, layers: &[EditTarget], followups: &[Followup]) -> Result<(), SchemaError> {
    let extents = crate::extent_registry();
    let mut writes = Vec::new();
    // TODO(rayon): each prim's extents compute independently of the others'.
    for followup in followups.iter().filter(|followup| !followup.extent_times.is_empty()) {
        let mut values = Vec::new();
        for &time in &followup.extent_times {
            if let Some(extent) = extents.shape_extent(&followup.prim, time, None)? {
                values.push((time, sdf::Value::Vec3fVec(extent.to_vec())));
            }
        }
        if !values.is_empty() {
            writes.push(Write {
                layer: followup.layer,
                attribute: followup.prim.path().append_property(geom::tokens::EXTENT)?,
                type_name: sdf::ValueTypeName::FLOAT3_ARRAY,
                variability: sdf::Variability::Varying,
                values,
            });
        }
    }
    if writes.is_empty() {
        return Ok(());
    }
    let identifiers: Vec<&str> = layers.iter().map(EditTarget::layer_identifier).collect();
    stage.batch_edit(&identifiers, |edits| {
        for write in writes {
            let layer = write.layer;
            write.apply(&mut edits[layer], &layers[layer])?;
        }
        Ok(())
    })?;
    Ok(())
}

/// Recompute the `extentsHint` of each model at or above a prim in
/// `followups` that has one, at every time a skeleton of its prims baked,
/// and author the hints through the stage's edit target in one transaction,
/// each hint's own values there cleared first (C++ `_UpdateExtentHints`).
/// `true` where a hint was authored.
fn bake_extent_hints(stage: &usd::Stage, followups: &[Followup]) -> Result<bool, SchemaError> {
    let mut models: Vec<(ModelAPI, Vec<Option<TimeCode>>)> = Vec::new();
    for followup in followups {
        let mut at = Some(followup.prim.clone());
        // The walk stops below the pseudo-root, the one prim with no parent.
        while let Some(prim) = at.filter(|prim| prim.parent().is_some()) {
            if prim.is_model()? {
                let model = ModelAPI::from_prim_unchecked(prim.clone());
                if model.extents_hint_attr().is_defined()? {
                    match models.iter_mut().find(|(known, _)| known.prim() == model.prim()) {
                        Some((_, times)) => times.extend(&followup.times),
                        None => models.push((model, followup.times.clone())),
                    }
                }
            }
            at = prim.parent();
        }
    }
    if models.is_empty() {
        return Ok(false);
    }

    let mut times: Vec<Option<TimeCode>> = models.iter().flat_map(|(_, times)| times.iter().copied()).collect();
    times.sort_by(compare_times);
    times.dedup();
    let mut hints: Vec<Vec<(Option<TimeCode>, Vec<Extent>)>> = models.iter().map(|_| Vec::new()).collect();
    let mut cache = BBoxCache::new(None, Purpose::ORDERED);
    // TODO(rayon): the times are independent of each other, each chunk of
    // them with a cache of its own.
    for time in times {
        cache.set_time(time);
        for ((model, model_times), hints) in models.iter().zip(&mut hints) {
            if model_times.contains(&time) {
                hints.push((time, model.compute_extents_hint(&mut cache)?));
            }
        }
    }

    stage.edit(|edit| {
        for ((model, _), hints) in models.iter().zip(hints) {
            let mut builder = model
                .prim()
                .attribute_builder(geom::tokens::EXTENTS_HINT, sdf::ValueTypeName::FLOAT3_ARRAY)
                .custom(false)
                .in_edit(edit)
                .clear();
            for (time, extents) in hints {
                builder = builder.set_at(extents.as_flattened().to_vec(), time);
            }
            builder.build()?;
        }
        Ok::<_, SchemaError>(())
    })?;
    Ok(true)
}

/// The order of baked times: the default time first, then by time.
fn compare_times(a: &Option<TimeCode>, b: &Option<TimeCode>) -> Ordering {
    match (a, b) {
        (Some(a), Some(b)) => sdf::compare_sample_times(a.value(), b.value()),
        _ => a.is_some().cmp(&b.is_some()),
    }
}

/// `true` for an instance or an instance proxy.
fn is_instanced(prim: &Prim) -> openusd::Result<bool> {
    Ok(prim.is_instance()? || prim.is_instance_proxy()?)
}

/// The stage's playback frames within `interval`: from the start time code
/// to the end, one frame of `timeCodesPerSecond / framesPerSecond` apart.
/// Empty without an authored time-code range, or with either rate zero.
fn playback_times(stage: &usd::Stage, interval: gf::Interval) -> Vec<f64> {
    let (tcps, fps) = (stage.time_codes_per_second(), stage.frames_per_second());
    if !stage.has_authored_time_code_range() || tcps.abs() < 1e-6 || fps.abs() < 1e-6 {
        return Vec::new();
    }
    let step = (tcps / fps).abs();
    let (start, end) = (stage.start_time_code(), stage.end_time_code());
    if end < start {
        return Vec::new();
    }
    // Each frame is a multiple of the step from the start, which keeps the
    // rounding error from accumulating; the tolerance keeps a quotient a hair
    // under a whole number of frames from dropping the last.
    #[allow(clippy::cast_possible_truncation)] // `end >= start`, and a range of 2^63 frames is no stage's.
    let frames = ((end - start) / step + 1e-9).floor() as i64 + 1;
    (0..frames)
        .map(|frame| start + step * frame as f64)
        .filter(|&time| interval.contains(time))
        .collect()
}

/// The times one skeleton bakes at within `interval`, from every time its
/// inputs are sampled at: the default time where there are none; else those
/// within `interval`, with the `playback` frames between the first and last
/// of all of them where there is more than one, and the closed finite bounds
/// of `interval` where that leaves none.
fn bake_times(mut times: Vec<f64>, playback: &[f64], interval: gf::Interval) -> Vec<Option<TimeCode>> {
    let (Some(first), Some(last)) = (
        times.iter().copied().reduce(f64::min),
        times.iter().copied().reduce(f64::max),
    ) else {
        return vec![None];
    };
    times.retain(|&time| interval.contains(time));
    if first < last {
        times.extend(playback.iter().filter(|&&time| first <= time && time <= last));
    }
    if times.is_empty() {
        let bounds = [
            (interval.min(), interval.is_min_closed()),
            (interval.max(), interval.is_max_closed()),
        ];
        times.extend(
            bounds
                .into_iter()
                .filter(|&(bound, closed)| closed && bound.is_finite())
                .map(|(bound, _)| bound),
        );
    }
    times.sort_by(|a, b| sdf::compare_sample_times(*a, *b));
    times.dedup_by(|a, b| sdf::compare_sample_times(*a, *b).is_eq());
    times.into_iter().map(|time| Some(TimeCode::new(time))).collect()
}

/// Fail unless the spec at `path` in `layer`, where there is one, has
/// `type_name`.
fn check_type(
    stage: &usd::Stage,
    layer: &str,
    path: &sdf::Path,
    type_name: &sdf::ValueTypeName,
) -> Result<(), SchemaError> {
    let Some(layer) = stage.layer(layer) else {
        return Ok(());
    };
    let Some(spec) = layer.attribute(path)? else {
        return Ok(());
    };
    let found = spec.type_name();
    if found.as_ref() == Some(type_name) {
        return Ok(());
    }
    Err(SchemaError::BakeSpecType {
        attribute: path.clone(),
        found: found.map(|found| found.as_token()).unwrap_or_default(),
        expected: type_name.as_token(),
    })
}
