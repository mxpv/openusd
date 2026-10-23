//! `UsdGeomBBoxCache` — the bounds of prims and of everything beneath them,
//! memoized across a hierarchy.
//!
//! A [`BBoxCache`] answers the box around a prim's subtree at one time, for
//! a set of purposes. It keeps the box of each prim it resolves, in that
//! prim's own space, and a later query for the prim or for an ancestor
//! reuses it.
//!
//! The cache does not observe the stage. A stage edit refreshes nothing an
//! entry holds, and neither does it refresh the transforms the cache keeps
//! in its [`XformCache`]. Call [`BBoxCache::clear`] after an edit.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use openusd::usd::{self, SchemaBase};
use openusd::{gf, sdf, tf};

use super::boundable::authored_extent;
use super::imageable::{is_invisible, purpose_below};
use super::{
    Boundable, BoundableSchema, ExtentContext, ExtentFn, ExtentRegistry, Imageable, ImageableExt, ImageableSchema,
    MaskApplication, ModelAPI, PointInstancer, PointInstancerSchema, ProtoXformInclusion, Purpose, PurposeInfo,
    XformCache, tokens,
};
use crate::SchemaError;

/// A per-time cache of the bounds of prims (C++ `UsdGeomBBoxCache`).
///
/// A prim's bound is the box around the boundable prims at and beneath it:
/// each one's `extent`, authored or computed, placed by the transforms
/// between it and the prim. Only the children that are active, defined and
/// not abstract are bounded, and of those the ones whose purpose is among
/// the cache's [included purposes](Self::included_purposes), whose type is
/// `Imageable` or unknown, and whose own `visibility` is not `invisible`
/// at the cache's time. None of that is asked of the prim the bound is asked
/// for. A boundable prim's `extent` stands for everything beneath it. An
/// unloaded prim is bounded like any other, by what the stage holds of it.
///
/// The children of a prim are unioned in the space of the nearest component
/// or subcomponent at or above it, or in world space where there is none,
/// so a model's box is tight in the model's own space. The box answered
/// keeps the matrix of that space: take [`gf::BBox3d::aligned_range`] for
/// an axis-aligned box. A prim whose place in that space flattens it, a
/// scale of zero along an axis say, unions its children in its own space,
/// each under its local transform. A child that resets the transform stack
/// has no place in such a space, and the prim's bound is then
/// [`SchemaError::ResetBeneathFlattened`], where C++ answers a box that
/// leaves the child out.
///
/// Entries are keyed by [`usd::Prim`], so one cache serves prims of several
/// stages. The instances of one prototype share the entries of the
/// prototype's prims. Queries take `&mut self`, since answering one may
/// fill the cache. A query that fails keeps the entries it completed and
/// leaves the cache as usable as it was.
///
/// A prim that does not exist on its stage has the empty box, where C++
/// raises a coding error. An extent that cannot be computed fails the query
/// that reached the prim, where C++ warns and bounds the prim by nothing.
///
/// # Example
///
/// ```
/// use openusd::{gf, usd};
/// use openusd_schemas::geom::{self, Purpose, SphereSchema, XformableExt};
///
/// let stage = usd::Stage::builder()
///     .schema_registry(openusd_schemas::schema_registry())
///     .in_memory("scene.usda")?;
/// geom::Xform::define(&stage, "/World")?.set_translate(gf::vec3d(10.0, 0.0, 0.0))?;
/// let ball = geom::Sphere::define(&stage, "/World/Ball")?;
/// ball.create_radius_attr()?.set(2.0)?;
/// let world = stage.prim("/World")?;
///
/// let mut cache = geom::BBoxCache::new(None, [Purpose::Default]);
///
/// // The box around the children, in the prim's own space.
/// let untransformed = cache.untransformed_bound(&world)?;
/// assert_eq!(untransformed.aligned_range().min(), gf::vec3d(-2.0, -2.0, -2.0));
///
/// // The same box where the prim sits in the world.
/// let range = cache.world_bound(&world)?.aligned_range();
/// assert_eq!(range.min(), gf::vec3d(8.0, -2.0, -2.0));
/// assert_eq!(range.max(), gf::vec3d(12.0, 2.0, 2.0));
///
/// // The cache does not observe the stage: clear it after an edit.
/// ball.radius_attr().set(1.0)?;
/// cache.clear();
/// assert_eq!(cache.world_bound(&world)?.aligned_range().min(), gf::vec3d(9.0, -1.0, -1.0));
/// # Ok::<(), openusd_schemas::SchemaError>(())
/// ```
#[derive(Clone)]
pub struct BBoxCache {
    time: Option<usd::TimeCode>,
    base_time: BaseTime,
    purposes: Vec<Purpose>,
    use_extents_hint: bool,
    ignore_visibility: bool,
    /// What extents are computed with: the registry, and the prims whose
    /// extents this cache is bounding prims for.
    context: ExtentContext,
    xforms: XformCache,
    /// The resolved prims. An entry is inserted once its resolve has
    /// succeeded, so every entry is complete.
    entries: HashMap<Context, Entry>,
    types: SchemaTypes,
    /// Where the instances of each point instancer asked about are, at the
    /// cache's time.
    instancers: HashMap<usd::Prim, Placements>,
}

impl BBoxCache {
    /// A cache answering at `time`, where `None` is the default time, for
    /// the prims whose purpose is one of `purposes` (C++ the
    /// `UsdGeomBBoxCache` constructor).
    pub fn new(time: impl Into<Option<usd::TimeCode>>, purposes: impl IntoIterator<Item = Purpose>) -> Self {
        let time = time.into();
        Self {
            time,
            base_time: BaseTime::Unset,
            purposes: purposes.into_iter().collect(),
            use_extents_hint: false,
            ignore_visibility: false,
            context: ExtentContext::default(),
            xforms: XformCache::new(time),
            entries: HashMap::new(),
            types: SchemaTypes::default(),
            instancers: HashMap::new(),
        }
    }

    /// Compute extents with `extents` from now on, where a cache otherwise
    /// uses [`extent_registry`](crate::extent_registry). Every bound the
    /// cache holds is dropped.
    pub fn with_extents(self, extents: ExtentRegistry) -> Self {
        self.in_context(ExtentContext::new(extents))
    }

    /// Compute extents in `context` from now on: by its registry, and
    /// nested in the extents it is nested in. Every bound the cache holds
    /// is dropped.
    ///
    /// This is how an extent function bounds the prims its own prim's
    /// extent is made of: with a cache in the [`ExtentContext::nested`]
    /// context of the one it was handed.
    pub fn in_context(mut self, context: ExtentContext) -> Self {
        self.context = context;
        self.entries.clear();
        self.types = SchemaTypes::default();
        self
    }

    /// Whether a model is bounded by its `extentsHint` where it authors one
    /// (C++ the `useExtentsHint` constructor argument). Every bound the
    /// cache holds is dropped when the setting changes.
    ///
    /// With the hint in use, a prim that [is a model](usd::Prim::is_model),
    /// other than the pseudo-root, takes the extents its hint holds at the
    /// cache's time as its boxes, one for each purpose in
    /// [`Purpose::ORDERED`] the hint reaches, and nothing beneath it is
    /// visited. This is what bounds a model whose payload is not loaded. A
    /// model whose hint holds no extent is bounded by what is beneath it.
    ///
    /// A hinted prim's bound follows its transform and its visibility
    /// across [`set_time`](Self::set_time) as any other prim's does, where
    /// C++ invalidates it by the hint attribute alone.
    pub fn with_extents_hint(mut self, use_hint: bool) -> Self {
        if self.use_extents_hint != use_hint {
            self.use_extents_hint = use_hint;
            self.entries.clear();
        }
        self
    }

    /// Whether invisible prims are bounded too (C++ the `ignoreVisibility`
    /// constructor argument). Every bound the cache holds is dropped when
    /// the setting changes.
    pub fn with_ignore_visibility(mut self, ignore: bool) -> Self {
        if self.ignore_visibility != ignore {
            self.ignore_visibility = ignore;
            self.entries.clear();
        }
        self
    }

    /// `true` when a model is bounded by its `extentsHint` (C++
    /// `GetUseExtentsHint`).
    pub fn uses_extents_hint(&self) -> bool {
        self.use_extents_hint
    }

    /// `true` when invisible prims are bounded too (C++
    /// `GetIgnoreVisibility`).
    pub fn ignores_visibility(&self) -> bool {
        self.ignore_visibility
    }

    /// The time the cache answers at, `None` for the default time (C++
    /// `GetTime`).
    pub fn time(&self) -> Option<usd::TimeCode> {
        self.time
    }

    /// Answer at `time` from now on (C++ `SetTime`). The same time changes
    /// nothing. A change to or from the default time drops every bound, and
    /// a change between two other times drops the bounds that might differ
    /// between times: those of prims whose transform, extent, visibility or
    /// hint might vary, whose extent is computed, or with such a prim
    /// beneath them. Two more kinds are dropped where C++ keeps them. A
    /// prim with a prim beneath it that resets the transform stack is
    /// dropped where its own transform, or one above it, might vary: the
    /// prim beneath stays put while the rest moves. And a prim bounded by
    /// its children is dropped where a transform between it and the space
    /// they were unioned in might vary, so that a bound is the one a new
    /// cache would answer.
    pub fn set_time(&mut self, time: impl Into<Option<usd::TimeCode>>) {
        let time = time.into();
        if time == self.time {
            return;
        }
        // An attribute with a default value and one sample does not vary
        // between two times, and still reads differently at the default
        // time.
        let across_default = time.is_none() || self.time.is_none();
        self.entries.retain(|_, entry| !across_default && !entry.varying);
        self.instancers.clear();
        self.time = time;
        self.xforms.set_time(time);
    }

    /// The purposes whose prims are bounded (C++ `GetIncludedPurposes`).
    pub fn included_purposes(&self) -> &[Purpose] {
        &self.purposes
    }

    /// Bound the prims whose purpose is one of `purposes` from now on (C++
    /// `SetIncludedPurposes`). The cache keeps each prim's box for every
    /// purpose, so nothing is dropped.
    pub fn set_included_purposes(&mut self, purposes: impl IntoIterator<Item = Purpose>) {
        self.purposes = purposes.into_iter().collect();
    }

    /// The time point-instance bounds carry their instances from, `None`
    /// for the default time: the base time set, or else [`time`](Self::time)
    /// (C++ `GetBaseTime`).
    pub fn base_time(&self) -> Option<usd::TimeCode> {
        match self.base_time {
            BaseTime::Set(time) => time,
            BaseTime::Unset => self.time,
        }
    }

    /// `true` when a base time has been set (C++ `HasBaseTime`).
    pub fn has_base_time(&self) -> bool {
        matches!(self.base_time, BaseTime::Set(_))
    }

    /// Carry point instances from `time`, where `None` is the default time
    /// (C++ `SetBaseTime`). No bound is dropped.
    ///
    /// The base time and the cache's time are both numeric or both the
    /// default time. With one of each, the point-instance bounds are
    /// [`SchemaError::DefaultTimeMismatch`].
    pub fn set_base_time(&mut self, time: impl Into<Option<usd::TimeCode>>) {
        self.base_time = BaseTime::Set(time.into());
    }

    /// Carry point instances from the cache's time again (C++
    /// `ClearBaseTime`).
    pub fn clear_base_time(&mut self) {
        self.base_time = BaseTime::Unset;
    }

    /// Drop everything cached (C++ `Clear`), as needed after a stage edit.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.xforms.clear();
        self.types = SchemaTypes::default();
        self.instancers.clear();
    }

    /// The bound of `prim` in world space: its
    /// [untransformed bound](Self::untransformed_bound) under its
    /// local-to-world transform (C++ `ComputeWorldBound`).
    ///
    /// A prim with no geometry of any purpose has the empty box. One with
    /// geometry of other purposes than the included ones has an empty range
    /// under its transform, as in C++.
    pub fn world_bound(&mut self, prim: &usd::Prim) -> Result<gf::BBox3d, SchemaError> {
        let Some(mut bbox) = self.combined(prim, None, None)? else {
            return Ok(gf::BBox3d::default());
        };
        bbox.transform(self.xforms.local_to_world_transform(prim)?);
        Ok(bbox)
    }

    /// The bound of `prim` in its parent's space: its
    /// [untransformed bound](Self::untransformed_bound) under its local
    /// transform (C++ `ComputeLocalBound`). Whether the prim resets the
    /// transform stack plays no part.
    pub fn local_bound(&mut self, prim: &usd::Prim) -> Result<gf::BBox3d, SchemaError> {
        let Some(mut bbox) = self.combined(prim, None, None)? else {
            return Ok(gf::BBox3d::default());
        };
        bbox.transform(self.xforms.local_transform(prim)?.0);
        Ok(bbox)
    }

    /// The bound of `prim` in its own space, its own transform left out
    /// (C++ `ComputeUntransformedBound`).
    ///
    /// The box may still hold a matrix other than the identity, the one of
    /// the space its children were unioned in.
    pub fn untransformed_bound(&mut self, prim: &usd::Prim) -> Result<gf::BBox3d, SchemaError> {
        Ok(self.combined(prim, None, None)?.unwrap_or_default())
    }

    /// The bound of `prim` in the space of `ancestor`, the transform of
    /// `ancestor` itself left out (C++ `ComputeRelativeBound`).
    ///
    /// The transform is the prim's local-to-world one followed by the
    /// inverse of the ancestor's, so a prim between the two that resets the
    /// transform stack is honored as it is in world space. An `ancestor`
    /// that is not above `prim` gives a box that means nothing.
    pub fn relative_bound(&mut self, prim: &usd::Prim, ancestor: &usd::Prim) -> Result<gf::BBox3d, SchemaError> {
        self.bound_in(prim, ancestor, None, None)
    }

    /// The bound of what is beneath `prim` in world space, with the
    /// subtrees at `skip` left out, `prim` placed by `prim_override` where
    /// its own local-to-world transform would place it, and each subtree at
    /// a path of `ctm_overrides` placed in the world by the matrix there
    /// (C++ `ComputeWorldBoundWithOverrides`).
    ///
    /// The nearest override at or above a prim places it, as its
    /// local-to-world transform and with `prim_override` playing no part.
    /// The walk goes beneath a prim only where a skipped path or an
    /// override is beneath it, and bounds each prim it stops at as the prim
    /// a bound is asked for: its own visibility and purpose are not looked
    /// at. It reaches the prims a bound covers, unloaded ones among them,
    /// and goes beneath an instance through its instance proxies, where C++
    /// leaves out an unloaded prim and everything beneath an instance it
    /// would have to go beneath. The bounds the cache keeps are the
    /// ordinary ones: nothing an override or a skipped path shaped is kept.
    pub fn world_bound_with_overrides(
        &mut self,
        prim: &usd::Prim,
        skip: &BTreeSet<sdf::Path>,
        prim_override: gf::Mat4d,
        ctm_overrides: &HashMap<sdf::Path, gf::Mat4d>,
    ) -> Result<gf::BBox3d, SchemaError> {
        self.bound_with_overrides(prim, skip, Some(prim_override), ctm_overrides)
    }

    /// The bound of what is beneath `prim` in its own space, with the
    /// subtrees at `skip` left out and each subtree at a path of
    /// `ctm_overrides` placed in `prim`'s space by the matrix there (C++
    /// `ComputeUntransformedBound` with `pathsToSkip` and `ctmOverrides`).
    ///
    /// The nearest override at or above a prim places it. The walk is that
    /// of [`world_bound_with_overrides`](Self::world_bound_with_overrides).
    /// The bounds the cache keeps are the ordinary ones: nothing an override
    /// or a skipped path shaped is kept.
    pub fn untransformed_bound_with_overrides(
        &mut self,
        prim: &usd::Prim,
        skip: &BTreeSet<sdf::Path>,
        ctm_overrides: &HashMap<sdf::Path, gf::Mat4d>,
    ) -> Result<gf::BBox3d, SchemaError> {
        self.bound_with_overrides(prim, skip, None, ctm_overrides)
    }

    /// The bound of each instance of `instancer` at `indices`, in world
    /// space (C++ `ComputePointInstanceWorldBounds`); see
    /// [`point_instance_untransformed_bounds`](Self::point_instance_untransformed_bounds).
    pub fn point_instance_world_bounds(
        &mut self,
        instancer: &PointInstancer,
        indices: &[usize],
    ) -> Result<Vec<gf::BBox3d>, SchemaError> {
        let xform = self.xforms.local_to_world_transform(instancer.prim())?;
        self.point_instance_bounds(instancer, indices, xform)
    }

    /// The bound of each instance of `instancer` at `indices`, in the space
    /// of `ancestor`, the transform of `ancestor` itself left out (C++
    /// `ComputePointInstanceRelativeBounds`); see
    /// [`point_instance_untransformed_bounds`](Self::point_instance_untransformed_bounds).
    ///
    /// The instancer is taken to the ancestor's space as
    /// [`relative_bound`](Self::relative_bound) takes a prim there: by its
    /// local-to-world transform followed by the inverse of the ancestor's.
    /// C++ multiplies the two the other way round here, which is that
    /// transform only where the two commute.
    pub fn point_instance_relative_bounds(
        &mut self,
        instancer: &PointInstancer,
        indices: &[usize],
        ancestor: &usd::Prim,
    ) -> Result<Vec<gf::BBox3d>, SchemaError> {
        let xform = self.ancestor_transform(instancer.prim(), ancestor)?;
        self.point_instance_bounds(instancer, indices, xform)
    }

    /// The bound of each instance of `instancer` at `indices`, in the space
    /// of the instancer's parent (C++ `ComputePointInstanceLocalBounds`);
    /// see
    /// [`point_instance_untransformed_bounds`](Self::point_instance_untransformed_bounds).
    pub fn point_instance_local_bounds(
        &mut self,
        instancer: &PointInstancer,
        indices: &[usize],
    ) -> Result<Vec<gf::BBox3d>, SchemaError> {
        let xform = self.xforms.local_transform(instancer.prim())?.0;
        self.point_instance_bounds(instancer, indices, xform)
    }

    /// The bound of each instance of `instancer` at `indices`, in the
    /// instancer's own space (C++ `ComputePointInstanceUntransformedBounds`).
    /// The boxes are in the order of `indices`.
    ///
    /// An index is an instance's position in `protoIndices`, which C++ calls
    /// its `instanceId`. It is not a value of the `ids` attribute. An index
    /// that names no instance is [`SchemaError::InstanceIndexOutOfRange`].
    ///
    /// An instance's box is the
    /// [untransformed bound](Self::untransformed_bound) of its prototype
    /// root, under that root's local transform and then the instance's own
    /// placement at the cache's time, carried there from its
    /// [base time](Self::base_time). The mask plays no part: a pruned
    /// instance is bounded like any other.
    ///
    /// The prototype is the one `protoIndices` names at the cache's time,
    /// for the box and for the transform alike. C++ takes the prototype's
    /// transform by `protoIndices` at the base time, which gives an instance
    /// that changes prototype between the two times one prototype's
    /// geometry under the other's transform.
    ///
    /// The errors are those of
    /// [`PointInstancer::instance_transforms_at`], and
    /// [`SchemaError::NoValue`] for `protoIndices` without a value at the
    /// cache's time.
    pub fn point_instance_untransformed_bounds(
        &mut self,
        instancer: &PointInstancer,
        indices: &[usize],
    ) -> Result<Vec<gf::BBox3d>, SchemaError> {
        self.point_instance_bounds(instancer, indices, gf::Mat4d::IDENTITY)
    }

    /// The bound of each instance at `indices` in the instancer's space,
    /// then under `xform` (C++ `_ComputePointInstanceBoundsHelper`).
    fn point_instance_bounds(
        &mut self,
        instancer: &PointInstancer,
        indices: &[usize],
        xform: gf::Mat4d,
    ) -> Result<Vec<gf::BBox3d>, SchemaError> {
        if indices.is_empty() {
            return Ok(Vec::new());
        }
        // The placements are taken out of the cache while the prototypes
        // are bounded through it, and put back whatever comes of that.
        let key = instancer.prim().clone();
        let base_time = self.base_time();
        let placed = match self.instancers.remove(&key) {
            Some(placed) if placed.base_time == base_time => placed,
            _ => Placements::read(instancer, self.time, base_time)?,
        };
        let bounds = self.placed_bounds(instancer, &placed, indices, xform);
        self.instancers.insert(key, placed);
        bounds
    }

    /// The bound of each instance of `placed` at `indices`, in the
    /// instancer's space and then under `xform`.
    fn placed_bounds(
        &mut self,
        instancer: &PointInstancer,
        placed: &Placements,
        indices: &[usize],
        xform: gf::Mat4d,
    ) -> Result<Vec<gf::BBox3d>, SchemaError> {
        let stage = instancer.stage();
        // The box and the local transform of each prototype root asked for.
        let mut prototypes: HashMap<usize, (Option<gf::BBox3d>, gf::Mat4d)> = HashMap::new();
        let mut bounds = Vec::with_capacity(indices.len());
        for &index in indices {
            // `protoIndices` is read at the cache's time and the placements
            // are those of the base time, so the two can differ in length.
            let (Some(&prototype), Some(&placement)) = (placed.proto_indices.get(index), placed.transforms.get(index))
            else {
                return Err(SchemaError::InstanceIndexOutOfRange {
                    prim: instancer.path().clone(),
                    index,
                    instances: placed.proto_indices.len().min(placed.transforms.len()),
                });
            };
            // Every index was checked against the paths when they were read.
            let prototype = usize::try_from(prototype).unwrap_or_default();
            let (bbox, local) = if let Some(found) = prototypes.get(&prototype) {
                *found
            } else {
                let root = stage.prim(&placed.proto_paths[prototype])?;
                let found = (self.combined(&root, None, None)?, self.xforms.local_transform(&root)?.0);
                prototypes.insert(prototype, found);
                found
            };
            bounds.push(match bbox {
                Some(mut bbox) => {
                    bbox.transform(local * placement * xform);
                    bbox
                }
                None => gf::BBox3d::default(),
            });
        }
        Ok(bounds)
    }

    /// The bound of what is beneath `prim`, in world space where
    /// `prim_override` places it and in its own space with none (C++
    /// `_ComputeBoundWithOverridesHelper`).
    fn bound_with_overrides(
        &mut self,
        prim: &usd::Prim,
        skip: &BTreeSet<sdf::Path>,
        prim_override: Option<gf::Mat4d>,
        ctm_overrides: &HashMap<sdf::Path, gf::Mat4d>,
    ) -> Result<gf::BBox3d, SchemaError> {
        if !prim.is_valid()? {
            return Ok(gf::BBox3d::default());
        }
        // A prim above a skipped path or above an override is not bounded
        // whole: the walk goes on to the prims beneath it.
        let above: HashSet<sdf::Path> = (skip.iter().chain(ctm_overrides.keys()))
            .flat_map(sdf::Path::strict_ancestors)
            .collect();

        let mut result = gf::BBox3d::default();
        // Each prim is visited with what the prim above it hands down, so
        // that a bound asked for beneath `prim` is resolved from there.
        let mut stack = vec![(prim.clone(), None, None)];
        while let Some((visited, composed, above_visited)) = stack.pop() {
            let path = visited.path();
            if skip.contains(path) {
                continue;
            }
            if above.contains(path) {
                let context = Context {
                    prim: visited.clone(),
                    purpose: None,
                };
                let imageable = self.schema_type(&visited)?.imageable;
                let info = purpose_info(&context, imageable, above_visited.map(|above: Above| above.purpose))?;
                let moves = self.xforms.transform_might_be_time_varying(&visited)?;
                let (below, _) = self.below(&visited, info, moves, above_visited)?;
                // The prims a bound covers, an instance's through its
                // proxies, so that what is skipped or placed beneath one
                // is told from the rest of it.
                let children = visited.filtered_children_from(CHILDREN.with_instance_proxies(true), composed)?;
                stack.extend(
                    children
                        .into_iter()
                        .rev()
                        .map(|(child, composed)| (child, Some(composed), Some(below))),
                );
                continue;
            }

            // The nearest override from the visited prim up to `prim`,
            // which has none of its own, places the prim. With none, the
            // prim is placed as `prim` is.
            let overridden = visited
                .ancestors()
                .take_while(|ancestor| ancestor != prim)
                .find_map(|ancestor| ctm_overrides.get(ancestor.path()).map(|matrix| (ancestor, *matrix)));
            let (ancestor, placement) = match overridden {
                Some((at, matrix)) => (at, Some(matrix)),
                None => (prim.clone(), prim_override),
            };
            let mut bbox = self.bound_in(&visited, &ancestor, above_visited, composed)?;
            if let Some(placement) = placement {
                bbox.transform(placement);
            }
            result = gf::BBox3d::combine(&result, &bbox);
        }
        Ok(result)
    }

    /// The bound of `prim` in the space of `ancestor`, resolved with what
    /// the prim above `prim` hands down where a walk has it.
    fn bound_in(
        &mut self,
        prim: &usd::Prim,
        ancestor: &usd::Prim,
        above: Option<Above>,
        composed: Option<usd::ComposedStatus>,
    ) -> Result<gf::BBox3d, SchemaError> {
        let Some(mut bbox) = self.combined(prim, above, composed)? else {
            return Ok(gf::BBox3d::default());
        };
        bbox.transform(self.ancestor_transform(prim, ancestor)?);
        Ok(bbox)
    }

    /// The transform from `prim`'s space to `ancestor`'s: the prim's
    /// local-to-world transform, then the inverse of the ancestor's. An
    /// ancestor whose transform has no inverse counts as the identity, and
    /// a prim is in its own space as it stands.
    fn ancestor_transform(&mut self, prim: &usd::Prim, ancestor: &usd::Prim) -> Result<gf::Mat4d, SchemaError> {
        if prim == ancestor {
            return Ok(gf::Mat4d::IDENTITY);
        }
        let prim_ctm = self.xforms.local_to_world_transform(prim)?;
        let ancestor_ctm = self.xforms.local_to_world_transform(ancestor)?;
        Ok(prim_ctm * inverse(ancestor_ctm))
    }

    /// What extents are computed with.
    pub(super) fn context(&self) -> &ExtentContext {
        &self.context
    }

    /// The untransformed bound of `prim` for each purpose taken alone, as
    /// an axis-aligned range in the prim's own space, in the order of
    /// [`Purpose::ORDERED`]. A purpose the prim has no geometry of has the
    /// empty range.
    pub(super) fn purpose_ranges(
        &mut self,
        prim: &usd::Prim,
    ) -> Result<[gf::Range3d; Purpose::ORDERED.len()], SchemaError> {
        let context = Context {
            prim: prim.clone(),
            purpose: None,
        };
        self.resolve(&context, None, None)?;
        let Some(entry) = self.entries.get(&context) else {
            return Ok(Default::default());
        };
        let matrix = entry.boxes.matrix();
        Ok(Purpose::ORDERED.map(|purpose| match entry.boxes.range(purpose) {
            Some(range) => range.transformed(matrix),
            None => gf::Range3d::EMPTY,
        }))
    }

    /// The boxes of `prim` for the included purposes, combined in the order
    /// the purposes were given (C++ `_GetCombinedBBoxForIncludedPurposes`).
    /// `None` is a prim with no box for any purpose, the included ones or
    /// not, and a prim that does not exist.
    ///
    /// `above` and `composed` are what the prim above `prim` hands down and
    /// the status `prim` composed, where a walk comes to `prim` with them.
    fn combined(
        &mut self,
        prim: &usd::Prim,
        above: Option<Above>,
        composed: Option<usd::ComposedStatus>,
    ) -> Result<Option<gf::BBox3d>, SchemaError> {
        let context = Context {
            prim: prim.clone(),
            purpose: None,
        };
        self.resolve(&context, above, composed)?;
        let Some(entry) = self.entries.get(&context).filter(|entry| !entry.boxes.is_empty()) else {
            return Ok(None);
        };
        // The boxes share one matrix, under which their union is the box
        // of the union of their ranges.
        let ranges = self.purposes.iter().filter_map(|purpose| entry.boxes.range(*purpose));
        let range = ranges.fold(gf::Range3d::EMPTY, gf::Range3d::union);
        Ok(Some(match range.is_empty() {
            true => gf::BBox3d::default(),
            false => gf::BBox3d::new(range, entry.boxes.matrix()),
        }))
    }

    /// Resolve the entry of the prim of `context` where the cache does not
    /// hold it (C++ `_Resolve`). A prim that does not exist gets none.
    ///
    /// The walk keeps the prims it has gathered and is waiting on the
    /// children of in a stack of its own, so neither the depth of namespace
    /// nor the nesting of prototypes grows the call stack. A prim's entry
    /// is inserted when its children's are all there, which makes every
    /// entry complete and leaves the entries of finished subtrees behind a
    /// walk that fails.
    ///
    /// `above` and `composed` are what the prim above `prim` hands down and
    /// the status `prim` composed, where a walk comes to `prim` with them.
    /// With neither, what the prim's own children need is found by walking
    /// up from the prim.
    fn resolve(
        &mut self,
        context: &Context,
        above: Option<Above>,
        composed: Option<usd::ComposedStatus>,
    ) -> Result<(), SchemaError> {
        if self.entries.contains_key(context) || !context.prim.is_valid()? {
            return Ok(());
        }

        let root = Task {
            context: context.clone(),
            schema: None,
            above,
            composed,
            by_proxies: false,
        };
        let mut stack = vec![self.gather(root)?];
        while let Some(frame) = stack.last_mut() {
            let children = &frame.children;
            while children
                .get(frame.next)
                .is_some_and(|child| self.entries.contains_key(&child.context))
            {
                frame.next += 1;
            }
            if let Some(child) = children.get(frame.next) {
                let task = Task {
                    context: child.context.clone(),
                    schema: Some(child.schema),
                    above: frame.below,
                    composed: Some(child.composed.clone()),
                    by_proxies: false,
                };
                stack.push(self.gather(task)?);
            } else {
                let mut frame = stack.pop().expect("the frame just read");
                // A prim that resets the transform stack in a prototype
                // has its place in the world from its own transform, which
                // the entries the prototype's instances share cannot hold:
                // they place everything by the instance. Such an instance
                // is resolved again through its instance proxies.
                let resets = |child: &Child| child.resets || self.entries.get(&child.context).is_some_and(|e| e.resets);
                if let Some(retry) = frame.by_proxies.take().filter(|_| frame.children.iter().any(resets)) {
                    stack.push(self.gather(retry)?);
                    continue;
                }
                // TODO(rayon): the folds of sibling subtrees are
                // independent once their inputs are gathered, and
                // computing them over those owned values needs no
                // thread-safe stage. Gathering reads the stage and
                // stays on one thread until stage access is
                // thread-safe. An `ExtentFn` is an arbitrary callback
                // over a prim and needs the stage wherever it runs:
                // only the pure functions under it, which take the
                // sizes as values, could run on workers.
                let entry = fold(&frame, &self.entries);
                self.entries.insert(frame.context, entry);
            }
        }
        Ok(())
    }

    /// Read from the stage everything the entry of `task`'s prim is folded
    /// from: its own boxes where its extent or its hint bounds it, whether
    /// any of that might change with time, and the children to resolve
    /// with the matrix that takes each to the space they are unioned in
    /// (C++ `_ResolvePrim` up to the tasks it spawns).
    fn gather(&mut self, task: Task) -> Result<Frame, SchemaError> {
        let Task {
            context,
            schema,
            above,
            composed,
            by_proxies,
        } = task;
        let prim = context.prim.clone();
        let time = self.time;
        let schema = match schema {
            Some(schema) => schema,
            None => self.schema_type(&prim)?,
        };
        let info = purpose_info(&context, schema.imageable, above.map(|above| above.purpose))?;

        // The prim's transform and visibility do not change its boxes.
        // They change what the boxes add to its parent's, which is dropped
        // with this entry.
        let moves = self.xforms.transform_might_be_time_varying(&prim)?;
        let mut varying = moves;
        if !self.ignore_visibility && schema.imageable {
            let imageable = Imageable::from_prim_unchecked(prim.clone());
            varying |= imageable.visibility_attr().might_be_time_varying()?;
        }
        let mut frame = Frame {
            context,
            own: Ranges::default(),
            varying,
            moves,
            frame_moves: false,
            to_local: gf::Mat4d::IDENTITY,
            below: None,
            by_proxies: None,
            children: Vec::new(),
            next: 0,
        };

        if self.use_extents_hint && !prim.path().is_abs_root() && prim.is_model()? {
            // C++ reads the hint whether or not the API is applied.
            let model = ModelAPI::from_prim_unchecked(prim.clone());
            // A hint that holds no extent at this time may hold one at
            // another.
            frame.varying |= model.extents_hint_attr().might_be_time_varying()?;
            let extents = model.extents_hint_at(time)?.unwrap_or_default();
            if !extents.is_empty() {
                for (own, extent) in frame.own.iter_mut().zip(extents) {
                    *own = Some(gf::Range3d::from(extent)).filter(|range| !range.is_empty());
                }
                return Ok(frame);
            }
        }

        if schema.boundable {
            let boundable = Boundable::from_prim_unchecked(prim.clone());
            frame.varying |= boundable.extent_attr().might_be_time_varying()?;
            let extent = if let Some(extent) = authored_extent(&boundable, time)? {
                Some(extent)
            } else {
                let compute = schema.extent_fn;
                // What a function computes an extent from is its own
                // affair, so a computed extent is taken to differ at each
                // time, whether or not the function answers one at this
                // time.
                frame.varying |= compute.is_some();
                match compute {
                    Some(compute) => compute(&prim, time, None, &self.context)?,
                    None => None,
                }
            };
            // An extent that holds nothing, that of a mesh with no points
            // say, is no box.
            let range = extent.map(gf::Range3d::from).filter(|range| !range.is_empty());
            frame.own[slot(info.purpose)] = range;
            return Ok(frame);
        }

        // Only a prim bounded by its children needs the space they are
        // unioned in.
        let (handed, frame_moves) = self.below(&prim, info, moves, above)?;
        frame.moves = handed.moves;
        let inverse_enclosing = handed.inverse_component;
        let ctm = self.xforms.local_to_world_transform(&prim)?;
        // A transform that flattens space has no inverse to take the union
        // back to the prim's own space by. The children are then unioned in
        // that space itself, each placed by its own local transform.
        let local_to_component = ctm * inverse_enclosing;
        let (local_to_component, own_space) = match local_to_component.inverse() {
            Some(to_local) => {
                frame.to_local = to_local;
                (local_to_component, false)
            }
            None => (gf::Mat4d::IDENTITY, true),
        };
        // A union taken in the prim's own space follows no transform above.
        frame.frame_moves = frame_moves && !own_space;

        // An instance is bounded by its prototype's children, which every
        // instance with the same inheritable purpose shares the entries of.
        // A prototype's prims sit in the prototype's own space, which the
        // instance's place in its component takes them out of.
        // The listing that found the prim may already say it is no
        // instance.
        let instance = composed.as_ref().and_then(usd::ComposedStatus::is_instance);
        let prototype = match by_proxies || instance == Some(false) {
            true => None,
            false => prim.prototype()?,
        };
        let by_local = prototype.is_some() || own_space;
        let (holder, purpose, below) = if let Some(prototype) = &prototype {
            let purpose = info.inheritable_purpose();
            let below = Above {
                purpose: PurposeInfo {
                    purpose: purpose.unwrap_or_default(),
                    is_inheritable: purpose.is_some(),
                },
                inverse_component: gf::Mat4d::IDENTITY,
                moves: false,
                frame_moves: false,
            };
            frame.by_proxies = Some(Task {
                context: frame.context.clone(),
                schema: Some(schema),
                above,
                composed: composed.clone(),
                by_proxies: true,
            });
            (prim.stage().prim(prototype)?, purpose, below)
        } else {
            (prim.clone(), frame.context.purpose, handed)
        };
        frame.below = Some(below);

        // TODO(rayon): the children of an instance are a prototype's, and
        // prototypes with no dependency on each other resolve
        // independently, under the constraints the fold in `resolve` names.
        // An instance resolved through its instance proxies lists them,
        // and they list theirs under either predicate.
        let listed = CHILDREN.with_instance_proxies(by_proxies);
        // A prototype's children are listed from the prototype root, which
        // the walk did not list and has no status of.
        let composed = composed.filter(|_| prototype.is_none());
        for (child, composed) in holder.filtered_children_from(listed, composed)? {
            let schema = self.schema_type(&child)?;
            // A prim of no type, or of a type the registry does not know,
            // may hold imageable prims. A prim of any other type that is
            // not imageable bounds nothing.
            if schema.typed && !schema.imageable {
                continue;
            }
            if !self.ignore_visibility && schema.imageable {
                let imageable = Imageable::from_prim_unchecked(child.clone());
                if is_invisible(&imageable, time)? {
                    // The parent's bound changes when the child turns
                    // visible.
                    frame.varying |= imageable.visibility_attr().might_be_time_varying()?;
                    continue;
                }
            }

            let to_component = match by_local {
                true => self.xforms.local_transform(&child)?.0 * local_to_component,
                false => self.xforms.local_to_world_transform(&child)? * inverse_enclosing,
            };
            // A child that resets the transform stack is placed by its own
            // transform alone, whatever is above it. Where it sits in its
            // parent's space then changes with every transform above.
            let resets = self.xforms.resets_xform_stack(&child)?;
            // The child's place in the world is not one the prim's
            // flattened space reaches, so no box in that space holds it.
            if resets && own_space && prototype.is_none() {
                return Err(SchemaError::ResetBeneathFlattened {
                    prim: child.path().clone(),
                    ancestor: prim.path().clone(),
                });
            }
            frame.children.push(Child {
                context: Context { prim: child, purpose },
                schema,
                composed,
                to_component,
                resets,
            });
        }
        Ok(frame)
    }

    /// What the children of `prim` are resolved with, from what the prim
    /// above `prim` hands down, and whether the space `prim` unions its
    /// children in moves against `prim` with a transform above it. `info`
    /// is the prim's purpose and `moves` whether its own transform might
    /// differ between two times. With no `above`, what is above the prim is
    /// found by walking up from it.
    fn below(
        &mut self,
        prim: &usd::Prim,
        info: PurposeInfo,
        moves: bool,
        above: Option<Above>,
    ) -> Result<(Above, bool), SchemaError> {
        let above = match above {
            Some(above) => above,
            None => self.above(prim)?,
        };
        // A component unions its children in its own space, and so do the
        // prims beneath it down to the next one: what is above the
        // component moves that space and them alike.
        let component = is_component_kind(prim)?;
        let below = Above {
            purpose: info,
            inverse_component: match component {
                true => inverse(self.xforms.local_to_world_transform(prim)?),
                false => above.inverse_component,
            },
            moves: moves || above.moves,
            frame_moves: !component && (moves || above.frame_moves),
        };
        Ok((below, !component && above.frame_moves))
    }

    /// What the prims above `prim` hand down to it, less a purpose, when
    /// none of them was resolved with it (C++ `_GetNearestComponent` for
    /// the space): the space of the nearest component or subcomponent above
    /// `prim`, the world's where there is none, and which transforms above
    /// might differ between two times.
    fn above(&mut self, prim: &usd::Prim) -> Result<Above, SchemaError> {
        let mut inverse_component = None;
        let (mut moves, mut frame_moves) = (false, false);
        for prim in prim.ancestors().skip(1) {
            let varies = self.xforms.transform_might_be_time_varying(&prim)?;
            moves |= varies;
            if inverse_component.is_none() {
                match is_component_kind(&prim)? {
                    true => inverse_component = Some(inverse(self.xforms.local_to_world_transform(&prim)?)),
                    false => frame_moves |= varies,
                }
            }
            if moves && inverse_component.is_some() {
                break;
            }
        }
        Ok(Above {
            purpose: PurposeInfo::default(),
            inverse_component: inverse_component.unwrap_or(gf::Mat4d::IDENTITY),
            moves,
            frame_moves,
        })
    }

    /// What the cache asks of the schema type of `prim`, answered once for
    /// each type of each schema registry and kept.
    fn schema_type(&mut self, prim: &usd::Prim) -> openusd::Result<SchemaType> {
        let registry = prim.stage().schema_registry();
        let info = prim.prim_type_info()?;
        let name = info.schema_type_name();
        let (_, types) = (self.types.by_registry)
            .entry(Arc::as_ptr(registry).addr())
            .or_insert_with(|| (registry.clone(), HashMap::new()));
        if let Some(schema) = types.get(name) {
            return Ok(*schema);
        }
        let is_a = |base: &'static str| registry.is_a(name, &tf::Token::new(base));
        let boundable = is_a(tokens::BOUNDABLE);
        let schema = SchemaType {
            typed: is_a(usd::tokens::TYPED),
            imageable: is_a(tokens::IMAGEABLE),
            boundable,
            extent_fn: match boundable {
                true => self.context.extents().extent_fn(prim)?,
                false => None,
            },
        };
        types.insert(name.clone(), schema);
        Ok(schema)
    }
}

/// A prim with the purpose it would inherit from the instance above it (C++
/// `_PrimContext`): what an entry is keyed by.
///
/// The purpose is `None` for a prim outside a prototype, and for a prim in
/// a prototype whose instance has no purpose to hand down. A prim in a
/// prototype has one entry for each purpose its instances hand down, since
/// its own purpose may come from theirs.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Context {
    prim: usd::Prim,
    purpose: Option<Purpose>,
}

/// The base time of a cache.
#[derive(Clone, Copy)]
enum BaseTime {
    /// None is set: the cache's time is the base time.
    Unset,
    /// The time set, where `None` is the default time.
    Set(Option<usd::TimeCode>),
}

/// The range of a prim's subtree for each purpose, in the order of
/// [`Purpose::ORDERED`], `None` for a purpose the subtree has no geometry
/// of.
type Ranges = [Option<gf::Range3d>; Purpose::ORDERED.len()];

/// What the cache holds for a resolved prim.
#[derive(Clone)]
struct Entry {
    /// The box of the prim's subtree for each purpose, in the prim's own
    /// space.
    boxes: Boxes,
    /// Whether anything that decides what the prim adds to its parent's
    /// boxes might differ between two times: what its own boxes come from,
    /// and its transform and visibility, which place the boxes in the
    /// parent's union or keep them out of it.
    varying: bool,
    /// Whether a prim beneath this one, among those its boxes are unioned
    /// from, resets the transform stack. Such a prim stays where it is
    /// when a prim above this one moves, so its place in this prim's space
    /// follows every transform at and above this prim.
    resets: bool,
}

/// The box of a prim's subtree for each purpose, all under one matrix.
///
/// Most prims are bounded by their own extent: one purpose's range, under
/// the identity. That case is held in place, and the general one behind a
/// pointer, so that an entry is the size of the first.
#[derive(Clone)]
enum Boxes {
    /// No geometry of any purpose.
    Empty,
    /// The range of one purpose, under the identity.
    One(Purpose, gf::Range3d),
    /// The range of each purpose, under a matrix.
    Placed(Box<(Ranges, gf::Mat4d)>),
}

impl Boxes {
    /// The boxes of `ranges` under `matrix`.
    fn new(ranges: &Ranges, matrix: gf::Mat4d) -> Self {
        let mut held = Purpose::ORDERED
            .into_iter()
            .zip(ranges)
            .filter_map(|(purpose, range)| Some((purpose, (*range)?)));
        match (held.next(), held.next()) {
            (None, _) => Boxes::Empty,
            (Some((purpose, range)), None) if matrix == gf::Mat4d::IDENTITY => Boxes::One(purpose, range),
            _ => Boxes::Placed(Box::new((*ranges, matrix))),
        }
    }

    /// `true` when no purpose has a range.
    fn is_empty(&self) -> bool {
        matches!(self, Boxes::Empty)
    }

    /// The matrix every one of the boxes has: the one from the space the
    /// prim's children were unioned in to the prim's own, and the identity
    /// for a prim bounded by its extent.
    fn matrix(&self) -> gf::Mat4d {
        match self {
            Boxes::Placed(placed) => placed.1,
            Boxes::Empty | Boxes::One(..) => gf::Mat4d::IDENTITY,
        }
    }

    /// The range of the box of `purpose`, `None` where the subtree has no
    /// geometry of it.
    fn range(&self, purpose: Purpose) -> Option<gf::Range3d> {
        match self {
            Boxes::Empty => None,
            Boxes::One(held, range) => (*held == purpose).then_some(*range),
            Boxes::Placed(placed) => placed.0[slot(purpose)],
        }
    }
}

/// Where the instances of a point instancer are at the cache's time,
/// carried there from a base time. Kept so that asking for the instances a
/// few at a time reads the instancer once.
#[derive(Clone)]
struct Placements {
    /// The base time the instances were carried from.
    base_time: Option<usd::TimeCode>,
    /// The prototype of each instance at the cache's time.
    proto_indices: Vec<i32>,
    /// The prototype roots, each of which an index of `proto_indices`
    /// names.
    proto_paths: Vec<sdf::Path>,
    /// The transform of each instance in the instancer's space, its
    /// prototype's own left out, for every instance the mask keeps or not.
    transforms: Vec<gf::Mat4d>,
}

impl Placements {
    /// Read where the instances of `instancer` are at `time`, carried there
    /// from `base_time`.
    fn read(
        instancer: &PointInstancer,
        time: Option<usd::TimeCode>,
        base_time: Option<usd::TimeCode>,
    ) -> Result<Self, SchemaError> {
        let Some(proto_indices) = instancer.proto_indices_at(time)? else {
            return Err(SchemaError::NoValue {
                attribute: instancer.proto_indices_attr().path().clone(),
            });
        };
        let proto_paths = instancer.prototype_paths(&proto_indices)?;
        // The transforms keep every instance, so that an index reaches the
        // same instance in them as in `proto_indices`.
        let transforms =
            instancer.instance_transforms_at(time, base_time, ProtoXformInclusion::Exclude, MaskApplication::Ignore)?;
        Ok(Placements {
            base_time,
            proto_indices,
            proto_paths,
            transforms,
        })
    }
}

/// What the cache asks of a schema type.
#[derive(Clone, Copy)]
struct SchemaType {
    /// Whether a prim of the type is typed at all: a prim of no type, or of
    /// a type its stage's registry does not know, is not.
    typed: bool,
    /// Whether the type is `Imageable`.
    imageable: bool,
    /// Whether the type is `Boundable`.
    boundable: bool,
    /// The function that computes the type's extent, from the cache's
    /// registry, `None` for a type that computes none.
    extent_fn: Option<ExtentFn>,
}

/// What resolving a prim takes from the prim above it.
#[derive(Clone, Copy)]
struct Above {
    /// The purpose of the prim's parent.
    purpose: PurposeInfo,
    /// The inverse of the local-to-world transform of the nearest component
    /// above the prim, the identity where there is none and for a prim in
    /// a prototype resolved for an instance.
    inverse_component: gf::Mat4d,
    /// Whether the transform of a prim above this one might differ between
    /// two times. For a prim in a prototype resolved for an instance, the
    /// prims above are those of the prototype.
    moves: bool,
    /// Whether one of those transforms is of a prim beneath the nearest
    /// component, or of any prim above where there is no component. The
    /// space this prim's children are unioned in is that component's, or
    /// the world's, and such a transform moves this prim against it.
    frame_moves: bool,
}

/// A prim to resolve.
struct Task {
    context: Context,
    /// What the prim's schema type answers, or `None` for the prim a bound
    /// was asked for, which nothing listed.
    schema: Option<SchemaType>,
    /// What the prim above hands down, or `None` for the prim a bound was
    /// asked for, which nothing above was resolved with.
    above: Option<Above>,
    /// The status the prim composed when its parent listed it, or `None`
    /// for the prim a bound was asked for.
    composed: Option<usd::ComposedStatus>,
    /// Whether an instance is bounded by its instance proxies, where it is
    /// otherwise bounded by the prims of its prototype.
    by_proxies: bool,
}

/// A child whose boxes a prim's are unioned from.
struct Child {
    context: Context,
    /// What the child's schema type answers.
    schema: SchemaType,
    /// The status the child composed when it was listed, which the listing
    /// of its own children starts from.
    composed: usd::ComposedStatus,
    /// The matrix that takes the child's boxes to the space the prim
    /// unions its children in.
    to_component: gf::Mat4d,
    /// Whether the child resets the transform stack and is placed by its
    /// local-to-world transform, which then ties its place in the prim's
    /// space to the transforms above the prim.
    resets: bool,
}

/// A prim whose inputs are gathered and whose children are resolving.
struct Frame {
    context: Context,
    /// The ranges the prim's extent or hint gives it. A prim with either
    /// has no children here.
    own: Ranges,
    /// Whether what was gathered might differ between two times.
    varying: bool,
    /// Whether the transform of the prim, or of a prim above it, might
    /// differ between two times. For a prim with no children it is the
    /// prim's own alone.
    moves: bool,
    /// The matrix from the space the prim's children are unioned in to the
    /// prim's own. Where the prim's place in the space of its component has
    /// no inverse, the children are unioned in the prim's own space and
    /// this is the identity.
    to_local: gf::Mat4d,
    /// Whether the space the children are unioned in moves against the
    /// prim with a transform above it, so that the union holds only until
    /// one of those transforms changes.
    frame_moves: bool,
    /// What each child is resolved with, `None` for a prim with none.
    below: Option<Above>,
    /// For an instance bounded by the prims of its prototype, the task
    /// that bounds it by its instance proxies.
    by_proxies: Option<Task>,
    children: Vec<Child>,
    /// The first child that may still be without an entry.
    next: usize,
}

/// What each schema type the cache has met answers, for each schema
/// registry it met the type in.
///
/// A registry is keyed by the address of its `Arc`, and the clone held
/// beside the answers keeps that allocation alive. An address therefore
/// names one registry for as long as its key is here.
#[derive(Clone, Default)]
struct SchemaTypes {
    by_registry: HashMap<usize, (Arc<usd::SchemaRegistry>, HashMap<tf::Token, SchemaType>)>,
}

/// The children a bound covers: active, defined and not abstract. Unloaded
/// prims are among them, since a hint may bound a model whose payload is
/// not loaded.
const CHILDREN: usd::PrimPredicate = usd::PrimPredicate::new(
    usd::PrimStatus::ACTIVE.union(usd::PrimStatus::DEFINED),
    usd::PrimStatus::ABSTRACT,
);

/// The entry of the prim of `frame`, from what was gathered for it and the
/// entries of its children in `entries` (C++ `_ResolvePrim` from the
/// accumulation on).
///
/// The children are unioned in the order the frame holds them, purpose by
/// purpose, and the union is stored under the matrix that takes it back to
/// the prim's own space.
fn fold(frame: &Frame, entries: &HashMap<Context, Entry>) -> Entry {
    let mut varying = frame.varying;
    let mut resets = false;
    let mut ranges = Ranges::default();
    for child in &frame.children {
        let Some(entry) = entries.get(&child.context) else {
            continue;
        };
        varying |= entry.varying;
        resets |= child.resets || entry.resets;
        let to_component = entry.boxes.matrix() * child.to_component;
        for (range, purpose) in ranges.iter_mut().zip(Purpose::ORDERED) {
            if let Some(child_range) = entry.boxes.range(purpose) {
                *range = Some(range.unwrap_or_default().union(child_range.transformed(to_component)));
            }
        }
    }
    // A prim that resets the transform stack beneath this one keeps its
    // place while this one moves with what is above it, so the union holds
    // only until one of those transforms changes.
    varying |= resets && frame.moves;
    let boxes = if ranges.iter().all(Option::is_none) {
        Boxes::new(&frame.own, gf::Mat4d::IDENTITY)
    } else {
        // The ranges are those of the space the children were unioned in,
        // which a transform between it and the prim turns under them.
        varying |= frame.frame_moves;
        Boxes::new(&ranges, frame.to_local)
    };
    Entry { boxes, varying, resets }
}

/// The purpose of the prim of `context`, from its parent's where the walk
/// resolved one (C++ `_ComputePurposeInfo`). `imageable` is whether the
/// prim's type is.
fn purpose_info(context: &Context, imageable: bool, parent: Option<PurposeInfo>) -> Result<PurposeInfo, SchemaError> {
    let view = Imageable::from_prim_unchecked(context.prim.clone());
    let Some(parent) = parent else {
        // A prototype root has no purpose of its own. It stands for what
        // its instance hands down.
        if context.prim.is_prototype()? {
            return Ok(PurposeInfo {
                purpose: context.purpose.unwrap_or_default(),
                is_inheritable: context.purpose.is_some(),
            });
        }
        return Ok(view.purpose_info()?);
    };
    Ok(purpose_below(imageable.then_some(&view), parent)?)
}

/// `true` when `prim`'s own `kind` is a component or a subcomponent kind,
/// whatever is above it (C++ `_IsComponentOrSubComponent`).
fn is_component_kind(prim: &usd::Prim) -> openusd::Result<bool> {
    let kinds = prim.stage().schema_registry().kinds();
    Ok(prim
        .kind()?
        .is_some_and(|kind| kinds.is_component(&kind) || kinds.is_subcomponent(&kind)))
}

/// The place of `purpose` in [`Purpose::ORDERED`], which is where
/// [`Ranges`] and an `extentsHint` hold its box.
fn slot(purpose: Purpose) -> usize {
    let place = Purpose::ORDERED.iter().position(|ordered| *ordered == purpose);
    place.expect("every purpose is ordered")
}

/// The inverse of `matrix`, or the identity where it has none.
fn inverse(matrix: gf::Mat4d) -> gf::Mat4d {
    matrix.inverse().unwrap_or(gf::Mat4d::IDENTITY)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeSet, HashMap};

    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf};

    use super::{BBoxCache, Boxes, Context, Entry};
    use crate::SchemaError;
    use crate::geom::boundable::tests::{stage_with, typed};
    use crate::geom::xformable::tests::assert_close;
    use crate::geom::{Cube, ExtentFn, PointInstancer, Purpose, Sphere, SphereSchema, tokens};

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    fn range(min: [f64; 3], max: [f64; 3]) -> gf::Range3d {
        gf::Range3d::new(min.into(), max.into())
    }

    #[track_caller]
    fn assert_range(found: gf::Range3d, expected: gf::Range3d) {
        let close = |a: gf::Vec3d, b: gf::Vec3d| (a - b).length() < 1e-5;
        assert!(
            close(found.min(), expected.min()) && close(found.max(), expected.max()),
            "{found:?} is not {expected:?}"
        );
    }

    fn default_cache() -> BBoxCache {
        BBoxCache::new(None, [Purpose::Default])
    }

    fn at(time: f64) -> Option<usd::TimeCode> {
        Some(usd::TimeCode::new(time))
    }

    /// The world-aligned range of the prim at `path`.
    fn world(cache: &mut BBoxCache, stage: &usd::Stage, path: &str) -> Result<gf::Range3d> {
        Ok(cache.world_bound(&stage.prim(path)?)?.aligned_range())
    }

    /// Whether `cache` holds an entry for the prim at `path`, outside any
    /// prototype.
    fn holds(cache: &BBoxCache, stage: &usd::Stage, path: &str) -> Result<bool> {
        let context = Context {
            prim: stage.prim(path)?,
            purpose: None,
        };
        Ok(cache.entries.contains_key(&context))
    }

    /// A static entry survives a change between two times and not one
    /// across the default time. An entry whose prim moves is dropped.
    #[test]
    fn set_time_drops_varying() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Static"
{
    def Sphere "Ball"
    {
        float3[] extent = [(-1, -1, -1), (1, 1, 1)]
    }
}

def Xform "Moving"
{
    double3 xformOp:translate.timeSamples = { 1: (0, 0, 0), 2: (5, 0, 0) }
    uniform token[] xformOpOrder = ["xformOp:translate"]

    def Sphere "Ball"
    {
        float3[] extent = [(-1, -1, -1), (1, 1, 1)]
    }
}
"#,
        )?;
        let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]);
        assert_range(world(&mut cache, &stage, "/")?, range([-1.0; 3], [1.0; 3]));
        assert!(holds(&cache, &stage, "/Static")? && holds(&cache, &stage, "/Moving")?);

        cache.set_time(at(1.0));
        assert!(holds(&cache, &stage, "/Moving")?, "the same time drops nothing");

        cache.set_time(at(2.0));
        assert_eq!(cache.time(), at(2.0));
        assert!(holds(&cache, &stage, "/Static")? && holds(&cache, &stage, "/Moving/Ball")?);
        assert!(!holds(&cache, &stage, "/Moving")? && !holds(&cache, &stage, "/")?);
        assert_range(world(&mut cache, &stage, "/")?, range([-1.0; 3], [6.0, 1.0, 1.0]));

        cache.set_time(None);
        assert!(cache.entries.is_empty());
        Ok(())
    }

    /// A prim that resets the transform stack stays where it is while a
    /// prim above it moves, and the bounds of the prims between the two
    /// follow.
    #[test]
    fn reset_stack_under_moving() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "A"
{
    double3 xformOp:translate.timeSamples = { 1: (0, 0, 0), 2: (10, 0, 0) }
    uniform token[] xformOpOrder = ["xformOp:translate"]

    def Xform "B"
    {
        def Cube "Fixed"
        {
            float3[] extent = [(-1, -1, -1), (1, 1, 1)]
            uniform token[] xformOpOrder = ["!resetXformStack!"]
        }
    }

    def Xform "C"
    {
        def Cube "Carried"
        {
            float3[] extent = [(-1, -1, -1), (1, 1, 1)]
        }
    }
}
"#,
        )?;
        let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]);
        for path in ["/A/B", "/A/C", "/A"] {
            assert_range(world(&mut cache, &stage, path)?, range([-1.0; 3], [1.0; 3]));
        }

        cache.set_time(at(2.0));
        // A prim bounded by its extent keeps its entry, and is carried by
        // the prims above.
        assert!(holds(&cache, &stage, "/A/C/Carried")? && !holds(&cache, &stage, "/A/B")?);
        assert_range(world(&mut cache, &stage, "/A/B")?, range([-1.0; 3], [1.0; 3]));
        assert_range(
            world(&mut cache, &stage, "/A/C")?,
            range([9.0, -1.0, -1.0], [11.0, 1.0, 1.0]),
        );
        assert_range(world(&mut cache, &stage, "/A")?, range([-1.0; 3], [11.0, 1.0, 1.0]));

        // Asked for first at the later time, the answers are the same.
        let mut fresh = BBoxCache::new(at(2.0), [Purpose::Default]);
        for path in ["/A/B", "/A/C", "/A"] {
            assert_range(world(&mut cache, &stage, path)?, world(&mut fresh, &stage, path)?);
        }
        Ok(())
    }

    /// A prim beneath a prim that turns is bounded at each time as a new
    /// cache bounds it, where the box it held was turned with the prim
    /// above. Beneath a component it keeps its box, which is in the
    /// component's space.
    #[test]
    fn turning_ancestor_matches_fresh() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "A"
{
    float xformOp:rotateZ.timeSamples = { 1: 45, 2: 0 }
    uniform token[] xformOpOrder = ["xformOp:rotateZ"]

    def Xform "Q"
    {
        def Cube "Cube"
        {
            float3[] extent = [(-1, -1, -1), (1, 1, 1)]
        }
    }

    def Xform "Model" (kind = "component")
    {
        def Xform "Q"
        {
            def Cube "Cube"
            {
                float3[] extent = [(-1, -1, -1), (1, 1, 1)]
            }
        }
    }
}
"#,
        )?;
        let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]);
        let half = 2f64.sqrt();
        assert_range(
            world(&mut cache, &stage, "/A")?,
            range([-half, -half, -1.0], [half, half, 1.0]),
        );

        cache.set_time(at(2.0));
        assert!(!holds(&cache, &stage, "/A/Q")? && holds(&cache, &stage, "/A/Model/Q")?);
        let mut fresh = BBoxCache::new(at(2.0), [Purpose::Default]);
        for path in ["/A", "/A/Q", "/A/Model", "/A/Model/Q"] {
            let prim = stage.prim(path)?;
            assert_eq!(cache.world_bound(&prim)?, fresh.world_bound(&prim)?, "{path}");
            assert_range(cache.world_bound(&prim)?.aligned_range(), range([-1.0; 3], [1.0; 3]));
        }
        Ok(())
    }

    /// A prim that resets the transform stack in a prototype is where its
    /// own transform puts it, bounded through the instance as through the
    /// instance's proxies. An instance with no such prim shares its
    /// prototype's entries.
    #[test]
    fn reset_stack_in_prototype() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Proto"
{
    def Xform "Grp"
    {
        def Cube "Fixed"
        {
            float3[] extent = [(-1, -1, -1), (1, 1, 1)]
            uniform token[] xformOpOrder = ["!resetXformStack!"]
        }

        def Cube "Carried"
        {
            float3[] extent = [(-1, -1, -1), (1, 1, 1)]
        }
    }
}

def Xform "A" (instanceable = true references = </Proto>)
{
    double3 xformOp:translate = (10, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]
}
"#,
        )?;
        let mut cache = default_cache();
        let whole = range([-1.0; 3], [11.0, 1.0, 1.0]);
        assert_range(world(&mut cache, &stage, "/A")?, whole);
        let mut by_proxy = default_cache();
        assert_range(world(&mut by_proxy, &stage, "/A/Grp")?, whole);
        assert_range(
            world(&mut by_proxy, &stage, "/A/Grp/Fixed")?,
            range([-1.0; 3], [1.0; 3]),
        );
        assert_range(world(&mut cache, &stage, "/")?, world(&mut by_proxy, &stage, "/")?);

        let (_dir, stage) = crate::tests::from_usda(INSTANCES)?;
        let mut cache = default_cache();
        world(&mut cache, &stage, "/A")?;
        assert!(!holds(&cache, &stage, "/A/Ball")?, "bounded by the prototype's prims");
        Ok(())
    }

    /// The override walk goes beneath an instance through its instance
    /// proxies, and bounds the rest of the instance a skipped path is in.
    #[test]
    fn overrides_cover_instances() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Proto"
{
    def Sphere "Near" {}

    def Sphere "Far"
    {
        double3 xformOp:translate = (50, 0, 0)
        uniform token[] xformOpOrder = ["xformOp:translate"]
    }
}

def Xform "World"
{
    def Xform "Inst" (instanceable = true references = </Proto>) {}

    def Sphere "Other"
    {
        double3 xformOp:translate = (0, 20, 0)
        uniform token[] xformOpOrder = ["xformOp:translate"]
    }
}
"#,
        )?;
        let world = stage.prim("/World")?;
        let mut cache = default_cache();
        let none = HashMap::new();
        let all = cache.untransformed_bound_with_overrides(&world, &BTreeSet::new(), &none)?;
        assert_range(all.aligned_range(), range([-1.0; 3], [51.0, 21.0, 1.0]));

        let skip = BTreeSet::from([sdf::path("/World/Inst/Far")?]);
        let found = cache.untransformed_bound_with_overrides(&world, &skip, &none)?;
        assert_range(found.aligned_range(), range([-1.0; 3], [1.0, 21.0, 1.0]));
        Ok(())
    }

    /// A prim whose transform flattens space bounds its children in its
    /// own space, and its transform is applied to that once.
    #[test]
    fn singular_parent_transform() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Flat"
{
    double3 xformOp:scale = (0, 2, 1)
    uniform token[] xformOpOrder = ["xformOp:scale"]

    def Cube "Cube" {}

    def Xform "Deep"
    {
        double3 xformOp:translate = (0, 5, 0)
        uniform token[] xformOpOrder = ["xformOp:translate"]

        def Cube "Cube" {}
    }
}

def Xform "FlatModel" (kind = "component")
{
    double3 xformOp:scale = (1, 0, 3)
    uniform token[] xformOpOrder = ["xformOp:scale"]

    def Cube "Cube" {}
}
"#,
        )?;
        let mut cache = default_cache();
        let flat = stage.prim("/Flat")?;
        let own = cache.untransformed_bound(&flat)?;
        assert_close(own.matrix(), gf::Mat4d::IDENTITY);
        assert_range(own.range(), range([-1.0; 3], [1.0, 6.0, 1.0]));
        assert_range(
            cache.world_bound(&flat)?.aligned_range(),
            range([0.0, -2.0, -1.0], [0.0, 12.0, 1.0]),
        );
        assert_range(
            world(&mut cache, &stage, "/Flat/Deep")?,
            range([0.0, 8.0, -1.0], [0.0, 12.0, 1.0]),
        );
        assert_range(
            world(&mut cache, &stage, "/FlatModel")?,
            range([-1.0, 0.0, -3.0], [1.0, 0.0, 3.0]),
        );

        // A prim relative to itself is in its own space, flattened or not.
        let whole = cache.untransformed_bound_with_overrides(&flat, &BTreeSet::new(), &HashMap::new())?;
        assert_eq!(whole, own);
        assert_eq!(cache.relative_bound(&flat, &flat)?, own);
        Ok(())
    }

    /// A prim that resets the transform stack beneath a prim whose space is
    /// flattened at one time and not at another cannot be placed at the
    /// first, and is placed anew at the second.
    #[test]
    fn reset_stack_under_flattening() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "A"
{
    double3 xformOp:scale.timeSamples = { 1: (0, 1, 1), 2: (1, 1, 1) }
    double3 xformOp:translate.timeSamples = { 1: (0, 0, 0), 2: (10, 0, 0) }
    uniform token[] xformOpOrder = ["xformOp:translate", "xformOp:scale"]

    def Xform "P"
    {
        def Cube "Fixed"
        {
            float3[] extent = [(-1, -1, -1), (1, 1, 1)]
            uniform token[] xformOpOrder = ["!resetXformStack!"]
        }
    }
}
"#,
        )?;
        let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]);
        // While the space above is flattened, the prim that resets the
        // stack is bounded where it is, and the prims that hold it cannot
        // place it in a space of their own.
        assert_range(world(&mut cache, &stage, "/A/P/Fixed")?, range([-1.0; 3], [1.0; 3]));
        for path in ["/A/P", "/A", "/"] {
            let refused = cache.world_bound(&stage.prim(path)?);
            assert!(
                matches!(
                    &refused,
                    Err(SchemaError::ResetBeneathFlattened { prim, ancestor })
                        if prim.as_str() == "/A/P/Fixed" && ancestor.as_str() == "/A/P"
                ),
                "{path}: {refused:?}"
            );
        }
        cache.set_time(at(2.0));
        assert!(!holds(&cache, &stage, "/A/P")?);
        let mut fresh = BBoxCache::new(at(2.0), [Purpose::Default]);
        assert_range(world(&mut cache, &stage, "/A/P")?, world(&mut fresh, &stage, "/A/P")?);
        assert_range(world(&mut cache, &stage, "/A/P")?, range([-1.0; 3], [1.0; 3]));
        Ok(())
    }

    /// A mesh whose points are animated follows the time where its extent
    /// is computed: with no `extent`, a blocked one, and one of one corner.
    #[test]
    fn animated_points_vary() -> Result {
        for extent in ["", "float3[] extent = None", "float3[] extent = [(0, 0, 0)]"] {
            let (_dir, stage) = crate::tests::from_usda(&format!(
                r#"#usda 1.0

def Xform "Root"
{{
    def Mesh "Mesh"
    {{
        {extent}
        point3f[] points.timeSamples = {{
            1: [(0, 0, 0), (1, 1, 1)],
            2: [(0, 0, 0), (3, 3, 3)],
        }}
    }}
}}
"#
            ))?;
            let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]);
            assert_range(world(&mut cache, &stage, "/Root")?, range([0.0; 3], [1.0; 3]));
            cache.set_time(at(2.0));
            assert_range(world(&mut cache, &stage, "/Root")?, range([0.0; 3], [3.0; 3]));
        }
        Ok(())
    }

    const INSTANCES: &str = r#"#usda 1.0

def Xform "Proto"
{
    def Sphere "Ball"
    {
        double radius = 2
    }
}

def Xform "A" (instanceable = true references = </Proto>)
{
    double3 xformOp:translate = (10, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]
}

def Xform "B" (instanceable = true references = </Proto>)
{
    double3 xformOp:translate = (20, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]
}
"#;

    /// Two instances of one prototype share the entry of the prototype's
    /// prim.
    #[test]
    fn prototype_entries_shared() -> Result {
        let (_dir, stage) = crate::tests::from_usda(INSTANCES)?;
        let mut cache = default_cache();
        assert_range(
            world(&mut cache, &stage, "/A")?,
            range([8.0, -2.0, -2.0], [12.0, 2.0, 2.0]),
        );
        assert_range(
            world(&mut cache, &stage, "/B")?,
            range([18.0, -2.0, -2.0], [22.0, 2.0, 2.0]),
        );

        let mut in_prototype = 0;
        for context in cache.entries.keys() {
            in_prototype += usize::from(context.prim.is_in_prototype()?);
        }
        assert_eq!(in_prototype, 1);
        Ok(())
    }

    /// The boxes of two instances do not depend on which was asked for
    /// first.
    #[test]
    fn instance_query_order() -> Result {
        let (_dir, stage) = crate::tests::from_usda(INSTANCES)?;
        let (a, b) = (stage.prim("/A")?, stage.prim("/B")?);
        let mut forward = default_cache();
        let first = (forward.world_bound(&a)?, forward.world_bound(&b)?);
        let mut backward = default_cache();
        let second_b = backward.world_bound(&b)?;
        assert_eq!(first, (backward.world_bound(&a)?, second_b));
        Ok(())
    }

    const COMPONENT: &str = r#"#usda 1.0

def Xform "World"
{
    double3 xformOp:translate = (0, 0, 7)
    uniform token[] xformOpOrder = ["xformOp:translate"]

    def Xform "Comp" (kind = "component")
    {
        float xformOp:rotateZ = 45
        uniform token[] xformOpOrder = ["xformOp:rotateZ"]

        def Xform "Geom"
        {
            double3 xformOp:translate = (2, 0, 0)
            uniform token[] xformOpOrder = ["xformOp:translate"]

            def Cube "A" {}

            def Cube "B"
            {
                double3 xformOp:translate = (4, 4, 0)
                uniform token[] xformOpOrder = ["xformOp:translate"]
            }
        }
    }

    def Xform "Plain"
    {
        float xformOp:rotateZ = 30
        uniform token[] xformOpOrder = ["xformOp:rotateZ"]

        def Xform "Geom"
        {
            def Cube "A" {}
        }
    }
}
"#;

    /// A prim beneath a component unions its children in the component's
    /// space, and keeps the matrix that takes the union back to its own.
    #[test]
    fn component_space_union() -> Result {
        let (_dir, stage) = crate::tests::from_usda(COMPONENT)?;
        let mut cache = default_cache();
        let union = range([1.0, -1.0, -1.0], [7.0, 5.0, 1.0]);

        let geom = cache.untransformed_bound(&stage.prim("/World/Comp/Geom")?)?;
        assert_range(geom.range(), union);
        assert_close(geom.matrix(), gf::Mat4d::translation([-2.0, 0.0, 0.0]));
        assert_range(geom.aligned_range(), range([-1.0; 3], [5.0, 5.0, 1.0]));

        let component = cache.untransformed_bound(&stage.prim("/World/Comp")?)?;
        assert_range(component.range(), union);
        assert_close(component.matrix(), gf::Mat4d::IDENTITY);

        // In world space the box is the component's, turned: wider than the
        // boxes of the two cubes each turned on its own.
        let found = world(&mut cache, &stage, "/World/Comp")?;
        let turn = gf::Mat4d::rotation_z(45f64.to_radians()) * gf::Mat4d::translation([0.0, 0.0, 7.0]);
        assert_range(found, union.transformed(turn));
        let leaves = (gf::BBox3d::new(range([1.0, -1.0, -1.0], [3.0, 1.0, 1.0]), turn).aligned_range())
            .union(gf::BBox3d::new(range([5.0, 3.0, -1.0], [7.0, 5.0, 1.0]), turn).aligned_range());
        let slack = gf::vec3d(1e-9, 1e-9, 1e-9);
        assert!(gf::Range3d::new(found.min() - slack, found.max() + slack).contains_range(leaves));
        assert!(found.size().x > leaves.size().x + 1.0, "{found:?} against {leaves:?}");
        Ok(())
    }

    /// A prim's box does not depend on whether it or a prim above it was
    /// asked for first, beneath a component and beneath none.
    #[test]
    fn ancestor_query_order() -> Result {
        let (_dir, stage) = crate::tests::from_usda(COMPONENT)?;
        for (above, below) in [
            ("/World", "/World/Comp/Geom"),
            ("/World/Comp", "/World/Comp/Geom"),
            ("/World", "/World/Plain/Geom"),
            ("/World/Plain", "/World/Plain/Geom"),
        ] {
            let (above, below) = (stage.prim(above)?, stage.prim(below)?);
            let mut down = default_cache();
            let first = (down.untransformed_bound(&above)?, down.untransformed_bound(&below)?);
            let mut up = default_cache();
            let below_first = up.untransformed_bound(&below)?;
            assert_eq!(first, (up.untransformed_bound(&above)?, below_first));
            assert!(!first.1.range().is_empty());
        }
        Ok(())
    }

    /// A prim whose children are turned differently has the same box, bit
    /// for bit, whether its children were resolved with it or one at a
    /// time before it, the last one first.
    #[test]
    fn merge_order_stable() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Root"
{
    def Cube "A"
    {
        float xformOp:rotateZ = 17
        uniform token[] xformOpOrder = ["xformOp:rotateZ"]
    }

    def Cube "B"
    {
        float xformOp:rotateX = 33
        double3 xformOp:translate = (0.1, 0.2, 0.3)
        uniform token[] xformOpOrder = ["xformOp:translate", "xformOp:rotateX"]
    }

    def Cube "C"
    {
        float xformOp:rotateY = 71
        uniform token[] xformOpOrder = ["xformOp:rotateY"]
    }
}
"#,
        )?;
        let root = stage.prim("/Root")?;
        let mut together = default_cache();
        let expected = together.world_bound(&root)?;

        let mut apart = default_cache();
        for child in ["/Root/C", "/Root/B", "/Root/A"] {
            apart.world_bound(&stage.prim(child)?)?;
        }
        let found = apart.world_bound(&root)?;
        let bits = |v: gf::Vec3d| [v.x.to_bits(), v.y.to_bits(), v.z.to_bits()];
        assert_eq!(bits(found.range().min()), bits(expected.range().min()));
        assert_eq!(bits(found.range().max()), bits(expected.range().max()));
        assert_eq!(found.matrix(), expected.matrix());
        Ok(())
    }

    /// A query that reaches a prim whose extent cannot be computed fails,
    /// and the cache goes on answering: the subtrees it finished, and the
    /// failure again.
    #[test]
    fn failed_query_reusable() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Good"
{
    def Sphere "Ball" {}
}

def Xform "Bad"
{
    def Points "Points"
    {
        point3f[] points = [(0, 0, 0), (1, 1, 1)]
        float[] widths = [1]
    }
}
"#,
        )?;
        let mut cache = default_cache();
        let root = stage.prim("/")?;
        let refused =
            |found: Result<gf::BBox3d>| matches!(found, Err(SchemaError::WidthCountMismatch { found: 1, expected: 2 }));
        assert!(refused(cache.world_bound(&root)));
        assert!(holds(&cache, &stage, "/Good")?, "a finished subtree is kept");
        assert!(!holds(&cache, &stage, "/")? && !holds(&cache, &stage, "/Bad")?);

        assert_range(world(&mut cache, &stage, "/Good")?, range([-1.0; 3], [1.0; 3]));
        assert!(refused(cache.world_bound(&root)));
        assert!(refused(cache.world_bound(&stage.prim("/Bad")?)));
        Ok(())
    }

    /// A prim bounded by its extent is held as one range, a prim with no
    /// geometry as nothing, and only a prim that unions children carries a
    /// matrix, behind a pointer.
    #[test]
    fn entries_compact() -> Result {
        let (_dir, stage) = crate::tests::from_usda(COMPONENT)?;
        let mut cache = default_cache();
        cache.world_bound(&stage.prim("/World")?)?;
        cache.world_bound(&stage.prim("/World/Comp/Geom/A")?)?;
        let boxes = |path: &str| -> Result<Boxes> {
            let context = Context {
                prim: stage.prim(path)?,
                purpose: None,
            };
            Ok(cache.entries[&context].boxes.clone())
        };
        assert!(matches!(boxes("/World/Comp/Geom/A")?, Boxes::One(Purpose::Default, _)));
        assert!(matches!(boxes("/World/Comp/Geom")?, Boxes::Placed(_)));
        assert!(size_of::<Entry>() <= 64, "{}", size_of::<Entry>());

        let empty = crate::tests::stage("anon.usda")?;
        let scope = empty.define_typed_prim("/Scope", "Scope")?;
        cache.world_bound(&scope)?;
        let context = Context {
            prim: scope,
            purpose: None,
        };
        assert!(cache.entries[&context].boxes.is_empty());
        Ok(())
    }

    /// A prim that does not exist has the empty box in every space, and
    /// nothing is cached for it.
    #[test]
    fn missing_prim_empty() -> Result {
        let stage = crate::tests::stage("anon.usda")?;
        let root = stage.prim("/")?;
        let missing = stage.prim("/Missing")?;
        let mut cache = default_cache();
        assert_eq!(cache.world_bound(&missing)?, gf::BBox3d::default());
        assert_eq!(cache.local_bound(&missing)?, gf::BBox3d::default());
        assert_eq!(cache.untransformed_bound(&missing)?, gf::BBox3d::default());
        assert_eq!(cache.relative_bound(&missing, &root)?, gf::BBox3d::default());
        let none = cache.untransformed_bound_with_overrides(&missing, &BTreeSet::new(), &HashMap::new())?;
        assert_eq!(none, gf::BBox3d::default());
        assert!(cache.entries.is_empty());
        assert_eq!(cache.world_bound(&root)?, gf::BBox3d::default());
        Ok(())
    }

    /// The base time is the cache's time until one is set, and the default
    /// time is one that can be set.
    #[test]
    fn base_time_defaults() {
        let mut cache = BBoxCache::new(at(3.0), [Purpose::Default]);
        assert!(!cache.has_base_time());
        assert_eq!(cache.base_time(), at(3.0));
        cache.set_time(at(4.0));
        assert_eq!(cache.base_time(), at(4.0));

        cache.set_base_time(usd::TimeCode::new(1.0));
        assert!(cache.has_base_time());
        assert_eq!(cache.base_time(), at(1.0));
        cache.set_base_time(None);
        assert!(cache.has_base_time());
        assert_eq!(cache.base_time(), None);

        cache.clear_base_time();
        assert!(!cache.has_base_time());
        assert_eq!(cache.base_time(), at(4.0));
    }

    /// A cache given another registry drops what it computed with the
    /// first.
    #[test]
    fn with_extents_invalidates() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Root"
{
    def Sphere "Ball"
    {
        double radius = 5
    }
}
"#,
        )?;
        let mut cache = default_cache();
        assert_range(world(&mut cache, &stage, "/Root")?, range([-5.0; 3], [5.0; 3]));

        let cube: ExtentFn = |_prim, _time, transform, _context| Ok(Some(Cube::extent_from(2.0, transform)));
        let mut extents = crate::extent_registry().clone();
        extents.register(tokens::SPHERE, cube);
        let mut cache = cache.with_extents(extents);
        assert_range(world(&mut cache, &stage, "/Root")?, range([-1.0; 3], [1.0; 3]));
        Ok(())
    }

    /// A point instancer's prototypes are bounded by the functions of the
    /// cache that bounds the instancer.
    #[test]
    fn instancer_by_cache_extents() -> Result {
        let (_dir, stage, instancer) = instancer("int[] protoIndices = [0]", "point3f[] positions = [(0, 0, 0)]")?;
        let cube: ExtentFn = |_prim, _time, transform, _context| Ok(Some(Cube::extent_from(6.0, transform)));
        let mut extents = crate::extent_registry().clone();
        extents.register(tokens::SPHERE, cube);
        let mut cache = default_cache().with_extents(extents);

        let prototype = stage.prim("/World/Inst/Protos/Small")?;
        assert_range(
            cache.untransformed_bound(&prototype)?.range(),
            range([-3.0; 3], [3.0; 3]),
        );
        let own = cache.untransformed_bound(instancer.prim())?;
        assert_range(own.range(), range([-3.0; 3], [3.0; 3]));
        let instances = cache.point_instance_untransformed_bounds(&instancer, &[0])?;
        assert_range(instances[0].aligned_range(), range([-3.0; 3], [3.0; 3]));

        // The registry of this crate's schemas bounds the same sphere by
        // its radius.
        let mut plain = default_cache();
        assert_range(
            plain.untransformed_bound(instancer.prim())?.range(),
            range([-1.0; 3], [1.0; 3]),
        );
        Ok(())
    }

    /// One cache over two stages bounds a type by what each stage's own
    /// schema registry says it derives from.
    #[test]
    fn registries_kept_apart() -> Result {
        let round = stage_with(&[typed("Widget", &[tokens::SPHERE])])?;
        let bare = stage_with(&[typed("Widget", &[tokens::BOUNDABLE])])?;
        for stage in [&round, &bare] {
            let widget = stage.define_typed_prim("/Widget", "Widget")?;
            Sphere::from_prim_unchecked(widget).create_radius_attr()?.set(3.0)?;
        }
        let (round, bare) = (round.prim("/Widget")?, bare.prim("/Widget")?);

        for order in [[&round, &bare], [&bare, &round]] {
            let mut cache = default_cache();
            for prim in order {
                cache.world_bound(prim)?;
            }
            assert_range(cache.world_bound(&round)?.aligned_range(), range([-3.0; 3], [3.0; 3]));
            assert!(cache.world_bound(&bare)?.range().is_empty());
            assert_eq!(cache.types.by_registry.len(), 2);
        }
        Ok(())
    }

    const OVERRIDES: &str = r#"#usda 1.0

def Xform "Root"
{
    double3 xformOp:translate = (1, 0, 0)
    uniform token[] xformOpOrder = ["xformOp:translate"]

    def Sphere "A" {}

    def Xform "B"
    {
        double3 xformOp:translate = (10, 0, 0)
        uniform token[] xformOpOrder = ["xformOp:translate"]

        def Sphere "Ball" {}
    }

    def Sphere "C"
    {
        double3 xformOp:translate = (20, 0, 0)
        uniform token[] xformOpOrder = ["xformOp:translate"]
    }
}
"#;

    /// A skipped path leaves its subtree out of the bound.
    #[test]
    fn overrides_skip() -> Result {
        let (_dir, stage) = crate::tests::from_usda(OVERRIDES)?;
        let root = stage.prim("/Root")?;
        let mut cache = default_cache();
        let none = HashMap::new();

        let all = cache.untransformed_bound_with_overrides(&root, &BTreeSet::new(), &none)?;
        assert_range(all.aligned_range(), range([-1.0; 3], [21.0, 1.0, 1.0]));

        let skip = BTreeSet::from([sdf::path("/Root/C")?]);
        let found = cache.untransformed_bound_with_overrides(&root, &skip, &none)?;
        assert_range(found.aligned_range(), range([-1.0; 3], [11.0, 1.0, 1.0]));

        let skip = BTreeSet::from([sdf::path("/Root/B/Ball")?, sdf::path("/Root/C")?]);
        let found = cache.untransformed_bound_with_overrides(&root, &skip, &none)?;
        assert_range(found.aligned_range(), range([-1.0; 3], [1.0; 3]));
        Ok(())
    }

    /// An override places its subtree in the prim's space, and the prim's
    /// own override places the rest in the world.
    #[test]
    fn overrides_place() -> Result {
        let (_dir, stage) = crate::tests::from_usda(OVERRIDES)?;
        let root = stage.prim("/Root")?;
        let mut cache = default_cache();
        let skip = BTreeSet::from([sdf::path("/Root/C")?]);
        let moved = HashMap::from([(sdf::path("/Root/B")?, gf::Mat4d::translation([0.0, 5.0, 0.0]))]);

        let found = cache.untransformed_bound_with_overrides(&root, &skip, &moved)?;
        assert_range(found.aligned_range(), range([-1.0; 3], [1.0, 6.0, 1.0]));

        // An override above a prim places it too.
        let beneath = HashMap::from([(sdf::path("/Root/B/Ball")?, gf::Mat4d::translation([0.0, 0.0, 9.0]))]);
        let found = cache.untransformed_bound_with_overrides(&root, &skip, &beneath)?;
        assert_range(found.aligned_range(), range([-1.0; 3], [1.0, 1.0, 10.0]));

        let far = gf::Mat4d::translation([100.0, 0.0, 0.0]);
        let found = cache.world_bound_with_overrides(&root, &skip, far, &HashMap::new())?;
        assert_range(found.aligned_range(), range([99.0, -1.0, -1.0], [111.0, 1.0, 1.0]));
        Ok(())
    }

    /// A bound the override walk asks for beneath a component is the one an
    /// ordinary query answers, and so are the entries it leaves.
    #[test]
    fn overrides_beneath_component() -> Result {
        let (_dir, stage) = crate::tests::from_usda(COMPONENT)?;
        let world = stage.prim("/World")?;
        let skip = BTreeSet::from([sdf::path("/World/Plain")?]);
        let mut cache = default_cache();
        let found = cache.untransformed_bound_with_overrides(&world, &skip, &HashMap::new())?;

        let mut fresh = default_cache();
        let component = stage.prim("/World/Comp")?;
        assert_eq!(found, fresh.relative_bound(&component, &world)?);
        assert!(!found.range().is_empty());
        for path in ["/World/Comp", "/World/Comp/Geom", "/World/Comp/Geom/B"] {
            let prim = stage.prim(path)?;
            assert_eq!(
                cache.untransformed_bound(&prim)?,
                fresh.untransformed_bound(&prim)?,
                "{path}"
            );
        }

        // Skipping beneath the component walks through it.
        let skip = BTreeSet::from([sdf::path("/World/Comp/Geom/B")?, sdf::path("/World/Plain")?]);
        let found = cache.untransformed_bound_with_overrides(&world, &skip, &HashMap::new())?;
        let cube = stage.prim("/World/Comp/Geom/A")?;
        assert_eq!(found, fresh.relative_bound(&cube, &world)?);
        Ok(())
    }

    /// An override query leaves the cache answering ordinary queries as a
    /// fresh one does.
    #[test]
    fn overrides_then_plain() -> Result {
        let (_dir, stage) = crate::tests::from_usda(OVERRIDES)?;
        let root = stage.prim("/Root")?;
        let mut cache = default_cache();
        let skip = BTreeSet::from([sdf::path("/Root/C")?]);
        let moved = HashMap::from([(sdf::path("/Root/B")?, gf::Mat4d::translation([0.0, 5.0, 0.0]))]);
        cache.world_bound_with_overrides(&root, &skip, gf::Mat4d::translation([100.0, 0.0, 0.0]), &moved)?;

        let mut fresh = default_cache();
        for path in ["/Root", "/Root/B", "/Root/C", "/"] {
            let prim = stage.prim(path)?;
            assert_eq!(cache.world_bound(&prim)?, fresh.world_bound(&prim)?, "{path}");
        }
        assert_range(
            world(&mut cache, &stage, "/Root")?,
            range([0.0, -1.0, -1.0], [22.0, 1.0, 1.0]),
        );
        Ok(())
    }

    const HINTED: &str = r#"#usda 1.0

def Xform "Model" (kind = "component")
{
    float3[] extentsHint = [(-5, -5, -5), (5, 5, 5), (-9, -9, -9), (-7, -7, -7)]

    def Sphere "Ball" {}

    def Sphere "Hidden"
    {
        token visibility = "invisible"
        double3 xformOp:translate = (0, 0, 50)
        uniform token[] xformOpOrder = ["xformOp:translate"]
    }
}

def Xform "Loose"
{
    float3[] extentsHint = [(-5, -5, -5), (5, 5, 5)]

    def Sphere "Ball" {}

    def Xform "Part" (kind = "component")
    {
        float3[] extentsHint = [(-5, -5, -5), (5, 5, 5)]

        def Sphere "Ball" {}
    }
}
"#;

    /// A hint holds the box of each purpose it reaches, in the order of
    /// the purposes, and no box for the rest.
    #[test]
    fn hint_per_purpose() -> Result {
        let (_dir, stage) = crate::tests::from_usda(HINTED)?;
        let model = stage.prim("/Model")?;
        let mut cache = default_cache().with_extents_hint(true);
        assert_eq!(cache.untransformed_bound(&model)?.range(), range([-5.0; 3], [5.0; 3]));
        cache.set_included_purposes([Purpose::Render]);
        assert_eq!(cache.untransformed_bound(&model)?.range(), range([-9.0; 3], [-7.0; 3]));
        cache.set_included_purposes([Purpose::Proxy, Purpose::Guide]);
        assert!(cache.untransformed_bound(&model)?.range().is_empty());
        cache.set_included_purposes([Purpose::Render, Purpose::Default]);
        assert_range(
            cache.untransformed_bound(&model)?.aligned_range(),
            range([-9.0; 3], [5.0; 3]),
        );
        Ok(())
    }

    /// A hint on a prim that is not a model is passed over: one with no
    /// kind, and a component beneath a prim that is no group.
    #[test]
    fn hint_needs_model() -> Result {
        let (_dir, stage) = crate::tests::from_usda(HINTED)?;
        let mut cache = default_cache().with_extents_hint(true);
        for path in ["/Loose", "/Loose/Part"] {
            assert!(!stage.prim(path)?.is_model()?);
            assert_range(world(&mut cache, &stage, path)?, range([-1.0; 3], [1.0; 3]));
        }
        Ok(())
    }

    /// A cache whose options change drops what it held: it answers by the
    /// hint once hints are in use, and bounds an invisible prim once
    /// visibility is ignored.
    #[test]
    fn options_invalidate() -> Result {
        let (_dir, stage) = crate::tests::from_usda(HINTED)?;
        let mut cache = default_cache();
        assert_range(world(&mut cache, &stage, "/Model")?, range([-1.0; 3], [1.0; 3]));

        let mut cache = cache.with_ignore_visibility(true);
        assert_range(world(&mut cache, &stage, "/Model")?, range([-1.0; 3], [1.0, 1.0, 51.0]));

        let mut cache = cache.with_extents_hint(true);
        assert_range(world(&mut cache, &stage, "/Model")?, range([-5.0; 3], [5.0; 3]));

        // The same setting again keeps what is held.
        let cache = cache.with_extents_hint(true).with_ignore_visibility(true);
        assert!(holds(&cache, &stage, "/Model")?);
        Ok(())
    }

    /// A model bounded by a constant hint still moves in its parent's
    /// bound with its own transform.
    #[test]
    fn hint_moves_with_model() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Model" (kind = "component")
{
    float3[] extentsHint = [(-5, -5, -5), (5, 5, 5)]
    double3 xformOp:translate.timeSamples = { 1: (0, 0, 0), 2: (100, 0, 0) }
    uniform token[] xformOpOrder = ["xformOp:translate"]
}
"#,
        )?;
        let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]).with_extents_hint(true);
        assert_range(world(&mut cache, &stage, "/")?, range([-5.0; 3], [5.0; 3]));
        cache.set_time(at(2.0));
        assert_range(
            world(&mut cache, &stage, "/")?,
            range([95.0, -5.0, -5.0], [105.0, 5.0, 5.0]),
        );
        Ok(())
    }

    /// A model bounded by a constant hint leaves its parent's bound while
    /// it is invisible.
    #[test]
    fn hint_follows_visibility() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Model" (kind = "component")
{
    float3[] extentsHint = [(-5, -5, -5), (5, 5, 5)]
    token visibility.timeSamples = { 1: "invisible", 2: "inherited", 3: "invisible" }
}
"#,
        )?;
        let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]).with_extents_hint(true);
        // Asked for directly, the model is bounded while invisible too.
        assert_range(world(&mut cache, &stage, "/Model")?, range([-5.0; 3], [5.0; 3]));
        for (time, empty) in [(1.0, true), (2.0, false), (3.0, true)] {
            cache.set_time(at(time));
            assert_eq!(world(&mut cache, &stage, "/")?.is_empty(), empty, "at {time}");
        }
        Ok(())
    }

    /// A hint that holds no extent at one time and one at another bounds
    /// the model from the time it holds one.
    #[test]
    fn hint_becomes_usable() -> Result {
        let (_dir, stage) = crate::tests::from_usda(
            r#"#usda 1.0

def Xform "Model" (kind = "component")
{
    float3[] extentsHint.timeSamples = {
        1: [],
        2: [(-5, -5, -5), (5, 5, 5)],
        3: [(-6, -6, -6), (6, 6, 6)],
    }

    def Sphere "Ball"
    {
        float3[] extent = [(-1, -1, -1), (1, 1, 1)]
    }
}
"#,
        )?;
        let mut cache = BBoxCache::new(at(1.0), [Purpose::Default]).with_extents_hint(true);
        for (time, reach) in [(1.0, 1.0), (2.0, 5.0), (3.0, 6.0), (1.0, 1.0)] {
            cache.set_time(at(time));
            assert_range(world(&mut cache, &stage, "/")?, range([-reach; 3], [reach; 3]));
        }
        Ok(())
    }

    /// An instancer under a turned parent, with a small and a big
    /// prototype. `{indices}` and `{extra}` are the instancer's
    /// `protoIndices` and whatever else it authors.
    fn instancer(indices: &str, extra: &str) -> Result<(tempfile::TempDir, usd::Stage, PointInstancer)> {
        let (dir, stage) = crate::tests::from_usda(&format!(
            r#"#usda 1.0

def Xform "World"
{{
    float xformOp:rotateZ = 90
    uniform token[] xformOpOrder = ["xformOp:rotateZ"]

    def PointInstancer "Inst"
    {{
        double3 xformOp:translate = (10, 0, 0)
        uniform token[] xformOpOrder = ["xformOp:translate"]
        {indices}
        {extra}
        rel prototypes = [</World/Inst/Protos/Small>, </World/Inst/Protos/Big>]

        def Scope "Protos"
        {{
            def Sphere "Small" {{}}

            def Cube "Big"
            {{
                double size = 4
                double3 xformOp:translate = (0, 0, 1)
                uniform token[] xformOpOrder = ["xformOp:translate"]
            }}
        }}
    }}
}}
"#
        ))?;
        let instancer = PointInstancer::get(&stage, sdf::path("/World/Inst")?)?.expect("an instancer");
        Ok((dir, stage, instancer))
    }

    const THREE: &str = "int[] protoIndices = [0, 1, 0]";
    const POSITIONS: &str = "point3f[] positions = [(0, 0, 0), (5, 0, 0), (0, 5, 0)]";

    /// An instance's bound is its prototype's, under the prototype's own
    /// transform and the instance's placement, in each of the four spaces.
    #[test]
    fn instance_bounds_spaces() -> Result {
        let (_dir, stage, instancer) = instancer(THREE, POSITIONS)?;
        let mut cache = default_cache();
        let aligned =
            |bounds: Vec<gf::BBox3d>| -> Vec<gf::Range3d> { bounds.iter().map(gf::BBox3d::aligned_range).collect() };

        let own = aligned(cache.point_instance_untransformed_bounds(&instancer, &[0, 1, 2])?);
        assert_range(own[0], range([-1.0; 3], [1.0; 3]));
        assert_range(own[1], range([3.0, -2.0, -1.0], [7.0, 2.0, 3.0]));
        assert_range(own[2], range([-1.0, 4.0, -1.0], [1.0, 6.0, 1.0]));

        let local = aligned(cache.point_instance_local_bounds(&instancer, &[0, 1, 2])?);
        assert_range(local[1], range([13.0, -2.0, -1.0], [17.0, 2.0, 3.0]));

        // A quarter turn about Z sends X to Y and Y to -X.
        let in_world = aligned(cache.point_instance_world_bounds(&instancer, &[0, 1, 2])?);
        assert_range(in_world[0], range([-1.0, 9.0, -1.0], [1.0, 11.0, 1.0]));
        assert_range(in_world[1], range([-2.0, 13.0, -1.0], [2.0, 17.0, 3.0]));
        assert_range(in_world[2], range([-6.0, 9.0, -1.0], [-4.0, 11.0, 1.0]));

        // Out of order and repeated, the boxes follow the indices.
        let picked = aligned(cache.point_instance_untransformed_bounds(&instancer, &[2, 0, 2])?);
        assert_eq!(picked, [own[2], own[0], own[2]]);
        assert!(cache.point_instance_world_bounds(&instancer, &[])?.is_empty());
        assert_eq!(cache.instancers.len(), 1, "the instancer was read once and kept");

        // With no `extent` authored, the instancer is bounded by its
        // instances, and its prototypes are not bounded beside them.
        assert_range(
            world(&mut cache, &stage, "/World")?,
            range([-6.0, 9.0, -1.0], [2.0, 17.0, 3.0]),
        );
        Ok(())
    }

    /// Relative to an ancestor that turns, the instancer is taken to the
    /// ancestor's space by its own transform and then the inverse of the
    /// ancestor's.
    #[test]
    fn relative_noncommuting() -> Result {
        let (_dir, stage, instancer) = instancer(THREE, POSITIONS)?;
        let mut cache = default_cache();
        let ancestor = stage.prim("/World")?;
        let relative = cache.point_instance_relative_bounds(&instancer, &[0, 1], &ancestor)?;
        let local = cache.point_instance_local_bounds(&instancer, &[0, 1])?;
        assert_range(relative[0].aligned_range(), range([9.0, -1.0, -1.0], [11.0, 1.0, 1.0]));
        for (relative, local) in relative.iter().zip(&local) {
            assert_range(relative.aligned_range(), local.aligned_range());
        }
        let prim = cache.relative_bound(&stage.prim("/World/Inst/Protos/Small")?, &ancestor)?;
        assert_range(prim.aligned_range(), range([9.0, -1.0, -1.0], [11.0, 1.0, 1.0]));
        Ok(())
    }

    /// An index is a position among the instances, whatever `ids` holds,
    /// and a pruned instance is bounded like any other.
    #[test]
    fn indices_not_ids() -> Result {
        let extra = format!("{POSITIONS}\n        int64[] ids = [7, 3, 42]\n        int64[] invisibleIds = [3]");
        let (_dir, _stage, instancer) = instancer(THREE, &extra)?;
        assert_eq!(instancer.mask_at(None, None)?, [true, false, true]);
        let mut cache = default_cache();
        let bounds = cache.point_instance_untransformed_bounds(&instancer, &[0, 1, 2])?;
        assert_eq!(bounds.len(), 3);
        assert_range(bounds[1].aligned_range(), range([3.0, -2.0, -1.0], [7.0, 2.0, 3.0]));

        let refused = cache.point_instance_untransformed_bounds(&instancer, &[0, 7]);
        assert!(
            matches!(
                refused,
                Err(SchemaError::InstanceIndexOutOfRange {
                    index: 7,
                    instances: 3,
                    ..
                })
            ),
            "{refused:?}"
        );
        Ok(())
    }

    /// An instance that changes prototype between the base time and the
    /// cache's time is bounded by the prototype of the cache's time, under
    /// that prototype's own transform.
    #[test]
    fn prototype_switch() -> Result {
        let (_dir, _stage, instancer) = instancer(
            "int[] protoIndices.timeSamples = { 1: [0], 2: [1] }",
            "point3f[] positions = [(0, 0, 0)]",
        )?;
        let mut cache = BBoxCache::new(at(2.0), [Purpose::Default]);
        cache.set_base_time(usd::TimeCode::new(1.0));
        let bounds = cache.point_instance_untransformed_bounds(&instancer, &[0])?;
        assert_range(bounds[0].aligned_range(), range([-2.0, -2.0, -1.0], [2.0, 2.0, 3.0]));

        cache.set_time(at(1.0));
        let bounds = cache.point_instance_untransformed_bounds(&instancer, &[0])?;
        assert_range(bounds[0].aligned_range(), range([-1.0; 3], [1.0; 3]));
        Ok(())
    }

    /// An instance is carried from the base time to the cache's time by
    /// its velocity.
    #[test]
    fn instances_from_base_time() -> Result {
        let (_dir, _stage, instancer) = instancer(
            "int[] protoIndices = [0]",
            "point3f[] positions.timeSamples = { 1: [(0, 0, 0)], 2: [(100, 0, 0)] }
        vector3f[] velocities.timeSamples = { 1: [(24, 0, 0)], 2: [(24, 0, 0)] }",
        )?;
        // From the cache's own time, the instance is where the sample
        // before it puts it, a time code's travel on.
        let mut cache = BBoxCache::new(at(3.0), [Purpose::Default]);
        let bounds = cache.point_instance_untransformed_bounds(&instancer, &[0])?;
        assert_range(bounds[0].aligned_range(), range([100.0, -1.0, -1.0], [102.0, 1.0, 1.0]));

        // From the first sample, it has travelled two.
        cache.set_base_time(usd::TimeCode::new(1.0));
        let bounds = cache.point_instance_untransformed_bounds(&instancer, &[0])?;
        assert_range(bounds[0].aligned_range(), range([1.0, -1.0, -1.0], [3.0, 1.0, 1.0]));

        // A default base time beside a numeric time is refused.
        cache.set_base_time(None);
        let refused = cache.point_instance_untransformed_bounds(&instancer, &[0]);
        assert!(
            matches!(refused, Err(SchemaError::DefaultTimeMismatch { .. })),
            "{refused:?}"
        );
        Ok(())
    }

    /// An instancer with no `protoIndices`, or no prototypes, bounds no
    /// instance.
    #[test]
    fn instancer_without_data() -> Result {
        let (_dir, _stage, bare) = instancer("", POSITIONS)?;
        let mut cache = default_cache();
        let refused = cache.point_instance_world_bounds(&bare, &[0]);
        assert!(matches!(refused, Err(SchemaError::NoValue { .. })), "{refused:?}");

        let stage = crate::tests::stage("anon.usda")?;
        let lone = PointInstancer::define(&stage, "/Inst")?;
        lone.attribute(tokens::PROTO_INDICES).set(vec![0])?;
        let refused = cache.point_instance_world_bounds(&lone, &[0]);
        assert!(matches!(refused, Err(SchemaError::NoPrototypes { .. })), "{refused:?}");
        Ok(())
    }
}
