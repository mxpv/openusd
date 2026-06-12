//! Composed USD stage.
//!
//! A [`Stage`] loads a root layer file and all its dependencies, then provides
//! composed access to the scene graph by merging opinions across layers
//! according to USD's [LIVERPS] strength ordering:
//!
//! 1. **L**ocal opinions (root layer stack / sublayers) — strongest
//! 2. **I**nherit arcs
//! 3. **V**ariant set arcs
//! 4. **R**eference arcs
//! 5. **P**ayload arcs
//! 6. **S**pecialize arcs — weakest
//!
//! The strength ordering applies recursively within each composition context.
//! When building prim and property stacks:
//!
//! - Local opinions are evaluated first
//! - Inherit arcs follow
//! - Variant sets are applied next
//! - References are processed
//! - Payloads are composed
//! - Specialize arcs provide fallback values
//!
//! # Configuration
//!
//! Use [`StageBuilder`] to customize stage behavior before opening:
//!
//! - [`StageBuilder::resolver`] sets a custom
//!   [`ar::Resolver`](crate::ar::Resolver) for mapping asset paths to files.
//! - [`StageBuilder::variant_fallbacks`] provides a
//!   [`VariantFallbackMap`](crate::pcp::VariantFallbackMap) with preferred
//!   selections for variant sets that have no authored opinion.
//! - [`StageBuilder::load`] controls whether payload arcs are
//!   loaded during stage population.
//! - [`StageBuilder::mask`] limits the prim working set exposed by
//!   stage queries and traversal.
//!
//! [LIVERPS]: https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html

use std::cell::{Cell, Ref, RefCell};
use std::rc::{Rc, Weak};

use anyhow::Result;
use bitflags::bitflags;

use crate::tf::Token;
use crate::{ar, layer, pcp, sdf};

use super::interp::{self, InterpolationType};
use super::notice::{self, Deletion, LayerDiff, LayerMutingChanged, Notice, ObjectsChanged};

bitflags! {
    /// Resolved stage-level status bits for a prim.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct PrimStatus: u32 {
        /// The prim and all ancestors are active.
        const ACTIVE = 1 << 0;
        /// The prim is loaded according to the stage's current load behavior.
        const LOADED = 1 << 1;
        /// The prim and all ancestors have defining specifiers.
        const DEFINED = 1 << 2;
        /// The prim or an ancestor has a `class` specifier.
        const ABSTRACT = 1 << 3;
        /// The prim is instanceable and has at least one composition arc.
        const INSTANCE = 1 << 4;
        /// The prim is part of the contiguous model hierarchy.
        const MODEL = 1 << 5;
        /// The prim lies within a prototype's namespace (`/__Prototype_N`).
        const IN_PROTOTYPE = 1 << 6;
    }
}

/// Predicate used to filter prim traversal by resolved status bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrimPredicate {
    required: PrimStatus,
    rejected: PrimStatus,
    /// When `false` (the default), traversal does not descend into an instance
    /// prim's subtree — its contents are reached through the prototype
    /// (`Prim::prototype`). When `true`, instance subtrees are traversed
    /// directly (the "instance proxy" view, spec 11.3.3).
    traverse_instance_proxies: bool,
}

impl PrimPredicate {
    /// Status bits inherited from a prim's ancestors. Missing any of these on a
    /// parent guarantees that no descendant can have them either, enabling
    /// subtree pruning during traversal.
    const INHERITED_REQUIRED: PrimStatus = PrimStatus::ACTIVE.union(PrimStatus::LOADED).union(PrimStatus::DEFINED);

    /// Status bits that, once set on an ancestor, are inherited by every descendant.
    const INHERITED_REJECTED: PrimStatus = PrimStatus::ABSTRACT;

    /// Match every composed prim, descending into instance subtrees so the
    /// full composed namespace is visited regardless of instancing.
    pub const ALL: Self = Self {
        required: PrimStatus::empty(),
        rejected: PrimStatus::empty(),
        traverse_instance_proxies: true,
    };

    /// OpenUSD-style default traversal predicate.
    ///
    /// Matches prims that are active, loaded, defined, and not abstract.
    pub const DEFAULT: Self = Self::new(Self::INHERITED_REQUIRED, Self::INHERITED_REJECTED);

    /// The default region, but descending into instance subtrees (instance
    /// proxies). Schema and connection readers gather every prim of interest
    /// across the stage and so must reach instanced content; public traversal
    /// stops at instances and reaches their contents through the prototype, but
    /// prototypes are not yet materialized as separately traversable roots.
    pub const DEFAULT_PROXIES: Self = Self {
        required: Self::INHERITED_REQUIRED,
        rejected: Self::INHERITED_REJECTED,
        traverse_instance_proxies: true,
    };

    /// Creates a predicate with required and rejected status bits. Instance
    /// subtrees are not traversed; see [`Self::with_instance_proxies`].
    pub const fn new(required: PrimStatus, rejected: PrimStatus) -> Self {
        Self {
            required,
            rejected,
            traverse_instance_proxies: false,
        }
    }

    /// Returns a copy that descends into instance subtrees (instance proxies)
    /// when `enabled`, instead of stopping at instance prims (spec 11.3.3).
    pub fn with_instance_proxies(mut self, enabled: bool) -> Self {
        self.traverse_instance_proxies = enabled;
        self
    }

    /// Returns `true` if `status` satisfies the predicate.
    pub const fn matches(self, status: PrimStatus) -> bool {
        status.contains(self.required) && !status.intersects(self.rejected)
    }

    /// Returns the set of status bits this predicate actually consults.
    fn consulted_bits(self) -> PrimStatus {
        let mut bits = self.required.union(self.rejected);
        // Stopping at instances requires knowing which prims are instances.
        if !self.traverse_instance_proxies {
            bits = bits.union(PrimStatus::INSTANCE);
        }
        bits
    }

    /// Returns `true` if no descendant can satisfy this predicate.
    fn prunes_descendants(self, status: PrimStatus) -> bool {
        let required = self.required.intersection(Self::INHERITED_REQUIRED);
        if !status.contains(required) {
            return true;
        }
        status.intersects(self.rejected.intersection(Self::INHERITED_REJECTED))
    }
}

impl Default for PrimPredicate {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// Initial payload loading behavior for a stage.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum InitialLoadSet {
    /// Load all payload arcs during stage population.
    #[default]
    LoadAll,
    /// Leave payload arcs unloaded during stage population.
    LoadNone,
}

impl InitialLoadSet {
    /// Returns `true` when payload arcs should be followed.
    pub const fn load_payloads(self) -> bool {
        matches!(self, Self::LoadAll)
    }
}

/// Population mask limiting which prim paths are exposed by a [`Stage`].
///
/// A mask path includes that prim's subtree. Ancestors of masked paths are
/// also included so traversal can reach the requested working set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StagePopulationMask {
    paths: Vec<sdf::Path>,
}

impl StagePopulationMask {
    /// Creates a mask that includes the full stage.
    pub fn all() -> Self {
        Self {
            paths: vec![sdf::Path::abs_root()],
        }
    }

    /// Creates an empty mask.
    pub fn empty() -> Self {
        Self { paths: Vec::new() }
    }

    /// Creates a mask from prim paths.
    pub fn new(paths: impl IntoIterator<Item = impl Into<sdf::Path>>) -> Self {
        let mut mask = Self::empty();
        for path in paths {
            mask.add_path(path);
        }
        mask
    }

    /// Returns a copy of this mask with `path` added.
    pub fn with_path(mut self, path: impl Into<sdf::Path>) -> Self {
        self.add_path(path);
        self
    }

    /// Adds a prim path to the mask.
    pub fn add_path(&mut self, path: impl Into<sdf::Path>) -> &mut Self {
        let path = sdf::Path::abs_root().make_absolute(&path.into().prim_path());
        if path == sdf::Path::abs_root() {
            self.paths.clear();
            self.paths.push(path);
        } else if !self.is_all() && !self.paths.contains(&path) {
            self.paths.push(path);
        }
        self
    }

    /// Returns the authored mask paths.
    pub fn paths(&self) -> &[sdf::Path] {
        &self.paths
    }

    /// Returns `true` if the mask contains no paths.
    pub fn is_empty(&self) -> bool {
        self.paths.is_empty()
    }

    /// Returns `true` if the mask includes the full stage.
    ///
    /// `add_path` clears `paths` to `[abs_root]` whenever the root is added,
    /// so a single front-position check captures the invariant.
    pub fn is_all(&self) -> bool {
        self.paths.first() == Some(&sdf::Path::abs_root())
    }

    /// Returns `true` if `path` is inside the population mask.
    ///
    /// Variant selection segments in `path` are stripped before matching so a
    /// mask of `/Prim/Child` still includes opinions authored under
    /// `/Prim{set=sel}Child`.
    pub fn includes(&self, path: &sdf::Path) -> bool {
        if self.is_all() {
            return true;
        }
        let path = path.prim_path().strip_all_variant_selections();
        self.paths
            .iter()
            .any(|mask_path| path.has_prefix(mask_path) || mask_path.has_prefix(&path))
    }
}

impl Default for StagePopulationMask {
    fn default() -> Self {
        Self::all()
    }
}

/// Identifies which layer in a [`Stage`] receives authored opinions, and how
/// stage-namespace paths map into that layer's namespace.
///
/// Subset of C++ `UsdEditTarget`. Like C++, it pairs a target layer with a
/// `PcpMapFunction` (`mapping`) that translates a scene (stage-namespace) path
/// into the spec (layer-namespace) path actually authored. For a plain local
/// target the mapping is the identity, so authoring writes to the target layer
/// using the composed path verbatim. A variant target (see
/// [`for_local_direct_variant`](Self::for_local_direct_variant)) carries a
/// mapping that inserts the `{set=sel}` segment so child opinions land inside
/// the variant. An arc target (see
/// [`Stage::edit_target_for_node`](Stage::edit_target_for_node)) carries the
/// referencing/inheriting arc's `map_to_root`, so authoring writes into the
/// arc's source layer.
#[derive(Debug, Clone, PartialEq)]
pub struct EditTarget {
    /// Canonical identifier of the layer this target writes to. Stored as a
    /// string (not a [`pcp::LayerId`]) so the constructor needs no graph and the
    /// target stays valid across layer remove/re-add; it is resolved to the
    /// graph handle at author time.
    layer_identifier: String,
    /// Maps the layer (spec) namespace to the stage (scene) namespace — the
    /// same orientation as [`pcp::Node`](crate::pcp::Node)'s `map_to_root`.
    /// Authoring queries it in reverse via
    /// [`map_to_spec_path`](Self::map_to_spec_path). Identity for a local
    /// target, so the default authoring path is unchanged.
    mapping: pcp::MapFunction,
    /// Identity of the stage's root layer stack this target was constructed
    /// against, or `None` for a stage-agnostic target
    /// ([`for_layer`](Self::for_layer) /
    /// [`for_local_direct_variant`](Self::for_local_direct_variant)). A `Some`
    /// target applied to a stage with a different identity is rejected by
    /// [`set_edit_target`](Stage::set_edit_target), so an arc target built
    /// against one stage's composition can't silently retarget another's.
    layer_stack: Option<pcp::LayerStackIdentifier>,
}

/// Composition arc kind selecting which arc on a prim an arc-based
/// [`EditTarget`] writes into (C++ `UsdEditTarget::Reference` / `Inherit` /
/// `Specialize` / `Payload`). Built via
/// [`Stage::edit_target_for_node`](Stage::edit_target_for_node) or
/// [`Prim::edit_target_for_arc`](super::Prim::edit_target_for_arc).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EditTargetArc {
    /// A reference arc.
    Reference,
    /// A payload arc (the payload must be loaded to contribute a node).
    Payload,
    /// An inherit arc.
    Inherit,
    /// A specialize arc.
    Specialize,
}

impl EditTargetArc {
    /// Whether this selector matches a composed node's arc type.
    fn matches(self, arc: pcp::ArcType) -> bool {
        matches!(
            (self, arc),
            (EditTargetArc::Reference, pcp::ArcType::Reference)
                | (EditTargetArc::Payload, pcp::ArcType::Payload)
                | (EditTargetArc::Inherit, pcp::ArcType::Inherit)
                | (EditTargetArc::Specialize, pcp::ArcType::Specialize)
        )
    }
}

impl EditTarget {
    /// Edit target pointing at the layer with the given identifier, with an
    /// identity path mapping (scene path == spec path).
    pub fn for_layer(layer_identifier: impl Into<String>) -> Self {
        Self {
            layer_identifier: layer_identifier.into(),
            mapping: pcp::MapFunction::identity(),
            layer_stack: None,
        }
    }

    /// Edit target that routes authoring into a local variant. `var_sel_path`
    /// is the variant-selection prim path (e.g. `/Prim{set=sel}`) on the
    /// target layer; child prim and property opinions authored at the stripped
    /// scene path (`/Prim/child`) land at `/Prim{set=sel}child` in the layer.
    ///
    /// Mirrors C++ `UsdEditTarget::ForLocalDirectVariant`. Paths outside the
    /// variant prim map to themselves, so authoring elsewhere is unaffected.
    pub fn for_local_direct_variant(layer_identifier: impl Into<String>, var_sel_path: sdf::Path) -> Self {
        let stripped = var_sel_path.strip_all_variant_selections();
        Self {
            layer_identifier: layer_identifier.into(),
            mapping: pcp::MapFunction::from_pair_identity(var_sel_path, stripped),
            layer_stack: None,
        }
    }

    /// The identifier of the layer this target writes to.
    pub fn layer_identifier(&self) -> &str {
        &self.layer_identifier
    }

    /// Maps a scene (stage-namespace) path to the spec (layer-namespace) path
    /// authoring should write at. Returns `None` when `scene_path` falls
    /// outside the mapping's co-domain (C++ returns an empty `SdfPath`).
    ///
    /// Mirrors C++ `UsdEditTarget::MapToSpecPath`. First the path is mapped in
    /// the target-to-source direction. Then any relationship/connection target
    /// path embedded in a `[..]` bracket is re-mapped the same way, and the
    /// whole result is rejected (`None`) when that embedded target falls outside
    /// the co-domain — for a restricted arc mapping, a target naming a prim the
    /// arc does not reach cannot be authored. The re-mapped target is stripped of
    /// variant selections, which a target path never carries.
    pub fn map_to_spec_path(&self, scene_path: &sdf::Path) -> Option<sdf::Path> {
        let mapped = self.mapping.map_target_to_source(scene_path)?;
        match scene_path.embedded_target_path() {
            None => Some(mapped),
            Some(target) => {
                let mapped_target = self
                    .mapping
                    .map_target_to_source(&target)?
                    .strip_all_variant_selections();
                mapped.replace_embedded_target(&mapped_target)
            }
        }
    }

    /// Maps a stage (scene) time to the source (layer) time a time sample
    /// authored through this target should be keyed at.
    ///
    /// An arc target captures the arc's composed time offset (e.g. a reference
    /// with `(offset = 10)`), which maps a source-layer time to the composed
    /// stage time. Authoring keys the sample in the source layer, so the stage
    /// time is run through the inverse offset. A local or variant target carries
    /// the identity offset, so this is a no-op there.
    pub fn map_to_spec_time(&self, stage_time: f64) -> f64 {
        self.mapping.time_offset().inverse().apply(stage_time)
    }

    /// Whether this target names no layer, so it can author nothing (C++
    /// `UsdEditTarget::IsNull`). The default target of a stage with no layers.
    pub fn is_null(&self) -> bool {
        self.layer_identifier.is_empty()
    }

    /// Whether this target names a layer and carries a mapping that maps
    /// something (C++ `UsdEditTarget::IsValid`). Validity does not guarantee the
    /// layer is present in any particular stage — [`Stage::set_edit_target`]
    /// performs that check.
    pub fn is_valid(&self) -> bool {
        !self.is_null() && !self.mapping.is_null()
    }

    /// Composes this (stronger) target over a `weaker` one, returning a target
    /// on this target's layer whose mapping routes a scene path through the
    /// weaker context first, then this refinement (C++
    /// `UsdEditTarget::ComposeOver`). A null target composes to the other.
    ///
    /// This expresses a deeper edit relative to a broader one — e.g. a variant
    /// refinement (`/Source{set=sel}`) over a reference target
    /// (`/Source ↔ /World/MyPrim`) yields a target that authors a stage write at
    /// `/World/MyPrim/Child` into `/Source{set=sel}Child`.
    ///
    /// Both targets should belong to the same stage (or be stage-agnostic); the
    /// result carries that shared stage identity. Composing targets bound to
    /// different stages would mix unrelated namespaces, so it yields a null
    /// target instead — keeping the cross-stage guard intact rather than
    /// producing a target one stage would wrongly accept.
    pub fn compose_over(&self, weaker: &EditTarget) -> EditTarget {
        if self.is_null() {
            return weaker.clone();
        }
        if weaker.is_null() {
            return self.clone();
        }
        if matches!((&self.layer_stack, &weaker.layer_stack), (Some(a), Some(b)) if a != b) {
            return EditTarget {
                layer_identifier: String::new(),
                mapping: pcp::MapFunction::null(),
                layer_stack: None,
            };
        }
        EditTarget {
            layer_identifier: self.layer_identifier.clone(),
            mapping: weaker.mapping.compose(&self.mapping),
            layer_stack: self.layer_stack.clone().or_else(|| weaker.layer_stack.clone()),
        }
    }
}

/// RAII guard that scopes a [`Stage`] edit-target switch, restoring the
/// previous target when dropped. Created by
/// [`Stage::edit_context`](Stage::edit_context); mirrors C++ `UsdEditContext`.
///
/// ```no_run
/// # use openusd::usd::{Stage, EditTarget};
/// # fn f(stage: &Stage) -> anyhow::Result<()> {
/// let root = stage.root_layer().identifier().to_string();
/// {
///     let _ctx = stage.edit_context(EditTarget::for_layer(root))?;
///     stage.define_prim("/World")?; // authored into the root layer
/// } // previous edit target restored here
/// # Ok(())
/// # }
/// ```
///
/// The guard is neither `Clone` nor `Copy`, mirroring C++'s deleted copy and
/// assignment. Note that [`Stage::set_default_prim`](Stage::set_default_prim)
/// always targets the root layer, so wrapping it in an `EditContext` has no
/// effect.
pub struct EditContext<'a> {
    stage: &'a Stage,
    saved: EditTarget,
}

impl Drop for EditContext<'_> {
    fn drop(&mut self) {
        // The saved target was valid when the guard was created, so restoring it
        // needs no validation. `replace_edit_target` notifies the change so a
        // listener tracking the edit target stays current (C++ `UsdEditContext`
        // notifies on both enter and restore).
        self.stage.replace_edit_target(self.saved.clone());
    }
}

/// Errors raised by [`Stage`]'s authoring methods.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum StageAuthoringError {
    /// The layer at the current edit target rejected the authoring call.
    #[error(transparent)]
    Layer(#[from] sdf::AuthoringError),

    /// A composed-stage query needed to route or validate the authoring call failed.
    #[error(transparent)]
    Composition(#[from] anyhow::Error),

    /// The named layer is not present in this stage's layer graph.
    #[error("layer {layer:?} is not in the stage")]
    LayerNotFound {
        /// The offending layer's identifier.
        layer: String,
    },

    /// No composition arc of the requested kind authors a spec on the prim, so
    /// no arc-based edit target can be built for it.
    #[error("prim {path} has no {arc:?} arc to author into")]
    NoArcNode {
        /// The prim path the arc target was requested for.
        path: sdf::Path,
        /// The arc kind that was requested.
        arc: EditTargetArc,
    },

    /// The edit target was built against a different stage's composition and
    /// cannot be applied here.
    #[error("edit target belongs to a different stage")]
    EditTargetWrongStage,

    /// The path being authored falls outside the current edit target's
    /// mapping co-domain, so it cannot be translated to a layer-local spec
    /// path. The local and variant edit targets map every path (their mapping
    /// carries an identity catch-all), so this only arises for arc-based
    /// targets with a restricted domain — e.g. an external reference or
    /// payload edit context, which are not yet implemented.
    #[error("path {path} is outside the current edit target")]
    OutsideEditTarget {
        /// The scene-namespace path that could not be mapped.
        path: sdf::Path,
    },

    /// Stage-level metadata (the time-code range and rates) resolves only from
    /// the root and session layers (session over root), so it can be authored
    /// only when the current edit target is one of them. Mirrors C++
    /// `UsdStage`, which authors into the edit-target layer when it is the root
    /// or session layer and warns otherwise — authoring elsewhere would write
    /// an opinion stage-metadata resolution never reads.
    #[error("stage metadata can only be authored on the root or session layer, not edit-target layer {layer:?}")]
    StageMetadataTarget {
        /// The current edit target's layer identifier.
        layer: String,
    },

    /// [`Stage::apply_diff`] replays a diff in the originating layer's
    /// namespace, so it requires the current edit target to map paths
    /// identically — a local or root-layer target. A variant or arc edit target
    /// carries a non-identity namespace mapping that diff replay does not yet
    /// translate through; switch to a matching edit target before replaying.
    #[error("apply_diff requires an identity edit-target mapping; the current target remaps the namespace")]
    NonLocalEditTarget,
}

/// Shared state behind a [`Stage`] handle.
///
/// Owns the loaded layer stack and the composed-scene state. Composition
/// indices are built lazily and cached in the [`IndexCache`](crate::pcp::IndexCache).
/// Reached through [`Stage`]'s [`Deref`](std::ops::Deref); every mutation
/// goes through a per-field cell so it works from any cloned handle.
///
/// `pub` only to satisfy the `Deref` impl on the public `Stage` (a private
/// `Target` would be an E0446 leak); the enclosing `stage` module is
/// private and this type is not re-exported, so it is not externally
/// nameable, and all its fields are private.
pub struct StageInner {
    /// The loaded layers and their sublayer DAG. Held separately from the
    /// composition cache so layer data and the composed index can be borrowed
    /// independently.
    layers: RefCell<pcp::LayerGraph>,
    /// Lazily-built composition cache of per-prim indices and contexts.
    cache: RefCell<pcp::IndexCache>,
    /// Muted layer identifiers (C++ `UsdStage::MuteLayer`). A muted layer
    /// contributes no opinions while remaining in the graph.
    muted: RefCell<std::collections::HashSet<String>>,
    /// Initial payload loading behavior for this stage.
    initial_load_set: InitialLoadSet,
    /// Population mask limiting stage-visible prims.
    population_mask: StagePopulationMask,
    /// Stage-level interpolation mode for time-sampled attributes
    /// (AOUSD §12.5). Defaults to [`InterpolationType::Linear`] per
    /// spec.
    interpolation_type: Cell<InterpolationType>,
    /// Where authored opinions land. Defaults to the root layer.
    edit_target: RefCell<EditTarget>,
    /// This stage's root layer stack identity (root + session + resolver
    /// identity). Computed once at open and stable for the stage's life — the
    /// root and session layers and the resolver never change after
    /// construction. Stamped onto stage-bound edit targets and read by the
    /// cross-stage guard, both without recomputing.
    layer_stack_id: pcp::LayerStackIdentifier,
    /// Reusable buffer that each authoring op drains its layer's recorded
    /// [`sdf::ChangeList`] into, so classification doesn't allocate a fresh
    /// list per edit. Cleared at the start of every [`StageInner::finalize_layer`].
    change_scratch: RefCell<sdf::ChangeList>,
    /// Optional change listener (C++ `UsdNotice` registration), fired by
    /// [`Stage::finalize_layer`] after each successful edit. A single slot:
    /// callers fan out to multiple sinks inside their own closure. Boxed for
    /// single ownership; the fire path holds a shared borrow across the call,
    /// so the callback must not install or clear the listener.
    listener: RefCell<Option<ChangeListener>>,
}

/// A stage change-listener callback, installed with
/// [`Stage::set_listener`]. Receives the originating stage (so it can call
/// [`Stage::extract_diff`] without capturing a handle) and the [`Notice`].
type ChangeListener = Box<dyn Fn(&Stage, Notice<'_>)>;

/// A composed USD stage.
///
/// A cheap reference-counted handle to the shared [`StageInner`] (mirroring
/// C++ `UsdStageRefPtr`). Cloning bumps the refcount; the composed handles
/// ([`Prim`](super::Prim) and friends) hold a clone, so they can be stored
/// and outlive the call that produced them. Provides composed access to
/// prims, properties, and metadata.
#[derive(Clone)]
pub struct Stage(Rc<StageInner>);

impl std::ops::Deref for Stage {
    type Target = StageInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A non-owning handle to a [`Stage`] (C++ `UsdStageWeakPtr`).
///
/// Holds no strong reference, so it does not keep the stage alive. Obtain one
/// with [`Stage::downgrade`] and recover a strong handle with
/// [`WeakStage::upgrade`]. Capture this — not a [`Stage`] clone — inside a
/// change listener that must retain stage access across calls, so the listener
/// does not form a reference cycle that leaks the stage.
#[derive(Clone)]
pub struct WeakStage(Weak<StageInner>);

impl WeakStage {
    /// Recover a strong [`Stage`] handle, or `None` if every strong handle has
    /// been dropped.
    pub fn upgrade(&self) -> Option<Stage> {
        self.0.upgrade().map(Stage)
    }
}

impl Stage {
    /// Opens a stage from a root layer file using the [`ar::DefaultResolver`].
    ///
    /// An error opening the root layer fails. Recoverable composition errors in
    /// transitive dependencies are available through
    /// [`Stage::composition_errors`].
    pub fn open(root_path: &str) -> Result<Self> {
        Self::builder().open(root_path)
    }

    /// Creates a [`StageBuilder`] for configuring how the stage is opened.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::usd;
    ///
    /// let stage = usd::Stage::builder().open("scene.usda").unwrap();
    /// ```
    pub fn builder() -> StageBuilder<ar::DefaultResolver> {
        StageBuilder::new()
    }

    /// Returns composition errors encountered while composing this stage.
    ///
    /// Combines the layer graph's current diagnostics (sublayer cycles and
    /// invalid relocates, always reflecting present graph state) with the
    /// cache's per-prim build errors. Prim indices are built lazily, so the
    /// per-prim half is a snapshot of errors discovered by stage queries
    /// performed so far.
    pub fn composition_errors(&self) -> Vec<pcp::Error> {
        let mut errors = self.layers().errors();
        errors.extend(self.cache().composition_errors());
        errors
    }

    /// Returns the current edit target — the layer that authoring methods
    /// write into.
    pub fn edit_target(&self) -> EditTarget {
        self.edit_target.borrow().clone()
    }

    /// Maps a stage time to the spec time the current edit target writes a
    /// time sample at, borrowing the target rather than cloning it. See
    /// [`EditTarget::map_to_spec_time`].
    pub(super) fn map_to_spec_time(&self, stage_time: f64) -> f64 {
        self.edit_target.borrow().map_to_spec_time(stage_time)
    }

    /// This stage's cached root layer stack identity, stamped onto stage-bound
    /// edit targets so one built against this stage's composition is rejected by
    /// an unrelated stage.
    fn layer_stack_id(&self) -> &pcp::LayerStackIdentifier {
        &self.layer_stack_id
    }

    /// An [`EditTarget`] tagged with this stage's identity, so it is rejected by
    /// another stage's [`set_edit_target`](Self::set_edit_target).
    fn bound_target(&self, layer_identifier: String, mapping: pcp::MapFunction) -> EditTarget {
        EditTarget {
            layer_identifier,
            mapping,
            layer_stack: Some(self.layer_stack_id().clone()),
        }
    }

    /// Edit target for the stage's root layer, with an identity mapping. The
    /// target installed by default when a stage is opened.
    pub fn edit_target_root(&self) -> EditTarget {
        let identifier = self
            .layers()
            .root_layer()
            .map(|l| l.identifier().to_string())
            .unwrap_or_default();
        self.bound_target(identifier, pcp::MapFunction::identity())
    }

    /// Edit target for the stage's strongest session layer, or `None` when the
    /// stage has no session layer.
    pub fn edit_target_session(&self) -> Option<EditTarget> {
        let layers = self.layers();
        let &id = layers.session_layers().first()?;
        Some(self.bound_target(layers.identifier(id).to_string(), pcp::MapFunction::identity()))
    }

    /// Edit target that authors into the source layer of the strongest `arc`
    /// composition arc on `prim_path` (C++ `UsdEditTarget(UsdPrim, ...)`).
    ///
    /// Builds (or reuses) the prim's composition index, finds the strongest node
    /// of the requested arc kind that authors a spec, and captures that node's
    /// target layer and namespace mapping, so authoring a composed path lands at
    /// the corresponding spec path in the arc's source layer. Returns
    /// [`StageAuthoringError::NoArcNode`] when `prim_path` has no such arc (an
    /// unloaded payload contributes no node).
    ///
    /// When `prim_path` is an instance proxy, the target addresses the shared
    /// prototype: its mapping is expressed in the `/__Prototype_N` namespace
    /// (not the proxy's), so authoring goes through prototype-namespace paths and
    /// affects every instance. A proxy-namespace path does not reach the arc
    /// source — it falls outside the mapping's explicit domain — so author
    /// through the prototype path obtained from
    /// [`Prim::prototype`](super::Prim::prototype).
    ///
    /// The captured mapping carries the arc's composed time offset, so a time
    /// sample authored through the target is retimed into the source layer by
    /// [`EditTarget::map_to_spec_time`].
    pub fn edit_target_for_node(
        &self,
        prim_path: &sdf::Path,
        arc: EditTargetArc,
    ) -> Result<EditTarget, StageAuthoringError> {
        let info = {
            let graph = self.layers.borrow();
            let mut cache = self.cache.borrow_mut();
            cache.edit_target_node_info(&graph, prim_path, |a| arc.matches(a))?
        };
        let (layer_identifier, mapping) = info.ok_or_else(|| StageAuthoringError::NoArcNode {
            path: prim_path.clone(),
            arc,
        })?;
        Ok(self.bound_target(layer_identifier, mapping))
    }

    /// Replace the current edit target. Subsequent authoring calls write to
    /// the new target's layer.
    ///
    /// Validates that `target.layer_identifier()` names a layer in this stage so
    /// a bad target surfaces here, not on some later unrelated authoring call.
    /// An arc target built against a different stage is rejected with
    /// [`StageAuthoringError::EditTargetWrongStage`].
    pub fn set_edit_target(&self, target: EditTarget) -> Result<(), StageAuthoringError> {
        if target
            .layer_stack
            .as_ref()
            .is_some_and(|id| id != self.layer_stack_id())
        {
            return Err(StageAuthoringError::EditTargetWrongStage);
        }
        if self.layers().id_of(target.layer_identifier()).is_none() {
            return Err(StageAuthoringError::LayerNotFound {
                layer: target.layer_identifier().to_string(),
            });
        }

        self.replace_edit_target(target);
        Ok(())
    }

    /// Store `target` as the edit target, delivering [`Notice::EditTargetChanged`]
    /// when it differs from the current one. The shared core of
    /// [`set_edit_target`](Self::set_edit_target) and the [`EditContext`] restore;
    /// it performs no validation. The notification is skipped while the thread is
    /// unwinding — an [`EditContext`] may restore during a panic, where a
    /// listener panic would abort the process.
    fn replace_edit_target(&self, target: EditTarget) {
        let mut changed = false;
        self.edit_target.replace_with(|current| {
            changed = *current != target;
            target
        });
        if changed && !std::thread::panicking() {
            self.notify(Notice::EditTargetChanged);
        }
    }

    /// Scope a temporary edit-target switch. Sets `target` as the current edit
    /// target and returns an [`EditContext`] guard that restores the previous
    /// target when dropped — including on early return via `?`. Mirrors C++
    /// `UsdEditContext`.
    ///
    /// Returns an error (leaving the current target unchanged) when `target`
    /// fails the same validation as [`set_edit_target`](Self::set_edit_target).
    pub fn edit_context(&self, target: EditTarget) -> Result<EditContext<'_>, StageAuthoringError> {
        let saved = self.edit_target.borrow().clone();
        self.set_edit_target(target)?;
        Ok(EditContext { stage: self, saved })
    }

    /// Author a `def` prim spec at `path` on the edit target's layer and
    /// return a [`Prim`] handle. Mirrors C++ `UsdStage::DefinePrim`. The
    /// returned handle lets callers chain field setters (`set_type_name`,
    /// `set_active`, `set_kind`, …) and child-property authoring
    /// (`create_attribute`, `create_relationship`).
    pub fn define_prim(&self, path: impl Into<sdf::Path>) -> Result<super::Prim, StageAuthoringError> {
        let path = path.into();
        self.with_target_layer_at(&path, |layer, layer_path| {
            // The layer's `EditProxy` records the spec add and any auto-created
            // ancestor `over`s; an idempotent call (existing def) records
            // nothing because the value-diff suppresses the no-op write.
            sdf::PrimSpec::new(layer.data_mut(), layer_path, sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        Ok(super::Prim::new(self, path))
    }

    /// Ensure a prim spec exists at `path` and return a [`Prim`] handle.
    /// Mirrors C++ `UsdStage::OverridePrim`. If a spec already exists at
    /// `path` its specifier is left untouched — `override_prim` does not
    /// downgrade an existing `def` or `class` to `over`. Chain fluent
    /// setters on the returned handle to author additional fields.
    pub fn override_prim(&self, path: impl Into<sdf::Path>) -> Result<super::Prim, StageAuthoringError> {
        let path = path.into();
        self.with_target_layer_at(&path, |layer, layer_path| {
            sdf::PrimSpec::over(layer.data_mut(), layer_path)?;
            Ok(())
        })?;
        Ok(super::Prim::new(self, path))
    }

    /// Author an attribute spec at a property path (e.g. `/World/Mesh.points`)
    /// on the edit target's layer with default variability `Varying` and
    /// `custom = true`, matching C++ `UsdPrim::CreateAttribute`'s generic
    /// overloads. Override the defaults via the returned
    /// [`Attribute`](super::Attribute) handle's fluent setters.
    pub fn create_attribute(
        &self,
        path: impl Into<sdf::Path>,
        type_name: impl Into<String>,
    ) -> Result<super::Attribute, StageAuthoringError> {
        let path = path.into();
        let type_name = type_name.into();
        self.with_target_layer_at(&path, |layer, layer_path| {
            // The owning prim and any missing ancestors are auto-created as
            // `over` specs; the layer's `EditProxy` records them and the
            // property add.
            sdf::AttributeSpec::new(layer.data_mut(), layer_path, type_name, sdf::Variability::Varying, true)?;
            Ok(())
        })?;
        Ok(super::Attribute::new(self, path))
    }

    /// Author a relationship spec at a property path on the edit target's
    /// layer with default variability `Varying` and `custom = true`, matching
    /// C++ `UsdPrim::CreateRelationship`. Override the defaults and add targets
    /// via the returned [`Relationship`] handle's fluent setters.
    pub fn create_relationship(&self, path: impl Into<sdf::Path>) -> Result<super::Relationship, StageAuthoringError> {
        let path = path.into();
        self.with_target_layer_at(&path, |layer, layer_path| {
            sdf::RelationshipSpec::new(layer.data_mut(), layer_path, sdf::Variability::Varying, true)?;
            Ok(())
        })?;
        Ok(super::Relationship::new(self, path))
    }

    /// Remove the prim spec at `path` (and its descendant specs) from the
    /// current edit target's layer. Mirrors C++ `UsdStage::RemovePrim`.
    ///
    /// Returns `true` when a spec was present and removed, `false` when the
    /// edit-target layer had nothing at `path`. The removal is authored on the
    /// current [`EditTarget`], fires [`Notice::ObjectsChanged`], and invalidates
    /// the affected composition subtree — a prim removed from the edit-target
    /// layer drops out of the composed stage when no weaker layer still defines
    /// it.
    pub fn remove_prim(&self, path: impl Into<sdf::Path>) -> Result<bool, StageAuthoringError> {
        let path = path.into();
        if path.is_property_path() {
            return Err(sdf::AuthoringError::InvalidPath {
                path,
                reason: "remove_prim expects a prim path, got a property path",
            }
            .into());
        }
        self.remove_spec(&path)
    }

    /// Remove the property spec (attribute or relationship) at `path` from the
    /// current edit target's layer. Mirrors C++ `UsdPrim::RemoveProperty`.
    ///
    /// Returns `true` when a spec was present and removed, `false` when the
    /// edit-target layer had nothing at `path`. The removal is authored on the
    /// current [`EditTarget`], fires [`Notice::ObjectsChanged`], and invalidates
    /// the owning prim.
    pub fn remove_property(&self, path: impl Into<sdf::Path>) -> Result<bool, StageAuthoringError> {
        let path = path.into();
        if !path.is_property_path() {
            return Err(sdf::AuthoringError::InvalidPath {
                path,
                reason: "remove_property expects a property path, got a prim path",
            }
            .into());
        }
        self.remove_spec(&path)
    }

    /// Erase the spec at `path` on the current edit target's layer, routing
    /// through [`with_target_layer_at`](Self::with_target_layer_at) so the edit
    /// target mapping, change recording, invalidation, and notice all run. The
    /// returned `bool` reflects whether the erase recorded any change, which is
    /// exactly whether a spec was present. Shared by [`remove_prim`](Self::remove_prim)
    /// and [`remove_property`](Self::remove_property).
    fn remove_spec(&self, path: &sdf::Path) -> Result<bool, StageAuthoringError> {
        self.with_target_layer_at(path, |layer, layer_path| {
            layer.remove_spec(&layer_path);
            Ok(())
        })
    }

    /// Author `defaultPrim` on the stage's root layer.
    ///
    /// `defaultPrim` is a layer-level field that resolves from the root
    /// layer only (AOUSD §12.2.7), so this method always writes to the root
    /// layer regardless of the current [`EditTarget`]. Mirrors C++
    /// `UsdStage::SetDefaultPrim` which routes through `GetRootLayer()`.
    ///
    /// `name` must be a valid USD identifier or nested prim path — see
    /// [`sdf::Layer::set_default_prim`].
    pub fn set_default_prim(&self, name: impl Into<String>) -> Result<(), StageAuthoringError> {
        let name = name.into();
        self.with_root_layer(|layer| {
            // The layer's `EditProxy` records the `defaultPrim` change, and its
            // value-diff skips cache invalidation when the value isn't changing.
            layer.set_default_prim(name)?;
            Ok(())
        })
    }

    /// Authors the root layer's `customLayerData` dictionary. Mirrors C++
    /// `UsdStage::GetRootLayer()->SetCustomLayerData()`: the write targets the
    /// root layer regardless of the current [`EditTarget`], pairing with
    /// [`Stage::custom_layer_data`].
    pub fn set_custom_layer_data(&self, value: impl Into<sdf::Value>) -> Result<(), StageAuthoringError> {
        let value = value.into();
        self.with_root_layer(|layer| {
            layer
                .pseudo_root_mut()?
                .set(sdf::FieldKey::CustomLayerData.as_str(), value);
            Ok(())
        })
    }

    /// A non-owning [`WeakStage`] handle to this stage (C++
    /// `UsdStage::GetWeakPtr`-style). Capture this inside a change listener that
    /// must retain stage access, so the listener does not leak the stage.
    pub fn downgrade(&self) -> WeakStage {
        WeakStage(Rc::downgrade(&self.0))
    }

    /// Install this stage's change listener, replacing any previous one
    /// (C++ `TfNotice::Register`).
    ///
    /// The callback fires after every successful, non-empty edit with the
    /// originating stage and a [`Notice`]. It may read the stage, call
    /// [`extract_diff`](Self::extract_diff), or author further edits.
    ///
    /// It must not call `set_listener` / `unset_listener`, though: the listener
    /// slot is held borrowed across the call, so mutating it from inside the
    /// callback (e.g. a "fire once then detach" pattern) panics with a
    /// [`RefCell`](std::cell::RefCell) double borrow. Detach from outside the
    /// callback, or have the closure gate itself on captured state instead.
    ///
    /// A single slot: register one closure and fan out to multiple sinks inside
    /// it. The stage is passed to the callback as an argument so the closure
    /// need not capture one; capturing a [`Stage`] clone forms a reference
    /// cycle that leaks the stage, so capture a [`WeakStage`] from
    /// [`downgrade`](Self::downgrade) if you must retain stage access.
    ///
    /// Returns the previously installed listener, if any, so a caller can
    /// temporarily swap in a listener and later restore the old one.
    pub fn set_listener(&self, f: impl Fn(&Stage, Notice<'_>) + 'static) -> Option<ChangeListener> {
        self.listener.replace(Some(Box::new(f)))
    }

    /// Remove this stage's change listener and return it, if one was installed.
    pub fn unset_listener(&self) -> Option<ChangeListener> {
        self.listener.take()
    }

    /// Deliver `notice` to the installed listener, if any. The listener slot is
    /// borrowed across the call, so the callback must not set/unset the listener
    /// (see [`set_listener`](Self::set_listener)); reading or re-authoring the
    /// stage is fine. Callers must release any other stage borrow first, since
    /// the callback may read or mutate the stage.
    fn notify(&self, notice: Notice<'_>) {
        if let Some(listener) = self.listener.borrow().as_ref() {
            listener(self, notice);
        }
    }

    /// Extract a serializable diff for the edit described by `objects`.
    ///
    /// Reads the authored values for the specs named in
    /// [`objects.change_list`](ObjectsChanged::change_list) out of the
    /// originating layer into a fresh anonymous [`sdf::Layer`]. Deletions an
    /// overlay layer cannot express — whole-spec removals and erased fields —
    /// are reported out of band in [`LayerDiff::removed`]. Call it synchronously
    /// from the listener callback: the notice borrows the transient change
    /// record and the layer keeps mutating afterward.
    ///
    /// List-valued field edits (reference / target / apiSchema removals
    /// included) ride along in the layer as their authored list ops.
    ///
    /// The diff is in the originating layer's namespace: for an edit authored
    /// through an arc or variant edit target the specs carry the arc source
    /// layer's paths (e.g. a `{set=sel}` variant segment), not the composed
    /// stage paths. This is deliberate — the diff is meant to be replayed onto
    /// the same layer on a mirror, where the layer-namespace paths apply
    /// directly. The composed stage paths the edit touched are reported
    /// separately on
    /// [`ObjectsChanged`](super::ObjectsChanged) (`resynced` /
    /// `changed_info_only`).
    pub fn extract_diff(&self, objects: &ObjectsChanged<'_>) -> Result<LayerDiff> {
        let mut layer = sdf::Layer::new_anonymous("diff");
        let mut removed = Vec::new();
        let layers = self.layers();
        let layer_id = layers
            .id_of(objects.layer_identifier)
            .ok_or_else(|| anyhow::anyhow!("change notice references a layer no longer in the stage"))?;
        let src = layers.layer(layer_id).data();
        for (path, entry) in objects.change_list.entries() {
            // A spec's presence in `src` is the source of truth: one still there
            // (added, modified, or removed-then-re-added within the edit) is
            // copied with its current authored state; one gone with a removal
            // flag is a whole-spec deletion the overlay layer cannot carry.
            if src.spec_type(path).is_some() {
                layer.copy_spec_from(src, path)?;
                // A field the edit touched but that is now absent from `src` was
                // erased, not set; the copied overlay can't express that, so
                // carry it for the mirror to erase. Child-name lists are
                // structural bookkeeping `copy_spec_from` maintains, not authored
                // opinions to delete.
                for field in &entry.info_changed {
                    let name = field.as_str();
                    if name == sdf::ChildrenKey::PrimChildren.as_str()
                        || name == sdf::ChildrenKey::PropertyChildren.as_str()
                    {
                        continue;
                    }
                    if src.try_field(path, name)?.is_none() {
                        removed.push(Deletion::Field(path.clone(), field.clone()));
                    }
                }
            } else if entry.flags.intersects(sdf::ChangeFlags::REMOVE) {
                removed.push(Deletion::Spec(path.clone()));
            }
        }
        Ok(LayerDiff { layer, removed })
    }

    /// Replay a [`LayerDiff`] onto the current edit target's layer in one
    /// transaction, the consume half of [`extract_diff`](Self::extract_diff).
    /// The diff's overlay specs are copied in (adds plus value, metadata, and
    /// list-op target edits) and each [`Deletion`] the overlay cannot carry is
    /// applied: a whole-spec removal through [`sdf::Layer::remove_spec`], an
    /// erased field through [`sdf::AbstractData::erase_field`]. The whole replay
    /// drains as a single edit, firing one [`Notice::ObjectsChanged`] and
    /// invalidating composition for every path it touched.
    ///
    /// The diff is applied in the originating layer's namespace, so this is
    /// exact when the target's edit layer shares that namespace — the common
    /// local / root-layer mirror. Translating a diff authored through an arc or
    /// variant edit target into a different target namespace is a separate
    /// feature; until it lands, mirror through a matching edit target.
    ///
    /// `apply_diff` fires this stage's own `ObjectsChanged`. A bidirectional
    /// mirror that feeds those notices back to the origin must tag or suppress
    /// the echo itself — that is an application-level concern this method does
    /// not arbitrate.
    pub fn apply_diff(&self, diff: &LayerDiff) -> Result<(), StageAuthoringError> {
        // The diff's paths are in the originating layer's namespace and are
        // authored verbatim, with `mapping = None` in the notice. Under a
        // non-identity target (variant or arc) that would silently write to the
        // wrong spec paths, so refuse rather than mis-author. Replaying through
        // the target mapping is the arc-target translation feature.
        if !self.edit_target.borrow().mapping.is_identity() {
            return Err(StageAuthoringError::NonLocalEditTarget);
        }
        let layer_id = self.edit_target_layer_id()?;
        // TODO: this replay is not atomic — if `apply_diff_to_layer` fails after
        // copying some specs, `finalize_layer`'s error path discards the change
        // record but not the partial layer mutations, leaving a half-applied
        // diff that composition then rebuilds over. Apply to a scratch layer and
        // swap on success (or pre-validate every path) to make it all-or-nothing.
        let authored = {
            let mut layers = self.layers.borrow_mut();
            let node = layers
                .get_mut(layer_id)
                .expect("edit-target layer id refers to a live layer");
            apply_diff_to_layer(&mut node.layer, diff).map_err(StageAuthoringError::Composition)
        };
        self.finalize_layer(layer_id, authored, None).map(|_| ())
    }

    /// The id of the layer the current edit target writes to, or
    /// [`StageAuthoringError::LayerNotFound`] when that layer is no longer in
    /// the stage. Resolves the edit-target identifier to its graph id, the
    /// shared step of the stage-metadata and diff-replay authoring paths.
    fn edit_target_layer_id(&self) -> Result<pcp::LayerId, StageAuthoringError> {
        let identifier = self.edit_target.borrow().layer_identifier.clone();
        self.layers
            .borrow()
            .id_of(&identifier)
            .ok_or(StageAuthoringError::LayerNotFound { layer: identifier })
    }

    /// Authors `startTimeCode` on the current edit target's layer when it is
    /// the root or session layer (see [`Self::with_stage_metadata_layer`]).
    /// Mirrors C++ `UsdStage::SetStartTimeCode`.
    pub fn set_start_time_code(&self, time: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_start_time_code(time))
    }

    /// Authors `endTimeCode` on the current edit target's layer when it is the
    /// root or session layer (see [`Self::with_stage_metadata_layer`]). Mirrors
    /// C++ `UsdStage::SetEndTimeCode`.
    pub fn set_end_time_code(&self, time: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_end_time_code(time))
    }

    /// Authors `timeCodesPerSecond` on the current edit target's layer when it
    /// is the root or session layer (see [`Self::with_stage_metadata_layer`]).
    /// Mirrors C++ `UsdStage::SetTimeCodesPerSecond`.
    pub fn set_time_codes_per_second(&self, rate: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_time_codes_per_second(rate))
    }

    /// Authors `framesPerSecond` on the current edit target's layer when it is
    /// the root or session layer (see [`Self::with_stage_metadata_layer`]).
    /// Mirrors C++ `UsdStage::SetFramesPerSecond`.
    pub fn set_frames_per_second(&self, rate: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_frames_per_second(rate))
    }

    /// Map `scene_path` through the current edit target, borrow the target's
    /// layer, and hand both the layer and the mapped spec path to `f`, then
    /// drive cache invalidation from the [`sdf::ChangeList`] the closure
    /// returns.
    ///
    /// The closure receives the spec (layer-namespace) path; under a local
    /// target this equals `scene_path`, under a variant target it carries the
    /// `{set=sel}` segment. The closure must author at, and record its
    /// `ChangeList` against, that spec path — `did_change` consumes paths in
    /// layer namespace.
    ///
    /// Callers must drop any typed spec view inside the closure — the closure
    /// can't return a borrow from `&mut layer`. The returned [`sdf::ChangeList`]
    /// describes what was authored; an empty list means "no mutation
    /// happened" and skips invalidation.
    ///
    /// On any post-mutation error the cache falls back to "blow the world".
    pub(super) fn with_target_layer_at<F>(&self, scene_path: &sdf::Path, f: F) -> Result<bool, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer, sdf::Path) -> Result<(), sdf::AuthoringError>,
    {
        // Read the target identifier and mapped spec path under a short borrow
        // of `edit_target` (which owns a heap `MapFunction`), releasing it
        // before the layer borrow below. The mapping is cloned out (rather than
        // borrowed across `finalize_layer`) because the listener it ultimately
        // feeds can re-author and re-target the stage; clone it only when a
        // listener is installed to consume it, keeping the common no-listener
        // authoring path allocation-free.
        let notify = self.listener.borrow().is_some();
        let (identifier, spec_path, mapping) = {
            let target = self.edit_target.borrow();
            let spec_path =
                target
                    .map_to_spec_path(scene_path)
                    .ok_or_else(|| StageAuthoringError::OutsideEditTarget {
                        path: scene_path.clone(),
                    })?;
            (
                target.layer_identifier.clone(),
                spec_path,
                notify.then(|| target.mapping.clone()),
            )
        };
        let (layer_id, authored) = {
            let mut layers = self.layers.borrow_mut();
            let layer_id = layers
                .id_of(&identifier)
                .ok_or(StageAuthoringError::LayerNotFound { layer: identifier })?;
            let node = layers.get_mut(layer_id).expect("id_of returned a live id");
            (
                layer_id,
                f(&mut node.layer, spec_path).map_err(StageAuthoringError::from),
            )
        };
        self.finalize_layer(layer_id, authored, mapping.as_ref())
    }

    /// Borrow the stage's root layer, hand it to `f`, then drive cache
    /// invalidation from the closure's [`sdf::ChangeList`]. See
    /// [`Stage::with_target_layer_at`] for the contract. Unlike that method,
    /// this ignores the edit target and its mapping — `defaultPrim` is a
    /// root-layer field authored at `abs_root` verbatim.
    fn with_root_layer<F>(&self, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer) -> Result<(), sdf::AuthoringError>,
    {
        let layer_id = self
            .layers
            .borrow()
            .root_id()
            .ok_or(StageAuthoringError::OutsideEditTarget {
                path: sdf::Path::abs_root(),
            })?;
        self.author_on_layer(layer_id, f)
    }

    /// Author stage-level metadata on the current edit target's layer, but only
    /// when that layer is the stage's root or session layer — the layers stage
    /// metadata resolves from (session over root). Mirrors C++ `UsdStage`'s
    /// edit-target-aware stage-metadata authoring; returns
    /// [`StageAuthoringError::StageMetadataTarget`] when the edit target is any
    /// other layer, where the opinion would never resolve.
    ///
    /// The closure authors at `abs_root` verbatim; the edit target's namespace
    /// mapping is irrelevant for layer-wide metadata.
    fn with_stage_metadata_layer<F>(&self, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer) -> Result<(), sdf::AuthoringError>,
    {
        let layer_id = self.edit_target_layer_id()?;
        {
            let layers = self.layers.borrow();
            if layers.root_id() != Some(layer_id) && !layers.session_layers().contains(&layer_id) {
                return Err(StageAuthoringError::StageMetadataTarget {
                    layer: layers.identifier(layer_id).to_string(),
                });
            }
        }
        self.author_on_layer(layer_id, f)
    }

    /// Borrow the layer identified by `layer_id` mutably, run `f`, then drive
    /// cache invalidation from the change list it records. The shared tail of
    /// [`Self::with_root_layer`] and [`Self::with_stage_metadata_layer`].
    fn author_on_layer<F>(&self, layer_id: pcp::LayerId, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer) -> Result<(), sdf::AuthoringError>,
    {
        let authored = {
            let mut layers = self.layers.borrow_mut();
            let node = layers.get_mut(layer_id).expect("layer id refers to a live layer");
            f(&mut node.layer).map_err(StageAuthoringError::from)
        };
        self.finalize_layer(layer_id, authored, None).map(|_| ())
    }

    /// Drain the layer's recorded changes after an authoring call and drive
    /// composition invalidation from them. On success the layer's `EditProxy`
    /// change list is taken and classified through [`pcp::Changes`]: an empty
    /// list short-circuits with no invalidation, a non-empty one is applied. On
    /// failure the partial record is discarded and the cache falls back to a
    /// stage-wide blow-out, because the layer may be in a partial state.
    ///
    /// `mapping` is the edit target's namespace mapping (layer source to stage
    /// target), used to translate the change record's layer-namespace paths back
    /// to stage namespace for the notice. `None` means identity — a root or
    /// metadata edit whose paths are already in stage namespace.
    //
    // TODO: the error-path fallback to layer-stack-wide reset is
    // conservative. Once `Layer` authoring methods either complete
    // atomically or return a "partial mutation up to here" marker, the
    // fallback can be narrowed to just the paths the closure touched
    // before failing.
    fn finalize_layer(
        &self,
        layer_id: pcp::LayerId,
        authored: Result<(), StageAuthoringError>,
        mapping: Option<&pcp::MapFunction>,
    ) -> Result<bool, StageAuthoringError> {
        // Drain the layer's record into the stage scratch buffer (reusing its
        // allocation across edits) — or discard a partial record — under a short
        // layer borrow, before re-borrowing the graph and cache for classification.
        let mut scratch = self.change_scratch.borrow_mut();
        scratch.clear();
        let drained = {
            let mut layers = self.layers.borrow_mut();
            let node = layers
                .get_mut(layer_id)
                .expect("finalize_layer called with a live layer id");
            match authored {
                Ok(()) => {
                    node.layer.drain_changes(&mut scratch);
                    Ok(())
                }
                Err(e) => {
                    node.layer.discard_changes();
                    Err(e)
                }
            }
        };
        match drained {
            Ok(()) if scratch.is_empty() => Ok(false),
            Ok(()) => {
                let mut changes = pcp::Changes::new();
                let edits = [(layer_id, &*scratch)];
                {
                    let cache = self.cache.borrow();
                    changes.did_change(&cache, &edits);
                }
                // Snapshot the notice payload before `apply` consumes `changes`,
                // and only when a listener is installed — the no-listener path
                // stays allocation-free.
                let payload = self
                    .listener
                    .borrow()
                    .is_some()
                    .then(|| notice::Payload::new(&changes, &scratch, mapping));
                {
                    let mut graph = self.layers.borrow_mut();
                    let mut cache = self.cache.borrow_mut();
                    changes.apply(&mut cache, &mut graph);
                }

                if let Some(payload) = payload {
                    let layer_identifier = self.layer_identifier(layer_id).unwrap_or_default();
                    // Release the scratch borrow before invoking the listener:
                    // it may re-author, which re-enters `finalize_layer` and
                    // re-borrows this buffer.
                    drop(scratch);
                    self.notify(Notice::ObjectsChanged(
                        payload.objects_changed(&layer_identifier, mapping),
                    ));
                }
                Ok(true)
            }
            Err(e) => {
                // Conservatively drop every cached index on post-mutation
                // failure (the layer may be in a partial state). `SIGNIFICANT`
                // alone is enough — `apply` routes it through `clear_all_indices`
                // and the layer graph cannot have been affected by a failing
                // prim/property edit.
                let mut changes = pcp::Changes::new();
                changes.layer_stack |= pcp::LayerStackChanges::SIGNIFICANT;
                let mut graph = self.layers.borrow_mut();
                let mut cache = self.cache.borrow_mut();
                changes.apply(&mut cache, &mut graph);
                Err(e)
            }
        }
    }

    /// Returns the number of layers in the stage (including session layers).
    pub fn layer_count(&self) -> usize {
        self.layers().len()
    }

    /// Returns `true` when the composition cache currently holds a prim
    /// index at `path`. Useful for verifying surgical invalidation and
    /// for callers that want to observe cache occupancy.
    pub fn is_indexed(&self, path: &sdf::Path) -> bool {
        self.cache().is_indexed(path)
    }

    /// Total number of cached prim indices.
    pub fn indexed_count(&self) -> usize {
        self.cache().indexed_count()
    }

    /// Returns the layer identifiers in strength order (session layers first,
    /// then root layer and its sublayers).
    pub fn layer_identifiers(&self) -> Vec<String> {
        self.layers().identifiers()
    }

    /// Returns the identifiers of the stage's root layer stack — the session
    /// layers, the root layer, and its sublayers, in strength order. Mirrors
    /// C++ `UsdStage::GetLayerStack` (with `includeSessionLayers = true`).
    ///
    /// Unlike [`layer_identifiers`](Self::layer_identifiers), which lists every
    /// loaded layer including those reached across reference/payload arcs, this
    /// is only the local layer stack a top-level prim scans for direct opinions.
    pub fn layer_stack(&self) -> Vec<String> {
        self.layers().root_layer_stack_identifiers()
    }

    /// Returns `true` if the stage has a session layer.
    pub fn has_session_layer(&self) -> bool {
        self.layers().session_layer_count() > 0
    }

    /// Borrows the stage's root layer (C++ `UsdStage::GetRootLayer`). Panics if
    /// the stage has no root layer (only possible for a degenerate empty graph,
    /// which `StageBuilder` never produces).
    ///
    /// The returned [`Ref`] borrows the layer graph, and a `&self` authoring
    /// call (`insert_sub_layer`, `define_prim`, …) takes `self.layers` mutably,
    /// so a live `Ref` held across one panics with a `RefCell` double-borrow. In
    /// particular `stage.insert_sub_layer(stage.root_layer().identifier(), …)`
    /// panics — the `Ref` temporary lives to the end of the statement. Bind the
    /// identifier first so the borrow is released:
    ///
    /// ```no_run
    /// # use openusd::{sdf, usd};
    /// # fn f(stage: &usd::Stage, layer: sdf::Layer) {
    /// let id = stage.root_layer().identifier().to_owned();
    /// stage.insert_sub_layer(&id, 0, layer, sdf::LayerOffset::IDENTITY).unwrap();
    /// # }
    /// ```
    pub fn root_layer(&self) -> Ref<'_, sdf::Layer> {
        Ref::map(self.layers(), |layers| {
            layers.root_layer().expect("stage has a root layer")
        })
    }

    /// The identifiers of the layers contributing to `parent`'s sublayer stack,
    /// in strength order (the parent first). Empty when `parent` is not in the
    /// stage. `parent` is matched by its canonical identifier.
    pub fn sub_layers(&self, parent: &str) -> Vec<String> {
        let graph = self.layers();
        let Some(parent_id) = graph.id_of(parent) else {
            return Vec::new();
        };
        graph.identifiers_of(graph.sublayer_stack(parent_id).iter().map(|&(id, _)| id))
    }

    /// Records a layer identifier in the muted set (C++ `UsdStage::MuteLayer`,
    /// which likewise mutes by identifier — the layer need not be loaded). Full
    /// value-resolution suppression of muted layers is not yet wired into
    /// composition.
    pub fn mute_layer(&self, identifier: impl Into<String>) {
        let identifier = identifier.into();
        // Bind the result so the `muted` borrow is released before notifying:
        // the listener may read the muted set or re-author.
        let newly_muted = self.muted.borrow_mut().insert(identifier.clone());
        if newly_muted {
            self.notify(Notice::LayerMutingChanged(LayerMutingChanged {
                layer: &identifier,
                muted: true,
            }));
        }
    }

    /// Removes a layer identifier from the muted set.
    pub fn unmute_layer(&self, identifier: &str) {
        let was_muted = self.muted.borrow_mut().remove(identifier);
        if was_muted {
            self.notify(Notice::LayerMutingChanged(LayerMutingChanged {
                layer: identifier,
                muted: false,
            }));
        }
    }

    /// Whether the layer with the given identifier is currently muted.
    pub fn is_layer_muted(&self, identifier: &str) -> bool {
        self.muted.borrow().contains(identifier)
    }

    /// The currently muted layer identifiers, sorted for a deterministic result.
    pub fn muted_layers(&self) -> Vec<String> {
        let mut ids: Vec<String> = self.muted.borrow().iter().cloned().collect();
        ids.sort();
        ids
    }

    /// Returns the stage's initial payload loading behavior.
    pub fn load(&self) -> InitialLoadSet {
        self.initial_load_set
    }

    /// Returns the population mask used by this stage.
    pub fn mask(&self) -> &StagePopulationMask {
        &self.population_mask
    }

    /// Borrows the stage's strongest session layer, if one was provided (C++
    /// `UsdStage::GetSessionLayer`).
    ///
    /// Like [`root_layer`](Self::root_layer), the returned [`Ref`] borrows the
    /// layer graph. Drop it before calling an authoring method that mutably
    /// borrows the graph.
    pub fn session_layer(&self) -> Option<Ref<'_, sdf::Layer>> {
        Ref::filter_map(self.layers(), |layers| {
            let id = *layers.session_layers().first()?;
            Some(layers.layer(id))
        })
        .ok()
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    ///
    /// When a session layer is present, `defaultPrim` is still read from
    /// the root layer (not the session layer), matching C++ behavior.
    pub fn default_prim(&self) -> Option<Token> {
        self.with_cache(|g, c| Ok(c.default_prim(g))).unwrap_or_default()
    }

    /// Returns composed pseudo-root stage metadata, honoring a session-layer
    /// opinion over the root layer (C++ `UsdStage::GetMetadata`).
    ///
    /// Distinct from [`Stage::field`] on [`sdf::Path::abs_root`], which reads
    /// root-layer-only metadata for the spec 12.2.7 fields like `defaultPrim`.
    /// Returns the raw [`sdf::Value`]; the caller coerces it.
    pub fn stage_metadata(&self, field: impl AsRef<str>) -> Result<Option<sdf::Value>> {
        self.with_cache(|g, c| c.stage_metadata(g, field.as_ref()))
    }

    /// The stage's `startTimeCode`, or `0.0` when unauthored. The session
    /// layer's opinion wins over the root layer (via [`Stage::stage_metadata`]).
    /// Mirrors C++ `UsdStage::GetStartTimeCode`.
    pub fn start_time_code(&self) -> f64 {
        self.metadata_double(sdf::FieldKey::StartTimeCode).unwrap_or(0.0)
    }

    /// The stage's `endTimeCode`, or `0.0` when unauthored. The session layer's
    /// opinion wins over the root layer. Mirrors C++ `UsdStage::GetEndTimeCode`.
    pub fn end_time_code(&self) -> f64 {
        self.metadata_double(sdf::FieldKey::EndTimeCode).unwrap_or(0.0)
    }

    /// Whether the stage authors both `startTimeCode` and `endTimeCode`.
    /// Mirrors C++ `UsdStage::HasAuthoredTimeCodeRange`.
    pub fn has_authored_time_code_range(&self) -> bool {
        self.metadata_double(sdf::FieldKey::StartTimeCode).is_some()
            && self.metadata_double(sdf::FieldKey::EndTimeCode).is_some()
    }

    /// The stage's `timeCodesPerSecond`. Falls back to the authored
    /// `framesPerSecond`, then to `24.0`, when unauthored. The session layer's
    /// opinion wins over the root layer. Mirrors C++
    /// `UsdStage::GetTimeCodesPerSecond`.
    pub fn time_codes_per_second(&self) -> f64 {
        self.metadata_double(sdf::FieldKey::TimeCodesPerSecond)
            .or_else(|| self.metadata_double(sdf::FieldKey::FramesPerSecond))
            .unwrap_or(24.0)
    }

    /// The stage's `framesPerSecond`, or `24.0` when unauthored. The session
    /// layer's opinion wins over the root layer. Mirrors C++
    /// `UsdStage::GetFramesPerSecond`.
    pub fn frames_per_second(&self) -> f64 {
        self.metadata_double(sdf::FieldKey::FramesPerSecond).unwrap_or(24.0)
    }

    /// Reads a composed stage-metadata field as a `double`, honoring the
    /// session-over-root resolution of [`Stage::stage_metadata`]. `None` when
    /// unauthored or stored with a non-`double` value.
    fn metadata_double(&self, field: sdf::FieldKey) -> Option<f64> {
        self.stage_metadata(field.as_str())
            .ok()
            .flatten()
            .and_then(|v| v.try_as_double())
    }

    /// Returns the stage-level interpolation mode applied when resolving a
    /// value at a time code (see [`Attribute::get`](super::Attribute::get)).
    /// AOUSD §12.5 defaults this to [`InterpolationType::Linear`].
    pub fn interpolation_type(&self) -> InterpolationType {
        self.interpolation_type.get()
    }

    /// Override the stage-level interpolation mode at runtime.
    /// Cheap — no recomputation, the next value resolution reads the new mode.
    pub fn set_interpolation_type(&self, mode: InterpolationType) {
        self.interpolation_type.set(mode);
    }

    /// Returns the composed `timeSamples` for an attribute, or
    /// `None` when the attribute has none authored.
    ///
    /// This returns raw composed samples. Read through
    /// [`Attribute::get`](super::Attribute::get) with a time code when you
    /// need the stage's [`InterpolationType`] applied to a specific time.
    pub fn time_samples(&self, attr_path: impl Into<sdf::Path>) -> Result<Option<sdf::TimeSampleMap>> {
        Ok(match self.field::<sdf::Value>(attr_path, sdf::FieldKey::TimeSamples)? {
            Some(sdf::Value::TimeSamples(samples)) => Some(samples),
            _ => None,
        })
    }

    /// Returns the composed `timeSamples` sample times for an attribute, or
    /// `None` when none are authored. Resolves the times without cloning the
    /// sample values, retimed by the contributing layer offsets to match
    /// [`Self::time_samples`].
    pub fn time_sample_times(&self, attr_path: impl Into<sdf::Path>) -> Result<Option<Vec<f64>>> {
        let attr_path = attr_path.into();
        self.masked(&attr_path, |g, c| c.time_sample_times(g, &attr_path))
    }

    /// Returns the number of composed `timeSamples` for an attribute, zero when
    /// none are authored. Resolves the count without cloning the sample values.
    pub fn num_time_samples(&self, attr_path: impl Into<sdf::Path>) -> Result<usize> {
        let attr_path = attr_path.into();
        self.masked(&attr_path, |g, c| c.num_time_samples(g, &attr_path))
    }

    /// Evaluate an attribute's value at `time` under the stage's current
    /// [`InterpolationType`]. The crate-internal resolution engine behind
    /// [`Attribute::get`](super::Attribute::get) with a numeric time code.
    ///
    /// Resolution order (AOUSD §12.3):
    /// 1. Local `timeSamples` (root layer stack), §12.5 interpolated.
    /// 2. Value clips anchored on the prim or an ancestor (§12.3.4).
    /// 3. Remaining `timeSamples` (reference/payload arcs), interpolated.
    /// 4. The attribute's `default` value.
    ///
    /// Returns `Ok(None)` when the attribute is unauthored, when the
    /// authored value is a [`sdf::Value::ValueBlock`] / [`sdf::Value::None`]
    /// (the spec sentinels for "no value"), or when the queried prim
    /// is excluded by the stage's population mask.
    pub(crate) fn resolve_at(&self, attr_path: impl Into<sdf::Path>, time: f64) -> Result<Option<sdf::Value>> {
        let attr_path = attr_path.into();
        if !self.mask_includes(&attr_path.prim_path()) {
            return Ok(None);
        }
        let interp_type = self.interpolation_type.get();
        let interp = |samples: &sdf::TimeSampleMap, t: f64| interp::evaluate(samples, t, interp_type);
        self.with_cache(|g, c| c.value_at(g, &attr_path, time, &interp))
    }

    /// Resolves the cacheable value source for an attribute, the source half of
    /// [`Self::resolve_at`]. Backs [`AttributeQuery`](super::AttributeQuery),
    /// which snapshots the source and replays it across time codes. Returns
    /// [`AttributeValueSource::Static`](pcp::AttributeValueSource::Static)
    /// `None` when the attribute's prim is outside the population mask.
    pub(crate) fn resolve_value_source(&self, attr_path: &sdf::Path) -> Result<pcp::AttributeValueSource> {
        if !self.mask_includes(&attr_path.prim_path()) {
            return Ok(pcp::AttributeValueSource::Static(None));
        }
        self.with_cache(|g, c| c.resolve_value_source(g, attr_path))
    }

    /// The current composition revision, advanced once per applied edit batch.
    /// [`AttributeQuery`](super::AttributeQuery) snapshots this and rebuilds its
    /// cached source when it advances.
    pub(crate) fn cache_revision(&self) -> u64 {
        self.cache.borrow().revision()
    }

    /// Returns a [`Prim`](super::Prim) handle anchored to `path`. Mirrors C++
    /// `UsdStage::GetPrimAtPath`. The handle is a value-type `(stage, path)`
    /// wrapper; it is returned unconditionally and does not assert that a prim
    /// is composed at the path (query the handle to find out).
    pub fn prim(&self, path: impl Into<sdf::Path>) -> super::Prim {
        super::Prim::new(self, path.into().prim_path())
    }

    /// Returns an [`Attribute`](super::Attribute) handle anchored to `path`.
    /// Mirrors C++ `UsdStage::GetAttributeAtPath`. Like [`Self::prim`],
    /// the handle is returned unconditionally; query it to resolve a value.
    pub fn attribute(&self, path: impl Into<sdf::Path>) -> super::Attribute {
        super::Attribute::new(self, path.into())
    }

    /// Returns a [`Relationship`](super::Relationship) handle anchored to `path`.
    /// Mirrors C++ `UsdStage::GetRelationshipAtPath`.
    pub fn relationship(&self, path: impl Into<sdf::Path>) -> super::Relationship {
        super::Relationship::new(self, path.into())
    }

    /// Returns an [`AttributeQuery`](super::AttributeQuery) for the attribute at
    /// `path` — a cached value source for repeated time-code reads. The
    /// `Stage`-anchored spelling of [`Attribute::query`](super::Attribute::query).
    pub fn attribute_query(&self, path: impl Into<sdf::Path>) -> super::AttributeQuery {
        super::AttributeQuery::new(&self.attribute(path))
    }

    /// Returns the composed list of root prim names (children of the pseudo-root).
    pub fn root_prims(&self) -> Result<Vec<Token>> {
        let root = sdf::Path::abs_root();
        let children = self.with_cache(|g, c| c.prim_children(g, &root))?;
        Ok(self.filter_child_names(&root, children))
    }

    // `has_spec` / `spec_type` below are low-level composed-spec infrastructure
    // (the post-composition analog of `SdfAbstractData::HasSpec` /
    // `GetSpecType`), shared by the composed handles and the stage's own status
    // queries. The public, C++-shaped scene queries live on the handles:
    // children / property names on `Prim` (`GetChildren` / `GetPropertyNames`),
    // targets / connections on `Relationship` / `Attribute` (`GetTargets` /
    // `GetConnections`). The handles reach the cache through [`Self::cache`]
    // and [`Self::masked`], with population filtering supplied by
    // [`Self::filter_child_names`] and [`Self::mask`].

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    pub(crate) fn has_spec(&self, path: impl Into<sdf::Path>) -> Result<bool> {
        let path = path.into();
        if !self.mask_includes(&path.prim_path()) {
            return Ok(false);
        }
        self.with_cache(|g, c| c.has_spec(g, &path))
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub(crate) fn spec_type(&self, path: impl Into<sdf::Path>) -> Result<Option<sdf::SpecType>> {
        let path = path.into();
        if !self.mask_includes(&path.prim_path()) {
            return Ok(None);
        }
        self.with_cache(|g, c| c.spec_type(g, &path))
    }

    /// Resolves a composed field value by walking the prim index from strongest
    /// to weakest. This is the crate-internal composed-field primitive — the
    /// post-composition analog of `SdfLayer::GetField` / `SdfAbstractData::Get`,
    /// not a `UsdStage` API (C++ has no `UsdStage::GetField`). Public reads go
    /// through the typed handle accessors ([`Attribute::get`], the `Prim::*`
    /// accessors, and the `Stage::*` accessors), which delegate here.
    ///
    /// For prim paths, walks the prim index nodes. For property paths (containing
    /// a `.`), uses the owning prim's index to determine layer order, then queries
    /// the property spec directly in each layer.
    ///
    /// Returns the first (strongest) opinion found, or `None` if no layer
    /// provides a value. A [`sdf::Value::ValueBlock`] explicitly blocks opinions
    /// from weaker layers and causes `None` to be returned.
    ///
    /// The return type is generic: use `sdf::Value` to get the raw enum, or a
    /// concrete type (e.g. `bool`, `f64`, `String`) to convert automatically
    /// via [`TryFrom<sdf::Value>`].
    ///
    /// Accepts both [`sdf::FieldKey`] and `&str` as the field name.
    ///
    /// [`Attribute::get`]: super::Attribute::get
    pub(crate) fn field<T>(&self, path: impl Into<sdf::Path>, field: impl AsRef<str>) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        let path = path.into();
        if !self.mask_includes(&path.prim_path()) {
            return Ok(None);
        }
        let raw = self.with_cache(|g, c| c.resolve_field(g, &path, field.as_ref()))?;
        match raw {
            Some(value) => Ok(Some(T::try_from(value)?)),
            None => Ok(None),
        }
    }

    /// Runs a composed query at `path` under the population mask: when the
    /// path's owning prim is outside the working set, resolves to `T::default()`
    /// without touching the cache; otherwise runs `query` with a short mutable
    /// cache borrow. This is the mask-gated query runner the composed handles
    /// ([`Prim`](super::Prim) / [`Attribute`](super::Attribute) /
    /// [`Relationship`](super::Relationship)) build their scene queries on.
    pub(crate) fn masked<T: Default>(
        &self,
        path: &sdf::Path,
        query: impl FnOnce(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T>,
    ) -> Result<T> {
        if !self.mask_includes(&path.prim_path()) {
            return Ok(T::default());
        }
        self.with_cache(query)
    }

    /// Whether `prim` is exposed by the population mask, accounting for
    /// prototype content (spec 11.3.3). A `/__Prototype_N[/...]` path carries no
    /// instance of its own and is never named in a user mask, so it is included
    /// when any instance sharing that prototype is in the mask — mirroring C++,
    /// where a prototype is populated iff at least one of its instances is.
    /// Ordinary paths defer to [`StagePopulationMask::includes`]; instance
    /// proxies are in their instance's namespace and so are covered by the
    /// instance's own mask entry.
    pub(crate) fn mask_includes(&self, prim: &sdf::Path) -> bool {
        if self.population_mask.includes(prim) {
            return true;
        }
        let cache = self.cache();
        match cache.prototype_root_of(prim) {
            Some(root) => cache
                .prototype_instances(&root)
                .iter()
                .any(|instance| self.population_mask.includes(instance)),
            None => false,
        }
    }

    /// Returns a handle to a prim's composition index (C++
    /// `UsdPrim::GetPrimIndex`). The handle is a cheap `(stage, path)` value;
    /// each of its queries borrows the cache briefly, so it can be held and
    /// reused freely.
    pub fn prim_index(&self, prim: impl Into<sdf::Path>) -> super::PrimIndexRef {
        super::PrimIndexRef::new(self, prim.into())
    }

    /// Resolves a layer id — as carried by a composition
    /// [`Node`](pcp::Node) (`layer_id`, `layer_stack`) — to its identifier.
    /// Unlike [`Self::layer_stack`], this covers every loaded layer, including
    /// those reached across reference/payload arcs.
    pub fn layer_identifier(&self, id: pcp::LayerId) -> Option<String> {
        let layers = self.layers();
        layers.contains(id).then(|| layers.identifier(id).to_string())
    }

    /// Returns the root layer's `customLayerData` dictionary, if authored.
    /// Mirrors C++ `UsdStage::GetRootLayer()->GetCustomLayerData()`: layer
    /// metadata is read from the root layer alone, not composed across the
    /// layer stack.
    pub fn custom_layer_data(&self) -> Result<Option<sdf::Value>> {
        self.field::<sdf::Value>(sdf::Path::abs_root(), sdf::FieldKey::CustomLayerData)
    }

    /// Returns every registered prototype root (`/__Prototype_N`) with at least
    /// one instance inside the population mask.
    pub fn prototypes(&self) -> Vec<sdf::Path> {
        let mask = &self.population_mask;
        let cache = self.cache();
        cache
            .prototypes()
            .into_iter()
            .filter(|root| cache.instances_of(root).iter().any(|instance| mask.includes(instance)))
            .collect()
    }

    /// Returns the resolved stage status bits for a prim.
    pub fn prim_status(&self, prim: impl Into<sdf::Path>) -> Result<PrimStatus> {
        self.prim_status_masked(&prim.into().prim_path(), PrimStatus::all())
    }

    /// Computes only the status bits set in `mask`. Bits outside `mask` are
    /// left unset. Used by traversal so unused checks (e.g. INSTANCE, MODEL
    /// for default traversal) are skipped.
    fn prim_status_masked(&self, prim: &sdf::Path, mask: PrimStatus) -> Result<PrimStatus> {
        let prim = self.prim(prim.clone());
        let mut status = PrimStatus::empty();
        if mask.contains(PrimStatus::ACTIVE) {
            status.set(PrimStatus::ACTIVE, prim.is_active()?);
        }
        if mask.contains(PrimStatus::LOADED) {
            status.set(PrimStatus::LOADED, prim.is_loaded()?);
        }
        if mask.contains(PrimStatus::DEFINED) {
            status.set(PrimStatus::DEFINED, prim.is_defined()?);
        }
        if mask.contains(PrimStatus::ABSTRACT) {
            status.set(PrimStatus::ABSTRACT, prim.is_abstract()?);
        }
        if mask.contains(PrimStatus::INSTANCE) {
            status.set(PrimStatus::INSTANCE, prim.is_instance()?);
        }
        if mask.contains(PrimStatus::MODEL) {
            status.set(PrimStatus::MODEL, prim.is_model()?);
        }
        if mask.contains(PrimStatus::IN_PROTOTYPE) {
            status.set(PrimStatus::IN_PROTOTYPE, prim.is_in_prototype());
        }
        Ok(status)
    }

    /// Filters a child-name list to the prims the population mask includes.
    /// Population-mask infrastructure shared by [`Prim::children`](super::Prim::children)
    /// and the stage's own [`traverse`](Self::traverse) walk. Prototype children
    /// are gated through [`Self::mask_includes`], so a prototype populated by a
    /// masked instance stays traversable (spec 11.3.3).
    pub(crate) fn filter_child_names(&self, parent: &sdf::Path, children: Vec<Token>) -> Vec<Token> {
        if self.population_mask.is_all() {
            return children;
        }
        children
            .into_iter()
            .filter(|name| {
                parent
                    .append_path(name.as_str())
                    .is_ok_and(|child| self.mask_includes(&child))
            })
            .collect()
    }

    /// Iterates the prim path and its ancestors from leaf to root, stopping
    /// before the pseudo-root. Assumes `start` is already a prim path.
    pub(crate) fn prim_ancestors_inclusive(start: sdf::Path) -> impl Iterator<Item = sdf::Path> {
        std::iter::successors(Some(start), sdf::Path::parent).take_while(|p| *p != sdf::Path::abs_root())
    }

    /// Borrows the stage's composition cache.
    pub(crate) fn cache(&self) -> Ref<'_, pcp::IndexCache> {
        self.cache.borrow()
    }

    /// Inserts `layer` as a sublayer of `parent` at `pos`. `parent` is matched
    /// by its canonical identifier.
    ///
    /// `parent`'s `subLayers` / `subLayerOffsets` metadata is the single source
    /// of truth: this authors `layer`'s identifier and `offset` there, then
    /// rebuilds the graph edges and invalidates composition through the same
    /// change pipeline an ordinary `subLayers` edit uses. The sublayer therefore
    /// persists on save.
    ///
    /// Returns [`StageAuthoringError::LayerNotFound`] if `parent` is not in the
    /// stage and [`StageAuthoringError::Layer`] if `parent` is read-only. In
    /// both cases the graph is left untouched — `layer` only joins it once the
    /// parent edit succeeds, so a failed insert never leaves an orphan node.
    ///
    /// Only `layer` itself is added. If `layer` authors its own `subLayers`
    /// naming layers not already loaded in the stage, those nested sublayers are
    /// not auto-collected from disk — their edges resolve to nothing and
    /// contribute no opinions. Insert an already-collected layer (e.g. from a
    /// [`layer::Collector`](crate::layer::Collector)) when nested sublayers must
    /// load.
    //
    // TODO: run the collector on `layer` so its sublayer/reference/payload
    // dependencies load (and unresolved ones surface as `UnresolvedSublayer`),
    // matching what `StageBuilder::open` does for the root layer.
    pub fn insert_sub_layer(
        &self,
        parent: &str,
        pos: usize,
        layer: sdf::Layer,
        offset: sdf::LayerOffset,
    ) -> Result<(), StageAuthoringError> {
        let identifier = layer.identifier().to_string();
        // Author the parent's metadata first; the child node is added only after
        // this succeeds (the authored asset path is a plain string, so the node
        // need not exist yet — only the later rebuild's `find()` needs it).
        let parent_id = {
            let mut layers = self.layers.borrow_mut();
            let parent_id = layers.id_of(parent).ok_or_else(|| StageAuthoringError::LayerNotFound {
                layer: parent.to_string(),
            })?;
            let node = layers.get_mut(parent_id).expect("id_of returned a live id");
            node.layer
                .pseudo_root_mut()
                .map(|mut root| root.insert_sublayer(pos, identifier, offset))
                .map_err(StageAuthoringError::Layer)?;
            parent_id
        };
        self.layers.borrow_mut().ensure_layer(layer);
        self.finalize_layer(parent_id, Ok(()), None)?;
        Ok(())
    }

    /// Removes the sublayer `child` from `parent`'s `subLayers` and its aligned
    /// `subLayerOffsets` entry, then rebuilds the graph edges and invalidates
    /// composition through the change pipeline. `parent` is matched by its
    /// canonical identifier; `child` may be either a canonical identifier (as
    /// returned by [`sub_layers`](Self::sub_layers)) or the as-authored asset
    /// path — both are resolved to the same layer, and the authored `subLayers`
    /// entry pointing at that layer is the one removed, even when the entry is a
    /// relative path that differs from the canonical identifier.
    ///
    /// Returns `Ok(true)` if a sublayer was removed, `Ok(false)` if `child` is
    /// not a sublayer of `parent`, [`StageAuthoringError::LayerNotFound`] if
    /// `parent` is not in the stage, and [`StageAuthoringError::Layer`] if
    /// `parent` is read-only.
    pub fn remove_sub_layer(&self, parent: &str, child: &str) -> Result<bool, StageAuthoringError> {
        let (parent_id, removed) = {
            let mut layers = self.layers.borrow_mut();
            let parent_id = layers.id_of(parent).ok_or_else(|| StageAuthoringError::LayerNotFound {
                layer: parent.to_string(),
            })?;
            // Resolve `child` to a layer id (exact canonical identifier, or an
            // authored asset path), then find the authored `subLayers` entry
            // that resolves to it. The entry string can differ from the
            // canonical id (e.g. a relative path), so an exact string match
            // against the caller's `child` would miss it.
            let authored = layers.id_of(child).or_else(|| layers.find(child)).and_then(|child_id| {
                let subs = layers.get(parent_id)?.layer.pseudo_root()?.sublayers()?.to_vec();
                subs.into_iter()
                    .find(|entry| layers.id_of(entry).or_else(|| layers.find(entry)) == Some(child_id))
            });
            let removed = match authored {
                Some(entry) => {
                    let node = layers.get_mut(parent_id).expect("id_of returned a live id");
                    node.layer
                        .pseudo_root_mut()
                        .map(|mut root| root.remove_sublayer(&entry))
                        .map_err(StageAuthoringError::Layer)?
                }
                None => false,
            };
            (parent_id, removed)
        };
        if removed {
            self.finalize_layer(parent_id, Ok(()), None)?;
        }
        Ok(removed)
    }

    /// Borrows the stage's layer graph.
    pub(crate) fn layers(&self) -> Ref<'_, pcp::LayerGraph> {
        self.layers.borrow()
    }

    /// Runs a composed query that needs both the layer graph and the
    /// composition cache, borrowing each for the call. The layer graph is
    /// borrowed shared and the cache mutably, mirroring how composition reads
    /// layer data through a `&LayerGraph` while lazily building the index.
    pub(crate) fn with_cache<T>(
        &self,
        query: impl FnOnce(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T>,
    ) -> Result<T> {
        let graph = self.layers.borrow();
        let mut cache = self.cache.borrow_mut();
        query(&graph, &mut cache)
    }

    /// Traverses composed prims depth-first, visiting prims that match `predicate`.
    ///
    /// Pass [`PrimPredicate::DEFAULT`] for OpenUSD's usual traversal region
    /// (active, loaded, defined, non-abstract). Descendants are pruned when
    /// inherited status bits make it impossible for them to match, such as below
    /// inactive, unloaded, undefined, or abstract prims when the predicate
    /// excludes those regions.
    pub fn traverse(&self, predicate: PrimPredicate, mut visitor: impl FnMut(&sdf::Path)) -> Result<()> {
        let needed = predicate.consulted_bits();
        let mut stack = vec![sdf::Path::abs_root()];

        while let Some(path) = stack.pop() {
            if path != sdf::Path::abs_root() {
                // TODO(perf): each `prim_status_masked` call recomputes the
                // inherited bits (active/loaded/defined/abstract/model) by
                // walking this prim's ancestor chain to the root, and several
                // predicates re-walk it for the same fields. Since traversal is
                // top-down, the parent's resolved inherited status could be
                // threaded down the stack so each prim only consults its own
                // local opinion — turning the per-prim O(depth) walk into O(1).
                let status = self.prim_status_masked(&path, needed)?;
                if predicate.matches(status) {
                    visitor(&path);
                }
                if predicate.prunes_descendants(status) {
                    continue;
                }
                // Stop at instance prims unless instance proxies are requested;
                // the instance's subtree is the prototype's (spec 11.3.3).
                if !predicate.traverse_instance_proxies && status.contains(PrimStatus::INSTANCE) {
                    continue;
                }
            }

            let names = self.masked(&path, |g, cache| cache.prim_children(g, &path))?;
            let children = self.filter_child_names(&path, names);
            // Push in reverse so first child is visited first.
            for name in children.iter().rev() {
                if let Ok(child) = path.append_path(name.as_str()) {
                    stack.push(child);
                }
            }
        }

        Ok(())
    }
}

/// Apply a [`LayerDiff`] to `layer`: copy every overlay spec, then replay each
/// deletion the overlay cannot carry. The mutating core of
/// [`Stage::apply_diff`], factored out so the borrow of the target layer node
/// is scoped tightly around it.
fn apply_diff_to_layer(layer: &mut sdf::Layer, diff: &LayerDiff) -> Result<()> {
    let src = diff.layer.data();
    for path in src.spec_paths() {
        layer.copy_spec_from(src, &path)?;
    }
    for deletion in &diff.removed {
        match deletion {
            Deletion::Spec(path) => {
                layer.remove_spec(path);
            }
            Deletion::Field(path, field) => layer.data_mut().erase_field(path, field.as_str()),
        }
    }
    Ok(())
}

/// Builder for configuring and opening a [`Stage`].
///
/// Created via [`Stage::builder`]. Allows setting a custom asset resolver and
/// composition options.
pub struct StageBuilder<R: ar::Resolver = ar::DefaultResolver> {
    resolver: R,
    variant_fallbacks: pcp::VariantFallbackMap,
    session_layer: Option<String>,
    initial_load_set: InitialLoadSet,
    population_mask: StagePopulationMask,
    interpolation_type: InterpolationType,
}

#[derive(Default)]
struct CollectedLayers {
    layers: Vec<sdf::Layer>,
    errors: Vec<pcp::Error>,
}

impl StageBuilder {
    fn new() -> Self {
        Self {
            resolver: ar::DefaultResolver::new(),
            variant_fallbacks: pcp::VariantFallbackMap::new(),
            session_layer: None,
            initial_load_set: InitialLoadSet::LoadAll,
            population_mask: StagePopulationMask::all(),
            interpolation_type: InterpolationType::default(),
        }
    }
}

impl<R: ar::Resolver> StageBuilder<R> {
    /// Sets a custom asset resolver.
    pub fn resolver<R2: ar::Resolver>(self, resolver: R2) -> StageBuilder<R2> {
        StageBuilder {
            resolver,
            variant_fallbacks: self.variant_fallbacks,
            session_layer: self.session_layer,
            initial_load_set: self.initial_load_set,
            population_mask: self.population_mask,
            interpolation_type: self.interpolation_type,
        }
    }

    /// Sets the stage-level interpolation mode for time-sampled
    /// attribute queries through [`Attribute::get`](super::Attribute::get).
    /// Default per AOUSD §12.5 is [`InterpolationType::Linear`].
    pub fn interpolation_type(mut self, mode: InterpolationType) -> Self {
        self.interpolation_type = mode;
        self
    }

    /// Sets the session layer for the stage.
    ///
    /// The session layer provides the strongest opinions in the composition,
    /// stronger than even the root layer. It is typically used for temporary,
    /// non-persistent overrides such as variant selections, visibility toggles,
    /// or LOD settings.
    ///
    /// The session layer and its sublayers are collected and prepended to the
    /// layer stack before the root layer.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::usd;
    ///
    /// let stage = usd::Stage::builder()
    ///     .session_layer("session.usda")
    ///     .open("scene.usda")
    ///     .unwrap();
    ///
    /// assert!(stage.has_session_layer());
    /// ```
    pub fn session_layer(mut self, path: impl Into<String>) -> Self {
        self.session_layer = Some(path.into());
        self
    }

    /// Sets the variant fallback map for the stage.
    ///
    /// When a prim has a variant set but no authored selection, the
    /// composition engine tries each fallback in order. The first fallback
    /// matching an existing variant in the set is used; if none match, the
    /// first variant in the set is used as default.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::usd;
    /// use openusd::pcp::VariantFallbackMap;
    ///
    /// let fallbacks = VariantFallbackMap::new()
    ///     .add("shadingComplexity", ["full", "simple"]);
    ///
    /// let stage = usd::Stage::builder()
    ///     .variant_fallbacks(fallbacks)
    ///     .open("scene.usda")
    ///     .unwrap();
    /// ```
    pub fn variant_fallbacks(mut self, fallbacks: pcp::VariantFallbackMap) -> Self {
        self.variant_fallbacks = fallbacks;
        self
    }

    /// Sets the initial payload loading behavior.
    pub fn load(mut self, load_set: InitialLoadSet) -> Self {
        self.initial_load_set = load_set;
        self
    }

    /// Sets the stage population mask.
    pub fn mask(mut self, mask: StagePopulationMask) -> Self {
        self.population_mask = mask;
        self
    }

    /// Opens a stage from a root layer file.
    ///
    /// Session layers (if any) are prepended at the front of the layer stack
    /// so they hold the strongest opinions.
    pub fn open(self, root_path: &str) -> Result<Stage>
    where
        R: 'static,
    {
        let session = self.collect_optional_session_layers()?;
        let root = self.collect_layers(root_path)?;
        let session_layer_count = session.layers.len();
        let layers = session.layers.into_iter().chain(root.layers).collect();
        let errors = session.errors.into_iter().chain(root.errors).collect();
        Ok(self.make_stage(layers, session_layer_count, errors))
    }

    /// Create an in-memory stage backed by a single writable anonymous root
    /// layer. Mirrors C++ `UsdStage::CreateInMemory`.
    ///
    /// If a session layer was configured on the builder, it is loaded from
    /// disk and prepended just like in [`StageBuilder::open`].
    ///
    /// # Example
    ///
    /// ```
    /// use openusd::usd;
    ///
    /// let stage = usd::Stage::builder()
    ///     .in_memory("anon.usda")
    ///     .unwrap();
    /// stage.define_prim("/World").unwrap().set_type_name("Xform").unwrap();
    /// ```
    pub fn in_memory(self, identifier: impl Into<String>) -> Result<Stage>
    where
        R: 'static,
    {
        let identifier = identifier.into();
        let session = self.collect_optional_session_layers()?;
        let session_layer_count = session.layers.len();
        let layers: Vec<sdf::Layer> = session
            .layers
            .into_iter()
            .chain(std::iter::once(sdf::Layer::new_anonymous(identifier)))
            .collect();
        Ok(self.make_stage(layers, session_layer_count, session.errors))
    }

    /// Collect layers reachable from `path`, honoring the builder's resolver,
    /// payload-loading flag, and population mask.
    fn collect_layers(&self, path: &str) -> Result<CollectedLayers> {
        let include_prim_dependency = |p: &sdf::Path| self.population_mask.includes(p);
        let errors = RefCell::new(Vec::new());
        let layers = {
            let collector = layer::Collector::new(&self.resolver)
                .load_payloads(self.initial_load_set.load_payloads())
                .on_error(|error| {
                    if let layer::Error::UnresolvedAsset {
                        asset_path,
                        referencing_layer,
                        kind: layer::DependencyKind::SubLayer,
                        ..
                    } = error
                    {
                        errors.borrow_mut().push(pcp::Error::UnresolvedSublayer {
                            asset_path,
                            introduced_by: referencing_layer,
                        });
                    }
                    Ok(())
                });
            if self.population_mask.is_all() {
                collector.collect(path)
            } else {
                collector.prim_dependency_filter(&include_prim_dependency).collect(path)
            }
        }?;
        Ok(CollectedLayers {
            layers,
            errors: errors.into_inner(),
        })
    }

    /// Collect the configured session layer (and its dependencies), if any.
    fn collect_optional_session_layers(&self) -> Result<CollectedLayers> {
        match self.session_layer.as_deref() {
            Some(p) => self.collect_layers(p),
            None => Ok(CollectedLayers::default()),
        }
    }

    /// Assemble a [`Stage`] from already-collected layers. Shared
    /// construction tail for [`StageBuilder::open`] and
    /// [`StageBuilder::in_memory`]; any new `Stage` field must be wired in
    /// here once.
    fn make_stage(
        self,
        layers: Vec<sdf::Layer>,
        session_layer_count: usize,
        collection_errors: Vec<pcp::Error>,
    ) -> Stage
    where
        R: 'static,
    {
        let load_payloads = self.initial_load_set.load_payloads();
        // The graph keeps its own regenerable diagnostics (sublayer cycles,
        // invalid relocates); the cache holds only the one-shot collection
        // errors. `Stage::composition_errors` concatenates the two.
        let graph = pcp::LayerGraph::from_layers(layers, session_layer_count, Box::new(self.resolver), load_payloads);
        let layer_stack_id = graph.layer_stack_id();
        // The root layer is the strongest authoring target by default; an
        // empty graph (no layers) has none, so the target names no layer and
        // resolves to nothing at author time. Tagged with the stack identity so
        // it matches [`Stage::edit_target_root`].
        let edit_target = EditTarget {
            layer_stack: Some(layer_stack_id.clone()),
            ..EditTarget::for_layer(graph.root_layer().map(sdf::Layer::identifier).unwrap_or_default())
        };
        Stage(Rc::new(StageInner {
            layers: RefCell::new(graph),
            cache: RefCell::new(pcp::IndexCache::new(self.variant_fallbacks, collection_errors)),
            muted: RefCell::new(std::collections::HashSet::new()),
            initial_load_set: self.initial_load_set,
            population_mask: self.population_mask,
            interpolation_type: Cell::new(self.interpolation_type),
            edit_target: RefCell::new(edit_target),
            layer_stack_id,
            change_scratch: RefCell::new(sdf::ChangeList::new()),
            listener: RefCell::new(None),
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const VENDOR_COMPOSITION: &str = "vendor/usd-wg-assets/test_assets/foundation/stage_composition";

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    fn composition_path(relative: &str) -> String {
        format!("{}/{VENDOR_COMPOSITION}/{relative}", manifest_dir())
    }

    /// The resolver's identity is the resolver component of the stack identity:
    /// two stages opened from the same root under resolvers with different
    /// search paths reject each other's edit targets; an identical config
    /// accepts.
    #[test]
    fn layer_stack_id_keys_on_resolver() -> Result<()> {
        let path = composition_path("active.usda");
        let open_with = |dir: &str| {
            Stage::builder()
                .resolver(ar::DefaultResolver::with_search_paths([dir]))
                .open(&path)
        };
        let stage_a = open_with("/assets/a")?;
        let stage_b = open_with("/assets/b")?;
        assert!(matches!(
            stage_b.set_edit_target(stage_a.edit_target_root()),
            Err(StageAuthoringError::EditTargetWrongStage)
        ));

        let stage_c = open_with("/assets/a")?;
        assert!(stage_c.set_edit_target(stage_a.edit_target_root()).is_ok());
        Ok(())
    }

    /// Querying a field that isn't authored should return None.
    #[test]
    fn field_not_authored() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let active = stage.field::<sdf::Value>("/World", sdf::FieldKey::Active)?;
        assert_eq!(active, None);

        Ok(())
    }

    #[test]
    fn remove_connection_deletes_inherited() -> Result<()> {
        let target = sdf::Path::new("/Mat.outputs:out")?;
        let input = sdf::Path::new("/Mat.inputs:in")?;

        let mut strong = sdf::Layer::new_in_memory("root.usda");
        strong.pseudo_root_mut()?.set_sublayers(["weak.usda"]);

        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        sdf::PrimSpec::new(weak.data_mut(), "/Mat", sdf::Specifier::Def, "Shader")?;
        sdf::AttributeSpec::new(
            weak.data_mut(),
            "/Mat.outputs:out",
            "color3f",
            sdf::Variability::Varying,
            true,
        )?;
        sdf::AttributeSpec::new(
            weak.data_mut(),
            "/Mat.inputs:in",
            "color3f",
            sdf::Variability::Varying,
            true,
        )?
        .set_connection_paths([target.clone()]);

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, Vec::new());
        let attr = crate::usd::Attribute::new(&stage, input.clone());

        assert_eq!(attr.connections()?, vec![target.clone()]);
        assert!(attr.remove_connection(&target)?);
        assert!(attr.connections()?.is_empty());

        let op = stage
            .field::<sdf::Value>(&input, sdf::FieldKey::ConnectionPaths)?
            .unwrap()
            .try_as_path_list_op()
            .unwrap();
        assert_eq!(op.deleted_items, vec![target]);
        Ok(())
    }

    #[test]
    fn add_connection_dedups_inherited() -> Result<()> {
        let target = sdf::Path::new("/Mat.outputs:out")?;
        let input = sdf::Path::new("/Mat.inputs:in")?;

        let mut strong = sdf::Layer::new_in_memory("root.usda");
        strong.pseudo_root_mut()?.set_sublayers(["weak.usda"]);

        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        sdf::PrimSpec::new(weak.data_mut(), "/Mat", sdf::Specifier::Def, "Shader")?;
        sdf::AttributeSpec::new(
            weak.data_mut(),
            "/Mat.outputs:out",
            "color3f",
            sdf::Variability::Varying,
            true,
        )?;
        sdf::AttributeSpec::new(
            weak.data_mut(),
            "/Mat.inputs:in",
            "color3f",
            sdf::Variability::Varying,
            true,
        )?
        .set_connection_paths([target.clone()]);

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, Vec::new());
        let attr = crate::usd::Attribute::new(&stage, input.clone());
        let attr = attr.add_connection(target.clone())?;

        assert_eq!(attr.connections()?, vec![target.clone()]);
        let op = stage
            .field::<sdf::Value>(&input, sdf::FieldKey::ConnectionPaths)?
            .unwrap()
            .try_as_path_list_op()
            .unwrap();
        assert!(op.explicit, "add_connection should not author a duplicate local op");
        assert_eq!(op.explicit_items, vec![target]);
        Ok(())
    }

    #[test]
    fn add_connection_clears_delete() -> Result<()> {
        let target = sdf::Path::new("/Mat.outputs:out")?;
        let input = sdf::Path::new("/Mat.inputs:in")?;

        let mut strong = sdf::Layer::new_in_memory("root.usda");
        strong.pseudo_root_mut()?.set_sublayers(["weak.usda"]);

        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        sdf::PrimSpec::new(weak.data_mut(), "/Mat", sdf::Specifier::Def, "Shader")?;
        sdf::AttributeSpec::new(
            weak.data_mut(),
            "/Mat.outputs:out",
            "color3f",
            sdf::Variability::Varying,
            true,
        )?;
        sdf::AttributeSpec::new(
            weak.data_mut(),
            "/Mat.inputs:in",
            "color3f",
            sdf::Variability::Varying,
            true,
        )?
        .set_connection_paths([target.clone()]);

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, Vec::new());
        let attr = crate::usd::Attribute::new(&stage, input.clone());

        assert!(attr.remove_connection(&target)?);
        assert!(attr.connections()?.is_empty());
        let attr = attr.add_connection(target.clone())?;

        assert_eq!(attr.connections()?, vec![target.clone()]);
        let op = stage
            .field::<sdf::Value>(&input, sdf::FieldKey::ConnectionPaths)?
            .unwrap()
            .try_as_path_list_op()
            .unwrap();
        assert!(op.deleted_items.is_empty());
        assert_eq!(op.prepended_items, vec![target]);
        Ok(())
    }

    fn in_memory_stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    /// Authoring a child prim under a variant edit target lands the spec at
    /// the `{set=sel}` path in the target layer.
    #[test]
    fn variant_target_routes_child() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.edit_target().layer_identifier().to_string();
        stage.define_prim("/Prim")?;
        stage.set_edit_target(EditTarget::for_local_direct_variant(
            root.clone(),
            sdf::path("/Prim{set=sel}")?,
        ))?;
        stage.define_prim("/Prim/child")?;

        let landed = {
            let layers = stage.layers();
            let root_id = layers.id_of(&root).unwrap();
            layers
                .layer(root_id)
                .data()
                .spec_type(&sdf::path("/Prim{set=sel}child")?)
        };
        assert_eq!(landed, Some(sdf::SpecType::Prim));
        Ok(())
    }

    /// A property authored under a variant edit target carries its `.attr`
    /// suffix into the `{set=sel}` namespace.
    #[test]
    fn variant_target_routes_property() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.edit_target().layer_identifier().to_string();
        stage.define_prim("/Prim")?;
        stage.set_edit_target(EditTarget::for_local_direct_variant(
            root.clone(),
            sdf::path("/Prim{set=sel}")?,
        ))?;
        stage.create_attribute("/Prim.size", "double")?;

        let landed = {
            let layers = stage.layers();
            let root_id = layers.id_of(&root).unwrap();
            layers
                .layer(root_id)
                .data()
                .spec_type(&sdf::path("/Prim{set=sel}.size")?)
        };
        assert_eq!(landed, Some(sdf::SpecType::Attribute));
        Ok(())
    }

    /// A weak sublayer carrying one opinion, for the sublayer-mutation tests.
    /// Uses a verbatim identifier so an authored `subLayers` entry naming it
    /// resolves by exact or suffix match.
    fn opinion_layer(identifier: &str, value: f64) -> Result<sdf::Layer> {
        let mut layer = sdf::Layer::new_in_memory(identifier);
        sdf::AttributeSpec::new(layer.data_mut(), "/A.x", "double", sdf::Variability::Varying, true)?
            .set_default(sdf::Value::Double(value));
        Ok(layer)
    }

    /// The parent layer's authored `subLayers` asset paths.
    fn authored_sublayers(stage: &Stage) -> Vec<String> {
        let root = stage.root_layer();
        root.pseudo_root().and_then(|pr| pr.sublayers()).unwrap_or_default()
    }

    /// `ensure_layer` must not clobber an already-loaded node: re-inserting a
    /// layer whose identifier is already in the graph keeps the existing node's
    /// data (and therefore its derived sublayer children), not the fresh empty
    /// layer passed in. Anonymous layers are unique, so the colliding identifier
    /// is fabricated with [`sdf::Layer::new_in_memory`].
    #[test]
    fn insert_sub_layer_keeps_loaded_node() -> Result<()> {
        // Build root → mid → leaf incrementally so `mid` is a loaded node with a
        // derived child edge to `leaf`, and `leaf`'s opinion composes.
        let stage = Stage::builder().in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        let mid = sdf::Layer::new_in_memory("mid.usda");
        let mid_id = mid.identifier().to_string();
        stage.insert_sub_layer(&root_id, 0, mid, sdf::LayerOffset::IDENTITY)?;
        stage.insert_sub_layer(&mid_id, 0, opinion_layer("leaf.usda", 5.0)?, sdf::LayerOffset::IDENTITY)?;
        assert_eq!(
            stage
                .attribute("/A.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(5.0))
        );

        // Re-insert `mid` by its identifier, passing a fresh empty layer with the
        // same identifier. The graph must keep the loaded `mid` (whose
        // `subLayers` still names `leaf`), so `leaf`'s opinion survives.
        stage.insert_sub_layer(
            &root_id,
            0,
            sdf::Layer::new_in_memory(&mid_id),
            sdf::LayerOffset::IDENTITY,
        )?;
        assert_eq!(
            stage
                .attribute("/A.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(5.0)),
            "the already-loaded mid layer's child edge to leaf must survive re-insertion"
        );
        Ok(())
    }

    /// `remove_sub_layer` resolves `child` to a layer before matching, so a
    /// sublayer authored with a relative path (whose canonical identifier
    /// differs from the authored entry) is still removed when named by the
    /// canonical identifier `sub_layers` returns.
    #[test]
    fn remove_sub_layer_resolves_relative() -> Result<()> {
        // root authors `subLayers = ["sub.usda"]`, but the child layer's
        // canonical identifier is `dir/sub.usda` (find() resolves the relative
        // entry to it by suffix).
        let mut root = sdf::Layer::new_in_memory("root.usda");
        root.pseudo_root_mut()?.set_sublayers(["sub.usda"]);
        let child = opinion_layer("dir/sub.usda", 5.0)?;
        let stage = Stage::builder().make_stage(vec![root, child], 0, Vec::new());
        assert_eq!(
            stage
                .attribute("/A.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(5.0))
        );

        // sub_layers reports the canonical identifier, not the authored string.
        let canonical = stage.sub_layers("root.usda");
        assert!(canonical.iter().any(|id| id == "dir/sub.usda"));

        // Removing by that canonical identifier must still drop the relative
        // `sub.usda` entry (exact-string matching would have missed it).
        assert!(
            stage.remove_sub_layer("root.usda", "dir/sub.usda")?,
            "the relative sublayer is removed when named by canonical identifier"
        );
        assert_eq!(
            stage
                .attribute("/A.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            None,
            "the removed sublayer's opinion is gone"
        );
        assert!(
            authored_sublayers(&stage).is_empty(),
            "the authored subLayers entry is gone"
        );
        Ok(())
    }

    /// The stage time-code range round-trips through the root layer and reports
    /// the documented unauthored defaults beforehand.
    #[test]
    fn stage_time_code_range() -> Result<()> {
        let stage = in_memory_stage()?;
        assert_eq!(stage.start_time_code(), 0.0);
        assert_eq!(stage.end_time_code(), 0.0);
        assert!(!stage.has_authored_time_code_range());

        stage.set_start_time_code(1.0)?;
        stage.set_end_time_code(48.0)?;

        assert_eq!(stage.start_time_code(), 1.0);
        assert_eq!(stage.end_time_code(), 48.0);
        assert_eq!(stage.root_layer().start_time_code(), 1.0);
        assert!(stage.has_authored_time_code_range());
        Ok(())
    }

    /// `time_codes_per_second` falls back to the authored `framesPerSecond`,
    /// then to `24.0`, when no `timeCodesPerSecond` opinion exists.
    #[test]
    fn stage_tcps_fps_fallback() -> Result<()> {
        let stage = in_memory_stage()?;
        assert_eq!(stage.time_codes_per_second(), 24.0);
        assert_eq!(stage.frames_per_second(), 24.0);

        stage.set_frames_per_second(30.0)?;
        assert_eq!(stage.time_codes_per_second(), 30.0);

        stage.set_time_codes_per_second(48.0)?;
        assert_eq!(stage.time_codes_per_second(), 48.0);
        Ok(())
    }

    /// `has_authored_time_code_range` requires both endpoints; one alone is
    /// not a range.
    #[test]
    fn authored_time_code_range() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.set_start_time_code(0.0)?;
        assert!(!stage.has_authored_time_code_range());
        stage.set_end_time_code(10.0)?;
        assert!(stage.has_authored_time_code_range());
        Ok(())
    }

    /// Stage metadata resolves only from the root and session layers, so the
    /// time-code setters reject an edit target on any other layer (a sublayer
    /// here) and author successfully once it is back on the root.
    #[test]
    fn time_code_target_rejects() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.root_layer().identifier().to_string();
        let sub = sdf::Layer::new_anonymous("sub.usda");
        let sub_id = sub.identifier().to_string();
        stage.insert_sub_layer(&root, 0, sub, sdf::LayerOffset::IDENTITY)?;

        stage.set_edit_target(EditTarget::for_layer(sub_id.clone()))?;
        let err = stage
            .set_start_time_code(1.0)
            .expect_err("sublayer target must be rejected");
        assert!(matches!(err, StageAuthoringError::StageMetadataTarget { layer } if layer == sub_id));

        stage.set_edit_target(EditTarget::for_layer(root))?;
        stage.set_start_time_code(1.0)?;
        assert_eq!(stage.start_time_code(), 1.0);
        Ok(())
    }

    /// `extract_diff` routes a whole-spec removal into `removed`, keeping it out
    /// of the overlay layer, while a spec that still exists is copied. Driven
    /// with a synthetic notice and a direct `erase_spec` to unit-test the
    /// routing in isolation; the end-to-end `remove_prim` / `apply_diff` path is
    /// covered in `tests/stage.rs`.
    #[test]
    fn extract_diff_removal() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/World")?;
        stage.create_attribute("/World.size", "double")?;
        let size = sdf::path("/World.size")?;
        let root = stage.root_layer().identifier().to_string();
        // Actually remove the spec, as a real removal edit would, so it is gone
        // from the layer when the notice is processed.
        {
            let mut layers = stage.layers.borrow_mut();
            let root_id = layers.root_id().expect("root layer");
            layers
                .get_mut(root_id)
                .expect("root layer node")
                .layer
                .data_mut()
                .erase_spec(&size);
        }
        let mut change_list = sdf::ChangeList::new();
        change_list.entry_mut(&size).flags |= sdf::ChangeFlags::REMOVE_PROPERTY;
        let objects = ObjectsChanged {
            resynced: &[],
            changed_info_only: std::slice::from_ref(&size),
            layer_identifier: &root,
            change_list: &change_list,
            mapping: None,
        };
        let diff = stage.extract_diff(&objects)?;
        assert_eq!(diff.removed, vec![Deletion::Spec(size.clone())]);
        assert_eq!(diff.layer.data().spec_type(&size), None);
        Ok(())
    }
}
