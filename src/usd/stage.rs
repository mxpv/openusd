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

use std::cell::{Cell, Ref, RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::mem;
use std::rc::{Rc, Weak};

use anyhow::Result;
use bitflags::bitflags;

use crate::tf::Token;
use crate::{ar, pcp, sdf};

use super::interp::{self, InterpolationType};
use super::sink::{Payload, PendingChange, Provenance, StageSink, StageSinkId};

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

/// How deeply a [`Stage::load`] call expands payloads. Mirrors C++
/// `UsdLoadPolicy`.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum LoadPolicy {
    /// Load the requested prim, its ancestors, and every descendant payload
    /// recursively. C++ `UsdLoadWithDescendants`.
    #[default]
    WithDescendants,
    /// Load only the requested prim (and its ancestors); a descendant with
    /// no rule of its own is excluded. C++ `UsdLoadWithoutDescendants`.
    WithoutDescendants,
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
    /// The layer stack this target authors into, captured from the target node
    /// when known ([`edit_target_for_node`](Stage::edit_target_for_node)), or
    /// `None` for a target whose stack the namespace editor infers from layer
    /// membership ([`for_layer`](Self::for_layer) /
    /// [`for_local_direct_variant`](Self::for_local_direct_variant)). An arc
    /// target records it so a relocate synthesized for it lands in the right
    /// stack even when the referenced asset is also a root sublayer — a case
    /// membership alone cannot disambiguate.
    authoring_stack: Option<AuthoringStack>,
}

/// The layer stack an [`EditTarget`] authors into, captured at construction.
/// Distinguishes the stage root stack from a referenced asset's sublayer stack
/// so the namespace editor seeds and authors relocates in the correct stack
/// rather than re-inferring it from which stacks a layer happens to belong to.
#[derive(Debug, Clone, PartialEq)]
enum AuthoringStack {
    /// The stage root layer stack.
    Root,
    /// A referenced asset's sublayer stack (boxed to keep the enum small). The
    /// context is kept so the namespace editor reconstructs the same
    /// context-resolved stack rather than the plain one, whose members can differ.
    Referenced(Box<ReferencedStack>),
}

/// A referenced asset's sublayer stack an [`EditTarget`] authors into, rooted at
/// the layer with `root`'s canonical identifier and resolved under `expr_vars` —
/// the expression variables inherited across the arc (empty for a plain stack, the
/// `${VAR}` context for a contextual one).
#[derive(Debug, Clone, PartialEq)]
struct ReferencedStack {
    root: String,
    expr_vars: HashMap<String, sdf::Value>,
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
            authoring_stack: None,
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
            authoring_stack: None,
        }
    }

    /// The identifier of the layer this target writes to.
    pub fn layer_identifier(&self) -> &str {
        &self.layer_identifier
    }

    /// The namespace mapping this target translates through — layer (spec)
    /// namespace to stage (scene) namespace, with the arc's composed time
    /// offset (C++ `UsdEditTarget::GetMapFunction`).
    pub fn map_function(&self) -> &pcp::MapFunction {
        &self.mapping
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
                let mapped_target = self.map_to_spec_target_path(&target)?;
                mapped.replace_embedded_target(&mapped_target)
            }
        }
    }

    /// Maps a target-valued path — a relationship target, attribute
    /// connection, inherit, or specialize — from scene namespace into this
    /// target's layer namespace. Target paths never carry variant selections,
    /// so the mapped result is stripped of them; under a variant target this
    /// maps a path to itself. `None` when the path falls outside the mapping's
    /// co-domain.
    pub(super) fn map_to_spec_target_path(&self, scene_path: &sdf::Path) -> Option<sdf::Path> {
        Some(
            self.mapping
                .map_target_to_source(scene_path)?
                .strip_all_variant_selections(),
        )
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
                authoring_stack: None,
            };
        }
        EditTarget {
            layer_identifier: self.layer_identifier.clone(),
            mapping: weaker.mapping.compose(&self.mapping),
            layer_stack: self.layer_stack.clone().or_else(|| weaker.layer_stack.clone()),
            // A refinement (a variant) over an arc inherits the arc's authoring
            // stack: the deeper target's stack when it has one, else the weaker's.
            authoring_stack: self.authoring_stack.clone().or_else(|| weaker.authoring_stack.clone()),
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

    /// A [`sdf::LayerSink`] rejected the staged edit from its
    /// [`before_commit`](sdf::LayerSink::before_commit), so the whole edit rolled
    /// back.
    #[error(transparent)]
    Rejected(#[from] sdf::sink::Error),

    /// A composed-stage query needed to route or validate the authoring call failed.
    #[error(transparent)]
    Composition(#[from] anyhow::Error),

    /// The named layer is not present in this stage's layer graph.
    #[error("layer {layer:?} is not in the stage")]
    LayerNotFound {
        /// The offending layer's identifier.
        layer: String,
    },

    /// A [`Stage::batch_edit`] named the same layer more than once. Each layer in
    /// a batch is opened with a single mutable edit view, so a repeat would alias
    /// it.
    #[error("layer {layer:?} appears more than once in the batch")]
    DuplicateLayer {
        /// The repeated layer's identifier.
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
    /// carries an identity catch-all), so this arises for arc-based targets
    /// with a restricted domain — authoring a path the arc does not reach, or
    /// replaying a [`Diff`](super::Diff) one of whose paths the target cannot express.
    #[error("path {path} is outside the current edit target")]
    OutsideEditTarget {
        /// The path that could not be mapped, in the namespace it was
        /// presented in (composed stage namespace, or the diff's own layer
        /// namespace for [`Stage::apply_diff`]).
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
}

impl From<sdf::EditError> for StageAuthoringError {
    fn from(error: sdf::EditError) -> Self {
        match error {
            sdf::EditError::Author(e) => Self::Layer(e),
            sdf::EditError::Rejected(e) => Self::Rejected(e),
        }
    }
}

/// One committed layer edit queued in [`StageInner::pending`]: the transaction id
/// it committed under (for grouping the drain), the edited layer, its change
/// record, and the [`Provenance`] staged for it (`None` for a direct edit).
type PendingEdit = (u64, pcp::LayerId, sdf::ChangeList, Option<Provenance>);

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
    /// Installed stage-tier change sinks (C++ `UsdNotice` registrations,
    /// generalized), fanned out after each recompose and on lifecycle changes.
    /// Empty by default, so the no-sink path allocates nothing extra.
    ///
    /// Held under a shared borrow for the duration of a fan-out, so a sink may
    /// re-author the stage (a re-entrant fan-out takes its own shared borrow), but
    /// must not add or remove sinks from within a callback — that would borrow the
    /// set mutably while the fan-out holds it shared, and panic.
    sinks: RefCell<sdf::sink::Set<dyn StageSink>>,
    /// Layer edits recorded by each layer's aggregator sink (installed by
    /// [`add_layer`](Stage::add_layer)), awaiting composed processing by
    /// [`process_pending`](Stage::process_pending). Each entry carries the
    /// transaction id it committed under (so the drain groups a transaction's
    /// layers together, from [`current_generation`](Self::current_generation)) and its
    /// [`Provenance`], or `None` when no stage authoring method staged one — a
    /// direct [`layer_mut`](Stage::layer_mut) edit, resolved against local-layer
    /// membership when the queue drains.
    ///
    /// Recording an edit and recomposing for it are deliberately split across this
    /// queue rather than recomposing straight from the aggregator callback,
    /// because:
    ///
    /// - Borrows. The aggregator fires inside [`Layer::commit`](sdf::Layer::commit),
    ///   which the stage reaches by holding [`layers`](Self::layers) borrowed
    ///   mutably (the layer lives in the graph). Recomposing needs that same
    ///   borrow, plus [`cache`](Self::cache) — so the callback can only append to
    ///   this independent cell; [`process_pending`](Stage::process_pending) runs
    ///   the recompose once the graph borrow is released. A layer cannot recompose
    ///   the stage from the middle of its own mutation.
    /// - Batching. A multi-layer edit (a namespace edit across the local stack)
    ///   commits N layers, each firing its aggregator, so N records accumulate and
    ///   [`process_pending`](Stage::process_pending) drives one recompose for the
    ///   whole batch instead of N.
    /// - One path for every editor. A direct edit through
    ///   [`layer_mut`](Stage::layer_mut) fires the same aggregator with no stage
    ///   borrow held; the callback can't tell, so it records uniformly and the
    ///   recompose happens on the next composed read (drain-on-read). Stage-routed
    ///   and raw layer edits flow through the identical path.
    pending: RefCell<Vec<PendingEdit>>,
    /// The [`Provenance`] a stage authoring method publishes for the commit
    /// currently underway, read by the aggregator as it records into
    /// [`pending`](Self::pending). `None` for a direct edit, which the drain
    /// resolves from local-layer membership.
    edit_provenance: RefCell<Option<Provenance>>,
    /// The transaction id of the layer commit currently draining, cached from its
    /// [`PendingLayerChange`](sdf::PendingLayerChange) by the aggregator's
    /// `before_commit` so the matching `after_commit`
    /// ([`record_pending`](Stage::record_pending)) can stamp it onto the queued
    /// edit, which [`process_pending`](Stage::process_pending) then groups by. The
    /// id is minted once per atomic transaction by `sdf::edit_layers`, so a
    /// stage-authored batch and a direct [`layer_mut`](Stage::layer_mut) edit are
    /// each one transaction without the stage tracking any boundary of its own.
    current_generation: Cell<u64>,
}

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

/// Resets [`StageInner::edit_provenance`] to `None` on drop, so the provenance a
/// stage edit publishes for its aggregator is cleared on every exit — including a
/// panicking sink — and never leaks into a later commit.
struct ClearEditProvenance<'a>(&'a RefCell<Option<Provenance>>);

impl Drop for ClearEditProvenance<'_> {
    fn drop(&mut self) {
        self.0.take();
    }
}

/// The [`sdf::LayerSink`] a [`Stage`] installs on every layer it owns (through
/// [`add_layer`](Stage::add_layer)) to bridge the low tier of the change
/// pipeline to the high tier: it records each commit into
/// [`pending`](StageInner::pending) for a composed recompose, and forwards the
/// staged pre-commit edit to the stage's [`StageSink`]s. It holds a
/// [`WeakStage`] so it forms no reference cycle (the stage owns the layer, which
/// owns this sink).
struct StageAggregator {
    stage: WeakStage,
    layer_id: pcp::LayerId,
}

impl sdf::LayerSink for StageAggregator {
    fn before_commit(&self, change: &sdf::PendingLayerChange<'_>) -> Result<(), sdf::sink::Error> {
        if let Some(stage) = self.stage.upgrade() {
            // Cache this transaction's id (minted by `sdf::edit_layers`) for the
            // matching `after_commit`'s `record_pending` to read; `before_commit`
            // fires for a layer before its `after_commit`, and every layer of a
            // transaction shares one id, so the cache is correct for each.
            stage.current_generation.set(change.generation);
            stage.forward_before_commit(change);
        }
        Ok(())
    }

    fn after_commit(&self, _layer: &str, changes: &sdf::ChangeList) {
        if let Some(stage) = self.stage.upgrade() {
            stage.record_pending(self.layer_id, changes.clone());
        }
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
    pub fn builder() -> StageBuilder {
        StageBuilder::new()
    }

    /// Returns composition errors encountered while composing this stage.
    ///
    /// Combines the layer graph's current diagnostics (sublayer cycles and
    /// invalid relocates, always reflecting present graph state) with the
    /// cache's per-prim build errors. Prim indices are built lazily, so the
    /// per-prim half is a snapshot of errors discovered by stage queries
    /// performed so far.
    ///
    /// A muted branch's missing/unreadable sublayer, which the loader recorded raw,
    /// is filtered out here against the current composed state — the referring layer
    /// contributes nothing, or the sublayer itself is muted — so muting suppresses
    /// the diagnostic and unmuting restores it, without the one-shot error ever
    /// being discarded.
    pub fn composition_errors(&self) -> Vec<pcp::Error> {
        // Drain pending edits once, then take both borrows directly: routing through
        // the `layers()`/`cache()` accessors would each re-run `process_pending`, and
        // holding the graph borrow across the second run risks a re-entrant
        // borrow-mut if a sink re-queues an edit during notification.
        self.process_pending();
        let graph = self.layers.borrow();
        let mut errors = graph.errors();
        let cache_errors = self.cache.borrow().composition_errors();
        // Only a muted stage suppresses anything, and only sublayer diagnostics; skip
        // building the effective-layer set when there is nothing to filter.
        if !graph.has_muted_layers() || !cache_errors.iter().any(is_sublayer_error) {
            errors.extend(cache_errors);
            return errors;
        }
        // The effectively-composed layers: every composed stack's members (the root
        // stack and each interned reference/payload target stack), which muting has
        // pruned muted subtrees from. This is a pure function of the muted set and
        // the graph, so a diagnostic's visibility is deterministic and does not
        // flicker with cache warmth. A still-interned target whose only arc became
        // muted keeps its diagnostic — a deliberate conservative over-report (see the
        // pcp "Muted sublayer diagnostics" remaining-work note), chosen over hiding a
        // valid error because an unrelated invalidation evicted the proving index.
        let effective = graph.effective_layers();
        errors.extend(
            cache_errors
                .into_iter()
                .filter(|error| graph.sublayer_error_contributes(error, &effective)),
        );
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
            authoring_stack: None,
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
        // Composes the prim (loading any reference/payload target on demand) so
        // the arc lookup reads the current, fully-resolved composition.
        let info = self.with_cache(|graph, cache| cache.edit_target_node_info(graph, prim_path, |a| arc.matches(a)))?;
        let (layer_identifier, mapping, stack_info) = info.ok_or_else(|| StageAuthoringError::NoArcNode {
            path: prim_path.clone(),
            arc,
        })?;
        let mut target = self.bound_target(layer_identifier, mapping);
        // Record the node's own layer stack so the namespace editor authors into
        // it exactly, rather than inferring it from layer membership.
        target.authoring_stack = Some(match stack_info {
            None => AuthoringStack::Root,
            Some((root, expr_vars)) => AuthoringStack::Referenced(Box::new(ReferencedStack { root, expr_vars })),
        });
        Ok(target)
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

    /// Store `target` as the edit target, notifying sinks via
    /// [`StageSink::edit_target_changed`] when it differs from the current one.
    /// The shared core of
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
            for sink in self.sinks.borrow().iter() {
                sink.edit_target_changed(self);
            }
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
            // The layer records the spec add and any auto-created ancestor
            // `over`s; an idempotent call (existing def) records nothing because
            // deriving the change skips the no-op write.
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
            // `over` specs; the layer records them and the property add.
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
    /// current [`EditTarget`], delivers a `CommittedChange` to sinks, and invalidates
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
    /// current [`EditTarget`], delivers a `CommittedChange` to sinks, and invalidates
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
            layer.remove_spec(&layer_path)?;
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
    /// [`sdf::LayerEdit::set_default_prim`].
    pub fn set_default_prim(&self, name: impl Into<String>) -> Result<(), StageAuthoringError> {
        let name = name.into();
        self.with_root_layer(|layer| {
            // The layer records the `defaultPrim` change, and deriving it skips
            // cache invalidation when the value isn't changing.
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

    /// Install a [`StageSink`] (C++ `TfNotice::Register`, generalized) and
    /// return its [`StageSinkId`] for a later [`remove_sink`](Self::remove_sink).
    /// The sink stays installed until removed or the stage drops. A bare
    /// `Fn(&Stage, &CommittedChange)` closure is a sink, so this takes either a
    /// full sink type or a closure observer.
    ///
    /// Sinks observe each recompose ([`after_commit`](StageSink::after_commit))
    /// and lifecycle changes, fired after composition is invalidated and the
    /// stage borrows are released, so a sink may read or re-author the stage — but
    /// must not add or remove sinks from within a callback. A sink that retains
    /// stage access should capture a [`WeakStage`] from
    /// [`downgrade`](Self::downgrade), not a [`Stage`] clone (which would leak the
    /// stage through a reference cycle). To observe a single layer's edits
    /// regardless of composition, install an [`sdf::LayerSink`] on the layer
    /// instead.
    pub fn add_sink<S: StageSink + 'static>(&self, sink: S) -> StageSinkId {
        // Deliver any edit already committed (e.g. a direct `layer_mut` commit
        // awaiting drain) to the current set before this sink joins, so a sink
        // only ever observes edits committed after it was installed.
        self.process_pending();
        self.sinks.borrow_mut().add(Box::new(sink))
    }

    /// Remove the sink with the given [`StageSinkId`]; the inverse of
    /// [`add_sink`](Self::add_sink). A no-op if it was already removed.
    pub fn remove_sink(&self, id: StageSinkId) {
        // Deliver any already-committed edit to the full set, including this sink,
        // before it leaves — so it sees every edit committed while it was installed.
        self.process_pending();
        self.sinks.borrow_mut().remove(id);
    }

    /// The id of the layer the current edit target writes to, or
    /// [`StageAuthoringError::LayerNotFound`] when that layer is no longer in
    /// the stage. Resolves the edit-target identifier to its graph id, the
    /// shared step of the stage-metadata and diff-replay authoring paths.
    pub(super) fn edit_target_layer_id(&self) -> Result<pcp::LayerId, StageAuthoringError> {
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

    /// Authors `expressionVariables` on the current edit target's layer when it
    /// is the root or session layer (see [`Self::with_stage_metadata_layer`]).
    /// The dictionary supplies the values `${VAR}` expressions in sublayer asset
    /// paths and reference/payload targets resolve against; replacing it
    /// recomposes every prim whose composition reads the edited layer stack.
    pub fn set_expression_variables(&self, vars: HashMap<String, sdf::Value>) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_expression_variables(vars))
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
    /// On an authoring error [`Layer::edit`](sdf::Layer::edit) has already rolled
    /// the layer back — the staged edits vanish and the backend is untouched — so
    /// the cache stays valid and no invalidation is needed.
    pub(super) fn with_target_layer_at<F>(&self, scene_path: &sdf::Path, f: F) -> Result<bool, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::LayerEdit<'_>, sdf::Path) -> Result<(), sdf::AuthoringError>,
    {
        // Read the target identifier and mapped spec path under a short borrow
        // of `edit_target` (which owns a heap `MapFunction`), releasing it
        // before the layer borrow below. The mapping is cloned out (rather than
        // borrowed across the authoring call) because the sinks it ultimately
        // feeds can re-author and re-target the stage; clone it only when a sink
        // is installed to consume it, keeping the common no-sink authoring path
        // allocation-free.
        let notify = !self.sinks.borrow().is_empty();
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
        let edited = {
            let mut layers = self.layers.borrow_mut();
            let layer_id = layers
                .id_of(&identifier)
                .ok_or(StageAuthoringError::LayerNotFound { layer: identifier })?;
            let node = layers.get_mut(layer_id).expect("id_of returned a live id");
            self.edit_layer(&mut node.layer, mapping.as_ref(), |layer| f(layer, spec_path))
        };
        // `edit_layer` reports whether the edit produced a composition change.
        self.process_pending();
        edited
    }

    /// Borrow the stage's root layer, hand it to `f`, then drive cache
    /// invalidation from the closure's [`sdf::ChangeList`]. See
    /// [`Stage::with_target_layer_at`] for the contract. Unlike that method,
    /// this ignores the edit target and its mapping — `defaultPrim` is a
    /// root-layer field authored at `abs_root` verbatim.
    fn with_root_layer<F>(&self, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), sdf::AuthoringError>,
    {
        let layer_id = self
            .layers
            .borrow()
            .root_id()
            .ok_or(StageAuthoringError::OutsideEditTarget {
                path: sdf::Path::abs_root(),
            })?;
        self.author_on_layer(layer_id, None, f)
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
        F: FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), sdf::AuthoringError>,
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
        self.author_on_layer(layer_id, None, f)
    }

    /// Stage a batch across `layer_ids` as one atomic transaction, then drive
    /// cache invalidation from the change lists it records — or, for a dry run
    /// (`commit = false`), stage and discard without committing or firing any
    /// sink. The shared transaction core behind
    /// [`author_on_layer`](Self::author_on_layer) (single-layer) and the
    /// namespace editor's mapped relocate batch (which authors across the edit
    /// target's own layer stack: the structural moves land in the target layer
    /// while the synthesized relocates spread across that stack's layers, all
    /// committing together). `apply` commits, `can_apply` dry-runs, both sharing
    /// `f` so an error surfaces identically.
    ///
    /// `mapping` is the edit target's namespace mapping, recorded with a committed
    /// edit so the composed change keeps full path precision; a non-identity
    /// mapping publishes [`Provenance::EditTarget`] so the edit is attributed to
    /// its variant or arc target. `None` (or an identity mapping) authors at
    /// stage-namespace paths verbatim. `f` receives the realized layer ids (those
    /// `layer_ids` with a live layer, dropping any that vanished) paired in order
    /// with their [`sdf::LayerEdit`]s. The closure's error type is free (any
    /// `E: From<sdf::sink::Error>`) so the caller can surface its own validation
    /// errors through the same transaction.
    pub(super) fn author_layers_txn<E>(
        &self,
        layer_ids: &[pcp::LayerId],
        mapping: Option<&pcp::MapFunction>,
        commit: bool,
        f: impl FnOnce(&[pcp::LayerId], &mut [sdf::LayerEdit<'_>]) -> Result<(), E>,
    ) -> Result<(), E>
    where
        E: From<sdf::sink::Error>,
    {
        let result = {
            let mut graph = self.layers.borrow_mut();
            let mut layers: Vec<(pcp::LayerId, &mut sdf::Layer)> = graph.layers_mut(layer_ids).into_iter().collect();
            // The realized ids, aligned with the edits below: `layers_mut` drops any
            // id with no live layer, so the closure keys on these rather than the
            // requested `layer_ids` to stay paired with each `LayerEdit`.
            let ids: Vec<pcp::LayerId> = layers.iter().map(|(id, _)| *id).collect();
            let mut batch: Vec<&mut sdf::Layer> = layers.iter_mut().map(|(_, layer)| &mut **layer).collect();
            if commit {
                let provenance = mapping
                    .filter(|m| !m.is_identity())
                    .map(|m| Provenance::EditTarget(m.clone()));
                self.edit_provenance.replace(provenance);
                let _clear = ClearEditProvenance(&self.edit_provenance);
                sdf::edit_layers(&mut batch, |edits| f(&ids, edits)).map(|_| ())
            } else {
                sdf::dry_run_layers(&mut batch, |edits| f(&ids, edits))
            }
        };
        if commit {
            self.process_pending();
        }
        result
    }

    /// The handle for the layer stack the mapped edit `target_layer` writes
    /// into — the stack a relocate synthesized for that target must land in. An
    /// arc target carries its [`AuthoringStack`] from construction, so it resolves
    /// exactly (the referenced asset's stack even when that asset is also a root
    /// sublayer); a target without one (a local or variant target) is inferred
    /// from layer membership — the root stack when `target_layer` belongs to it,
    /// else the sublayer stack rooted at it. Per spec §10.3.2.6, relocates take
    /// effect in the stack where the bringing-in arc is authored, so this is
    /// where the editor seeds and authors the mapped relocate plan; resolve it to
    /// member layer ids with
    /// [`LayerGraph::layer_stack`](crate::pcp::LayerGraph::layer_stack).
    pub(super) fn mapped_target_stack_id(&self, target_layer: pcp::LayerId) -> pcp::LayerStackId {
        // Determine the `(root, inherited context)` the target authors into: the
        // captured stack for an arc target (its context preserved so a contextual
        // stack reconstructs faithfully), or, for a target inferred from layer
        // membership, the root stack when the layer belongs to it, else the plain
        // stack rooted at the layer itself.
        let (root, expr_vars) = match &self.edit_target.borrow().authoring_stack {
            Some(AuthoringStack::Root) => return self.layers().root_layer_stack_id(),
            Some(AuthoringStack::Referenced(stack)) => (
                self.layers().id_of(&stack.root).unwrap_or(target_layer),
                stack.expr_vars.clone(),
            ),
            None if self
                .layers()
                .root_layer_stack()
                .iter()
                .any(|&(id, _)| id == target_layer) =>
            {
                return self.layers().root_layer_stack_id()
            }
            None => (target_layer, HashMap::new()),
        };
        // Resolve to the exact stack, minting it when the target was never composed
        // in this session rather than falling back to an unrelated stack (which would
        // seed the relocate plan from the wrong layers).
        self.layers.borrow_mut().ensure_external_stack(root, &expr_vars)
    }

    /// Run `f` as one committed atomic transaction on the single layer
    /// `layer_id`. The [`StageAuthoringError`]-typed, single-layer convenience
    /// over [`author_layers_txn`](Self::author_layers_txn) shared by
    /// [`with_root_layer`](Self::with_root_layer),
    /// [`with_stage_metadata_layer`](Self::with_stage_metadata_layer), and
    /// [`apply_diff`](Stage::apply_diff). A multi-edit replay that fails midway
    /// rolls back wholesale, leaving the layer and cache untouched.
    pub(super) fn author_on_layer<F>(
        &self,
        layer_id: pcp::LayerId,
        mapping: Option<&pcp::MapFunction>,
        f: F,
    ) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), sdf::AuthoringError>,
    {
        self.author_layers_txn(&[layer_id], mapping, true, |_ids, edits| {
            f(&mut edits[0]).map_err(StageAuthoringError::from)
        })
    }

    /// Run `f` as one atomic [`Layer::edit`](sdf::Layer::edit) on `layer`: commit
    /// and return the recorded change list on success, or roll the layer back on
    /// error (`f`'s authoring error, or a sink veto).
    ///
    /// Committing fires the layer's sinks — including the stage's aggregator
    /// (installed by [`add_layer`](Self::add_layer)), which records the edit into
    /// [`pending`](StageInner::pending) for [`process_pending`](Self::process_pending)
    /// to recompose. A [`before_commit`](sdf::LayerSink::before_commit) rejection
    /// surfaces as [`StageAuthoringError::Rejected`]. `mapping` is the edit
    /// target's namespace mapping; a non-local target publishes
    /// [`Provenance::EditTarget`] and a local/root one [`Provenance::LocalStack`]
    /// through [`edit_provenance`](StageInner::edit_provenance) for the aggregator
    /// to tag the recorded edit with.
    fn edit_layer<F>(
        &self,
        layer: &mut sdf::Layer,
        mapping: Option<&pcp::MapFunction>,
        f: F,
    ) -> Result<bool, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), sdf::AuthoringError>,
    {
        // Publish the provenance for the aggregator firing inside `edit`'s commit,
        // under a guard that clears it on the way out — including if the edit
        // panics — so a later commit never inherits a stale provenance. Only a
        // remapping arc or variant target (a non-identity mapping) is `EditTarget`;
        // an identity-mapped or unmapped target authors at the layer's own paths,
        // so it is left unset for the drain to resolve from local-layer membership
        // (`LocalStack` for a local layer, `DirectLayerEdit` for a non-local one).
        let provenance = mapping
            .filter(|m| !m.is_identity())
            .map(|m| Provenance::EditTarget(m.clone()));
        self.edit_provenance.replace(provenance);
        let _clear = ClearEditProvenance(&self.edit_provenance);
        layer.edit(f).map_err(StageAuthoringError::from)
    }

    /// The layer ids of the root (local) layer stack, strongest first — the
    /// layers a namespace edit authors into to move or delete a composed object.
    pub(super) fn root_stack_layer_ids(&self) -> Vec<pcp::LayerId> {
        self.layers().root_layer_stack().iter().map(|&(id, _)| id).collect()
    }

    /// Add `layer` to the stage's graph, returning its id and whether it newly
    /// joined (a duplicate identifier collapses onto the existing node). The one
    /// seam by which a layer joins the stage — both opening (`make_stage`) and
    /// [`insert_layer`](Self::insert_layer) go through it. A freshly-added layer
    /// gets the stage's change aggregator: a [`sdf::LayerSink`] that records the
    /// layer's commits into [`pending`](StageInner::pending) for
    /// [`process_pending`](Self::process_pending) to recompose, so every layer the
    /// stage owns reports its edits no matter who authors them. The sink holds a
    /// [`WeakStage`], so it does not form a reference cycle (the stage owns the
    /// layer, which owns the sink).
    fn add_layer(&self, layer: sdf::Layer) -> (pcp::LayerId, bool) {
        let mut layers = self.layers.borrow_mut();
        let (id, fresh) = layers.ensure_layer(layer);
        if fresh {
            let node = layers.get_mut(id).expect("just-interned layer is live");
            node.layer.add_sink(StageAggregator {
                stage: self.downgrade(),
                layer_id: id,
            });
        }
        (id, fresh)
    }

    /// Fan out a layer's staged pre-commit edit to the installed
    /// [`StageSink`]s' [`before_commit`](StageSink::before_commit), bridging one
    /// [`sdf::PendingLayerChange`] to the stage-tier [`PendingChange`]. Called by
    /// the [`StageAggregator`] from inside the layer's commit seam, while the
    /// layer graph is borrowed for the edit — so it reads only
    /// [`sinks`](StageInner::sinks) and [`edit_provenance`](StageInner::edit_provenance),
    /// never the graph or cache. A no-op when no sink is installed.
    fn forward_before_commit(&self, change: &sdf::PendingLayerChange<'_>) {
        let sinks = self.sinks.borrow();
        if sinks.is_empty() {
            return;
        }
        // Borrow the provenance's mapping into the event rather than cloning it: a
        // `before_commit` sink observes and must not re-enter authoring (which is
        // what would re-borrow `edit_provenance`), so holding the borrow across the
        // fan-out is safe and avoids a per-commit `MapFunction` clone.
        let provenance = self.edit_provenance.borrow();
        let pending = PendingChange {
            layer_identifier: change.layer_identifier,
            base: change.base,
            change_list: change.change_list,
            mapping: provenance.as_ref().and_then(|p| p.mapping()),
            generation: change.generation,
        };
        for sink in sinks.iter() {
            sink.before_commit(self, &pending);
        }
    }

    /// Record a committed layer edit for [`process_pending`](Self::process_pending),
    /// tagged with the [`Provenance`] staged for it (read from
    /// [`edit_provenance`](StageInner::edit_provenance); `None` for a direct
    /// edit). Called by the per-layer aggregator sink (installed by
    /// [`add_layer`](Self::add_layer)) as a layer commits — while the layer graph
    /// is borrowed for the edit, which is why it appends to the independent
    /// [`pending`](StageInner::pending) cell rather than recomposing inline.
    pub(super) fn record_pending(&self, layer_id: pcp::LayerId, changes: sdf::ChangeList) {
        let provenance = self.edit_provenance.take();
        self.pending
            .borrow_mut()
            .push((self.current_generation.get(), layer_id, changes, provenance));
    }

    /// Drain the layer edits recorded by the aggregators and drive one composition
    /// recompose, delivering the composed [`CommittedChange`](super::CommittedChange)
    /// to the stage sinks. The deferred counterpart to a layer commit: an
    /// aggregator records the edit while the layer graph is borrowed, and this
    /// runs once that borrow is released — after each authoring call, and before
    /// any composed read. A no-op when nothing is pending, so a read on a clean
    /// stage costs only the empty check.
    pub(crate) fn process_pending(&self) {
        let mut drained = {
            let mut queue = self.pending.borrow_mut();
            if queue.is_empty() {
                return;
            }
            std::mem::take(&mut *queue)
        };
        // An edit changes the layers, so a target that previously failed to read
        // may now be readable: forget recorded load failures and drop the indices
        // that recorded one, so the next query re-demands and recomposes them.
        if self.layers.borrow_mut().clear_failed_loads() {
            self.cache.borrow_mut().drop_load_failed_indices();
        }
        // Entries committed under one transaction id are contiguous — a
        // transaction's layers record together, and the id increases across
        // transactions — so grouping by adjacent equal id carves the queue into
        // per-transaction groups. Each group applies as its own composed change,
        // so unrelated edits (a direct `layer_mut` commit sitting pending when the
        // next stage edit lands) stay separate rather than merging into one event.
        for group in drained.chunk_by_mut(|a, b| a.0 == b.0) {
            let generation = group[0].0;
            let provenance = self.resolve_group_provenance(group);
            let edits: Vec<(pcp::LayerId, &sdf::ChangeList)> =
                group.iter().map(|(_, id, changes, _)| (*id, changes)).collect();
            self.apply_change_sets(generation, &edits, &provenance);
        }
    }

    /// The [`Provenance`] for one transaction's group of recorded edits. A staged
    /// provenance (published by a stage authoring method) rides the first layer
    /// the transaction committed; an unstaged direct edit resolves from
    /// local-layer membership — [`Provenance::LocalStack`] when the edited layer
    /// is in the root layer stack (its paths are stage paths), else
    /// [`Provenance::DirectLayerEdit`]. A multi-layer group with no staged
    /// provenance is a local-stack batch (its layers share the stage namespace).
    fn resolve_group_provenance(&self, group: &mut [PendingEdit]) -> Provenance {
        if let Some(provenance) = group.iter_mut().find_map(|(_, _, _, provenance)| provenance.take()) {
            return provenance;
        }
        match group {
            [(_, id, _, _)]
                if !self
                    .layers
                    .borrow()
                    .root_layer_stack()
                    .iter()
                    .any(|&(lid, _)| lid == *id) =>
            {
                Provenance::DirectLayerEdit
            }
            _ => Provenance::LocalStack,
        }
    }

    /// Classify one transaction's committed [`sdf::ChangeList`]s — one per edited
    /// layer — through a single [`pcp::Changes`] cycle and apply the resulting
    /// cache invalidation, delivering one [`CommittedChange`](super::CommittedChange)
    /// (tagged with the transaction `generation`) to the installed sinks.
    ///
    /// [`pcp::Changes::did_change`] takes the per-layer split because
    /// classification is layer-relative; the event instead reports the merged
    /// record, attributed to the strongest edited layer. `provenance` says how the
    /// records' layer-namespace paths reach stage namespace — a batched namespace
    /// edit is [`Provenance::LocalStack`], the local layer stack sharing the
    /// stage's namespace.
    fn apply_change_sets(&self, generation: u64, edits: &[(pcp::LayerId, &sdf::ChangeList)], provenance: &Provenance) {
        let mut pcp_changes = pcp::Changes::new();
        {
            let cache = self.cache.borrow();
            pcp_changes.did_change(&cache, edits);
        }
        // Snapshot the after-commit payload before `apply` consumes
        // `pcp_changes`, and only when a sink is installed — the no-sink path
        // stays allocation-free. The event carries both the merged change list
        // (the union, keyed to the strongest layer) and the per-layer records
        // ([`layer_changes`]), so a sink deriving a per-layer diff reads each
        // layer's own record rather than mis-reading a sublayer's change against
        // the strongest layer's data.
        let payload = (!self.sinks.borrow().is_empty()).then(|| {
            let layer_changes: Vec<(String, sdf::ChangeList)> = edits
                .iter()
                .map(|(id, changes)| (self.layer_identifier(*id).unwrap_or_default(), (*changes).clone()))
                .collect();
            let mut merged = sdf::ChangeList::new();
            for (_, changes) in edits {
                merged.merge_from(changes);
            }
            Payload::new(&pcp_changes, &merged, layer_changes, provenance)
        });
        {
            let mut graph = self.layers.borrow_mut();
            let mut cache = self.cache.borrow_mut();
            pcp_changes.apply(&mut cache, &mut graph);
        }

        if let Some(payload) = payload {
            let layer_identifier = edits
                .first()
                .and_then(|(id, _)| self.layer_identifier(*id))
                .unwrap_or_default();
            let change = payload.committed_change(&layer_identifier, provenance, generation);
            for sink in self.sinks.borrow().iter() {
                sink.after_commit(self, &change);
            }
        }
    }

    /// Returns the number of layers loaded so far (including session layers).
    ///
    /// Layers behind references and payloads load on demand as composition
    /// reaches their arcs, so this is the count loaded by the queries performed
    /// so far — it grows as more of the stage is visited, mirroring C++
    /// `UsdStage::GetUsedLayers`. The root layer stack is always fully loaded.
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

    /// Returns the identifiers of the layers loaded so far, in collection order
    /// (session and root layer stack first, then arc-target layers in the order
    /// composition opened them).
    ///
    /// Reference and payload target layers load on demand, so this lists the
    /// layers reached by the queries performed so far rather than the full
    /// transitive closure (C++ `UsdStage::GetUsedLayers`). Traverse the stage
    /// to force every reachable layer to load.
    pub fn layer_identifiers(&self) -> Vec<String> {
        self.layers().identifiers()
    }

    /// Returns the identifiers of the stage's root layer stack — the session
    /// layers, the root layer, and its sublayers, in strength order. Mirrors
    /// C++ `UsdStage::GetLayerStack` (with `includeSessionLayers = true`).
    ///
    /// Unlike [`layer_identifiers`](Self::layer_identifiers), which lists the
    /// loaded layers including those reached across reference/payload arcs, this
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
    /// call (`insert_layer`, `define_prim`, …) takes `self.layers` mutably,
    /// so a live `Ref` held across one panics with a `RefCell` double-borrow. In
    /// particular `stage.insert_layer(stage.root_layer().identifier(), …)`
    /// panics — the `Ref` temporary lives to the end of the statement. Bind the
    /// identifier first so the borrow is released:
    ///
    /// ```no_run
    /// # use openusd::{sdf, usd};
    /// # fn f(stage: &usd::Stage, layer: sdf::Layer) {
    /// let id = stage.root_layer().identifier().to_owned();
    /// stage.insert_layer(&id, 0, layer, sdf::LayerOffset::IDENTITY).unwrap();
    /// # }
    /// ```
    pub fn root_layer(&self) -> Ref<'_, sdf::Layer> {
        Ref::map(self.layers(), |layers| {
            layers.root_layer().expect("stage has a root layer")
        })
    }

    /// Borrow the stage's layer named `identifier`, or `None` if no such layer is
    /// in the stage. `identifier` is matched by canonical identifier.
    pub fn layer(&self, identifier: &str) -> Option<Ref<'_, sdf::Layer>> {
        Ref::filter_map(self.layers(), |layers| {
            let id = layers.id_of(identifier)?;
            layers.get(id).map(|node| &node.layer)
        })
        .ok()
    }

    /// Borrow the stage's layer named `identifier` mutably, or `None` if no such
    /// layer is in the stage — an advanced escape hatch for editing a layer
    /// directly, or installing an [`sdf::LayerSink`] on it with
    /// [`Layer::add_sink`](sdf::Layer::add_sink). Prefer the stage's authoring
    /// methods, which integrate the edit into composition before they return.
    ///
    /// An edit committed through the returned layer is recorded and integrated
    /// lazily, on the next stage access: both the graph and the index cache drain
    /// any pending edit before they are observed, so a structural edit (sublayers,
    /// offsets, relocates) never leaves [`sub_layers`](Self::sub_layers) and
    /// friends reading stale topology. A direct edit to a non-local (referenced or
    /// payload) layer reports its [`CommittedChange`](super::CommittedChange) paths
    /// in that layer's own namespace, flagged
    /// [`Provenance::DirectLayerEdit`](super::Provenance::DirectLayerEdit). Holds
    /// the layer graph borrowed for the guard's lifetime; drop it before any other
    /// stage call.
    pub fn layer_mut(&self, identifier: &str) -> Option<RefMut<'_, sdf::Layer>> {
        RefMut::filter_map(self.layers_mut(), |layers| {
            let id = layers.id_of(identifier)?;
            layers.get_mut(id).map(|node| &mut node.layer)
        })
        .ok()
    }

    /// Edit several of the stage's layers as one atomic transaction, then drive a
    /// single composition recompose — the public door for multi-layer authoring
    /// of a stage's layers.
    ///
    /// `layers` names the layers to edit by canonical identifier; `f` receives one
    /// [`LayerEdit`](sdf::LayerEdit) per name, in the same order, so `edits[i]`
    /// authors `layers[i]`. The batch is all-or-nothing: an authoring error from
    /// `f`, a [`sdf::LayerSink`] veto, or a panic rolls every layer back, leaving
    /// none partially applied; the layers commit together and the composed scene
    /// is coherent on return. Returns whether the batch produced a composition
    /// change.
    ///
    /// For a single layer, prefer the stage's typed authoring methods (which route
    /// through the current [`EditTarget`]) or [`layer_mut`](Self::layer_mut).
    /// Returns [`StageAuthoringError::LayerNotFound`] if a name is not in the stage
    /// and [`StageAuthoringError::DuplicateLayer`] if a name is repeated. On any
    /// error the stage is left untouched.
    pub fn batch_edit(
        &self,
        layers: &[&str],
        f: impl FnOnce(&mut [sdf::LayerEdit<'_>]) -> Result<(), StageAuthoringError>,
    ) -> Result<bool, StageAuthoringError> {
        let mut ids = Vec::with_capacity(layers.len());
        {
            let graph = self.layers();
            for &identifier in layers {
                let id = graph
                    .id_of(identifier)
                    .ok_or_else(|| StageAuthoringError::LayerNotFound {
                        layer: identifier.to_string(),
                    })?;
                if ids.contains(&id) {
                    return Err(StageAuthoringError::DuplicateLayer {
                        layer: identifier.to_string(),
                    });
                }
                ids.push(id);
            }
        }
        // Open every named layer in `ids` order and edit them as one transaction;
        // each commit feeds the stage's aggregator, so the recompose below folds
        // the whole batch in one cycle.
        //
        // TODO: `NamespaceEditor::execute` open-codes this same
        // `layers_mut` → `edit_layers` → `process_pending` transaction; it could
        // share this path once the closure exposes each layer's id (for its
        // per-layer relocate authoring) and a dry-run variant (for `can_apply`).
        let changed = {
            let mut graph = self.layers_mut();
            let mut batch: Vec<&mut sdf::Layer> = graph.layers_mut(&ids).into_iter().map(|(_, layer)| layer).collect();
            sdf::edit_layers(&mut batch, f)?
        };
        self.process_pending();
        Ok(changed)
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

    /// Mutes the layer with the given identifier so it contributes no opinions to
    /// composition — as if absent from every layer stack it participates in —
    /// while staying registered so [`unmute_layer`](Self::unmute_layer) restores
    /// it (C++ `UsdStage::MuteLayer` → `PcpCache::RequestLayerMuting`). Muting
    /// prunes the layer's whole sublayer subtree, not just the one layer.
    ///
    /// The layer need not be loaded: muting an identifier the stage does not
    /// (yet) contain records it and takes effect if such a layer is later
    /// encountered. The session layer can be muted; the root layer cannot (it
    /// "would lead to empty layer stacks", matching C++), so a request to mute it
    /// is ignored and `is_layer_muted` stays false for the root.
    ///
    /// This implements Pcp/Stage-level muting. Sdf-level layer muting
    /// (`SdfLayer::SetMuted`, a process-global data swap) is a separate feature
    /// and is not implemented.
    pub fn mute_layer(&self, identifier: impl Into<String>) {
        if let Some(changed) = self.apply_mute(|graph| graph.mute_layer(identifier.into())) {
            self.notify_muting_changed(&changed, true);
        }
    }

    /// Unmutes the layer with the given identifier, restoring its opinions to
    /// composition (C++ `UsdStage::UnmuteLayer`).
    pub fn unmute_layer(&self, identifier: &str) {
        if let Some(changed) = self.apply_mute(|graph| graph.unmute_layer(identifier)) {
            self.notify_muting_changed(&changed, false);
        }
    }

    /// Loads `path`'s payload — and its ancestors', if not already loaded —
    /// per `policy` (C++ `UsdStage::Load`). Loading an already-loaded path is
    /// legal and simply costs nothing (see [`load_rules`](Self::load_rules)'s
    /// no-op guarantee). `path` need not currently resolve to a composed
    /// prim — only an ancestor need exist — since loading a not-yet-visible
    /// descendant is the common case.
    ///
    /// A `path` that normalizes into a `/__Prototype_N` prototype's namespace
    /// is silently ignored, mirroring [`mute_layer`](Self::mute_layer)'s
    /// treatment of the root layer: load rules are always authored in
    /// real-namespace terms, and a rule on a synthetic prototype path would
    /// never be consulted. No inactive-ancestor validation is performed — an
    /// inactive subtree never composes regardless of its load rule, so a rule
    /// authored there is inert but harmless.
    pub fn load(&self, path: impl Into<sdf::Path>, policy: LoadPolicy) {
        let Some(path) = self.normalize_load_target(path.into()) else {
            return;
        };
        let victims = self.install_load_rules(|rules| match policy {
            LoadPolicy::WithDescendants => rules.load_with_descendants(path.clone()),
            LoadPolicy::WithoutDescendants => rules.load_without_descendants(path.clone()),
        });
        self.notify_load_rules_changed(&victims);
    }

    /// Unloads `path`'s payload and everything beneath it (C++
    /// `UsdStage::Unload`). Same leniency as [`load`](Self::load) for a
    /// prototype-namespace path.
    pub fn unload(&self, path: impl Into<sdf::Path>) {
        let Some(path) = self.normalize_load_target(path.into()) else {
            return;
        };
        let victims = self.install_load_rules(|rules| rules.unload(path.clone()));
        self.notify_load_rules_changed(&victims);
    }

    /// Loads every path in `to_load` (with `policy`) and unloads every path
    /// in `to_unload`, applying every edit to one clone of the rules and
    /// recomposing once for the whole batch (C++ `UsdStage::LoadAndUnload`).
    /// Every `to_unload` path is applied before
    /// any `to_load` path, matching C++'s own "unloads first, then loads" —
    /// so a path in both sets ends up loaded, and unloading an ancestor while
    /// loading one of its descendants in the same call still leaves the
    /// descendant reachable (the ancestor resolves to
    /// [`pcp::Rule::Only`](crate::pcp::Rule::Only), not excluded, via
    /// [`pcp::LoadRules::effective_rule`]'s lookahead).
    pub fn load_and_unload(
        &self,
        to_load: impl IntoIterator<Item = (impl Into<sdf::Path>, LoadPolicy)>,
        to_unload: impl IntoIterator<Item = impl Into<sdf::Path>>,
    ) {
        let to_unload: Vec<sdf::Path> = to_unload
            .into_iter()
            .filter_map(|path| self.normalize_load_target(path.into()))
            .collect();
        let to_load: Vec<(sdf::Path, LoadPolicy)> = to_load
            .into_iter()
            .filter_map(|(path, policy)| self.normalize_load_target(path.into()).map(|path| (path, policy)))
            .collect();
        let victims = self.install_load_rules(|rules| {
            for path in to_unload {
                rules.unload(path);
            }
            for (path, policy) in to_load {
                match policy {
                    LoadPolicy::WithDescendants => rules.load_with_descendants(path),
                    LoadPolicy::WithoutDescendants => rules.load_without_descendants(path),
                }
            }
        });
        self.notify_load_rules_changed(&victims);
    }

    /// A clone of the stage's current load rules (C++
    /// `UsdStage::GetLoadRules`).
    pub fn load_rules(&self) -> pcp::LoadRules {
        self.cache().load_rules().clone()
    }

    /// Replaces the stage's load rules wholesale, recomposing every cached
    /// index the change could affect (C++ `UsdStage::SetLoadRules`) — the
    /// same bounded invalidation [`load`](Self::load)/[`unload`](Self::unload)
    /// use, not a blunt whole-stage drop, since the affected set is already
    /// provably sufficient (see [`pcp::LoadRules`]'s module documentation).
    pub fn set_load_rules(&self, rules: pcp::LoadRules) {
        let victims = self.replace_load_rules(rules);
        self.notify_load_rules_changed(&victims);
    }

    /// Every prim below `root` (inclusive) that carries a payload arc, loaded
    /// or not, excluding inactive prims (C++ `UsdStage::FindLoadable`).
    ///
    /// Discovering a payload nested several levels deep requires actually
    /// reading its target layer — there is no way to know a layer's content
    /// without loading it — so this call transiently installs
    /// [`pcp::LoadRules::all`] to make every payload discoverable, walks the
    /// tree, and then restores the stage's original load rules. Neither swap
    /// fires [`StageSink::load_rules_changed`], and [`load_rules`](Self::load_rules)
    /// reads back the original table afterward, so the *rules* are not
    /// observable — but if `root`'s current rules are not already the
    /// all-inclusive default, each swap can still evict cached prim indices
    /// and bump the composition revision (matching whatever `set_load_rules`
    /// would do for that same transition), which a cached value view keyed
    /// on the revision will notice.
    ///
    /// This also has a real, permanent side effect worth calling out: every
    /// payload-target layer under `root` is left loaded in the layer
    /// registry afterward, even though the load *rules* are restored — this
    /// codebase has no layer-eviction mechanism yet, so there is no way to
    /// discover a payload's content without leaving its layer resident.
    /// C++'s own `FindLoadable` equally must traverse (and thus compose)
    /// every candidate subtree.
    // TODO(perf): when the stage's current rules are not already
    // `LoadRules::all()`, the install and the restore each evict the whole
    // store (the root rule itself changes), so a stage opened with
    // `InitialLoadSet::LoadNone` pays two full-store recomposes per call. A
    // scratch cache the walk composes into, left uncommitted, would avoid
    // this, but is a larger change than this method currently needs.
    pub fn find_loadable(&self, root: impl Into<sdf::Path>) -> anyhow::Result<Vec<sdf::Path>> {
        let root = root.into();
        let _guard = LoadRulesGuard {
            stage: self,
            original: self.load_rules(),
        };
        self.replace_load_rules(pcp::LoadRules::all());
        let mut found = Vec::new();
        self.walk_loadable(&root, &mut found)?;
        found.sort();
        found.dedup();
        Ok(found)
    }

    /// Every prim currently included by the load rules — i.e. carrying a
    /// payload arc whose own rule currently resolves loaded (C++
    /// `UsdStage::GetLoadSet`). Unlike [`load_rules`](Self::load_rules), this
    /// reports the actual composed state, not the raw authored rules.
    pub fn load_set(&self) -> anyhow::Result<Vec<sdf::Path>> {
        Ok(self
            .find_loadable(sdf::Path::abs_root())?
            .into_iter()
            .filter(|path| self.is_path_loaded(path))
            .collect())
    }

    /// Collects every active, payload-carrying prim at or below `path` into
    /// `found` — the walk behind [`find_loadable`](Self::find_loadable). An
    /// explicit work stack, not native recursion, so a pathologically deep
    /// prim hierarchy cannot overflow the call stack — matching
    /// [`traverse`](Self::traverse)'s own approach to the same style of
    /// whole-tree walk.
    fn walk_loadable(&self, path: &sdf::Path, found: &mut Vec<sdf::Path>) -> anyhow::Result<()> {
        let mut stack = vec![path.clone()];
        while let Some(path) = stack.pop() {
            let prim = self.prim(path.clone());
            if !prim.is_active()? {
                continue;
            }
            if super::prim::has_payload(self, &path)? {
                found.push(path.clone());
            }
            for child in prim.children()? {
                stack.push(child.path().clone());
            }
        }
        Ok(())
    }

    /// Reduces `path` to an absolute prim path (`prim_path` strips a property
    /// suffix and `strip_all_variant_selections` collapses any variant
    /// segment — [`pcp::LoadRules`]' table requires genuinely prim-only
    /// paths), then rejects a path inside a `/__Prototype_N` namespace, where
    /// load rules are never consulted (see [`pcp::LoadRules`]'s instancing
    /// notes). A cheap early exit for `load`/`unload`/`load_and_unload` — the
    /// real enforcement of the same invariant lives in
    /// `IndexCache::set_load_rules`, the single choke point every mutation
    /// (including a caller-supplied [`set_load_rules`](Self::set_load_rules)
    /// table this normalization never sees) passes through.
    fn normalize_load_target(&self, path: sdf::Path) -> Option<sdf::Path> {
        let path = sdf::Path::abs_root().make_absolute(&path.prim_path().strip_all_variant_selections());
        let cache = self.cache();
        if cache.is_prototype(&path) || cache.is_in_prototype(&path) {
            return None;
        }
        Some(path)
    }

    /// Applies `edit` to a clone of the stage's current load rules and
    /// installs the result, returning the bounded set of paths whose cached
    /// index was dropped (empty for a no-op edit). For `load`/`unload`/
    /// `load_and_unload`, which build on the existing table.
    fn install_load_rules(&self, edit: impl FnOnce(&mut pcp::LoadRules)) -> Vec<sdf::Path> {
        let mut rules = self.cache.borrow().load_rules().clone();
        edit(&mut rules);
        self.replace_load_rules(rules)
    }

    /// Installs `rules` directly in place of the stage's current load rules,
    /// returning the bounded set of paths whose cached index was dropped. The
    /// entry point for callers that already hold the exact replacement
    /// value: [`set_load_rules`](Self::set_load_rules) and the transient
    /// swaps in [`find_loadable`](Self::find_loadable)/[`LoadRulesGuard`].
    fn replace_load_rules(&self, rules: pcp::LoadRules) -> Vec<sdf::Path> {
        // Drain pending edits first so the mutation recomposes against a
        // current graph and cache, matching `apply_mute`.
        self.process_pending();
        self.cache.borrow_mut().set_load_rules(rules)
    }

    /// Fires [`StageSink::load_rules_changed`] with the resynced paths, after
    /// the cache borrow is released — skipped entirely when `resynced` is
    /// empty (a no-op edit invalidated nothing).
    fn notify_load_rules_changed(&self, resynced: &[sdf::Path]) {
        if resynced.is_empty() {
            return;
        }
        for sink in self.sinks.borrow().iter() {
            sink.load_rules_changed(self, resynced);
        }
    }

    /// `true` if `path`'s own payload is included by the stage's load rules —
    /// the per-ancestor check behind [`Prim::is_loaded`](super::Prim::is_loaded).
    pub(crate) fn is_path_loaded(&self, path: &sdf::Path) -> bool {
        self.cache().is_loaded(path)
    }

    /// Applies a muted-set mutation to the layer graph and recomposes when it
    /// reports a change, returning the canonical identifier whose muted state
    /// toggled (`None` when the set was unchanged). Unmuting through an alternate
    /// spelling reports the canonical identifier the layer was muted under, not the
    /// one passed, so a listener mirroring the set stays in sync. The mutation also
    /// reports the layers whose cached indices the change can invalidate, so only
    /// those are dropped rather than the whole cache. The graph owns the muted set
    /// and rejects the root layer; the borrows are released before the caller
    /// notifies, so the listener may read the set or re-author.
    fn apply_mute(&self, mutate: impl FnOnce(&mut pcp::LayerGraph) -> Option<pcp::MuteChange>) -> Option<String> {
        // Drain pending edits first so the mute recomposes against a current
        // graph and cache rather than stranding queued changes.
        self.process_pending();
        let mut graph = self.layers.borrow_mut();
        let mut cache = self.cache.borrow_mut();
        let change = mutate(&mut graph)?;
        // The mutation already rebuilt the graph's sublayer stacks, relocates, and
        // cycle diagnostics; only the cache needs work. Removing a session variable
        // drops the root `${VAR}` sublayer it selected — the graph re-resolves the
        // already-interned layer out of the stack. Dropping the affected indices by
        // both the toggled layer's fanout and its canonical identifier reaches a
        // referrer that skipped this target while it was muted-and-never-loaded, so
        // unmuting recomposes it and the load barrier finally opens the target.
        //
        // Runtime session-variable changes that newly *select* an unopened root
        // `${VAR}` sublayer — a mute exposing the root's own variable, or a session
        // `expressionVariables` edit (which reaches the cache through the change
        // pipeline, not here) — do not load it: they resolve root sublayers only
        // against already-interned layers. The open-time builder path loads the
        // initial selection (see `StageBuilder::session_expression_variables`);
        // reloading a newly-selected root sublayer at runtime would need an on-demand
        // sublayer open through the graph, left as remaining work.
        cache.invalidate_muting(&change.affected, &change.changed);
        Some(change.changed)
    }

    /// Fires [`StageSink::layer_muting_changed`] for the toggled identifier, after
    /// the graph and cache borrows are released.
    fn notify_muting_changed(&self, changed: &str, muted: bool) {
        for sink in self.sinks.borrow().iter() {
            sink.layer_muting_changed(self, changed, muted);
        }
    }

    /// Whether the layer with the given identifier is currently muted.
    pub fn is_layer_muted(&self, identifier: &str) -> bool {
        self.layers().is_layer_muted(identifier)
    }

    /// The currently muted layer identifiers, sorted for a deterministic result.
    pub fn muted_layers(&self) -> Vec<String> {
        self.layers().muted_layers()
    }

    /// Returns the stage's initial payload loading behavior, as requested at
    /// open time (`StageBuilder::load`). The live, runtime-mutable policy is
    /// [`load_rules`](Self::load_rules).
    pub fn initial_load_set(&self) -> InitialLoadSet {
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

    /// Whether an attribute's value may vary over time, the introspection behind
    /// [`Attribute::value_might_be_time_varying`](super::Attribute::value_might_be_time_varying).
    /// Reports `true` when the winning value source has more than one composed
    /// sample, and conservatively when that source is a value-clip set with more
    /// than one active clip — those clips can each contribute a different value
    /// even where the discrete sample count collapses to one (spec 12.3.4).
    pub fn value_might_be_time_varying(&self, attr_path: impl Into<sdf::Path>) -> Result<bool> {
        let attr_path = attr_path.into();
        self.masked(&attr_path, |g, c| c.value_might_be_time_varying(g, &attr_path))
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
        self.process_pending();
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
    pub(crate) fn has_spec(&self, path: &sdf::Path) -> Result<bool> {
        if !self.mask_includes(&path.prim_path()) {
            return Ok(false);
        }
        self.with_cache(|g, c| c.has_spec(g, path))
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
        query: impl FnMut(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T>,
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

    /// The raw `(layer id, sublayer offset)` members of `node`'s layer stack, in
    /// strength order (C++ `PcpNodeRef::GetLayerStack`'s layers and offsets). A
    /// composition [`Node`](pcp::Node) references its layer stack by handle and
    /// leaves the members to the cache, so this resolves them through the stage's
    /// layer graph for composition introspection. The offsets are the authored
    /// sublayer offsets; the arc time offset is read separately from the node's
    /// `map_to_root`.
    pub fn node_layer_stack(&self, node: &pcp::Node) -> Vec<(pcp::LayerId, sdf::LayerOffset)> {
        self.layers().layer_stack(node.layer_stack_id()).to_vec()
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

    /// Borrows the stage's composition cache, first draining any pending layer
    /// edits so the cache reflects every commit before it is read.
    pub(crate) fn cache(&self) -> Ref<'_, pcp::IndexCache> {
        self.process_pending();
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
    /// not auto-opened from disk — their edges resolve to nothing and contribute
    /// no opinions. Insert an already-opened sublayer stack when nested sublayers
    /// must load.
    //
    // TODO: open `layer`'s sublayer stack so its nested sublayers load (and
    // unresolved ones surface as `UnresolvedSublayer`), matching what
    // `StageBuilder::open` does for the root layer.
    pub fn insert_layer(
        &self,
        parent: &str,
        pos: usize,
        layer: sdf::Layer,
        offset: sdf::LayerOffset,
    ) -> Result<(), StageAuthoringError> {
        let identifier = layer.identifier().to_string();
        // Author the parent's metadata first; the child node is added only after
        // this succeeds (the authored asset path is a plain string, so the node
        // need not exist yet — only the later rebuild's edge resolution needs it).
        let edited = {
            let mut layers = self.layers.borrow_mut();
            let parent_id = layers.id_of(parent).ok_or_else(|| StageAuthoringError::LayerNotFound {
                layer: parent.to_string(),
            })?;
            let node = layers.get_mut(parent_id).expect("id_of returned a live id");
            self.edit_layer(&mut node.layer, None, |l| {
                l.pseudo_root_mut()
                    .map(|mut root| root.insert_sublayer(pos, identifier, offset))
            })
        };
        // Add the child node only once the parent edit succeeded, so a failed
        // insert never leaves an orphan node. `add_layer` interns it and attaches
        // the aggregator (skipping a duplicate identifier that collapses onto an
        // already-loaded node), the same path opening a stage uses.
        if edited.is_ok() {
            self.add_layer(layer);
        }
        self.process_pending();
        edited.map(|_| ())
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
    pub fn remove_layer(&self, parent: &str, child: &str) -> Result<bool, StageAuthoringError> {
        let edited = {
            let mut layers = self.layers.borrow_mut();
            let parent_id = layers.id_of(parent).ok_or_else(|| StageAuthoringError::LayerNotFound {
                layer: parent.to_string(),
            })?;
            // Resolve `child` to a layer id (an exact canonical identifier, or an
            // asset path authored relative to `parent`), then find the authored
            // `subLayers` entry that resolves to the same layer. An entry is
            // authored relative to `parent`, so anchoring it the way the load path
            // interned the sublayer makes the entry's canonical id comparable to
            // `child_id` even when the entry string differs from the canonical id.
            let authored = layers.find_relative(child, parent_id).and_then(|child_id| {
                let subs = layers.get(parent_id)?.layer.pseudo_root()?.sublayers()?.to_vec();
                subs.into_iter()
                    .find(|entry| layers.find_relative(entry, parent_id) == Some(child_id))
            });
            authored.map(|entry| {
                let node = layers.get_mut(parent_id).expect("parent_id is a live id");
                self.edit_layer(&mut node.layer, None, move |l| {
                    l.pseudo_root_mut()
                        .map(|mut root| root.remove_sublayer(&entry))
                        .map(|_| ())
                })
            })
        };
        // A removed entry changes `subLayers`, so a non-empty change set means a
        // sublayer was removed; no authored entry means nothing to remove.
        match edited {
            Some(edited) => {
                // `edit_layer` reports whether the edit changed anything.
                self.process_pending();
                edited
            }
            None => Ok(false),
        }
    }

    // TODO: the drain-on-read invariant (a graph or cache read drains pending
    // edits first) is enforced only by `layers`/`layers_mut`/`cache`; other
    // methods reach `self.layers`/`self.cache` through a raw `borrow()` and
    // hand-place `process_pending()`, so a new direct-borrow read path can
    // silently observe stale state. Making the `layers`/`cache` cells private
    // behind these draining accessors would fold "borrow the graph" and "graph is
    // current" into one operation and drop the scattered manual drains.
    /// Borrows the stage's layer graph, first draining any pending layer edits so
    /// the graph reflects every commit before it is read — a structural edit
    /// (sublayers, offsets, relocates) leaves the topology stale until then. The
    /// drain is a no-op when nothing is pending.
    pub(crate) fn layers(&self) -> Ref<'_, pcp::LayerGraph> {
        self.process_pending();
        self.layers.borrow()
    }

    /// Borrows the stage's layer graph mutably, for an authoring helper that
    /// edits its layers directly — e.g. the namespace editor's batched, atomic
    /// multi-layer edit. Drains pending edits first so the graph is current before
    /// it is re-authored; the caller drives composition invalidation from the new
    /// change lists through [`Self::process_pending`].
    pub(crate) fn layers_mut(&self) -> RefMut<'_, pcp::LayerGraph> {
        self.process_pending();
        self.layers.borrow_mut()
    }

    /// Runs a composed query that needs both the layer graph and the
    /// composition cache, driving on-demand layer loading to a fixpoint.
    ///
    /// Each pass borrows the layer graph shared and the cache mutably, mirroring
    /// how composition reads layer data through a `&LayerGraph` while lazily
    /// building the index. A reference or payload arc to a not-yet-loaded layer
    /// records a demand instead of composing (the index is left uncached); after
    /// the pass the borrows are released, the demanded layers are opened into the
    /// graph, and the query re-runs. The loop ends when a pass demands nothing,
    /// or when a demanded target cannot be opened (so loading makes no progress).
    /// Composition thus drives layer loading: an un-visited subtree never loads.
    pub(crate) fn with_cache<T>(
        &self,
        mut query: impl FnMut(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T>,
    ) -> Result<T> {
        self.process_pending();
        // Reused across passes: swapped with the cache's queue so neither
        // reallocates once warmed up.
        let mut pending: Vec<pcp::Demand> = Vec::new();
        loop {
            let result = {
                let graph = self.layers.borrow();
                let mut cache = self.cache.borrow_mut();
                let result = query(&graph, &mut cache);
                cache.swap_pending_loads(&mut pending);
                result
            };
            // The pass left a reference/payload arc uncomposed pending these
            // layers; open them and recompose. `load_demanded` reports false once a
            // pass neither loads a layer nor newly marks one failed, so the loop
            // ends after an unopenable target is marked failed and the following
            // pass recomposes its prim — recording the arc unresolved — without it.
            if pending.is_empty() || !self.load_demanded(&pending) {
                return result;
            }
            pending.clear();
        }
    }

    /// Opens the layers a composition pass demanded but that were not yet loaded.
    ///
    /// Each demanded asset path is opened together with its sublayer stack and
    /// interned through [`add_layer`](Self::add_layer), so the new layers join
    /// the graph with a change sink; the sublayer DAG is then rewired. A missing
    /// sublayer of an on-demand target is recorded as an
    /// [`UnresolvedSublayer`](pcp::Error::UnresolvedSublayer) collection error,
    /// matching root-stack collection so a lazily-reached stack reports the same
    /// diagnostics. A target that resolves but cannot be read or parsed is marked
    /// failed on the graph, so the next composition pass reports it
    /// [`UnresolvedLayer`](pcp::Error::UnresolvedLayer) (with the arc's site
    /// context) rather than demanding it again — otherwise the demanding prim's
    /// index would never cache.
    ///
    /// Returns whether the pass made progress — a layer joined or a target was
    /// newly marked failed — so the caller recomposes once more; a demanded path
    /// already loaded or already known failed is skipped.
    fn load_demanded(&self, pending: &[pcp::Demand]) -> bool {
        let before = self.layers.borrow().len();
        let sublayer_errors: RefCell<Vec<pcp::Error>> = RefCell::new(Vec::new());
        let mut newly_failed = false;
        let mut newly_interned = false;
        for demand in pending {
            let asset_path = demand.asset_path.as_str();
            // Whether the target needs opening, and `reload` whether it is a re-open
            // of an already-interned target reached by a new expression-variable
            // context with no contextual instance yet. A re-open (re)loads the
            // `${VAR}` sublayers the new context resolves — including ones nested
            // below a literal sublayer — that an earlier context's open left
            // unloaded. A target a prior open failed is not retried.
            let open = {
                let graph = self.layers.borrow();
                if graph.load_failed(asset_path) {
                    None
                } else {
                    match graph.id_of(asset_path) {
                        None => Some(false),
                        Some(target) if graph.needs_contextual_open(target, &demand.expr_vars) => Some(true),
                        Some(_) => None,
                    }
                }
            };
            if let Some(reload) = open {
                // The shared graph borrow is dropped before `add_layer` /
                // `mark_load_failed` take a mutable one. The arc anchored `asset_path`
                // to an absolute identifier, so no anchor is needed.
                let opened = {
                    let graph = self.layers.borrow();
                    graph.layer_registry().open_stack(
                        asset_path,
                        None,
                        &demand.expr_vars,
                        reload,
                        &|error| {
                            sublayer_errors.borrow_mut().push(error.into());
                            Ok(())
                        },
                        &|id| graph.id_of(id).is_some(),
                    )
                };
                match opened {
                    Ok(layers) => {
                        for layer in layers {
                            self.add_layer(layer);
                        }
                    }
                    Err(err) => {
                        self.layers.borrow_mut().mark_load_failed(asset_path, err.to_string());
                        newly_failed = true;
                        continue;
                    }
                }
            }
        }
        let errors = sublayer_errors.into_inner();
        if !errors.is_empty() {
            self.cache.borrow_mut().record_collection_errors(errors);
        }
        let grew = self.layers.borrow().len() != before;
        // Newly joined layers need their plain sublayer edges (and relocates) wired
        // before any stack is composed against them.
        if grew {
            // TODO(perf): rebuild only the new subtrees rather than the whole DAG.
            let relocated = self.layers.borrow_mut().recompute_sublayers(None);
            // A demanded layer that introduces relocates restructures prims
            // composed against its stack; drop their cached indices so they
            // recompose with the relocates applied.
            if !relocated.is_empty() {
                self.cache.borrow_mut().invalidate_layers(&relocated);
            }
        }
        // Mint each demand's layer stack now that the edges are wired. The layer
        // graph applies the plain-vs-contextual policy; `intern_external` is
        // idempotent, so a plain stack the rebuild above already minted, or a
        // context reached before, is left unchanged.
        for demand in pending {
            let root = self.layers.borrow().id_of(demand.asset_path.as_str());
            if let Some(root) = root {
                newly_interned |= self.layers.borrow_mut().intern_external(root, &demand.expr_vars).1;
            }
        }
        grew || newly_failed || newly_interned
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

/// Restores a stage's load rules on drop — the RAII half of
/// [`Stage::find_loadable`]'s transient `LoadRules::all()` swap, so the
/// original rules are reinstalled even if the walk between construction and
/// drop returns early on error.
struct LoadRulesGuard<'a> {
    stage: &'a Stage,
    original: pcp::LoadRules,
}

impl Drop for LoadRulesGuard<'_> {
    fn drop(&mut self) {
        self.stage.replace_load_rules(mem::take(&mut self.original));
    }
}

/// Builder for configuring and opening a [`Stage`].
///
/// Created via [`Stage::builder`]. Configures the [`LayerRegistry`] layers load
/// through (resolver + file formats) and composition options.
pub struct StageBuilder {
    registry: sdf::LayerRegistry,
    variant_fallbacks: pcp::VariantFallbackMap,
    session_layer: Option<String>,
    initial_load_set: InitialLoadSet,
    population_mask: StagePopulationMask,
    interpolation_type: InterpolationType,
    muted: HashSet<String>,
}

#[derive(Default)]
struct CollectedLayers {
    layers: Vec<sdf::Layer>,
    errors: Vec<pcp::Error>,
}

/// Whether a composition error is a sublayer load diagnostic — the only kind
/// [`Stage::composition_errors`] filters against the muted-aware effective set.
fn is_sublayer_error(error: &pcp::Error) -> bool {
    matches!(
        error,
        pcp::Error::UnresolvedSublayer { .. } | pcp::Error::MalformedSublayer { .. }
    )
}

impl StageBuilder {
    fn new() -> Self {
        Self {
            registry: sdf::LayerRegistry::default(),
            variant_fallbacks: pcp::VariantFallbackMap::new(),
            session_layer: None,
            initial_load_set: InitialLoadSet::LoadAll,
            population_mask: StagePopulationMask::all(),
            interpolation_type: InterpolationType::default(),
            muted: HashSet::new(),
        }
    }

    /// Sets the [`LayerRegistry`](sdf::LayerRegistry) the stage loads layers
    /// through — its resolver and (in the future) registered file formats.
    pub fn registry(mut self, registry: sdf::LayerRegistry) -> Self {
        self.registry = registry;
        self
    }

    /// Sets a custom asset resolver, wrapping it in a [`LayerRegistry`] over the
    /// built-in formats. A convenience over [`registry`](Self::registry).
    pub fn resolver<R: ar::Resolver + 'static>(mut self, resolver: R) -> Self {
        self.registry = sdf::LayerRegistry::new(Box::new(resolver));
        self
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

    /// Mutes the given layer identifiers at open time, so they contribute no
    /// opinions to the stage's first composition (see
    /// [`Stage::mute_layer`]). The root layer cannot be muted and a request to
    /// mute it is ignored. C++ has no open-time mute; this mirrors how
    /// [`variant_fallbacks`](Self::variant_fallbacks) and the population mask are
    /// threaded into the initial build.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::usd;
    ///
    /// let stage = usd::Stage::builder()
    ///     .mute(["override.usda"])
    ///     .open("scene.usda")
    ///     .unwrap();
    /// ```
    pub fn mute(mut self, identifiers: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.muted.extend(identifiers.into_iter().map(Into::into));
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
    pub fn open(self, root_path: &str) -> Result<Stage> {
        let session = self.collect_optional_session_layers()?;
        // Seed the root collection with the session layers' composed expression
        // variables (muted ones excluded): the session is part of the root layer
        // stack, so a `${VAR}` root sublayer the session resolves must be loaded
        // here — composition later resolves it against the same variables but can
        // only intern a layer this collection opened.
        let session_vars = self.session_expression_variables(root_path, &session.layers);
        let root = self.collect_layers(root_path, &session_vars)?;
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
    pub fn in_memory(self, identifier: impl Into<String>) -> Result<Stage> {
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

    /// Open the root layer named by `path` and its sublayer stack.
    ///
    /// References and payloads are not followed here — composition opens those
    /// target layers on demand (see [`Stage::with_cache`]), so the population
    /// mask prunes them naturally: a culled prim is never composed, so its arc
    /// targets are never demanded. A missing sublayer is recorded as an
    /// [`UnresolvedSublayer`](pcp::Error::UnresolvedSublayer) collection error
    /// rather than aborting the open; one under a muted branch is filtered out
    /// later, once the muted-aware graph exists (see
    /// [`StageBuilder::make_stage`](Self::make_stage)).
    fn collect_layers(&self, path: &str, ancestor_expr_vars: &HashMap<String, sdf::Value>) -> Result<CollectedLayers> {
        let errors = RefCell::new(Vec::new());
        // `ancestor_expr_vars` are the expression variables the enclosing context
        // contributes: the session layers' composed set for the root stack, empty
        // for the session stack itself (nothing sublayers it).
        let layers = self.registry.open_stack(
            path,
            None,
            ancestor_expr_vars,
            false,
            &|error| {
                errors.borrow_mut().push(error.into());
                Ok(())
            },
            &|_| false,
        )?;
        Ok(CollectedLayers {
            layers,
            errors: errors.into_inner(),
        })
    }

    /// Collect the configured session layer (and its dependencies), if any.
    fn collect_optional_session_layers(&self) -> Result<CollectedLayers> {
        match self.session_layer.as_deref() {
            Some(p) => self.collect_layers(p, &HashMap::new()),
            None => Ok(CollectedLayers::default()),
        }
    }

    /// The builder's requested mutes, canonicalized against the root layer the way
    /// the graph's muted set is (C++ `Pcp_MutedLayers::_GetCanonicalLayerId`): with
    /// a resolvable root anchor each spelling is resolved to the identifier its
    /// layer interns under, so any spelling of one layer collapses to one entry; an
    /// in-memory or anonymous root has no anchor, so the spelling passes through.
    /// Lets collection test a sublayer's interned identifier for muting before the
    /// graph exists. Empty when nothing is muted.
    fn canonical_muted_set(&self, root_path: &str) -> HashSet<String> {
        if self.muted.is_empty() {
            return HashSet::new();
        }
        let root_anchor = self
            .registry
            .resolve_layer(&self.registry.create_identifier(root_path, None));
        self.muted
            .iter()
            .map(|m| match root_anchor.as_ref() {
                Some(a) => self.registry.create_identifier(m, Some(a)),
                None => m.clone(),
            })
            .collect()
    }

    /// The composed expression variables of the *effective* session stack — the
    /// collected session layers minus any muted layer and the whole subtree it
    /// sublayers. A muted session opinion must not select the root's `${VAR}`
    /// sublayers, matching the graph's muted-aware resolution once the stage is
    /// built (the graph would otherwise re-resolve the sublayer to one this
    /// collection never opened). Pruning uses the shared
    /// [`muted_subtree`](pcp::muted_subtree) rule the graph applies over its
    /// resolved edges, walked here over the collected layers' authored sublayer
    /// paths so the two agree on the effective stack. Mutes and sublayer paths are
    /// canonicalized against the root / their layer the way the interned
    /// identifiers were, so any spelling of a muted layer is excluded. Expression-
    /// valued session sublayers are evaluated with the variables inherited from
    /// their session ancestors.
    fn session_expression_variables(
        &self,
        root_path: &str,
        session_layers: &[sdf::Layer],
    ) -> HashMap<String, sdf::Value> {
        if self.muted.is_empty() {
            return sdf::expr::compose_layer_variables(session_layers.iter().map(|l| l.data()));
        }
        let muted = self.canonical_muted_set(root_path);
        let mut scope = HashSet::new();
        for layer in session_layers {
            scope.insert(layer.identifier().to_string());
        }
        let mut contexts: HashMap<String, HashMap<String, sdf::Value>> = HashMap::new();
        let mut children: HashMap<String, Vec<String>> = HashMap::new();
        for layer in session_layers {
            let inherited = contexts.get(layer.identifier()).cloned().unwrap_or_default();
            let mut vars = sdf::expr::read_expression_variables(layer.data())
                .map(|vars| vars.into_owned())
                .unwrap_or_default();
            sdf::expr::compose_over(&mut vars, &inherited);
            let layer_children: Vec<String> = sdf::LayerRegistry::sublayer_paths(layer.data())
                .iter()
                .filter_map(|sub| sdf::expr::evaluate_asset_path(sub, &vars).ok())
                .map(|sub| self.registry.create_identifier_anchored(&sub, layer.real_path()))
                .collect();
            for child in &layer_children {
                contexts.entry(child.clone()).or_insert_with(|| vars.clone());
            }
            children.insert(layer.identifier().to_string(), layer_children);
        }
        let pruned = pcp::muted_subtree(&scope, scope.iter().filter(|id| muted.contains(*id)).cloned(), |id| {
            children.get(id).cloned().unwrap_or_default()
        });
        sdf::expr::compose_layer_variables(
            session_layers
                .iter()
                .filter(|l| !pruned.contains(l.identifier()))
                .map(|l| l.data()),
        )
    }

    /// Assemble a [`Stage`] from already-collected layers. Shared
    /// construction tail for [`StageBuilder::open`] and
    /// [`StageBuilder::in_memory`]; any new `Stage` field must be wired in
    /// here once. Crate-visible so tests can assemble a multi-layer stage
    /// (references, sublayers) from hand-built [`sdf::Layer`]s.
    pub(crate) fn make_stage(
        self,
        layers: Vec<sdf::Layer>,
        session_layer_count: usize,
        collection_errors: Vec<pcp::Error>,
    ) -> Stage {
        let load_rules = match self.initial_load_set {
            InitialLoadSet::LoadAll => pcp::LoadRules::all(),
            InitialLoadSet::LoadNone => pcp::LoadRules::none(),
        };
        // The root layer stack's identity, from the collected inputs: the root is
        // the first non-session layer, the session layer the first of any. The
        // graph below is populated layer by layer, so this is read from the inputs
        // rather than the (initially empty) graph.
        let layer_stack_id = pcp::LayerStackIdentifier {
            root_layer: layers
                .get(session_layer_count)
                .map(|l| l.identifier().to_string())
                .unwrap_or_default(),
            session_layer: (session_layer_count > 0).then(|| layers[0].identifier().to_string()),
            resolver: self.registry.identity(),
        };
        // The root layer is the strongest authoring target by default; an empty
        // stack names no layer, so the target resolves to nothing at author time.
        let edit_target = EditTarget {
            layer_stack: Some(layer_stack_id.clone()),
            ..EditTarget::for_layer(layer_stack_id.root_layer.clone())
        };
        // The graph keeps its own regenerable diagnostics (sublayer cycles,
        // invalid relocates); the cache holds only the one-shot collection errors.
        // `Stage::composition_errors` concatenates the two.
        let stage = Stage(Rc::new(StageInner {
            layers: RefCell::new(pcp::LayerGraph::new(self.registry)),
            cache: RefCell::new(pcp::IndexCache::new(
                self.variant_fallbacks,
                load_rules,
                collection_errors,
            )),
            initial_load_set: self.initial_load_set,
            population_mask: self.population_mask,
            interpolation_type: Cell::new(self.interpolation_type),
            edit_target: RefCell::new(edit_target),
            layer_stack_id,
            sinks: RefCell::default(),
            pending: RefCell::new(Vec::new()),
            edit_provenance: RefCell::new(None),
            current_generation: Cell::new(0),
        }));
        // Add every collected layer through the one join seam, so each gets its
        // change aggregator as it joins; then wire the sublayer DAG from the
        // authored `subLayers` metadata. The root is the first non-session layer;
        // a duplicate identifier (a dependency reached through both the session and
        // root collections) collapses onto one node, so only fresh session layers
        // count and the root is captured at its original slot.
        let mut root = None;
        let mut session_count = 0;
        for (i, layer) in layers.into_iter().enumerate() {
            let (id, fresh) = stage.add_layer(layer);
            if i == session_layer_count {
                root = Some(id);
            }
            if fresh && i < session_layer_count {
                session_count += 1;
            }
        }
        stage.layers.borrow_mut().finalize(session_count, root);
        if !self.muted.is_empty() {
            // Seed the graph's muted set (it drops any root-layer request and
            // re-resolves identifiers on each later rebuild). The cache is still
            // empty (composition is lazy), so no cache invalidation is needed yet.
            // The raw collection diagnostics stay as the loader recorded them; the
            // muted ones are filtered out at report time (`Stage::composition_errors`)
            // against the current composed state, so an unmute restores a diagnostic
            // a muted branch had hidden.
            stage.layers.borrow_mut().set_muted_identifiers(self.muted);
        }
        stage
    }
}

#[cfg(test)]
impl Stage {
    /// The number of installed [`StageSink`]s, for tests asserting a wrapper's
    /// recording sink is installed and later removed.
    pub(crate) fn sink_count(&self) -> usize {
        self.sinks.borrow().iter().count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Author through a layer's `edit` API and commit, for building test fixtures
    /// before they join a stage.
    fn edit_layer(layer: &mut sdf::Layer, f: impl FnOnce(&mut sdf::LayerEdit<'_>)) {
        layer
            .edit(|e| {
                f(e);
                Ok(())
            })
            .expect("authored");
    }

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
        edit_layer(&mut strong, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });

        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        edit_layer(&mut weak, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Mat", sdf::Specifier::Def, "Shader").unwrap();
            sdf::AttributeSpec::new(
                e.data_mut(),
                "/Mat.outputs:out",
                "color3f",
                sdf::Variability::Varying,
                true,
            )
            .unwrap();
            sdf::AttributeSpec::new(
                e.data_mut(),
                "/Mat.inputs:in",
                "color3f",
                sdf::Variability::Varying,
                true,
            )
            .unwrap()
            .set_connection_paths([target.clone()]);
        });

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
        edit_layer(&mut strong, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });

        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        edit_layer(&mut weak, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Mat", sdf::Specifier::Def, "Shader").unwrap();
            sdf::AttributeSpec::new(
                e.data_mut(),
                "/Mat.outputs:out",
                "color3f",
                sdf::Variability::Varying,
                true,
            )
            .unwrap();
            sdf::AttributeSpec::new(
                e.data_mut(),
                "/Mat.inputs:in",
                "color3f",
                sdf::Variability::Varying,
                true,
            )
            .unwrap()
            .set_connection_paths([target.clone()]);
        });

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
        edit_layer(&mut strong, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });

        let mut weak = sdf::Layer::new_in_memory("weak.usda");
        edit_layer(&mut weak, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Mat", sdf::Specifier::Def, "Shader").unwrap();
            sdf::AttributeSpec::new(
                e.data_mut(),
                "/Mat.outputs:out",
                "color3f",
                sdf::Variability::Varying,
                true,
            )
            .unwrap();
            sdf::AttributeSpec::new(
                e.data_mut(),
                "/Mat.inputs:in",
                "color3f",
                sdf::Variability::Varying,
                true,
            )
            .unwrap()
            .set_connection_paths([target.clone()]);
        });

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
        edit_layer(&mut layer, |e| {
            sdf::AttributeSpec::new(e.data_mut(), "/A.x", "double", sdf::Variability::Varying, true)
                .unwrap()
                .set_default(sdf::Value::Double(value));
        });
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
    fn insert_layer_keeps_loaded_node() -> Result<()> {
        // Build root → mid → leaf incrementally so `mid` is a loaded node with a
        // derived child edge to `leaf`, and `leaf`'s opinion composes.
        let stage = Stage::builder().in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        let mid = sdf::Layer::new_in_memory("mid.usda");
        let mid_id = mid.identifier().to_string();
        stage.insert_layer(&root_id, 0, mid, sdf::LayerOffset::IDENTITY)?;
        stage.insert_layer(&mid_id, 0, opinion_layer("leaf.usda", 5.0)?, sdf::LayerOffset::IDENTITY)?;
        assert_eq!(
            stage
                .attribute("/A.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(5.0))
        );

        // Re-insert `mid` by its identifier, passing a fresh empty layer with the
        // same identifier. The graph must keep the loaded `mid` (whose
        // `subLayers` still names `leaf`), so `leaf`'s opinion survives.
        stage.insert_layer(
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

    /// `remove_layer` resolves `child` to a layer before matching, so a
    /// sublayer authored with a relative path (whose canonical identifier — the
    /// resolved absolute path — differs from the authored entry) is still removed
    /// when named by the canonical identifier `sub_layers` returns.
    #[test]
    fn remove_layer_resolves_relative() -> Result<()> {
        // root.usda authors `subLayers = [@./sub.usda@]`; sub.usda sits beside it
        // on disk. The sublayer is interned under its absolute identifier, which
        // differs from the authored `./sub.usda`, and `remove_layer` anchors the
        // authored entry against root to match it.
        let tmp = tempfile::tempdir()?;
        let root_path = tmp.path().join("root.usda");
        let sub_path = tmp.path().join("sub.usda");

        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["./sub.usda"]);
        });
        root.export(root_path.to_string_lossy())?;
        opinion_layer("sub.usda", 5.0)?.export(sub_path.to_string_lossy())?;

        let stage = Stage::open(&root_path.to_string_lossy())?;
        assert_eq!(
            stage
                .attribute("/A.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(5.0)),
            "the relative sublayer composes its opinion"
        );

        // sub_layers reports the canonical absolute identifier, not the authored
        // `./sub.usda` string.
        let root_id = stage.root_layer().identifier().to_string();
        let sub_canonical = stage
            .sub_layers(&root_id)
            .into_iter()
            .find(|id| id != &root_id)
            .expect("the sublayer is in the stack");
        assert_ne!(
            sub_canonical, "./sub.usda",
            "the canonical id differs from the authored entry"
        );

        // Removing by that canonical identifier must still drop the relative
        // `./sub.usda` entry (exact-string matching would have missed it).
        assert!(
            stage.remove_layer(&root_id, &sub_canonical)?,
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

    /// Builds a stage where `/P` references a shared target with no expression
    /// variables and `/Q` reaches the same target through `middle.usda` (which
    /// defines `V = "chosen"`), composes `/P` first so the target loads unseeded,
    /// and asserts the target's `${V}` sublayer (resolving to `chosen.usda`, which
    /// overrides `/T.x` to 42) still contributes to `/Q`. `target_layers` supplies
    /// `target.usda` and any layer it sublayers. Returns the composed stage so a
    /// caller can make further assertions over it.
    fn assert_shared_target_seeds_later_arc(target_layers: &[(&str, &str)]) -> Result<Stage> {
        let tmp = tempfile::tempdir()?;
        let write = |name: &str, body: &str| std::fs::write(tmp.path().join(name), body);
        write(
            "root.usda",
            r#"#usda 1.0
def "P" (
    references = @./target.usda@</T>
) {
}
def "Q" (
    references = @./middle.usda@</Q>
) {
}
"#,
        )?;
        write(
            "middle.usda",
            r#"#usda 1.0
(
    expressionVariables = {
        string V = "chosen"
    }
)
def "Q" (
    references = @./target.usda@</T>
) {
}
"#,
        )?;
        write(
            "chosen.usda",
            r#"#usda 1.0
over "T" {
    custom double x = 42
}
"#,
        )?;
        for &(name, body) in target_layers {
            write(name, body)?;
        }

        let stage = Stage::open(&tmp.path().join("root.usda").to_string_lossy())?;
        // Compose `/P` first, loading the shared target under the empty (no
        // variable) context.
        let _ = stage
            .attribute("/P.x")
            .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?;
        // `/Q` reaches the same target carrying `V=chosen`; the target's `${V}`
        // sublayer must resolve and contribute `chosen.usda`'s opinion.
        assert_eq!(
            stage
                .attribute("/Q.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(42.0)),
            "the later variable-carrying arc seeds the shared target's ${{V}} sublayer",
        );
        Ok(stage)
    }

    /// A reference target shared by two arcs resolves its `${VAR}` sublayer
    /// against a later variable-carrying arc even when an earlier variable-free
    /// arc interned it first (the `${V}` sublayer is authored on the target root).
    #[test]
    fn shared_target_seeds_later_var_arc() -> Result<()> {
        assert_shared_target_seeds_later_arc(&[(
            "target.usda",
            r#"#usda 1.0
(
    subLayers = [
        @`"./${V}.usda"`@
    ]
)
def "T" {
}
"#,
        )])
        .map(|_| ())
    }

    /// As [`shared_target_seeds_later_var_arc`], but the `${VAR}` sublayer is
    /// nested below the target root, under a literal sublayer (`mid.usda`). The
    /// re-seed must scan the whole subtree to demand a re-open, and the re-open
    /// must re-walk the already-present `mid.usda` to load the now-resolvable
    /// `chosen.usda`.
    #[test]
    fn shared_target_seeds_nested_var_sublayer() -> Result<()> {
        assert_shared_target_seeds_later_arc(&[
            (
                "target.usda",
                r#"#usda 1.0
(
    subLayers = [
        @./mid.usda@
    ]
)
def "T" {
}
"#,
            ),
            (
                "mid.usda",
                r#"#usda 1.0
(
    subLayers = [
        @`"./${V}.usda"`@
    ]
)
"#,
            ),
        ])
        .map(|_| ())
    }

    /// A variable-free arc to a shared `${VAR}`-sublayer target stays isolated from
    /// another arc that reached the same target carrying a variable, even when the
    /// variable-carrying arc composed first. Each arc resolves the `${V}` sublayer
    /// against its own inherited context, so `/P` (no variable) does not pick up
    /// `/Q`'s `V=chosen` sublayer and `/P.x` stays absent.
    #[test]
    fn shared_target_contexts_isolated() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let write = |name: &str, body: &str| std::fs::write(tmp.path().join(name), body);
        write(
            "root.usda",
            r#"#usda 1.0
def "P" (
    references = @./target.usda@</T>
) {
}
def "Q" (
    references = @./middle.usda@</Q>
) {
}
"#,
        )?;
        write(
            "middle.usda",
            r#"#usda 1.0
(
    expressionVariables = {
        string V = "chosen"
    }
)
def "Q" (
    references = @./target.usda@</T>
) {
}
"#,
        )?;
        write(
            "target.usda",
            r#"#usda 1.0
(
    subLayers = [
        @`"./${V}.usda"`@
    ]
)
def "T" {
}
"#,
        )?;
        write(
            "chosen.usda",
            r#"#usda 1.0
over "T" {
    custom double x = 42
}
"#,
        )?;

        let stage = Stage::open(&tmp.path().join("root.usda").to_string_lossy())?;
        // Compose `/Q` first: it reaches the target carrying `V=chosen`, so the
        // target's `${V}` sublayer resolves to `chosen.usda`.
        assert_eq!(
            stage
                .attribute("/Q.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(42.0)),
            "the variable-carrying arc resolves the `${{V}}` sublayer",
        );
        // `/P` reaches the same target with no variable. Its `${V}` sublayer cannot
        // resolve, so `/P.x` stays absent — not polluted by `/Q`'s context.
        assert_eq!(
            stage
                .attribute("/P.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            None,
            "the variable-free arc is isolated from the other arc's context",
        );
        Ok(())
    }

    /// A target shared by a variable-free arc and a later variable-carrying arc
    /// re-opens under the second arc's context to reach its `${V}` sublayer. That
    /// re-walk re-visits the target's genuinely-missing `missing.usda` sublayer,
    /// but the diagnostic is recorded once, not once per open.
    #[test]
    fn shared_target_error_once() -> Result<()> {
        let stage = assert_shared_target_seeds_later_arc(&[(
            "target.usda",
            r#"#usda 1.0
(
    subLayers = [
        @./missing.usda@,
        @`"./${V}.usda"`@
    ]
)
def "T" {
}
"#,
        )])?;
        let reported = stage
            .composition_errors()
            .into_iter()
            .filter(|e| e.to_string().contains("missing.usda"))
            .count();
        assert_eq!(reported, 1, "the missing sublayer is reported once across both opens");
        Ok(())
    }

    /// An in-memory stage whose root authors a `./`-relative sublayer composes
    /// it: the dot-relative entry normalizes to the child's interned identifier
    /// (C++ `ArResolver::CreateIdentifier` drops `.` via `TfNormPath`), so the
    /// edge forms even though the child is an in-memory layer with no file to
    /// canonicalize against.
    #[test]
    fn dot_relative_sublayer_in_memory() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["./sub.usda"]);
        });
        let stage = Stage::builder().make_stage(vec![root, opinion_layer("sub.usda", 5.0)?], 0, Vec::new());
        assert_eq!(
            stage
                .attribute("/A.x")
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(5.0)),
            "the dot-relative sublayer composes its opinion"
        );
        Ok(())
    }

    /// Reads the composed `/A.x` default value as an `f64`, for the muting tests.
    fn read_ax(stage: &Stage) -> Result<Option<f64>> {
        stage.attribute("/A.x").get_at::<f64>(crate::usd::TimeCode::new(0.0))
    }

    /// A root layer sublayering each `(identifier, value)` opinion in strength
    /// order, followed by the opinion sublayers — the layer list for `make_stage`
    /// or a configured builder in the muting tests.
    fn sublayer_layers(opinions: &[(&str, f64)]) -> Result<Vec<sdf::Layer>> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut()
                .unwrap()
                .set_sublayers(opinions.iter().map(|(id, _)| *id));
        });
        let mut layers = vec![root];
        for &(id, value) in opinions {
            layers.push(opinion_layer(id, value)?);
        }
        Ok(layers)
    }

    /// Muting a sublayer suppresses its opinions, so a stronger value falls back
    /// to the weaker sublayer; unmuting restores the stronger opinion.
    #[test]
    fn mute_sublayer_drops_opinions() -> Result<()> {
        let stage = Stage::builder().make_stage(
            sublayer_layers(&[("strong.usda", 9.0), ("weak.usda", 5.0)])?,
            0,
            Vec::new(),
        );
        assert_eq!(read_ax(&stage)?, Some(9.0));

        stage.mute_layer("strong.usda");
        assert!(stage.is_layer_muted("strong.usda"));
        assert_eq!(read_ax(&stage)?, Some(5.0), "value falls back to the weaker sublayer");

        stage.unmute_layer("strong.usda");
        assert!(!stage.is_layer_muted("strong.usda"));
        assert_eq!(read_ax(&stage)?, Some(9.0), "unmuting restores the stronger opinion");
        Ok(())
    }

    /// Muting a session layer suppresses its pseudo-root stage metadata too, so
    /// `startTimeCode` falls back to the root layer's opinion.
    #[test]
    fn mute_session_metadata() -> Result<()> {
        let mut session = sdf::Layer::new_in_memory("session.usda");
        edit_layer(&mut session, |e| {
            e.set_start_time_code(10.0).unwrap();
        });
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.set_start_time_code(1.0).unwrap();
        });
        let stage = Stage::builder().make_stage(vec![session, root], 1, Vec::new());
        assert_eq!(stage.start_time_code(), 10.0, "the session opinion wins");

        stage.mute_layer("session.usda");
        assert_eq!(
            stage.start_time_code(),
            1.0,
            "muting the session falls back to the root opinion"
        );
        Ok(())
    }

    /// Muting a session layer prunes its whole sublayer subtree, not just the
    /// session layer itself, so a sublayer's opinion disappears too.
    #[test]
    fn mute_session_prunes_subtree() -> Result<()> {
        let mut session = sdf::Layer::new_in_memory("session.usda");
        edit_layer(&mut session, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["subsession.usda"]);
        });
        let subsession = opinion_layer("subsession.usda", 7.0)?;
        let root = sdf::Layer::new_in_memory("root.usda");
        let stage = Stage::builder().make_stage(vec![session, subsession, root], 2, Vec::new());
        assert_eq!(read_ax(&stage)?, Some(7.0), "the session sublayer contributes");

        stage.mute_layer("session.usda");
        assert_eq!(
            read_ax(&stage)?,
            None,
            "muting the session layer prunes its sublayer subtree"
        );

        stage.unmute_layer("session.usda");
        assert_eq!(read_ax(&stage)?, Some(7.0), "unmuting restores the subtree");
        Ok(())
    }

    /// A session-layer opinion disappears when the session layer is muted.
    #[test]
    fn mute_session_layer() -> Result<()> {
        let session = opinion_layer("session.usda", 7.0)?;
        let root = sdf::Layer::new_in_memory("root.usda");
        let stage = Stage::builder().make_stage(vec![session, root], 1, Vec::new());
        assert_eq!(read_ax(&stage)?, Some(7.0));

        stage.mute_layer("session.usda");
        assert_eq!(read_ax(&stage)?, None, "the muted session layer contributes nothing");
        Ok(())
    }

    /// Muting the root layer is rejected: it stays unmuted and composition is
    /// unchanged.
    #[test]
    fn mute_root_rejected() -> Result<()> {
        let stage = Stage::builder().make_stage(vec![opinion_layer("root.usda", 3.0)?], 0, Vec::new());
        let root_id = stage.root_layer().identifier().to_string();

        stage.mute_layer(root_id.clone());
        assert!(!stage.is_layer_muted(&root_id), "the root layer cannot be muted");
        assert!(stage.muted_layers().is_empty());
        assert_eq!(read_ax(&stage)?, Some(3.0), "composition is unchanged");
        Ok(())
    }

    /// Muting a sublayer that itself has sublayers prunes the whole subtree.
    #[test]
    fn mute_prunes_subtree() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["mid.usda"]);
        });
        let mut mid = sdf::Layer::new_in_memory("mid.usda");
        edit_layer(&mut mid, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["leaf.usda"]);
        });
        let stage = Stage::builder().make_stage(vec![root, mid, opinion_layer("leaf.usda", 5.0)?], 0, Vec::new());
        assert_eq!(read_ax(&stage)?, Some(5.0));

        stage.mute_layer("mid.usda");
        assert_eq!(read_ax(&stage)?, None, "the muted layer's whole subtree is pruned");

        stage.unmute_layer("mid.usda");
        assert_eq!(read_ax(&stage)?, Some(5.0));
        Ok(())
    }

    /// Muting bumps the cache revision, so an [`AttributeQuery`] built before the
    /// mute returns the new composed value afterward.
    #[test]
    fn mute_bumps_revision() -> Result<()> {
        let stage = Stage::builder().make_stage(
            sublayer_layers(&[("strong.usda", 9.0), ("weak.usda", 5.0)])?,
            0,
            Vec::new(),
        );
        let query = stage.attribute("/A.x").query();
        assert_eq!(query.get_at::<f64>(crate::usd::TimeCode::new(0.0))?, Some(9.0));

        stage.mute_layer("strong.usda");
        assert_eq!(
            query.get_at::<f64>(crate::usd::TimeCode::new(0.0))?,
            Some(5.0),
            "the pre-mute query reflects the post-mute value"
        );
        Ok(())
    }

    /// Muting an identifier not present in the stage stores it without panicking
    /// and leaves composition unchanged.
    #[test]
    fn mute_unknown_identifier_noop() -> Result<()> {
        let stage = Stage::builder().make_stage(vec![opinion_layer("root.usda", 3.0)?], 0, Vec::new());
        stage.mute_layer("nonexistent.usda");
        assert!(stage.is_layer_muted("nonexistent.usda"));
        assert_eq!(read_ax(&stage)?, Some(3.0), "an unmatched mute changes nothing");
        Ok(())
    }

    /// `mute_layer` / `unmute_layer` are reflected by `is_layer_muted` and
    /// `muted_layers`.
    #[test]
    fn muted_layers_roundtrip() -> Result<()> {
        let stage = Stage::builder().make_stage(sublayer_layers(&[("a.usda", 1.0), ("b.usda", 2.0)])?, 0, Vec::new());
        stage.mute_layer("a.usda");
        stage.mute_layer("b.usda");
        assert_eq!(stage.muted_layers(), vec!["a.usda".to_string(), "b.usda".to_string()]);
        assert!(stage.is_layer_muted("a.usda"));

        stage.unmute_layer("a.usda");
        assert_eq!(stage.muted_layers(), vec!["b.usda".to_string()]);
        assert!(!stage.is_layer_muted("a.usda"));
        Ok(())
    }

    /// Muting an identifier before its layer is loaded takes effect once a later
    /// `insert_layer` interns a matching layer; unmuting restores it.
    #[test]
    fn mute_before_load_excludes() -> Result<()> {
        let stage = Stage::builder().in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();

        stage.mute_layer("late.usda");
        assert!(stage.is_layer_muted("late.usda"));

        stage.insert_layer(
            &root_id,
            0,
            opinion_layer("late.usda", 5.0)?,
            sdf::LayerOffset::IDENTITY,
        )?;
        assert_eq!(
            read_ax(&stage)?,
            None,
            "a layer muted before loading is excluded once interned"
        );

        stage.unmute_layer("late.usda");
        assert_eq!(read_ax(&stage)?, Some(5.0), "unmuting restores the now-loaded layer");
        Ok(())
    }

    /// An anonymous layer is muted by its `anon:` identifier even in a filesystem
    /// stage: it has no asset-resolvable location, so canonicalization passes the
    /// identifier through (C++ `_GetCanonicalLayerId`) rather than anchoring it
    /// against the root.
    #[test]
    fn mute_anonymous_sublayer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root_path = dir.path().join("root.usda");
        std::fs::write(&root_path, "#usda 1.0\n")?;
        let stage = Stage::open(root_path.to_str().unwrap())?;
        let root_id = stage.root_layer().identifier().to_string();

        let mut anon = sdf::Layer::new_anonymous("opinion.usda");
        edit_layer(&mut anon, |e| {
            sdf::AttributeSpec::new(e.data_mut(), "/A.x", "double", sdf::Variability::Varying, true)
                .unwrap()
                .set_default(sdf::Value::Double(5.0));
        });
        let anon_id = anon.identifier().to_string();
        stage.insert_layer(&root_id, 0, anon, sdf::LayerOffset::IDENTITY)?;
        assert_eq!(read_ax(&stage)?, Some(5.0), "the anonymous sublayer contributes");

        stage.mute_layer(anon_id.clone());
        assert!(
            stage.is_layer_muted(&anon_id),
            "the anonymous layer reads as muted by its id"
        );
        assert_eq!(
            read_ax(&stage)?,
            None,
            "muting the anonymous sublayer drops its opinion"
        );

        stage.unmute_layer(&anon_id);
        assert_eq!(read_ax(&stage)?, Some(5.0), "unmuting restores it");
        Ok(())
    }

    /// Muting a layer that is a reference target skips the arc without panicking
    /// (its `sublayer_stack` is empty); unmuting restores the referenced opinion.
    #[test]
    fn mute_reference_target() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/P", sdf::Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &sdf::path("/P").unwrap(),
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "target.usda".into(),
                    prim_path: sdf::path("/Target").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Target", sdf::Specifier::Def, "").unwrap();
            sdf::AttributeSpec::new(e.data_mut(), "/Target.x", "double", sdf::Variability::Varying, true)
                .unwrap()
                .set_default(sdf::Value::Double(5.0));
        });

        let stage = Stage::builder().make_stage(vec![root, target], 0, Vec::new());
        let read_px = |stage: &Stage| stage.attribute("/P.x").get_at::<f64>(crate::usd::TimeCode::new(0.0));
        assert_eq!(read_px(&stage)?, Some(5.0), "the reference brings /Target.x to /P.x");

        stage.mute_layer("target.usda");
        assert_eq!(
            read_px(&stage)?,
            None,
            "muting the reference target drops the arc without panic"
        );

        stage.unmute_layer("target.usda");
        assert_eq!(read_px(&stage)?, Some(5.0), "unmuting restores the referenced opinion");
        Ok(())
    }

    /// Toggling a reference target's mute recomposes only the prims that reach it:
    /// the referencing prim's index is dropped while a sibling that does not
    /// depend on the target keeps its cached index.
    #[test]
    fn mute_keeps_independent_index() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", sdf::Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &sdf::path("/Ref").unwrap(),
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "target.usda".into(),
                    prim_path: sdf::path("/Target").unwrap(),
                    ..Default::default()
                }])),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Indep", sdf::Specifier::Def, "").unwrap();
        });
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Target", sdf::Specifier::Def, "").unwrap();
        });

        let stage = Stage::builder().make_stage(vec![root, target], 0, Vec::new());
        let (refp, indep) = (sdf::path("/Ref")?, sdf::path("/Indep")?);
        // Force both prim indices into the cache.
        assert!(stage.prim(refp.clone()).is_valid()?);
        assert!(stage.prim(indep.clone()).is_valid()?);
        assert!(stage.is_indexed(&refp) && stage.is_indexed(&indep));

        stage.mute_layer("target.usda");
        assert!(!stage.is_indexed(&refp), "the referencing prim is recomposed");
        assert!(stage.is_indexed(&indep), "the independent prim keeps its cached index");

        // Rebuild the referencing prim's index (now recording the muted target),
        // then unmute and confirm it is dropped again while the sibling stays warm.
        assert!(stage.prim(refp.clone()).is_valid()?);
        stage.unmute_layer("target.usda");
        assert!(!stage.is_indexed(&refp), "unmuting recomposes the referencing prim");
        assert!(stage.is_indexed(&indep), "unmuting leaves the independent prim cached");
        Ok(())
    }

    /// A prim whose only opinion lives in a sublayer of the root composes into a
    /// single local node on the stage Root layer stack, which the reverse
    /// `layer → indices` map registers under every member layer the node spans
    /// (`session`, `root`, and the `child` sublayer). Muting `child` fans out to
    /// `{child, root}`, so the index is found through its `child` registration
    /// even though the stack's strongest member is the unaffected session layer.
    /// Registering only the stack's strongest member would leave this index stale.
    #[test]
    fn mute_sublayer_drops_root_stack_index() -> Result<()> {
        let session = sdf::Layer::new_in_memory("session.usda");
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["child.usda"]);
        });
        let mut child = sdf::Layer::new_in_memory("child.usda");
        edit_layer(&mut child, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/P", sdf::Specifier::Def, "").unwrap();
        });

        // session at index 0, root + its `child` sublayer after: /P's Root node
        // spans [session, root, child].
        let stage = Stage::builder().make_stage(vec![session, root, child], 1, Vec::new());
        let p = sdf::path("/P")?;
        assert!(stage.prim(p.clone()).is_valid()?);
        assert!(stage.is_indexed(&p), "the sublayer opinion composes and caches");

        stage.mute_layer("child.usda");
        assert!(
            !stage.is_indexed(&p),
            "muting the root sublayer holding /P's opinion drops the cached index"
        );
        Ok(())
    }

    /// A `subLayers` edit scopes its invalidation to the stacks the edited layer
    /// belongs to: editing a reference target's sublayer stack drops the
    /// referencing prim's index (its composition reads that target) while a prim
    /// composed only from the root stack keeps its cached index. A blanket cache
    /// clear would drop both.
    #[test]
    fn edit_keeps_independent_index() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", sdf::Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &sdf::path("/Ref").unwrap(),
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "target.usda".into(),
                    prim_path: sdf::path("/Target").unwrap(),
                    ..Default::default()
                }])),
            );
            sdf::PrimSpec::new(e.data_mut(), "/Indep", sdf::Specifier::Def, "").unwrap();
        });
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Target", sdf::Specifier::Def, "").unwrap();
        });

        let stage = Stage::builder().make_stage(vec![root, target], 0, Vec::new());
        let (refp, indep) = (sdf::path("/Ref")?, sdf::path("/Indep")?);
        // Force both prim indices into the cache (querying /Ref loads the target).
        assert!(stage.prim(refp.clone()).is_valid()?);
        assert!(stage.prim(indep.clone()).is_valid()?);
        assert!(stage.is_indexed(&refp) && stage.is_indexed(&indep));

        // Edit the reference target's sublayer stack — only /Ref reads it.
        let extra = sdf::Layer::new_in_memory("extra.usda");
        stage.insert_layer("target.usda", 0, extra, sdf::LayerOffset::IDENTITY)?;
        assert!(
            !stage.is_indexed(&refp),
            "the referencing prim recomposes against the edited target stack"
        );
        assert!(stage.is_indexed(&indep), "the independent prim keeps its cached index");
        Ok(())
    }

    /// Editing a reference target's sublayer stack re-resolves that target's stack
    /// instance, so the referencing prim recomposes against the inserted sublayer's
    /// stronger opinion.
    #[test]
    fn target_edit_recomposes_ref() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", sdf::Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &sdf::path("/Ref").unwrap(),
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "target.usda".into(),
                    prim_path: sdf::path("/A").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/A", sdf::Specifier::Def, "").unwrap();
            e.pseudo_root_mut().unwrap().set_sublayers(["base.usda"]);
        });

        let stage = Stage::builder().make_stage(vec![root, target, opinion_layer("base.usda", 1.0)?], 0, Vec::new());
        let ref_x = || stage.attribute("/Ref.x").get::<f64>();
        assert_eq!(ref_x()?, Some(1.0), "the reference target's sublayer opinion composes");

        // Insert a stronger sublayer into the target's stack; the referencing prim
        // must recompose against the re-resolved target stack.
        stage.insert_layer(
            "target.usda",
            0,
            opinion_layer("over.usda", 2.0)?,
            sdf::LayerOffset::IDENTITY,
        )?;
        assert_eq!(
            ref_x()?,
            Some(2.0),
            "editing the target's subLayers re-resolves its stack and recomposes the referencing prim"
        );
        Ok(())
    }

    /// A `subLayers` edit that introduces a previously-absent prim invalidates its
    /// cached negative result, so the prim becomes visible: the cached miss composed
    /// against the edited layer's stack, so the scoped layer-set drop reaches it.
    #[test]
    fn edit_revives_missing_prim() -> Result<()> {
        let root = sdf::Layer::new_in_memory("root.usda");
        let stage = Stage::builder().make_stage(vec![root], 0, Vec::new());
        let newp = sdf::path("/New")?;
        // Query the absent prim, caching a negative (empty) index.
        assert!(!stage.prim(newp.clone()).is_valid()?, "the prim is absent");
        assert!(stage.is_indexed(&newp), "the miss is cached");

        // Add a root sublayer that defines the prim.
        let mut over = sdf::Layer::new_in_memory("over.usda");
        edit_layer(&mut over, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/New", sdf::Specifier::Def, "").unwrap();
        });
        stage.insert_layer("root.usda", 0, over, sdf::LayerOffset::IDENTITY)?;
        assert!(
            stage.prim(newp.clone()).is_valid()?,
            "the subLayers edit invalidates the cached miss and the prim becomes visible"
        );
        Ok(())
    }

    /// A cached miss for a reference descendant is invalidated when the reference
    /// target's sublayer stack gains a spec for it — the decisive case, since the
    /// miss's only tie to the edited layer is its arc node, not its root-stack
    /// local node.
    #[test]
    fn target_edit_revives_descendant() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Ref", sdf::Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &sdf::path("/Ref").unwrap(),
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "target.usda".into(),
                    prim_path: sdf::path("/T").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/T", sdf::Specifier::Def, "").unwrap();
        });

        let stage = Stage::builder().make_stage(vec![root, target], 0, Vec::new());
        let missing = sdf::path("/Ref/Missing")?;
        assert!(
            !stage.prim(missing.clone()).is_valid()?,
            "the reference descendant is absent"
        );
        assert!(stage.is_indexed(&missing), "the miss is cached");

        // Add a sublayer to the target that defines the missing prim.
        let mut over = sdf::Layer::new_in_memory("over.usda");
        edit_layer(&mut over, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/T", sdf::Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/T/Missing", sdf::Specifier::Def, "").unwrap();
        });
        stage.insert_layer("target.usda", 0, over, sdf::LayerOffset::IDENTITY)?;
        assert!(
            stage.prim(missing.clone()).is_valid()?,
            "editing the target's subLayers invalidates the cached reference-descendant miss"
        );
        Ok(())
    }

    /// Editing the root layer's `timeCodesPerSecond` re-scales the sublayer edge
    /// offsets, so a time-sampled value from a sublayer at a different rate
    /// recomposes to the value a fresh open at the new rate produces.
    #[test]
    fn tcps_edit_rescales_samples() -> Result<()> {
        let build = |root_tcps: f64| -> Stage {
            let mut root = sdf::Layer::new_in_memory("root.usda");
            edit_layer(&mut root, |e| {
                let mut pr = e.pseudo_root_mut().unwrap();
                pr.set_sublayers(["sub.usda"]);
                pr.set_time_codes_per_second(root_tcps);
            });
            let mut sub = sdf::Layer::new_in_memory("sub.usda");
            edit_layer(&mut sub, |e| {
                e.pseudo_root_mut().unwrap().set_time_codes_per_second(2.0);
                let mut x =
                    sdf::AttributeSpec::new(e.data_mut(), "/A.x", "double", sdf::Variability::Varying, true).unwrap();
                x.set_time_sample(0.0, sdf::Value::Double(0.0));
                x.set_time_sample(20.0, sdf::Value::Double(200.0));
            });
            Stage::builder().make_stage(vec![root, sub], 0, Vec::new())
        };
        let read = |s: &Stage| s.attribute("/A.x").get_at::<f64>(crate::usd::TimeCode::new(8.0));

        let stage = build(1.0);
        let before = read(&stage)?;
        stage.set_time_codes_per_second(2.0)?;
        let after = read(&stage)?;
        let fresh = read(&build(2.0))?;

        assert_ne!(before, fresh, "the root rate changes the retimed sample value");
        assert_eq!(
            after, fresh,
            "editing timeCodesPerSecond recomposes the sublayer offset to the fresh-open value"
        );
        Ok(())
    }

    /// Editing the root layer's `expressionVariables` re-expands a `${VAR}`
    /// sublayer asset path, so the cached prim index recomposes against the newly
    /// named sublayer — the correctness gap the expression-variable invalidation
    /// closes (a stale read before the fix).
    #[test]
    fn expr_var_edit_recomposes_sublayer() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            let mut pr = e.pseudo_root_mut().unwrap();
            pr.set_expression_variables(HashMap::from([("WHICH".to_string(), sdf::Value::String("a".into()))]));
            pr.set_sublayers([r#"`"${WHICH}.usda"`"#]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("a.usda", 1.0)?, opinion_layer("b.usda", 2.0)?],
            0,
            Vec::new(),
        );

        assert_eq!(
            stage.attribute("/A.x").get::<f64>()?,
            Some(1.0),
            "the WHICH-valued sublayer resolves to a.usda"
        );
        stage.set_expression_variables(HashMap::from([("WHICH".to_string(), sdf::Value::String("b".into()))]))?;
        assert_eq!(
            stage.attribute("/A.x").get::<f64>()?,
            Some(2.0),
            "editing WHICH re-expands the sublayer to b.usda and recomposes the cached index"
        );
        Ok(())
    }

    /// A `${VAR}` sublayer in the root layer resolves against an expression
    /// variable authored on the *session* layer: the session is part of the root
    /// layer stack, so its variables seed the root's sublayer expansion — the same
    /// composition a `${VAR}` reference already gets.
    #[test]
    fn session_var_resolves_sublayer() -> Result<()> {
        let mut session = sdf::Layer::new_in_memory("session.usda");
        edit_layer(&mut session, |e| {
            e.pseudo_root_mut()
                .unwrap()
                .set_expression_variables(HashMap::from([("WHICH".to_string(), sdf::Value::String("a".into()))]));
        });
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${WHICH}.usda"`"#]);
        });
        let stage = Stage::builder().make_stage(
            vec![
                session,
                root,
                opinion_layer("a.usda", 1.0)?,
                opinion_layer("b.usda", 2.0)?,
            ],
            1,
            Vec::new(),
        );

        assert_eq!(
            stage.attribute("/A.x").get::<f64>()?,
            Some(1.0),
            "the root sublayer expression resolves against the session layer's WHICH variable"
        );
        Ok(())
    }

    /// A builder-requested mute takes effect on the first composition, and a
    /// builder mute of the root layer is dropped.
    #[test]
    fn builder_mute_at_open() -> Result<()> {
        let stage = Stage::builder().mute(["strong.usda", "root.usda"]).make_stage(
            sublayer_layers(&[("strong.usda", 9.0), ("weak.usda", 5.0)])?,
            0,
            Vec::new(),
        );
        assert!(stage.is_layer_muted("strong.usda"));
        assert!(
            !stage.is_layer_muted("root.usda"),
            "a builder mute of the root is dropped"
        );
        assert_eq!(
            read_ax(&stage)?,
            Some(5.0),
            "the muted sublayer is excluded from the start"
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
        stage.insert_layer(&root, 0, sub, sdf::LayerOffset::IDENTITY)?;

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

    /// A direct `layer_mut` edit to `subLayers` rebuilds the graph's edges before
    /// any graph query observes it: `sub_layers` reflects the removal with no
    /// intervening composed read to trigger the flush.
    #[test]
    fn raw_sublayer_edit_current() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak1.usda", "weak2.usda"]);
        });
        let stage = Stage::builder().make_stage(
            vec![
                root,
                opinion_layer("weak1.usda", 1.0)?,
                opinion_layer("weak2.usda", 2.0)?,
            ],
            0,
            Vec::new(),
        );
        assert_eq!(
            stage.sub_layers("root.usda"),
            vec!["root.usda", "weak1.usda", "weak2.usda"]
        );

        {
            let mut root = stage.layer_mut("root.usda").expect("root layer");
            root.edit(|e| {
                e.pseudo_root_mut().unwrap().set_sublayers(["weak2.usda"]);
                Ok(())
            })?;
        }
        assert_eq!(stage.sub_layers("root.usda"), vec!["root.usda", "weak2.usda"]);
        Ok(())
    }

    /// The aggregator tags each committed edit with its origin: a stage edit on a
    /// local layer reports [`Provenance::LocalStack`], while a direct edit to a
    /// non-local (referenced) layer reports [`Provenance::DirectLayerEdit`].
    #[test]
    fn provenance_local_vs_direct() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/P", sdf::Specifier::Def, "").unwrap();
            e.data_mut().set_field(
                &sdf::path("/P").unwrap(),
                sdf::FieldKey::References.as_str(),
                sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                    asset_path: "target.usda".into(),
                    prim_path: sdf::path("/Target").unwrap(),
                    ..Default::default()
                }])),
            );
        });
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Target", sdf::Specifier::Def, "").unwrap();
        });
        let stage = Stage::builder().make_stage(vec![root, target], 0, Vec::new());

        let seen: Rc<Cell<Option<&'static str>>> = Rc::new(Cell::new(None));
        {
            let seen = seen.clone();
            stage.add_sink(move |_: &Stage, change: &crate::usd::CommittedChange<'_>| {
                seen.set(Some(match change.provenance {
                    Provenance::LocalStack => "local",
                    Provenance::EditTarget(_) => "target",
                    Provenance::DirectLayerEdit => "direct",
                }));
            });
        }

        stage.define_prim("/Q")?;
        assert_eq!(seen.get(), Some("local"), "a local stage edit reports LocalStack");

        {
            let mut target = stage.layer_mut("target.usda").expect("target layer");
            target.edit(|e| {
                sdf::PrimSpec::new(e.data_mut(), "/Target/Child", sdf::Specifier::Def, "").unwrap();
                Ok(())
            })?;
        }
        stage.process_pending();
        assert_eq!(
            seen.get(),
            Some("direct"),
            "a direct non-local edit reports DirectLayerEdit"
        );
        Ok(())
    }

    /// `batch_edit` authors several of the stage's layers as one transaction; both
    /// edits land and the composed scene reflects them after one recompose.
    #[test]
    fn batch_edit_atomic() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(vec![root, opinion_layer("weak.usda", 1.0)?], 0, Vec::new());

        let changed = stage.batch_edit(&["root.usda", "weak.usda"], |edits| {
            sdf::PrimSpec::new(edits[0].data_mut(), "/FromRoot", sdf::Specifier::Def, "")?;
            sdf::PrimSpec::new(edits[1].data_mut(), "/FromWeak", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        assert!(changed);
        assert!(stage.prim(sdf::path("/FromRoot")?).is_valid()?);
        assert!(stage.prim(sdf::path("/FromWeak")?).is_valid()?);
        Ok(())
    }

    /// A `ReplayStage` records a multi-layer `batch_edit` as one forward diff per
    /// layer, reading each layer's own change against its own data — so a spec
    /// authored only in the weaker layer is captured, not masked by the strongest
    /// layer holding no such spec.
    #[test]
    fn replay_multi_layer_batch() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(vec![root, opinion_layer("weak.usda", 1.0)?], 0, Vec::new());
        let recorder = crate::usd::ReplayStage::from(stage);
        recorder.batch_edit(&["root.usda", "weak.usda"], |edits| {
            sdf::PrimSpec::new(edits[0].data_mut(), "/FromRoot", sdf::Specifier::Def, "")?;
            sdf::PrimSpec::new(edits[1].data_mut(), "/FromWeak", sdf::Specifier::Def, "")?;
            Ok(())
        })?;

        let paths: Vec<sdf::Path> = recorder
            .diff()
            .iter()
            .flat_map(|d| d.edits.iter().map(|e| e.path().clone()))
            .collect();
        assert!(paths.contains(&sdf::path("/FromRoot")?));
        assert!(
            paths.contains(&sdf::path("/FromWeak")?),
            "the sublayer's edit is captured"
        );
        Ok(())
    }

    /// A `batch_edit` whose closure errors rolls every layer back, so no partial
    /// edit survives on the layers it had already staged.
    #[test]
    fn batch_edit_rolls_back() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(vec![root, opinion_layer("weak.usda", 1.0)?], 0, Vec::new());

        let result = stage.batch_edit(&["root.usda", "weak.usda"], |edits| {
            sdf::PrimSpec::new(edits[0].data_mut(), "/FromRoot", sdf::Specifier::Def, "")?;
            // A property path is invalid for a prim spec, aborting the batch.
            sdf::PrimSpec::new(edits[1].data_mut(), "/Bad.attr", sdf::Specifier::Def, "")?;
            Ok(())
        });
        assert!(result.is_err());
        assert!(
            !stage.prim(sdf::path("/FromRoot")?).is_valid()?,
            "the staged root edit rolled back with the batch"
        );
        Ok(())
    }

    /// `batch_edit` rejects an unknown layer and a repeated one before authoring.
    #[test]
    fn batch_edit_bad_args() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.root_layer().identifier().to_string();
        assert!(matches!(
            stage.batch_edit(&["missing.usda"], |_| Ok(())),
            Err(StageAuthoringError::LayerNotFound { .. })
        ));
        assert!(matches!(
            stage.batch_edit(&[root.as_str(), root.as_str()], |_| Ok(())),
            Err(StageAuthoringError::DuplicateLayer { .. })
        ));
        Ok(())
    }
}
