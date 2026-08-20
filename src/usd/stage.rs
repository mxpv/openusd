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
use std::sync::Arc;

use bitflags::bitflags;

use crate::tf::Token;
use crate::{Result, ar, pcp, sdf};

use super::composition::{self, PendingEdit, StageComposition};

use super::interp::{self, InterpolationType};
use super::sink::{PendingChange, Provenance, StageSink, StageSinkId, keep_ancestors};
use super::{PrimTypeId, PrimTypeInfo, SchemaRegistry, Schematics, StagePopulationMask};

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

    /// This predicate restricted to its inherited bits. It descends and
    /// prunes exactly like the original while also visiting the prims the
    /// original declines for non-inherited bits (e.g. a `MODEL` rejection,
    /// which excludes a model prim whose non-model descendants still
    /// match), so a traversal under it visits a depth-first order with only
    /// whole subtrees skipped, over a superset of the original's prims. A
    /// projection equal to the original means the original's own traversal
    /// already has that gap-free shape.
    pub(crate) fn inherited_projection(self) -> Self {
        Self {
            required: self.required.intersection(Self::INHERITED_REQUIRED),
            rejected: self.rejected.intersection(Self::INHERITED_REJECTED),
            traverse_instance_proxies: self.traverse_instance_proxies,
        }
    }

    /// Returns `true` if no descendant can satisfy this predicate.
    fn prunes_descendants(self, status: PrimStatus) -> bool {
        !self.inherited_projection().matches(status)
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
    /// The value identity of the layer stack this target authors into, captured
    /// from the target node when known
    /// ([`edit_target_for_node`](Stage::edit_target_for_node); boxed to keep
    /// the struct small), or `None` for a target whose stack the namespace
    /// editor infers from layer membership ([`for_layer`](Self::for_layer) /
    /// [`for_local_direct_variant`](Self::for_local_direct_variant)). An arc
    /// target records it so a relocate synthesized for it lands in the right
    /// stack even when the referenced asset is also a root sublayer — a case
    /// membership alone cannot disambiguate. Carried by value — not as a
    /// graph-local `LayerStackId` — because an `EditTarget` transfers between
    /// stages with equal composition inputs, whose graphs number their stacks
    /// independently; the captured (possibly contextual) stack then resolves by
    /// content wherever the target is installed.
    authoring_stack: Option<Box<pcp::StackIdentity>>,
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
    pub fn for_local_direct_variant(
        layer_identifier: impl Into<String>,
        var_sel_path: impl sdf::IntoPath,
    ) -> Result<Self, sdf::PathParseError> {
        let var_sel_path = sdf::try_into_path(var_sel_path)?;
        let stripped = var_sel_path.strip_all_variant_selections();
        Ok(Self {
            layer_identifier: layer_identifier.into(),
            mapping: pcp::MapFunction::from_pair_identity(var_sel_path, stripped),
            layer_stack: None,
            authoring_stack: None,
        })
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
        self.spec_time_offset().apply(stage_time)
    }

    /// Maps a stage (scene) value to the one an authoring write should put in
    /// the source layer, retiming every `timecode` it holds (C++
    /// `_StageValueToFieldXf`).
    ///
    /// A `timecode` is a time coordinate in the same frame as the key a sample
    /// is authored at, so it runs through the same inverse offset and likewise
    /// reads back unchanged once composition re-applies the arc's offset. A
    /// value holding no timecode passes through, as does any value through a
    /// local or variant target, which carries the identity offset.
    pub fn map_to_spec_value(&self, value: impl Into<sdf::Value>) -> sdf::Value {
        let mut value = value.into();
        self.spec_time_offset().apply_to_value(&mut value);
        value
    }

    /// The offset that maps a stage time into the time frame of the layer this
    /// target authors into — the inverse of the arc's composed offset (C++
    /// `_StageValueToFieldXf::GetLayerOffset`).
    fn spec_time_offset(&self) -> sdf::LayerOffset {
        self.mapping.time_offset().inverse()
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
/// # fn f(stage: &Stage) -> openusd::Result<()> {
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
    /// A path argument failed to parse.
    #[error(transparent)]
    Parse(#[from] sdf::PathParseError),

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
    Composition(#[from] pcp::QueryError),

    /// The prim's schemas reject the API schema being applied.
    #[error(transparent)]
    Schema(#[from] super::ApplyApiError),

    /// A name argument is not a legal identifier for what it names.
    #[error("invalid {what} {name:?}: must be a valid identifier")]
    InvalidIdentifier {
        /// The offending name.
        name: String,
        /// What the name was for.
        what: &'static str,
    },

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

    /// An arc edit target's captured authoring stack cannot be resolved on this
    /// stage: a layer in its source chain failed to load, so the (possibly
    /// contextual) stack it authors into cannot be composed here. Authoring
    /// into a substitute stack would land opinions in the wrong members, so the
    /// call fails instead.
    #[error("edit target authoring stack unavailable: layer {layer:?} cannot be loaded")]
    EditTargetStackUnavailable {
        /// Identifier of the source-chain layer that could not be loaded.
        layer: String,
    },

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
    /// The composed state — layer graph, composition cache, and the queue of
    /// edits awaiting a recompose — behind the operations that name which side
    /// of the pending drain each access sits on.
    composition: StageComposition,
    /// Initial payload loading behavior for this stage.
    initial_load_set: InitialLoadSet,
    /// The population epoch of the last completed prototype-discovery pass, or
    /// `None` when none has completed. Stage population is what fills the
    /// prototype registry, so a query addressing the `/__Prototype_N` namespace
    /// runs [`Stage::discover_prototypes`] whenever this no longer matches the
    /// cache's epoch. See [`Stage::resolve_prototype_path`].
    prototypes_discovered: Cell<Option<u64>>,
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
    /// The [`Provenance`] a stage authoring method publishes for the commit
    /// currently underway, read by the aggregator as it records into
    /// [`StageComposition`]'s queue. `None` for a direct edit, which the drain
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
    /// The schemas this stage resolves fallback values against. Pinned at open,
    /// so the definitions a prim reads never shift under it.
    schema_registry: Arc<SchemaRegistry>,
    /// Which prim is of which schema type, so a fallback read does not recompose
    /// `typeName` and `apiSchemas` every time. The registry holds the composed
    /// definitions themselves; this only remembers which one each path resolved
    /// to, and is dropped wholesale when composition moves on.
    prim_types: RefCell<PrimTypeMemo>,
}

/// Per-prim schema type handles, valid as of one composition revision.
///
/// This is the stage-local half of prim type resolution: the registry caches
/// definitions by type identity, and this remembers which identity each prim
/// currently has. An edit that changes any prim's type advances the revision,
/// which drops the whole memo — cheap, since re-deriving one prim's identity is
/// two composed reads.
#[derive(Default)]
struct PrimTypeMemo {
    revision: u64,
    types: HashMap<sdf::Path, Arc<PrimTypeInfo>>,
}

impl PrimTypeMemo {
    /// The remembered type of a prim, if it was resolved under the revision
    /// still in effect.
    fn lookup(&self, revision: u64, path: &sdf::Path) -> Option<Arc<PrimTypeInfo>> {
        if self.revision != revision {
            return None;
        }
        self.types.get(path).cloned()
    }

    /// Remembers a prim's type, discarding everything resolved under an
    /// earlier revision.
    fn remember(&mut self, revision: u64, path: sdf::Path, info: Arc<PrimTypeInfo>) {
        if self.revision != revision {
            self.types.clear();
            self.revision = revision;
        }
        self.types.insert(path, info);
    }
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

impl composition::CompositionHooks for Stage {
    fn attach_layer_sink(&self, id: pcp::LayerId, layer: &mut sdf::Layer) {
        layer.add_sink(StageAggregator {
            stage: self.downgrade(),
            layer_id: id,
            prior_default_prim: Cell::new(None),
        });
    }

    fn wants_notice(&self) -> bool {
        !self.sinks.borrow().is_empty()
    }

    fn notify(&self, notice: composition::CompositionNotice) {
        let change = notice
            .payload
            .committed_change(&notice.layer_identifier, &notice.provenance, notice.generation);
        for sink in self.sinks.borrow().iter() {
            sink.after_commit(self, &change);
        }
    }
}

impl Stage {
    /// Drain the layer edits recorded by the aggregators and drive one
    /// composition recompose per snapshot, delivering each composed
    /// [`CommittedChange`](super::CommittedChange) to the stage sinks. The
    /// deferred counterpart to a layer commit: an aggregator records the edit
    /// while the layer graph is borrowed, and this runs once that borrow is
    /// released — after each authoring call, and before any composed read.
    ///
    /// The public re-entry boundary for reconciliation; the drain itself, and
    /// the quiescence rule it runs under, belong to
    /// [`StageComposition`].
    pub(crate) fn process_pending(&self) {
        self.composition.process_pending(self);
    }

    /// Whether `self` and `other` are the same stage instance — handle
    /// identity, like C++ `UsdStage` pointer equality — as opposed to two
    /// stages that merely compose the same content.
    pub fn ptr_eq(&self, other: &Stage) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

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
/// [`intern_layer`](composition::StageComposition::intern_layer)) to bridge the low tier of the change
/// pipeline to the high tier: it records each commit into
/// [`StageComposition`]'s pending queue for a composed recompose, and forwards the
/// staged pre-commit edit to the stage's [`StageSink`]s. It holds a
/// [`WeakStage`] so it forms no reference cycle (the stage owns the layer, which
/// owns this sink).
struct StageAggregator {
    stage: WeakStage,
    layer_id: pcp::LayerId,
    /// The layer's `defaultPrim` token as `before_commit` saw it, for the
    /// matching `after_commit` to hand to the composition queue.
    ///
    /// Composition classification runs after the commit, by which point the
    /// pre-edit values are gone, and it needs this one to fan a `defaultPrim`
    /// edit out the way C++ `PcpChanges` does. One sink is installed per layer,
    /// and `sdf::edit_layers` runs every `before_commit` ahead of any
    /// `after_commit`, so sink-local scratch stays correct across a multi-layer
    /// transaction — and a vetoed commit simply leaves a value the next
    /// `before_commit` overwrites.
    prior_default_prim: Cell<Option<Token>>,
}

impl sdf::LayerSink for StageAggregator {
    fn before_commit(&self, change: &sdf::PendingLayerChange<'_>) -> Result<(), sdf::sink::Error> {
        // Only a commit that staged something on the pseudo-root can have touched
        // the field, and the overlay answers that in one probe — the change list
        // is a flat vector, so scanning it would cost a walk per commit. A
        // pseudo-root edit that left `defaultPrim` alone reads a value nothing
        // consumes, which is cheaper than finding out. An absent field, an
        // unreadable one, and a non-token value all record `None`: no prior prim,
        // the conservative fanout.
        let prior = change
            .overlay
            .keys()
            .any(sdf::Path::is_abs_root)
            .then(|| sdf::PseudoRootSpecRef::get(change.base)?.default_prim())
            .flatten();
        self.prior_default_prim.set(prior);
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
        let prior = self.prior_default_prim.take();
        if let Some(stage) = self.stage.upgrade() {
            stage.record_pending(self.layer_id, changes.clone(), prior);
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
    pub fn composition_errors(&self) -> Vec<pcp::CompositionError> {
        // Drain once, then read both together: routing through the
        // `layers()`/`cache()` accessors would each re-run `process_pending`, and
        // holding the graph borrow across the second run risks a re-entrant
        // borrow-mut if a sink re-queues an edit during notification.
        self.process_pending();
        let graph = self.composition.settled_graph();
        let mut errors = graph.errors();
        let mut cache_errors = self.composition.settled_cache().composition_errors();
        // A diagnostic the graph regenerates per stack can coexist with an
        // identical one-shot loader copy kept at open — a referrer the session
        // prefix reaches, or a branch muted at open and unmuted later; the
        // regenerable copy wins so one failure reads once.
        cache_errors.retain(|error| !errors.contains(error));
        // Only a muted stage suppresses anything, and only sublayer diagnostics; skip
        // building the effective-layer set when there is nothing to filter.
        if !graph.has_muted_layers() || !cache_errors.iter().any(is_sublayer_error) {
            errors.extend(cache_errors);
            return errors;
        }
        // The effectively-composed layers: every interned composed stack's
        // members (the root stack and each reference/payload target stack),
        // which muting has pruned muted subtrees from. This is a pure function
        // of the muted set and the interned stacks: a stack and its diagnostics
        // are removed together when a sweep reclaims it, so a diagnostic never
        // outlives the membership that justified it. Ownership-scheduled
        // reclamation keeps the set tight — a target whose last owning index
        // drops (a mute or unload severing its only arc included) is swept at
        // that same edit seam, and recomposition re-derives whatever still
        // holds.
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

    /// Maps a stage value to the one the current edit target authors, borrowing
    /// the target rather than cloning it. See
    /// [`EditTarget::map_to_spec_value`].
    pub(super) fn map_to_spec_value(&self, value: impl Into<sdf::Value>) -> sdf::Value {
        self.edit_target.borrow().map_to_spec_value(value)
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
        target.authoring_stack = Some(Box::new(stack_info));
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
    pub fn define_prim(&self, path: impl sdf::IntoPath) -> Result<super::Prim, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
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
    pub fn override_prim(&self, path: impl sdf::IntoPath) -> Result<super::Prim, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
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
        path: impl sdf::IntoPath,
        type_name: impl Into<String>,
    ) -> Result<super::Attribute, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
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
    pub fn create_relationship(&self, path: impl sdf::IntoPath) -> Result<super::Relationship, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
        self.with_target_layer_at(&path, |layer, layer_path| {
            sdf::RelationshipSpec::new(layer.data_mut(), layer_path, sdf::Variability::Uniform, true)?;
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
    pub fn remove_prim(&self, path: impl sdf::IntoPath) -> Result<bool, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
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
    pub fn remove_property(&self, path: impl sdf::IntoPath) -> Result<bool, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
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
    /// `name` must name a prim, in either spelling — `"World"`, `"World/Char"`,
    /// or `"/World/Char"`. See [`sdf::LayerEdit::set_default_prim`].
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
        self.composition
            .authoring_graph()
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
            let mut layers = self.composition.authoring_graph_mut();
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
            .composition
            .authoring_graph()
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
            let layers = self.composition.authoring_graph();
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
    /// errors through the same transaction. Returns whether the transaction
    /// changed anything: the commit's change flag, or `false` for a dry run.
    ///
    /// A commit may enter with edits already queued, appends its own
    /// transaction to that queue, and drains everything afterwards — including
    /// when the transaction itself failed, so a failed commit can still deliver
    /// the notifications its predecessors earned. A dry run neither queues nor
    /// drains, so a caller whose validation reads composed state settles before
    /// calling; and its rollback discards each layer's whole staged overlay, not
    /// only what the dry run wrote, so the batch assumes its layers carry no
    /// uncommitted direct edits.
    pub(super) fn author_layers_txn<E>(
        &self,
        layer_ids: &[pcp::LayerId],
        mapping: Option<&pcp::MapFunction>,
        commit: bool,
        f: impl FnOnce(&[pcp::LayerId], &mut [sdf::LayerEdit<'_>]) -> Result<(), E>,
    ) -> Result<bool, E>
    where
        E: From<sdf::sink::Error>,
    {
        let result = {
            // The borrow states the mode's drain contract: a commit may arrive
            // with edits queued and appends to them, while a dry run validates
            // against composed state and so takes the settled borrow, whose
            // backstop catches a caller that stopped settling first.
            let mut graph = if commit {
                self.composition.authoring_graph_mut()
            } else {
                self.composition.settled_graph_mut()
            };
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
                sdf::edit_layers(&mut batch, |edits| f(&ids, edits))
            } else {
                sdf::dry_run_layers(&mut batch, |edits| f(&ids, edits)).map(|()| false)
            }
        };
        if commit {
            self.process_pending();
        }
        result
    }

    /// The handle for the layer stack the mapped edit `target_layer` writes
    /// into — the stack a relocate synthesized for that target must land in. An
    /// arc target carries its authoring stack's value identity from
    /// construction, so it resolves exactly (the referenced asset's stack even
    /// when that asset is also a root sublayer); a target without one (a local
    /// or variant target) is inferred from layer membership — the root stack
    /// when `target_layer` belongs to it, else the sublayer stack rooted at it.
    /// Per spec §10.3.2.6, relocates take effect in the stack where the
    /// bringing-in arc is authored, so this is where the editor seeds and
    /// authors the mapped relocate plan; resolve it to member layer ids with
    /// [`LayerGraph::layer_stack`](crate::pcp::LayerGraph::layer_stack).
    ///
    /// Fails with [`StageAuthoringError::EditTargetStackUnavailable`] when a
    /// layer in the captured identity's source chain cannot be loaded here —
    /// authoring into a substitute stack would seed the relocate plan from the
    /// wrong members and expression variables.
    pub(super) fn mapped_target_stack_id(
        &self,
        target_layer: pcp::LayerId,
    ) -> Result<pcp::LayerStackId, StageAuthoringError> {
        let authoring = self.edit_target.borrow().authoring_stack.clone();
        self.composition
            .resolve_authoring_stack(target_layer, authoring, self)
            .map_err(|layer| StageAuthoringError::EditTargetStackUnavailable { layer })
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
            let edit = edits
                .first_mut()
                .expect("the caller resolved `layer_id` against this graph, so it is live");
            f(edit).map_err(StageAuthoringError::from)
        })
        .map(|_changed| ())
    }

    /// Run `f` as one atomic [`Layer::edit`](sdf::Layer::edit) on `layer`: commit
    /// and return the recorded change list on success, or roll the layer back on
    /// error (`f`'s authoring error, or a sink veto).
    ///
    /// Committing fires the layer's sinks — including the stage's aggregator
    /// (installed when its layer interned), which records the edit into
    /// [`StageComposition`]'s pending queue for [`process_pending`](Self::process_pending)
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
    /// installed when its layer interned) as a layer commits — while the layer graph
    /// is borrowed for the edit, which is why it appends to the independent
    /// [`StageComposition`]'s pending queue rather than recomposing inline.
    pub(super) fn record_pending(
        &self,
        layer_id: pcp::LayerId,
        changes: sdf::ChangeList,
        prior_default_prim: Option<Token>,
    ) {
        let provenance = self.edit_provenance.take();
        self.composition.record_pending(PendingEdit {
            generation: self.current_generation.get(),
            layer: layer_id,
            changes,
            provenance,
            prior_default_prim,
        });
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
        self.author_layers_txn(&ids, None, true, |realized, edits| {
            // `edits[i]` authors `layers[i]` is this method's public contract, so
            // the realized ids must still line up with the requested ones.
            debug_assert_eq!(realized.len(), ids.len(), "batch_edit realized every layer");
            f(edits)
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
        if let Some((changed, resynced)) = self
            .composition
            .apply_mute(|graph| graph.mute_layer(identifier.into()), self)
        {
            self.notify_muting_changed(&changed, true, resynced);
        }
    }

    /// Unmutes the layer with the given identifier, restoring its opinions to
    /// composition (C++ `UsdStage::UnmuteLayer`).
    pub fn unmute_layer(&self, identifier: &str) {
        if let Some((changed, resynced)) = self
            .composition
            .apply_mute(|graph| graph.unmute_layer(identifier), self)
        {
            self.notify_muting_changed(&changed, false, resynced);
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
    pub fn load(&self, path: impl sdf::IntoPath, policy: LoadPolicy) -> Result<(), sdf::PathParseError> {
        let Some(path) = Self::normalize_load_target(sdf::try_into_path(path)?) else {
            return Ok(());
        };
        let victims = self.composition.install_load_rules(
            |rules| match policy {
                LoadPolicy::WithDescendants => rules.load_with_descendants(path.clone()),
                LoadPolicy::WithoutDescendants => rules.load_without_descendants(path.clone()),
            },
            self,
        );
        self.notify_load_rules_changed(victims);
        Ok(())
    }

    /// Unloads `path`'s payload and everything beneath it (C++
    /// `UsdStage::Unload`). Same leniency as [`load`](Self::load) for a
    /// prototype-namespace path.
    pub fn unload(&self, path: impl sdf::IntoPath) -> Result<(), sdf::PathParseError> {
        let Some(path) = Self::normalize_load_target(sdf::try_into_path(path)?) else {
            return Ok(());
        };
        let victims = self
            .composition
            .install_load_rules(|rules| rules.unload(path.clone()), self);
        self.notify_load_rules_changed(victims);
        Ok(())
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
        to_load: impl IntoIterator<Item = (impl sdf::IntoPath, LoadPolicy)>,
        to_unload: impl IntoIterator<Item: sdf::IntoPath>,
    ) -> Result<(), sdf::PathParseError> {
        // Convert (and fail) before any rule is edited, so a bad path in
        // either set leaves the stage untouched.
        let to_unload: Vec<sdf::Path> = to_unload
            .into_iter()
            .map(|path| Ok(Self::normalize_load_target(sdf::try_into_path(path)?)))
            .filter_map(Result::transpose)
            .collect::<Result<_, sdf::PathParseError>>()?;
        let to_load: Vec<(sdf::Path, LoadPolicy)> = to_load
            .into_iter()
            .map(|(path, policy)| Ok(Self::normalize_load_target(sdf::try_into_path(path)?).map(|path| (path, policy))))
            .filter_map(Result::transpose)
            .collect::<Result<_, sdf::PathParseError>>()?;
        let victims = self.composition.install_load_rules(
            |rules| {
                for path in to_unload {
                    rules.unload(path);
                }
                for (path, policy) in to_load {
                    match policy {
                        LoadPolicy::WithDescendants => rules.load_with_descendants(path),
                        LoadPolicy::WithoutDescendants => rules.load_without_descendants(path),
                    }
                }
            },
            self,
        );
        self.notify_load_rules_changed(victims);
        Ok(())
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
        let victims = self.composition.install_load_rules(|current| *current = rules, self);
        self.notify_load_rules_changed(victims);
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
    pub fn find_loadable(&self, root: impl sdf::IntoPath) -> Result<Vec<sdf::Path>> {
        let root = sdf::try_into_path(root)?.prim_path();
        let _guard = LoadRulesGuard {
            stage: self,
            original: self.load_rules(),
        };
        self.composition.swap_load_rules(pcp::LoadRules::all(), self);
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
    pub fn load_set(&self) -> Result<Vec<sdf::Path>> {
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
    fn walk_loadable(&self, path: &sdf::Path, found: &mut Vec<sdf::Path>) -> Result<()> {
        let mut stack = vec![path.clone()];
        while let Some(path) = stack.pop() {
            let prim = super::Prim::new(self, path.clone());
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
    /// paths), then drops a path in the reserved `/__Prototype_N` namespace,
    /// where load rules are never consulted (see [`pcp::LoadRules`]'s
    /// instancing notes) — silently, as C++ does. The test is syntactic, so it
    /// does not depend on whether that prototype has been registered yet.
    ///
    /// A cheap early exit for `load`/`unload`/`load_and_unload` — the real
    /// enforcement of the same invariant lives in `IndexCache::set_load_rules`,
    /// the single choke point every mutation (including a caller-supplied
    /// [`set_load_rules`](Self::set_load_rules) table this normalization never
    /// sees) passes through.
    fn normalize_load_target(path: sdf::Path) -> Option<sdf::Path> {
        let path = sdf::Path::abs_root().make_absolute(&path.prim_path().strip_all_variant_selections());
        (!pcp::is_prototype_namespace(&path)).then_some(path)
    }

    /// Fires [`StageSink::load_rules_changed`] with the paths the edit
    /// invalidated, reduced to the subtrees they stand for, after the cache
    /// borrow is released. A no-op edit invalidates nothing and reports nothing.
    fn notify_load_rules_changed(&self, mut resynced: Vec<sdf::Path>) {
        let sinks = self.sinks.borrow();
        if resynced.is_empty() || sinks.is_empty() {
            return;
        }
        keep_ancestors(&mut resynced);
        for sink in sinks.iter() {
            sink.load_rules_changed(self, &resynced);
        }
    }

    /// `true` if `path`'s own payload is included by the stage's load rules —
    /// the per-ancestor check behind [`Prim::is_loaded`](super::Prim::is_loaded).
    pub(crate) fn is_path_loaded(&self, path: &sdf::Path) -> bool {
        self.cache().is_loaded(path)
    }

    /// Fires [`StageSink::layer_muting_changed`] for the toggled identifier and
    /// the paths the toggle invalidated, reduced the same way, after the graph
    /// and cache borrows are released. Unlike the load-rules notice an empty set
    /// still fires: the muted set changed whether or not anything was cached
    /// against the layer.
    ///
    /// TODO(perf): a mute that reaches the root layer hands over every cached
    /// index, so this reduction is `keep_ancestors` at its worst case — see the
    /// `sdf::PathTable` covering set noted there.
    fn notify_muting_changed(&self, changed: &str, muted: bool, mut resynced: Vec<sdf::Path>) {
        let sinks = self.sinks.borrow();
        if sinks.is_empty() {
            return;
        }
        keep_ancestors(&mut resynced);
        for sink in sinks.iter() {
            sink.layer_muting_changed(self, changed, muted, &resynced);
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

    /// Returns the population mask this stage was opened with (C++
    /// `UsdStage::GetPopulationMask`, which likewise returns by value).
    ///
    /// The mask lives on the composition cache, where it also keys instancing
    /// (see [`StagePopulationMask`]), so this hands back a copy rather than a
    /// borrow into it.
    pub fn mask(&self) -> StagePopulationMask {
        self.cache().population_mask().clone()
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
        self.with_cache(|g, _| Ok(g.default_prim())).unwrap_or_default()
    }

    /// Returns composed pseudo-root stage metadata, honoring a session-layer
    /// opinion over the root layer (C++ `UsdStage::GetMetadata`).
    ///
    /// Distinct from [`Stage::field`] on [`sdf::Path::abs_root`], which reads
    /// root-layer-only metadata for the spec 12.2.7 fields like `defaultPrim`.
    /// Returns the raw [`sdf::Value`]; the caller coerces it.
    pub fn stage_metadata(&self, field: impl AsRef<str>) -> Result<Option<sdf::Value>> {
        Ok(self.with_cache(|g, _| Ok(g.stage_metadata(field.as_ref())?))?)
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
    pub fn time_samples(&self, attr_path: impl sdf::IntoPath) -> Result<Option<sdf::TimeSampleMap>> {
        let attr_path = sdf::try_into_path(attr_path)?;
        Ok(match self.field::<sdf::Value>(attr_path, sdf::FieldKey::TimeSamples)? {
            Some(sdf::Value::TimeSamples(samples)) => Some(samples),
            _ => None,
        })
    }

    /// Returns the composed `timeSamples` sample times for an attribute, or
    /// `None` when none are authored. Resolves the times without cloning the
    /// sample values, retimed by the contributing layer offsets to match
    /// [`Self::time_samples`].
    pub fn time_sample_times(&self, attr_path: impl sdf::IntoPath) -> Result<Option<Vec<f64>>> {
        let attr_path = sdf::try_into_path(attr_path)?;
        Ok(self.masked(&attr_path, |g, c| c.time_sample_times(g, &attr_path))?)
    }

    /// Returns the number of composed `timeSamples` for an attribute, zero when
    /// none are authored. Resolves the count without cloning the sample values.
    pub fn num_time_samples(&self, attr_path: impl sdf::IntoPath) -> Result<usize> {
        let attr_path = sdf::try_into_path(attr_path)?;
        Ok(self.masked(&attr_path, |g, c| c.num_time_samples(g, &attr_path))?)
    }

    /// Whether an attribute's value may vary over time, the introspection behind
    /// [`Attribute::value_might_be_time_varying`](super::Attribute::value_might_be_time_varying).
    /// Reports `true` when the winning value source has more than one composed
    /// sample, and conservatively when that source is a value-clip set with more
    /// than one active clip — those clips can each contribute a different value
    /// even where the discrete sample count collapses to one (spec 12.3.4).
    pub fn value_might_be_time_varying(&self, attr_path: impl sdf::IntoPath) -> Result<bool> {
        let attr_path = sdf::try_into_path(attr_path)?;
        Ok(self.masked(&attr_path, |g, c| c.value_might_be_time_varying(g, &attr_path))?)
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
    pub(crate) fn resolve_at(&self, attr_path: impl sdf::IntoPath, time: f64) -> Result<Option<sdf::Value>> {
        let attr_path = sdf::try_into_path(attr_path)?;
        let interp_type = self.interpolation_type.get();
        let interp = |samples: &sdf::TimeSampleMap, t: f64| interp::evaluate(samples, t, interp_type);
        Ok(self.masked(&attr_path, |g, c| c.value_at(g, &attr_path, time, &interp))?)
    }

    /// Resolves the cacheable value source for an attribute, the source half of
    /// [`Self::resolve_at`]. Backs [`AttributeQuery`](super::AttributeQuery),
    /// which snapshots the source and replays it across time codes. Returns
    /// [`AttributeValueSource::Static`](pcp::AttributeValueSource::Static)
    /// `None` when the attribute's prim is outside the population mask.
    pub(crate) fn resolve_value_source(&self, attr_path: &sdf::Path) -> Result<pcp::AttributeValueSource> {
        Ok(self.masked(attr_path, |g, c| c.resolve_value_source(g, attr_path))?)
    }

    /// The current composition revision, advanced once per applied edit batch.
    /// [`AttributeQuery`](super::AttributeQuery) snapshots this and rebuilds its
    /// cached source when it advances.
    pub(crate) fn cache_revision(&self) -> u64 {
        self.cache().revision()
    }

    /// The schemas this stage resolves against (C++
    /// `UsdStage::GetSchemaRegistry` is a global; here it is per stage).
    pub fn schema_registry(&self) -> &Arc<SchemaRegistry> {
        &self.schema_registry
    }

    /// The schema type of the prim at `path` (C++ `UsdPrim::GetPrimTypeInfo`).
    ///
    /// Derived from the prim's composed `typeName` and `apiSchemas`, and shared
    /// with every other prim resolving to the same pair. A prim with neither —
    /// including one the population mask excludes — gets the registry's empty
    /// type.
    pub fn prim_type_info(&self, path: impl sdf::IntoPath) -> Result<Arc<PrimTypeInfo>> {
        Ok(self.prim_type_info_composed(path)?)
    }

    /// [`prim_type_info`](Self::prim_type_info) at the composition tier, for
    /// the internal readers and authoring routers that fold the failure into
    /// their own error.
    pub(crate) fn prim_type_info_composed(
        &self,
        path: impl sdf::IntoPath,
    ) -> Result<Arc<PrimTypeInfo>, pcp::QueryError> {
        let path = sdf::try_into_path(path)?;
        let revision = self.cache_revision();
        if let Some(info) = self.prim_types.borrow().lookup(revision, &path) {
            return Ok(info);
        }

        // Keyed on the authored list, not the composed one: the composed list
        // is what the definition this identity selects reports back
        // (C++ `_ComposeAuthoredAppliedSchemas`).
        let prim = super::Prim::new(self, path.prim_path());
        let mut id = PrimTypeId::new(prim.type_name_composed()?, prim.authored_api_schemas_composed()?);
        if let Some(mapped) = self.fallback_prim_type(id.type_name())? {
            id = id.with_mapped_type_name(mapped);
        }
        let info = self.schema_registry.prim_type_info(id);
        self.prim_types.borrow_mut().remember(revision, path, info.clone());
        Ok(info)
    }

    /// The registered type to use in place of `type_name`, when the stage's
    /// root layer names one and the registry does not know the authored type
    /// (C++ `Usd_PrimTypeInfoCache::ComputeInvalidPrimTypeToFallbackMap`).
    ///
    /// `fallbackPrimTypes` maps each such type to an ordered list of
    /// substitutes; the first the registry knows wins, so an asset written
    /// against a newer schema still resolves against what this build has.
    fn fallback_prim_type(&self, type_name: &Token) -> Result<Option<Token>, pcp::QueryError> {
        const FALLBACK_PRIM_TYPES: &str = "fallbackPrimTypes";

        if type_name.as_str().is_empty() || self.schema_registry.is_concrete_type(type_name) {
            return Ok(None);
        }
        let Some(sdf::Value::Dictionary(fallbacks)) =
            self.field::<sdf::Value>(sdf::Path::abs_root(), FALLBACK_PRIM_TYPES)?
        else {
            return Ok(None);
        };
        let Some(candidates) = fallbacks
            .get(type_name.as_str())
            .cloned()
            .and_then(sdf::Value::try_as_token_vec)
        else {
            return Ok(None);
        };
        Ok(candidates
            .into_iter()
            .find(|candidate| self.schema_registry.is_concrete_type(candidate)))
    }

    /// Returns a [`Prim`](super::Prim) handle anchored to `path`. Mirrors C++
    /// `UsdStage::GetPrimAtPath`. The handle is a value-type `(stage, path)`
    /// wrapper; `Ok` does not assert that a prim is composed at the path
    /// (query the handle to find out) — `Err` means `path` failed to parse.
    pub fn prim(&self, path: impl sdf::IntoPath) -> Result<super::Prim, sdf::PathParseError> {
        Ok(super::Prim::new(self, sdf::try_into_path(path)?.prim_path()))
    }

    /// Returns an [`Attribute`](super::Attribute) handle anchored to `path`.
    /// Mirrors C++ `UsdStage::GetAttributeAtPath`. Like [`Self::prim`], the
    /// `Ok` handle asserts nothing about composed scene content; query it to
    /// resolve a value.
    pub fn attribute(&self, path: impl sdf::IntoPath) -> Result<super::Attribute, sdf::PathParseError> {
        Ok(super::Attribute::new(self, sdf::try_into_path(path)?))
    }

    /// Returns a [`Relationship`](super::Relationship) handle anchored to `path`.
    /// Mirrors C++ `UsdStage::GetRelationshipAtPath`.
    pub fn relationship(&self, path: impl sdf::IntoPath) -> Result<super::Relationship, sdf::PathParseError> {
        Ok(super::Relationship::new(self, sdf::try_into_path(path)?))
    }

    /// Returns an [`AttributeQuery`](super::AttributeQuery) for the attribute at
    /// `path` — a cached value source for repeated time-code reads. The
    /// `Stage`-anchored spelling of [`Attribute::query`](super::Attribute::query).
    pub fn attribute_query(&self, path: impl sdf::IntoPath) -> Result<super::AttributeQuery, sdf::PathParseError> {
        Ok(super::AttributeQuery::new(&self.attribute(path)?))
    }

    /// Returns the composed list of root prim names (children of the pseudo-root).
    pub fn root_prims(&self) -> Result<Vec<Token>> {
        let root = sdf::Path::abs_root();
        Ok(self.with_cache(|g, c| c.prim_children(g, &root))?)
    }

    // `has_spec` / `spec_type` below are low-level composed-spec infrastructure
    // (the post-composition analog of `SdfAbstractData::HasSpec` /
    // `GetSpecType`), shared by the composed handles and the stage's own status
    // queries. The public, C++-shaped scene queries live on the handles:
    // children / property names on `Prim` (`GetChildren` / `GetPropertyNames`),
    // targets / connections on `Relationship` / `Attribute` (`GetTargets` /
    // `GetConnections`). The handles reach the cache through [`Self::cache`]
    // and [`Self::masked`], which applies the population mask; child lists come
    // back filtered from [`pcp::IndexCache::prim_children`].

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    pub(crate) fn has_spec(&self, path: &sdf::Path) -> Result<bool, pcp::QueryError> {
        self.masked(path, |g, c| c.has_spec(g, path))
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub(crate) fn spec_type(&self, path: impl sdf::IntoPath) -> Result<Option<sdf::SpecType>, pcp::QueryError> {
        let path = sdf::try_into_path(path)?;
        self.masked(&path, |g, c| c.spec_type(g, &path))
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
    /// Returns the composed value: strongest-opinion-wins for plain fields,
    /// with spec 12.2's field-class rules — list-op folding, dictionary
    /// merging, path-expression `%_` composition,
    /// `specifier`/`variability`/`custom` — applied where they hold.
    /// `None` if no layer provides a value. A [`sdf::Value::ValueBlock`]
    /// blocks the opinions weaker than it: the composed result is whatever
    /// the stronger opinions alone produce, or `None` when the block is the
    /// strongest opinion.
    ///
    /// The return type is generic: use `sdf::Value` to get the raw enum, or a
    /// concrete type (e.g. `bool`, `f64`, `String`) to convert automatically
    /// via [`TryFrom<sdf::Value>`].
    ///
    /// Accepts both [`sdf::FieldKey`] and `&str` as the field name.
    ///
    /// [`Attribute::get`]: super::Attribute::get
    pub(crate) fn field<T>(
        &self,
        path: impl sdf::IntoPath,
        field: impl AsRef<str>,
    ) -> Result<Option<T>, pcp::QueryError>
    where
        T: TryFrom<sdf::Value>,
        T::Error: Into<pcp::QueryError>,
    {
        let path = sdf::try_into_path(path)?;
        let raw = self.masked(&path, |g, c| c.resolve_field(g, &path, field.as_ref()))?;
        super::decode_value(raw)
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
        mut query: impl FnMut(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
    ) -> Result<T, pcp::QueryError> {
        let prim = path.prim_path();
        // Before the borrow, not inside it: a prototype path is unanswerable
        // until stage population has registered its root, and completing that
        // is itself a composed walk.
        self.resolve_prototype_path(&prim)?;
        self.with_cache(move |g, c| {
            if c.mask_includes(&prim) {
                query(g, c)
            } else {
                Ok(T::default())
            }
        })
    }

    /// Completes stage population before a query on `prim` is answered, when
    /// `prim` addresses the reserved `/__Prototype_N` namespace.
    ///
    /// The registry that namespace belongs to is filled by composing
    /// instances, so a prototype path is unanswerable until the prims that
    /// share it have been populated — C++ has already done that by the time
    /// `Open` returns, while composition here is demand-driven. Whether the
    /// queried root happens to be registered decides the *result*, never
    /// whether discovery runs: an edit that adds an instance to a prototype
    /// that already exists advances the epoch while leaving the root looking
    /// known.
    ///
    /// Nothing happens for an ordinary stage path, which is every path on a
    /// stage that never asks about a prototype.
    pub(super) fn resolve_prototype_path(&self, prim: &sdf::Path) -> Result<(), pcp::QueryError> {
        if !pcp::is_prototype_namespace(prim) {
            return Ok(());
        }
        self.ensure_prototypes_discovered()
    }

    /// Completes stage population unless it is already current for the live
    /// population epoch.
    fn ensure_prototypes_discovered(&self) -> Result<(), pcp::QueryError> {
        if self.prototypes_discovered.get() == Some(self.cache().population_epoch()) {
            return Ok(());
        }
        self.discover_prototypes()
    }

    /// Registers every prototype the stage's population contains (C++'s
    /// open-time `_ComposePrimIndexesInParallel` plus `Usd_InstanceChanges`,
    /// paid on demand instead).
    ///
    /// The walk is the same shape as [`Self::walk_loadable`] and is built from
    /// the same primitives [`Self::traverse`] uses, so mask, activeness, and
    /// the stop at instances cannot drift from ordinary traversal. It descends
    /// only into populated prims — [`Prim::children`](super::Prim::children)
    /// does not prune on activeness, so without that test the walk would
    /// compose and load whole inactive subtrees — stops at each instance, whose
    /// subtree belongs to its prototype, and then walks each newly registered
    /// prototype's namespace the same way to reach nested instances.
    ///
    /// The pass must be *epoch-stable*. It runs through many separate
    /// [`Self::with_cache`] calls; each settles its own layer loading, but the
    /// traversal as a whole does not, so a demand raised late can install a
    /// layer whose invalidation drops prototypes and child names the walk
    /// already consumed — a demanded layer that introduces relocates, or one
    /// whose own `${VAR}` sublayer resolves afterwards, both reach
    /// `IndexCache::invalidate_layers`. Restarting whenever the epoch moved is
    /// what keeps the stamped result a snapshot of one coherent population.
    /// That terminates for the same reason the loader's own fixpoints do: a
    /// restart means a demanded layer was installed, and each pass settles at
    /// least one previously unsettled target, of which there are finitely many.
    //
    // TODO(perf): the walk composes — and, under `InitialLoadSet::LoadAll`,
    // loads — the whole populated namespace, so one cheap read of a
    // `/__Prototype_N` path pays for the entire stage; any structural edit
    // advances the epoch and re-arms it. C++ pays the same cost, but eagerly
    // and once per recompose; the generalization here is an incremental pass
    // keyed on the change set, registering only the subtrees an edit could have
    // made instanceable.
    // TODO(rayon): distinct prototype namespaces in the fixpoint are
    // independent subtrees, so their passes can run concurrently once
    // materialization does (see `IndexCache::materialize_prototype`).
    fn discover_prototypes(&self) -> Result<(), pcp::QueryError> {
        loop {
            let epoch = self.cache().population_epoch();
            let mut roots: Vec<sdf::Path> = Vec::new();
            let mut visited: HashSet<sdf::Path> = HashSet::new();
            self.register_instances_below(&sdf::Path::abs_root(), &mut roots)?;
            // A prototype's own namespace can hold further instances, and each
            // of those mints a prototype to walk in turn. The visited set
            // bounds the fixpoint however the composition nests.
            while let Some(root) = roots.pop() {
                if visited.insert(root.clone()) {
                    self.register_instances_below(&root, &mut roots)?;
                }
            }
            if self.cache().population_epoch() == epoch {
                self.prototypes_discovered.set(Some(epoch));
                return Ok(());
            }
        }
    }

    /// Registers every instance in the subtree below `root`, collecting the
    /// prototype roots they resolve to into `roots`. One pass of
    /// [`Self::discover_prototypes`]'s walk.
    fn register_instances_below(&self, root: &sdf::Path, roots: &mut Vec<sdf::Path>) -> Result<(), pcp::QueryError> {
        let mut stack = vec![root.clone()];
        while let Some(path) = stack.pop() {
            // One settled pass per prim, straight against the cache. Going
            // through the composed handles instead would re-enter
            // [`Self::resolve_prototype_path`] the moment the walk reached a
            // prototype namespace, so the walk sits below that gate rather than
            // guarding against itself.
            let step = self.with_cache(|g, c| {
                if path != *root && !c.is_populated(g, &path)? {
                    return Ok(None);
                }
                if let Some(prototype) = c.prototype_of(g, &path)? {
                    return Ok(Some(Err(prototype)));
                }
                Ok(Some(Ok(c.prim_children(g, &path)?)))
            })?;
            match step {
                // An instance's subtree belongs to its prototype, so stop here
                // and walk that namespace in its own right.
                Some(Err(prototype)) => roots.push(prototype),
                // Reversed, as `traverse` does, so the walk visits children in
                // namespace order and prototypes mint in stage order.
                Some(Ok(children)) => {
                    for name in children.iter().rev() {
                        if let Ok(child) = path.append_path(name.as_str()) {
                            stack.push(child);
                        }
                    }
                }
                // Not populated: nothing below it composes either.
                None => {}
            }
        }
        Ok(())
    }

    /// Returns a handle to a prim's composition index (C++
    /// `UsdPrim::GetPrimIndex`). The handle is a cheap `(stage, path)` value;
    /// each of its queries borrows the cache briefly, so it can be held and
    /// reused freely.
    pub fn prim_index(&self, prim: impl sdf::IntoPath) -> Result<super::PrimIndexRef, sdf::PathParseError> {
        Ok(super::PrimIndexRef::new(self, sdf::try_into_path(prim)?))
    }

    /// Resolves a layer id — as carried by a composition
    /// [`Node`](pcp::Node) (`layer_id`, `layer_stack`) — to its identifier.
    /// Unlike [`Self::layer_stack`], this covers every loaded layer, including
    /// those reached across reference/payload arcs.
    pub fn layer_identifier(&self, id: pcp::LayerId) -> Option<String> {
        self.layers().try_identifier(id).map(str::to_string)
    }

    /// The raw `(layer id, sublayer offset)` members of `node`'s layer stack, in
    /// strength order (C++ `PcpNodeRef::GetLayerStack`'s layers and offsets). A
    /// composition [`Node`](pcp::Node) references its layer stack by handle and
    /// leaves the members to the cache, so this resolves them through the stage's
    /// layer graph for composition introspection. The offsets are the authored
    /// sublayer offsets; the arc time offset is read separately from the node's
    /// `map_to_root`. Returns `None` for a stale view — a node cloned out of an
    /// index the stage has since dropped, whose stack reclamation removed; a
    /// recomposition mints a successor under a fresh id, never the stale
    /// handle's.
    pub fn node_layer_stack(&self, node: &pcp::Node) -> Option<Vec<(pcp::LayerId, sdf::LayerOffset)>> {
        self.layers().try_layer_stack(node.layer_stack_id()).map(<[_]>::to_vec)
    }

    /// Returns the root layer's `customLayerData` dictionary, if authored.
    /// Mirrors C++ `UsdStage::GetRootLayer()->GetCustomLayerData()`: layer
    /// metadata is read from the root layer alone, not composed across the
    /// layer stack.
    pub fn custom_layer_data(&self) -> Result<Option<sdf::Value>> {
        Ok(self.field::<sdf::Value>(sdf::Path::abs_root(), sdf::FieldKey::CustomLayerData)?)
    }

    /// Returns every prototype root (`/__Prototype_N`) this stage's population
    /// contains, in registration order (C++ `UsdStage::GetPrototypes`).
    ///
    /// Completing the population is what makes the answer whole: the registry
    /// fills as instances compose, so a stage that has composed nothing knows
    /// no prototypes until this call has walked it. Only a prim the mask
    /// exposes can register, so no filtering is applied here.
    pub fn prototypes(&self) -> Result<Vec<sdf::Path>> {
        self.ensure_prototypes_discovered()?;
        Ok(self.cache().prototypes())
    }

    /// Returns the resolved stage status bits for a prim.
    pub fn prim_status(&self, prim: impl sdf::IntoPath) -> Result<PrimStatus> {
        self.prim_status_masked(&sdf::try_into_path(prim)?.prim_path(), PrimStatus::all())
    }

    /// Computes only the status bits set in `mask`. Bits outside `mask` are
    /// left unset. Used by traversal so unused checks (e.g. INSTANCE, MODEL
    /// for default traversal) are skipped.
    fn prim_status_masked(&self, prim: &sdf::Path, mask: PrimStatus) -> Result<PrimStatus> {
        let prim = super::Prim::new(self, prim.clone());
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
            status.set(PrimStatus::IN_PROTOTYPE, prim.is_in_prototype()?);
        }
        Ok(status)
    }

    /// Borrows the stage's composition cache, first draining any pending layer
    /// edits so the cache reflects every commit before it is read.
    pub(crate) fn cache(&self) -> Ref<'_, pcp::IndexCache> {
        self.process_pending();
        self.composition.settled_cache()
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
    /// If `layer` authors its own `subLayers` naming layers not yet loaded,
    /// the recompose records them as sublayer demands and the load barrier
    /// opens them from disk, with one that fails to resolve surfacing as an
    /// [`UnresolvedSublayer`](pcp::CompositionError::UnresolvedSublayer) diagnostic — the
    /// same treatment the root layer's sublayers get at open.
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
            let mut layers = self.composition.authoring_graph_mut();
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
        // insert never leaves an orphan node. Interning attaches
        // the aggregator (skipping a duplicate identifier that collapses onto an
        // already-loaded node), the same path opening a stage uses.
        if edited.is_ok() {
            self.composition.intern_layer(layer, self);
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
            let mut layers = self.composition.authoring_graph_mut();
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
                let subs = layers.get(parent_id)?.layer.pseudo_root()?.sublayers()?.clone();
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

    /// Borrows the stage's layer graph, first draining any pending layer edits so
    /// the graph reflects every commit before it is read — a structural edit
    /// (sublayers, offsets, relocates) leaves the topology stale until then. The
    /// drain is a no-op when nothing is pending.
    pub(crate) fn layers(&self) -> Ref<'_, pcp::LayerGraph> {
        self.process_pending();
        self.composition.settled_graph()
    }

    /// Borrows the stage's layer graph mutably, behind the guard
    /// [`layer_mut`](Self::layer_mut) hands out for direct authoring. Drains
    /// pending edits first so the graph is current before it is re-authored; the
    /// commit's own aggregator records the new change list for the next drain.
    fn layers_mut(&self) -> RefMut<'_, pcp::LayerGraph> {
        self.process_pending();
        self.composition.settled_graph_mut()
    }

    /// Drains, then runs a composed query against the settled stage through
    /// [`StageComposition::query`](composition::StageComposition::query), which
    /// owns the query/load fixpoint.
    pub(crate) fn with_cache<T>(
        &self,
        query: impl FnMut(&pcp::LayerGraph, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
    ) -> Result<T, pcp::QueryError> {
        self.process_pending();
        self.composition.query(query, self)
    }

    /// Anchors an `asset` an attribute's schema fallback supplied, against the
    /// location the schematics that authored it was resolved from.
    ///
    /// This has no C++ counterpart, and is a deliberate extension rather than a
    /// gap being closed: `UsdStage::_GetAssetPathContext` yields no context for
    /// a fallback-sourced value, and `UsdSchemaRegistry` opens each
    /// `generatedSchema.usda` with `SdfLayer::OpenAsAnonymous`, so C++ has no
    /// location to anchor against in the first place. It stays opt-in — a
    /// family registered without a
    /// [`resolved_location`](super::FamilySource::resolved_location) reads back
    /// exactly as C++ leaves it, since resolving an unanchored relative path
    /// would canonicalize it against the process working directory and invent a
    /// location the author never named.
    ///
    /// No variable scope is supplied: a schema layer belongs to no layer stack,
    /// so an expression-valued fallback is left unevaluated and unresolved, and
    /// reports nothing — there are no variables in scope for it to be wrong
    /// about. With nothing to evaluate, nothing can fail either, so the error
    /// sink has nothing to collect.
    ///
    /// A value holding no asset paths passes through untouched, so the caller
    /// need only gate on the type when it has its own reason to.
    pub(crate) fn resolve_schema_asset(&self, source: &Schematics, value: sdf::Value) -> sdf::Value {
        let Some(anchor) = source.resolved_location() else {
            return value;
        };
        let registry = self.composition.layer_registry();
        let mut failures = Vec::new();
        let value = sdf::resolve_asset_paths(&registry, Some(anchor), None, value, &mut failures);
        debug_assert!(
            failures.is_empty(),
            "a schema fallback evaluates nothing, so nothing can fail"
        );
        value
    }

    /// Whether the composed prim at `path` satisfies `predicate`.
    pub(crate) fn prim_matches(&self, path: &sdf::Path, predicate: PrimPredicate) -> Result<bool> {
        Ok(predicate.matches(self.prim_status_masked(path, predicate.consulted_bits())?))
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

            let children = self.masked(&path, |g, cache| cache.prim_children(g, &path))?;
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
        self.stage
            .composition
            .swap_load_rules(mem::take(&mut self.original), self.stage);
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
    schema_registry: Option<Arc<SchemaRegistry>>,
}

#[derive(Default)]
struct CollectedLayers {
    layers: Vec<sdf::Layer>,
    errors: Vec<pcp::CompositionError>,
}

/// Whether a composition error is a sublayer load diagnostic — the only kind
/// [`Stage::composition_errors`] filters against the muted-aware effective set.
fn is_sublayer_error(error: &pcp::CompositionError) -> bool {
    matches!(
        error,
        pcp::CompositionError::UnresolvedSublayer { .. } | pcp::CompositionError::MalformedSublayer { .. }
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
            schema_registry: None,
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

    /// Sets the schemas the stage resolves fallback values against.
    ///
    /// Defaults to [`SchemaRegistry::global`](SchemaRegistry::global),
    /// the process-wide registry. Supply one built through
    /// [`SchemaRegistry::builder`](SchemaRegistry::builder) to give a
    /// stage schemas the process does not have, or to give it none. The
    /// registry is pinned for the stage's life.
    pub fn schema_registry(mut self, registry: Arc<SchemaRegistry>) -> Self {
        self.schema_registry = Some(registry);
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
        // The stage root stack is one layer stack whose single expression-variable
        // context (C++ `PcpExpressionVariables`) — the root layer's own variables
        // overlaid by the session root's own — resolves the `${VAR}` sublayers of
        // both the session region and the root region. Compose it once, up front,
        // and collect both regions against it: a session sublayer can then reference
        // a variable authored on the stage root layer (and a root sublayer one on the
        // session), and composition later resolves each `${VAR}` sublayer to the same
        // layer this collection opened.
        let root_stack_vars = self.root_stack_expression_variables(root_path)?;
        let session = self.collect_optional_session_layers(&root_stack_vars)?;
        let root = self.collect_layers(root_path, &root_stack_vars)?;
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
        // The anonymous root layer authors no `expressionVariables`, so the root
        // stack context reduces to the session root's own — which `open_stack`
        // composes from the empty ancestor anyway.
        let session = self.collect_optional_session_layers(&HashMap::new())?;
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
    /// [`UnresolvedSublayer`](pcp::CompositionError::UnresolvedSublayer) collection error
    /// rather than aborting the open; one under a muted branch is filtered out
    /// later, once the muted-aware graph exists (see
    /// [`StageBuilder::make_stage`](Self::make_stage)).
    fn collect_layers(&self, path: &str, ancestor_expr_vars: &HashMap<String, sdf::Value>) -> Result<CollectedLayers> {
        let errors = RefCell::new(Vec::new());
        // `ancestor_expr_vars` are the expression variables the enclosing context
        // contributes: the session layers' composed set for the root stack, empty
        // for the session stack itself (nothing sublayers it).
        let layers = self
            .registry
            .open_stack(
                path,
                None,
                ancestor_expr_vars,
                false,
                &|error| {
                    errors.borrow_mut().push(error.into());
                    Ok(())
                },
                &|_| false,
            )?
            .ok_or_else(|| sdf::LoadError::Unresolved {
                asset_path: path.to_owned(),
            })?;
        Ok(CollectedLayers {
            layers,
            errors: errors.into_inner(),
        })
    }

    /// Collect the configured session layer (and its dependencies), if any, resolving
    /// its `${VAR}` sublayers against `root_stack_vars` — the stage root stack's single
    /// context, so a session sublayer sees variables authored on the stage root layer
    /// (C++ `PcpExpressionVariables`).
    fn collect_optional_session_layers(
        &self,
        root_stack_vars: &HashMap<String, sdf::Value>,
    ) -> Result<CollectedLayers> {
        match self.session_layer.as_deref() {
            Some(p) => self.collect_layers(p, root_stack_vars),
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

    /// The stage root stack's single expression-variable context (C++
    /// `PcpExpressionVariables`): the stage root layer's own `expressionVariables`
    /// overlaid by the session root's own (session wins), a muted session root
    /// contributing none. Read shallowly from the two root layers — their sublayers
    /// contribute nothing — since it is the fixed context both the session region's
    /// and the root region's `${VAR}` sublayers resolve against.
    fn root_stack_expression_variables(&self, root_path: &str) -> Result<HashMap<String, sdf::Value>> {
        let mut vars = self.registry.own_expression_variables(root_path, None)?;
        if let Some(session_path) = self.session_layer.as_deref() {
            let session_id = self.registry.create_identifier(session_path, None);
            let muted = !self.muted.is_empty() && self.canonical_muted_set(root_path).contains(&session_id);
            if !muted {
                let session_own = self.registry.own_expression_variables(session_path, None)?;
                sdf::expr::compose_over(&mut vars, &session_own);
            }
        }
        Ok(vars)
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
        collection_errors: Vec<pcp::CompositionError>,
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
        // Every sublayer load failure the collect pass reported, keyed for the
        // graph's failure memo below: the finalize drain then regenerates each
        // broken entry's per-stack diagnostic without re-attempting an open the
        // loader already ran.
        let failure_seeds: Vec<(String, String, pcp::LoadFailure)> = collection_errors
            .iter()
            .filter_map(|error| match error {
                pcp::CompositionError::UnresolvedSublayer {
                    asset_path,
                    introduced_by,
                } => Some((asset_path.clone(), introduced_by.clone(), pcp::LoadFailure::Unresolved)),
                pcp::CompositionError::MalformedSublayer {
                    asset_path,
                    introduced_by,
                    reason,
                } => Some((
                    asset_path.clone(),
                    introduced_by.clone(),
                    pcp::LoadFailure::Unreadable(reason.clone()),
                )),
                _ => None,
            })
            .collect();
        // The graph keeps its own regenerable diagnostics (sublayer cycles,
        // invalid relocates); the cache holds only the one-shot collection errors.
        // `Stage::composition_errors` concatenates the two.
        let stage = Stage(Rc::new(StageInner {
            composition: StageComposition::new(
                pcp::LayerGraph::new(self.registry),
                pcp::IndexCache::new(
                    self.variant_fallbacks,
                    load_rules,
                    self.population_mask,
                    collection_errors,
                ),
            ),
            initial_load_set: self.initial_load_set,
            prototypes_discovered: Cell::new(None),
            interpolation_type: Cell::new(self.interpolation_type),
            edit_target: RefCell::new(edit_target),
            layer_stack_id,
            sinks: RefCell::default(),
            edit_provenance: RefCell::new(None),
            current_generation: Cell::new(0),
            schema_registry: self.schema_registry.unwrap_or_else(|| SchemaRegistry::global().clone()),
            prim_types: RefCell::default(),
        }));
        stage
            .composition
            .initialize(layers, session_layer_count, self.muted, failure_seeds, &stage);
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
    use std::fs;
    use std::path::Path as FsPath;

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

    /// Writes the cross-stage fixture into `dir`, returning the root layer
    /// path: /M1 and /M2 payload mid1/mid2 (authoring V=a / V=b), each
    /// referencing t.usda, whose `${V}` sublayer selects a.usda / b.usda.
    fn write_cross_stage_fixture(dir: &FsPath) -> Result<String> {
        let write = |name: &str, text: &str| fs::write(dir.join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"M1\" (\n    payload = @mid1.usda@</P>\n) {}\ndef \"M2\" (\n    payload = @mid2.usda@</P>\n) {}\n",
        )?;
        for (name, sel) in [("mid1.usda", "a"), ("mid2.usda", "b")] {
            write(
                name,
                &format!(
                    "#usda 1.0\n(\n    expressionVariables = {{ string V = \"{sel}\" }}\n)\ndef \"P\" (\n    references = @t.usda@</P>\n) {{}}\n",
                ),
            )?;
        }
        write(
            "t.usda",
            "#usda 1.0\n(\n    subLayers = [@`\"${V}.usda\"`@]\n)\ndef \"P\" {\n    custom double x\n}\n",
        )?;
        write("a.usda", "#usda 1.0\nover \"P\" {\n    custom double x = 1\n}\n")?;
        write("b.usda", "#usda 1.0\nover \"P\" {\n    custom double x = 2\n}\n")?;
        Ok(dir.join("root.usda").to_str().expect("utf-8 path").to_string())
    }

    /// An arc edit target transfers between equal-input stages by stack value
    /// identity, not by graph-local handle: the two stages warm their
    /// composition in opposite orders, so the same contextual target stacks get
    /// different numeric ids per stage, and the installed target must still
    /// resolve the stack matching its captured source chain.
    #[test]
    fn cross_stage_arc_stack() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = write_cross_stage_fixture(dir.path())?;
        let m1 = sdf::Path::new("/M1")?;
        let m2 = sdf::Path::new("/M2")?;

        // Stage A composes /M1 first; stage B composes /M2 first, so the two
        // graphs mint the contextual `t.usda` stacks under opposite numbering.
        let stage_a = Stage::open(&path)?;
        let transferred = stage_a.edit_target_for_node(&m1, EditTargetArc::Reference)?;
        let stage_b = Stage::open(&path)?;
        let own_m2 = stage_b.edit_target_for_node(&m2, EditTargetArc::Reference)?;
        let own_m1 = stage_b.edit_target_for_node(&m1, EditTargetArc::Reference)?;
        let t_layer = stage_b
            .layers()
            .id_of(own_m1.layer_identifier())
            .expect("t.usda is loaded on stage B");

        // Stage B's own view of the two contextual stacks, as the reference.
        stage_b.set_edit_target(own_m1)?;
        let b_m1_stack = stage_b.mapped_target_stack_id(t_layer)?;
        stage_b.set_edit_target(own_m2)?;
        let b_m2_stack = stage_b.mapped_target_stack_id(t_layer)?;
        assert_ne!(b_m1_stack, b_m2_stack, "the two variable contexts are distinct stacks");

        stage_b.set_edit_target(transferred)?;
        assert_eq!(
            stage_b.mapped_target_stack_id(t_layer)?,
            b_m1_stack,
            "the transferred /M1 target resolves B's own /M1 contextual stack"
        );
        Ok(())
    }

    /// Resolving a transferred arc target drives the load barrier: the
    /// installing stage never composed /M1, so mid1.usda (the captured source
    /// chain) and a.usda (the sublayer its context selects) are both unloaded.
    /// The resolution loads the chain, reopens the target under its context,
    /// and interns the complete contextual stack instead of substituting
    /// another stack.
    #[test]
    fn cross_stage_loads_chain() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = write_cross_stage_fixture(dir.path())?;

        let stage_a = Stage::open(&path)?;
        let transferred = stage_a.edit_target_for_node(&sdf::Path::new("/M1")?, EditTargetArc::Reference)?;
        let stage_b = Stage::open(&path)?;
        let _ = stage_b.edit_target_for_node(&sdf::Path::new("/M2")?, EditTargetArc::Reference)?;
        let t_layer = stage_b
            .layers()
            .id_of(transferred.layer_identifier())
            .expect("t.usda is loaded on stage B through /M2");
        assert!(
            stage_b.layers().find_by_leaf("mid1.usda").is_none(),
            "premise: the source-chain layer is not loaded"
        );

        stage_b.set_edit_target(transferred)?;
        let stack = stage_b.mapped_target_stack_id(t_layer)?;

        let layers = stage_b.layers();
        assert!(layers.find_by_leaf("mid1.usda").is_some(), "the chain layer loaded");
        let has_leaf = |leaf: &str| {
            layers
                .layer_stack(stack)
                .iter()
                .any(|&(id, _)| FsPath::new(layers.identifier(id)).ends_with(leaf))
        };
        assert!(
            has_leaf("a.usda") && !has_leaf("b.usda"),
            "the resolved stack composes under mid1's V=a context"
        );
        Ok(())
    }

    /// A transferred arc target whose source-chain layer cannot be opened fails
    /// the authoring-stack resolution with a typed error: authoring into a
    /// substitute stack would land opinions in the wrong members.
    #[test]
    fn cross_stage_chain_unloadable() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = write_cross_stage_fixture(dir.path())?;

        let stage_a = Stage::open(&path)?;
        let transferred = stage_a.edit_target_for_node(&sdf::Path::new("/M1")?, EditTargetArc::Reference)?;
        drop(stage_a);
        fs::remove_file(dir.path().join("mid1.usda"))?;

        let stage_b = Stage::open(&path)?;
        let _ = stage_b.edit_target_for_node(&sdf::Path::new("/M2")?, EditTargetArc::Reference)?;
        let t_layer = stage_b
            .layers()
            .id_of(transferred.layer_identifier())
            .expect("t.usda is loaded on stage B through /M2");

        stage_b.set_edit_target(transferred)?;
        assert!(
            matches!(
                stage_b.mapped_target_stack_id(t_layer),
                Err(StageAuthoringError::EditTargetStackUnavailable { layer }) if layer.ends_with("mid1.usda")
            ),
            "the unopenable chain layer fails the resolution"
        );
        Ok(())
    }

    /// The identifier of the loaded layer whose file name is `leaf`.
    fn identifier_by_leaf(stage: &Stage, leaf: &str) -> String {
        let layers = stage.layers();
        let id = layers.find_by_leaf(leaf).expect("layer is loaded");
        layers.identifier(id).to_string()
    }

    /// Strands and reclaims /M1's contextual reference stack on the
    /// cross-stage fixture: captures the /M1 reference edit target, resolves
    /// its stack, then clears mid1's authored variables — the source flip
    /// drops /M1's index, leaving the old contextual instance unowned, and
    /// the sweep reclaims it. Returns the target layer and the reclaimed
    /// stack id.
    fn strand_m1_stack(stage: &Stage) -> Result<(pcp::LayerId, pcp::LayerStackId)> {
        let target = stage.edit_target_for_node(&sdf::Path::new("/M1")?, EditTargetArc::Reference)?;
        let t_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("t.usda is loaded");
        stage.set_edit_target(target)?;
        let before = stage.mapped_target_stack_id(t_layer)?;

        let mid1 = identifier_by_leaf(stage, "mid1.usda");
        stage
            .layer_mut(&mid1)
            .expect("mid1 is live")
            .edit(|e| e.set_expression_variables(HashMap::new()))?;
        // The drain seam drops /M1's index — the stack's only owner — and the
        // ownership loss schedules the sweep at that same seam.
        assert!(
            !stage.layers().stack_is_live(before),
            "losing the last owner reclaims the stack at the edit seam"
        );
        Ok((t_layer, before))
    }

    /// A source flip strands the old contextual stack and reclamation removes
    /// it once its only owner — the referring prim's index — drops; the
    /// re-keyed arc resolves a successor under a fresh id, never the
    /// reclaimed one, and composes the flipped context's values.
    #[test]
    fn swept_key_recomposes() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = write_cross_stage_fixture(dir.path())?;
        let stage = Stage::open(&path)?;
        let x_at_m1 = |stage: &Stage| -> Result<Option<sdf::Value>> {
            stage
                .attribute("/M1.x")?
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))
        };
        assert_eq!(x_at_m1(&stage)?, Some(sdf::Value::Double(1.0)), "V=a selects a.usda");

        let (t_layer, before) = strand_m1_stack(&stage)?;

        assert_eq!(
            x_at_m1(&stage)?,
            None,
            "the flipped context no longer selects a.usda's opinion"
        );
        let after = stage.mapped_target_stack_id(t_layer)?;
        assert_ne!(after, before, "the successor mints under a fresh id");
        assert!(stage.layers().stack_is_live(after));
        Ok(())
    }

    /// An edit target captured before a sweep stays usable after it: the
    /// carried value identity re-resolves through the demand loop, minting a
    /// successor for the reclaimed contextual stack, and an opinion authored
    /// through the target composes.
    #[test]
    fn swept_edit_target_recomposes() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = write_cross_stage_fixture(dir.path())?;
        let stage = Stage::open(&path)?;
        let (t_layer, before) = strand_m1_stack(&stage)?;

        // Resolve the dormant target first — no query has recomposed /M1, so
        // the demand loop itself must recompose the reclaimed chain.
        let after = stage.mapped_target_stack_id(t_layer)?;
        assert_ne!(after, before, "the dormant identity resolves a fresh successor");
        assert!(stage.layers().stack_is_live(after));

        stage.attribute("/M1.x")?.set(sdf::Value::Double(7.0))?;
        assert_eq!(
            stage
                .attribute("/M1.x")?
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(7.0)),
            "the opinion authored through the recomposed target composes"
        );
        Ok(())
    }

    /// Diagnostics stay coupled to composition state, not cache warmth: an
    /// unresolved-selection error retires with the stack once nothing owns
    /// it, recomposition re-derives the successor's own diagnostic, and a
    /// later edit round's failure requeue resurrects neither.
    #[test]
    fn sweep_clears_stack_diagnostics() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"M1\" (\n    payload = @mid1.usda@</P>\n) {}\n",
        )?;
        write(
            "mid1.usda",
            "#usda 1.0\n(\n    expressionVariables = { string V = \"missing\" }\n)\ndef \"P\" (\n    references = @t.usda@</P>\n) {}\n",
        )?;
        write(
            "t.usda",
            "#usda 1.0\n(\n    subLayers = [@`\"${V}.usda\"`@]\n)\ndef \"P\" {}\n",
        )?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        let mentions = |stage: &Stage, needle: &str| {
            stage
                .composition_errors()
                .iter()
                .any(|error| error.to_string().contains(needle))
        };
        assert!(stage.prim("/M1")?.is_defined()?, "the payload chain composes");
        assert!(mentions(&stage, "missing.usda"), "the unresolved selection reports");

        // Clearing mid1's variables re-keys the arc away from the old
        // contextual stack; the sweep retires it together with its bucket.
        let (_, old) = strand_m1_stack(&stage)?;
        assert!(
            !mentions(&stage, "missing.usda"),
            "the reclaimed stack's diagnostic retires with it"
        );

        // Recomposition re-derives diagnostics from current state: the
        // flipped context leaves `${V}` undefined, so the successor reports
        // V.usda.
        let _ = stage.prim("/M1")?.is_defined()?;
        assert!(!stage.layers().stack_is_live(old));
        assert!(
            mentions(&stage, "V.usda"),
            "the successor stack's own unresolved selection reports"
        );

        // An edit clears the load-failure memo and requeues failures from the
        // surviving buckets; the reclaimed bucket is gone, so no demand
        // derives against the dead stack and the survivor keeps reporting.
        stage.set_edit_target(stage.edit_target_root())?;
        stage.define_prim("/Zed")?;
        assert!(!mentions(&stage, "missing.usda"));
        assert!(mentions(&stage, "V.usda"));
        Ok(())
    }

    /// A source flip strands a whole fan of contextual stacks at once, and
    /// the flip edit's own pending-drain seam — no bypassing sweep call —
    /// reclaims them: dropping the referring indices releases every fan
    /// member's last owner, which schedules the sweep directly.
    #[test]
    fn gated_seam_reclaims() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        let fan = 3;
        let mut root_text = String::from("#usda 1.0\n");
        let mut mid_text = String::from("#usda 1.0\n(\n    expressionVariables = { string V = \"a\" }\n)\n");
        for i in 0..fan {
            root_text.push_str(&format!("def \"P{i}\" (\n    payload = @mid.usda@</P{i}>\n) {{}}\n"));
            mid_text.push_str(&format!("def \"P{i}\" (\n    references = @t{i}.usda@</P>\n) {{}}\n"));
            write(
                &format!("t{i}.usda"),
                "#usda 1.0\ndef \"P\" {\n    custom double x\n}\n",
            )?;
        }
        write("root.usda", &root_text)?;
        write("mid.usda", &mid_text)?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        for i in 0..fan {
            assert!(stage.prim(format!("/P{i}"))?.is_defined()?);
        }
        let target = stage.edit_target_for_node(&sdf::Path::new("/P0")?, EditTargetArc::Reference)?;
        let t_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("t0.usda is loaded");
        stage.set_edit_target(target)?;
        let before = stage.mapped_target_stack_id(t_layer)?;
        stage.set_edit_target(stage.edit_target_root())?;

        // The flip drops every referring index, orphaning the whole fan; the
        // drain seam of the next composed read sweeps it.
        let mid = identifier_by_leaf(&stage, "mid.usda");
        stage
            .layer_mut(&mid)
            .expect("mid is live")
            .edit(|e| e.set_expression_variables(HashMap::new()))?;
        assert!(stage.prim("/P0")?.is_defined()?);
        assert!(
            !stage.layers().stack_is_live(before),
            "the gated seam sweep reclaims the stranded stack"
        );
        Ok(())
    }

    /// Warming a referenced prim and then removing it reclaims its target
    /// stack and diagnostic at the next sweep, without the deleted path ever
    /// being queried again.
    #[test]
    fn deleted_prim_reclaims() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"D\" (\n    references = @t.usda@</P>\n) {}\ndef \"Other\" {}\n",
        )?;
        write(
            "t.usda",
            "#usda 1.0\n(\n    subLayers = [@gone.usda@]\n)\ndef \"P\" {}\n",
        )?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        let mentions_gone = |stage: &Stage| {
            stage
                .composition_errors()
                .iter()
                .any(|error| error.to_string().contains("gone.usda"))
        };
        assert!(stage.prim("/D")?.is_defined()?, "the reference composes");
        assert!(mentions_gone(&stage), "the missing sublayer reports");
        let target = stage.edit_target_for_node(&sdf::Path::new("/D")?, EditTargetArc::Reference)?;
        let t_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("t.usda is loaded");
        stage.set_edit_target(target)?;
        let stack = stage.mapped_target_stack_id(t_layer)?;
        stage.set_edit_target(stage.edit_target_root())?;

        assert!(stage.remove_prim("/D")?, "the prim spec is removed");
        assert!(
            !stage.layers().stack_is_live(stack),
            "the deleted prim's target stack is reclaimed at the edit seam, without a re-query"
        );
        assert!(!mentions_gone(&stage), "its diagnostic retires with it");
        Ok(())
    }

    /// Repeatedly warming and deleting referenced prims keeps the registry
    /// and the diagnostic buckets bounded: each cycle's stack and error are
    /// reclaimed before the next.
    #[test]
    fn repeated_delete_bounded() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        let cycles = 5;
        let mut root_text = String::from("#usda 1.0\n");
        for i in 0..cycles {
            root_text.push_str(&format!("def \"D{i}\" (\n    references = @t.usda@</P>\n) {{}}\n"));
        }
        write("root.usda", &root_text)?;
        write(
            "t.usda",
            "#usda 1.0\n(\n    subLayers = [@gone.usda@]\n)\ndef \"P\" {}\n",
        )?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        let mut baseline = None;
        for i in 0..cycles {
            assert!(stage.prim(format!("/D{i}"))?.is_defined()?);
            assert!(stage.remove_prim(format!("/D{i}"))?);
            let counts = {
                let layers = stage.layers();
                (layers.live_stack_count(), layers.diagnostic_bucket_count())
            };
            match baseline {
                None => baseline = Some(counts),
                Some(baseline) => assert_eq!(
                    counts, baseline,
                    "registry and diagnostics stay bounded across delete cycles"
                ),
            }
        }
        Ok(())
    }

    /// A single unload releases the payload target's last cache owner, and
    /// the load-rules seam itself sweeps: stack and diagnostic retire without
    /// any re-query, and reloading recomposes both.
    #[test]
    fn single_unload_reclaims() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"L\" (\n    payload = @p.usda@</P>\n) {}\n",
        )?;
        write(
            "p.usda",
            "#usda 1.0\n(\n    subLayers = [@gone.usda@]\n)\ndef \"P\" {}\n",
        )?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        let mentions_gone = |stage: &Stage| {
            stage
                .composition_errors()
                .iter()
                .any(|error| error.to_string().contains("gone.usda"))
        };
        assert!(stage.prim("/L")?.is_defined()?, "the payload composes");
        assert!(mentions_gone(&stage), "the missing sublayer reports");
        let target = stage.edit_target_for_node(&sdf::Path::new("/L")?, EditTargetArc::Payload)?;
        let p_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("p.usda is loaded");
        stage.set_edit_target(target)?;
        let stack = stage.mapped_target_stack_id(p_layer)?;
        stage.set_edit_target(stage.edit_target_root())?;

        stage.unload("/L")?;
        assert!(
            !stage.layers().stack_is_live(stack),
            "the unload seam reclaims the orphaned payload stack"
        );
        assert!(!mentions_gone(&stage), "its diagnostic retires with it");

        stage.load("/L", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/L")?.is_defined()?, "reloading recomposes");
        assert!(mentions_gone(&stage), "recomposition re-derives the diagnostic");
        Ok(())
    }

    /// A single mute releases the reference target's last cache owner, and
    /// the mute seam itself sweeps; unmuting and re-querying recomposes the
    /// target and re-derives its diagnostic.
    #[test]
    fn single_mute_reclaims() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"M\" (\n    references = @t.usda@</P>\n) {}\n",
        )?;
        write(
            "t.usda",
            "#usda 1.0\n(\n    subLayers = [@gone.usda@]\n)\ndef \"P\" {}\n",
        )?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        let mentions_gone = |stage: &Stage| {
            stage
                .composition_errors()
                .iter()
                .any(|error| error.to_string().contains("gone.usda"))
        };
        assert!(stage.prim("/M")?.is_defined()?, "the reference composes");
        assert!(mentions_gone(&stage), "the missing sublayer reports");
        let target = stage.edit_target_for_node(&sdf::Path::new("/M")?, EditTargetArc::Reference)?;
        let t_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("t.usda is loaded");
        stage.set_edit_target(target)?;
        let stack = stage.mapped_target_stack_id(t_layer)?;
        stage.set_edit_target(stage.edit_target_root())?;

        let t_id = identifier_by_leaf(&stage, "t.usda");
        stage.mute_layer(t_id.clone());
        assert!(
            !stage.layers().stack_is_live(stack),
            "the mute seam reclaims the orphaned reference stack"
        );
        assert!(!mentions_gone(&stage), "its diagnostic retires with it");

        stage.unmute_layer(&t_id);
        assert!(stage.prim("/M")?.is_defined()?, "unmuting recomposes");
        assert!(mentions_gone(&stage), "recomposition re-derives the diagnostic");
        Ok(())
    }

    /// A stack shared by several cached prims survives until its final cache
    /// owner is removed.
    #[test]
    fn shared_stack_survives() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    references = @t.usda@</P>\n) {}\ndef \"B\" (\n    references = @t.usda@</P>\n) {}\n",
        )?;
        write("t.usda", "#usda 1.0\ndef \"P\" {}\n")?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        assert!(stage.prim("/A")?.is_defined()?);
        assert!(stage.prim("/B")?.is_defined()?);
        let target = stage.edit_target_for_node(&sdf::Path::new("/A")?, EditTargetArc::Reference)?;
        let t_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("t.usda is loaded");
        stage.set_edit_target(target)?;
        let stack = stage.mapped_target_stack_id(t_layer)?;
        stage.set_edit_target(stage.edit_target_root())?;

        assert!(stage.remove_prim("/A")?);
        assert!(
            stage.layers().stack_is_live(stack),
            "the shared stack survives while another cached prim owns it"
        );
        assert!(stage.remove_prim("/B")?);
        assert!(
            !stage.layers().stack_is_live(stack),
            "removing the final owner reclaims the shared stack"
        );
        Ok(())
    }

    /// Deletion through a direct layer edit — not `Stage::remove_prim` —
    /// reclaims the same way: ownership follows the cached index, not the
    /// authoring entry point.
    #[test]
    fn direct_delete_reclaims() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"D\" (\n    references = @t.usda@</P>\n) {}\n",
        )?;
        write("t.usda", "#usda 1.0\ndef \"P\" {}\n")?;
        let root_path = dir.path().join("root.usda");
        let stage = Stage::open(root_path.to_str().expect("utf-8 path"))?;

        assert!(stage.prim("/D")?.is_defined()?);
        let target = stage.edit_target_for_node(&sdf::Path::new("/D")?, EditTargetArc::Reference)?;
        let t_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("t.usda is loaded");
        stage.set_edit_target(target)?;
        let stack = stage.mapped_target_stack_id(t_layer)?;
        stage.set_edit_target(stage.edit_target_root())?;

        let root_id = identifier_by_leaf(&stage, "root.usda");
        let d_path = sdf::Path::new("/D")?;
        stage
            .layer_mut(&root_id)
            .expect("root is live")
            .edit(|e| e.remove_spec(&d_path).map(|_| ()))?;
        assert!(
            !stage.layers().stack_is_live(stack),
            "a direct-layer deletion reclaims the target stack too"
        );
        Ok(())
    }

    /// A node cloned out of a dropped index is a weak snapshot: after its
    /// stack is reclaimed, `node_layer_stack` reports `None` rather than an
    /// empty-but-plausible member list.
    #[test]
    fn stale_node_returns_none() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = write_cross_stage_fixture(dir.path())?;
        let stage = Stage::open(&path)?;
        assert!(stage.prim("/M1")?.is_defined()?);

        let index = stage.prim_index("/M1")?.graph()?;
        let target = stage.edit_target_for_node(&sdf::Path::new("/M1")?, EditTargetArc::Reference)?;
        let t_layer = stage
            .layers()
            .id_of(target.layer_identifier())
            .expect("t.usda is loaded");
        stage.set_edit_target(target)?;
        let before = stage.mapped_target_stack_id(t_layer)?;
        let node = index
            .nodes()
            .find(|node| node.layer_stack_id() == before)
            .expect("the reference node composes in the contextual stack");
        assert!(stage.node_layer_stack(node).is_some(), "a live node's members resolve");

        strand_m1_stack(&stage)?;
        assert!(
            stage.node_layer_stack(node).is_none(),
            "a reclaimed stack reads as None, not as an empty stack"
        );
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
            .set_connection_paths([target.clone()])
            .unwrap();
        });

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, Vec::new());
        let attr = crate::usd::Attribute::new(&stage, input.clone());

        assert_eq!(attr.connections()?, vec![target.clone()]);
        assert!(attr.remove_connection(&target)?);
        assert!(attr.connections()?.is_empty());

        let op = stage
            .root_layer()
            .attribute(input.clone())?
            .expect("delete authored on the root layer")
            .connection_path_list()
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
            .set_connection_paths([target.clone()])
            .unwrap();
        });

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, Vec::new());
        let attr = crate::usd::Attribute::new(&stage, input.clone());
        let attr = attr.add_connection(target.clone())?;

        assert_eq!(attr.connections()?, vec![target.clone()]);
        // The dedup leaves the root layer without any local connection
        // opinion; the composed target keeps coming from the weak layer.
        assert!(
            stage
                .root_layer()
                .attribute(input.clone())?
                .and_then(|attr| attr.connection_path_list())
                .is_none()
        );
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
            .set_connection_paths([target.clone()])
            .unwrap();
        });

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, Vec::new());
        let attr = crate::usd::Attribute::new(&stage, input.clone());

        assert!(attr.remove_connection(&target)?);
        assert!(attr.connections()?.is_empty());
        let attr = attr.add_connection(target.clone())?;

        assert_eq!(attr.connections()?, vec![target.clone()]);
        let op = stage
            .root_layer()
            .attribute(input.clone())?
            .expect("authored on the root layer")
            .connection_path_list()
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
        )?)?;
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
        )?)?;
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
                .attribute("/A.x")?
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
                .attribute("/A.x")?
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
                .attribute("/A.x")?
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
                .attribute("/A.x")?
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
            .attribute("/P.x")?
            .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?;
        // `/Q` reaches the same target carrying `V=chosen`; the target's `${V}`
        // sublayer must resolve and contribute `chosen.usda`'s opinion.
        assert_eq!(
            stage
                .attribute("/Q.x")?
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
                .attribute("/Q.x")?
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(42.0)),
            "the variable-carrying arc resolves the `${{V}}` sublayer",
        );
        // `/P` reaches the same target with no variable. Its `${V}` sublayer cannot
        // resolve, so `/P.x` stays absent — not polluted by `/Q`'s context.
        assert_eq!(
            stage
                .attribute("/P.x")?
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
                .attribute("/A.x")?
                .get_at::<sdf::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(sdf::Value::Double(5.0)),
            "the dot-relative sublayer composes its opinion"
        );
        Ok(())
    }

    /// Reads the composed `/A.x` default value as an `f64`, for the muting tests.
    fn read_ax(stage: &Stage) -> Result<Option<f64>> {
        stage.attribute("/A.x")?.get_at::<f64>(crate::usd::TimeCode::new(0.0))
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

    /// Muting a session layer prunes the session descendants its `${VAR}` sublayers
    /// bring in, not only the layers a plain sublayer names. The session root's
    /// `CHILD` variable expands to `strong.usda`; muting the session root must drop
    /// `strong.usda` from the composed stack even though the edge is an expression the
    /// context-free graph does not carry.
    #[test]
    fn mute_session_expr_subtree() -> Result<()> {
        let mut session = sdf::Layer::new_in_memory("session.usda");
        edit_layer(&mut session, |e| {
            let mut pr = e.pseudo_root_mut().unwrap();
            pr.set_expression_variables(HashMap::from([(
                "CHILD".to_string(),
                sdf::Value::String("strong".into()),
            )]));
            pr.set_sublayers([r#"`"${CHILD}.usda"`"#]);
        });
        let stage = Stage::builder().make_stage(
            vec![
                session,
                opinion_layer("strong.usda", 2.0)?,
                opinion_layer("root.usda", 1.0)?,
            ],
            2,
            Vec::new(),
        );
        assert_eq!(
            read_ax(&stage)?,
            Some(2.0),
            "the expression-resolved session sublayer contributes"
        );

        stage.mute_layer("session.usda");
        assert_eq!(
            read_ax(&stage)?,
            Some(1.0),
            "muting the session root drops its expression-resolved sublayer subtree, so the root wins"
        );

        stage.unmute_layer("session.usda");
        assert_eq!(read_ax(&stage)?, Some(2.0), "unmuting restores the expression subtree");
        Ok(())
    }

    /// The pruned session subtree follows expression edges below a muted *intermediate*
    /// session layer too. `mid` (a plain session sublayer) expands `${CHILD}` — a
    /// variable authored on the session root — to `strong.usda`; muting `mid` drops
    /// `strong.usda` with it.
    #[test]
    fn mute_intermediate_expr_subtree() -> Result<()> {
        let mut session = sdf::Layer::new_in_memory("session.usda");
        edit_layer(&mut session, |e| {
            let mut pr = e.pseudo_root_mut().unwrap();
            pr.set_expression_variables(HashMap::from([(
                "CHILD".to_string(),
                sdf::Value::String("strong".into()),
            )]));
            pr.set_sublayers(["mid.usda"]);
        });
        let mut mid = sdf::Layer::new_in_memory("mid.usda");
        edit_layer(&mut mid, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${CHILD}.usda"`"#]);
        });
        let stage = Stage::builder().make_stage(
            vec![
                session,
                mid,
                opinion_layer("strong.usda", 2.0)?,
                opinion_layer("root.usda", 1.0)?,
            ],
            3,
            Vec::new(),
        );
        assert_eq!(
            read_ax(&stage)?,
            Some(2.0),
            "the expression sublayer under mid contributes"
        );

        stage.mute_layer("mid.usda");
        assert_eq!(
            read_ax(&stage)?,
            Some(1.0),
            "muting mid drops the strong.usda it expands to"
        );
        Ok(())
    }

    /// Unmuting a layer selected only through a stack variable invalidates the prim
    /// indices composed against its stack. The root's `${V}` sublayer resolves to
    /// `strong.usda`, which contributes the child prim `/A/Child`; that edge is absent
    /// from the context-free graph, so the mute fanout must still reach the root layer,
    /// or the cached-miss index for `/A/Child` keeps it absent after `strong` returns.
    #[test]
    fn unmute_expr_sublayer_recomposes() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            let mut pr = e.pseudo_root_mut().unwrap();
            pr.set_expression_variables(HashMap::from([("V".to_string(), sdf::Value::String("strong".into()))]));
            pr.set_sublayers([r#"`"${V}.usda"`"#, "weak.usda"]);
        });
        let mut strong = sdf::Layer::new_in_memory("strong.usda");
        edit_layer(&mut strong, |e| {
            sdf::AttributeSpec::new(e.data_mut(), "/A/Child.y", "double", sdf::Variability::Varying, true)
                .unwrap()
                .set_default(sdf::Value::Double(5.0));
        });
        let stage = Stage::builder().make_stage(vec![root, strong, opinion_layer("weak.usda", 1.0)?], 0, Vec::new());
        assert!(
            stage.prim("/A/Child")?.is_valid()?,
            "the expression sublayer strong.usda contributes /A/Child"
        );

        stage.mute_layer("strong.usda");
        assert!(
            !stage.prim("/A/Child")?.is_valid()?,
            "muting strong.usda removes its /A/Child"
        );

        stage.unmute_layer("strong.usda");
        assert!(
            stage.prim("/A/Child")?.is_valid()?,
            "unmuting recomposes the index so /A/Child, selected via the expression sublayer, returns"
        );
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
        let query = stage.attribute("/A.x")?.query();
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
        let read_px = |stage: &Stage| stage.attribute("/P.x")?.get_at::<f64>(crate::usd::TimeCode::new(0.0));
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
        assert!(stage.prim(refp.clone())?.is_valid()?);
        assert!(stage.prim(indep.clone())?.is_valid()?);
        assert!(stage.is_indexed(&refp) && stage.is_indexed(&indep));

        stage.mute_layer("target.usda");
        assert!(!stage.is_indexed(&refp), "the referencing prim is recomposed");
        assert!(stage.is_indexed(&indep), "the independent prim keeps its cached index");

        // Rebuild the referencing prim's index (now recording the muted target),
        // then unmute and confirm it is dropped again while the sibling stays warm.
        assert!(stage.prim(refp.clone())?.is_valid()?);
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
        assert!(stage.prim(p.clone())?.is_valid()?);
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
        assert!(stage.prim(refp.clone())?.is_valid()?);
        assert!(stage.prim(indep.clone())?.is_valid()?);
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
        let ref_x = || stage.attribute("/Ref.x")?.get::<f64>();
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
        assert!(!stage.prim(newp.clone())?.is_valid()?, "the prim is absent");
        assert!(stage.is_indexed(&newp), "the miss is cached");

        // Add a root sublayer that defines the prim.
        let mut over = sdf::Layer::new_in_memory("over.usda");
        edit_layer(&mut over, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/New", sdf::Specifier::Def, "").unwrap();
        });
        stage.insert_layer("root.usda", 0, over, sdf::LayerOffset::IDENTITY)?;
        assert!(
            stage.prim(newp.clone())?.is_valid()?,
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
            !stage.prim(missing.clone())?.is_valid()?,
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
            stage.prim(missing.clone())?.is_valid()?,
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
        let read = |s: &Stage| s.attribute("/A.x")?.get_at::<f64>(crate::usd::TimeCode::new(8.0));

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
            stage.attribute("/A.x")?.get::<f64>()?,
            Some(1.0),
            "the WHICH-valued sublayer resolves to a.usda"
        );
        stage.set_expression_variables(HashMap::from([("WHICH".to_string(), sdf::Value::String("b".into()))]))?;
        assert_eq!(
            stage.attribute("/A.x")?.get::<f64>()?,
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
            stage.attribute("/A.x")?.get::<f64>()?,
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
        assert!(stage.prim("/FromRoot")?.is_valid()?);
        assert!(stage.prim("/FromWeak")?.is_valid()?);
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
            !stage.prim("/FromRoot")?.is_valid()?,
            "the staged root edit rolled back with the batch"
        );
        Ok(())
    }

    /// A dry run validates against composed state, so the seam takes the settled
    /// borrow: reaching it with an edit still queued trips the backstop rather
    /// than validating against a stale graph.
    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "settled composition access")]
    fn dry_run_requires_settled() {
        let stage = in_memory_stage().expect("stage");
        let root = stage.root_layer().identifier().to_string();
        let root_id = stage.layers().id_of(&root).expect("root layer id");
        stage
            .layer_mut(&root)
            .expect("root layer")
            .edit(|e| {
                sdf::PrimSpec::new(e.data_mut(), "/Queued", sdf::Specifier::Def, "")?;
                Ok(())
            })
            .expect("direct edit commits");
        // No composed read since that commit, so the edit is still queued.
        let _ = stage.author_layers_txn(
            &[root_id],
            None,
            false,
            |_ids, _edits| Ok::<(), StageAuthoringError>(()),
        );
    }

    /// A batch that authors nothing reports no change; the flag comes from the
    /// transaction, not from the batch being non-empty.
    #[test]
    fn batch_edit_no_op() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.root_layer().identifier().to_string();
        assert!(!stage.batch_edit(&[&root], |_edits| Ok(()))?);
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
