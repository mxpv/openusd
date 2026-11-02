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

use std::borrow::Cow;
use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::Deref;
use std::rc::{Rc, Weak};
use std::sync::Arc;
use std::thread;

use bitflags::bitflags;

use crate::tf::Token;
use crate::{Result, ar, pcp, sdf, vt};

use super::composition::{self, PendingEdit, StageComposition};

use super::authoring::{Operation, PlanStamp, PlanState, PrimOp};
use super::interp::{self, InterpolationType};
use super::sink::{PendingChange, Provenance, StageSink, StageSinkId, TxnObserver, keep_ancestors};
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

impl PrimStatus {
    /// The bits a prim composes from its parent's status and its own opinions
    /// (C++ `Usd_PrimData::_ComposeAndCacheFlags`), answered together: the
    /// three the default traversal requires and the one it rejects.
    const INHERITED: PrimStatus = PrimPredicate::INHERITED_REQUIRED.union(PrimPredicate::INHERITED_REJECTED);

    /// The pseudo-root's status, which every root prim composes from: active,
    /// loaded and defined, as C++ `Usd_PrimData` sets it.
    const ROOT: PrimStatus = PrimStatus::ACTIVE.union(PrimStatus::LOADED).union(PrimStatus::DEFINED);
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

/// The status a prim composed when a walk listed it, for the walk to hand
/// back when it lists the prim's own children
/// ([`Prim::filtered_children_from`](super::Prim::filtered_children_from)).
///
/// A prim's active, loaded, defined and abstract bits come from its parent's
/// and its own opinions (C++ `Usd_PrimData::_ComposeAndCacheFlags`). A walk
/// that hands each prim's status down composes each prim once, where a
/// prim asked on its own composes every prim above it.
///
/// The status is that of one prim of one stage under the stage's population
/// when it was read. It is passed over for a fresh read once the population
/// has changed, and where it is handed to another prim than the one it was
/// read for.
#[derive(Debug, Clone)]
pub struct ComposedStatus {
    /// The prim the status is of.
    prim: super::Prim,
    /// The prim's inherited bits, and its `INSTANCE` bit where
    /// `instance_known`.
    status: PrimStatus,
    /// Whether `status` says if the prim is an instance.
    instance_known: bool,
    /// The population epoch `status` was read under.
    epoch: u64,
}

impl ComposedStatus {
    /// Whether the prim is an instance, or `None` where the listing that
    /// composed the status did not ask: one under a predicate that
    /// traverses instance proxies stops at no instance, and has no need to
    /// know.
    pub fn is_instance(&self) -> Option<bool> {
        self.instance_known.then(|| self.status.contains(PrimStatus::INSTANCE))
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
        let stripped = var_sel_path.strip_variant_selections();
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
        match scene_path.embedded_target() {
            None => Some(mapped),
            Some(target) => {
                let mapped_target = self.map_to_spec_target_path(&target).ok()?;
                mapped.replace_embedded_target(&mapped_target)
            }
        }
    }

    /// Maps a target-valued path — a relationship target, attribute
    /// connection, inherit, or specialize — from scene namespace into this
    /// target's layer namespace. Target paths never carry variant selections,
    /// so the mapped result is stripped of them; under a variant target this
    /// maps a path to itself. A path outside the mapping's co-domain is
    /// [`OutsideEditTarget`](StageAuthoringError::OutsideEditTarget).
    pub(super) fn map_to_spec_target_path(&self, scene_path: &sdf::Path) -> Result<sdf::Path, StageAuthoringError> {
        self.mapping
            .map_target_to_source(scene_path)
            .map(|mapped| mapped.strip_variant_selections())
            .ok_or_else(|| StageAuthoringError::OutsideEditTarget {
                path: scene_path.clone(),
            })
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

    /// Maps a stage (scene) value authored on the object at `object_path` (a
    /// prim or one of its properties) to the one the write should put in the
    /// source layer, retiming every `timecode` it holds and mapping every path
    /// expression (C++ `_StageValueToFieldXf` and `_PathExprToField`).
    ///
    /// A `timecode` is a time coordinate in the same frame as the key a sample
    /// is authored at, so it runs through the same inverse offset and likewise
    /// reads back unchanged once composition re-applies the arc's offset. A
    /// `pathExpression`, wherever it sits — the value itself, an element, a
    /// dictionary entry, a time sample — is made absolute against the owning
    /// prim, then each pattern prefix and reference path is mapped
    /// target-to-source through this target's namespace mapping; an atom the
    /// mapping cannot reach becomes the empty expression, and a `%_` or
    /// `%:name` reference keeps its empty path. Any other value passes
    /// through. A local or variant target carries the identity offset and
    /// mapping, so through one only the anchoring applies.
    pub fn map_to_spec_value(&self, object_path: &sdf::Path, value: impl Into<vt::Value>) -> vt::Value {
        let value = value.into();
        // TODO(perf): an owned sample map is cloned to be retimed.
        self.to_spec(&OnceCell::new(), object_path, &value).unwrap_or(value)
    }

    /// `value` as [`map_to_spec_value`](Self::map_to_spec_value) maps it, or
    /// `None` where nothing in it changes: the one walk of C++
    /// `_StageValueToFieldXf`, whose sample-map arm moves the times and walks
    /// each sample through the same transform. `anchor` holds the owning
    /// prim's path once a path expression needs it.
    fn to_spec(&self, anchor: &OnceCell<sdf::Path>, object_path: &sdf::Path, value: &vt::Value) -> Option<vt::Value> {
        let offset = self.spec_time_offset();
        let map = |expr: sdf::PathExpression| {
            expr.make_absolute(anchor.get_or_init(|| object_path.prim_path()))
                .map_paths(|path| self.mapping.map_target_to_source(path))
        };
        value.try_transform(&mut |value| match value {
            vt::Value::TimeCode(_) | vt::Value::TimeCodeVec(_) => offset.apply_to_value(value),
            vt::Value::TimeSamples(samples) if !offset.is_identity() => {
                let mut samples = samples.clone();
                offset.retime_samples(&mut samples, |sample| self.to_spec(anchor, object_path, sample));
                Some(vt::Value::TimeSamples(samples))
            }
            vt::Value::PathExpression(_) | vt::Value::PathExpressionVec(_) => value.map_path_expressions(map),
            _ => None,
        })
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
        {
            let mut saved = self.stage.saved_edit_targets.borrow_mut();
            if let Some(at) = saved.iter().rposition(|layer| layer == self.saved.layer_identifier()) {
                saved.remove(at);
            }
        }
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

    /// No prim composes at the path, so there is nothing to author against:
    /// a prim-handle setter never conjures a prim (C++ `UsdPrim` setters on
    /// an invalid prim).
    #[error("no prim composes at {path}")]
    PrimNotValid {
        /// The path nothing composes at.
        path: sdf::Path,
    },

    /// The path lies inside an instancing prototype (`/__Prototype_N`), a
    /// composed namespace nothing authors into (C++ `_ValidateEditPrim`:
    /// "authoring to an instancing prototype is not allowed").
    #[error("authoring to an instancing prototype is not allowed: {path}")]
    PrototypeEdit {
        /// The prototype path the edit named.
        path: sdf::Path,
    },

    /// The path is an instance proxy — a view into a prototype through an
    /// instance — so an opinion authored there would compose nowhere
    /// (C++ `_ValidateEditPrim`: "authoring to an instance proxy is not
    /// allowed").
    #[error("authoring to an instance proxy is not allowed: {path}")]
    InstanceProxyEdit {
        /// The instance-proxy path the edit named.
        path: sdf::Path,
    },
    /// A relationship target or attribute connection names a prototype, or
    /// an object within one, which no layer can name (C++
    /// `UsdRelationship::_GetTargetForAuthoring`: "Cannot target a prototype
    /// or an object within a prototype").
    #[error("a target cannot name a prototype or an object within one: {path}")]
    PrototypeTarget {
        /// The target as given.
        path: sdf::Path,
    },

    /// The layer at the current edit target rejected the authoring call.
    #[error(transparent)]
    Layer(sdf::AuthoringError),

    /// A value does not fit the attribute's declared type, or the declaration
    /// itself is unusable — whether the composed declaration said so, before
    /// the write, or the edit target's own, as the spec was written. Every
    /// path into this error lifts the layer tier's
    /// [`AuthoringError::ValueType`](sdf::AuthoringError::ValueType) here, so
    /// there is one variant to match.
    #[error(transparent)]
    ValueType(#[from] sdf::ValueTypeError),

    /// The edit-target layer declares the attribute as a type that does not
    /// agree with the composed one, so writing the composed-type value would
    /// leave the layer inconsistent with its own declaration.
    #[error(transparent)]
    LocalTypeConflict(Box<TypeConflict>),

    /// The edit target, or a declaration it would copy, holds a property of
    /// the other kind at the path: an attribute where a relationship was asked
    /// for, or the reverse.
    #[error("{path} is a {found} spec where a {expected} spec was expected")]
    SpecKindMismatch {
        /// The property path.
        path: sdf::Path,
        /// The kind the call needed.
        expected: sdf::SpecType,
        /// The kind found instead.
        found: sdf::SpecType,
    },

    /// The field is authored only through its dedicated, validated setter,
    /// never through the generic metadata calls.
    #[error("field {field} is authored through its own setter, not as metadata")]
    ReservedField {
        /// The refused field.
        field: &'static str,
    },

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

    /// The layer's identifier is not the spelling the stage's resolver gives
    /// a layer of that name
    /// ([`in_memory_identifier`](ar::Resolver::in_memory_identifier)), so no
    /// asset path authored in the stage would reach the layer under it.
    #[error(
        "layer identifier {identifier:?} is not canonical under the stage's resolver, which spells it {expected:?}"
    )]
    IncompatibleLayerIdentifier {
        /// The layer's identifier.
        identifier: String,
        /// The spelling the stage's resolver gives it.
        expected: String,
    },

    /// The edit target moved while a [`StageEdit`](super::StageEdit) was open.
    /// Every queued property resolved its spec path, its value and its sample
    /// time through the target the batch planned against, so committing them
    /// through another one would write them somewhere else.
    #[error("the edit target moved while the batch was open")]
    EditTargetMoved,

    /// A property planned on one stage was handed to another stage's
    /// [`StageEdit`](super::StageEdit), which has none of that stage's
    /// layers to write it to.
    #[error("property {path} belongs to another stage than the batch")]
    EditOfAnotherStage {
        /// The property's path on its own stage.
        path: sdf::Path,
    },

    /// A prim operation queued in a [`StageEdit`](super::StageEdit) would
    /// change the schema of a prim a queued property was planned against, or
    /// a property was planned against a schema the batch has since changed.
    /// The property's declaration came from the schema the commit would not
    /// leave.
    #[error("a queued property under {path} was planned against a schema the batch changes")]
    PlannedTypeChanged {
        /// The prim whose schema changed.
        path: sdf::Path,
    },

    /// A [`StageEdit`](super::StageEdit) cannot tell what the prim at `path`
    /// composes to: a spec the batch queued revives a culled arc target its
    /// composition reads, which only rebuilding the prim's index answers.
    #[error("the effect of the batch's queued specs on {path} cannot be planned")]
    PlannedEffectUnknown {
        /// The prim the batch cannot plan against.
        path: sdf::Path,
    },

    /// A change made outside a [`StageEdit`](super::StageEdit) while it was
    /// open — a commit, a muting or load-rule change — moved a prim the batch
    /// had read, so its plans no longer hold.
    #[error("{path} changed while the batch was open")]
    PlanStale {
        /// The prim that changed.
        path: sdf::Path,
    },

    /// A [`StageEdit`](super::StageEdit) was given the same property twice.
    /// Each queued property resolves its declaration before the batch opens, so
    /// a second plan for one property would be resolved against a stage the
    /// first has not changed yet.
    #[error("property {path} appears more than once in the batch")]
    DuplicateProperty {
        /// The repeated property's path.
        path: sdf::Path,
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

    /// An edit target is asked of a variant set that selects no variant on
    /// its prim, so there is no variant to author into.
    #[error("variant set {set:?} on {prim} selects no variant")]
    NoVariantSelection {
        /// The prim.
        prim: sdf::Path,
        /// The variant set.
        set: String,
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

    /// The layers' store refused the edit, most often because a read or an
    /// edit of the stage's layers was already in progress
    /// ([`sdf::LayerError::Busy`]). An edit's own failure is not this variant.
    #[error(transparent)]
    Registry(sdf::LayerError),
}

/// The payload of [`StageAuthoringError::LocalTypeConflict`]: which
/// declaration composition found and which the edit-target layer holds.
#[derive(Debug, thiserror::Error)]
#[error("{path} composes as {effective} but the edit-target layer declares it {local}")]
pub struct TypeConflict {
    /// The attribute path.
    pub path: sdf::Path,
    /// The composed declaration the value was validated against.
    pub effective: Token,
    /// The edit-target layer's own declaration.
    pub local: Token,
}

/// Lifts a value-type failure to its own stage variant and keeps every other
/// layer failure under [`Layer`](StageAuthoringError::Layer).
impl From<sdf::AuthoringError> for StageAuthoringError {
    fn from(error: sdf::AuthoringError) -> Self {
        match error {
            sdf::AuthoringError::ValueType(error) => Self::ValueType(error),
            other => Self::Layer(other),
        }
    }
}

impl From<sdf::DataError> for StageAuthoringError {
    fn from(error: sdf::DataError) -> Self {
        Self::Layer(error.into())
    }
}

impl From<sdf::SpecError> for StageAuthoringError {
    fn from(error: sdf::SpecError) -> Self {
        Self::Layer(error.into())
    }
}

impl From<sdf::EditError> for StageAuthoringError {
    fn from(error: sdf::EditError) -> Self {
        match error {
            sdf::EditError::Author(e) => Self::from(e),
            sdf::EditError::Rejected(e) => Self::Rejected(e),
        }
    }
}

/// An edit's own failure keeps its stage variant; the layer registry's
/// refusal of the edit is [`Registry`](StageAuthoringError::Registry).
impl From<sdf::LayerError> for StageAuthoringError {
    fn from(error: sdf::LayerError) -> Self {
        match error {
            sdf::LayerError::Edit(e) => Self::from(e),
            other => Self::Registry(other),
        }
    }
}

/// A borrow of one of a [`Stage`]'s layers, as [`Stage::root_layer`],
/// [`Stage::layer`] and [`Stage::session_layer`] hand it out. It derefs to the
/// [`sdf::Layer`].
///
/// It holds the stage's layers borrowed for its lifetime. An authoring call
/// made while one is live (`insert_layer`, `define_prim`, …) panics with a
/// `RefCell` double borrow. Taking one from inside a
/// [`LayerHandle::edit`](sdf::LayerHandle::edit) closure on one of the
/// stage's layers panics too, as the edit holds the layers' content.
pub struct LayerRef<'a> {
    /// The stage's layers.
    view: pcp::LayerView<'a>,
    /// The layer.
    id: pcp::LayerId,
}

impl Deref for LayerRef<'_> {
    type Target = sdf::Layer;

    fn deref(&self) -> &sdf::Layer {
        self.view.layer(self.id)
    }
}

impl fmt::Debug for LayerRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
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
    interpolation: Cell<InterpolationType>,
    /// Where authored opinions land. Defaults to the root layer.
    edit_target: RefCell<EditTarget>,
    /// The layer identifiers of the targets the open [`EditContext`]s will
    /// restore, outermost first, which a layer reclamation keeps.
    saved_edit_targets: RefCell<Vec<String>>,
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
    /// re-author the stage, but must not add or remove sinks from within a
    /// callback: that would borrow the set mutably while the fan-out holds it
    /// shared, and panic.
    sinks: RefCell<sdf::sink::Set<dyn StageSink>>,
    /// The internal observers of transaction outcomes (see
    /// [`TxnObserver`]).
    observers: RefCell<sdf::sink::Set<dyn TxnObserver>>,
    /// The [`Provenance`] each stage-authored transaction publishes, keyed by
    /// its transaction id, read by the stage's recorder as the transaction
    /// prepares. A direct edit publishes none, and the
    /// drain resolves it from local-layer membership.
    edit_provenance: TxnTable<Rc<Provenance>>,
    /// The identity the stage's own commits carry as their origin, which
    /// tells them from edits made through a [`sdf::LayerHandle`] or by another
    /// stage.
    editor: sdf::EditorId,
    /// The schemas this stage resolves fallback values against. Pinned at open,
    /// so the definitions a prim reads never shift under it.
    schema_registry: Arc<SchemaRegistry>,
    /// Which prim is of which schema type, so a fallback read does not recompose
    /// `typeName` and `apiSchemas` every time. The registry holds the composed
    /// definitions themselves; this only remembers which one each path resolved
    /// to, and is dropped wholesale when composition moves on.
    prim_types: RefCell<PrimTypeMemo>,
}

/// Which of a prim's composed answers a stage query reads. C++ keeps a
/// prim's source index (`Usd_PrimData::GetSourcePrimIndex`) apart from the
/// index its opinions are read through (`GetPrimIndex`), and the two differ
/// only for a prototype root, whose opinions read empty.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reads {
    /// Children, validity, flags and instancing, from the source index.
    Source,
    /// Values, metadata, properties and stacks, which a prototype root lacks.
    Opinions,
}

impl Reads {
    /// What a spec query at `path` reads: a property is one of its prim's
    /// opinions, and the prim's own spec is part of its source.
    fn spec_of(path: &sdf::Path) -> Self {
        match path.is_property() {
            true => Reads::Opinions,
            false => Reads::Source,
        }
    }
}

/// Per-prim schema type handles, valid as of one pair of composition epochs.
///
/// This is the stage-local half of prim type resolution: the registry caches
/// definitions by type identity, and this remembers which identity each prim
/// currently has.
///
/// Two epochs stamp it, because a prim's identity moves in two unrelated ways.
/// Authoring `typeName`, `apiSchemas`, or the stage's `fallbackPrimTypes` moves
/// it directly, which is the type-opinion epoch; and any structural change —
/// a reference, a variant switch, muting, a load rule, a prim removal — can
/// change which opinion wins without authoring a type field at all, which is
/// exactly what the population epoch already tracks. Neither covers the other,
/// and a value-only edit advances neither, which is the point.
///
/// A move of either drops the whole memo — cheap, since re-deriving one prim's
/// identity is two composed reads, and it keeps the map bounded by the prims
/// queried since the last one.
#[derive(Default, PartialEq, Eq, Clone, Copy)]
struct TypeEpochs {
    /// See [`pcp::IndexCache::type_opinion_epoch`].
    opinions: u64,
    /// See [`pcp::IndexCache::population_epoch`].
    population: u64,
}

#[derive(Default)]
struct PrimTypeMemo {
    epochs: TypeEpochs,
    types: sdf::PathMap<Arc<PrimTypeInfo>>,
}

impl PrimTypeMemo {
    /// The remembered type of a prim, if it was resolved under the epochs still
    /// in effect.
    fn lookup(&self, epochs: TypeEpochs, path: &sdf::Path) -> Option<Arc<PrimTypeInfo>> {
        if self.epochs != epochs {
            return None;
        }
        self.types.get(path).cloned()
    }

    /// Remembers a prim's type, discarding everything resolved under earlier
    /// epochs.
    fn remember(&mut self, epochs: TypeEpochs, path: sdf::Path, info: Arc<PrimTypeInfo>) {
        if self.epochs != epochs {
            self.types.clear();
            self.epochs = epochs;
        }
        self.types.insert(path, info);
    }
}

/// A composed USD stage.
///
/// A cheap reference-counted handle to the shared `StageInner` (mirroring
/// C++ `UsdStageRefPtr`). Cloning bumps the refcount; the composed handles
/// ([`Prim`](super::Prim) and friends) hold a clone, so they can be stored
/// and outlive the call that produced them. Provides composed access to
/// prims, properties, and metadata.
///
/// Composition runs user code: a resolver or a file format, reached while
/// layers are read and while their composition is rebuilt. A panic out of it
/// poisons the stage: the composition it left half-built cannot be finished.
/// A later composed read fails with [`pcp::QueryError::Poisoned`] (one that
/// folds a failure into a default returns the default), an accessor that
/// cannot fail panics, and the stage records, reconciles and delivers nothing
/// more: an edit of one of its layers still lands, unheard by it.
#[derive(Clone)]
pub struct Stage(Rc<StageInner>);

impl composition::CompositionHooks for Stage {
    fn subscribe_layer(&self, id: pcp::LayerId, layer: &sdf::LayerHandle) -> sdf::Subscription {
        layer
            .subscribe(Rc::new(StageRecorder {
                stage: self.downgrade(),
                layer_id: id,
            }))
            .expect("a layer joins the stage between edits of its layers")
    }

    fn wants_notice(&self) -> bool {
        !self.sinks.borrow().is_empty() || !self.observers.borrow().is_empty()
    }

    fn delivers(&self) -> bool {
        !self.sinks.borrow().is_empty()
    }

    fn notify(&self, notice: composition::CompositionNotice) {
        let change = notice.payload.committed_change(
            &notice.layer_identifier,
            &notice.provenance,
            notice.generation,
            notice.own,
        );
        self.each_sink(|sink| sink.after_commit(self, &change));
    }

    fn aborted(&self, generation: u64) {
        self.each_sink(|sink| sink.aborted(self, generation));
    }

    fn observe(&self, notice: &composition::CompositionNotice) {
        let observers = self.observers.borrow().snapshot();
        if observers.is_empty() {
            return;
        }
        let change = notice.payload.committed_change(
            &notice.layer_identifier,
            &notice.provenance,
            notice.generation,
            notice.own,
        );
        for observer in observers {
            observer.committed(self, &change, &notice.footprints);
        }
    }

    fn notify_stage(&self, notice: &composition::StageNotice) {
        self.each_sink(|sink| match notice {
            composition::StageNotice::EditTarget => sink.edit_target_changed(self),
            composition::StageNotice::LoadRules(resynced) => sink.load_rules_changed(self, resynced),
            composition::StageNotice::LoadsRetried(resynced) => sink.loads_retried(self, resynced),
            composition::StageNotice::Muting { layer, muted, resynced } => {
                sink.layer_muting_changed(self, layer, *muted, resynced);
            }
        });
    }

    fn observe_abort(&self, generation: u64) {
        for observer in self.observers.borrow().snapshot() {
            observer.aborted(generation);
        }
    }

    fn departed(&self, layers: &HashSet<pcp::LayerId>) {
        for observer in self.observers.borrow().snapshot() {
            observer.departed(layers);
        }
    }

    fn edit_target_identifiers(&self) -> Vec<String> {
        let mut identifiers = self.saved_edit_targets.borrow().clone();
        identifiers.push(self.edit_target.borrow().layer_identifier().to_owned());
        identifiers
    }
}

impl Stage {
    /// Drain the layer edits the stage's recorders queued and drive one
    /// composition recompose per snapshot, delivering each composed
    /// [`CommittedChange`](super::CommittedChange) to the stage sinks. The
    /// deferred counterpart to a layer commit: a recorder queues the edit as
    /// the commit lands, with the layers borrowed, and this runs once they are
    /// released — after each authoring call, and before any composed read.
    ///
    /// The public re-entry boundary for reconciliation; the drain itself, and
    /// the quiescence rule it runs under, belong to
    /// [`StageComposition`].
    pub(crate) fn process_pending(&self) {
        self.composition.process_pending(self);
    }

    /// [`process_pending`](Self::process_pending) for a fallible read (see
    /// [`StageComposition::settle`]).
    pub(crate) fn settle(&self) -> Result<(), pcp::QueryError> {
        self.composition.settle(self)
    }

    /// Calls `deliver` with each sink in turn, until one poisons the stage:
    /// a poisoned stage delivers nothing more.
    fn each_sink(&self, mut deliver: impl FnMut(&dyn StageSink)) {
        for sink in self.sinks.borrow().iter() {
            if self.composition.is_poisoned() {
                return;
            }
            deliver(sink);
        }
    }
}

/// Two handles are equal when they share one stage instance, as C++
/// `UsdStageRefPtr`s compare by pointer. Two stages that compose the same
/// content are still different stages.
impl PartialEq for Stage {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Stage {}

/// Hashes the stage instance, consistent with its [`PartialEq`].
impl Hash for Stage {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state);
    }
}

impl std::ops::Deref for Stage {
    type Target = StageInner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl fmt::Debug for Stage {
    /// The root layer stack identity names the stage; the composition state
    /// behind it is elided.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Stage")
            .field("layer_stack_id", &self.layer_stack_id)
            .finish_non_exhaustive()
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

/// The [`Provenance`] a stage-authored transaction publishes in
/// [`StageInner::edit_provenance`] for the stage's recorder, which shares it
/// with each layer's recording as the transaction prepares. Dropped as the
/// commit returns, it withdraws the entry.
struct PublishedProvenance<'a> {
    table: &'a TxnTable<Rc<Provenance>>,
    generation: u64,
}

impl Drop for PublishedProvenance<'_> {
    fn drop(&mut self) {
        self.table.withdraw(self.generation);
    }
}

/// Values keyed by the transaction that recorded them, for the stage's
/// recorder to read while the transaction prepares.
struct TxnTable<T>(RefCell<Vec<(u64, T)>>);

impl<T> Default for TxnTable<T> {
    fn default() -> Self {
        Self(RefCell::new(Vec::new()))
    }
}

impl<T> TxnTable<T> {
    /// Record `value` for the transaction `generation`.
    fn insert(&self, generation: u64, value: T) {
        self.0.borrow_mut().push((generation, value));
    }

    /// Run `f` on the value the transaction `generation` recorded, if any.
    fn with<R>(&self, generation: u64, f: impl FnOnce(Option<&T>) -> R) -> R {
        let entries = self.0.borrow();
        f(entries
            .iter()
            .find(|(entry, _)| *entry == generation)
            .map(|(_, value)| value))
    }

    /// Drop the value the transaction `generation` recorded.
    fn withdraw(&self, generation: u64) {
        self.0.borrow_mut().retain(|(entry, _)| *entry != generation);
    }
}

/// The [`sdf::Subscriber`] a [`Stage`] subscribes to every layer it holds. It
/// hands each staged edit of the layer to the stage's [`StageSink`]s before
/// it commits, and records the commit into [`StageComposition`]'s pending
/// queue as it lands, before any sink's `after_commit` runs. A read made from
/// a sink's callback therefore composes with every edit committed so far. It
/// reaches the stage through a [`WeakStage`] and forms no reference cycle
/// (the stage holds the layer, which holds this subscriber). The layer's node
/// in the stage's graph holds its subscription.
struct StageRecorder {
    stage: WeakStage,
    layer_id: pcp::LayerId,
}

impl sdf::Subscriber for StageRecorder {
    fn prepare(&self, commit: &sdf::PendingCommit<'_>) -> Option<Box<dyn sdf::Prepared>> {
        // Composition classification runs after the commit, by which point the
        // pre-edit values are gone, and it needs the prior `defaultPrim` to fan
        // a `defaultPrim` edit out the way C++ `PcpChanges` does. Only a commit
        // that staged something on the pseudo-root can have touched the field,
        // and the overlay answers that in one probe — the change list is a flat
        // vector, so scanning it would cost a walk per commit. A pseudo-root
        // edit that left `defaultPrim` alone reads a value nothing consumes,
        // which is cheaper than finding out. An absent field, an unreadable
        // one, and a non-token value all record `None`: no prior prim, the
        // conservative fanout.
        let change = commit.change;
        let stage = self.stage.upgrade()?;
        // A poisoned stage composes nothing more, so it neither records nor
        // tells its sinks of an edit to one of its layers.
        if stage.composition.is_poisoned() {
            return None;
        }
        let own = commit.txn.origin == Some(stage.editor);
        let prior_default_prim = change
            .overlay
            .keys()
            .any(sdf::Path::is_abs_root)
            .then(|| sdf::PseudoRootSpecRef::get(change.base)?.default_prim())
            .flatten();
        // A stage edit's provenance travels with its recording from here.
        let generation = commit.txn.id.get();
        let provenance = own
            .then(|| stage.edit_provenance.with(generation, |provenance| provenance.cloned()))
            .flatten();
        // Made before the stage's sinks see the edit: a sink that panics drops
        // it unlanded, and the stage reports the transaction aborted.
        let recording = Box::new(StageRecording {
            stage: self.stage.clone(),
            layer_id: self.layer_id,
            prior_default_prim,
            own,
            provenance,
            generation,
            landed: false,
        });
        let mapping = recording.provenance.as_deref().and_then(Provenance::mapping);
        stage.forward_before_commit(change, self.layer_id, own, mapping);
        Some(recording)
    }
}

/// One commit a [`StageRecorder`] prepared, queued on the stage when it lands.
/// Dropped without landing, it records the transaction as aborted, for the
/// stage's sinks to hear of at the next delivery.
struct StageRecording {
    stage: WeakStage,
    layer_id: pcp::LayerId,
    /// The layer's `defaultPrim` token before the commit.
    prior_default_prim: Option<Token>,
    /// Whether the stage made the edit itself.
    own: bool,
    /// The [`Provenance`] the stage published for its own edit.
    provenance: Option<Rc<Provenance>>,
    /// The transaction the commit belongs to.
    generation: u64,
    /// Whether the commit landed.
    landed: bool,
}

impl sdf::Prepared for StageRecording {
    fn commit(mut self: Box<Self>, record: &sdf::CommitRecord) -> Option<Rc<dyn sdf::LayerSink>> {
        self.landed = true;
        let stage = self.stage.upgrade()?;
        stage.composition.record_pending(PendingEdit {
            generation: self.generation,
            own: self.own,
            layer: self.layer_id,
            changes: record.changes.clone(),
            provenance: self.provenance.take(),
            prior_default_prim: self.prior_default_prim.take(),
            footprint: (!stage.observers.borrow().is_empty()).then(|| Rc::clone(&record.footprint)),
        });
        Some(Rc::new(StageDelivery(self.stage.clone())))
    }
}

/// The sink a [`StageRecording`] hands its transaction, so the registry's
/// dispatch delivers the stage's notices for an edit made through any stage
/// or handle on the registry, after the edited layer's own sinks.
struct StageDelivery(WeakStage);

impl sdf::LayerSink for StageDelivery {
    fn after_commit(&self, _change: &sdf::CommittedLayerChange<'_>) {
        if let Some(stage) = self.0.upgrade() {
            stage.process_pending();
        }
    }
}

impl Drop for StageRecording {
    fn drop(&mut self) {
        if !self.landed
            && let Some(stage) = self.stage.upgrade()
        {
            stage.composition.record_aborted(self.generation);
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
    /// Unique by structural equality: one failure reads once, however many
    /// owners hold it and however many passes found it. Two prims failing the
    /// same way at the same site are therefore one entry, so the length counts
    /// distinct failures rather than affected prims.
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
    pub fn composition_errors(&self) -> Vec<pcp::CompositionDiagnostic> {
        self.process_pending();
        self.composition.settled_errors()
    }

    /// Returns the current edit target — the layer that authoring methods
    /// write into.
    pub fn edit_target(&self) -> EditTarget {
        self.edit_target.borrow().clone()
    }

    /// Whether `target` is still the stage's edit target, borrowing it rather
    /// than cloning it to compare.
    pub(super) fn holds_edit_target(&self, target: &EditTarget) -> bool {
        *self.edit_target.borrow() == *target
    }

    /// Maps a stage time to the spec time the current edit target writes a
    /// time sample at, borrowing the target rather than cloning it. See
    /// [`EditTarget::map_to_spec_time`].
    pub(super) fn map_to_spec_time(&self, stage_time: f64) -> f64 {
        self.edit_target.borrow().map_to_spec_time(stage_time)
    }

    /// Maps a stage value authored on the object at `object_path` to the one
    /// the current edit target authors, borrowing the target rather than
    /// cloning it. See [`EditTarget::map_to_spec_value`].
    pub(super) fn map_to_spec_value(&self, object_path: &sdf::Path, value: impl Into<vt::Value>) -> vt::Value {
        self.edit_target.borrow().map_to_spec_value(object_path, value)
    }

    /// Maps a target-valued path into the layer namespace of the current edit
    /// target, under a borrow of the target. See
    /// `EditTarget::map_to_spec_target_path`.
    pub(super) fn map_to_spec_target_path(&self, scene_path: &sdf::Path) -> Result<sdf::Path, StageAuthoringError> {
        self.edit_target.borrow().map_to_spec_target_path(scene_path)
    }

    /// The current edit target's layer identifier and the spec path
    /// `scene_path` maps to on it, read under a short borrow of the target
    /// (which owns a heap `MapFunction`) so no layer borrow overlaps it.
    /// `OutsideEditTarget` when the mapping does not reach `scene_path`.
    fn target_spec_path(&self, scene_path: &sdf::Path) -> Result<(String, sdf::Path), StageAuthoringError> {
        let target = self.edit_target.borrow();
        let spec_path = target
            .map_to_spec_path(scene_path)
            .ok_or_else(|| StageAuthoringError::OutsideEditTarget {
                path: scene_path.clone(),
            })?;
        Ok((target.layer_identifier.clone(), spec_path))
    }

    /// Refuses an edit that instancing makes meaningless
    /// (C++ `_ValidateEditPrimAtPath`): an opinion authored at a prototype
    /// path or beneath an instance composes nowhere it can be seen. Only a
    /// target on a local layer that maps the prim to itself is checked; one
    /// that maps it elsewhere — a reference arc's layer, say — is trusted
    /// to have been set up to author the site it names, as C++ trusts it.
    /// `identifier` names the target's layer.
    fn validate_edit_prim(&self, scene_path: &sdf::Path, identifier: &str) -> Result<(), StageAuthoringError> {
        let prim = scene_path.prim_path();
        let maps_to_self = self.edit_target.borrow().map_to_spec_path(&prim).as_ref() == Some(&prim);
        if !maps_to_self || !self.is_local_layer(identifier) {
            return Ok(());
        }
        // The prototype namespace is reserved, so its spelling alone convicts
        // (C++ `Usd_InstanceCache::IsPathInPrototype`).
        if pcp::is_prototype_namespace(&prim) {
            return Err(StageAuthoringError::PrototypeEdit { path: prim });
        }
        // Anything beneath an instance is a proxy, whether or not a prim
        // composes there yet (C++ `_IsObjectDescendantOfInstance`).
        if self
            .with_cache(|g, cache| cache.enclosing_instance(g, &prim))?
            .is_some()
        {
            return Err(StageAuthoringError::InstanceProxyEdit { path: prim });
        }
        Ok(())
    }

    /// Refuses a property write on a prim the stage's population excludes: one
    /// outside the population mask or below an inactive prim, where C++ holds
    /// no `UsdPrim` to author through. A prim nothing composes yet passes at
    /// any depth, so an edit target can author inside a variant the stage has
    /// not selected.
    pub(super) fn require_included(&self, scene_path: &sdf::Path) -> Result<(), StageAuthoringError> {
        let prim = scene_path.prim_path();
        if self.with_cache(|g, c| c.population_excludes(g, &prim))? {
            return Err(StageAuthoringError::PrimNotValid { path: prim });
        }
        Ok(())
    }

    /// Refuses a prim operation at `scene_path` that the current edit target
    /// could not author: one it does not map, or one instancing makes
    /// meaningless ([`validate_edit_prim`](Self::validate_edit_prim)). What a
    /// plan checks before deciding the operation; the transaction checks
    /// again.
    pub(super) fn validate_target_prim(&self, scene_path: &sdf::Path) -> Result<(), StageAuthoringError> {
        let (identifier, _) = self.target_spec_path(scene_path)?;
        self.validate_edit_prim(scene_path, &identifier)
    }

    /// Whether the layer `identifier` names is in the stage's root layer stack
    /// (C++ `UsdStage::HasLocalLayer`).
    fn is_local_layer(&self, identifier: &str) -> bool {
        self.local_layer(identifier).is_some()
    }

    /// The canonical identifier of the layer `identifier` names and its
    /// composed offset in the stage's root layer stack, the strongest where
    /// the stack holds it twice. `None` when the stack does not hold it.
    fn local_layer(&self, identifier: &str) -> Option<(String, sdf::LayerOffset)> {
        let layers = self.layers();
        let id = layers.id_of(identifier)?;
        let &(_, offset) = layers.root_layer_stack().iter().find(|&&(member, _)| member == id)?;
        Some((layers.identifier(id).to_string(), offset))
    }

    /// Read the current edit target's layer at the spec path `scene_path`
    /// maps to, outside any transaction and under a short borrow of the layer
    /// graph: what a write consults before it opens its transaction.
    // TODO(perf): a planned write maps `scene_path` here and again in
    // `with_target_layer_at`; carrying the resolved site in the plan would
    // spare the second mapping.
    fn read_target_layer<T>(
        &self,
        scene_path: &sdf::Path,
        read: impl FnOnce(&sdf::Layer, &sdf::Path) -> T,
    ) -> Result<T, StageAuthoringError> {
        self.settle()?;
        let (id, spec_path) = self.target_site(scene_path)?;
        Ok(read(self.layer_view().layer(id), &spec_path))
    }

    /// The current edit target's layer and the spec path `scene_path` maps to
    /// on it: the site an authoring plan records the opinions it queues at.
    pub(super) fn target_site(&self, scene_path: &sdf::Path) -> Result<(pcp::LayerId, sdf::Path), StageAuthoringError> {
        self.settle()?;
        let (identifier, spec_path) = self.target_spec_path(scene_path)?;
        let id = self
            .layers()
            .id_of(&identifier)
            .ok_or(StageAuthoringError::LayerNotFound { layer: identifier })?;
        Ok((id, spec_path))
    }

    /// The kind of spec the current edit target's layer holds at the mapped
    /// `scene_path`, or `None` when it holds none: the first step of
    /// [`plan_property_spec`](super::authoring::plan_property_spec).
    pub(super) fn local_spec_type(&self, scene_path: &sdf::Path) -> Result<Option<sdf::SpecType>, StageAuthoringError> {
        self.read_target_layer(scene_path, |layer, path| layer.data().spec_type(path))
    }

    /// The opinion the current edit target's layer holds for `key` at the
    /// mapped `scene_path`, or `None` when it holds none. Fallible so an
    /// undecodable local field surfaces instead of reading back as absent.
    pub(super) fn local_field(
        &self,
        scene_path: &sdf::Path,
        key: &str,
    ) -> Result<Option<vt::Value>, StageAuthoringError> {
        let value = self.read_target_layer(scene_path, |layer, path| {
            layer
                .data()
                .try_field(path, key)
                .map(|value| value.map(|value| value.into_owned()))
        })?;
        Ok(value?)
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
        let identifier = {
            let layers = self.layers();
            layers
                .root_id()
                .map(|id| layers.identifier(id).to_string())
                .unwrap_or_default()
        };
        self.bound_target(identifier, pcp::MapFunction::identity())
    }

    /// Edit target for the stage's strongest session layer, or `None` when the
    /// stage has no session layer.
    pub fn edit_target_session(&self) -> Option<EditTarget> {
        let layers = self.layers();
        let &id = layers.session_layers().first()?;
        Some(self.bound_target(layers.identifier(id).to_string(), pcp::MapFunction::identity()))
    }

    /// Edit target for `identifier`, a layer of the stage's root layer stack,
    /// carrying the layer's composed offset in that stack (C++
    /// `GetEditTargetForLocalLayer`). A time sample authored through it is
    /// keyed at the layer time that composes to the stage time it was authored
    /// at ([`EditTarget::map_to_spec_time`]). `None` when the layer is not in
    /// the root layer stack. A layer the stack holds twice takes its strongest
    /// offset.
    pub fn edit_target_for_local_layer(&self, identifier: &str) -> Option<EditTarget> {
        let (identifier, offset) = self.local_layer(identifier)?;
        Some(self.bound_target(identifier, pcp::MapFunction::identity().with_time_offset(offset)))
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
        self.settle()?;
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
        if changed && !thread::panicking() && !self.sinks.borrow().is_empty() {
            self.composition.announce(composition::StageNotice::EditTarget, self);
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
        // The saved target is kept from a reclaim before the switch notifies a
        // sink, which may unload. The guard is made first, so a failed switch
        // drops it: it unpins and restores the target the switch left alone.
        self.saved_edit_targets
            .borrow_mut()
            .push(saved.layer_identifier().to_owned());
        let context = EditContext { stage: self, saved };
        self.set_edit_target(target)?;
        Ok(context)
    }

    /// Author a `def` prim spec at `path` on the edit target's layer and
    /// return a [`Prim`](super::Prim) handle (C++ `UsdStage::DefinePrim` with no
    /// type). The returned handle lets callers chain field setters (`set_type_name`,
    /// `set_active`, `set_kind`, …) and child-property authoring
    /// (`create_attribute`, `create_relationship`) on a prim the stage
    /// composes. One it will not compose — outside its population mask, below
    /// an inactive prim, or inside a variant it has not selected — takes no
    /// setter, and gets its type through
    /// [`define_typed_prim`](Self::define_typed_prim).
    pub fn define_prim(&self, path: impl sdf::IntoPath) -> Result<super::Prim, StageAuthoringError> {
        self.define_typed_prim(path, "")
    }

    /// Author a `def` prim spec typed `type_name` at `path` on the edit
    /// target's layer and return a [`Prim`](super::Prim) handle (C++
    /// `UsdStage::DefinePrim(path, typeName)`). A prim the stage holds as
    /// defined is left as it is, unless `type_name` names a type other than
    /// its own; any other prim gets a `def` spec on the edit target, typed
    /// `type_name` where that is not empty, which is
    /// [`define_prim`](Self::define_prim). An ancestor the stage does not
    /// hold as defined gets a `def` of its own in the same write, its type
    /// left alone: a prim is [defined](super::Prim::is_defined) only under
    /// defined ancestors. A prim the stage does not hold at all, outside its
    /// population or below an inactive prim, counts as undefined here, as
    /// the invalid `UsdPrim` does in C++.
    pub fn define_typed_prim(
        &self,
        path: impl sdf::IntoPath,
        type_name: impl Into<String>,
    ) -> Result<super::Prim, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
        let type_name = Token::from(type_name.into());
        self.author_prim(path, PrimOp::Define { type_name })
    }

    /// Return the prim at `path`, authoring an `over` spec for it on the edit
    /// target's layer only where the stage holds no prim there (C++
    /// `UsdStage::OverridePrim`). A prim some layer already composes is
    /// returned as it is, with no spec added: a later write through the
    /// handle creates the spec it needs on the edit target. An `over` is
    /// authored with `over` ancestors where they have no spec there. Chain
    /// fluent setters on the returned handle to author additional fields.
    pub fn override_prim(&self, path: impl sdf::IntoPath) -> Result<super::Prim, StageAuthoringError> {
        let path = sdf::try_into_path(path)?;
        self.author_prim(path, PrimOp::Override)
    }

    /// Plans the prim operation `op` at `path` on its own and commits it, the
    /// decision a [`StageEdit`](super::StageEdit) makes for the same request.
    ///
    /// A define whose own writes leave an ancestor's composition unknown to
    /// the plan (a spec that revives an arc only a rebuild composes) defines
    /// the parent on its own first, as C++ commits each prim of the chain,
    /// and is decided again against what that commit composes.
    fn author_prim(&self, path: sdf::Path, op: PrimOp) -> Result<super::Prim, StageAuthoringError> {
        let mut plan = PlanState::untracked();
        match plan.admit(
            self,
            Operation::Prim {
                path: path.clone(),
                op: op.clone(),
            },
        ) {
            Err(StageAuthoringError::PlannedEffectUnknown { .. })
                if matches!(op, PrimOp::Define { .. }) && !path.parent().is_none_or(|parent| parent.is_abs_root()) =>
            {
                self.define_prim(path.parent().expect("checked above"))?;
                plan = PlanState::untracked();
                plan.admit(self, Operation::Prim { path: path.clone(), op })?;
            }
            admitted => admitted?,
        }
        plan.commit(self)?;
        Ok(super::Prim::new(self, path))
    }
    /// Author an attribute spec at a property path on the edit target's layer,
    /// following C++ `UsdPrim::CreateAttribute`'s contract: an attribute
    /// already at the edit target is returned untouched, whatever type it
    /// declares; otherwise the declaration composition finds — the schema's,
    /// else the strongest authored spec's — is stamped. Only an attribute
    /// nothing declares is created with `type_name`, variability `Varying`
    /// and `custom = true`, the supplied type being checked (an empty spelling
    /// is rejected) only in that case. A
    /// relationship at the path is
    /// [`SpecKindMismatch`](StageAuthoringError::SpecKindMismatch), and a prim
    /// the stage does not hold — outside the population mask or below an
    /// inactive prim — is [`PrimNotValid`](StageAuthoringError::PrimNotValid).
    pub fn create_attribute(
        &self,
        path: impl sdf::IntoPath,
        type_name: impl Into<sdf::ValueTypeName>,
    ) -> Result<super::Attribute, StageAuthoringError> {
        self.attribute_builder(path, type_name).build()
    }

    /// The same authoring, with what the attribute is declared as — and the
    /// value it starts with — left to the caller. Everything the builder
    /// carries is authored as one edit of the target layer.
    pub fn attribute_builder(
        &self,
        path: impl sdf::IntoPath,
        type_name: impl Into<sdf::ValueTypeName>,
    ) -> super::AttributeBuilder<'static> {
        super::AttributeBuilder::new(self.property_site(path), type_name.into())
    }

    /// Author a relationship spec at a property path on the edit target's
    /// layer, following C++ `UsdPrim::CreateRelationship`'s contract: a
    /// relationship already at the edit target is returned untouched;
    /// otherwise the declaration composition finds — the schema's, else the
    /// strongest authored spec's — is stamped. Only a relationship nothing
    /// declares is created `custom` and uniform, as C++ generic property
    /// authoring does; a
    /// [`relationship_builder`](Self::relationship_builder) says otherwise. An
    /// attribute at the path is
    /// [`SpecKindMismatch`](StageAuthoringError::SpecKindMismatch), and a prim
    /// the stage does not hold is
    /// [`PrimNotValid`](StageAuthoringError::PrimNotValid).
    pub fn create_relationship(&self, path: impl sdf::IntoPath) -> Result<super::Relationship, StageAuthoringError> {
        self.relationship_builder(path).build()
    }

    /// The same authoring, with the declaration left to the caller.
    pub fn relationship_builder(&self, path: impl sdf::IntoPath) -> super::RelationshipBuilder<'static> {
        super::RelationshipBuilder::new(self.property_site(path))
    }

    /// The stage and property path a builder authors at, or what naming them
    /// hit: the stage-tier counterpart of `Prim::property_target`.
    fn property_site(&self, path: impl sdf::IntoPath) -> Result<(Stage, sdf::Path), StageAuthoringError> {
        Ok((self.clone(), sdf::try_into_path(path)?))
    }

    /// Author several prims and properties as one transaction.
    ///
    /// `f` receives the transaction: [`StageEdit`](super::StageEdit) offers the
    /// same authoring entry points this stage does, and the prim operations and
    /// property builders it hands out queue their writes rather than committing
    /// them. The queue is written together when `f` returns — all of it, or on
    /// any error none of it — and `f`'s own value comes back once it commits,
    /// so the handle a caller wants returns through it.
    ///
    /// Each operation is planned against the stage with the prims the batch has
    /// queued so far composed in, and for every batch it accepts, the commit
    /// authors what the same calls made one after another would author. The
    /// sequences it cannot plan, and refuses, are listed on
    /// [`StageEdit`](super::StageEdit). Ordinary reads inside `f` see the stage
    /// as it stands. A builder taken from the stage or a [`Prim`](super::Prim)
    /// still commits on its own unless it is handed to the transaction with
    /// [`AttributeBuilder::in_edit`](super::AttributeBuilder::in_edit) or
    /// [`RelationshipBuilder::in_edit`](super::RelationshipBuilder::in_edit),
    /// and such a commit, or a muting or load-rule change, that moves what the
    /// batch planned against makes the batch
    /// [`PlanStale`](StageAuthoringError::PlanStale).
    ///
    /// The batch is tied to the edit target it opened on, and moving that
    /// target inside `f` is [`StageAuthoringError::EditTargetMoved`]: a queued
    /// property has already resolved its spec path, its value and its sample
    /// time through the target it was planned against.
    ///
    /// The error is the closure's own: any type a [`StageAuthoringError`]
    /// converts into, so a caller layered on the stage reports its failures
    /// through the same transaction. A closure that ends in a bare `Ok` names
    /// the type, as `Ok::<_, StageAuthoringError>(..)`.
    ///
    /// ```
    /// # use openusd::usd;
    /// # fn main() -> openusd::Result<()> {
    /// let stage = usd::Stage::builder().in_memory("anon.usda")?;
    /// stage.define_prim("/Cylinder")?;
    ///
    /// let radius = stage.edit(|edit| {
    ///     let cylinder = edit.prim("/Cylinder")?;
    ///     cylinder.attribute_builder("height", "double").set(2.0).build()?;
    ///     cylinder.attribute_builder("radius", "double").set(1.0).build()
    /// })?;
    ///
    /// assert_eq!(radius.get::<f64>()?, Some(1.0));
    /// # Ok(())
    /// # }
    /// ```
    pub fn edit<T, E>(&self, f: impl FnOnce(&super::StageEdit) -> Result<T, E>) -> Result<T, E>
    where
        E: From<StageAuthoringError>,
    {
        let edit = super::StageEdit::new(self);
        let value = f(&edit)?;
        edit.commit()?;
        Ok(value)
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
        if path.is_property() {
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
        if !path.is_property() {
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
    ///
    /// Runs without the instancing validation of `with_target_layer_at`, as
    /// C++ `_RemovePrim` / `_RemoveProperty` do: stripping a layer's stale
    /// opinion beneath an instance or at a prototype path is what removal is
    /// for.
    fn remove_spec(&self, path: &sdf::Path) -> Result<bool, StageAuthoringError> {
        let (identifier, spec_path) = self.target_spec_path(path)?;
        self.edit_target_layer(identifier, spec_path, |layer, layer_path| {
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
    pub fn set_custom_layer_data(&self, value: impl Into<vt::Value>) -> Result<(), StageAuthoringError> {
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
        // Deliver any edit already committed (e.g. a direct `layer_handle` commit
        // awaiting drain) to the current set before this sink joins, so a sink
        // only ever observes edits committed after it was installed.
        self.process_pending();
        self.sinks.borrow_mut().add(Rc::new(sink))
    }

    /// Remove the sink with the given [`StageSinkId`]; the inverse of
    /// [`add_sink`](Self::add_sink). A no-op if it was already removed.
    pub fn remove_sink(&self, id: StageSinkId) {
        // Deliver any already-committed edit to the full set, including this sink,
        // before it leaves — so it sees every edit committed while it was installed.
        self.process_pending();
        self.sinks.borrow_mut().remove(id);
    }

    /// The layers with their content as they stand, read without draining:
    /// for a [`TxnObserver`], which runs as a
    /// transaction reconciles.
    pub(super) fn current_view(&self) -> pcp::LayerView<'_> {
        self.composition.current_view()
    }

    /// Install `observer` to hear each transaction outcome as it is
    /// reconciled.
    pub(super) fn add_observer(&self, observer: Rc<dyn TxnObserver>) -> sdf::sink::Id<dyn TxnObserver> {
        // As `add_sink` does: the observer hears only of later edits.
        self.process_pending();
        self.observers.borrow_mut().add(observer)
    }

    /// Remove the observer with `id`.
    pub(super) fn remove_observer(&self, id: sdf::sink::Id<dyn TxnObserver>) {
        // As `remove_sink` does: the observer hears of every edit made while
        // it was installed.
        self.process_pending();
        self.observers.borrow_mut().remove(id);
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

    /// Authors `startTimeCode` on the current edit target's layer, which must
    /// be the root or session layer; any other target fails with
    /// [`StageAuthoringError::StageMetadataTarget`].
    /// Mirrors C++ `UsdStage::SetStartTimeCode`.
    pub fn set_start_time_code(&self, time: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_start_time_code(time))
    }

    /// Authors `endTimeCode` on the current edit target's layer, which must be
    /// the root or session layer; any other target fails with
    /// [`StageAuthoringError::StageMetadataTarget`].
    /// Mirrors C++ `UsdStage::SetEndTimeCode`.
    pub fn set_end_time_code(&self, time: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_end_time_code(time))
    }

    /// Authors `timeCodesPerSecond` on the current edit target's layer, which
    /// must be the root or session layer; any other target fails with
    /// [`StageAuthoringError::StageMetadataTarget`].
    /// Mirrors C++ `UsdStage::SetTimeCodesPerSecond`.
    pub fn set_time_codes_per_second(&self, rate: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_time_codes_per_second(rate))
    }

    /// Authors the pseudo-root metadata `field` on the current edit target's
    /// layer, which must be the root or session layer; any other target fails
    /// with [`StageAuthoringError::StageMetadataTarget`]. Mirrors C++
    /// `UsdStage::SetMetadata`, and [`stage_metadata`](Self::stage_metadata)
    /// reads it back.
    ///
    /// A value of another type than the field is declared with is converted
    /// to it where the conversion loses nothing, and is
    /// [`StageAuthoringError::ValueType`] otherwise. `defaultPrim`,
    /// `subLayers`, `subLayerOffsets` and `layerRelocates` are
    /// [`StageAuthoringError::ReservedField`]: each is authored through the
    /// operation that validates it.
    pub fn set_stage_metadata(
        &self,
        field: &'static str,
        value: impl Into<vt::Value>,
    ) -> Result<(), StageAuthoringError> {
        super::authoring::check_reserved(sdf::SpecType::PseudoRoot, field)?;
        let declared = match sdf::registered_field_type(field) {
            Some(sdf::FieldType::Value(type_name)) => Some(type_name),
            Some(_) => sdf::layer_field_type(field),
            None => self
                .schema_registry()
                .metadata_field(&Token::new(field))
                .map(|declared| declared.type_name().clone()),
        };
        let value = match declared.filter(|type_name| type_name.kind().is_some()) {
            Some(type_name) => type_name.coerce(value.into())?,
            None => value.into(),
        };
        self.with_stage_metadata_layer(|layer| {
            layer.pseudo_root_mut()?.set(field, value);
            Ok(())
        })
    }

    /// Removes the opinion the current edit target's layer holds for the
    /// pseudo-root metadata `field`, on the terms of
    /// [`set_stage_metadata`](Self::set_stage_metadata). Mirrors C++
    /// `UsdStage::ClearMetadata`.
    pub fn clear_stage_metadata(&self, field: &'static str) -> Result<(), StageAuthoringError> {
        super::authoring::check_reserved(sdf::SpecType::PseudoRoot, field)?;
        self.with_stage_metadata_layer(|layer| {
            layer.pseudo_root_mut()?.erase(field);
            Ok(())
        })
    }

    /// Authors `framesPerSecond` on the current edit target's layer, which
    /// must be the root or session layer; any other target fails with
    /// [`StageAuthoringError::StageMetadataTarget`].
    /// Mirrors C++ `UsdStage::SetFramesPerSecond`.
    pub fn set_frames_per_second(&self, rate: f64) -> Result<(), StageAuthoringError> {
        self.with_stage_metadata_layer(|layer| layer.set_frames_per_second(rate))
    }

    /// Authors `expressionVariables` on the current edit target's layer, which
    /// must be the root or session layer; any other target fails with
    /// [`StageAuthoringError::StageMetadataTarget`].
    /// The dictionary supplies the values `${VAR}` expressions in sublayer asset
    /// paths and reference/payload targets resolve against; replacing it
    /// recomposes every prim whose composition reads the edited layer stack.
    pub fn set_expression_variables(&self, vars: HashMap<String, vt::Value>) -> Result<(), StageAuthoringError> {
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
        F: FnOnce(&mut sdf::LayerEdit<'_>, sdf::Path) -> Result<(), StageAuthoringError>,
    {
        let (identifier, spec_path) = self.target_spec_path(scene_path)?;
        self.validate_edit_prim(scene_path, &identifier)?;
        self.edit_target_layer(identifier, spec_path, f)
    }

    /// [`with_target_layer_at`](Self::with_target_layer_at) for several paths
    /// at once: map each through the current edit target, borrow the target's
    /// layer, and hand it and the mapped spec paths — in the order the scene
    /// paths were given — to `f`.
    ///
    /// The edit target names one layer whatever path it maps, so the whole
    /// batch is one layer transaction, one change list, and one invalidation
    /// pass. An empty batch borrows nothing and reports no change.
    pub(super) fn with_target_layer_at_each<F>(
        &self,
        scene_paths: &[sdf::Path],
        f: F,
    ) -> Result<bool, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::LayerEdit<'_>, Vec<sdf::Path>) -> Result<(), StageAuthoringError>,
    {
        if scene_paths.is_empty() {
            return Ok(false);
        }
        let identifier = self.edit_target.borrow().layer_identifier.clone();
        let mut spec_paths = Vec::with_capacity(scene_paths.len());
        // Properties of one prim are validated once between them: the check is
        // a composed query up the prim's ancestors, and a batch is usually
        // several properties of the same prim.
        let mut validated: Option<sdf::Path> = None;
        for scene_path in scene_paths {
            let prim = scene_path.prim_path();
            if validated.as_ref() != Some(&prim) {
                self.validate_edit_prim(scene_path, &identifier)?;
                validated = Some(prim);
            }
            spec_paths.push(self.target_spec_path(scene_path)?.1);
        }
        self.edit_target_layer(identifier, spec_paths, f)
    }

    /// Borrow the layer `identifier` names, hand it and `authored` — whatever
    /// the closure needs to say where it writes — to `f`,
    /// then drive cache invalidation from the closure's change list: the
    /// transaction behind [`with_target_layer_at`](Self::with_target_layer_at),
    /// once the target mapping and the instancing validation are done.
    fn edit_target_layer<P, F>(&self, identifier: String, authored: P, f: F) -> Result<bool, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::LayerEdit<'_>, P) -> Result<(), StageAuthoringError>,
    {
        // The target is read under a short borrow released before the layer
        // borrow below. The mapping is cloned out (rather than borrowed across
        // the authoring call) because the sinks it ultimately feeds can
        // re-author and re-target the stage; clone it only when a sink is
        // installed to consume it, keeping the common no-sink authoring path
        // allocation-free.
        let notify = composition::CompositionHooks::wants_notice(self);
        let mapping = notify.then(|| self.edit_target.borrow().mapping.clone());
        let edited = {
            let layers = self.composition.authoring_graph();
            let layer_id = layers
                .id_of(&identifier)
                .ok_or(StageAuthoringError::LayerNotFound { layer: identifier })?;
            self.commit_layer(&layers, layer_id, mapping.as_ref(), |layer| f(layer, authored))
        };
        let edited = edited.map(|committed| self.composition.deliver(committed, self));
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
        E: From<sdf::sink::Error> + From<sdf::LayerError>,
    {
        let result = {
            // The borrow states the mode's drain contract: a commit may arrive
            // with edits queued and appends to them, while a dry run validates
            // against composed state and so takes the settled borrow, whose
            // backstop catches a caller that stopped settling first.
            let graph = if commit {
                self.composition.authoring_graph()
            } else {
                self.composition.settled_graph()
            };
            // The realized ids, aligned with the edits below: `handles` drops any
            // id with no live layer, so the closure keys on these rather than the
            // requested `layer_ids` to stay paired with each `LayerEdit`.
            let (ids, handles): (Vec<pcp::LayerId>, Vec<&sdf::LayerHandle>) =
                graph.handles(layer_ids).into_iter().unzip();
            let store = graph.store();
            if commit {
                self.commit_attributed(store, &handles, mapping, |edits| f(&ids, edits))
                    .map(Some)
            } else {
                store.dry_run(&handles, |edits| f(&ids, edits)).map(|()| None)
            }
        };
        let result =
            result.map(|committed| committed.is_some_and(|committed| self.composition.deliver(committed, self)));
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
        // Resolving the stack may load one of its layers.
        self.composition.ensure_writable()?;
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

    /// Run `f` as one atomic [`Layer::edit`](sdf::Layer::edit) on the layer
    /// `layer` names: commit it and hand back the landed commit, for the caller
    /// to [`deliver`](composition::StageComposition::deliver) once it releases
    /// the graph, or roll the layer back on error (`f`'s authoring error, or a
    /// sink veto).
    ///
    /// Committing queues the edit, through the stage's recorder (subscribed
    /// when its layer interned), on [`StageComposition`]'s pending queue for
    /// [`process_pending`](Self::process_pending) to recompose. A [`before_commit`](sdf::LayerSink::before_commit) rejection
    /// surfaces as [`StageAuthoringError::Rejected`]. `mapping` is the edit
    /// target's namespace mapping (see
    /// [`commit_attributed`](Self::commit_attributed)).
    fn commit_layer<F>(
        &self,
        layers: &pcp::LayerGraph,
        layer: pcp::LayerId,
        mapping: Option<&pcp::MapFunction>,
        f: F,
    ) -> Result<sdf::Committed, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), StageAuthoringError>,
    {
        // The stage's own closure error rides through the layer transaction, so
        // a stage-only failure inside it rolls the layer back like a layer one.
        self.commit_attributed(layers.store(), &[layers.handle(layer)], mapping, |edits| {
            f(&mut edits[0])
        })
    }

    /// Commit `f` over `handles` as one transaction, publishing its
    /// [`Provenance`] in [`edit_provenance`](StageInner::edit_provenance) for
    /// the stage's recorder to tag the queued edit with. Only a remapping arc or
    /// variant target (a non-identity `mapping`) publishes one,
    /// [`Provenance::EditTarget`]; an identity-mapped or unmapped target
    /// authors at the layer's own paths and publishes none, for the drain to
    /// resolve from local-layer membership ([`Provenance::LocalStack`] for a
    /// local layer, [`Provenance::DirectLayerEdit`] for a non-local one).
    ///
    /// The stage's recorder queues the edit as it lands. The caller delivers
    /// the landed commit's notifications
    /// ([`StageComposition::deliver`](composition::StageComposition::deliver))
    /// once it releases the graph. The layers' sinks can then read the stage.
    fn commit_attributed<E: From<sdf::sink::Error> + From<sdf::LayerError>>(
        &self,
        store: &sdf::LayerStore,
        handles: &[&sdf::LayerHandle],
        mapping: Option<&pcp::MapFunction>,
        f: impl FnOnce(&mut [sdf::LayerEdit<'_>]) -> Result<(), E>,
    ) -> Result<sdf::Committed, E> {
        let txn = sdf::TxnContext::new(Some(self.editor));
        let generation = txn.id.get();
        let _published = PublishedProvenance {
            table: &self.edit_provenance,
            generation,
        };
        if let Some(mapping) = mapping.filter(|m| !m.is_identity()) {
            self.edit_provenance
                .insert(generation, Rc::new(Provenance::EditTarget(mapping.clone())));
        }
        store.commit(handles, txn, f)
    }

    /// The layer ids of the root (local) layer stack, strongest first — the
    /// layers a namespace edit authors into to move or delete a composed object.
    pub(super) fn root_stack_layer_ids(&self) -> Vec<pcp::LayerId> {
        self.layers().root_layer_stack().iter().map(|&(id, _)| id).collect()
    }

    /// Fan out the staged pre-commit edit to the layer `layer` to the stage's
    /// transaction observers' [`capture`](TxnObserver::capture) and then the
    /// installed [`StageSink`]s' [`before_commit`](StageSink::before_commit),
    /// bridging one [`sdf::PendingLayerChange`] to the stage-tier
    /// [`PendingChange`]. Called by the layer's [`StageRecorder`] from inside
    /// the commit seam, while the layers are borrowed for the edit — so it reads
    /// only the observers and [`sinks`](StageInner::sinks), never the graph or
    /// cache. A no-op when neither is installed. `mapping` is the edit
    /// target's, for a stage edit through a remapping target.
    fn forward_before_commit(
        &self,
        change: &sdf::PendingLayerChange<'_>,
        layer: pcp::LayerId,
        own: bool,
        mapping: Option<&pcp::MapFunction>,
    ) {
        let observers = self.observers.borrow().snapshot();
        let sinks = self.sinks.borrow();
        if sinks.is_empty() && observers.is_empty() {
            return;
        }
        let pending = PendingChange {
            layer_identifier: change.layer_identifier,
            base: change.base,
            change_list: change.change_list,
            mapping,
            generation: change.generation,
            own,
        };
        // Observers capture first, so no sink's order or panic reaches them.
        for observer in observers {
            observer.capture(self, &pending, layer);
        }
        drop(sinks);
        self.each_sink(|sink| sink.before_commit(self, &pending));
    }

    /// Returns the number of layers the stage holds (including session layers).
    ///
    /// Layers behind references and payloads load on demand as composition
    /// reaches their arcs, and value-clip layers as a value read reaches them,
    /// so this is the count loaded by the queries performed so far, less the
    /// layers an [`unload`](Self::unload) or other load-rules change freed,
    /// mirroring C++ `UsdStage::GetUsedLayers` (which counts clip layers by
    /// default). The root layer stack is always fully loaded.
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

    /// How much composition-graph data the stage holds and how much composing
    /// it copied.
    pub fn graph_stats(&self) -> pcp::GraphStats {
        self.cache().graph_stats()
    }

    /// Returns the identifiers of the layers loaded so far, in collection order
    /// (session and root layer stack first, then arc-target layers in the order
    /// composition opened them).
    ///
    /// Reference, payload and value-clip layers load on demand, so this lists
    /// the layers reached by the queries performed so far, less those a
    /// load-rules change freed (C++ `UsdStage::GetUsedLayers`). Traverse the
    /// stage to force every reachable layer to load.
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
    /// The returned [`LayerRef`] borrows the stage's layers (see its borrow
    /// rules). In particular `stage.insert_layer(stage.root_layer().identifier(),
    /// …)` panics because the temporary lives to the end of the statement.
    /// Bind the identifier first so the borrow is released:
    ///
    /// ```no_run
    /// # use openusd::{sdf, usd};
    /// # fn f(stage: &usd::Stage, layer: sdf::Layer) {
    /// let id = stage.root_layer().identifier().to_owned();
    /// stage.insert_layer(&id, 0, layer, sdf::LayerOffset::IDENTITY).unwrap();
    /// # }
    /// ```
    pub fn root_layer(&self) -> LayerRef<'_> {
        let view = self.layer_view();
        let id = view.root_id().expect("stage has a root layer");
        LayerRef { view, id }
    }

    /// Borrow the stage's layer named `identifier`, or `None` if no such layer is
    /// in the stage. `identifier` is matched by canonical identifier. The
    /// [`LayerRef`] borrows the stage's layers (see its borrow rules).
    pub fn layer(&self, identifier: &str) -> Option<LayerRef<'_>> {
        let view = self.layer_view();
        let id = view.id_of(identifier)?;
        Some(LayerRef { view, id })
    }

    /// Edit the stage's layer named `identifier` directly, as one atomic
    /// transaction (see [`sdf::Layer::edit`]), and integrate it into
    /// composition before returning. Returns whether the edit produced a
    /// composition change. An advanced escape hatch: prefer the stage's
    /// authoring methods, which route through the current
    /// [`EditTarget`](super::EditTarget).
    ///
    /// The edit authors at the layer's own paths. Edited through a non-local
    /// (referenced or payload) layer, its [`CommittedChange`](super::CommittedChange)
    /// paths are in that layer's own namespace, flagged
    /// [`Provenance::DirectLayerEdit`](super::Provenance::DirectLayerEdit).
    /// Returns [`StageAuthoringError::LayerNotFound`] if no such layer is in the
    /// stage.
    pub fn edit_layer(
        &self,
        identifier: &str,
        f: impl FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), sdf::AuthoringError>,
    ) -> Result<bool, StageAuthoringError> {
        self.batch_edit(&[identifier], |edits| {
            f(&mut edits[0]).map_err(StageAuthoringError::from)
        })
    }

    /// A handle to the stage's layer named `identifier`, or `None` if no such
    /// layer is in the stage. An edit through the handle is not attributed to
    /// the stage: the stage integrates it like any direct layer edit, flagged
    /// [`Provenance::DirectLayerEdit`](super::Provenance::DirectLayerEdit)
    /// on a non-local layer.
    ///
    /// From inside a [`read`](sdf::LayerHandle::read) or an
    /// [`edit`](sdf::LayerHandle::edit) of a layer on the stage's registry, while
    /// an earlier edit of them is still queued, a fallible stage read fails
    /// with [`sdf::LayerError::Busy`], and one that cannot fail (such as
    /// [`sub_layers`](Self::sub_layers)) panics. A read can also demand a
    /// load: one that first reaches a reference or payload target, a `${VAR}`
    /// sublayer, or a value clip the stage has not loaded fails there with
    /// `Busy` too, since loading adds the layer to the registry, while a read
    /// of loaded layers succeeds.
    pub fn layer_handle(&self, identifier: &str) -> Option<sdf::LayerHandle> {
        let layers = self.layers();
        Some(layers.handle(layers.id_of(identifier)?).clone())
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
    /// through the current [`EditTarget`]) or [`edit_layer`](Self::edit_layer).
    /// Returns [`StageAuthoringError::LayerNotFound`] if a name is not in the stage
    /// and [`StageAuthoringError::DuplicateLayer`] if a name is repeated. On any
    /// error the stage is left untouched.
    pub fn batch_edit(
        &self,
        layers: &[&str],
        f: impl FnOnce(&mut [sdf::LayerEdit<'_>]) -> Result<(), StageAuthoringError>,
    ) -> Result<bool, StageAuthoringError> {
        self.settle()?;
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

    /// Reloads every layer the stage uses from its asset (C++
    /// `UsdStage::Reload`), clip layers included, leaving out the session
    /// layers and the sublayers beneath them, and muted layers. Each layer
    /// reloads as [`sdf::LayerHandle::reload`] does, unforced: one with no
    /// unsaved edits whose file is unchanged is not read. A sublayer that
    /// failed to load is then tried again, and a reference or payload that
    /// failed to load on its next read.
    ///
    /// The layers reload in one transaction ([`sdf::LayerHandle::reload_all`])
    /// attributed to no stage, as a reload through a handle is: the stage's
    /// sinks hear it as one committed change, and a retried load as
    /// [`StageSink::loads_retried`](super::StageSink::loads_retried). Undo
    /// steps touching a reloaded layer are dropped. Every layer is tried; the
    /// first failure is returned.
    ///
    /// Fails with [`sdf::LayerError::Busy`] from inside a read or an edit of
    /// a layer on the stage's registry.
    pub fn reload(&self) -> Result<()> {
        // A retry loads, and the drain a reload runs recomposes, so neither
        // can run inside a read of the registry's layers.
        self.settle()?;
        self.composition.ensure_writable()?;
        let handles: Vec<sdf::LayerHandle> = {
            let layers = self.layers();
            let used = layers.used_layers();
            let session = layers.session_stack();
            layers
                .all_ids()
                .iter()
                .filter(|&&id| used.contains(&id) && session.iter().all(|&(member, _)| member != id))
                .map(|&id| layers.handle(id).clone())
                .collect()
        };
        // A drain of a reloaded layer's edit retries the failed loads (C++
        // `PcpCache::Reload`), in every stage on the registry; this stage
        // retries them itself when no edit reached it.
        let retries = self.composition.retries();
        let reloaded = sdf::LayerHandle::reload_all(&handles, false);
        self.process_pending();
        if self.composition.retries() == retries {
            self.composition.retry_failed_loads(self);
        }
        self.process_pending();
        reloaded.map(drop)
    }

    /// Mutes the layer with the given identifier so it contributes no opinions to
    /// composition — as if absent from every layer stack it participates in
    /// (C++ `UsdStage::MuteLayer` → `PcpCache::RequestLayerMuting`). Muting
    /// prunes the layer's whole sublayer subtree, not just the one layer.
    ///
    /// The muted layer, and the layers only it brought in, leave the stage,
    /// and the registry frees each unless something else holds it, as
    /// [`unload`](Self::unload) frees a payload's. Undo steps touching a layer
    /// that leaves are dropped. Staying are a layer with unsaved edits, the
    /// edit target's layer, one with no file to read it from again, the
    /// session layers the stage opened with (a sublayer added to one later
    /// leaves), and the root of a reference or payload target still composed.
    /// A layer a value clip reads stays for the clip alone, composing nothing.
    /// A sublayer muted at open ([`StageBuilder::mute`]) is not read.
    /// [`unmute_layer`](Self::unmute_layer) reads a freed layer from its file
    /// again.
    ///
    /// The layer need not be loaded: muting an identifier the stage does not
    /// (yet) contain records it and takes effect if such a layer is later
    /// encountered. A loaded layer answers to its identifier and to the file it
    /// resolved to (a layer found through a resolver search directory keeps the
    /// search path as its identifier), and either spelling mutes, unmutes or
    /// queries the same layer. The session layer can be muted; the root layer
    /// cannot (it "would lead to empty layer stacks", matching C++), so a
    /// request to mute it is ignored and `is_layer_muted` stays false for the
    /// root.
    ///
    /// This implements Pcp/Stage-level muting. Sdf-level layer muting
    /// (`SdfLayer::SetMuted`, a process-global data swap) is a separate feature
    /// and is not implemented.
    ///
    /// Panics from inside a [`read`](sdf::LayerHandle::read) or an
    /// [`edit`](sdf::LayerHandle::edit) of a layer on the stage's registry.
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
    ///
    /// Panics from inside a [`read`](sdf::LayerHandle::read) or an
    /// [`edit`](sdf::LayerHandle::edit) of a layer on the stage's registry.
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
    /// prim, since loading a not-yet-visible descendant is the common case.
    ///
    /// A `path` that normalizes into a `/__Prototype_N` prototype's namespace
    /// is silently ignored: load rules are always authored in real-namespace
    /// terms, so a rule on a synthetic prototype path would never be
    /// consulted. C++ drops such a path too, but reports a coding error first.
    /// Nor is `path` checked for being present and active on the stage, which
    /// C++ does reject: such a subtree never composes whatever its load rule
    /// says, so the rule simply sits inert in the table.
    pub fn load(&self, path: impl sdf::IntoPath, policy: LoadPolicy) -> Result<(), sdf::PathParseError> {
        self.load_path(&sdf::try_into_path(path)?, policy);
        Ok(())
    }

    /// [`load`](Self::load) for an already-validated path.
    pub(super) fn load_path(&self, path: &sdf::Path, policy: LoadPolicy) {
        let Some(path) = Self::normalize_load_target(path) else {
            return;
        };
        let victims = self.composition.install_load_rules(
            move |rules| match policy {
                LoadPolicy::WithDescendants => rules.load_with_descendants(path),
                LoadPolicy::WithoutDescendants => rules.load_without_descendants(path),
            },
            self,
        );
        self.notify_load_rules_changed(victims);
    }

    /// Unloads `path`'s payload and everything beneath it (C++
    /// `UsdStage::Unload`). Same leniency as [`load`](Self::load) for a
    /// prototype-namespace path.
    ///
    /// The layers the unloaded payloads brought in, and that nothing loaded
    /// still uses, leave the stage, and the registry frees each unless
    /// something else holds it, a [`sdf::LayerHandle`] or another stage. A
    /// layer with unsaved edits stays, as does the edit target's, unlike C++,
    /// which frees a dirty layer nothing holds and holds the edit target's
    /// weakly; so does a layer with no file to read it from again, and a layer
    /// a value clip reads stays for the clip alone, composing nothing. Loading
    /// the payload again reads a freed layer from its file. A
    /// [`sdf::LayerSink`] does not hold its layer, and goes with it.
    pub fn unload(&self, path: impl sdf::IntoPath) -> Result<(), sdf::PathParseError> {
        self.unload_path(&sdf::try_into_path(path)?);
        Ok(())
    }

    /// [`unload`](Self::unload) for an already-validated path.
    pub(super) fn unload_path(&self, path: &sdf::Path) {
        let Some(path) = Self::normalize_load_target(path) else {
            return;
        };
        let victims = self
            .composition
            .install_load_rules(move |rules| rules.unload(path), self);
        self.notify_load_rules_changed(victims);
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
            .map(|path| Ok(Self::normalize_load_target(&sdf::try_into_path(path)?)))
            .filter_map(Result::transpose)
            .collect::<Result<_, sdf::PathParseError>>()?;
        let to_load: Vec<(sdf::Path, LoadPolicy)> = to_load
            .into_iter()
            .map(
                |(path, policy)| Ok(Self::normalize_load_target(&sdf::try_into_path(path)?).map(|path| (path, policy))),
            )
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
    /// (matching whatever `set_load_rules` would do for that same transition),
    /// which a cached value view stamped on one of them will notice.
    ///
    /// It also leaves every payload-target layer under `root` loaded, though
    /// the load *rules* are restored: the swaps free no layer, so one stays
    /// until the next load-rules change ([`load`](Self::load),
    /// [`unload`](Self::unload) and the rest) drops the layers no loaded prim
    /// uses.
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
        self.settle()?;
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
    /// suffix and `strip_variant_selections` collapses any variant
    /// segment — [`pcp::LoadRules`]' table requires genuinely prim-only
    /// paths), then drops a path in the reserved `/__Prototype_N` namespace,
    /// where load rules are never consulted (see [`pcp::LoadRules`]'s
    /// instancing notes) — silently, where C++ reports a coding error before
    /// dropping it (`UsdStage::_IsValidForUnload`, which likewise rejects the
    /// relative path this absolutizes). The test is syntactic, so it
    /// does not depend on whether that prototype has been registered yet.
    ///
    /// A cheap early exit for `load`/`unload`/`load_and_unload` — the real
    /// enforcement of the same invariant lives in `IndexCache::set_load_rules`,
    /// the single choke point every mutation (including a caller-supplied
    /// [`set_load_rules`](Self::set_load_rules) table this normalization never
    /// sees) passes through.
    fn normalize_load_target(path: &sdf::Path) -> Option<sdf::Path> {
        let path = sdf::Path::abs_root().make_absolute(&path.prim_path().strip_variant_selections());
        (!pcp::is_prototype_namespace(&path)).then_some(path)
    }

    /// Fires [`StageSink::load_rules_changed`] with the paths the edit
    /// invalidated, reduced to the subtrees they stand for, after the cache
    /// borrow is released. A no-op edit invalidates nothing and reports nothing.
    fn notify_load_rules_changed(&self, mut resynced: Vec<sdf::Path>) {
        if resynced.is_empty() || self.sinks.borrow().is_empty() {
            return;
        }
        keep_ancestors(&mut resynced);
        self.composition
            .announce(composition::StageNotice::LoadRules(resynced), self);
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
        if self.sinks.borrow().is_empty() {
            return;
        }
        keep_ancestors(&mut resynced);
        let notice = composition::StageNotice::Muting {
            layer: changed.to_owned(),
            muted,
            resynced,
        };
        self.composition.announce(notice, self);
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
    /// The returned [`LayerRef`] borrows the stage's layers (see its borrow
    /// rules).
    pub fn session_layer(&self) -> Option<LayerRef<'_>> {
        let view = self.layer_view();
        let id = *view.session_layers().first()?;
        Some(LayerRef { view, id })
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    ///
    /// When a session layer is present, `defaultPrim` is still read from
    /// the root layer (not the session layer), matching C++ behavior.
    pub fn default_prim(&self) -> Option<Token> {
        self.with_cache(|g, _| Ok(g.default_prim())).unwrap_or_default()
    }

    /// Returns composed pseudo-root stage metadata, honoring a session-layer
    /// opinion over the root layer, and falling back to the default a
    /// registered family declares for a field that applies to layers where no
    /// layer authors it
    /// (C++ `UsdStage::GetMetadata`, with `SdfSchema::GetFallback` behind it).
    ///
    /// The session and root layers' dictionaries merge, over the fallback
    /// dictionary where there is one, and an `asset` path is resolved against
    /// the layer that authored it.
    ///
    /// Distinct from [`Stage::field`] on [`sdf::Path::abs_root`]. Returns an
    /// undecoded [`vt::Value`]; the caller coerces it.
    pub fn stage_metadata(&self, field: impl AsRef<str>) -> Result<Option<vt::Value>> {
        let field = field.as_ref();
        let authored = self.stage_metadata_with(field, pcp::AssetMode::Resolve)?;
        let fallback = self.schema_registry().stage_metadata_fallback(&Token::from(field));
        Ok(match (authored, fallback) {
            (Some(vt::Value::Dictionary(mut dict)), Some(vt::Value::Dictionary(fallback))) => {
                dict.over(fallback.clone());
                Some(vt::Value::Dictionary(dict))
            }
            (Some(authored), _) => Some(authored),
            (None, fallback) => fallback.cloned(),
        })
    }

    /// The authored half of [`stage_metadata`](Self::stage_metadata), with its
    /// `asset` paths as `assets` says: what a flattened layer keeps.
    pub(crate) fn stage_metadata_with(&self, field: &str, assets: pcp::AssetMode) -> Result<Option<vt::Value>> {
        Ok(self.with_cache(|g, c| c.stage_metadata(g, field, assets))?)
    }

    /// Whether the session or root layer authors the pseudo-root metadata
    /// `field` (C++ `UsdStage::HasAuthoredMetadata`). A fallback counts for
    /// nothing, and a block counts as an opinion, so this tells a stage that
    /// states a value equal to the fallback, or blocks the field, from one
    /// that says nothing.
    pub fn has_authored_stage_metadata(&self, field: impl AsRef<str>) -> Result<bool> {
        Ok(self.with_cache(|g, _| Ok(g.has_stage_metadata(field.as_ref())))?)
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
        [sdf::FieldKey::StartTimeCode, sdf::FieldKey::EndTimeCode]
            .into_iter()
            .all(|field| self.has_authored_stage_metadata(field.as_str()).unwrap_or(false))
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
    pub fn interpolation(&self) -> InterpolationType {
        self.interpolation.get()
    }

    /// Override the stage-level interpolation mode at runtime.
    /// Cheap — no recomputation, the next value resolution reads the new mode.
    pub fn set_interpolation(&self, mode: InterpolationType) {
        self.interpolation.set(mode);
    }

    /// Returns the `timeSamples` map value resolution answers from, retimed to
    /// stage time, or `None` when the source that answers is not a `timeSamples`
    /// opinion.
    ///
    /// These are the samples the source
    /// [`Attribute::get_at`](super::Attribute::get_at) reads from, so a stronger
    /// `default` hiding a weaker layer's samples yields `None` here too. A winning value-clip set answers with a schedule rather than a map
    /// and likewise yields `None`; its times reach
    /// [`Self::time_sample_times`].
    ///
    /// This returns the samples uninterpolated. Read through
    /// [`Attribute::get`](super::Attribute::get) with a time code when you
    /// need the stage's [`InterpolationType`] applied to a specific time.
    pub fn time_samples(&self, attr_path: impl sdf::IntoPath) -> Result<Option<sdf::TimeSampleMap>> {
        self.time_samples_with(&sdf::try_into_path(attr_path)?, pcp::AssetMode::Resolve)
    }

    /// [`time_samples`](Self::time_samples) with its `asset` paths as `assets`
    /// says: what a flattened layer keeps.
    pub(crate) fn time_samples_with(
        &self,
        attr_path: &sdf::Path,
        assets: pcp::AssetMode,
    ) -> Result<Option<sdf::TimeSampleMap>> {
        Ok(self.masked_opinions(attr_path, |g, c| c.time_samples(g, attr_path, assets))?)
    }

    /// Returns the sample times of whichever source value resolution answers
    /// from, or `None` when none has samples. Resolves the times without cloning
    /// the sample values.
    ///
    /// Wider than [`Self::time_samples`], which reports only a `timeSamples`
    /// source's map: a winning value-clip set contributes its times here.
    pub fn time_sample_times(&self, attr_path: impl sdf::IntoPath) -> Result<Option<Vec<f64>>> {
        let attr_path = sdf::try_into_path(attr_path)?;
        Ok(self.masked_opinions(&attr_path, |g, c| c.time_sample_times(g, &attr_path))?)
    }

    /// Returns the number of composed `timeSamples` for an attribute, zero when
    /// none are authored. Resolves the count without cloning the sample values.
    pub fn num_time_samples(&self, attr_path: impl sdf::IntoPath) -> Result<usize> {
        let attr_path = sdf::try_into_path(attr_path)?;
        Ok(self.masked_opinions(&attr_path, |g, c| c.num_time_samples(g, &attr_path))?)
    }

    /// Whether an attribute's value may vary over time, the introspection behind
    /// [`Attribute::might_be_time_varying`](super::Attribute::might_be_time_varying).
    /// Reports `true` when the winning value source has more than one composed
    /// sample, and conservatively when that source is a value-clip set with more
    /// than one active clip — those clips can each contribute a different value
    /// even where the discrete sample count collapses to one (spec 12.3.4).
    pub fn value_might_be_time_varying(&self, attr_path: impl sdf::IntoPath) -> Result<bool> {
        let attr_path = sdf::try_into_path(attr_path)?;
        Ok(self.masked_opinions(&attr_path, |g, c| c.value_might_be_time_varying(g, &attr_path))?)
    }

    /// Evaluate an attribute's value at `time`, or at the default time when it
    /// is `None`, under the stage's current [`InterpolationType`]. The
    /// crate-internal resolution engine behind
    /// [`Attribute::get`](super::Attribute::get).
    ///
    /// Resolution visits the prim's contributing sites strongest-first,
    /// probing `timeSamples` (interpolated per §12.5) then `default` at each,
    /// so a stronger layer's `default` hides a weaker layer's samples. Value
    /// clips (§12.3.4) sit between the root layer stack's own opinions and
    /// anything reached across an arc.
    ///
    /// Answers [`pcp::TimedValue::Fallback`] when the attribute is
    /// unauthored, its `default` is blocked, or the stage does not hold the
    /// queried prim, and [`pcp::TimedValue::NoValue`] when
    /// a blocked sample or a clip answers at `time` without a value.
    ///
    /// `read` says which kinds a typed read accepts and what it makes of an
    /// `asset` path ([`pcp::IndexCache::value_at`]).
    pub(crate) fn resolve_at(
        &self,
        attr_path: impl sdf::IntoPath,
        time: Option<f64>,
        read: pcp::ValueRead,
    ) -> Result<pcp::TimedValue> {
        let attr_path = sdf::try_into_path(attr_path)?;
        let interp_type = self.interpolation.get();
        let interp = |samples: &sdf::TimeSampleMap, t: f64| interp::evaluate(samples, t, interp_type);
        Ok(self.masked_opinions(&attr_path, |g, c| c.value_at(g, &attr_path, time, &interp, read))?)
    }

    /// Resolves the cacheable value source for an attribute, the source half of
    /// [`Self::resolve_at`], paired with the stamp it stays replayable under.
    /// Backs [`AttributeQuery`](super::AttributeQuery), which snapshots both and
    /// replays the source across time codes. Resolves to
    /// [`AttributeValueSource::Static`](pcp::AttributeValueSource::Static)
    /// `None` with no stamp when the attribute's prim is outside the population
    /// mask.
    pub(crate) fn resolve_value_source(&self, attr_path: &sdf::Path) -> Result<pcp::StampedValueSource> {
        Ok(self.masked_opinions(attr_path, |g, c| c.resolve_value_source(g, attr_path))?)
    }

    /// Every spec contributing to the property at `path`, strongest first, with
    /// the clip layers participating at `time` when one is named. Backs
    /// [`Attribute::property_stack`](super::Attribute::property_stack) and
    /// [`property_stack_at`](super::Attribute::property_stack_at).
    pub(crate) fn property_stack(&self, path: &sdf::Path, time: Option<f64>) -> Result<Vec<super::SpecSite>> {
        Ok(self.masked_opinions(path, |g, c| c.property_stack(g, path, time))?)
    }

    /// The strongest site whose value opinion would shadow one authored for
    /// the attribute at the current edit target, to a read at `time`. Backs
    /// [`Attribute::shadowing_opinion_at`](super::Attribute::shadowing_opinion_at).
    pub(crate) fn shadowing_opinion(
        &self,
        attr_path: &sdf::Path,
        time: Option<f64>,
    ) -> Result<Option<super::SpecSite>> {
        self.settle()?;
        let (identifier, spec_path) = self.target_spec_path(attr_path)?;
        let outside = || StageAuthoringError::OutsideEditTarget {
            path: attr_path.clone(),
        };
        let layer = self.layers().id_of(&identifier).ok_or_else(outside)?;
        let standing = self.masked_opinions(attr_path, |g, c| {
            c.opinion_standing(g, attr_path, layer, &spec_path, time)
        })?;
        match standing {
            // A prim the stage does not hold has no opinions to be shadowed
            // by, and authoring on it reports that itself.
            None | Some(pcp::Standing::Strongest) => Ok(None),
            Some(pcp::Standing::Shadowed(site)) => Ok(Some(site)),
            Some(pcp::Standing::Absent) => Err(outside().into()),
        }
    }

    /// Resolves where an attribute's value comes from, without producing the
    /// value. Backs [`Attribute::resolve_info`](super::Attribute::resolve_info).
    pub(crate) fn resolve_info(&self, attr_path: &sdf::Path, mode: pcp::ResolveMode) -> Result<pcp::Resolution> {
        let stage_id = self.layer_stack_id().clone();
        // The same policy [`Self::resolve_at`] reads through, so a timed query
        // decides which samples answer exactly as the value read does.
        let interp_type = self.interpolation.get();
        let interp = |samples: &sdf::TimeSampleMap, t: f64| interp::evaluate(samples, t, interp_type);
        Ok(self.masked_opinions(attr_path, |g, c| c.resolve_info(g, &stage_id, attr_path, mode, &interp))?)
    }

    /// The epochs a memoized prim type stays valid under, read together from
    /// one settled cache borrow.
    fn type_epochs(&self) -> TypeEpochs {
        let cache = self.cache();
        TypeEpochs {
            opinions: cache.type_opinion_epoch(),
            population: cache.population_epoch(),
        }
    }

    /// The current population epoch, which advances whenever the composed
    /// population may differ.
    pub(crate) fn population_epoch(&self) -> u64 {
        self.cache().population_epoch()
    }

    /// The stamp a cached answer about `path` is rechecked against: the prim's
    /// revision (`None` when no index is cached there) and the population epoch
    /// a redirection to it was memoized under.
    ///
    /// Read from one settled cache borrow, which the caller settles for
    /// ([`process_pending`](Self::process_pending)) rather than draining here: a
    /// caller checking this against a memo it has borrowed must not have a sink
    /// fire underneath that borrow.
    pub(crate) fn value_stamp(&self, path: &sdf::Path) -> (Option<pcp::PrimRevision>, u64) {
        let cache = self.composition.settled_cache();
        (cache.prim_revision(path), cache.population_epoch())
    }

    /// The stamp an authoring plan rechecks a prim it read against: the
    /// prim's revision (`None` when no index is cached there) and the
    /// population and type-opinion epochs, the three a prim's composed fields
    /// and schema can move with. Read from one settled cache borrow, as
    /// [`value_stamp`](Self::value_stamp) is.
    pub(super) fn plan_stamp(&self, path: &sdf::Path) -> PlanStamp {
        let cache = self.composition.settled_cache();
        PlanStamp {
            revision: cache.prim_revision(path),
            population: cache.population_epoch(),
            type_opinions: cache.type_opinion_epoch(),
        }
    }

    /// The composition's edit epoch ([`pcp::IndexCache::edit_epoch`]): an
    /// authoring plan tells from it whether anything changed what the stage
    /// composes while it was open. Drains first, so a queued direct edit
    /// counts.
    pub(super) fn edit_epoch(&self) -> u64 {
        self.process_pending();
        self.composition.settled_cache().edit_epoch()
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
    /// including one the stage does not hold — gets the registry's empty type.
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
        self.settle()?;
        let path = sdf::try_into_path(path)?;
        let epochs = self.type_epochs();
        if let Some(info) = self.prim_types.borrow().lookup(epochs, &path) {
            return Ok(info);
        }

        // Keyed on the authored list, not the composed one: the composed list
        // is what the definition this identity selects reports back
        // (C++ `_ComposeAuthoredAppliedSchemas`).
        let prim = super::Prim::new(self, path.prim_path());
        let info = self.prim_type_info_for(prim.type_name_composed()?, prim.authored_api_schemas_composed()?)?;
        self.prim_types.borrow_mut().remember(epochs, path, info.clone());
        Ok(info)
    }

    /// The schema type of a prim typed `type_name` with the authored applied
    /// schemas `applied`, the root layer's `fallbackPrimTypes` standing in for
    /// a type the registry does not know: the identity
    /// [`prim_type_info_composed`](Self::prim_type_info_composed) resolves a
    /// composed prim to, for a type and list given rather than composed.
    pub(super) fn prim_type_info_for(
        &self,
        type_name: Option<Token>,
        applied: Vec<Token>,
    ) -> Result<Arc<PrimTypeInfo>, pcp::QueryError> {
        let mut id = PrimTypeId::new(type_name, applied);
        if let Some(mapped) = self.fallback_prim_type(id.type_name())? {
            id = id.with_mapped_type_name(mapped);
        }
        Ok(self.schema_registry.prim_type_info(id))
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
        let Some(vt::Value::Dictionary(fallbacks)) =
            self.field::<vt::Value>(sdf::Path::abs_root(), FALLBACK_PRIM_TYPES)?
        else {
            return Ok(None);
        };
        let Some(candidates) = fallbacks
            .get(type_name.as_str())
            .cloned()
            .and_then(vt::Value::try_as_token_vec)
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
    ///
    /// A path that cannot name a prim on the stage gives the invalid prim,
    /// whose path is empty, as in C++. That is a property or a relationship
    /// target, a path with a variant selection in it, and a relative path.
    pub fn prim(&self, path: impl sdf::IntoPath) -> Result<super::Prim, sdf::PathParseError> {
        let path = sdf::try_into_path(path)?;
        let names_prim = path.is_abs() && (path.is_abs_root() || (path.is_prim() && !path.has_variant_selection()));
        let path = match names_prim {
            true => path,
            false => sdf::Path::default(),
        };
        Ok(super::Prim::new(self, path))
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
        Ok(self.with_cache(|g, c| c.populated_children(g, &root))?)
    }

    // `has_spec` / `spec_type` below are low-level composed-spec infrastructure
    // (the post-composition analog of `SdfAbstractData::HasSpec` /
    // `GetSpecType`), shared by the composed handles and the stage's own status
    // queries. The public, C++-shaped scene queries live on the handles:
    // children / property names on `Prim` (`GetChildren` / `GetPropertyNames`),
    // targets / connections on `Relationship` / `Attribute` (`GetTargets` /
    // `GetConnections`). The handles reach the cache through [`Self::cache`]
    // and [`Self::masked`], which applies the stage's population; child lists
    // come from [`pcp::IndexCache::populated_children`].

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    /// A property is one of the prim's opinions, so a prototype root has none.
    pub(crate) fn has_spec(&self, path: &sdf::Path) -> Result<bool, pcp::QueryError> {
        self.query_at(path, true, Reads::spec_of(path), |g, c| c.has_spec(g, path))
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub(crate) fn spec_type(&self, path: impl sdf::IntoPath) -> Result<Option<sdf::SpecType>, pcp::QueryError> {
        let path = sdf::try_into_path(path)?;
        self.query_at(&path, true, Reads::spec_of(&path), |g, c| c.spec_type(g, &path))
    }

    /// The composed `field` at `path`, undecoded, with its `asset` paths as
    /// `assets` says: what a flattened layer keeps (C++
    /// `Usd_FlattenAccess::GetAllMetadataForFlatten`).
    pub(crate) fn field_with(
        &self,
        path: &sdf::Path,
        field: &str,
        assets: pcp::AssetMode,
    ) -> Result<Option<vt::Value>, pcp::QueryError> {
        self.masked_opinions(path, |g, c| c.resolve_field_with(g, path, field, assets))
    }

    /// Resolves a composed field value by walking the prim index from strongest
    /// to weakest. The post-composition analog of `SdfLayer::GetField` /
    /// `SdfAbstractData::Get`, for fields the typed accessors do not expose;
    /// C++ has no `UsdStage::GetField`. Prefer the typed handles
    /// ([`Attribute::get`], the `Prim::*` accessors, and the `Stage::*`
    /// accessors) where one covers the field — they delegate here.
    ///
    /// For prim paths, walks the prim index nodes. For property paths (containing
    /// a `.`), uses the owning prim's index to determine layer order, then queries
    /// the property spec directly in each layer.
    ///
    /// Returns the composed value: strongest-opinion-wins for plain fields,
    /// with spec 12.2's field-class rules — list-op folding, dictionary
    /// merging, path-expression `%_` composition,
    /// `specifier`/`variability`/`custom` — applied where they hold.
    /// A prototype root reads no field but `specifier`, which is `def` (C++
    /// reads the root through an empty prim index, and `_GetPrimSpecifierImpl`
    /// answers `def` for it).
    ///
    /// `None` if no layer provides a value. A [`vt::Value::ValueBlock`]
    /// blocks the opinions weaker than it: the composed result is whatever
    /// the stronger opinions alone produce, or `None` when the block is the
    /// strongest opinion.
    ///
    /// The return type is generic: use `vt::Value` to get the raw enum, or a
    /// concrete type (e.g. `bool`, `f64`, `String`) to convert automatically
    /// via [`TryFrom<vt::Value>`].
    ///
    /// Accepts both [`sdf::FieldKey`] and `&str` as the field name.
    ///
    /// [`Attribute::get`]: super::Attribute::get
    pub fn field<T>(&self, path: impl sdf::IntoPath, field: impl AsRef<str>) -> Result<Option<T>, pcp::QueryError>
    where
        T: TryFrom<vt::Value>,
        T::Error: Into<pcp::QueryError>,
    {
        self.settle()?;
        let path = sdf::try_into_path(path)?;
        let field = field.as_ref();
        let mut raw = self.field_with(&path, field, pcp::AssetMode::Resolve)?;
        // A prototype root reads no opinions, but is always defined (C++
        // `_GetPrimSpecifierImpl`).
        if raw.is_none() && field == sdf::FieldKey::Specifier.as_str() && self.cache().is_prototype(&path) {
            raw = Some(vt::Value::Specifier(sdf::Specifier::Def));
        }
        super::decode_value(raw)
    }

    /// Runs a composed query at `path` under the stage's population: when the
    /// population does not reach the path's owning prim — the mask excludes
    /// it, or an ancestor is inactive (C++ populates neither) — resolves to
    /// `T::default()` without composing that prim; otherwise runs `query` with
    /// a short mutable cache borrow. This is the query runner the composed
    /// handles ([`Prim`](super::Prim) / [`Attribute`](super::Attribute) /
    /// [`Relationship`](super::Relationship)) build their scene queries on.
    pub(crate) fn masked<T: Default>(
        &self,
        path: &sdf::Path,
        query: impl FnMut(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
    ) -> Result<T, pcp::QueryError> {
        self.query_at(path, true, Reads::Source, query)
    }

    /// Runs a query that reads a prim's opinions, under the stage's population
    /// like [`Self::masked`]. A prototype root answers `T::default()`. C++
    /// reads its opinions through an empty prim index
    /// (`Usd_PrimData::GetPrimIndex`), while its children, validity and flags
    /// come from the index the cache composed for it.
    pub(crate) fn masked_opinions<T: Default>(
        &self,
        path: &sdf::Path,
        query: impl FnMut(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
    ) -> Result<T, pcp::QueryError> {
        self.query_at(path, true, Reads::Opinions, query)
    }

    /// [`Self::masked_opinions`] outside the stage's population, for the
    /// composition-tier reads that answer for a prim the stage does not hold.
    pub(crate) fn opinions<T: Default>(
        &self,
        path: &sdf::Path,
        query: impl FnMut(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
    ) -> Result<T, pcp::QueryError> {
        self.query_at(path, false, Reads::Opinions, query)
    }

    /// The runner behind [`Self::masked`], [`Self::masked_opinions`] and
    /// [`Self::opinions`]: answers `T::default()` without running `query`
    /// when `gated` is set and the population does not reach the path's prim
    /// (see [`pcp::IndexCache::population_reaches`]), or when `reads` is
    /// [`Reads::Opinions`] and that prim is a prototype root.
    fn query_at<T: Default>(
        &self,
        path: &sdf::Path,
        gated: bool,
        reads: Reads,
        mut query: impl FnMut(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
    ) -> Result<T, pcp::QueryError> {
        let prim = path.prim_path();
        // Before the borrow, not inside it: a prototype path is unanswerable
        // until stage population has registered its root, and completing that
        // is itself a composed walk.
        self.resolve_prototype_path(&prim)?;
        self.with_cache(move |g, c| {
            let hidden =
                (gated && !c.population_reaches(g, &prim)?) || (reads == Reads::Opinions && c.is_prototype(&prim));
            if hidden { Ok(T::default()) } else { query(g, c) }
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
        self.settle()?;
        if self.prototypes_discovered.get() == Some(self.population_epoch()) {
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
    /// only into populated prims, so nothing below an inactive one is composed
    /// or loaded, stops at each instance, whose subtree belongs to its
    /// prototype, and then walks each newly registered prototype's namespace
    /// the same way to reach nested instances.
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
            let epoch = self.population_epoch();
            let mut roots: Vec<sdf::Path> = Vec::new();
            let mut visited = sdf::PathSet::default();
            self.register_instances_below(&sdf::Path::abs_root(), &mut roots)?;
            // A prototype's own namespace can hold further instances, and each
            // of those mints a prototype to walk in turn. The visited set
            // bounds the fixpoint however the composition nests.
            while let Some(root) = roots.pop() {
                if visited.insert(root.clone()) {
                    self.register_instances_below(&root, &mut roots)?;
                }
            }
            if self.population_epoch() == epoch {
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
            let step = self.with_cache(|g, c| match c.prototype_of(g, &path)? {
                Some(prototype) => Ok(Err(prototype)),
                None => Ok(Ok(c.populated_children(g, &path)?)),
            })?;
            match step {
                // An instance's subtree belongs to its prototype, so stop here
                // and walk that namespace in its own right.
                Err(prototype) => roots.push(prototype),
                // Reversed, as `traverse` does, so the walk visits children in
                // namespace order and prototypes mint in stage order. A prim
                // that is not populated has none.
                Ok(children) => {
                    for name in children.iter().rev() {
                        if let Ok(child) = path.append_path(name.as_str()) {
                            stack.push(child);
                        }
                    }
                }
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
    pub fn node_layer_stack(&self, node: pcp::Node<'_>) -> Option<Vec<(pcp::LayerId, sdf::LayerOffset)>> {
        self.layers().try_layer_stack(node.layer_stack_id()).map(<[_]>::to_vec)
    }

    /// Returns the root layer's `customLayerData` dictionary, if authored.
    /// Mirrors C++ `UsdStage::GetRootLayer()->GetCustomLayerData()`: layer
    /// metadata is read from the root layer alone, not composed across the
    /// layer stack.
    pub fn custom_layer_data(&self) -> Result<Option<vt::Value>> {
        Ok(self.field::<vt::Value>(sdf::Path::abs_root(), sdf::FieldKey::CustomLayerData)?)
    }

    /// Returns every prototype root (`/__Prototype_N`) this stage's population
    /// contains, in registration order (C++ `UsdStage::GetPrototypes`).
    ///
    /// Completing the population is what makes the answer whole: the registry
    /// fills as instances compose, so a stage that has composed nothing knows
    /// no prototypes until this call has walked it. Only a prim the mask
    /// exposes can register, so no filtering is applied here.
    pub fn prototypes(&self) -> Result<Vec<sdf::Path>> {
        self.settle()?;
        self.ensure_prototypes_discovered()?;
        Ok(self.cache().prototypes())
    }

    /// Returns the resolved stage status bits for a prim.
    pub fn prim_status(&self, prim: impl sdf::IntoPath) -> Result<PrimStatus> {
        self.prim_status_masked(&sdf::try_into_path(prim)?.prim_path(), PrimStatus::all())
    }

    /// Computes only the status bits set in `mask`, with the inherited four
    /// ([`PrimStatus::INHERITED`]) answered together whenever any is asked,
    /// since one composition down the ancestor chain yields them all. Bits
    /// outside `mask` are otherwise left unset. Used by traversal so unused
    /// checks (e.g. INSTANCE, MODEL for default traversal) are skipped.
    pub(super) fn prim_status_masked(&self, prim: &sdf::Path, mask: PrimStatus) -> Result<PrimStatus> {
        let status = self.masked(prim, |g, c| {
            let mut status = PrimStatus::empty();
            if mask.intersects(PrimStatus::INHERITED) {
                let chain: Vec<sdf::Path> = prim.ancestors_below_root().collect();
                status = chain.iter().rev().try_fold(PrimStatus::ROOT, |parent, ancestor| {
                    Self::status_below(c, g, parent, ancestor)
                })?;
            }
            if mask.contains(PrimStatus::INSTANCE) {
                status.set(PrimStatus::INSTANCE, c.is_instance(g, prim)?);
            }
            Ok(status)
        })?;
        self.with_own_status(prim, status, mask)
    }

    /// [`prim_status_masked`](Self::prim_status_masked) for a prim whose
    /// parent's inherited bits are `parent`: its own compose from them in one
    /// step.
    fn child_status_masked(&self, prim: &sdf::Path, parent: PrimStatus, mask: PrimStatus) -> Result<PrimStatus> {
        let status = self.masked(prim, |g, c| {
            let mut status = PrimStatus::empty();
            if mask.intersects(PrimStatus::INHERITED) {
                status = Self::status_below(c, g, parent, prim)?;
            }
            if mask.contains(PrimStatus::INSTANCE) {
                status.set(PrimStatus::INSTANCE, c.is_instance(g, prim)?);
            }
            Ok(status)
        })?;
        self.with_own_status(prim, status, mask)
    }

    /// The children of `parent` that match `predicate`, in the order
    /// [`Prim::children`](super::Prim::children) lists them, each with the
    /// status it composed (C++ `UsdPrim::GetFilteredChildren`).
    ///
    /// `composed` is the parent's own status where a walk has it from the
    /// step that listed the parent. With it, and while the population it
    /// was read under stands, each child composes its status from the
    /// parent's in one step, as C++ `Usd_PrimData` does. Without it the
    /// parent's status is composed from the pseudo-root first.
    ///
    /// An instance has no children unless `predicate` traverses instance
    /// proxies. An instance proxy lists its children under either setting,
    /// as C++ `Usd_CreatePredicateForTraversal` keeps proxy traversal on
    /// for a walk that starts at a proxy.
    pub(super) fn filtered_children(
        &self,
        parent: &sdf::Path,
        predicate: PrimPredicate,
        composed: Option<ComposedStatus>,
    ) -> Result<Vec<(super::Prim, ComposedStatus)>> {
        self.settle()?;
        let epoch = self.population_epoch();
        let composed = composed.filter(|composed| {
            composed.epoch == epoch && composed.prim.path() == parent && composed.prim.stage() == self
        });
        let status = match &composed {
            _ if parent.is_abs_root() => PrimStatus::ROOT,
            Some(composed) => composed.status,
            None => self.prim_status_masked(parent, PrimStatus::INHERITED)?,
        };
        if !predicate.traverse_instance_proxies {
            let instance = match composed.as_ref().and_then(ComposedStatus::is_instance) {
                Some(instance) => instance,
                None => self.masked(parent, |g, cache| cache.is_instance(g, parent))?,
            };
            if instance && !self.masked(parent, |g, cache| cache.is_instance_proxy(g, parent))? {
                return Ok(Vec::new());
            }
        }

        // A child's inherited bits are composed whatever the predicate
        // consults, so that its status can be handed to the next step.
        let needed = predicate.consulted_bits().union(PrimStatus::INHERITED);
        let instance_known = needed.contains(PrimStatus::INSTANCE);
        let names = self.masked(parent, |g, cache| cache.populated_children(g, parent))?;
        let mut children = Vec::with_capacity(names.len());
        for name in names {
            let Ok(child) = parent.append_path(name.as_str()) else {
                continue;
            };
            let status = self.child_status_masked(&child, status, needed)?;
            if predicate.matches(status) {
                let child = super::Prim::new(self, child);
                let composed = ComposedStatus {
                    prim: child.clone(),
                    status,
                    instance_known,
                    epoch,
                };
                children.push((child, composed));
            }
        }
        Ok(children)
    }

    /// The status of `prim` under `predicate`, for a walk that starts at the
    /// prim and lists it first (C++ `UsdPrimRange(start, predicate)`), or
    /// `None` where the prim does not match or nothing composes it.
    pub(super) fn matching_status(&self, prim: &sdf::Path, predicate: PrimPredicate) -> Result<Option<ComposedStatus>> {
        self.settle()?;
        if !self.has_spec(prim)? {
            return Ok(None);
        }
        let needed = predicate.consulted_bits().union(PrimStatus::INHERITED);
        let status = self.prim_status_masked(prim, needed)?;
        Ok(predicate.matches(status).then(|| ComposedStatus {
            prim: super::Prim::new(self, prim.clone()),
            status,
            instance_known: needed.contains(PrimStatus::INSTANCE),
            epoch: self.population_epoch(),
        }))
    }

    /// `prim`'s inherited bits below a parent whose are `parent`, from the
    /// prim's own opinions as C++ `Usd_PrimData::_ComposeAndCacheFlags`
    /// combines them: active and defined require the parent's, abstract is
    /// the parent's or the prim's own `class`, and loaded requires an active
    /// prim below a loaded parent whose own payload, if any, the load rules
    /// include. A prim nothing composes has no status.
    fn status_below(
        cache: &mut pcp::IndexCache,
        graph: &pcp::LayerView<'_>,
        parent: PrimStatus,
        prim: &sdf::Path,
    ) -> Result<PrimStatus, pcp::QueryError> {
        let Some(own) = cache.own_status(graph, prim)? else {
            return Ok(PrimStatus::empty());
        };
        let active = parent.contains(PrimStatus::ACTIVE) && own.active;
        let mut status = PrimStatus::empty();
        status.set(PrimStatus::ACTIVE, active);
        status.set(
            PrimStatus::LOADED,
            active && parent.contains(PrimStatus::LOADED) && own.payload_included,
        );
        status.set(
            PrimStatus::DEFINED,
            parent.contains(PrimStatus::DEFINED) && own.defining,
        );
        status.set(PrimStatus::ABSTRACT, parent.contains(PrimStatus::ABSTRACT) || own.class);
        Ok(status)
    }

    /// `status` with the bits `mask` asks for that neither `prim`'s ancestors
    /// nor its own composition decide.
    fn with_own_status(&self, prim: &sdf::Path, mut status: PrimStatus, mask: PrimStatus) -> Result<PrimStatus> {
        if mask.intersects(PrimStatus::MODEL | PrimStatus::IN_PROTOTYPE) {
            let prim = super::Prim::new(self, prim.clone());
            if mask.contains(PrimStatus::MODEL) {
                status.set(PrimStatus::MODEL, prim.is_model()?);
            }
            if mask.contains(PrimStatus::IN_PROTOTYPE) {
                status.set(PrimStatus::IN_PROTOTYPE, prim.is_in_prototype()?);
            }
        }
        Ok(status)
    }

    /// Borrows the stage's composition cache, first draining any pending layer
    /// edits so the cache reflects every commit before it is read.
    pub(crate) fn cache(&self) -> sdf::Held<'_, pcp::IndexCache> {
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
    /// `layer` joins the stage under its own identifier, which must be the
    /// spelling the stage's resolver gives a layer of that name; an anonymous
    /// identifier always is. The stage's registry takes `layer`, as
    /// [`LayerRegistry::adopt`](sdf::LayerRegistry::adopt) does.
    ///
    /// Returns [`StageAuthoringError::LayerNotFound`] if `parent` is not in the
    /// stage, [`StageAuthoringError::IncompatibleLayerIdentifier`] if the
    /// stage's resolver spells `layer`'s identifier another way, and
    /// [`StageAuthoringError::Layer`] if `parent` is read-only, and
    /// [`StageAuthoringError::Registry`] with
    /// [`sdf::LayerError::Duplicate`] when the registry already holds a layer
    /// with `layer`'s identifier or read from its file. In
    /// every case the graph is left untouched — `layer` only joins it once the
    /// parent edit succeeds, so a failed insert never leaves an orphan node —
    /// and `layer` is dropped.
    ///
    /// If `layer` authors its own `subLayers` naming layers not yet loaded,
    /// the recompose records them as sublayer demands and the load barrier
    /// opens them from disk, with one that fails to resolve surfacing as an
    /// [`UnresolvedSublayer`](pcp::CompositionDiagnostic::UnresolvedSublayer) diagnostic — the
    /// same treatment the root layer's sublayers get at open.
    pub fn insert_layer(
        &self,
        parent: &str,
        pos: usize,
        layer: sdf::Layer,
        offset: sdf::LayerOffset,
    ) -> Result<(), StageAuthoringError> {
        self.settle()?;
        let identifier = layer.identifier().to_string();
        // Author the parent's metadata first; the child node is added only after
        // this succeeds (the authored asset path is a plain string, so the node
        // need not exist yet — only the later rebuild's edge resolution needs it).
        let edited = {
            let layers = self.composition.authoring_graph();
            let parent_id = layers.id_of(parent).ok_or_else(|| StageAuthoringError::LayerNotFound {
                layer: parent.to_string(),
            })?;
            let expected = layers.layer_registry().in_memory_identifier(&identifier);
            if expected != identifier {
                return Err(StageAuthoringError::IncompatibleLayerIdentifier {
                    expected: expected.into_owned(),
                    identifier,
                });
            }
            let joined = sdf::LoadedLayer::from(layers.layer_registry().adopt(layer).map_err(|refused| refused.error)?);
            self.commit_layer(&layers, parent_id, None, |l| {
                l.pseudo_root_mut()
                    .map(|mut root| root.insert_sublayer(pos, identifier, offset))
                    .map_err(StageAuthoringError::from)
            })
            .map(|committed| (committed, joined))
        };
        // Add the child node only once the parent edit succeeded, so a failed
        // insert never leaves an orphan node. Interning subscribes
        // the stage's recorder, the same path opening a stage uses. It runs
        // before the parent's sinks hear of the edit. A sink that reads the
        // stage then composes the child given here, not a copy read from its
        // file.
        let edited = edited.map(|(committed, joined)| {
            self.composition.intern_layer(joined, self);
            self.composition.deliver(committed, self);
        });
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
        self.settle()?;
        let edited = {
            let layers = self.composition.authoring_graph();
            let parent_id = layers.id_of(parent).ok_or_else(|| StageAuthoringError::LayerNotFound {
                layer: parent.to_string(),
            })?;
            // Resolve `child` to a layer id (an exact canonical identifier, or an
            // asset path authored relative to `parent`), then find the authored
            // `subLayers` entry that resolves to the same layer. An entry is
            // authored relative to `parent`, so anchoring it the way the load path
            // interned the sublayer makes the entry's canonical id comparable to
            // `child_id` even when the entry string differs from the canonical id.
            let authored = {
                let view = layers.view()?;
                view.find_relative(child, parent_id).and_then(|child_id| {
                    let subs = view.layer(parent_id).pseudo_root()?.sublayers()?;
                    subs.into_iter()
                        .find(|entry| view.find_relative(entry, parent_id) == Some(child_id))
                })
            };
            authored.map(|entry| {
                self.commit_layer(&layers, parent_id, None, move |l| {
                    l.pseudo_root_mut()
                        .map(|mut root| root.remove_sublayer(&entry))
                        .map(|_| ())
                        .map_err(StageAuthoringError::from)
                })
            })
        };
        // A removed entry changes `subLayers`, so a non-empty change set means a
        // sublayer was removed; no authored entry means nothing to remove.
        match edited {
            Some(edited) => {
                let edited = edited.map(|committed| self.composition.deliver(committed, self));
                self.process_pending();
                edited
            }
            None => Ok(false),
        }
    }

    /// Borrows the stage's layer graph, first draining any pending layer edits so
    /// the graph reflects every commit before it is read — a structural edit
    /// (sublayers, offsets, relocates) leaves the topology stale until then. The
    /// drain is a no-op when nothing is pending. The graph's structure only:
    /// [`layer_view`](Self::layer_view) reads the layers' content too.
    pub(crate) fn layers(&self) -> sdf::Held<'_, pcp::LayerGraph> {
        self.process_pending();
        self.composition.settled_graph()
    }

    /// [`layers`](Self::layers) with the layers' content borrowed beside the
    /// graph. Panics from inside a [`LayerHandle::edit`](sdf::LayerHandle::edit)
    /// closure on one of the stage's layers, which holds the content.
    pub(crate) fn layer_view(&self) -> pcp::LayerView<'_> {
        self.process_pending();
        self.composition.settled_view()
    }

    /// Drains, then runs a composed query against the settled stage through
    /// [`StageComposition::query`](composition::StageComposition::query), which
    /// owns the query/load fixpoint.
    pub(crate) fn with_cache<T>(
        &self,
        query: impl FnMut(&pcp::LayerView<'_>, &mut pcp::IndexCache) -> Result<T, pcp::QueryError>,
    ) -> Result<T, pcp::QueryError> {
        self.settle()?;
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
    /// family whose schematics layer resolved from nowhere — an anonymous one,
    /// as C++ always has — reads back exactly as C++ leaves it, since resolving
    /// an unanchored relative path
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
    pub(crate) fn resolve_schema_asset(&self, source: &Schematics, value: vt::Value) -> vt::Value {
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
    pub fn prim_matches(&self, path: &sdf::Path, predicate: PrimPredicate) -> Result<bool> {
        Ok(predicate.matches(self.prim_status_masked(path, predicate.consulted_bits())?))
    }

    /// Traverses composed prims depth-first, visiting prims that match `predicate`.
    ///
    /// Pass [`PrimPredicate::DEFAULT`] for OpenUSD's usual traversal region
    /// (active, loaded, defined, non-abstract). Descendants are pruned when
    /// inherited status bits make it impossible for them to match, such as below
    /// unloaded, undefined, or abstract prims when the predicate excludes those
    /// regions. An inactive prim has no descendants on the stage. A predicate
    /// that admits it, [`PrimPredicate::ALL`] included, visits the prim and
    /// nothing below it (C++ `UsdPrimRange` under `UsdPrimAllPrimsPredicate`).
    pub fn traverse(&self, predicate: PrimPredicate, mut visitor: impl FnMut(&sdf::Path)) -> Result<()> {
        self.settle()?;
        let needed = predicate.consulted_bits();
        // Each prim carries its parent's status and the population epoch it
        // was read under. While the population is unchanged the prim composes
        // its inherited bits from that status and its own opinions, as C++
        // `Usd_PrimData` does; after a change it walks its ancestors afresh.
        let mut stack = vec![(sdf::Path::abs_root(), None)];

        while let Some((path, parent)) = stack.pop() {
            let epoch = self.population_epoch();
            let status = if path.is_abs_root() {
                PrimStatus::ROOT
            } else {
                let status = match parent {
                    Some((parent_epoch, parent)) if parent_epoch == epoch => {
                        self.child_status_masked(&path, parent, needed)?
                    }
                    _ => self.prim_status_masked(&path, needed)?,
                };
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
                status
            };

            let children = self.masked(&path, |g, cache| cache.populated_children(g, &path))?;
            // Push in reverse so first child is visited first.
            for name in children.iter().rev() {
                if let Ok(child) = path.append_path(name.as_str()) {
                    stack.push((child, Some((epoch, status))));
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
/// Created via [`Stage::builder`]. Configures the [`sdf::LayerRegistry`] layers
/// load through (resolver + file formats) and composition options.
pub struct StageBuilder {
    registry: sdf::LayerRegistry,
    variant_fallbacks: pcp::VariantFallbackMap,
    session_layer: Option<String>,
    initial_load_set: InitialLoadSet,
    population_mask: StagePopulationMask,
    interpolation: InterpolationType,
    muted: HashSet<String>,
    schema_registry: Option<Arc<SchemaRegistry>>,
}

/// What a stack open collected: its layers, the diagnostics of the
/// sublayers it could not load, and those failures as the graph records
/// them, so the stage reports each without opening it again.
#[derive(Default)]
struct CollectedLayers {
    layers: Vec<sdf::LoadedLayer>,
    diagnostics: pcp::Diagnostics,
    failures: Vec<pcp::LoadFailureSeed>,
}

impl StageBuilder {
    fn new() -> Self {
        Self {
            registry: sdf::LayerRegistry::default(),
            variant_fallbacks: pcp::VariantFallbackMap::new(),
            session_layer: None,
            initial_load_set: InitialLoadSet::LoadAll,
            population_mask: StagePopulationMask::all(),
            interpolation: InterpolationType::default(),
            muted: HashSet::new(),
            schema_registry: None,
        }
    }

    /// Sets the [`LayerRegistry`](sdf::LayerRegistry) the stage loads layers
    /// through and holds them in. Stages on one registry share each layer: a
    /// layer one of them holds is read once, and an edit through any of them
    /// reaches the others.
    ///
    /// Opening a stage from inside a read or an edit of the registry's layers
    /// fails with [`sdf::LayerError::Busy`].
    pub fn registry(mut self, registry: sdf::LayerRegistry) -> Self {
        self.registry = registry;
        self
    }

    /// Sets a custom asset resolver, wrapping it in a [`sdf::LayerRegistry`]
    /// over the built-in formats. A convenience over
    /// [`registry`](Self::registry).
    pub fn resolver<R: ar::Resolver + 'static>(mut self, resolver: R) -> Self {
        self.registry = sdf::LayerRegistry::new(Box::new(resolver));
        self
    }

    /// Sets the stage-level interpolation mode for time-sampled
    /// attribute queries through [`Attribute::get`](super::Attribute::get).
    /// Default per AOUSD §12.5 is [`InterpolationType::Linear`].
    pub fn interpolation(mut self, mode: InterpolationType) -> Self {
        self.interpolation = mode;
        self
    }

    /// Sets the schemas the stage resolves fallback values against.
    ///
    /// Defaults to [`SchemaRegistry::global`](SchemaRegistry::global), the
    /// process-wide registry. Supply one built through
    /// [`SchemaRegistry::builder`](SchemaRegistry::builder) to give a stage
    /// schemas the process does not have; that carries the core `usd` family
    /// too, and
    /// [`SchemaRegistryBuilder::empty`](super::SchemaRegistryBuilder::empty)
    /// is what gives a stage none. The registry is pinned for the stage's
    /// life.
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
        // One cache scope spans the open. A packaged root is opened once for
        // its default-layer lookup, its probes and its entry reads.
        let _scope = ar::CacheScope::begin();
        let root = self.registry.prepare_root(root_path, None)?;
        self.open_root(root)
    }

    /// Opens a stage whose root is `layer`, a layer already read (C++
    /// `UsdStage::Open(SdfLayerHandle)`). The layer's data is the stage's root
    /// as it stands, unsaved edits included, and its sublayers open through
    /// the builder's registry, as [`open`](Self::open)'s do.
    ///
    /// The root keeps the layer's identifier as given. The builder's registry
    /// takes the layer, sinks and all, and holds it for every stage on the
    /// registry. Fails with [`sdf::LayerError::Duplicate`] when the registry
    /// already holds a layer with its identifier or read from its file.
    pub fn open_layer(self, layer: sdf::Layer) -> Result<Stage> {
        let _scope = ar::CacheScope::begin();
        let root = self.registry.adopt(layer).map_err(|refused| refused.error)?;
        self.open_root(root.into())
    }

    /// Opens a stage over `root`, a root layer the builder's registry holds,
    /// with the session layer the builder names.
    fn open_root(self, root: sdf::LoadedLayer) -> Result<Stage> {
        // The stage root stack is one layer stack whose single expression-variable
        // context (C++ `PcpExpressionVariables`) — the root layer's own variables
        // overlaid by the session root's own — resolves the `${VAR}` sublayers of
        // both the session region and the root region. Compose it once, up front,
        // and collect both regions against it: a session sublayer can then reference
        // a variable authored on the stage root layer (and a root sublayer one on the
        // session), and composition later resolves each `${VAR}` sublayer to the same
        // layer this collection opened.
        let session = self.prepare_session()?;
        let root_stack_vars = self.root_stack_expression_variables(&root, session.as_ref())?;
        // The requested mutes as the identifiers the open meets, the root's
        // left out: muting the root is ignored.
        let anchor = root.handle.anchor_location();
        let mut muted: HashSet<String> = self
            .muted
            .iter()
            .map(|m| self.registry.create_identifier(m, anchor))
            .collect();
        muted.remove(&root.identifier);
        muted.remove(root.handle.identifier());
        let session = session
            .map(|session| self.collect_layers(session, &root_stack_vars, &muted))
            .transpose()?
            .unwrap_or_default();
        let root = self.collect_layers(root, &root_stack_vars, &muted)?;
        let session_layer_count = session.layers.len();
        let layers = session.layers.into_iter().chain(root.layers).collect();
        let diagnostics = session.diagnostics.into_iter().chain(root.diagnostics).collect();
        let failures = session.failures.into_iter().chain(root.failures).collect();
        Ok(self.assemble(layers, session_layer_count, diagnostics, failures))
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
        self.open_layer(sdf::Layer::new_anonymous(identifier.into()))
    }

    /// The configured session layer, held ahead of its stack, or `None` when
    /// the builder has none.
    fn prepare_session(&self) -> Result<Option<sdf::LoadedLayer>> {
        Ok(self
            .session_layer
            .as_deref()
            .map(|path| self.registry.prepare_root(path, None))
            .transpose()?)
    }

    /// Opens the sublayer stack of `root`, a root layer
    /// [`LayerRegistry::prepare_root`] holds.
    ///
    /// References and payloads are not followed here — composition opens those
    /// target layers on demand (see [`Stage::with_cache`]), so the population
    /// mask prunes them naturally: a culled prim is never composed, so its arc
    /// targets are never demanded. A missing sublayer is recorded as an
    /// [`UnresolvedSublayer`](pcp::CompositionDiagnostic::UnresolvedSublayer) collection error
    /// rather than aborting the open; one under a muted branch is filtered out
    /// later, once the muted-aware graph exists (see
    /// [`StageBuilder::assemble`](Self::assemble)). A sublayer the builder
    /// mutes, one of the identifiers in `muted`, is not read.
    fn collect_layers(
        &self,
        root: sdf::LoadedLayer,
        ancestor_expr_vars: &HashMap<String, vt::Value>,
        muted: &HashSet<String>,
    ) -> Result<CollectedLayers> {
        let diagnostics = RefCell::new(pcp::Diagnostics::default());
        let failures = RefCell::new(Vec::new());
        // `ancestor_expr_vars` are the expression variables the enclosing context
        // contributes: the session layers' composed set for the root stack, empty
        // for the session stack itself (nothing sublayers it).
        let layers = self.registry.open_prepared_stack(
            root,
            ancestor_expr_vars,
            false,
            &|error| {
                failures.borrow_mut().extend(pcp::load_failure_seed(&error));
                diagnostics.borrow_mut().report(error.into());
                Ok(())
            },
            &|identifier| {
                if muted.contains(identifier) {
                    sdf::Presence::Excluded
                } else {
                    sdf::Presence::Absent
                }
            },
        )?;
        Ok(CollectedLayers {
            layers,
            diagnostics: diagnostics.into_inner(),
            failures: failures.into_inner(),
        })
    }

    /// Whether the builder's requested mutes name `identifier`, each spelling
    /// canonicalized against `root`, the root layer's anchor, the way the graph's
    /// muted set is (C++ `Pcp_MutedLayers::_GetCanonicalLayerId`): resolved
    /// to the identifier its layer interns under. Any spelling of one layer
    /// therefore matches. Lets collection test an interned identifier for
    /// muting before the graph exists.
    fn mutes(&self, root: Option<&ar::ResolvedPath>, identifier: &str) -> bool {
        self.muted
            .iter()
            .any(|m| self.registry.create_identifier(m, root) == identifier)
    }

    /// The stage root stack's single expression-variable context (C++
    /// `PcpExpressionVariables`): the stage root layer's own `expressionVariables`
    /// overlaid by the session root's own (session wins), a muted session root
    /// contributing none. Read shallowly from the two root layers — their sublayers
    /// contribute nothing — since it is the fixed context both the session region's
    /// and the root region's `${VAR}` sublayers resolve against.
    fn root_stack_expression_variables(
        &self,
        root: &sdf::LoadedLayer,
        session: Option<&sdf::LoadedLayer>,
    ) -> Result<HashMap<String, vt::Value>> {
        let own = |layer: &sdf::LoadedLayer| -> Result<HashMap<String, vt::Value>> {
            Ok(layer
                .handle
                .read(|layer| sdf::expr::read_variables(layer.data()).map(Cow::into_owned))??)
        };
        let mut vars = own(root)?;
        if let Some(session) = session
            && !self.mutes(root.handle.anchor_location(), &session.identifier)
        {
            let session_own = own(session)?;
            sdf::expr::compose_over(&mut vars, &session_own);
        }
        Ok(vars)
    }

    /// Assemble a [`Stage`] from collected layers: the construction tail every
    /// open of the builder ends in. Any new `Stage` field must be wired in here
    /// once.
    fn assemble(
        self,
        layers: Vec<sdf::LoadedLayer>,
        session_layer_count: usize,
        collection_diagnostics: pcp::Diagnostics,
        failures: Vec<pcp::LoadFailureSeed>,
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
                .map(|l| l.handle.identifier().to_string())
                .unwrap_or_default(),
            session_layer: (session_layer_count > 0).then(|| layers[0].handle.identifier().to_string()),
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
            composition: StageComposition::new(
                pcp::LayerGraph::new(self.registry),
                pcp::IndexCache::new(
                    self.variant_fallbacks,
                    load_rules,
                    self.population_mask,
                    collection_diagnostics,
                ),
            ),
            initial_load_set: self.initial_load_set,
            prototypes_discovered: Cell::new(None),
            interpolation: Cell::new(self.interpolation),
            edit_target: RefCell::new(edit_target),
            saved_edit_targets: RefCell::default(),
            layer_stack_id,
            sinks: RefCell::default(),
            observers: RefCell::default(),
            edit_provenance: TxnTable::default(),
            editor: sdf::EditorId::next(),
            schema_registry: self.schema_registry.unwrap_or_else(|| SchemaRegistry::global().clone()),
            prim_types: RefCell::default(),
        }));
        stage
            .composition
            .initialize(layers, session_layer_count, self.muted, failures, &stage);
        stage
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::error;
    use std::fs;
    use std::panic::{self, AssertUnwindSafe};
    use std::path::Path as FsPath;

    use super::*;
    use crate::usd;
    use crate::usdz;

    /// Assembles a [`Stage`] from hand-built layers, which the builder's
    /// registry takes, so a test can build a multi-layer stage (references,
    /// sublayers) without files. A layer repeating an earlier one's identifier
    /// collapses onto it.
    pub(crate) trait MakeStage {
        /// The stage over `layers`, the first `session_layer_count` of them
        /// session layers.
        fn make_stage(
            self,
            layers: Vec<sdf::Layer>,
            session_layer_count: usize,
            collection_diagnostics: pcp::Diagnostics,
        ) -> Stage;
    }

    impl MakeStage for StageBuilder {
        fn make_stage(
            self,
            layers: Vec<sdf::Layer>,
            session_layer_count: usize,
            collection_diagnostics: pcp::Diagnostics,
        ) -> Stage {
            let store = self.registry.store();
            let layers = layers
                .into_iter()
                .map(|layer| sdf::layer_registry::tests::hold(&store, layer))
                .collect();
            self.assemble(layers, session_layer_count, collection_diagnostics, Vec::new())
        }
    }

    /// The numbers of [`StageSink`]s and transaction observers installed on
    /// `stage`, for tests asserting a wrapper's recorders are installed and
    /// later removed.
    pub(crate) fn recorder_counts(stage: &Stage) -> (usize, usize) {
        (
            stage.sinks.borrow().iter().count(),
            stage.observers.borrow().iter().count(),
        )
    }

    /// A stage over `files`, each a path relative to a fresh directory and its
    /// contents, opened at `root.usda` against the test schema family. A
    /// `.usda` file's contents are written after the `#usda` header.
    pub(crate) fn scene(files: &[(&str, &str)]) -> Result<(tempfile::TempDir, Stage)> {
        let dir = tempfile::tempdir()?;
        for (name, contents) in files {
            let path = dir.path().join(name);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)?;
            }
            match path.extension().is_some_and(|ext| ext == "usda") {
                true => fs::write(&path, format!("#usda 1.0\n{contents}\n"))?,
                false => fs::write(&path, contents)?,
            }
        }
        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::test_registry())
            .open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        Ok((dir, stage))
    }

    pub(crate) fn stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    /// A stage whose `/Child` references `</R>` in `ref.usda`, with the edit
    /// target set to that arc: `root` is authored before `/Child` in the root
    /// layer, `referenced` inside `/R`. Hands back `/Child` and the target.
    pub(crate) fn reference_scene(
        root: &str,
        referenced: &str,
    ) -> Result<(tempfile::TempDir, Stage, usd::Prim, usd::EditTarget)> {
        let root = format!("{root}def \"Child\" (\n    references = @ref.usda@</R>\n)\n{{\n}}");
        let referenced = format!("def \"R\"\n{{\n{referenced}}}");
        let (dir, stage) = scene(&[("root.usda", root.as_str()), ("ref.usda", referenced.as_str())])?;
        let child = stage.prim("/Child")?;
        let target = child.edit_target_for_arc(usd::EditTargetArc::Reference)?;
        stage.set_edit_target(target.clone())?;
        Ok((dir, stage, child, target))
    }

    /// The field `key` as `layer` authors it at `path`, read as `T`.
    pub(crate) fn authored<T: TryFrom<vt::Value>>(layer: &sdf::Layer, path: &str, key: sdf::FieldKey) -> Option<T> {
        let value = layer
            .data()
            .try_field(&sdf::Path::new(path).ok()?, key.as_str())
            .ok()??;
        T::try_from(value.into_owned()).ok()
    }

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

    /// The value of the attribute at `path` at time 0, or `None` when it has
    /// none.
    pub(crate) fn attribute_value(stage: &Stage, path: &str) -> Option<vt::Value> {
        stage.attribute(path).unwrap().get_at(usd::TimeCode::new(0.0)).unwrap()
    }

    const VENDOR_COMPOSITION: &str = concat!(
        env!("CARGO_WORKSPACE_DIR"),
        "vendor/usd-wg-assets/test_assets/foundation/stage_composition"
    );

    fn composition_path(relative: &str) -> String {
        format!("{VENDOR_COMPOSITION}/{relative}")
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
            .layer_handle(&mid1)
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
        let x_at_m1 = |stage: &Stage| -> Result<Option<vt::Value>> {
            stage
                .attribute("/M1.x")?
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))
        };
        assert_eq!(x_at_m1(&stage)?, Some(vt::Value::Double(1.0)), "V=a selects a.usda");

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

        stage.attribute("/M1.x")?.set(vt::Value::Double(7.0))?;
        assert_eq!(
            stage
                .attribute("/M1.x")?
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(vt::Value::Double(7.0)),
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
            .layer_handle(&mid)
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
            .layer_handle(&root_id)
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

        let active = stage.field::<vt::Value>("/World", sdf::FieldKey::Active)?;
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
            .edit_connections()
            .set([target.clone()])
            .unwrap();
        });

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, pcp::Diagnostics::default());
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
        assert_eq!(op.deleted_items(), vec![target]);
        Ok(())
    }

    /// A target a weaker layer holds is prepended on the edit target as
    /// well; composition lists it once.
    #[test]
    fn add_connection_inherited() -> Result<()> {
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
            .edit_connections()
            .set([target.clone()])
            .unwrap();
        });

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, pcp::Diagnostics::default());
        let attr = crate::usd::Attribute::new(&stage, input.clone());
        let attr = attr.add_connection(target.clone())?;

        assert_eq!(attr.connections()?, vec![target.clone()]);
        let op = stage
            .root_layer()
            .attribute(input)?
            .expect("authored on the root layer")
            .connection_path_list()
            .expect("connections");
        assert_eq!(op.prepended_items(), vec![target]);
        Ok(())
    }

    /// A target re-added on the layer that deletes it composes again, the
    /// delete left as it is (C++ `Usd_InsertListItem`).
    #[test]
    fn add_connection_after_delete() -> Result<()> {
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
            .edit_connections()
            .set([target.clone()])
            .unwrap();
        });

        let stage = Stage::builder().make_stage(vec![strong, weak], 0, pcp::Diagnostics::default());
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
        assert_eq!(op.deleted_items(), vec![target.clone()]);
        assert_eq!(op.prepended_items(), vec![target]);
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
            let layers = stage.layer_view();
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
            let layers = stage.layer_view();
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
                .set_default(vt::Value::Double(value))
                .expect("value fits the declared type");
        });
        Ok(layer)
    }

    /// The parent layer's authored `subLayers` asset paths.
    fn authored_sublayers(stage: &Stage) -> Vec<String> {
        let root = stage.root_layer();
        root.pseudo_root().and_then(|pr| pr.sublayers()).unwrap_or_default()
    }

    /// Re-inserting a layer whose identifier the stage already holds is refused
    /// with [`sdf::LayerError::Duplicate`], as C++ refuses a new layer under an
    /// open identifier, and the loaded node keeps its data and its derived
    /// sublayer children. Anonymous layers are unique, so the colliding
    /// identifier is fabricated with [`sdf::Layer::new_in_memory`].
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
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(vt::Value::Double(5.0))
        );

        // Re-insert `mid` by its identifier, passing a fresh empty layer with the
        // same identifier. The loaded `mid` (whose `subLayers` still names
        // `leaf`) stays, so `leaf`'s opinion survives.
        let reinserted = stage.insert_layer(
            &root_id,
            0,
            sdf::Layer::new_in_memory(&mid_id),
            sdf::LayerOffset::IDENTITY,
        );
        assert!(
            matches!(
                reinserted,
                Err(StageAuthoringError::Registry(sdf::LayerError::Duplicate { .. }))
            ),
            "{reinserted:?}"
        );
        assert_eq!(
            stage
                .attribute("/A.x")?
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(vt::Value::Double(5.0)),
            "the already-loaded mid layer's child edge to leaf must survive re-insertion"
        );
        Ok(())
    }

    /// A local edit target keys a sample at the time its sublayer's offset
    /// composes to the stage time asked for, and a layer outside the root
    /// layer stack has none.
    #[test]
    fn local_layer_target_offset() -> Result<()> {
        let stage = Stage::builder().in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        let sub = opinion_layer("sub.usda", 1.0)?;
        let sub_id = sub.identifier().to_string();
        stage.insert_layer(&root_id, 0, sub, sdf::LayerOffset::new(10.0, 2.0))?;

        let target = stage.edit_target_for_local_layer(&sub_id).expect("sub is local");
        assert_eq!(target.layer_identifier(), sub_id);
        assert_eq!(target.map_to_spec_time(30.0), 10.0);
        stage.set_edit_target(target)?;
        stage.attribute("/A.x")?.set_at(2.0, usd::TimeCode::new(30.0))?;
        let layer = stage.layer(&sub_id).expect("sub is loaded");
        let samples = layer.attribute("/A.x")?.expect("spec").time_samples();
        assert_eq!(samples, Some(vec![(10.0, vt::Value::Double(2.0))]));
        drop(layer);
        assert_eq!(
            stage.attribute("/A.x")?.get_at::<f64>(usd::TimeCode::new(30.0))?,
            Some(2.0)
        );

        let root_target = stage.edit_target_for_local_layer(&root_id).expect("root is local");
        assert_eq!(root_target.map_to_spec_time(30.0), 30.0);
        assert!(stage.edit_target_for_local_layer("elsewhere.usda").is_none());
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
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(vt::Value::Double(5.0)),
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
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
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
            .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?;
        // `/Q` reaches the same target carrying `V=chosen`; the target's `${V}`
        // sublayer must resolve and contribute `chosen.usda`'s opinion.
        assert_eq!(
            stage
                .attribute("/Q.x")?
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(vt::Value::Double(42.0)),
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
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(vt::Value::Double(42.0)),
            "the variable-carrying arc resolves the `${{V}}` sublayer",
        );
        // `/P` reaches the same target with no variable. Its `${V}` sublayer cannot
        // resolve, so `/P.x` stays absent — not polluted by `/Q`'s context.
        assert_eq!(
            stage
                .attribute("/P.x")?
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
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
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("sub.usda", 5.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        assert_eq!(
            stage
                .attribute("/A.x")?
                .get_at::<vt::Value>(crate::usd::TimeCode::new(0.0))?,
            Some(vt::Value::Double(5.0)),
            "the dot-relative sublayer composes its opinion"
        );
        Ok(())
    }

    /// Reads the composed `/A.x` default value as an `f64`, for the muting tests.
    fn read_ax(stage: &Stage) -> Result<Option<f64>> {
        stage.attribute("/A.x")?.get_at::<f64>(crate::usd::TimeCode::new(0.0))
    }

    /// A root layer sublayering each `(identifier, value)` opinion in strength
    /// order, followed by the opinion sublayers — the layer list for `MakeStage::make_stage`
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
            pcp::Diagnostics::default(),
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

    /// An attribute query on the pseudo-root leaves no empty path in the index
    /// cache, so a later mute and unmute do not panic dropping it.
    #[test]
    fn mute_after_root_query() -> Result<()> {
        let stage = Stage::builder().make_stage(
            sublayer_layers(&[("strong.usda", 9.0), ("weak.usda", 5.0)])?,
            0,
            pcp::Diagnostics::default(),
        );
        for name in ["purpose", "visibility"] {
            assert!(stage.prim("/")?.attribute(name).get::<vt::Value>()?.is_none());
        }

        stage.mute_layer("strong.usda");
        assert_eq!(read_ax(&stage)?, Some(5.0));
        stage.unmute_layer("strong.usda");
        assert_eq!(read_ax(&stage)?, Some(9.0));
        Ok(())
    }

    /// An explicit identity payload offset matches an omitted one, as in C++,
    /// so deleting `@content.usda@</Box> (offset = 0; scale = 1)` removes the
    /// payload a weaker layer added without an offset.
    #[test]
    fn payload_identity_offset() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write("content.usda", "#usda 1.0\ndef \"Box\" {\n    def \"Child\" {}\n}\n")?;
        write(
            "weak.usda",
            "#usda 1.0\ndef \"Root\" (\n    prepend payload = @content.usda@</Box>\n) {}\n",
        )?;
        write(
            "root.usda",
            "#usda 1.0\n(\n    subLayers = [@weak.usda@]\n)\nover \"Root\" (\n    delete payload = @content.usda@</Box> (offset = 0; scale = 1)\n) {}\n",
        )?;
        let stage = Stage::open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;

        assert!(stage.prim("/Root")?.is_defined()?);
        assert!(
            !stage.prim("/Root/Child")?.is_valid()?,
            "the deleted payload contributes nothing"
        );
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
        let stage = Stage::builder().make_stage(vec![session, root], 1, pcp::Diagnostics::default());
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
        let stage = Stage::builder().make_stage(vec![session, subsession, root], 2, pcp::Diagnostics::default());
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
                vt::Value::String("strong".into()),
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
            pcp::Diagnostics::default(),
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
                vt::Value::String("strong".into()),
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
            pcp::Diagnostics::default(),
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
            pr.set_expression_variables(HashMap::from([("V".to_string(), vt::Value::String("strong".into()))]));
            pr.set_sublayers([r#"`"${V}.usda"`"#, "weak.usda"]);
        });
        let mut strong = sdf::Layer::new_in_memory("strong.usda");
        edit_layer(&mut strong, |e| {
            sdf::AttributeSpec::new(e.data_mut(), "/A/Child.y", "double", sdf::Variability::Varying, true)
                .unwrap()
                .set_default(vt::Value::Double(5.0))
                .expect("value fits the declared type");
        });
        let stage = Stage::builder().make_stage(
            vec![root, strong, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
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
        let stage = Stage::builder().make_stage(vec![session, root], 1, pcp::Diagnostics::default());
        assert_eq!(read_ax(&stage)?, Some(7.0));

        stage.mute_layer("session.usda");
        assert_eq!(read_ax(&stage)?, None, "the muted session layer contributes nothing");
        Ok(())
    }

    /// Muting the root layer is rejected: it stays unmuted and composition is
    /// unchanged.
    #[test]
    fn mute_root_rejected() -> Result<()> {
        let stage = Stage::builder().make_stage(vec![opinion_layer("root.usda", 3.0)?], 0, pcp::Diagnostics::default());
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
        let stage = Stage::builder().make_stage(
            vec![root, mid, opinion_layer("leaf.usda", 5.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        assert_eq!(read_ax(&stage)?, Some(5.0));

        stage.mute_layer("mid.usda");
        assert_eq!(read_ax(&stage)?, None, "the muted layer's whole subtree is pruned");

        stage.unmute_layer("mid.usda");
        assert_eq!(read_ax(&stage)?, Some(5.0));
        Ok(())
    }

    /// A prim's schema identity is composed, so a structural edit can move it
    /// without authoring a type field anywhere: adding a reference brings the
    /// target's `typeName` in. The memo of identities must not answer from
    /// before the arc existed.
    #[test]
    fn type_memo_follows_reference() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/Source")?.set_type_name("Xform")?;
        let prim = stage.define_prim("/A")?;
        assert_eq!(
            stage.prim_type_info_composed("/A")?.id().type_name().as_str(),
            "",
            "/A authors no type of its own"
        );

        prim.set_metadata(
            sdf::FieldKey::References.as_str(),
            vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                prim_path: sdf::path("/Source")?,
                ..Default::default()
            }])),
        )?;

        assert_eq!(
            stage.prim_type_info_composed("/A")?.id().type_name().as_str(),
            "Xform",
            "the reference brought a type in, and no type field was authored on /A"
        );
        Ok(())
    }

    /// Authoring `typeName` restales the memo through its own channel: the edit
    /// restructures nothing, so no index is dropped and no population epoch
    /// moves.
    #[test]
    fn type_memo_follows_edit() -> Result<()> {
        let stage = in_memory_stage()?;
        let prim = stage.define_prim("/A")?.set_type_name("Scope")?;
        assert_eq!(stage.prim_type_info_composed("/A")?.id().type_name().as_str(), "Scope");

        prim.set_type_name("Xform")?;

        assert_eq!(stage.prim_type_info_composed("/A")?.id().type_name().as_str(), "Xform");
        Ok(())
    }

    /// Muting drops the indices that read the muted layer, so an
    /// [`AttributeQuery`] built before the mute returns the new composed value
    /// afterward: its stamp names a prim whose entry is gone.
    #[test]
    fn mute_retires_query() -> Result<()> {
        let stage = Stage::builder().make_stage(
            sublayer_layers(&[("strong.usda", 9.0), ("weak.usda", 5.0)])?,
            0,
            pcp::Diagnostics::default(),
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
        let stage = Stage::builder().make_stage(vec![opinion_layer("root.usda", 3.0)?], 0, pcp::Diagnostics::default());
        stage.mute_layer("nonexistent.usda");
        assert!(stage.is_layer_muted("nonexistent.usda"));
        assert_eq!(read_ax(&stage)?, Some(3.0), "an unmatched mute changes nothing");
        Ok(())
    }

    /// `mute_layer` / `unmute_layer` are reflected by `is_layer_muted` and
    /// `muted_layers`.
    #[test]
    fn muted_layers_roundtrip() -> Result<()> {
        let stage = Stage::builder().make_stage(
            sublayer_layers(&[("a.usda", 1.0), ("b.usda", 2.0)])?,
            0,
            pcp::Diagnostics::default(),
        );
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
                .set_default(vt::Value::Double(5.0))
                .expect("value fits the declared type");
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

    /// An absolute `subLayers` entry on an anonymous layer names a file
    /// without an anchor, so the load barrier opens it from disk (C++
    /// `SdfComputeAssetPathRelativeToLayer` resolves it unanchored): through
    /// `insert_layer`, and authored on the in-memory stage's anonymous root.
    #[test]
    fn anon_absolute_sublayer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let sub_path = dir.path().join("sub.usda");
        fs::write(&sub_path, "#usda 1.0\ndef \"Sub\" {}\n")?;
        let sub = sub_path.to_str().expect("utf-8 path");

        let stage = Stage::builder().in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        let mut anon = sdf::Layer::new_anonymous("lop.usda");
        edit_layer(&mut anon, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([sub]);
        });
        stage.insert_layer(&root_id, 0, anon, sdf::LayerOffset::IDENTITY)?;
        assert!(stage.prim("/Sub")?.is_defined()?, "the inserted layer's sublayer loads");
        assert!(stage.composition_errors().is_empty());

        let stage = Stage::builder().in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root_id, |e| {
            e.pseudo_root_mut()?.set_sublayers([sub]);
            Ok(())
        })?;
        assert!(stage.prim("/Sub")?.is_defined()?, "the root's authored sublayer loads");
        assert!(stage.composition_errors().is_empty());
        Ok(())
    }

    /// An anonymous layer's tag does not anchor the paths it authors. Under a
    /// tag ending in `.usdz`, a search-path entry still resolves through the
    /// resolver's search directories (C++ `SdfComputeAssetPathRelativeToLayer`
    /// creates an anonymous layer's identifiers without an anchor).
    #[test]
    fn anon_search_sublayer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("sub.usda"),
            "#usda 1.0
def \"Sub\" {}
",
        )?;
        let stage = Stage::builder()
            .resolver(ar::DefaultResolver::with_search_paths([dir.path()]))
            .in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        let mut anon = sdf::Layer::new_anonymous("lop.usdz");
        edit_layer(&mut anon, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["sub.usda"]);
        });
        stage.insert_layer(&root_id, 0, anon, sdf::LayerOffset::IDENTITY)?;
        assert!(stage.prim("/Sub")?.is_defined()?, "the search-path sublayer loads");
        assert!(stage.composition_errors().is_empty());
        Ok(())
    }

    /// A reference that reaches a loaded layer under a second spelling of its
    /// file composes on the first read.
    #[test]
    fn reference_second_spelling() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("lib.usda"),
            "#usda 1.0\ndef \"S\" {\n    def \"Child\" {}\n}\n",
        )?;
        let absolute = dir.path().join("lib.usda").canonicalize()?;
        let absolute = absolute.to_str().expect("utf-8 path").to_owned();
        let stage = Stage::builder()
            .resolver(ar::DefaultResolver::with_search_paths([dir.path()]))
            .in_memory("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root, |e| {
            for (prim, asset_path) in [("/A", absolute.as_str()), ("/B", "lib.usda")] {
                sdf::PrimSpec::new(e.data_mut(), prim, sdf::Specifier::Def, "")?;
                e.data_mut().set_field(
                    &sdf::path(prim)?,
                    sdf::FieldKey::References.as_str(),
                    vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
                        asset_path: asset_path.into(),
                        prim_path: sdf::path("/S")?,
                        ..Default::default()
                    }])),
                );
            }
            Ok(())
        })?;
        assert!(stage.prim("/A/Child")?.is_valid()?);
        assert!(
            stage.prim("/B/Child")?.is_valid()?,
            "the second spelling composes at once"
        );
        Ok(())
    }

    /// Two spellings of one file, a search-path one and its absolute path,
    /// name one layer, whichever the stage reaches first.
    #[test]
    fn two_spellings_one_layer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(dir.path().join("sub.usda"), "#usda 1.0\ndef \"Sub\" {}\n")?;
        let absolute = dir.path().join("sub.usda").canonicalize()?;
        let absolute = absolute.to_str().expect("utf-8 path").to_owned();
        for (first, second) in [("sub.usda", absolute.as_str()), (absolute.as_str(), "sub.usda")] {
            let stage = Stage::builder()
                .resolver(ar::DefaultResolver::with_search_paths([dir.path()]))
                .in_memory("root.usda")?;
            let root_id = stage.root_layer().identifier().to_string();
            stage.edit_layer(&root_id, |e| {
                e.pseudo_root_mut()?.set_sublayers([first]);
                Ok(())
            })?;
            assert!(stage.prim("/Sub")?.is_defined()?);
            let mut other = sdf::Layer::new_in_memory("other.usda");
            edit_layer(&mut other, |e| {
                e.pseudo_root_mut().unwrap().set_sublayers([second]);
            });
            stage.insert_layer(&root_id, 1, other, sdf::LayerOffset::IDENTITY)?;
            assert!(
                stage.composition_errors().is_empty(),
                "{:?}",
                stage.composition_errors()
            );
            assert_eq!(stage.layer_count(), 3, "the root, other.usda and one sub.usda");
            let other = stage.layers().id_of("other.usda").expect("other.usda is in the graph");
            assert_eq!(
                stage.layers().sublayer_stack(other).len(),
                2,
                "{second} reaches the sub.usda {first} loaded"
            );
        }
        Ok(())
    }

    /// The identifier of the stage's layer whose identifier ends with `name`.
    fn layer_named(stage: &Stage, name: &str) -> String {
        // The identifier canonicalizes the path, which may spell it another way
        // (a `\\?\` prefix on Windows).
        stage
            .layer_identifiers()
            .into_iter()
            .find(|identifier| identifier.ends_with(name))
            .expect("the layer is loaded")
    }

    /// A root layer whose `/P` has a payload on `payload.usda`, which holds
    /// `/M` with `double x = 0` and a child `/M/C`, both written to `dir`, and
    /// the root's and the payload's paths.
    fn payload_fixture(dir: &FsPath) -> Result<(String, String)> {
        fs::write(
            dir.join("root.usda"),
            "#usda 1.0\ndef \"P\" (payload = @./payload.usda@</M>) {}\n",
        )?;
        fs::write(
            dir.join("payload.usda"),
            "#usda 1.0\ndef \"M\" {\n    double x = 0\n    def \"C\" {}\n}\n",
        )?;
        let path = |name: &str| dir.join(name).to_str().expect("utf-8 path").to_owned();
        Ok((path("root.usda"), path("payload.usda")))
    }

    /// Unloading a payload drops its layer from the stage, and the registry
    /// frees it when nothing else holds it.
    #[test]
    fn unload_frees_layer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, payload) = payload_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let stage = Stage::builder().registry(registry.clone()).open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        assert_eq!(stage.layer_count(), 2);
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 1, "the payload layer left the stage");
        assert!(registry.find(&payload)?.is_none(), "and the registry");
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P/C")?.is_valid()?, "loading it again reads it again");
        Ok(())
    }

    /// A handle to an unloaded payload's layer keeps it in the registry, edits
    /// included, though the stage drops it.
    #[test]
    fn unload_kept_by_handle() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, payload) = payload_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let stage = Stage::builder().registry(registry.clone()).open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        let held = registry.find(&payload)?.expect("the stage holds the payload");
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 1);
        assert!(registry.find(&payload)?.is_some(), "the handle keeps it");
        drop(held);
        registry.sweep();
        assert!(registry.find(&payload)?.is_none());
        Ok(())
    }

    /// A payload layer with unsaved edits stays through an unload, so loading
    /// it again finds the edits.
    #[test]
    fn unload_keeps_dirty() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        let identifier = layer_named(&stage, "payload.usda");
        stage.edit_layer(&identifier, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M/Unsaved", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 2, "the dirty layer stays");
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P/Unsaved")?.is_valid()?);
        Ok(())
    }

    /// A payload layer leaving the stage drops the undo history touching it,
    /// and history touching only other layers stays.
    #[test]
    fn unload_departs_undo() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = usd::UndoStage::from(Stage::open(&root)?);
        assert!(stage.prim("/P/C")?.is_valid()?);
        let identifier = layer_named(&stage, "payload.usda");
        stage.edit_layer(&identifier, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M/Saved", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.layer_handle(&identifier).expect("loaded").save()?;
        stage.define_prim("/Newer")?;
        assert_eq!(stage.undo_depth(), 2);
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 1);
        assert_eq!(
            stage.undo_depth(),
            1,
            "the step on the departed layer went with the older ones"
        );
        assert!(stage.undo()?);
        assert!(!stage.prim("/Newer")?.is_valid()?);
        Ok(())
    }

    /// An anonymous payload layer has no file to read back, so an unload keeps
    /// it and loading the payload again finds its content.
    #[test]
    fn unload_keeps_anonymous() -> Result<()> {
        let registry = sdf::LayerRegistry::default();
        let mut payload = sdf::Layer::new_anonymous("payload.usda");
        edit_layer(&mut payload, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M", sdf::Specifier::Def, "").unwrap();
            sdf::PrimSpec::new(e.data_mut(), "/M/C", sdf::Specifier::Def, "").unwrap();
        });
        let identifier = payload.identifier().to_owned();
        let held = registry.adopt(payload).map_err(|refused| refused.error)?;
        let stage = Stage::builder().registry(registry).in_memory("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/P", sdf::Specifier::Def, "")?;
            e.data_mut().set_field(
                &sdf::path("/P")?,
                sdf::FieldKey::Payload.as_str(),
                vt::Value::PayloadListOp(sdf::PayloadListOp::prepended([sdf::Payload {
                    asset_path: identifier.clone(),
                    prim_path: sdf::path("/M")?,
                    ..Default::default()
                }])),
            );
            Ok(())
        })?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        drop(held);
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 2, "the anonymous layer stays");
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        Ok(())
    }

    /// A payload layer whose stack an edit's sweep already removed leaves at
    /// the next load-rules change.
    #[test]
    fn unload_frees_orphan() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = Stage::builder().load(InitialLoadSet::LoadNone).open(&root)?;
        assert_eq!(stage.find_loadable("/")?, [sdf::path("/P")?]);
        assert_eq!(stage.layer_count(), 2, "finding the payload read its layer");
        stage.define_prim("/Other")?;
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 1);
        Ok(())
    }

    /// A payload whose prims read value clips leaves with its clip sets.
    #[test]
    fn unload_frees_clipped() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("root.usda"),
            "#usda 1.0\ndef \"P\" (payload = @./payload.usda@</M>) {}\n",
        )?;
        fs::write(
            dir.path().join("payload.usda"),
            r#"#usda 1.0
def "M" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            string primPath = "/M"
            double2[] active = [(0, 0)]
        }
    }
)
{
    double x
}
"#,
        )?;
        fs::write(
            dir.path().join("clip.usda"),
            "#usda 1.0\ndef \"M\" {\n    double x.timeSamples = {\n        0: 5,\n    }\n}\n",
        )?;
        let stage = Stage::open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        assert_eq!(
            stage.attribute("/P.x")?.get_at::<f64>(usd::TimeCode::new(0.0))?,
            Some(5.0)
        );
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 1, "the clipped payload leaves");
        assert!(
            !stage.composition.settled_cache().has_clip_sources(),
            "and retracts the clip sources it registered"
        );
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert_eq!(
            stage.attribute("/P.x")?.get_at::<f64>(usd::TimeCode::new(0.0))?,
            Some(5.0)
        );
        Ok(())
    }

    /// An unload made while a handle edit holds the registry's layers frees
    /// nothing then, and the next load-rules change frees the layer.
    #[test]
    fn unload_inside_edit() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        let identifier = stage.root_layer().identifier().to_string();
        let handle = stage.layer_handle(&identifier).expect("the root layer");
        handle.edit(|_| {
            stage.unload("/P").expect("a valid path");
            Ok(())
        })?;
        assert_eq!(stage.layer_count(), 2, "the busy registry freed nothing");
        stage.load("/Nothing", LoadPolicy::WithDescendants)?;
        assert_eq!(stage.layer_count(), 1);
        Ok(())
    }

    /// A payload layer whose every relocate is invalid takes its relocate
    /// error with it when it leaves.
    #[test]
    fn unload_drops_relocate_error() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("root.usda"),
            "#usda 1.0\ndef \"P\" (payload = @./payload.usda@</M>) {}\n",
        )?;
        fs::write(
            dir.path().join("payload.usda"),
            "#usda 1.0\n(\n    relocates = { </M/C/D>: </M> }\n)\ndef \"M\" {\n    def \"C\" {}\n}\n",
        )?;
        let stage = Stage::open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        let relocate_errors = |stage: &Stage| {
            stage
                .composition_errors()
                .iter()
                .filter(|error| matches!(error, pcp::CompositionDiagnostic::InvalidRelocate { .. }))
                .count()
        };
        assert!(stage.prim("/P/C")?.is_valid()?);
        assert_eq!(relocate_errors(&stage), 1, "the loaded payload reports its relocate");
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 1);
        assert_eq!(relocate_errors(&stage), 0, "the error left with its layer");
        Ok(())
    }

    /// The layer an open edit context will restore as the edit target stays
    /// through an unload, so authoring after the context ends still reaches it.
    #[test]
    fn unload_keeps_saved_target() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        let payload = layer_named(&stage, "payload.usda");
        let root_layer = stage.root_layer().identifier().to_string();
        stage.set_edit_target(EditTarget::for_layer(payload.clone()))?;
        {
            let _context = stage.edit_context(EditTarget::for_layer(root_layer))?;
            stage.unload("/P")?;
            assert_eq!(stage.layer_count(), 2, "the target the context restores stays");
        }
        stage.edit_layer(&payload, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M/After", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        Ok(())
    }

    /// A payload layer an unload kept for its unsaved edits leaves at the next
    /// load-rules change once it is saved.
    #[test]
    fn saved_layer_leaves_later() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        let payload = layer_named(&stage, "payload.usda");
        stage.edit_layer(&payload, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M/Unsaved", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 2, "the dirty layer stays");
        stage.layer_handle(&payload).expect("held").save()?;
        stage.load("/Nothing", LoadPolicy::WithDescendants)?;
        assert_eq!(stage.layer_count(), 1, "saved, it leaves");
        Ok(())
    }

    /// A sink that unloads as an edit context switches the target cannot free
    /// the layer the context will restore.
    #[test]
    fn context_switch_unload() -> Result<()> {
        struct Unloads;
        impl StageSink for Unloads {
            fn edit_target_changed(&self, stage: &Stage) {
                stage.unload("/P").expect("a valid path");
            }
        }

        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        let payload = layer_named(&stage, "payload.usda");
        let root_layer = stage.root_layer().identifier().to_string();
        stage.set_edit_target(EditTarget::for_layer(payload.clone()))?;
        let sink = stage.add_sink(Unloads);
        {
            let _context = stage.edit_context(EditTarget::for_layer(root_layer))?;
            assert_eq!(stage.layer_count(), 2, "the target the context restores stays");
        }
        stage.remove_sink(sink);
        stage.edit_layer(&payload, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M/After", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        Ok(())
    }

    /// A layer read first as a value clip, then loaded as a payload layer and
    /// edited, gives its clip readers the edit, and stays once the payload
    /// unloads while a clip set names it.
    #[test]
    fn clip_payload_unload() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("root.usda"),
            r#"#usda 1.0
def "A" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            string primPath = "/M"
            double2[] active = [(0, 0)]
        }
    }
)
{
    double x
}
def "P" (payload = @./clip.usda@</M>) {}
"#,
        )?;
        fs::write(
            dir.path().join("clip.usda"),
            "#usda 1.0\ndef \"M\" {\n    double x.timeSamples = {\n        0: 5,\n    }\n}\n",
        )?;
        let stage = Stage::builder()
            .load(InitialLoadSet::LoadNone)
            .open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        assert_eq!(clip_x(&stage)?, Some(5.0));
        assert_eq!(stage.layer_count(), 2, "the clip layer joined the stage");
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P")?.is_valid()?);
        set_clip_x(&stage, 7.0)?;
        assert_eq!(clip_x(&stage)?, Some(7.0), "the clip reads the edit");
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 2, "the clip set keeps the layer");
        assert_eq!(clip_x(&stage)?, Some(7.0));
        Ok(())
    }

    /// A root layer whose `/A` reads `x` from the value clip at `clip`, and
    /// `clip.usda`, which samples 5 at time 0, both written to `dir`; returns
    /// the root's path.
    fn clip_fixture(dir: &FsPath, clip: &str) -> Result<String> {
        fs::write(
            dir.join("root.usda"),
            format!(
                "#usda 1.0\ndef \"A\" (\n    clips = {{\n        dictionary default = {{\n            \
                 asset[] assetPaths = [@./{clip}@]\n            string primPath = \"/M\"\n            \
                 double2[] active = [(0, 0)]\n        }}\n    }}\n)\n{{\n    double x\n}}\n"
            ),
        )?;
        fs::write(
            dir.join("clip.usda"),
            "#usda 1.0\ndef \"M\" {\n    double x.timeSamples = {\n        0: 5,\n    }\n}\n",
        )?;
        Ok(dir.join("root.usda").to_str().expect("utf-8 path").to_owned())
    }

    /// The value of `/A.x` at time 0.
    fn clip_x(stage: &Stage) -> Result<Option<f64>> {
        stage.attribute("/A.x")?.get_at::<f64>(usd::TimeCode::new(0.0))
    }

    /// Sets the clip layer `clip.usda` of `stage` to sample `value` for `/M.x`
    /// at time 0.
    fn set_clip_x(stage: &Stage, value: f64) -> Result<()> {
        stage.edit_layer(&layer_named(stage, "clip.usda"), |e| {
            e.data_mut().set_field(
                &sdf::path("/M.x")?,
                sdf::FieldKey::TimeSamples.as_str(),
                vt::Value::TimeSamples(vec![(0.0, vt::Value::Double(value))]),
            );
            Ok(())
        })?;
        Ok(())
    }

    /// An edit to a clip layer reaches the value it sources.
    #[test]
    fn clip_edit_reaches_value() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = Stage::open(&clip_fixture(dir.path(), "clip.usda")?)?;
        assert_eq!(clip_x(&stage)?, Some(5.0));
        set_clip_x(&stage, 7.0)?;
        assert_eq!(clip_x(&stage)?, Some(7.0));
        Ok(())
    }

    /// Stages on one registry read a clip layer once, and an edit to it
    /// through one reaches the other's clip value.
    #[test]
    fn shared_clip_one_read() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = clip_fixture(dir.path(), "clip.usda")?;
        let (registry, opens) = sdf::layer_registry::tests::counting_registry();
        let a = Stage::builder().registry(registry.clone()).open(&root)?;
        let b = Stage::builder().registry(registry).open(&root)?;
        assert_eq!(clip_x(&a)?, Some(5.0));
        assert_eq!(clip_x(&b)?, Some(5.0));
        assert_eq!(opens.get(), 2, "the root and the clip, each read once");
        set_clip_x(&b, 7.0)?;
        assert_eq!(clip_x(&a)?, Some(7.0), "the edit through the other stage");
        Ok(())
    }

    /// A layer read first as a clip and then referenced composes its
    /// sublayers into the reference.
    #[test]
    fn clip_then_reference() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = clip_fixture(dir.path(), "clip.usda")?;
        let mut text = fs::read_to_string(&root)?;
        text.push_str("def \"R\" (references = @./clip.usda@</M>) {}\n");
        fs::write(&root, text)?;
        fs::write(
            dir.path().join("clip.usda"),
            "#usda 1.0\n(\n    subLayers = [@./sub.usda@]\n)\ndef \"M\" {\n    double x.timeSamples = {\n        \
             0: 5,\n    }\n}\n",
        )?;
        fs::write(
            dir.path().join("sub.usda"),
            "#usda 1.0\nover \"M\" {\n    def \"Child\" {}\n}\n",
        )?;
        let stage = Stage::open(&root)?;
        assert_eq!(clip_x(&stage)?, Some(5.0), "read as a clip first");
        assert!(
            stage.prim("/R/Child")?.is_valid()?,
            "the reference reaches its sublayer"
        );
        Ok(())
    }

    /// A clip layer leaves the stage with the payload holding its clip set,
    /// and the next read once the payload loads opens it again.
    #[test]
    fn clip_reopens_after_unload() -> Result<()> {
        let dir = tempfile::tempdir()?;
        clip_fixture(dir.path(), "clip.usda")?;
        fs::rename(dir.path().join("root.usda"), dir.path().join("payload.usda"))?;
        let root = dir.path().join("root.usda");
        fs::write(&root, "#usda 1.0\ndef \"P\" (payload = @./payload.usda@</A>) {}\n")?;
        let stage = Stage::builder()
            .load(InitialLoadSet::LoadNone)
            .open(root.to_str().expect("utf-8 path"))?;
        let x = |stage: &Stage| stage.attribute("/P.x")?.get_at::<f64>(usd::TimeCode::new(0.0));
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert_eq!(x(&stage)?, Some(5.0));
        assert_eq!(stage.layer_count(), 3, "the root, the payload and the clip");
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 1, "the clip left with the payload");
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert_eq!(x(&stage)?, Some(5.0), "the clip is read again");
        assert_eq!(stage.layer_count(), 3);
        Ok(())
    }

    /// Opening a clip leaves the diagnostics of earlier reads standing.
    #[test]
    fn clip_read_keeps_errors() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = clip_fixture(dir.path(), "clip.usda")?;
        let mut text = fs::read_to_string(&root)?;
        text.push_str("def \"B\" {\n    asset t = @`if(`@\n}\n");
        fs::write(&root, text)?;
        let stage = Stage::open(&root)?;
        let _ = stage.attribute("/B.t")?.get::<sdf::AssetPath>();
        let before = stage.composition_errors().len();
        assert!(before > 0, "the malformed expression is reported");
        assert_eq!(clip_x(&stage)?, Some(5.0));
        assert_eq!(stage.composition_errors().len(), before);
        Ok(())
    }

    /// A clip layer's relocates are reported only while composition uses the
    /// layer: not while it serves a clip alone, then once a payload composes
    /// it, and no longer once the payload unloads and leaves it to the clip.
    #[test]
    fn clip_relocates_follow_composition() -> Result<()> {
        let invalid = |stage: &Stage| {
            stage
                .composition_errors()
                .iter()
                .any(|error| matches!(error, pcp::CompositionDiagnostic::InvalidRelocate { .. }))
        };
        let dir = tempfile::tempdir()?;
        let root = clip_fixture(dir.path(), "clip.usda")?;
        let mut text = fs::read_to_string(&root)?;
        text.push_str("def \"P\" (payload = @./clip.usda@</M>) {}\n");
        fs::write(&root, text)?;
        fs::write(
            dir.path().join("clip.usda"),
            "#usda 1.0\n(\n    relocates = { </M/C/D>: </M> }\n)\ndef \"M\" {\n    double x.timeSamples = {\n        \
             0: 5,\n    }\n}\n",
        )?;
        let stage = Stage::builder().load(InitialLoadSet::LoadNone).open(&root)?;
        assert_eq!(clip_x(&stage)?, Some(5.0));
        assert!(!invalid(&stage), "the clip alone reports nothing");
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P")?.is_valid()?);
        assert!(invalid(&stage), "composed, the layer's relocates are validated");
        stage.unload("/P")?;
        assert_eq!(stage.layer_count(), 2, "the clip keeps the layer");
        assert!(!invalid(&stage), "the clip alone reports nothing again");
        assert_eq!(clip_x(&stage)?, Some(5.0));
        Ok(())
    }

    /// A sublayer composition leaves while a clip reads it, under a parent
    /// that stays, composes its own sublayers again once composition reaches
    /// it: the parent's entry no longer names it until it rejoins.
    #[test]
    fn demoted_sublayer_rejoins() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = clip_fixture(dir.path(), "x.usda")?;
        let mut text = fs::read_to_string(&root)?;
        // `/Q` holds y.usda in composition, so only x.usda changes.
        text.push_str("def \"P\" (payload = @./r.usda@</M>) {}\ndef \"Q\" (references = @./y.usda@</M>) {}\n");
        fs::write(&root, text)?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "r.usda",
            "#usda 1.0\n(\n    subLayers = [@./x.usda@]\n)\ndef \"M\" {}\n",
        )?;
        write(
            "x.usda",
            "#usda 1.0\n(\n    subLayers = [@./y.usda@]\n)\ndef \"M\" {\n    double x.timeSamples = {\n        \
             0: 5,\n    }\n}\n",
        )?;
        write("y.usda", "#usda 1.0\nover \"M\" {\n    def \"Child\" {}\n}\n")?;
        let stage = Stage::builder().load(InitialLoadSet::LoadNone).open(&root)?;
        assert_eq!(clip_x(&stage)?, Some(5.0), "x.usda serves the clip alone");
        assert!(stage.prim("/Q/Child")?.is_valid()?);
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P/Child")?.is_valid()?, "x.usda composes its sublayer");
        // Unsaved edits keep r.usda once its payload unloads.
        stage.edit_layer(&layer_named(&stage, "r.usda"), |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M/Edited", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.unload("/P")?;
        assert_eq!(
            stage.layer_count(),
            4,
            "the root, r.usda, x.usda for the clip and y.usda"
        );
        assert_eq!(clip_x(&stage)?, Some(5.0));
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P/Edited")?.is_valid()?);
        assert!(
            stage.prim("/P/Child")?.is_valid()?,
            "x.usda composes its sublayer again"
        );
        Ok(())
    }

    /// A value read that must load a clip fails with
    /// [`sdf::LayerError::Busy`] from inside a read of the registry's layers,
    /// as an arc load does, and reads a clip already loaded there.
    #[test]
    fn clip_load_busy() -> Result<()> {
        let busy = |result: &Result<Option<f64>>| match result {
            Err(crate::Error::Query(error)) => error.is_busy(),
            _ => false,
        };
        let dir = tempfile::tempdir()?;
        let stage = Stage::open(&clip_fixture(dir.path(), "clip.usda")?)?;
        let root = stage
            .layer_handle(stage.root_layer().identifier())
            .expect("the stage holds its root");
        let unloaded = root.read(|_| clip_x(&stage))?;
        assert!(busy(&unloaded), "{unloaded:?}");
        assert_eq!(clip_x(&stage)?, Some(5.0), "outside the read, the clip loads");
        assert_eq!(root.read(|_| clip_x(&stage))??, Some(5.0), "a loaded clip reads");
        Ok(())
    }

    /// A clip that cannot be read fails the value read of a set with an
    /// authored manifest, with the load error as its source.
    #[test]
    fn clip_load_keeps_source() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = clip_fixture(dir.path(), "clip.usda")?;
        let text = fs::read_to_string(&root)?.replace(
            "string primPath",
            "asset manifestAssetPath = @./manifest.usda@\n            string primPath",
        );
        fs::write(&root, text)?;
        fs::write(
            dir.path().join("manifest.usda"),
            "#usda 1.0\nover \"M\" {\n    double x\n}\n",
        )?;
        fs::write(dir.path().join("clip.usda"), "#usda 1.0\ndef \"M\" {\n")?;
        let stage = Stage::open(&root)?;
        let Err(crate::Error::Query(pcp::QueryError::ClipLoad(load))) = clip_x(&stage) else {
            panic!("an unreadable clip fails the read");
        };
        assert!(error::Error::source(&*load).is_some(), "the parse error is kept");
        assert!(clip_x(&stage).is_err(), "the failure is remembered");
        Ok(())
    }

    /// A gap filled by interpolating across clips opens the clips it reads,
    /// the nearest later one with a sample, and none beyond it.
    #[test]
    fn interpolate_opens_neighbour() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let write = |name: &str, text: &str| fs::write(dir.path().join(name), text);
        write(
            "root.usda",
            "#usda 1.0\ndef \"A\" (\n    clips = {\n        dictionary default = {\n            \
             asset[] assetPaths = [@./a.usda@, @./b.usda@, @./c.usda@]\n            \
             asset manifestAssetPath = @./manifest.usda@\n            string primPath = \"/M\"\n            \
             double2[] active = [(0, 0), (10, 1), (20, 2)]\n            \
             bool interpolateMissingClipValues = 1\n        }\n    }\n)\n{\n    double x\n}\n",
        )?;
        write("manifest.usda", "#usda 1.0\nover \"M\" {\n    double x\n}\n")?;
        write("a.usda", "#usda 1.0\ndef \"M\" {}\n")?;
        for (name, value) in [("b.usda", 7), ("c.usda", 9)] {
            write(
                name,
                &format!("#usda 1.0\ndef \"M\" {{\n    double x.timeSamples = {{\n        0: {value},\n    }}\n}}\n"),
            )?;
        }
        let stage = Stage::open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        assert_eq!(clip_x(&stage)?, Some(7.0), "the gap holds b.usda's sample");
        let opened = stage.layer_identifiers();
        assert!(
            !opened.iter().any(|identifier| identifier.ends_with("c.usda")),
            "{opened:?}"
        );
        Ok(())
    }

    /// A clip whose file appears after a read found it missing is read on
    /// the next read.
    #[test]
    fn clip_appears_later() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = clip_fixture(dir.path(), "late.usda")?;
        let stage = Stage::open(&root)?;
        assert_eq!(clip_x(&stage)?, None);
        fs::copy(dir.path().join("clip.usda"), dir.path().join("late.usda"))?;
        assert_eq!(clip_x(&stage)?, Some(5.0), "the clip is read once it resolves");
        Ok(())
    }

    /// A clip whose asset does not resolve sources nothing, and the read
    /// finds no value.
    #[test]
    fn missing_clip_no_value() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = Stage::open(&clip_fixture(dir.path(), "absent.usda")?)?;
        assert_eq!(clip_x(&stage)?, None);
        assert_eq!(clip_x(&stage)?, None, "the failure is remembered");
        assert_eq!(stage.layer_count(), 1);
        Ok(())
    }

    /// A departed layer's sinks drop once the stage's composition is free, so
    /// a sink whose drop queries the stage does not meet a borrowed stage.
    #[test]
    fn departed_sink_drops_free() -> Result<()> {
        struct Probe {
            stage: WeakStage,
            dropped: Rc<Cell<bool>>,
        }
        impl sdf::LayerSink for Probe {}
        impl Drop for Probe {
            fn drop(&mut self) {
                if let Some(stage) = self.stage.upgrade() {
                    let _ = stage.layer_count();
                }
                self.dropped.set(true);
            }
        }

        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("root.usda"),
            "#usda 1.0\ndef \"P\" (payload = @./payload.usda@</M>) {}\n",
        )?;
        fs::write(
            dir.path().join("payload.usda"),
            "#usda 1.0\n(\n    relocates = { </M/C>: </M/D> }\n)\ndef \"M\" {\n    def \"C\" {}\n}\n",
        )?;
        let stage = Stage::open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        assert!(stage.prim("/P")?.is_valid()?);
        let payload = layer_named(&stage, "payload.usda");
        let dropped = Rc::new(Cell::new(false));
        stage.layer_handle(&payload).expect("held").add_sink(Probe {
            stage: stage.downgrade(),
            dropped: Rc::clone(&dropped),
        })?;
        stage.unload("/P")?;
        assert!(dropped.get(), "the sink went with its layer");
        assert_eq!(stage.layer_count(), 1);
        Ok(())
    }

    /// Muting a layer frees it, and unmuting reads it again.
    #[test]
    fn mute_frees_layer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let stage = Stage::builder().registry(registry.clone()).open(&root)?;
        assert!(stage.prim("/Sub")?.is_valid()?);
        let weak = layer_named(&stage, "sub.usda");
        stage.mute_layer(weak.as_str());
        assert_eq!(stage.layer_count(), 1, "the muted layer left the stage");
        assert!(registry.find(&weak)?.is_none(), "and the registry");
        assert!(stage.is_layer_muted(&weak), "it stays muted");
        assert!(!stage.prim("/Sub")?.is_valid()?);
        stage.unmute_layer(&weak);
        assert!(stage.prim("/Sub")?.is_valid()?, "unmuted, it is read again");
        assert_eq!(stage.layer_count(), 2);
        Ok(())
    }

    /// A muted layer with unsaved edits stays, so unmuting it finds them.
    #[test]
    fn mute_keeps_dirty() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        let weak = layer_named(&stage, "sub.usda");
        stage.edit_layer(&weak, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Unsaved", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.mute_layer(weak.as_str());
        assert_eq!(stage.layer_count(), 2, "the dirty layer stays");
        stage.unmute_layer(&weak);
        assert!(stage.prim("/Unsaved")?.is_valid()?);
        Ok(())
    }

    /// A muted layer leaving the stage drops the undo history touching it.
    #[test]
    fn mute_departs_undo() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let stage = usd::UndoStage::from(Stage::open(&root)?);
        let weak = layer_named(&stage, "sub.usda");
        stage.edit_layer(&weak, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Saved", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.layer_handle(&weak).expect("loaded").save()?;
        assert!(stage.can_undo());
        stage.mute_layer(weak.as_str());
        assert_eq!(stage.layer_count(), 1);
        assert!(!stage.can_undo(), "the step on the muted layer went with it");
        stage.unmute_layer(&weak);
        assert!(stage.prim("/Saved")?.is_valid()?, "the saved edit reads back");
        Ok(())
    }

    /// A stage reload reads only the files that changed, and composes what
    /// they hold.
    #[test]
    fn stage_reload_reads_changed() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let (registry, opens) = sdf::layer_registry::tests::counting_registry();
        let stage = Stage::builder().registry(registry).open(&root)?;
        assert!(stage.prim("/Sub")?.is_valid()?);
        let read = opens.get();
        stage.reload()?;
        assert_eq!(opens.get(), read, "unchanged files are not read");
        sdf::layer::tests::rewrite(&dir.path().join("sub.usda"), "#usda 1.0\ndef \"New\" {}\n")?;
        stage.reload()?;
        assert_eq!(opens.get(), read + 1, "only the changed file is read");
        assert!(!stage.prim("/Sub")?.is_valid()?);
        assert!(stage.prim("/New")?.is_valid()?);
        Ok(())
    }

    /// Reloading a layer drops the undo steps touching it, and keeps the
    /// steps on other layers, older ones included.
    #[test]
    fn reload_departs_undo() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let stage = usd::UndoStage::from(Stage::open(&root)?);
        let root_id = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root_id, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/OnRoot", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        let sub = layer_named(&stage, "sub.usda");
        stage.edit_layer(&sub, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/OnSub", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        assert_eq!(stage.undo_depth(), 2);
        // The edit is saved, and the file changes elsewhere: the reload
        // touches nothing the step did, yet sets a new baseline for its layer.
        let handle = stage.layer_handle(&sub).expect("loaded");
        handle.save()?;
        sdf::layer::tests::append(&dir.path().join("sub.usda"), "def \"Elsewhere\" {}\n")?;
        assert!(handle.reload(false)?);
        assert!(stage.prim("/OnSub")?.is_valid()?, "the saved edit reads back");
        assert!(stage.prim("/Elsewhere")?.is_valid()?);
        assert_eq!(stage.undo_depth(), 1, "the step on the reloaded layer went");
        assert!(stage.undo()?);
        assert!(!stage.prim("/OnRoot")?.is_valid()?, "the older step on the root stays");
        Ok(())
    }

    /// A reload that finds a layer's content as it was keeps the undo
    /// history on it.
    #[test]
    fn reload_same_keeps_undo() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = usd::UndoStage::from(Stage::open(&shared_fixture(dir.path())?)?);
        let sub = layer_named(&stage, "sub.usda");
        stage.edit_layer(&sub, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/OnSub", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        let handle = stage.layer_handle(&sub).expect("loaded");
        handle.save()?;
        assert!(handle.reload(true)?, "a forced reload reads the file");
        assert_eq!(stage.undo_depth(), 1);
        Ok(())
    }

    /// A step that edited a reloaded layer and another one goes whole.
    #[test]
    fn reload_drops_whole_step() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = usd::UndoStage::from(Stage::open(&shared_fixture(dir.path())?)?);
        let root_id = stage.root_layer().identifier().to_string();
        let sub = layer_named(&stage, "sub.usda");
        stage.batch_edit(&[&root_id, &sub], |edits| {
            sdf::PrimSpec::new(edits[0].data_mut(), "/OnRoot", sdf::Specifier::Def, "")?;
            sdf::PrimSpec::new(edits[1].data_mut(), "/OnSub", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        assert_eq!(stage.undo_depth(), 1);
        let handle = stage.layer_handle(&sub).expect("loaded");
        assert!(handle.reload(false)?, "the unsaved edit is discarded");
        assert_eq!(stage.undo_depth(), 0);
        assert!(stage.prim("/OnRoot")?.is_valid()?, "the root's half stays authored");
        Ok(())
    }

    /// What a dropped step authored on another layer stays, so an older step
    /// whose undo would overwrite it goes too.
    #[test]
    fn reload_drops_overlapped() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = usd::UndoStage::from(Stage::open(&shared_fixture(dir.path())?)?);
        let root_id = stage.root_layer().identifier().to_string();
        let sub = layer_named(&stage, "sub.usda");
        stage.edit_layer(&root_id, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/P", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.batch_edit(&[&root_id, &sub], |edits| {
            sdf::PrimSpec::new(edits[0].data_mut(), "/P/C", sdf::Specifier::Def, "")?;
            sdf::PrimSpec::new(edits[1].data_mut(), "/OnSub", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        assert_eq!(stage.undo_depth(), 2);
        let handle = stage.layer_handle(&sub).expect("loaded");
        assert!(handle.reload(false)?);
        assert_eq!(stage.undo_depth(), 0, "undoing /P would take the kept /P/C with it");
        assert!(stage.prim("/P/C")?.is_valid()?);
        Ok(())
    }

    /// A reload drops the undo steps on the reloaded layer in every stage
    /// holding it, before a layer sink's callback on the reload can read the
    /// history.
    #[test]
    fn reload_departs_shared() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let a = Stage::builder().registry(registry.clone()).open(&root)?;
        let b = Rc::new(usd::UndoStage::from(Stage::builder().registry(registry).open(&root)?));
        let sub = layer_named(&b, "sub.usda");
        b.edit_layer(&sub, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/OnSub", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        assert_eq!(b.undo_depth(), 1);
        let handle = a.layer_handle(&sub).expect("A holds the sublayer");
        let seen = Rc::new(Cell::new(None));
        let (record, held) = (Rc::clone(&seen), Rc::clone(&b));
        handle.add_sink(move |_: &str, changes: &sdf::ChangeList| {
            if changes.did_reload_content() {
                record.set(Some(held.undo_depth()));
            }
        })?;
        a.reload()?;
        assert_eq!(seen.get(), Some(0), "the callback reads the dropped history");
        assert_eq!(b.undo_depth(), 0);
        Ok(())
    }

    /// A reload through a handle reaches every stage on the registry, which
    /// resyncs the prims it changed and leaves the rest, as C++ does.
    #[test]
    fn reload_reaches_stages() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let a = Stage::builder().registry(registry.clone()).open(&root)?;
        let b = Stage::builder().registry(registry).open(&root)?;
        assert!(b.prim("/A")?.is_valid()?);
        let resynced = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&resynced);
        b.add_sink(move |_: &Stage, change: &usd::CommittedChange<'_>| {
            sink.borrow_mut().extend(change.resynced.iter().cloned());
        });
        sdf::layer::tests::append(FsPath::new(&root), "def \"Added\" {}\n")?;
        let handle = a.layer_handle(a.root_layer().identifier()).expect("A holds its root");
        assert!(handle.reload(false)?);
        assert!(b.prim("/Added")?.is_valid()?, "the other stage reads the reload");
        let resynced = resynced.borrow();
        assert!(resynced.iter().any(|path| path.as_str() == "/Added"), "{resynced:?}");
        assert!(!resynced.iter().any(|path| path.as_str() == "/A"), "{resynced:?}");
        Ok(())
    }

    /// A changed package reloads: a layer inside one takes the package's
    /// modification time.
    #[test]
    fn reload_reads_package() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let package = dir.path().join("scene.usdz");
        let write = |text: &str| -> Result<()> {
            let mut writer = usdz::ArchiveWriter::create(&package)?;
            writer.add_layer("root.usda", text.as_bytes())?;
            writer.finish()?;
            Ok(())
        };
        write("#usda 1.0\ndef \"A\" {}\n")?;
        let stage = Stage::open(package.to_str().expect("utf-8 path"))?;
        assert!(stage.prim("/A")?.is_valid()?);
        write("#usda 1.0\ndef \"B\" {}\n")?;
        sdf::layer::tests::touch_later(&package)?;
        stage.reload()?;
        assert!(stage.prim("/B")?.is_valid()?);
        assert!(!stage.prim("/A")?.is_valid()?);
        Ok(())
    }

    /// A layer built in memory has no file to read again, so a stage reload
    /// leaves it as it is, though the registry gave it a resolver; an
    /// anonymous one is emptied, as C++ does.
    #[test]
    fn reload_keeps_in_memory() -> Result<()> {
        let stage = Stage::builder().open_layer(sdf::Layer::new_in_memory("root.usda"))?;
        stage.define_prim("/A")?;
        stage.reload()?;
        assert!(stage.prim("/A")?.is_valid()?);
        let anonymous = Stage::builder().in_memory("scratch.usda")?;
        anonymous.define_prim("/A")?;
        anonymous.reload()?;
        assert!(!anonymous.prim("/A")?.is_valid()?);
        Ok(())
    }

    /// A layer the stage keeps only for its unsaved edits after its payload
    /// unloads is not one the stage uses, so a stage reload leaves it, edits
    /// included.
    #[test]
    fn reload_keeps_unused() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        stage.edit_layer(&layer_named(&stage, "payload.usda"), |e| {
            sdf::PrimSpec::new(e.data_mut(), "/M/Edited", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.unload("/P")?;
        stage.reload()?;
        stage.load("/P", LoadPolicy::WithDescendants)?;
        assert!(stage.prim("/P/Edited")?.is_valid()?, "the unsaved edit survives");
        Ok(())
    }

    /// A reload of layers outside the root layer stack is a direct layer
    /// edit, and so is one reaching the root layer stack too, whose root
    /// layer paths are stage paths.
    #[test]
    fn reload_direct_provenance() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, payload) = payload_fixture(dir.path())?;
        let sub = dir.path().join("sub.usda");
        fs::write(&sub, "#usda 1.0\n")?;
        let text = fs::read_to_string(&payload)?.replace("#usda 1.0\n", "#usda 1.0\n(subLayers = [@./sub.usda@])\n");
        fs::write(&payload, text)?;
        let stage = Stage::open(&root)?;
        assert!(stage.prim("/P/C")?.is_valid()?);
        let seen = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&seen);
        stage.add_sink(move |_: &Stage, change: &usd::CommittedChange<'_>| {
            let direct = matches!(change.provenance, usd::Provenance::DirectLayerEdit);
            let added = change.resynced.iter().any(|path| path.as_str() == "/X");
            sink.borrow_mut().push((direct, added));
        });
        sdf::layer::tests::append(FsPath::new(&payload), "def \"Y\" {}\n")?;
        sdf::layer::tests::append(&sub, "def \"Z\" {}\n")?;
        stage.reload()?;
        assert_eq!(
            *seen.borrow(),
            [(true, false)],
            "one transaction, outside the root layer stack"
        );
        sdf::layer::tests::append(FsPath::new(&root), "def \"X\" {}\n")?;
        sdf::layer::tests::append(FsPath::new(&payload), "def \"W\" {}\n")?;
        stage.reload()?;
        assert_eq!(
            *seen.borrow(),
            [(true, false), (true, true)],
            "the root layer's prim resyncs"
        );
        Ok(())
    }

    /// A stage reload leaves the session layers as they are.
    #[test]
    fn stage_reload_keeps_session() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let session = dir.path().join("session.usda");
        fs::write(&session, "#usda 1.0\n")?;
        let stage = Stage::builder()
            .session_layer(session.to_str().expect("utf-8 path"))
            .open(&root)?;
        let session = layer_named(&stage, "session.usda");
        stage.edit_layer(&session, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Session", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        stage.reload()?;
        assert!(stage.prim("/Session")?.is_valid()?);
        Ok(())
    }

    /// A stage reload tries a sublayer that failed to load again, and tells
    /// the stage's sinks what the retry resynced.
    #[test]
    fn stage_reload_retries_sublayer() -> Result<()> {
        struct Retried(Rc<RefCell<Vec<Vec<sdf::Path>>>>);
        impl StageSink for Retried {
            fn loads_retried(&self, _: &Stage, resynced: &[sdf::Path]) {
                self.0.borrow_mut().push(resynced.to_vec());
            }
        }

        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        fs::remove_file(dir.path().join("sub.usda"))?;
        let stage = Stage::open(&root)?;
        assert!(!stage.prim("/Sub")?.is_valid()?);
        let retried = Rc::new(RefCell::new(Vec::new()));
        stage.add_sink(Retried(Rc::clone(&retried)));
        fs::write(dir.path().join("sub.usda"), "#usda 1.0\ndef \"Sub\" {}\n")?;
        stage.reload()?;
        assert!(
            stage.prim("/Sub")?.is_valid()?,
            "the sublayer loads once its file exists"
        );
        let retried = retried.borrow();
        assert_eq!(retried.len(), 1, "{retried:?}");
        assert!(!retried[0].is_empty());
        Ok(())
    }

    /// An edit other than a reload tries the failed loads again without
    /// reporting it.
    #[test]
    fn edit_retry_unreported() -> Result<()> {
        struct Retried(Rc<Cell<usize>>);
        impl StageSink for Retried {
            fn loads_retried(&self, _: &Stage, _: &[sdf::Path]) {
                self.0.set(self.0.get() + 1);
            }
        }

        let dir = tempfile::tempdir()?;
        let root = dir.path().join("root.usda");
        fs::write(&root, "#usda 1.0\ndef \"P\" (references = @./missing.usda@) {}\n")?;
        let stage = Stage::open(&root.to_string_lossy())?;
        assert!(stage.prim("/P")?.is_valid()?, "the prim composes without its target");
        let retried = Rc::new(Cell::new(0));
        stage.add_sink(Retried(Rc::clone(&retried)));
        let root_id = stage.root_layer().identifier().to_owned();
        stage.edit_layer(&root_id, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/X", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        assert!(stage.prim("/X")?.is_valid()?);
        assert_eq!(retried.get(), 0);
        Ok(())
    }

    /// A layer whose last handle a sink drops while the stage delivers to it
    /// is freed once the delivery is over, with no borrow of the stage held:
    /// its own sink, which reads and authors the stage as it drops, gets an
    /// answer, and the edit it makes is delivered.
    #[test]
    fn freed_after_delivery() -> Result<()> {
        struct ReadOnDrop {
            stage: Stage,
            root: String,
            read: Rc<Cell<Option<bool>>>,
        }
        impl sdf::LayerSink for ReadOnDrop {}
        impl Drop for ReadOnDrop {
            fn drop(&mut self) {
                let read = self.stage.prim("/Child").is_ok();
                let authored = self.stage.edit_layer(&self.root, |e| {
                    sdf::PrimSpec::new(e.data_mut(), "/Late", sdf::Specifier::Def, "")?;
                    Ok(())
                });
                self.read.set(Some(read && authored.is_ok()));
            }
        }
        /// Drops the extra layer's handle when the edit target changes, then
        /// reads the stage inside the delivery.
        struct DropOnTarget {
            handle: RefCell<Option<sdf::LayerHandle>>,
            read: Rc<Cell<Option<bool>>>,
            during: Rc<Cell<Option<(bool, bool)>>>,
            late: Rc<Cell<bool>>,
        }
        impl StageSink for DropOnTarget {
            fn after_commit(&self, _: &Stage, change: &usd::CommittedChange<'_>) {
                self.late
                    .set(self.late.get() || change.resynced.iter().any(|path| path.as_str() == "/Late"));
            }
            fn edit_target_changed(&self, stage: &Stage) {
                drop(self.handle.borrow_mut().take());
                // Each read releases a borrow of the layers, which sweeps
                // when nothing holds the sweeps.
                drop(stage.root_layer());
                let answered = stage.prim("/Child").is_ok();
                self.during.set(Some((answered, self.read.get().is_none())));
            }
        }

        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("root.usda"),
            "#usda 1.0\ndef \"Child\" (references = @ref.usda@</R>) {}\n",
        )?;
        fs::write(dir.path().join("ref.usda"), "#usda 1.0\ndef \"R\" {}\n")?;
        let registry = sdf::LayerRegistry::default();
        let root = dir.path().join("root.usda");
        let stage = Stage::builder()
            .registry(registry.clone())
            .open(&root.to_string_lossy())?;
        let read = Rc::new(Cell::new(None));
        let mut extra = sdf::Layer::new_anonymous("extra.usda");
        extra.add_sink(ReadOnDrop {
            stage: stage.clone(),
            root: stage.root_layer().identifier().to_owned(),
            read: Rc::clone(&read),
        });
        let during = Rc::new(Cell::new(None));
        let late = Rc::new(Cell::new(false));
        stage.add_sink(DropOnTarget {
            handle: RefCell::new(registry.adopt(extra).ok()),
            read: Rc::clone(&read),
            during: Rc::clone(&during),
            late: Rc::clone(&late),
        });
        let target = stage
            .prim("/Child")?
            .edit_target_for_arc(usd::EditTargetArc::Reference)?;
        stage.set_edit_target(target)?;
        assert_eq!(during.get(), Some((true, true)), "held through the delivery");
        assert_eq!(read.get(), Some(true), "freed after the delivery, reading the stage");
        assert!(late.get(), "the edit the freed sink made was delivered");
        Ok(())
    }

    /// A reload through one stage tries the failed loads again in every stage
    /// it reaches.
    #[test]
    fn reload_retries_shared() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        fs::remove_file(dir.path().join("sub.usda"))?;
        let registry = sdf::LayerRegistry::default();
        let a = Stage::builder().registry(registry.clone()).open(&root)?;
        let b = Stage::builder().registry(registry).open(&root)?;
        assert!(!b.prim("/Sub")?.is_valid()?);
        fs::write(dir.path().join("sub.usda"), "#usda 1.0\ndef \"Sub\" {}\n")?;
        sdf::layer::tests::append(FsPath::new(&root), "def \"Added\" {}\n")?;
        a.reload()?;
        assert!(a.prim("/Sub")?.is_valid()?);
        assert!(b.prim("/Sub")?.is_valid()?, "the other stage loads the sublayer too");
        Ok(())
    }

    /// A stage reload that must reload a layer fails with
    /// [`sdf::LayerError::Busy`] from inside a read of its registry's layers.
    #[test]
    fn stage_reload_busy() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = Stage::open(&shared_fixture(dir.path())?)?;
        stage.edit_layer(&layer_named(&stage, "sub.usda"), |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Unsaved", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        let root = stage
            .layer_handle(stage.root_layer().identifier())
            .expect("the stage holds its root");
        let reloaded = root.read(|_| stage.reload())?;
        assert!(
            matches!(reloaded, Err(crate::Error::Layer(sdf::LayerError::Busy))),
            "{reloaded:?}"
        );
        Ok(())
    }

    /// Unmuting a sublayer its mute freed resyncs the prims it composes into.
    #[test]
    fn unmute_freed_resyncs() -> Result<()> {
        /// Each muting notice: whether it muted, and what it resynced.
        type Notices = Rc<RefCell<Vec<(bool, Vec<sdf::Path>)>>>;
        struct Log(Notices);
        impl StageSink for Log {
            fn layer_muting_changed(&self, _: &Stage, _: &str, muted: bool, resynced: &[sdf::Path]) {
                self.0.borrow_mut().push((muted, resynced.to_vec()));
            }
        }

        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let stage = Stage::open(&root)?;
        let weak = layer_named(&stage, "sub.usda");
        let log = Rc::new(RefCell::new(Vec::new()));
        stage.add_sink(Log(Rc::clone(&log)));
        stage.mute_layer(weak.as_str());
        assert!(!stage.prim("/Sub")?.is_valid()?, "composed while muted");
        assert_eq!(stage.layer_count(), 1);
        stage.unmute_layer(&weak);
        assert!(stage.prim("/Sub")?.is_valid()?);
        let log = log.borrow();
        let (muted, resynced) = log.last().expect("the unmute notified");
        assert!(!muted);
        assert!(!resynced.is_empty(), "the unmute resyncs what the layer reaches");
        Ok(())
    }

    /// A muted layer two spellings name keeps answering to both once freed,
    /// and unmuting by either reads it again.
    #[test]
    fn freed_mute_both_spellings() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(dir.path().join("sub.usda"), "#usda 1.0\ndef \"Sub\" {}\n")?;
        let absolute = dir.path().join("sub.usda").canonicalize()?;
        let absolute = absolute.to_str().expect("utf-8 path").to_owned();
        for unmute_by in ["sub.usda", absolute.as_str()] {
            let stage = Stage::builder()
                .resolver(ar::DefaultResolver::with_search_paths([dir.path()]))
                .in_memory("root.usda")?;
            let root_id = stage.root_layer().identifier().to_string();
            stage.edit_layer(&root_id, |e| {
                e.pseudo_root_mut()?.set_sublayers(["sub.usda"]);
                Ok(())
            })?;
            let mut other = sdf::Layer::new_in_memory("other.usda");
            edit_layer(&mut other, |e| {
                e.pseudo_root_mut().unwrap().set_sublayers([absolute.as_str()]);
            });
            stage.insert_layer(&root_id, 1, other, sdf::LayerOffset::IDENTITY)?;
            assert!(stage.prim("/Sub")?.is_defined()?);
            stage.mute_layer("sub.usda");
            assert_eq!(stage.layer_count(), 2, "sub.usda left the stage");
            assert!(stage.is_layer_muted("sub.usda"));
            assert!(stage.is_layer_muted(&absolute), "the other spelling reads muted");
            assert!(!stage.prim("/Sub")?.is_defined()?);
            stage.unmute_layer(unmute_by);
            assert!(stage.muted_layers().is_empty(), "unmuted by {unmute_by}");
            assert!(stage.prim("/Sub")?.is_defined()?, "read again");
        }
        Ok(())
    }

    /// Muting a session layer frees a sublayer added to it after the stage
    /// opened, though the session layer stays, and unmuting reads it again.
    #[test]
    fn session_mute_frees_child() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(dir.path().join("root.usda"), "#usda 1.0\n")?;
        fs::write(dir.path().join("session.usda"), "#usda 1.0\n")?;
        fs::write(dir.path().join("extra.usda"), "#usda 1.0\ndef \"E\" {}\n")?;
        let stage = Stage::builder()
            .session_layer(dir.path().join("session.usda").to_string_lossy().into_owned())
            .open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        let session = layer_named(&stage, "session.usda");
        stage.edit_layer(&session, |e| {
            e.pseudo_root_mut()?.set_sublayers(["./extra.usda"]);
            Ok(())
        })?;
        assert!(stage.prim("/E")?.is_valid()?);
        assert_eq!(stage.layer_count(), 3);
        stage.mute_layer(session.as_str());
        assert_eq!(stage.layer_count(), 2, "the session layer stays, its sublayer leaves");
        assert!(!stage.prim("/E")?.is_valid()?);
        stage.unmute_layer(&session);
        assert!(stage.prim("/E")?.is_valid()?, "unmuted, the sublayer is read again");
        assert_eq!(stage.layer_count(), 3);
        Ok(())
    }

    /// Muting a sublayer frees only it: a payload layer whose prims the mute
    /// recomposes stays.
    #[test]
    fn mute_keeps_payload() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (root, _) = payload_fixture(dir.path())?;
        fs::write(dir.path().join("sub.usda"), "#usda 1.0\ndef \"Sub\" {}\n")?;
        let stage = Stage::open(&root)?;
        let root_id = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root_id, |e| {
            e.pseudo_root_mut()?.set_sublayers(["./sub.usda"]);
            Ok(())
        })?;
        assert!(stage.prim("/Sub")?.is_valid()?);
        assert!(stage.prim("/P/C")?.is_valid()?);
        assert_eq!(stage.layer_count(), 3);
        stage.mute_layer(layer_named(&stage, "sub.usda"));
        assert_eq!(stage.layer_count(), 2, "the payload layer stays");
        assert!(stage.prim("/P/C")?.is_valid()?);
        Ok(())
    }

    /// A layer muted at open leaves the stage, and unmuting reads it.
    #[test]
    fn open_mute_unread() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let sub = dir.path().join("sub.usda").to_str().expect("utf-8 path").to_owned();
        let stage = Stage::builder().mute([sub.as_str()]).open(&root)?;
        assert!(stage.is_layer_muted(&sub));
        assert_eq!(stage.layer_count(), 1, "the muted layer is not on the stage");
        stage.unmute_layer(&sub);
        assert!(stage.prim("/Sub")?.is_valid()?, "unmuted, it is read");
        assert_eq!(stage.layer_count(), 2);
        Ok(())
    }

    /// A builder mute of the root layer is ignored.
    #[test]
    fn open_mute_root_ignored() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        let stage = Stage::builder().mute([root.as_str()]).open(&root)?;
        assert!(stage.muted_layers().is_empty());
        assert!(stage.prim("/A")?.is_valid()?);
        assert!(stage.prim("/Sub")?.is_valid()?);
        Ok(())
    }

    /// A session layer muted at open stays, its sublayers unread, and
    /// unmuting composes them.
    #[test]
    fn open_mute_session() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = shared_fixture(dir.path())?;
        fs::write(
            dir.path().join("session.usda"),
            "#usda 1.0\n(\n    subLayers = [@./extra.usda@]\n)\n",
        )?;
        fs::write(dir.path().join("extra.usda"), "#usda 1.0\ndef \"E\" {}\n")?;
        let session = dir.path().join("session.usda").to_str().expect("utf-8 path").to_owned();
        let stage = Stage::builder()
            .session_layer(session.clone())
            .mute([session.as_str()])
            .open(&root)?;
        assert!(stage.is_layer_muted(&session));
        assert!(!stage.prim("/E")?.is_valid()?);
        assert_eq!(stage.layer_count(), 3, "the session layer, the root and its sublayer");
        stage.unmute_layer(&session);
        assert!(stage.prim("/E")?.is_valid()?, "unmuted, its sublayer is read");
        Ok(())
    }

    /// A freed muted layer joining again under another of its spellings is
    /// muted.
    #[test]
    fn freed_mute_rejoin() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(dir.path().join("sub.usda"), "#usda 1.0\ndef \"Sub\" {}\n")?;
        let absolute = dir.path().join("sub.usda").canonicalize()?;
        let absolute = absolute.to_str().expect("utf-8 path").to_owned();
        let stage = Stage::builder()
            .resolver(ar::DefaultResolver::with_search_paths([dir.path()]))
            .in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root_id, |e| {
            e.pseudo_root_mut()?.set_sublayers(["sub.usda"]);
            Ok(())
        })?;
        assert!(stage.prim("/Sub")?.is_defined()?);
        stage.mute_layer("sub.usda");
        assert_eq!(stage.layer_count(), 1, "sub.usda left the stage");
        let mut again = sdf::Layer::new_in_memory(absolute.as_str());
        edit_layer(&mut again, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Sub", sdf::Specifier::Def, "").unwrap();
        });
        stage.insert_layer(&root_id, 1, again, sdf::LayerOffset::IDENTITY)?;
        assert!(stage.is_layer_muted(&absolute));
        assert!(!stage.prim("/Sub")?.is_defined()?, "it joined muted");
        Ok(())
    }

    /// A root layer sublayering `sub.usda`, both written to `dir`, and the
    /// root's path.
    fn shared_fixture(dir: &FsPath) -> Result<String> {
        fs::write(
            dir.join("root.usda"),
            "#usda 1.0\n(\n    subLayers = [@./sub.usda@]\n)\ndef \"A\" {}\n",
        )?;
        fs::write(dir.join("sub.usda"), "#usda 1.0\ndef \"Sub\" {}\n")?;
        Ok(dir.join("root.usda").to_str().expect("utf-8 path").to_owned())
    }

    /// Stages opened on one registry read each layer once.
    #[test]
    fn shared_registry_one_read() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = shared_fixture(dir.path())?;
        let (registry, opens) = sdf::layer_registry::tests::counting_registry();
        let a = Stage::builder().registry(registry.clone()).open(&path)?;
        assert_eq!(opens.get(), 2, "the root and its sublayer");
        let b = Stage::builder().registry(registry).open(&path)?;
        assert_eq!(opens.get(), 2, "the second stage finds both layers");
        assert!(a.prim("/Sub")?.is_valid()?);
        assert!(b.prim("/Sub")?.is_valid()?);
        Ok(())
    }

    /// An edit through one stage on a registry reaches another stage's
    /// composed reads, even ones it cached, and its sinks, as an edit the
    /// other stage did not make.
    #[test]
    fn shared_registry_fans_out() -> Result<()> {
        struct Own(Rc<RefCell<Vec<bool>>>);
        impl StageSink for Own {
            fn after_commit(&self, _: &Stage, change: &usd::CommittedChange<'_>) {
                self.0.borrow_mut().push(change.is_own());
            }
        }

        let dir = tempfile::tempdir()?;
        let path = shared_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let a = Stage::builder().registry(registry.clone()).open(&path)?;
        let b = Stage::builder().registry(registry).open(&path)?;
        let (seen_a, seen_b) = (Rc::new(RefCell::new(Vec::new())), Rc::new(RefCell::new(Vec::new())));
        a.add_sink(Own(Rc::clone(&seen_a)));
        b.add_sink(Own(Rc::clone(&seen_b)));
        assert!(!b.prim("/A/B")?.is_valid()?);

        a.define_prim("/A/B")?;
        assert_eq!(*seen_a.borrow(), [true]);
        assert_eq!(
            *seen_b.borrow(),
            [false],
            "B's sink hears A's edit as it commits, as foreign"
        );
        assert!(b.prim("/A/B")?.is_valid()?, "B composes A's edit");

        let sub = b.layer_handle(&b.sub_layers(b.root_layer().identifier())[0]);
        sub.expect("B holds the sublayer").edit(|e| {
            sdf::PrimSpec::new(e.data_mut(), "/Direct", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        assert_eq!(*seen_b.borrow(), [false, false], "B hears a handle edit as it commits");
        assert!(a.prim("/Direct")?.is_valid()?, "A composes a direct handle edit");
        assert_eq!(*seen_a.borrow(), [true, false], "a handle edit is no stage's own");
        Ok(())
    }

    /// A stage opened on a registry composes the layers it already holds as
    /// they stand, unsaved edits included.
    #[test]
    fn open_finds_unsaved_edit() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = shared_fixture(dir.path())?;
        let (registry, opens) = sdf::layer_registry::tests::counting_registry();
        let a = Stage::builder().registry(registry.clone()).open(&path)?;
        a.define_prim("/Unsaved")?;
        let b = Stage::builder().registry(registry).open(&path)?;
        assert!(b.prim("/Unsaved")?.is_valid()?);
        assert_eq!(opens.get(), 2, "nothing is read again");
        Ok(())
    }

    /// A registry holds a layer while any stage on it does.
    #[test]
    fn shared_layer_outlives_stage() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = shared_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let a = Stage::builder().registry(registry.clone()).open(&path)?;
        let b = Stage::builder().registry(registry.clone()).open(&path)?;
        drop(a);
        assert!(registry.find(&path)?.is_some(), "B still holds the root");
        drop(b);
        assert!(registry.find(&path)?.is_none(), "no stage holds the root");

        let sub = dir.path().join("sub.usda").to_str().expect("utf-8 path").to_owned();
        let a = Stage::builder().registry(registry.clone()).open(&path)?;
        let b = Stage::builder().registry(registry.clone()).open(&sub)?;
        drop(a);
        assert!(registry.find(&path)?.is_none(), "only A held the root");
        assert!(registry.find(&sub)?.is_some(), "B holds the sublayer");
        drop(b);
        Ok(())
    }

    /// A stage opened from inside a read of its registry's layers fails with
    /// [`sdf::LayerError::Busy`].
    #[test]
    fn open_inside_read_busy() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let path = shared_fixture(dir.path())?;
        let registry = sdf::LayerRegistry::default();
        let a = Stage::builder().registry(registry.clone()).open(&path)?;
        let root = a.layer_handle(a.root_layer().identifier()).expect("A holds its root");
        let opened = root.read(|_| Stage::builder().registry(registry.clone()).open(&path).map(drop))?;
        assert!(
            matches!(opened, Err(crate::Error::Layer(sdf::LayerError::Busy))),
            "{opened:?}"
        );
        Ok(())
    }

    /// A stage opened over a layer the registry takes refuses a layer whose
    /// identifier the registry already holds.
    #[test]
    fn open_layer_refuses_duplicate() -> Result<()> {
        let registry = sdf::LayerRegistry::default();
        let held = registry
            .adopt(sdf::Layer::new_in_memory("root.usda"))
            .map_err(|refused| refused.error)?;
        let opened = Stage::builder()
            .registry(registry)
            .open_layer(sdf::Layer::new_in_memory("root.usda"));
        assert!(matches!(
            opened,
            Err(crate::Error::Layer(sdf::LayerError::Duplicate { .. }))
        ));
        drop(held);
        Ok(())
    }

    /// An anonymous layer's sublayer entry that names no asset reports an
    /// [`UnresolvedSublayer`](pcp::CompositionDiagnostic::UnresolvedSublayer)
    /// diagnostic rather than vanishing (C++ `PcpErrorInvalidSublayerPath`).
    #[test]
    fn anon_missing_sublayer_reports() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let missing = dir.path().join("missing.usda");
        let stage = Stage::builder().in_memory("root.usda")?;
        let root_id = stage.root_layer().identifier().to_string();
        stage.edit_layer(&root_id, |e| {
            e.pseudo_root_mut()?
                .set_sublayers([missing.to_str().expect("utf-8 path")]);
            Ok(())
        })?;
        assert!(
            stage
                .composition_errors()
                .iter()
                .any(|error| matches!(error, pcp::CompositionDiagnostic::UnresolvedSublayer { .. })),
            "the missing sublayer reports"
        );
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
                vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
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
                .set_default(vt::Value::Double(5.0))
                .expect("value fits the declared type");
        });

        let stage = Stage::builder().make_stage(vec![root, target], 0, pcp::Diagnostics::default());
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
                vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
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

        let stage = Stage::builder().make_stage(vec![root, target], 0, pcp::Diagnostics::default());
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
        let stage = Stage::builder().make_stage(vec![session, root, child], 1, pcp::Diagnostics::default());
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
                vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
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

        let stage = Stage::builder().make_stage(vec![root, target], 0, pcp::Diagnostics::default());
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
                vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
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

        let stage = Stage::builder().make_stage(
            vec![root, target, opinion_layer("base.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
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
        let stage = Stage::builder().make_stage(vec![root], 0, pcp::Diagnostics::default());
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
                vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
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

        let stage = Stage::builder().make_stage(vec![root, target], 0, pcp::Diagnostics::default());
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
                x.set_time_sample(0.0, vt::Value::Double(0.0))
                    .expect("value fits the declared type");
                x.set_time_sample(20.0, vt::Value::Double(200.0))
                    .expect("value fits the declared type");
            });
            Stage::builder().make_stage(vec![root, sub], 0, pcp::Diagnostics::default())
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
            pr.set_expression_variables(HashMap::from([("WHICH".to_string(), vt::Value::String("a".into()))]));
            pr.set_sublayers([r#"`"${WHICH}.usda"`"#]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("a.usda", 1.0)?, opinion_layer("b.usda", 2.0)?],
            0,
            pcp::Diagnostics::default(),
        );

        assert_eq!(
            stage.attribute("/A.x")?.get::<f64>()?,
            Some(1.0),
            "the WHICH-valued sublayer resolves to a.usda"
        );
        stage.set_expression_variables(HashMap::from([("WHICH".to_string(), vt::Value::String("b".into()))]))?;
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
                .set_expression_variables(HashMap::from([("WHICH".to_string(), vt::Value::String("a".into()))]));
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
            pcp::Diagnostics::default(),
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
            pcp::Diagnostics::default(),
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

        let err = stage
            .set_stage_metadata("comment", "on a sublayer")
            .expect_err("sublayer target must be rejected");
        assert!(matches!(err, StageAuthoringError::StageMetadataTarget { layer } if layer == sub_id));
        assert!(!stage.has_authored_stage_metadata("comment")?);

        stage.set_edit_target(EditTarget::for_layer(root))?;
        stage.set_start_time_code(1.0)?;
        assert_eq!(stage.start_time_code(), 1.0);
        stage.set_stage_metadata("comment", "on the root")?;
        assert_eq!(stage.stage_metadata("comment")?, Some(vt::Value::from("on the root")));
        Ok(())
    }

    /// A direct `layer_handle` edit to `subLayers` rebuilds the graph's edges before
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
            pcp::Diagnostics::default(),
        );
        assert_eq!(
            stage.sub_layers("root.usda"),
            vec!["root.usda", "weak1.usda", "weak2.usda"]
        );

        {
            let root = stage.layer_handle("root.usda").expect("root layer");
            root.edit(|e| {
                e.pseudo_root_mut().unwrap().set_sublayers(["weak2.usda"]);
                Ok(())
            })?;
        }
        assert_eq!(stage.sub_layers("root.usda"), vec!["root.usda", "weak2.usda"]);
        Ok(())
    }

    /// The stage tags each committed edit with its origin: a stage edit on a
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
                vt::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
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
        let stage = Stage::builder().make_stage(vec![root, target], 0, pcp::Diagnostics::default());

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
            let target = stage.layer_handle("target.usda").expect("target layer");
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

        // A variant edit target remaps its paths, so its commit reports the
        // target's mapping.
        stage.set_edit_target(usd::EditTarget::for_local_direct_variant(
            "root.usda",
            sdf::path("/Q{set=sel}")?,
        )?)?;
        stage.create_attribute("/Q.v", sdf::ValueTypeName::FLOAT)?;
        assert_eq!(seen.get(), Some("target"), "a variant edit reports EditTarget");
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
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );

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

    /// A `batch_edit` that a sink's panic aborts on its second layer reaches
    /// the stage's sinks as one aborted transaction.
    #[test]
    fn batch_abort_once() -> Result<()> {
        struct Log {
            seen: Cell<usize>,
            aborted: Rc<RefCell<Vec<u64>>>,
        }
        impl StageSink for Log {
            fn before_commit(&self, _: &Stage, _: &PendingChange<'_>) {
                if self.seen.replace(self.seen.get() + 1) == 1 {
                    panic!("the sink panics on the second layer");
                }
            }
            fn aborted(&self, _: &Stage, generation: u64) {
                self.aborted.borrow_mut().push(generation);
            }
        }

        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        let aborted = Rc::new(RefCell::new(Vec::new()));
        stage.add_sink(Log {
            seen: Cell::new(0),
            aborted: Rc::clone(&aborted),
        });
        let unwound = panic::catch_unwind(AssertUnwindSafe(|| {
            stage.batch_edit(&["root.usda", "weak.usda"], |edits| {
                sdf::PrimSpec::new(edits[0].data_mut(), "/FromRoot", sdf::Specifier::Def, "")?;
                sdf::PrimSpec::new(edits[1].data_mut(), "/FromWeak", sdf::Specifier::Def, "")?;
                Ok(())
            })
        }));
        assert!(unwound.is_err());
        stage.process_pending();
        assert_eq!(aborted.borrow().len(), 1, "{:?}", aborted.borrow());
        Ok(())
    }

    /// A stage edit and then a mute a sink makes from `after_commit` reach the
    /// other sinks in that order, after the change that fired the sink.
    #[test]
    fn nested_mute_in_order() -> Result<()> {
        struct Log(Rc<RefCell<Vec<String>>>);
        impl StageSink for Log {
            fn after_commit(&self, _: &Stage, change: &usd::CommittedChange<'_>) {
                let paths: Vec<_> = change.resynced.iter().map(|path| path.as_str().to_owned()).collect();
                self.0.borrow_mut().push(format!("commit {}", paths.join(",")));
            }
            fn layer_muting_changed(&self, _: &Stage, layer: &str, _: bool, _: &[sdf::Path]) {
                self.0.borrow_mut().push(format!("mute {layer}"));
            }
        }

        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        {
            let nested = stage.clone();
            let fired = Cell::new(false);
            stage.add_sink(move |_: &Stage, _: &usd::CommittedChange<'_>| {
                if !fired.replace(true) {
                    nested.define_prim("/A").expect("the nested edit");
                    nested.mute_layer("weak.usda");
                }
            });
        }
        let log = Rc::new(RefCell::new(Vec::new()));
        stage.add_sink(Log(Rc::clone(&log)));
        stage.define_prim("/World")?;
        assert_eq!(*log.borrow(), ["commit /World", "commit /A", "mute weak.usda"]);
        Ok(())
    }

    /// A sink on the first layer of a `batch_edit` that reads the stage from its
    /// `after_commit` composes the whole batch, which the stage reports as one
    /// change.
    #[test]
    fn batch_read_in_sink() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        let events = Rc::new(Cell::new(0));
        {
            let events = events.clone();
            stage.add_sink(move |_: &Stage, _: &usd::CommittedChange<'_>| events.set(events.get() + 1));
        }
        let seen = Rc::new(Cell::new(None));
        let layer = stage.layer_handle("root.usda").expect("root layer");
        let sink = {
            let (stage, seen) = (stage.clone(), seen.clone());
            layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
                seen.set(Some(
                    stage
                        .prim("/FromWeak")
                        .expect("a valid path")
                        .is_valid()
                        .expect("a read"),
                ));
            })?
        };
        stage.batch_edit(&["root.usda", "weak.usda"], |edits| {
            sdf::PrimSpec::new(edits[0].data_mut(), "/FromRoot", sdf::Specifier::Def, "")?;
            sdf::PrimSpec::new(edits[1].data_mut(), "/FromWeak", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        layer.remove_sink(sink)?;
        assert_eq!(seen.get(), Some(true), "the sink composes the batch's other layer");
        assert_eq!(events.get(), 1, "the batch is one change");
        Ok(())
    }

    /// A layer sink can read the stage from its `after_commit` during a stage
    /// edit, as it can during a direct edit: the stage delivers its commit
    /// once it has released the graph.
    #[test]
    fn sink_reads_stage_edit() -> Result<()> {
        let stage = Stage::builder().in_memory("root.usda")?;
        stage.define_prim("/A")?;
        let root = stage.root_layer().identifier().to_string();
        let seen = Rc::new(Cell::new(None));
        let sink = {
            let (stage, seen) = (stage.clone(), seen.clone());
            stage
                .layer_handle(&root)
                .expect("root layer")
                .add_sink(move |_: &str, _: &sdf::ChangeList| {
                    seen.set(Some(stage.root_layer().identifier().to_owned()));
                })?
        };
        stage.define_prim("/Outer")?;
        stage.layer_handle(&root).expect("root layer").remove_sink(sink)?;
        assert_eq!(seen.take().as_deref(), Some(root.as_str()));
        Ok(())
    }

    /// A composed query made from inside an edit of the stage's layer, with
    /// an earlier direct edit still queued, fails with `Busy` and loses
    /// nothing: once the edit returns, the queued edit composes.
    #[test]
    fn query_inside_edit_busy() -> Result<()> {
        let stage = Stage::builder().in_memory("root.usda")?;
        let root = stage.root_layer().identifier().to_string();
        let layer = stage.layer_handle(&root).expect("root layer");
        layer.edit(|e| {
            sdf::PrimSpec::new(e.data_mut(), "/First", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        let mut inside = None;
        let mut traversed = None;
        layer.edit(|_| {
            inside = Some(stage.prim("/First").expect("a valid path").is_valid());
            traversed = Some(stage.traverse(PrimPredicate::DEFAULT, |_| {}));
            Ok(())
        })?;
        assert!(traversed.expect("the closure ran").is_err(), "a traversal fails too");
        let inside = inside.expect("the closure ran");
        assert!(
            inside.as_ref().is_err_and(|error| error.to_string().contains("in use")),
            "{inside:?}"
        );
        assert!(stage.prim("/First")?.is_valid()?, "the queued edit composes");
        Ok(())
    }

    /// Runs `f` on `stage` from a sink of its root layer, after a direct edit
    /// of the root lands and before the stage's delivery reconciles it, so the
    /// edit is still queued on the stage.
    fn while_queued(stage: &Stage, f: impl Fn(&Stage) + 'static) -> Result<()> {
        struct Run<F>(WeakStage, F);
        impl<F: Fn(&Stage)> sdf::LayerSink for Run<F> {
            fn after_commit(&self, _change: &sdf::CommittedLayerChange<'_>) {
                if let Some(stage) = self.0.upgrade() {
                    (self.1)(&stage);
                }
            }
        }
        let root = stage.root_layer().identifier().to_string();
        let layer = stage.layer_handle(&root).expect("root layer");
        let sink = layer.add_sink(Run(stage.downgrade(), f))?;
        let edited = layer.edit(|e| {
            sdf::PrimSpec::new(e.data_mut(), "/Queued", sdf::Specifier::Def, "")?;
            Ok(())
        });
        layer.remove_sink(sink)?;
        edited?;
        Ok(())
    }

    /// Cached reads made from inside a read of the stage's layer, with an
    /// earlier direct edit still queued, fail with `Busy` as composed queries
    /// do: a warmed attribute query and a prim's type.
    #[test]
    fn cached_reads_busy() -> Result<()> {
        let stage = Stage::builder().in_memory("root.usda")?;
        stage.define_prim("/A")?;
        let attribute = stage.create_attribute("/A.x", sdf::ValueTypeName::FLOAT)?;
        let query = usd::AttributeQuery::new(&attribute);
        assert_eq!(query.get_at::<f32>(None)?, None);
        stage.prim_type_info("/A")?;
        let root = stage.root_layer().identifier().to_string();
        let layer = stage.layer_handle(&root).expect("root layer");
        let failed = Rc::new(Cell::new(None));
        while_queued(&stage, {
            let failed = Rc::clone(&failed);
            move |stage| {
                let read = layer.read(|_| (query.get_at::<f32>(None).is_err(), stage.prim_type_info("/A").is_err()));
                failed.set(Some(read.expect("a read beside the sink's own")));
            }
        })?;
        assert_eq!(failed.get(), Some((true, true)), "the value and type reads fail");
        assert_eq!(usd::AttributeQuery::new(&attribute).get_at::<f32>(None)?, None);
        assert!(stage.prim("/Queued")?.is_valid()?, "the queued edit composes");
        Ok(())
    }

    /// A composed query made from inside a read of the stage's layer that
    /// reaches an unloaded reference fails with `Busy`, and a later query
    /// loads the reference.
    #[test]
    fn query_inside_read_busy() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("root.usda"),
            "#usda 1.0\ndef \"Ref\" (references = @./ref.usda@</Model>) {}\n",
        )?;
        fs::write(
            dir.path().join("ref.usda"),
            "#usda 1.0\ndef \"Model\" {\n    def \"Child\" {}\n}\n",
        )?;
        let stage = Stage::open(dir.path().join("root.usda").to_str().expect("utf-8 path"))?;
        let root = stage.root_layer().identifier().to_string();
        let layer = stage.layer_handle(&root).expect("root layer");
        let inside = layer.read(|_| stage.prim("/Ref/Child").expect("a valid path").is_valid())?;
        assert!(
            inside.as_ref().is_err_and(|error| error.to_string().contains("in use")),
            "{inside:?}"
        );
        assert!(
            stage.prim("/Ref/Child")?.is_valid()?,
            "a later query loads the reference"
        );
        Ok(())
    }

    /// A handle kept past its stage holds its own layer; every other layer
    /// the stage loaded is freed with the stage.
    #[test]
    fn kept_handle_frees_rest() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        let sentinel = Rc::new(());
        let freed = Rc::downgrade(&sentinel);
        stage
            .layer_handle("weak.usda")
            .expect("weak layer")
            .add_sink(move |_: &str, _: &sdf::ChangeList| {
                let _ = &sentinel;
            })?;
        let root = stage.layer_handle("root.usda").expect("root layer");
        drop(stage);
        assert!(freed.upgrade().is_none(), "the unheld sublayer is freed");
        assert_eq!(root.read(|layer| layer.identifier().to_owned())?, "root.usda");
        Ok(())
    }

    /// A stage dropped inside a read of a handle it gave out frees its other
    /// layers once the read ends.
    #[test]
    fn drop_inside_read_frees() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        let sentinel = Rc::new(());
        let freed = Rc::downgrade(&sentinel);
        stage
            .layer_handle("weak.usda")
            .expect("weak layer")
            .add_sink(move |_: &str, _: &sdf::ChangeList| {
                let _ = &sentinel;
            })?;
        let root = stage.layer_handle("root.usda").expect("root layer");
        let held = root.read(|_| {
            drop(stage);
            freed.upgrade().is_some()
        })?;
        assert!(held, "the read holds the store while the stage drops");
        assert!(freed.upgrade().is_none(), "the read's end frees the unheld sublayer");
        Ok(())
    }

    /// A direct edit a layer sink makes while a `batch_edit` delivers queues
    /// behind the whole batch: the stage sees the batch as one change, then
    /// the nested edit as another.
    #[test]
    fn nested_edit_after_batch() -> Result<()> {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["weak.usda"]);
        });
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
        let events = Rc::new(Cell::new(0));
        {
            let events = events.clone();
            stage.add_sink(move |_: &Stage, _: &usd::CommittedChange<'_>| events.set(events.get() + 1));
        }
        let layer = stage.layer_handle("root.usda").expect("root layer");
        let nested = layer.clone();
        let fired = Rc::new(Cell::new(false));
        let once = fired.clone();
        let sink = layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            if !once.replace(true) {
                nested
                    .edit(|e| {
                        sdf::PrimSpec::new(e.data_mut(), "/Nested", sdf::Specifier::Def, "")?;
                        Ok(())
                    })
                    .expect("nested edit");
            }
        })?;

        stage.batch_edit(&["root.usda", "weak.usda"], |edits| {
            sdf::PrimSpec::new(edits[0].data_mut(), "/FromRoot", sdf::Specifier::Def, "")?;
            sdf::PrimSpec::new(edits[1].data_mut(), "/FromWeak", sdf::Specifier::Def, "")?;
            Ok(())
        })?;
        layer.remove_sink(sink)?;
        stage.process_pending();

        assert!(stage.prim("/Nested")?.is_valid()?);
        assert_eq!(events.get(), 2, "the batch is one change and the nested edit another");
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
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );
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
        let stage = Stage::builder().make_stage(
            vec![root, opinion_layer("weak.usda", 1.0)?],
            0,
            pcp::Diagnostics::default(),
        );

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
        while_queued(&stage, move |stage| {
            let _ = stage.author_layers_txn(
                &[root_id],
                None,
                false,
                |_ids, _edits| Ok::<(), StageAuthoringError>(()),
            );
        })
        .expect("direct edit commits");
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

    /// A prototype root is a prim with no properties: its own spec answers,
    /// and each property's does not, while its child's property still does.
    #[test]
    fn prototype_root_specs() -> Result<()> {
        let stage = Stage::open(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/fixtures/instancing_root_empty.usda"
        ))?;
        let proto = stage.prim("/A")?.prototype()?.expect("A is an instance");

        assert!(stage.has_spec(&proto)?);
        assert_eq!(stage.spec_type(proto.clone())?, Some(sdf::SpecType::Prim));
        let animated = proto.append_property("animated")?;
        assert!(!stage.has_spec(&animated)?);
        assert_eq!(stage.spec_type(animated)?, None);
        let size = proto.append_path("Child")?.append_property("size")?;
        assert!(stage.has_spec(&size)?);
        assert_eq!(stage.spec_type(size)?, Some(sdf::SpecType::Attribute));
        Ok(())
    }
    /// A hook a stage's resolver runs once, on opening one file.
    type Hook = Rc<Cell<Option<Box<dyn FnOnce()>>>>;

    /// The stage over `root` in `dir`, whose other files are `files`,
    /// opened through a resolver that runs the returned hook on opening
    /// `name`.
    fn hooked_stage(dir: &FsPath, root: &str, files: &[(&str, &str)], name: &'static str) -> Result<(Stage, Hook)> {
        let hook: Hook = Rc::default();
        let run = Rc::clone(&hook);
        let open = move |file: &str| {
            if file == name
                && let Some(hook) = run.take()
            {
                hook();
            }
        };
        let stage = resolving_stage(dir, root, files, open, |_| {})?;
        Ok((stage, hook))
    }

    /// Defines `path` in `layer` through its handle, as user code outside the
    /// stage would.
    fn define_raw(layer: &sdf::LayerHandle, path: &str) {
        layer
            .edit(|e| {
                sdf::PrimSpec::new(e.data_mut(), path, sdf::Specifier::Def, "")?;
                Ok(())
            })
            .expect("the layer is free");
    }

    /// Sublayers `b.usda` under `layer` through its handle.
    fn sublayer_raw(layer: &sdf::LayerHandle) {
        layer
            .edit(|e| {
                e.pseudo_root_mut()
                    .expect("a layer has a pseudo-root")
                    .set_sublayers(["b.usda"]);
                Ok(())
            })
            .expect("the layer is free");
    }

    /// The paths each committed change resyncs, in delivery order.
    type Resyncs = Rc<RefCell<Vec<Vec<String>>>>;

    /// The [`Resyncs`] a sink added to `stage` records.
    fn record_resyncs(stage: &Stage) -> Resyncs {
        let resyncs = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&resyncs);
        stage.add_sink(move |_: &Stage, change: &usd::CommittedChange<'_>| {
            sink.borrow_mut()
                .push(change.resynced.iter().map(ToString::to_string).collect());
        });
        resyncs
    }

    /// A root prim, and the sublayer the drain tests add.
    const PLAIN: &str = "#usda 1.0\ndef \"P\" {}\n";
    const SUBLAYER: (&str, &str) = ("b.usda", "#usda 1.0\ndef \"B\" {}\n");
    const REFERENCED: &str = "#usda 1.0\ndef \"P\" (references = @a.usda@</A>) {}\n";
    const TARGET: &str = "#usda 1.0\ndef \"A\" {\n    def \"Inner\" {}\n}\n";

    /// A read whose layer load commits to a layer of the stage answers from
    /// the composition that edit makes, and the edit's notice waits for the
    /// next drain to deliver it.
    #[test]
    fn read_reconciles_load_commit() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, hook) = hooked_stage(dir.path(), REFERENCED, &[("a.usda", TARGET)], "a.usda")?;
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        hook.replace(Some(Box::new(move || define_raw(&root, "/Late"))));
        let resyncs = record_resyncs(&stage);

        assert!(stage.prim("/P/Inner")?.is_valid()?);
        assert!(
            stage.composition.pending_is_empty(),
            "the read reconciled the load's edit"
        );
        assert!(resyncs.borrow().is_empty(), "a read delivers nothing");
        assert!(stage.prim("/Late")?.is_valid()?);
        stage.process_pending();
        assert_eq!(*resyncs.borrow(), [vec!["/Late".to_owned()]]);
        Ok(())
    }

    /// A pass the drain it runs inside settles stops when its loads commit
    /// to a layer of the stage, leaving the edit queued for that drain.
    #[test]
    fn taken_fixpoint_interrupts() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, hook) = hooked_stage(dir.path(), REFERENCED, &[("a.usda", TARGET)], "a.usda")?;
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        hook.replace(Some(Box::new(move || define_raw(&root, "/Late"))));

        let inner = sdf::path("/P/Inner")?;
        let stopped = stage.composition.fixpoint(
            |view, cache| cache.is_populated(view, &inner),
            composition::Settled::Taken,
            &stage,
        );
        assert!(matches!(stopped, Err(composition::Interrupted::NewWork)));
        assert!(!stage.composition.pending_is_empty(), "the edit waits for the drain");
        stage.process_pending();
        assert!(stage.prim("/Late")?.is_valid()?);
        Ok(())
    }

    /// User code a drain's layer load runs finds the stage part-composed: a
    /// fallible read fails with `Busy`, and an infallible accessor panics.
    /// The drain then finishes.
    #[test]
    fn drain_reentry_busy() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, hook) = hooked_stage(dir.path(), PLAIN, &[SUBLAYER], "b.usda")?;
        let seen = Rc::new(Cell::new(None));
        let reader = stage.clone();
        let record = Rc::clone(&seen);
        hook.replace(Some(Box::new(move || {
            let read = reader.prim("/P").expect("a prim path").is_valid();
            let busy = matches!(read, Err(crate::Error::Query(error)) if error.is_busy());
            let panicked = panics_part_composed(|| {
                reader.layer_count();
            });
            record.set(Some((busy, panicked)));
        })));
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        sublayer_raw(&root);

        stage.process_pending();
        assert_eq!(seen.get(), Some((true, true)), "busy, then a panic");
        assert!(stage.prim("/B")?.is_valid()?, "the drain finished");
        Ok(())
    }

    /// An edit a drain's layer load commits is applied after the edits the
    /// drain took, and its notice follows theirs.
    #[test]
    fn drain_load_commit_ordered() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, hook) = hooked_stage(dir.path(), PLAIN, &[SUBLAYER], "b.usda")?;
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        let late = root.clone();
        hook.replace(Some(Box::new(move || define_raw(&late, "/C"))));
        let resyncs = record_resyncs(&stage);

        // A: a sublayer whose load commits C. B: a prim, queued behind A.
        // Both queue while the stage's layers are borrowed, and one drain
        // takes them.
        {
            let _layers = stage.layers();
            sublayer_raw(&root);
            define_raw(&root, "/Q");
        }
        assert!(resyncs.borrow().is_empty(), "queued behind the borrow");
        stage.process_pending();

        let resyncs = resyncs.borrow();
        assert_eq!(resyncs.len(), 3, "{resyncs:?}");
        assert_eq!(resyncs[1], ["/Q"]);
        assert_eq!(resyncs[2], ["/C"]);
        Ok(())
    }
    /// The message `read` panics with, if it panics.
    fn panic_message(read: impl FnOnce()) -> Option<String> {
        let payload = panic::catch_unwind(AssertUnwindSafe(read)).err()?;
        match payload.downcast::<String>() {
            Ok(message) => Some(*message),
            Err(payload) => payload.downcast_ref::<&str>().map(|message| (*message).to_owned()),
        }
    }

    /// Whether `read` panics with the message a part-composed stage gives.
    fn panics_part_composed(read: impl FnOnce()) -> bool {
        panic_message(read).is_some_and(|message| message.contains("user code a layer load runs"))
    }

    /// User code a read's layer load runs finds the stage part-composed, as
    /// one a drain's load runs does.
    #[test]
    fn read_load_reentry_busy() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, hook) = hooked_stage(dir.path(), REFERENCED, &[("a.usda", TARGET)], "a.usda")?;
        let seen = Rc::new(Cell::new(None));
        let reader = stage.clone();
        let record = Rc::clone(&seen);
        hook.replace(Some(Box::new(move || {
            let read = reader.prim("/P").expect("a prim path").is_valid();
            let busy = matches!(read, Err(crate::Error::Query(error)) if error.is_busy());
            record.set(Some((
                busy,
                panics_part_composed(|| {
                    reader.layer_count();
                }),
            )));
        })));

        assert!(stage.prim("/P/Inner")?.is_valid()?);
        assert_eq!(seen.get(), Some((true, true)), "busy, then a panic");
        Ok(())
    }

    /// A resolver that commits on every open of an asset that cannot be read
    /// does not keep a read retrying it: the edit was committed before the
    /// failure it would clear.
    #[test]
    fn load_commit_keeps_failure() -> Result<()> {
        let dir = tempfile::tempdir()?;
        fs::write(
            dir.path().join("root.usda"),
            "#usda 1.0\ndef \"P\" (references = @broken.usda@</X>) {}\n",
        )?;
        fs::write(dir.path().join("broken.usda"), "not a layer")?;
        let root: Rc<RefCell<Option<sdf::LayerHandle>>> = Rc::default();
        let opens = Rc::new(Cell::new(0));
        let (log, count) = (Rc::clone(&root), Rc::clone(&opens));
        let resolver = sdf::layer_registry::tests::HookResolver::new(move |resolved| {
            if resolved.file_name().is_some_and(|file| file == "broken.usda") {
                count.set(count.get() + 1);
                assert!(count.get() < 10, "the read keeps retrying the asset");
                let layer = log.borrow().clone().expect("the stage is open");
                define_raw(&layer, &format!("/Log{}", count.get()));
            }
        });
        let stage = Stage::builder()
            .resolver(resolver)
            .open(&dir.path().join("root.usda").to_string_lossy())?;
        root.replace(stage.layer_handle(stage.root_layer().identifier()));

        assert!(stage.prim("/P")?.is_valid()?);
        assert_eq!(opens.get(), 1);
        assert!(stage.prim("/Log1")?.is_valid()?);
        Ok(())
    }

    /// A stage over `root` whose resolver runs `open` before opening each
    /// asset, by file name, and `identify` before identifying each asset
    /// path.
    fn resolving_stage(
        dir: &FsPath,
        root: &str,
        files: &[(&str, &str)],
        open: impl Fn(&str) + 'static,
        identify: impl Fn(&str) + 'static,
    ) -> Result<Stage> {
        fs::write(dir.join("root.usda"), root)?;
        for (file, content) in files {
            fs::write(dir.join(file), content)?;
        }
        let resolver = sdf::layer_registry::tests::HookResolver::new(move |resolved| {
            if let Some(file) = resolved.file_name().and_then(|file| file.to_str()) {
                open(file);
            }
        })
        .on_identify(identify);
        Stage::builder()
            .resolver(resolver)
            .open(&dir.join("root.usda").to_string_lossy())
    }

    /// A drain that runs while an unrelated panic unwinds, and finishes,
    /// leaves the stage sound.
    #[test]
    fn unwind_drain_sound() -> Result<()> {
        struct EditOnDrop(sdf::LayerHandle);
        impl Drop for EditOnDrop {
            fn drop(&mut self) {
                define_raw(&self.0, "/Q");
            }
        }
        let dir = tempfile::tempdir()?;
        let (stage, _hook) = hooked_stage(dir.path(), PLAIN, &[], "none.usda")?;
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");

        let message = panic_message(|| {
            let _edit = EditOnDrop(root.clone());
            panic!("an unrelated failure");
        });
        assert_eq!(message.as_deref(), Some("an unrelated failure"));
        assert!(
            stage.prim("/Q")?.is_valid()?,
            "the drain applied the edit, and the stage is sound"
        );
        Ok(())
    }

    /// A read whose loads join one layer and then panic opening the next
    /// poisons the stage: the joined layer is left unwired.
    #[test]
    fn read_load_panic_poisons() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let stage = resolving_stage(
            dir.path(),
            "#usda 1.0\ndef \"P\" (references = [@a.usda@</A>, @c.usda@</C>]) {}\n",
            &[
                ("a.usda", "#usda 1.0\ndef \"A\" {}\n"),
                ("c.usda", "#usda 1.0\ndef \"C\" {}\n"),
            ],
            |file| assert!(file != "c.usda", "the resolver failed"),
            |_| {},
        )?;

        let message = panic_message(|| {
            let _ = stage.prim("/P").expect("a prim path").is_valid();
        });
        assert!(message.is_some_and(|message| message.contains("resolver failed")));
        let read = stage.prim("/P")?.is_valid();
        assert!(
            matches!(read, Err(crate::Error::Query(pcp::QueryError::Poisoned(None)))),
            "{read:?}"
        );
        Ok(())
    }

    /// A stage over `PLAIN` with a sink recording its resyncs, and its root
    /// layer's handle, poisoned by a resolver panic while a sublayer's change
    /// is applied.
    fn poisoned_stage(dir: &FsPath) -> Result<(Stage, Resyncs, sdf::LayerHandle)> {
        let armed = Rc::new(Cell::new(false));
        let trigger = Rc::clone(&armed);
        let stage = resolving_stage(
            dir,
            PLAIN,
            &[],
            |_| {},
            move |asset_path| {
                if trigger.get() && asset_path == "poison.usda" {
                    panic!("the resolver failed");
                }
            },
        )?;
        let resyncs = record_resyncs(&stage);
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        {
            let _layers = stage.layers();
            root.edit(|e| {
                e.pseudo_root_mut()
                    .expect("a layer has a pseudo-root")
                    .set_sublayers(["poison.usda"]);
                Ok(())
            })?;
        }
        armed.set(true);
        let message = panic_message(|| stage.process_pending());
        assert_eq!(message.as_deref(), Some("the resolver failed"));
        armed.set(false);
        Ok((stage, resyncs, root))
    }

    /// A panic in user code that applying a change runs poisons the stage:
    /// fallible calls fail naming the transaction, an infallible accessor
    /// panics, and no sink hears of the change or a later one.
    #[test]
    fn apply_panic_poisons() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, resyncs, root) = poisoned_stage(dir.path())?;
        let read = stage.prim("/P")?.is_valid();
        assert!(
            matches!(read, Err(crate::Error::Query(pcp::QueryError::Poisoned(Some(_))))),
            "{read:?}"
        );
        let accessor = panic_message(|| {
            stage.layer_count();
        });
        assert!(accessor.is_some_and(|message| message.contains("poisoned")));
        define_raw(&root, "/Late");
        assert!(resyncs.borrow().is_empty(), "no sink hears of a change");
        Ok(())
    }

    /// A fallible call on a poisoned stage fails, and a mutation that cannot
    /// fail panics, neither aborting.
    #[test]
    fn poisoned_calls_fail() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, ..) = poisoned_stage(dir.path())?;
        let found = stage.find_loadable("/");
        assert!(
            matches!(found, Err(crate::Error::Query(pcp::QueryError::Poisoned(_)))),
            "{found:?}"
        );
        let muted = panic_message(|| stage.mute_layer("other.usda"));
        assert!(muted.is_some_and(|message| message.contains("poisoned")));
        Ok(())
    }

    /// A panic while a drain loads a sublayer an edit demanded poisons the
    /// stage, and the edits queued behind it are not applied.
    #[test]
    fn drain_load_panic_poisons() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, hook) = hooked_stage(dir.path(), PLAIN, &[SUBLAYER], "b.usda")?;
        hook.replace(Some(Box::new(|| panic!("the resolver failed"))));
        let resyncs = record_resyncs(&stage);
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        {
            let _layers = stage.layers();
            sublayer_raw(&root);
            define_raw(&root, "/Q");
        }

        let message = panic_message(|| stage.process_pending());
        assert_eq!(message.as_deref(), Some("the resolver failed"));
        let read = stage.prim("/Q")?.is_valid();
        assert!(
            matches!(read, Err(crate::Error::Query(pcp::QueryError::Poisoned(Some(_))))),
            "{read:?}"
        );
        assert!(resyncs.borrow().is_empty());
        Ok(())
    }

    /// A panic while a drain retries the failed loads poisons the stage.
    #[test]
    fn retry_panic_poisons() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let armed = Rc::new(Cell::new(false));
        let trigger = Rc::clone(&armed);
        let stage = resolving_stage(
            dir.path(),
            "#usda 1.0\n(\n    subLayers = [@late.usda@]\n)\n",
            &[],
            move |file| {
                if file == "late.usda" && trigger.get() {
                    panic!("the resolver failed");
                }
            },
            |_| {},
        )?;
        assert!(!stage.prim("/Late")?.is_valid()?, "the sublayer is missing");
        fs::write(dir.path().join("late.usda"), "#usda 1.0\ndef \"Late\" {}\n")?;
        armed.set(true);
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        {
            let _layers = stage.layers();
            define_raw(&root, "/Q");
        }

        let message = panic_message(|| stage.process_pending());
        assert_eq!(message.as_deref(), Some("the resolver failed"));
        let read = stage.prim("/Q")?.is_valid();
        assert!(
            matches!(read, Err(crate::Error::Query(pcp::QueryError::Poisoned(None)))),
            "{read:?}"
        );
        Ok(())
    }

    /// A panic while a read builds an index, anchoring a reference through
    /// the resolver, poisons the stage.
    #[test]
    fn index_build_panic_poisons() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let armed = Rc::new(Cell::new(false));
        let trigger = Rc::clone(&armed);
        let stage = resolving_stage(
            dir.path(),
            REFERENCED,
            &[("a.usda", TARGET)],
            |_| {},
            move |asset_path| {
                if trigger.get() && asset_path == "a.usda" {
                    panic!("the resolver failed");
                }
            },
        )?;
        armed.set(true);

        let message = panic_message(|| {
            let _ = stage.prim("/P/Inner").expect("a prim path").is_valid();
        });
        assert_eq!(message.as_deref(), Some("the resolver failed"));
        armed.set(false);
        let read = stage.prim("/P")?.is_valid();
        assert!(
            matches!(read, Err(crate::Error::Query(pcp::QueryError::Poisoned(None)))),
            "{read:?}"
        );
        Ok(())
    }

    /// A panic while an unmute rejoins a sublayer poisons the stage.
    #[test]
    fn unmute_panic_poisons() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let (stage, hook) = hooked_stage(
            dir.path(),
            "#usda 1.0\n(\n    subLayers = [@b.usda@]\n)\n",
            &[SUBLAYER],
            "b.usda",
        )?;
        let sublayer = dir.path().join("b.usda").to_string_lossy().into_owned();
        stage.mute_layer(sublayer.as_str());
        hook.replace(Some(Box::new(|| panic!("the resolver failed"))));

        let message = panic_message(|| stage.unmute_layer(&sublayer));
        assert_eq!(message.as_deref(), Some("the resolver failed"));
        let read = stage.prim("/B")?.is_valid();
        assert!(
            matches!(read, Err(crate::Error::Query(pcp::QueryError::Poisoned(None)))),
            "{read:?}"
        );
        Ok(())
    }

    /// A poisoned stage tells its sinks nothing of an edit to its layer, not
    /// even before it commits, and the edit still lands.
    #[test]
    fn poisoned_edit_unheard() -> Result<()> {
        struct Heard(Rc<Cell<usize>>);
        impl StageSink for Heard {
            fn before_commit(&self, _: &Stage, _: &usd::PendingChange<'_>) {
                self.0.set(self.0.get() + 1);
            }
        }
        let dir = tempfile::tempdir()?;
        let (stage, _, root) = poisoned_stage(dir.path())?;
        let heard = Rc::new(Cell::new(0));
        stage.add_sink(Heard(Rc::clone(&heard)));

        define_raw(&root, "/Late");
        assert_eq!(heard.get(), 0);
        let late = sdf::path("/Late")?;
        assert!(root.read(|layer| layer.data().has_spec(&late))?);
        Ok(())
    }

    /// A panic that user code catches inside a drain, run while an unrelated
    /// panic unwinds, still poisons the stage.
    #[test]
    fn caught_unwind_panic_poisons() -> Result<()> {
        struct EditOnDrop(sdf::LayerHandle);
        impl Drop for EditOnDrop {
            fn drop(&mut self) {
                let caught = panic::catch_unwind(AssertUnwindSafe(|| {
                    self.0
                        .edit(|e| {
                            e.pseudo_root_mut()
                                .expect("a layer has a pseudo-root")
                                .set_sublayers(["poison.usda"]);
                            Ok(())
                        })
                        .expect("the layer is free");
                }));
                assert!(caught.is_err(), "the drain's resolver panicked");
            }
        }
        let dir = tempfile::tempdir()?;
        let stage = resolving_stage(
            dir.path(),
            PLAIN,
            &[],
            |_| {},
            |asset_path| {
                assert!(asset_path != "poison.usda", "the resolver failed");
            },
        )?;
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");

        let message = panic_message(|| {
            let _edit = EditOnDrop(root.clone());
            panic!("an unrelated failure");
        });
        assert_eq!(message.as_deref(), Some("an unrelated failure"));
        let read = stage.prim("/P")?.is_valid();
        assert!(
            matches!(read, Err(crate::Error::Query(pcp::QueryError::Poisoned(_)))),
            "{read:?}"
        );
        Ok(())
    }

    /// A sink that poisons the stage, catching the panic, ends the delivery
    /// it runs in: neither the sinks after it nor the notices queued after
    /// its own are delivered to.
    #[test]
    fn delivery_stops_when_poisoned() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let armed = Rc::new(Cell::new(false));
        let trigger = Rc::clone(&armed);
        let stage = resolving_stage(
            dir.path(),
            REFERENCED,
            &[("a.usda", TARGET)],
            |_| {},
            move |asset_path| {
                if trigger.get() && asset_path == "a.usda" {
                    panic!("the resolver failed");
                }
            },
        )?;
        let delivered = Rc::new(Cell::new(0));
        let count = Rc::clone(&delivered);
        stage.add_sink(move |stage: &Stage, _: &usd::CommittedChange<'_>| {
            count.set(count.get() + 1);
            armed.set(true);
            let read = panic::catch_unwind(AssertUnwindSafe(|| {
                let _ = stage.prim("/P/Inner").expect("a prim path").is_valid();
            }));
            assert!(read.is_err(), "the read's resolver panicked");
        });
        let after = Rc::new(Cell::new(0));
        let later = Rc::clone(&after);
        stage.add_sink(move |_: &Stage, _: &usd::CommittedChange<'_>| later.set(later.get() + 1));
        let root = stage.layer_handle(stage.root_layer().identifier()).expect("the root");
        {
            let _layers = stage.layers();
            define_raw(&root, "/X");
            define_raw(&root, "/Y");
        }

        stage.process_pending();
        assert_eq!(delivered.get(), 1, "the second notice is not delivered");
        assert_eq!(
            after.get(),
            0,
            "nor is the first, to the sinks after the one that poisoned"
        );
        Ok(())
    }
}
