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
//! - [`StageBuilder::initial_load_set`] controls whether payload arcs are
//!   loaded during stage population.
//! - [`StageBuilder::population_mask`] limits the prim working set exposed by
//!   stage queries and traversal.
//!
//! [LIVERPS]: https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html

use std::cell::{Cell, Ref, RefCell};
use std::rc::Rc;

use anyhow::Result;
use bitflags::bitflags;

use crate::{ar, layer, pcp, sdf};

use super::interp::{self, InterpolationType};

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
/// the variant.
//
// TODO: arc-based constructor (`for_node`) routing writes into a specific
// reference / specialize arc, mirroring C++
// `UsdEditTarget(UsdPrim, UsdEditTarget::Reference)`. Needs a narrow
// `pcp::IndexCache` accessor exposing the strongest matching node's `map_to_root`
// plus the per-layer sublayer offset.
//
// TODO: re-map embedded relationship / connection target paths in
// `map_to_spec_path` (C++ `MapToSpecPath` step 2), rejecting paths whose
// embedded targets fall outside the mapping's co-domain.
//
// TODO: validate target by `pcp::LayerStackIdentifier` instead of a bare
// `usize` so an `EditTarget` constructed against one stage can't be applied
// to another, and so layer reordering (when supported) doesn't silently
// retarget writes.
//
// TODO: add convenience constructors like `EditTarget::root(&stage)` /
// `EditTarget::session(&stage)` so callers don't have to do
// `session_layer_count`-arithmetic to address common slots.
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
}

impl EditTarget {
    /// Edit target pointing at the layer with the given identifier, with an
    /// identity path mapping (scene path == spec path).
    pub fn for_layer(layer_identifier: impl Into<String>) -> Self {
        Self {
            layer_identifier: layer_identifier.into(),
            mapping: pcp::MapFunction::identity(),
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
    /// Mirrors C++ `UsdEditTarget::MapToSpecPath`, which queries the mapping in
    /// the target-to-source direction.
    pub fn map_to_spec_path(&self, scene_path: &sdf::Path) -> Option<sdf::Path> {
        self.mapping.map_target_to_source(scene_path)
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
        // A `drop` must be infallible and must not re-enter the composition
        // cache. The saved target was valid when the guard was created, so
        // restoring it needs no validation — assign the field directly.
        *self.stage.edit_target.borrow_mut() = self.saved.clone();
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

    /// Replace the current edit target. Subsequent authoring calls write to
    /// the new target's layer.
    ///
    /// Validates that `target.layer_identifier()` names a layer in this stage so
    /// a bad target surfaces here, not on some later unrelated authoring call.
    pub fn set_edit_target(&self, target: EditTarget) -> Result<(), StageAuthoringError> {
        if self.layers().id_of(target.layer_identifier()).is_none() {
            return Err(StageAuthoringError::LayerNotFound {
                layer: target.layer_identifier().to_string(),
            });
        }

        *self.edit_target.borrow_mut() = target;
        Ok(())
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
            // Snapshot pre-author state so an idempotent call (existing
            // spec, matching specifier) emits an empty `ChangeList` instead
            // of triggering a stale-index drop.
            let data = layer.data();
            let had_spec = data.has_spec(&layer_path);
            let prior_specifier_matches = had_spec
                && matches!(
                    data.try_get(&layer_path, sdf::FieldKey::Specifier.as_str())
                        .ok()
                        .flatten()
                        .as_deref(),
                    Some(sdf::Value::Specifier(sdf::Specifier::Def))
                );

            let auto_ancestors = layer.missing_prim_ancestors(&layer_path);
            layer.create_prim(layer_path.clone(), sdf::Specifier::Def, "")?;
            let mut cl = sdf::ChangeList::new();
            if !had_spec {
                let entry = cl.entry_mut(&layer_path);
                entry.flags |= sdf::ChangeFlags::ADD_NON_INERT_PRIM;
                entry.info_changed.insert(sdf::FieldKey::Specifier.as_str());
            } else if !prior_specifier_matches {
                cl.entry_mut(&layer_path)
                    .info_changed
                    .insert(sdf::FieldKey::Specifier.as_str());
            }
            for anc in auto_ancestors {
                cl.entry_mut(&anc).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
            }
            Ok(cl)
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
            // `Layer::override_prim` is idempotent at the leaf when a spec
            // already exists. Record `ADD_INERT_PRIM` only for newly created
            // specs; auto-created ancestors are emitted unconditionally
            // because `missing_prim_ancestors` already filters them.
            let had_spec = layer.data().has_spec(&layer_path);
            let auto_ancestors = layer.missing_prim_ancestors(&layer_path);
            layer.override_prim(layer_path.clone())?;
            let mut cl = sdf::ChangeList::new();
            if !had_spec {
                cl.entry_mut(&layer_path).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
            }
            for anc in auto_ancestors {
                cl.entry_mut(&anc).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
            }
            Ok(cl)
        })?;
        Ok(super::Prim::new(self, path))
    }

    /// Author an attribute spec at a property path (e.g. `/World/Mesh.points`)
    /// on the edit target's layer with default variability `Varying` and
    /// `custom = true`, matching C++ `UsdPrim::CreateAttribute`'s generic
    /// overloads. Override the defaults via the returned [`Attribute`] handle's
    /// fluent setters.
    pub fn create_attribute(
        &self,
        path: impl Into<sdf::Path>,
        type_name: impl Into<String>,
    ) -> Result<super::Attribute, StageAuthoringError> {
        let path = path.into();
        let type_name = type_name.into();
        self.with_target_layer_at(&path, |layer, layer_path| {
            // The owning prim and all its missing ancestors get
            // auto-created as `over` specs by `create_attribute`.
            let owning_prim = layer_path.prim_path();
            let auto_ancestors = layer.missing_prim_chain_inclusive(&owning_prim);
            layer.create_attribute(layer_path.clone(), type_name, sdf::Variability::Varying, true)?;
            let mut cl = sdf::ChangeList::new();
            cl.entry_mut(&layer_path).flags |= sdf::ChangeFlags::ADD_PROPERTY;
            for anc in auto_ancestors {
                cl.entry_mut(&anc).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
            }
            Ok(cl)
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
            let owning_prim = layer_path.prim_path();
            let auto_ancestors = layer.missing_prim_chain_inclusive(&owning_prim);
            layer.create_relationship(layer_path.clone(), sdf::Variability::Varying, true)?;
            let mut cl = sdf::ChangeList::new();
            cl.entry_mut(&layer_path).flags |= sdf::ChangeFlags::ADD_PROPERTY;
            for anc in auto_ancestors {
                cl.entry_mut(&anc).flags |= sdf::ChangeFlags::ADD_INERT_PRIM;
            }
            Ok(cl)
        })?;
        Ok(super::Relationship::new(self, path))
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
            // Skip cache invalidation when the value isn't changing.
            // `defaultPrim` is stored as a `Token`; treat a matching
            // `String` opinion as equivalent (the Sdf-tier setter writes
            // `Token`, but a layer loaded from text might surface either).
            let prior = layer
                .data()
                .try_get(&sdf::Path::abs_root(), sdf::FieldKey::DefaultPrim.as_str())
                .ok()
                .flatten();
            let unchanged = matches!(
                prior.as_deref(),
                Some(sdf::Value::Token(s) | sdf::Value::String(s)) if s == &name
            );

            layer.set_default_prim(name)?;
            let mut cl = sdf::ChangeList::new();
            if !unchanged {
                cl.entry_mut(&sdf::Path::abs_root())
                    .info_changed
                    .insert(sdf::FieldKey::DefaultPrim.as_str());
            }
            Ok(cl)
        })
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
    /// The one error we can short-circuit is [`sdf::AuthoringError::ReadOnly`],
    /// which is detected before any layer state changes.
    pub(super) fn with_target_layer_at<F>(&self, scene_path: &sdf::Path, f: F) -> Result<bool, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer, sdf::Path) -> Result<sdf::ChangeList, sdf::AuthoringError>,
    {
        // Read the target identifier and mapped spec path under a short borrow
        // of `edit_target` (which owns a heap `MapFunction`), releasing it
        // before the layer borrow below.
        let (identifier, spec_path) = {
            let target = self.edit_target.borrow();
            let spec_path =
                target
                    .map_to_spec_path(scene_path)
                    .ok_or_else(|| StageAuthoringError::OutsideEditTarget {
                        path: scene_path.clone(),
                    })?;
            (target.layer_identifier.clone(), spec_path)
        };
        let (layer_id, result) = {
            let mut layers = self.layers.borrow_mut();
            let layer_id = layers
                .id_of(&identifier)
                .ok_or(StageAuthoringError::LayerNotFound { layer: identifier })?;
            let node = layers.get_mut(layer_id).expect("id_of returned a live id");
            (layer_id, f(&mut node.layer, spec_path))
        };
        self.finalize_layer(layer_id, result)
    }

    /// Borrow the stage's root layer, hand it to `f`, then drive cache
    /// invalidation from the closure's [`sdf::ChangeList`]. See
    /// [`Stage::with_target_layer_at`] for the contract. Unlike that method,
    /// this ignores the edit target and its mapping — `defaultPrim` is a
    /// root-layer field authored at `abs_root` verbatim.
    fn with_root_layer<F>(&self, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer) -> Result<sdf::ChangeList, sdf::AuthoringError>,
    {
        let layer_id = self
            .layers
            .borrow()
            .root_id()
            .ok_or(StageAuthoringError::OutsideEditTarget {
                path: sdf::Path::abs_root(),
            })?;
        let result = {
            let mut layers = self.layers.borrow_mut();
            let node = layers.get_mut(layer_id).expect("root_id refers to a live layer");
            f(&mut node.layer)
        };
        self.finalize_layer(layer_id, result).map(|_| ())
    }

    /// Translate a Layer-tier authoring result into the Stage error type and
    /// invalidate the composition cache via [`pcp::Changes`]. An empty
    /// change list short-circuits with no invalidation; a non-empty list is
    /// classified and applied. Post-mutation errors fall back to a
    /// stage-wide blow-out because the layer may be in a partial state.
    //
    // TODO: the error-path fallback to layer-stack-wide reset is
    // conservative. Once `Layer` authoring methods either complete
    // atomically or return a "partial mutation up to here" marker, the
    // fallback can be narrowed to just the paths the closure touched
    // before failing.
    fn finalize_layer(
        &self,
        layer_id: pcp::LayerId,
        result: Result<sdf::ChangeList, sdf::AuthoringError>,
    ) -> Result<bool, StageAuthoringError> {
        match result {
            Ok(cl) if cl.is_empty() => Ok(false),
            Ok(cl) => {
                let mut changes = pcp::Changes::new();
                let edits = [(layer_id, cl)];
                {
                    let graph = self.layers.borrow();
                    let cache = self.cache.borrow();
                    changes.did_change(&cache, &graph, &edits);
                }
                let mut graph = self.layers.borrow_mut();
                let mut cache = self.cache.borrow_mut();
                changes.apply(&mut cache, &mut graph);
                Ok(true)
            }
            Err(e) => {
                if !matches!(e, sdf::AuthoringError::ReadOnly { .. }) {
                    // Conservatively drop every cached index on post-mutation
                    // failure (the layer may be in a partial state). `SIGNIFICANT`
                    // alone is enough — `apply` routes it through
                    // `clear_all_indices` and the layer graph cannot have been
                    // affected by a failing prim/property edit.
                    let mut changes = pcp::Changes::new();
                    changes.layer_stack |= pcp::LayerStackChanges::SIGNIFICANT;
                    let mut graph = self.layers.borrow_mut();
                    let mut cache = self.cache.borrow_mut();
                    changes.apply(&mut cache, &mut graph);
                }
                Err(StageAuthoringError::Layer(e))
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
        self.muted.borrow_mut().insert(identifier.into());
    }

    /// Removes a layer identifier from the muted set.
    pub fn unmute_layer(&self, identifier: &str) {
        self.muted.borrow_mut().remove(identifier);
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
    pub fn initial_load_set(&self) -> InitialLoadSet {
        self.initial_load_set
    }

    /// Returns the population mask used by this stage.
    pub fn population_mask(&self) -> &StagePopulationMask {
        &self.population_mask
    }

    /// Returns the session layer identifier, if one was provided.
    pub fn session_layer(&self) -> Option<String> {
        let layers = self.layers();
        layers
            .session_layers()
            .first()
            .map(|&id| layers.identifier(id).to_string())
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    ///
    /// When a session layer is present, `defaultPrim` is still read from
    /// the root layer (not the session layer), matching C++ behavior.
    pub fn default_prim(&self) -> Option<String> {
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

    /// Returns the stage-level interpolation mode used by
    /// [`Stage::value_at`]. AOUSD §12.5 defaults this to
    /// [`InterpolationType::Linear`].
    pub fn interpolation_type(&self) -> InterpolationType {
        self.interpolation_type.get()
    }

    /// Override the stage-level interpolation mode at runtime.
    /// Cheap — no recomputation, the next [`Stage::value_at`] call
    /// reads the new mode.
    pub fn set_interpolation_type(&self, mode: InterpolationType) {
        self.interpolation_type.set(mode);
    }

    /// Returns the composed `timeSamples` for an attribute, or
    /// `None` when the attribute has none authored.
    ///
    /// This returns raw composed samples. Use [`Stage::value_at`] when you
    /// need the stage's [`InterpolationType`] applied to a specific time code.
    pub fn time_samples(&self, attr_path: impl Into<sdf::Path>) -> Result<Option<sdf::TimeSampleMap>> {
        Ok(match self.field::<sdf::Value>(attr_path, sdf::FieldKey::TimeSamples)? {
            Some(sdf::Value::TimeSamples(samples)) => Some(samples),
            _ => None,
        })
    }

    /// Evaluate an attribute's value at `time` under the stage's
    /// current [`InterpolationType`]. Mirrors C++ `UsdAttribute::Get`
    /// — the universal entry point for any consumer that needs a
    /// resolved value at a specific time code.
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
    ///
    /// For multi-frame queries against the same attribute, see
    /// [`Stage::time_samples`].
    pub fn value_at(&self, attr_path: impl Into<sdf::Path>, time: f64) -> Result<Option<sdf::Value>> {
        let attr_path = attr_path.into();
        if !self.mask_includes(&attr_path.prim_path()) {
            return Ok(None);
        }
        let interp_type = self.interpolation_type.get();
        let interp = |samples: &sdf::TimeSampleMap, t: f64| interp::evaluate(samples, t, interp_type);
        self.with_cache(|g, c| c.value_at(g, &attr_path, time, &interp))
    }

    /// Returns a [`Prim`](super::Prim) handle anchored to `path`. Mirrors C++
    /// `UsdStage::GetPrimAtPath`. The handle is a value-type `(stage, path)`
    /// wrapper; it is returned unconditionally and does not assert that a prim
    /// is composed at the path (query the handle to find out).
    pub fn prim_at(&self, path: impl Into<sdf::Path>) -> super::Prim {
        super::Prim::new(self, path.into().prim_path())
    }

    /// Returns an [`Attribute`](super::Attribute) handle anchored to `path`.
    /// Mirrors C++ `UsdStage::GetAttributeAtPath`. Like [`Self::prim_at`],
    /// the handle is returned unconditionally; query it to resolve a value.
    pub fn attribute_at(&self, path: impl Into<sdf::Path>) -> super::Attribute {
        super::Attribute::new(self, path.into())
    }

    /// Returns a [`Relationship`](super::Relationship) handle anchored to `path`.
    /// Mirrors C++ `UsdStage::GetRelationshipAtPath`.
    pub fn relationship_at(&self, path: impl Into<sdf::Path>) -> super::Relationship {
        super::Relationship::new(self, path.into())
    }

    /// Returns the composed list of root prim names (children of the pseudo-root).
    pub fn root_prims(&self) -> Result<Vec<String>> {
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
    // [`Self::filter_child_names`] and [`Self::population_mask`].

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
        let prim = self.prim_at(prim.clone());
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
    pub(crate) fn filter_child_names(&self, parent: &sdf::Path, children: Vec<String>) -> Vec<String> {
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
        let (parent_id, cl) = {
            let mut layers = self.layers.borrow_mut();
            let parent_id = layers.id_of(parent).ok_or_else(|| StageAuthoringError::LayerNotFound {
                layer: parent.to_string(),
            })?;
            let node = layers.get_mut(parent_id).expect("id_of returned a live id");
            let cl = node.layer.pseudo_root_mut().map(|mut root| {
                root.insert_sublayer(pos, identifier, offset);
                Self::sublayers_change_list()
            });
            (parent_id, cl)
        };
        let cl = cl.map_err(StageAuthoringError::Layer)?;
        self.layers.borrow_mut().ensure_layer(layer);
        self.finalize_layer(parent_id, Ok(cl))?;
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
        let (parent_id, cl) = {
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
            let cl = match authored {
                Some(entry) => {
                    let node = layers.get_mut(parent_id).expect("id_of returned a live id");
                    node.layer
                        .pseudo_root_mut()
                        .map(|mut root| root.remove_sublayer(&entry).then(Self::sublayers_change_list))
                }
                None => Ok(None),
            };
            (parent_id, cl)
        };
        match cl.map_err(StageAuthoringError::Layer)? {
            Some(cl) => {
                self.finalize_layer(parent_id, Ok(cl))?;
                Ok(true)
            }
            None => Ok(false),
        }
    }

    /// A pseudo-root [`sdf::ChangeList`] recording a `subLayers` /
    /// `subLayerOffsets` edit, so [`finalize_layer`](Self::finalize_layer)
    /// classifies it as a layer-stack rebuild.
    fn sublayers_change_list() -> sdf::ChangeList {
        let mut cl = sdf::ChangeList::new();
        let entry = cl.entry_mut(&sdf::Path::abs_root());
        entry.info_changed.insert(sdf::FieldKey::SubLayers.as_str());
        entry.info_changed.insert(sdf::FieldKey::SubLayerOffsets.as_str());
        cl
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
    /// attribute queries through [`Stage::value_at`]. Default per
    /// AOUSD §12.5 is [`InterpolationType::Linear`].
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
    pub fn initial_load_set(mut self, load_set: InitialLoadSet) -> Self {
        self.initial_load_set = load_set;
        self
    }

    /// Sets the stage population mask.
    pub fn population_mask(mut self, mask: StagePopulationMask) -> Self {
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
        // The root layer is the strongest authoring target by default; an
        // empty graph (no layers) has none, so the target names no layer and
        // resolves to nothing at author time.
        let edit_target = EditTarget::for_layer(graph.root_layer().map(sdf::Layer::identifier).unwrap_or_default());
        Stage(Rc::new(StageInner {
            layers: RefCell::new(graph),
            cache: RefCell::new(pcp::IndexCache::new(self.variant_fallbacks, collection_errors)),
            muted: RefCell::new(std::collections::HashSet::new()),
            initial_load_set: self.initial_load_set,
            population_mask: self.population_mask,
            interpolation_type: Cell::new(self.interpolation_type),
            edit_target: RefCell::new(edit_target),
        }))
    }
}

#[cfg(test)]
mod tests {

    /// The identifier of the stage's n-th layer (collection order), for tests
    /// that previously addressed layers by index.
    fn nth_identifier(stage: &Stage, n: usize) -> String {
        let layers = stage.layers();
        layers.identifier(layers.all_ids()[n]).to_string()
    }
    use super::*;
    use crate::gf;

    const VENDOR_COMPOSITION: &str = "vendor/usd-wg-assets/test_assets/foundation/stage_composition";

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    fn composition_path(relative: &str) -> String {
        format!("{}/{VENDOR_COMPOSITION}/{relative}", manifest_dir())
    }

    fn fixture_path(relative: &str) -> String {
        format!("{}/fixtures/{relative}", manifest_dir())
    }

    // Composed-scene query shims used throughout these tests: each routes
    // through the handle that now owns the query so the assertions stay terse.
    fn child_names(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
        stage.prim_at(path).child_names()
    }

    fn prop_names(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
        stage.prim_at(path).property_names()
    }

    fn connections(stage: &Stage, attr: &sdf::Path) -> Result<Vec<sdf::Path>> {
        stage.attribute_at(attr).connections()
    }

    fn rel_targets(stage: &Stage, rel: &sdf::Path) -> Result<Vec<sdf::Path>> {
        stage.relationship_at(rel).targets()
    }

    fn fwd_targets(stage: &Stage, rel: &sdf::Path) -> Result<Vec<sdf::Path>> {
        stage.relationship_at(rel).forwarded_targets()
    }

    // --- Basic stage opening (vendor/usd-wg-assets) ---

    #[test]
    fn missing_sublayer_retained() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n)\ndef \"Root\" {}\n",
        )?;

        let stage = Stage::open(root.to_str().unwrap())?;
        assert!(stage.composition_errors().iter().any(|error| matches!(
            error,
            pcp::Error::UnresolvedSublayer {
                asset_path,
                introduced_by,
            } if asset_path == "missing.usda" && introduced_by.ends_with("root.usda")
        )));
        assert!(stage.prim_at("/Root").is_valid()?);
        Ok(())
    }

    /// A direct arc to a `permission = private` site is retained as a
    /// composition error while the prim still composes (spec 10.3.3).
    #[test]
    fn arc_permission_denied_surfaced() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             ErrorPermissionDenied_root/usda/root.usd",
            manifest_dir()
        );
        let stage = StageBuilder::new().open(&path)?;

        // Querying /Model composes the private inherit and retains the error.
        assert!(stage.has_spec("/Model.attr")?, "private inherit must stay visible");
        assert!(
            stage
                .composition_errors()
                .iter()
                .any(|error| matches!(error, pcp::Error::ArcPermissionDenied { .. })),
            "composition_errors should contain the permission error"
        );

        Ok(())
    }

    /// A single-layer .usda file should load with correct defaultPrim and
    /// root prim list.
    #[test]
    fn open_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        assert_eq!(stage.layer_count(), 1);
        assert_eq!(stage.default_prim(), Some("World".to_string()));
        assert_eq!(stage.root_prims()?, vec!["World"]);

        Ok(())
    }

    /// Default traversal should visit active, loaded, defined, non-abstract prims.
    #[test]
    fn traverse_uses_default_predicate() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let mut prims = Vec::new();
        stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;

        assert_eq!(prims, vec!["/World", "/World/CubeActive"]);

        Ok(())
    }

    /// Exhaustive traversal should preserve raw composed hierarchy traversal.
    #[test]
    fn traverse_all_visits_every_composed_prim() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let mut prims = Vec::new();
        stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

        assert_eq!(prims, vec!["/World", "/World/CubeInactive", "/World/CubeActive"]);

        Ok(())
    }

    /// Reading a field from a single-layer stage should return the authored value.
    #[test]
    fn field_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        // The "active" metadata on CubeInactive should be false.
        let active = stage.field::<bool>("/World/CubeInactive", sdf::FieldKey::Active)?;
        assert_eq!(active, Some(false));

        // CubeActive has active = true.
        let active = stage.field::<bool>("/World/CubeActive", sdf::FieldKey::Active)?;
        assert_eq!(active, Some(true));

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

    // --- Sublayer composition ---

    /// sublayer_override.usda sublayers sublayer_base.usda. Both layers define
    /// /World/Cube but with different displayColor values. The stronger (override)
    /// layer's opinion should win (first-opinion-wins rule).
    #[test]
    fn sublayer_stronger_opinion_wins() -> Result<()> {
        let path = fixture_path("sublayer_override.usda");
        let stage = Stage::open(&path)?;

        assert_eq!(stage.layer_count(), 2);

        // /World/Cube.primvars:displayColor is overridden to blue [(0,0,1)] in
        // the stronger layer, base has red [(1,0,0)].
        let prop_path = sdf::Path::new("/World/Cube")?.append_property("primvars:displayColor")?;
        let value: Option<sdf::Value> = stage.field(&prop_path, sdf::FieldKey::Default)?;
        assert!(value.is_some(), "displayColor should have a composed value");

        // The composed value must come from the stronger layer (blue),
        // not the weaker layer (red). Verify by checking it's not the base red.
        let value = value.unwrap();
        let base_red = sdf::Value::Vec3fVec(vec![gf::vec3f(1.0, 0.0, 0.0)]);
        assert_ne!(value, base_red, "stronger layer opinion should win over weaker");

        Ok(())
    }

    /// A prim defined only in the stronger sublayer should appear in composed
    /// children alongside prims from the weaker layer.
    #[test]
    fn sublayer_children_union() -> Result<()> {
        let path = fixture_path("sublayer_override.usda");
        let stage = Stage::open(&path)?;

        let children = child_names(&stage, "/World")?;
        // Override layer adds Sphere; base layer defines Cube.
        assert!(children.contains(&"Cube".to_string()), "Cube from base layer");
        assert!(children.contains(&"Sphere".to_string()), "Sphere from override layer");

        Ok(())
    }

    /// The sublayer_same_folder vendor test asset should open correctly with
    /// 2 layers and expose the sublayer's prims through composition.
    #[test]
    fn sublayer_prims_from_weaker_layer() -> Result<()> {
        let path = composition_path("subLayer/sublayer_same_folder.usda");
        let stage = Stage::open(&path)?;

        assert_eq!(stage.layer_count(), 2);
        assert_eq!(stage.default_prim(), Some("World".to_string()));

        // The weaker sublayer (_stage.usda) defines /World/Cube.
        let mut prims = Vec::new();
        stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;
        assert!(prims.contains(&"/World/Cube".to_string()));

        Ok(())
    }

    /// The active.usda vendor test has prims with active=true/false metadata.
    /// Verify field resolution returns the correct authored values.
    #[test]
    fn field_active_metadata() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let inactive: Option<bool> = stage.field("/World/CubeInactive", sdf::FieldKey::Active)?;
        assert_eq!(inactive, Some(false));

        let active = stage.field::<bool>("/World/CubeActive", sdf::FieldKey::Active)?;
        assert_eq!(active, Some(true));

        Ok(())
    }

    // --- Reference composition ---

    /// An external reference with defaultPrim should pull the referenced prim's
    /// children into the referencing prim's namespace.
    /// ref_external.usda: /World/MyPrim references ref_target.usda (defaultPrim="Source").
    /// ref_target.usda defines /Source/Child with displayColor.
    #[test]
    fn reference_external_default_prim() -> Result<()> {
        let path = fixture_path("ref_external.usda");
        let stage = Stage::open(&path)?;

        // /World/MyPrim should exist via the reference.
        assert!(stage.has_spec("/World/MyPrim")?);

        // /World/MyPrim/Child should be reachable via namespace remapping.
        let children = child_names(&stage, "/World/MyPrim")?;
        assert!(
            children.contains(&"Child".to_string()),
            "referenced children should be visible"
        );

        Ok(())
    }

    /// Vendor test: reference_same_folder.usda references _stage.usda with
    /// defaultPrim. The referenced layer's /World/Cube should appear under the
    /// referencing prim.
    #[test]
    fn reference_default_prim_from_external_layer() -> Result<()> {
        let path = composition_path("references/reference_same_folder.usda");
        let stage = Stage::open(&path)?;

        // /World references _stage.usda's defaultPrim ("World"),
        // so /World/Cube should come from the referenced layer.
        let children = child_names(&stage, "/World")?;
        assert!(
            children.contains(&"Cube".to_string()),
            "Cube from referenced layer should appear under /World"
        );

        Ok(())
    }

    /// An external reference with an explicit prim path should remap the
    /// target prim into the referencing prim's namespace.
    /// ref_prim.usda: /World/RefPrim references @ref_target.usda@</Source>.
    #[test]
    fn reference_explicit_prim_path() -> Result<()> {
        let path = fixture_path("ref_prim.usda");
        let stage = Stage::open(&path)?;

        // /Source/Child in ref_target.usda should appear as /World/RefPrim/Child.
        let children = child_names(&stage, "/World/RefPrim")?;
        assert!(
            children.contains(&"Child".to_string()),
            "referenced children should be namespace-remapped"
        );

        Ok(())
    }

    // --- Inherit composition ---

    /// class_inherit.usda: cubeWithoutSetColor inherits from /_myClass which
    /// defines displayColor = green. The prim should pick up the class property.
    #[test]
    fn inherit_from_class() -> Result<()> {
        let path = composition_path("class_inherit.usda");
        let stage = Stage::open(&path)?;

        // The inherited property should be visible.
        let props = prop_names(&stage, "/World/cubeWithoutSetColor")?;
        assert!(
            props.contains(&"primvars:displayColor".to_string()),
            "inherited property should be visible"
        );

        Ok(())
    }

    /// class_inherit.usda: cubeWithSetColor inherits from /_myClass but
    /// overrides displayColor locally. Local opinion (red) should win
    /// over the inherited opinion (green).
    #[test]
    fn inherit_local_opinion_wins() -> Result<()> {
        let path = composition_path("class_inherit.usda");
        let stage = Stage::open(&path)?;

        // The local displayColor (red) should win over inherited (green).
        let prop = sdf::Path::new("/World/cubeWithSetColor")?.append_property("primvars:displayColor")?;
        let value: Option<sdf::Value> = stage.field(&prop, sdf::FieldKey::Default)?;
        assert!(value.is_some());

        // Verify it's the local red, not the inherited green.
        let green = sdf::Value::Vec3fVec(vec![gf::vec3f(0.0, 0.8, 0.0)]);
        assert_ne!(value.unwrap(), green, "local opinion should win over inherited");

        Ok(())
    }

    // --- Variant selection ---

    /// The local opinion on radius (1) should be stronger than the variant's (2).
    #[test]
    fn variant_local_opinion_wins() -> Result<()> {
        let path = format!(
            "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
            manifest_dir()
        );
        let stage = Stage::open(&path)?;

        // The local radius=1 should win over variant radius=2.
        let prop = sdf::Path::new("/World/Sphere")?.append_property("radius")?;
        let value = stage.field::<f64>(&prop, sdf::FieldKey::Default)?;
        assert_eq!(value, Some(1.0), "local opinion (1) should win over variant (2)");

        Ok(())
    }

    // --- Payload composition ---

    /// Vendor test: payload_same_folder.usda has a payload to _stage.usda.
    /// The payload's prim hierarchy should be composed into the stage.
    #[test]
    fn payload_pulls_children() -> Result<()> {
        let path = composition_path("payload/payload_same_folder.usda");
        let stage = Stage::open(&path)?;

        // The payload target layer has /World/Cube. Since /World is the payload
        // target, /World/Cube should appear.
        let children = child_names(&stage, "/World")?;
        assert!(
            children.contains(&"Cube".to_string()),
            "Cube from payload layer should appear under /World"
        );

        Ok(())
    }

    // --- Specialize composition ---

    /// The local opinion on displayColor (yellow) should win over the
    /// specialized source's displayColor (red).
    #[test]
    fn specialize_local_opinion_wins() -> Result<()> {
        let path = composition_path("inherit_and_specialize.usda");
        let stage = Stage::open(&path)?;

        let prop = sdf::Path::new("/World/cubeScene/specializes")?.append_property("primvars:displayColor")?;
        let value: Option<sdf::Value> = stage.field(&prop, sdf::FieldKey::Default)?;
        assert!(value.is_some());

        // Local is yellow (0.8, 0.8, 0), source is red (0.8, 0, 0).
        let red = sdf::Value::Vec3fVec(vec![gf::vec3f(0.8, 0.0, 0.0)]);
        assert_ne!(value.unwrap(), red, "local opinion should win over specialized");

        Ok(())
    }

    /// A prim with `instanceable = true` should parse without error, and the
    /// `instanceable` field should be readable via `stage.field()`.
    #[test]
    fn instanceable_true_parses_and_is_readable() -> Result<()> {
        let path = fixture_path("instanceable_metadata.usda");
        let stage = Stage::open(&path)?;

        let value = stage.field::<bool>("/Root/InstancePrototype", sdf::FieldKey::Instanceable)?;
        assert_eq!(value, Some(true), "instanceable = true should be stored");

        Ok(())
    }

    /// A prim with `instanceable = false` should also parse correctly.
    #[test]
    fn instanceable_false_parses_and_is_readable() -> Result<()> {
        let path = fixture_path("instanceable_metadata.usda");
        let stage = Stage::open(&path)?;

        let value = stage.field::<bool>("/Root/NotInstanceable", sdf::FieldKey::Instanceable)?;
        assert_eq!(value, Some(false), "instanceable = false should be stored");

        Ok(())
    }

    /// A prim without `instanceable` metadata should return None.
    #[test]
    fn instanceable_absent_returns_none() -> Result<()> {
        let path = fixture_path("instanceable_metadata.usda");
        let stage = Stage::open(&path)?;

        let value = stage.field::<bool>("/Root", sdf::FieldKey::Instanceable)?;
        assert_eq!(value, None, "instanceable should be None when not authored");

        Ok(())
    }

    // --- Variant fallback selection ---

    /// A variant fallback should select the specified variant when no authored
    /// selection exists. The prim should expose opinions from the fallback variant.
    #[test]
    fn variant_fallback_selects_preferred() -> Result<()> {
        let path = fixture_path("variant_fallback.usda");
        let fallbacks = crate::pcp::VariantFallbackMap::new().add("shadingComplexity", ["simple"]);
        let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

        // /NoSelection has no authored selection. With fallback "simple",
        // the complexity field should be 0.5 (not 1.0 from "full").
        let prop = sdf::Path::new("/NoSelection")?.append_property("complexity")?;
        let value = stage.field::<f64>(&prop, sdf::FieldKey::Default)?;
        assert_eq!(value, Some(0.5), "fallback 'simple' should give complexity=0.5");

        Ok(())
    }

    /// An authored selection should take priority over a variant fallback at the
    /// stage level.
    #[test]
    fn variant_fallback_does_not_override_authored() -> Result<()> {
        let path = fixture_path("variant_fallback.usda");
        let fallbacks = crate::pcp::VariantFallbackMap::new().add("shadingComplexity", ["none"]);
        let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

        // /Root has authored selection "full". Even with fallback "none",
        // the authored selection should win.
        let prop = sdf::Path::new("/Root")?.append_property("complexity")?;
        let value = stage.field::<f64>(&prop, sdf::FieldKey::Default)?;
        assert_eq!(value, Some(1.0), "authored 'full' should win over fallback 'none'");

        Ok(())
    }

    // --- Inherit child propagation ---

    /// A prim that inherits a class should expose the class's children even
    /// when the inheriting prim has no local override for them.
    #[test]
    fn inherit_child_exists_without_local_override() -> Result<()> {
        let path = fixture_path("inherit_child_propagation.usda");
        let stage = Stage::open(&path)?;

        // /Instance inherits /BaseClass which has child /BaseClass/Child.
        // /Instance/Child should exist even though Instance has no local "Child".
        let children = child_names(&stage, "/Instance")?;
        assert!(
            children.contains(&"Child".to_string()),
            "inherited child should appear: got {children:?}"
        );

        // The inherited property should be accessible.
        assert!(
            stage.has_spec(sdf::Path::new("/Instance/Child.name")?)?,
            "property from inherited child should be visible"
        );

        Ok(())
    }

    /// Nested children from an inherited class should propagate through
    /// multiple levels even without local overrides at any level.
    #[test]
    fn inherit_nested_child_propagation() -> Result<()> {
        let path = fixture_path("inherit_nested_child.usda");
        let stage = Stage::open(&path)?;

        // /Prim inherits /Base. /Base/A/B exists with val=1.0.
        // /Prim/A should exist, /Prim/A/B should exist.
        let a_children = child_names(&stage, "/Prim")?;
        assert!(
            a_children.contains(&"A".to_string()),
            "first-level child: got {a_children:?}"
        );

        let b_children = child_names(&stage, "/Prim/A")?;
        assert!(
            b_children.contains(&"B".to_string()),
            "second-level child: got {b_children:?}"
        );

        assert!(
            stage.has_spec(sdf::Path::new("/Prim/A/B.val")?)?,
            "deeply nested inherited property should be visible"
        );

        Ok(())
    }

    /// Children should propagate through an inherit chain (Leaf → Middle → GrandBase).
    #[test]
    fn inherit_chain_child_propagation() -> Result<()> {
        let path = fixture_path("inherit_chain_child.usda");
        let stage = Stage::open(&path)?;

        // /Leaf inherits /Middle which inherits /GrandBase.
        // /GrandBase/Deep exists with x=42. /Leaf/Deep should exist.
        let children = child_names(&stage, "/Leaf")?;
        assert!(
            children.contains(&"Deep".to_string()),
            "chain-inherited child: got {children:?}"
        );

        assert!(
            stage.has_spec(sdf::Path::new("/Leaf/Deep.x")?)?,
            "property from chain-inherited child should be visible"
        );

        Ok(())
    }

    // --- Session layer ---

    /// Opens a stage with session_layer.usda over session_root.usda.
    fn open_with_session() -> Result<Stage> {
        let root = fixture_path("session_root.usda");
        let session = fixture_path("session_layer.usda");
        Stage::builder().session_layer(&session).open(&root)
    }

    /// A stage opened without a session layer should report no session layer.
    #[test]
    fn no_session_layer_by_default() -> Result<()> {
        let stage = Stage::open(&fixture_path("session_root.usda"))?;

        assert!(!stage.has_session_layer());
        assert_eq!(stage.session_layer(), None);
        assert_eq!(stage.layer_count(), 1);

        Ok(())
    }

    /// A session layer's opinions should be stronger than the root layer's.
    #[test]
    fn session_layer_opinion_wins() -> Result<()> {
        let stage = open_with_session()?;

        assert!(stage.has_session_layer());
        assert_eq!(stage.layer_count(), 2);

        let prop = sdf::Path::new("/World")?.append_property("radius")?;
        let value = stage.field::<f64>(&prop, sdf::FieldKey::Default)?;
        assert_eq!(value, Some(99.0), "session layer opinion should win");

        Ok(())
    }

    /// The session layer can add properties not present in the root layer.
    #[test]
    fn session_layer_adds_properties() -> Result<()> {
        let stage = open_with_session()?;

        let prop = sdf::Path::new("/World")?.append_property("visibility")?;
        let value = stage.field::<String>(&prop, sdf::FieldKey::Default)?;
        assert_eq!(value, Some("hidden".to_string()));

        Ok(())
    }

    /// The root layer's properties not overridden by the session layer
    /// should still be accessible.
    #[test]
    fn session_layer_preserves_root_opinions() -> Result<()> {
        let stage = open_with_session()?;

        let prop = sdf::Path::new("/World")?.append_property("name")?;
        let value = stage.field::<String>(&prop, sdf::FieldKey::Default)?;
        assert_eq!(value, Some("root".to_string()));

        Ok(())
    }

    /// `defaultPrim` should come from the root layer, not the session layer.
    #[test]
    fn session_layer_does_not_affect_default_prim() -> Result<()> {
        let stage = open_with_session()?;
        assert_eq!(stage.default_prim(), Some("World".to_string()));
        Ok(())
    }

    /// Children defined only in the root layer should still be visible
    /// when a session layer is present.
    #[test]
    fn session_layer_preserves_children() -> Result<()> {
        let stage = open_with_session()?;

        let children = child_names(&stage, "/World")?;
        assert!(
            children.contains(&"Child".to_string()),
            "root layer's children should be visible: got {children:?}"
        );

        Ok(())
    }

    #[test]
    fn api_schemas_returns_applied_schemas() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let geo = sdf::Path::new("/World/Geo")?;
        let schemas = stage.prim_at(geo.clone()).api_schemas()?;
        assert!(schemas.contains(&"MaterialBindingAPI".to_string()));
        assert!(schemas.contains(&"SkelBindingAPI".to_string()));
        Ok(())
    }

    #[test]
    fn api_schemas_compose_list_ops() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("weak.usda"),
            r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        append apiSchemas = ["WeakAPI", "RemovedAPI"]
    )
    {
    }
}
"#,
        )?;
        std::fs::write(
            dir.path().join("middle.usda"),
            r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "World"
{
    over "Geo" (
        prepend apiSchemas = ["StrongAPI"]
    )
    {
    }
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0
(
    subLayers = [
        @middle.usda@
    ]
)

over "World"
{
    over "Geo" (
        delete apiSchemas = ["RemovedAPI"]
    )
    {
    }
}
"#,
        )?;

        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let schemas = stage.prim_at(sdf::Path::new("/World/Geo")?).api_schemas()?;
        assert_eq!(schemas, vec!["StrongAPI".to_string(), "WeakAPI".to_string()]);
        Ok(())
    }

    #[test]
    fn api_schemas_compose_reorder_list_op() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("weak.usda"),
            r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        apiSchemas = ["A", "B", "C"]
    )
    {
    }
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "World"
{
    over "Geo" (
        reorder apiSchemas = ["C", "A"]
    )
    {
    }
}
"#,
        )?;

        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let schemas = stage.prim_at(sdf::Path::new("/World/Geo")?).api_schemas()?;
        assert_eq!(schemas, vec!["C".to_string(), "A".to_string(), "B".to_string()]);
        Ok(())
    }

    /// Inherit arc: a class authoring `apiSchemas` contributes to the
    /// inheriting prim's composed list, with the local prim's edits applied
    /// on top. `has_api_schema` (the surface physics / skel readers depend
    /// on) sees both opinions.
    #[test]
    fn api_schemas_via_inherit() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0

class "_Base" (
    prepend apiSchemas = ["BaseAPI"]
)
{
}

def Xform "World"
{
    def Mesh "Geo" (
        inherits = </_Base>
        prepend apiSchemas = ["LocalAPI"]
    )
    {
    }
}
"#,
        )?;
        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let geo = sdf::Path::new("/World/Geo")?;
        assert_eq!(
            stage.prim_at(geo.clone()).api_schemas()?,
            vec!["LocalAPI".to_string(), "BaseAPI".to_string()],
        );
        assert!(stage.prim_at(geo.clone()).has_api_schema("BaseAPI")?);
        assert!(stage.prim_at(geo.clone()).has_api_schema("LocalAPI")?);
        Ok(())
    }

    /// Reference arc: a referenced asset's `apiSchemas` compose into the
    /// referencing prim's list, with the local layer's edits applied on top.
    #[test]
    fn api_schemas_via_reference() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("asset.usda"),
            r#"#usda 1.0
(
    defaultPrim = "Source"
)

def Mesh "Source" (
    prepend apiSchemas = ["AssetAPI"]
)
{
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0

def Xform "World"
{
    def "Geo" (
        references = @asset.usda@
        prepend apiSchemas = ["LocalAPI"]
    )
    {
    }
}
"#,
        )?;
        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let geo = sdf::Path::new("/World/Geo")?;
        assert_eq!(
            stage.prim_at(geo.clone()).api_schemas()?,
            vec!["LocalAPI".to_string(), "AssetAPI".to_string()],
        );
        Ok(())
    }

    /// Variant arc: a selected variant authoring `apiSchemas` contributes to
    /// the variant-set-owning prim's composed list.
    #[test]
    fn api_schemas_via_variant() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        variants = {
            string mode = "full"
        }
        prepend variantSets = "mode"
        prepend apiSchemas = ["LocalAPI"]
    )
    {
        variantSet "mode" = {
            "full" (
                prepend apiSchemas = ["VariantAPI"]
            ) {
            }
            "empty" {
            }
        }
    }
}
"#,
        )?;
        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let geo = sdf::Path::new("/World/Geo")?;
        let schemas = stage.prim_at(geo.clone()).api_schemas()?;
        assert!(
            schemas.contains(&"VariantAPI".to_string()),
            "variant contribution missing: {schemas:?}",
        );
        assert!(
            schemas.contains(&"LocalAPI".to_string()),
            "local contribution missing: {schemas:?}",
        );
        Ok(())
    }

    /// Property paths resolve to the owning prim's schemas (matches the
    /// `specifier` / `kind` convention).
    #[test]
    fn api_schemas_property_path() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let prim = sdf::Path::new("/World/Geo")?;
        let prop = sdf::Path::new("/World/Geo.points")?;
        assert_eq!(stage.prim_at(prop).api_schemas()?, stage.prim_at(prim).api_schemas()?);
        Ok(())
    }

    #[test]
    fn connection_paths_compose_list_ops() -> Result<()> {
        // Stack: weak sublayer authors `append`; root layer authors
        // `prepend`. `connection_paths` must fold edits across both
        // layers, not return only the strongest layer's list op.
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("weak.usda"),
            r#"#usda 1.0

def Shader "Mat"
{
    color3f outputs:out
    append color3f inputs:in.connect = [</Mat.outputs:out>]
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "Mat"
{
    prepend color3f inputs:in.connect = [</Mat.outputs:strong>]
}
"#,
        )?;

        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let conns = connections(&stage, &sdf::Path::new("/Mat.inputs:in")?)?;
        assert_eq!(
            conns,
            vec![
                sdf::Path::new("/Mat.outputs:strong")?,
                sdf::Path::new("/Mat.outputs:out")?
            ]
        );
        Ok(())
    }

    #[test]
    fn relationship_targets_compose_list_ops() -> Result<()> {
        // Weak sublayer appends a target; root prepends one. Raw targets must
        // fold list-op edits across both layers (spec 12.2.6, 12.4).
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("weak.usda"),
            r#"#usda 1.0

def "Set"
{
    def "A" {}
    def "B" {}
    append rel members = [</Set/B>]
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "Set"
{
    prepend rel members = [</Set/A>]
}
"#,
        )?;

        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let targets = rel_targets(&stage, &sdf::Path::new("/Set.members")?)?;
        assert_eq!(targets, vec![sdf::Path::new("/Set/A")?, sdf::Path::new("/Set/B")?]);
        Ok(())
    }

    #[test]
    fn relationship_targets_remap_reference() -> Result<()> {
        // Targets authored in a referenced asset's namespace resolve into the
        // referencing prim's namespace (spec 12.4 raw targets across arcs).
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("asset.usda"),
            r#"#usda 1.0
(
    defaultPrim = "Source"
)

def "Source"
{
    def "Child" {}
    rel members = [</Source/Child>]
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0

def "Inst" (
    references = @asset.usda@
)
{
}
"#,
        )?;

        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let targets = rel_targets(&stage, &sdf::Path::new("/Inst.members")?)?;
        assert_eq!(targets, vec![sdf::Path::new("/Inst/Child")?]);
        Ok(())
    }

    #[test]
    fn forwarded_targets_honor_mask() -> Result<()> {
        // Forwarding must not read a relationship on a masked-out prim, so the
        // chain through /Hidden.rel contributes nothing; a direct prim target
        // to the masked prim is still returned (raw target value, not a query).
        let dir = tempfile::tempdir()?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0

def "Vis"
{
    rel chain = [</Hidden.rel>]
    rel direct = [</Hidden>]
}

def "Hidden"
{
    rel rel = [</Hidden/Geom>]
    def "Geom" {}
}
"#,
        )?;

        let stage = Stage::builder()
            .population_mask(StagePopulationMask::new(["/Vis"]))
            .open(root.to_str().expect("utf-8 temp path"))?;

        // /Hidden is masked out: its relationship is not followed.
        assert!(fwd_targets(&stage, &sdf::Path::new("/Vis.chain")?)?.is_empty());
        // A direct prim target is still returned, matching raw targets.
        assert_eq!(
            fwd_targets(&stage, &sdf::Path::new("/Vis.direct")?)?,
            vec![sdf::Path::new("/Hidden")?]
        );
        Ok(())
    }

    #[test]
    fn connection_paths_remap_reference() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("asset.usda"),
            r#"#usda 1.0
(
    defaultPrim = "Source"
)

def Shader "Source"
{
    color3f outputs:out
    color3f inputs:in.connect = [</Source.outputs:out>]
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0

def Shader "Mat" (
    references = @asset.usda@
)
{
}
"#,
        )?;

        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        let input = sdf::Path::new("/Mat.inputs:in")?;
        let output = sdf::Path::new("/Mat.outputs:out")?;
        assert_eq!(connections(&stage, &input)?, vec![output.clone()]);

        let graph = crate::usd::ConnectionGraph::from_stage(&stage)?;
        assert_eq!(graph.sources(&input), std::slice::from_ref(&output));
        assert_eq!(graph.sinks(&output), &[input]);
        Ok(())
    }

    #[test]
    fn remove_connection_deletes_inherited() -> Result<()> {
        let target = sdf::Path::new("/Mat.outputs:out")?;
        let input = sdf::Path::new("/Mat.inputs:in")?;

        let mut strong = sdf::Layer::new_anonymous("root.usda");
        strong.pseudo_root_mut()?.set_sublayers(["weak.usda"]);

        let mut weak = sdf::Layer::new_anonymous("weak.usda");
        weak.create_prim("/Mat", sdf::Specifier::Def, "Shader")?;
        weak.create_attribute("/Mat.outputs:out", "color3f", sdf::Variability::Varying, true)?;
        weak.create_attribute("/Mat.inputs:in", "color3f", sdf::Variability::Varying, true)?
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

        let mut strong = sdf::Layer::new_anonymous("root.usda");
        strong.pseudo_root_mut()?.set_sublayers(["weak.usda"]);

        let mut weak = sdf::Layer::new_anonymous("weak.usda");
        weak.create_prim("/Mat", sdf::Specifier::Def, "Shader")?;
        weak.create_attribute("/Mat.outputs:out", "color3f", sdf::Variability::Varying, true)?;
        weak.create_attribute("/Mat.inputs:in", "color3f", sdf::Variability::Varying, true)?
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

        let mut strong = sdf::Layer::new_anonymous("root.usda");
        strong.pseudo_root_mut()?.set_sublayers(["weak.usda"]);

        let mut weak = sdf::Layer::new_anonymous("weak.usda");
        weak.create_prim("/Mat", sdf::Specifier::Def, "Shader")?;
        weak.create_attribute("/Mat.outputs:out", "color3f", sdf::Variability::Varying, true)?;
        weak.create_attribute("/Mat.inputs:in", "color3f", sdf::Variability::Varying, true)?
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

    #[test]
    fn api_schemas_empty_for_prim_without_schemas() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let props = sdf::Path::new("/World/Props")?;
        assert!(stage.prim_at(props).api_schemas()?.is_empty());
        Ok(())
    }

    #[test]
    fn has_api_schema_matches_applied() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let geo = sdf::Path::new("/World/Geo")?;
        assert!(stage.prim_at(geo.clone()).has_api_schema("MaterialBindingAPI")?);
        assert!(!stage.prim_at(geo.clone()).has_api_schema("SkelRootAPI")?);
        Ok(())
    }

    #[test]
    fn type_name_returns_prim_type() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        assert_eq!(
            stage.prim_at(sdf::Path::new("/World/Geo")?).type_name()?,
            Some("Mesh".to_string())
        );
        assert_eq!(
            stage.prim_at(sdf::Path::new("/World")?).type_name()?,
            Some("Xform".to_string())
        );
        Ok(())
    }

    fn open_stage_queries_fixture() -> Result<Stage> {
        Stage::open("fixtures/stage_queries.usda")
    }

    #[test]
    fn active_loaded() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert!(stage.prim_at("/World/ActiveParent/Child").is_active()?);
        assert!(stage.prim_at("/World/ActiveParent/Child").is_loaded()?);

        assert!(!stage.prim_at("/World/InactiveParent").is_active()?);
        assert!(!stage.prim_at("/World/InactiveParent/Child").is_active()?);
        assert!(!stage.prim_at("/World/InactiveParent/Child").is_loaded()?);

        assert!(!stage.prim_at("/World/Missing").is_active()?);
        Ok(())
    }

    #[test]
    fn load_none() -> Result<()> {
        let path = composition_path("payload/payload_same_folder.usda");

        let loaded = Stage::open(&path)?;
        assert_eq!(loaded.layer_count(), 2);
        assert!(loaded.prim_at("/World").is_loaded()?);
        assert_eq!(child_names(&loaded, "/World")?, vec!["Cube"]);

        let unloaded = Stage::builder()
            .initial_load_set(InitialLoadSet::LoadNone)
            .open(&path)?;
        assert_eq!(unloaded.initial_load_set(), InitialLoadSet::LoadNone);
        assert_eq!(unloaded.layer_count(), 1);
        assert!(!unloaded.prim_at("/World").is_loaded()?);
        assert_eq!(child_names(&unloaded, "/World")?, Vec::<String>::new());

        let mut prims = Vec::new();
        unloaded.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;
        assert!(prims.is_empty());
        Ok(())
    }

    #[test]
    fn mask_traverse() -> Result<()> {
        let stage = Stage::builder()
            .population_mask(StagePopulationMask::new(["/World/ActiveParent/Child"]))
            .open("fixtures/stage_queries.usda")?;

        assert_eq!(stage.root_prims()?, vec!["World"]);
        assert_eq!(child_names(&stage, "/World")?, vec!["ActiveParent"]);
        assert_eq!(child_names(&stage, "/World/ActiveParent")?, vec!["Child"]);

        assert!(stage.has_spec("/World")?);
        assert!(stage.has_spec("/World/ActiveParent/Child")?);
        assert!(!stage.has_spec("/World/Group")?);
        assert_eq!(stage.prim_at("/World/Group").kind()?, None);

        let mut prims = Vec::new();
        stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;
        assert_eq!(
            prims,
            vec!["/World", "/World/ActiveParent", "/World/ActiveParent/Child"]
        );
        Ok(())
    }

    #[test]
    fn mask_skips_dependency() -> Result<()> {
        let path = composition_path("references/reference_invalid.usda");
        let stage = Stage::builder()
            .population_mask(StagePopulationMask::new(["/World/cube"]))
            .open(&path)?;

        assert_eq!(stage.root_prims()?, vec!["World"]);
        assert_eq!(child_names(&stage, "/World")?, vec!["cube"]);
        assert!(!stage.has_spec("/World/invalid_reference")?);
        Ok(())
    }

    #[test]
    fn defined_abstract() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(
            stage.prim_at("/World/OverOnly").specifier()?,
            Some(sdf::Specifier::Over)
        );
        assert!(stage.prim_at("/World/ActiveParent/Child").is_defined()?);
        assert!(!stage.prim_at("/World/OverOnly").is_defined()?);
        assert!(!stage.prim_at("/World/OverParent/Child").is_defined()?);

        assert!(stage.prim_at("/World/ClassParent/Child").is_defined()?);
        assert!(stage.prim_at("/World/ClassParent").is_abstract()?);
        assert!(stage.prim_at("/World/ClassParent/Child").is_abstract()?);
        assert!(!stage.prim_at("/World/ActiveParent/Child").is_abstract()?);
        Ok(())
    }

    #[test]
    fn instance_flag() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert!(stage.prim_at("/World/Instance").has_composition_arc()?);
        assert!(stage.prim_at("/World/Instance").is_instance()?);

        assert!(!stage.prim_at("/World/InstanceableNoArc").has_composition_arc()?);
        assert!(!stage.prim_at("/World/InstanceableNoArc").is_instance()?);
        Ok(())
    }

    /// An instance prim's children come only from its composition arcs; a
    /// local-only child is discarded (spec 11.3.3).
    #[test]
    fn instance_children_from_arcs_only() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing.usda"))?;

        let mut children = child_names(&stage, "/Instance")?;
        children.sort();
        assert_eq!(children, vec!["Child".to_string()]);

        // A plain (non-instance) reference still merges local and referenced
        // children.
        let mut non_instance = child_names(&stage, "/NonInstance")?;
        non_instance.sort();
        assert_eq!(non_instance, vec!["Child".to_string(), "LocalOnly".to_string()]);
        Ok(())
    }

    /// Instances sharing a prototype resolve descendant values identically and
    /// expose the prototype's children (spec 11.3.3).
    #[test]
    fn shared_instances_resolve_identically() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

        assert_eq!(stage.value_at("/A/Child.size", 0.0)?, Some(sdf::Value::Double(5.0)));
        assert_eq!(stage.value_at("/B/Child.size", 0.0)?, Some(sdf::Value::Double(5.0)));
        assert_eq!(stage.value_at("/C/Child.size", 0.0)?, Some(sdf::Value::Double(9.0)));

        assert_eq!(child_names(&stage, "/A")?, vec!["Child".to_string()]);
        assert_eq!(child_names(&stage, "/B")?, vec!["Child".to_string()]);
        Ok(())
    }

    /// `get_prototype` / `get_instances` group instances by shared composition,
    /// and the prototype namespace is addressable (spec 11.3.3).
    #[test]
    fn prototype_queries() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

        let proto = stage.prim_at("/A").prototype()?;
        assert!(proto.is_some());
        assert_eq!(stage.prim_at("/B").prototype()?, proto); // same composition → shared
        assert_ne!(stage.prim_at("/C").prototype()?, proto); // different prototype
        assert_eq!(stage.prim_at("/Proto").prototype()?, None); // not an instance

        let proto = proto.unwrap();
        // Returned sorted by path, so callers need not sort themselves.
        let instances: Vec<String> = stage
            .prim_at(proto.clone())
            .instances()
            .iter()
            .map(|p| p.to_string())
            .collect();
        assert_eq!(instances, vec!["/A".to_string(), "/B".to_string()]);

        // The prototype namespace is addressable and resolves to the shared
        // (arc-only) subtree.
        assert!(stage.prim_at(proto.clone()).is_prototype());
        let child = sdf::path(format!("{proto}/Child"))?;
        assert!(stage.prim_at(child.clone()).is_in_prototype());
        assert_eq!(
            stage.value_at(child.append_property("size")?, 0.0)?,
            Some(sdf::Value::Double(5.0))
        );
        Ok(())
    }

    /// Prototype queries respect the population mask: a masked-out instance is
    /// not instanced and never appears among a prototype's instances.
    #[test]
    fn prototype_queries_masked() -> Result<()> {
        let stage = Stage::builder()
            .population_mask(StagePopulationMask::new(["/A"]))
            .open(&fixture_path("instancing_shared.usda"))?;

        // /A is in the mask; /B (which shares /A's prototype) is not.
        assert!(stage.prim_at("/A").is_instance()?);
        assert!(!stage.prim_at("/B").is_instance()?);

        let proto = stage.prim_at("/A").prototype()?;
        assert!(proto.is_some());
        assert_eq!(stage.prim_at("/B").prototype()?, None);

        // The masked-out /B is excluded from the prototype's instance list.
        let proto = proto.unwrap();
        assert_eq!(stage.prim_at(proto.clone()).instances(), vec![sdf::path("/A")?]);
        assert_eq!(stage.prototypes(), vec![proto]);
        Ok(())
    }

    /// A nested instance (an instance inside a prototype's subtree) is
    /// recognized, resolves values within the queried instance, and shares its
    /// own prototype across the outer instances (spec 11.3.3).
    #[test]
    fn nested_instances() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_nested.usda"))?;

        assert_eq!(stage.value_at("/A/Sub/L.v", 0.0)?, Some(sdf::Value::Double(7.0)));
        assert_eq!(stage.value_at("/B/Sub/L.v", 0.0)?, Some(sdf::Value::Double(7.0)));

        // The nested prims are instances and share one prototype.
        assert!(stage.prim_at("/A/Sub").is_instance()?);
        assert!(stage.prim_at("/B/Sub").is_instance()?);
        let nested = stage.prim_at("/A/Sub").prototype()?;
        assert!(nested.is_some());
        assert_eq!(stage.prim_at("/B/Sub").prototype()?, nested);

        // The outer instances share a distinct prototype.
        let outer = stage.prim_at("/A").prototype()?;
        assert_eq!(stage.prim_at("/B").prototype()?, outer);
        assert_ne!(outer, nested);

        // The nested subtree is also reachable through the outer prototype.
        let outer = outer.unwrap();
        assert_eq!(
            stage.value_at(sdf::path(format!("{outer}/Sub/L.v"))?, 0.0)?,
            Some(sdf::Value::Double(7.0))
        );
        Ok(())
    }

    /// A connection inside an instance subtree resolves within the queried
    /// instance, not the shared canonical instance (spec 11.3.3 + 11.3.4).
    #[test]
    fn instance_connection_remaps_to_instance() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

        // Query /I1 first so it becomes canonical.
        assert_eq!(
            connections(&stage, &sdf::path("/I1/Dst.inputs:in")?)?,
            vec![sdf::path("/I1/Src.outputs:out")?]
        );
        // /I2 shares the prototype; its connection must point into /I2.
        assert_eq!(
            connections(&stage, &sdf::path("/I2/Dst.inputs:in")?)?,
            vec![sdf::path("/I2/Src.outputs:out")?]
        );
        Ok(())
    }

    /// A connection on a prototype *descendant* resolves in the prototype
    /// namespace when queried directly on the prototype, and remaps to the
    /// queried instance when reached through a proxy (spec 11.3.3 + 12.4).
    #[test]
    fn prototype_descendant_target_remap() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

        // Query an instance proxy first to register the prototype; the target
        // remaps into that instance's namespace.
        assert_eq!(
            connections(&stage, &sdf::path("/I1/Dst.inputs:in")?)?,
            vec![sdf::path("/I1/Src.outputs:out")?]
        );

        // The same connection queried directly on the prototype descendant stays
        // in the prototype namespace (no instance to remap to).
        let proto = stage.prim_at("/I1").prototype()?.expect("I1 is an instance");
        let dst_in = proto.append_path("Dst")?.append_property("inputs:in")?;
        assert_eq!(
            connections(&stage, &dst_in)?,
            vec![proto.append_path("Src")?.append_property("outputs:out")?]
        );
        Ok(())
    }

    /// Forwarding through a relationship that lives inside an instance
    /// prototype resolves within the queried instance: the prototype rel is
    /// classified correctly (not mistaken for a terminal) and its targets
    /// remap into the instance namespace (spec 11.3.3 + 12.4).
    #[test]
    fn forwarded_targets_through_instance() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("asset.usda"),
            r#"#usda 1.0
(
    defaultPrim = "Proto"
)

def "Proto"
{
    def "Target" {}
    rel direct = [</Proto/Target>]
    rel chain = [</Proto.direct>]
}
"#,
        )?;
        let root = dir.path().join("root.usda");
        std::fs::write(
            &root,
            r#"#usda 1.0

def "I1" (
    instanceable = true
    references = @asset.usda@
)
{
}

def "I2" (
    instanceable = true
    references = @asset.usda@
)
{
}
"#,
        )?;

        let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
        // chain -> direct (a prototype relationship) -> Target. Each hop stays
        // in the queried instance's namespace.
        assert_eq!(
            fwd_targets(&stage, &sdf::path("/I1.chain")?)?,
            vec![sdf::path("/I1/Target")?]
        );
        assert_eq!(
            fwd_targets(&stage, &sdf::path("/I2.chain")?)?,
            vec![sdf::path("/I2/Target")?]
        );
        Ok(())
    }

    /// Connection and schema readers descend into instance subtrees, so
    /// content inside an instance is not silently skipped. Public traversal
    /// stops at instances, but these readers need the full composed namespace.
    #[test]
    fn readers_index_instanced_content() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

        let graph = crate::usd::ConnectionGraph::from_stage(&stage)?;
        // The connection lives inside the instance /I1; the reader must descend
        // into the instance proxy to index it.
        assert_eq!(
            graph.sources(&sdf::path("/I1/Dst.inputs:in")?),
            &[sdf::path("/I1/Src.outputs:out")?]
        );
        Ok(())
    }

    /// Default traversal stops at instance prims; `with_instance_proxies`
    /// descends into their subtrees (spec 11.3.3).
    #[test]
    fn traversal_instance_proxies() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

        let mut default = Vec::new();
        stage.traverse(PrimPredicate::DEFAULT, |p| default.push(p.to_string()))?;
        assert!(default.contains(&"/A".to_string()));
        assert!(!default.contains(&"/A/Child".to_string()));

        let mut proxies = Vec::new();
        stage.traverse(PrimPredicate::DEFAULT.with_instance_proxies(true), |p| {
            proxies.push(p.to_string())
        })?;
        assert!(proxies.contains(&"/A/Child".to_string()));
        Ok(())
    }

    /// A property authored at an instance root is local to the instance and
    /// does not leak onto the shared prototype root (spec 11.3.3): the prototype
    /// composes only the referenced opinions.
    #[test]
    fn prototype_root_drops_instance_overrides() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_root_override.usda"))?;

        // The instance root keeps its local overrides.
        assert_eq!(stage.value_at("/A.shared", 0.0)?, Some(sdf::Value::Double(7.0)));
        assert_eq!(stage.value_at("/A.rootOnly", 0.0)?, Some(sdf::Value::Double(42.0)));

        // The shared prototype root drops them: the overridden property falls
        // back to the referenced value and the instance-only property is gone.
        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");
        assert_eq!(
            stage.value_at(proto.append_property("shared")?, 0.0)?,
            Some(sdf::Value::Double(1.0))
        );
        assert_eq!(stage.value_at(proto.append_property("rootOnly")?, 0.0)?, None);
        Ok(())
    }

    /// A query on the deterministic synthetic prototype path before any instance
    /// composes must not leave the prototype root empty: materialization keys off
    /// the registry's mint signal, so it overwrites any stale empty index cached
    /// at `/__Prototype_N` (spec 11.3.3).
    #[test]
    fn prototype_root_survives_early_query() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_root_override.usda"))?;

        // Touch the deterministic synthetic path before any instance registers;
        // this caches an empty index at /__Prototype_0.
        assert_eq!(stage.value_at("/__Prototype_0.shared", 0.0)?, None);

        // Composing the instance mints and materializes /__Prototype_0.
        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");
        assert_eq!(proto.as_str(), "/__Prototype_0");

        // The prototype root now holds the real composition, not the stale empty
        // index that the guard would otherwise have mistaken for it.
        assert_eq!(
            stage.value_at(proto.append_property("shared")?, 0.0)?,
            Some(sdf::Value::Double(1.0))
        );
        Ok(())
    }

    /// A query on a synthetic prototype *descendant* before any instance
    /// registers caches a stale empty index and an identity redirection; minting
    /// the prototype must evict both so the descendant resolves the shared
    /// content rather than the stale synthetic composition (spec 11.3.3).
    #[test]
    fn prototype_descendant_survives_early_query() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

        // Touch the synthetic descendant before any instance registers; this
        // caches an empty index at /__Prototype_0/Child and memoizes its path as
        // an identity (non-redirected) mapping.
        assert_eq!(stage.value_at("/__Prototype_0/Child.size", 0.0)?, None);

        // Composing the instance mints and materializes /__Prototype_0.
        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");
        assert_eq!(proto.as_str(), "/__Prototype_0");

        // The descendant now resolves the shared content: minting evicted the
        // stale empty index and identity redirection under /__Prototype_0, so the
        // query recomposes it in place from the materialized prototype root.
        assert_eq!(
            stage.value_at(proto.append_path("Child")?.append_property("size")?, 0.0)?,
            Some(sdf::Value::Double(5.0))
        );
        Ok(())
    }

    /// A property authored inside a variant selected on an instance is shared
    /// content (the selection defines the prototype) and must resolve on the
    /// materialized prototype root (spec 11.3.3).
    #[test]
    fn prototype_root_keeps_variant_opinions() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_variant_root.usda"))?;

        // The instance resolves the variant-authored property.
        assert_eq!(stage.value_at("/A.picked", 0.0)?, Some(sdf::Value::Double(5.0)));

        // So must the prototype root: the variant opinion lives at the instance's
        // own namespace (/A{v=x}), and rebasing must not move the spec lookup off
        // it.
        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");
        assert_eq!(
            stage.value_at(proto.append_property("picked")?, 0.0)?,
            Some(sdf::Value::Double(5.0))
        );
        Ok(())
    }

    /// A relationship/connection target authored at a prototype's root resolves
    /// into the prototype namespace on the materialized prototype root, and into
    /// each instance's namespace on the instances (spec 11.3.3 + 12.4). Exercises
    /// the root rebase (`rebase_root`) of the prototype-root map.
    #[test]
    fn prototype_root_target_remap() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_root_target.usda"))?;

        // On the instances the targets stay in each instance's own namespace.
        assert_eq!(
            rel_targets(&stage, &sdf::path("/A.myrel")?)?,
            vec![sdf::path("/A/Target")?]
        );
        assert_eq!(
            connections(&stage, &sdf::path("/A.inputs:in")?)?,
            vec![sdf::path("/A.outputs:out")?]
        );
        assert_eq!(
            rel_targets(&stage, &sdf::path("/B.myrel")?)?,
            vec![sdf::path("/B/Target")?]
        );

        // On the materialized prototype root they resolve into the prototype
        // namespace, not the canonical instance's.
        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");
        assert_eq!(
            rel_targets(&stage, &proto.append_property("myrel")?)?,
            vec![proto.append_path("Target")?]
        );
        assert_eq!(
            connections(&stage, &proto.append_property("inputs:in")?)?,
            vec![proto.append_property("outputs:out")?]
        );
        Ok(())
    }

    /// The resolved variant selection is part of the instancing key: instances
    /// of one reference share a prototype iff their selections match (spec
    /// 11.3.3). /A and /C select `x` and share; /B selects `y` and is distinct.
    #[test]
    fn variant_selection_keys_prototype() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_variant_distinct.usda"))?;

        let proto = |p: &str| -> Result<sdf::Path> {
            stage
                .prim_at(p)
                .prototype()?
                .ok_or_else(|| anyhow::anyhow!("{p} is not an instance"))
        };

        // Same selection (`x`) shares one prototype; the other selection (`y`)
        // gets a distinct one.
        assert_eq!(proto("/A")?, proto("/C")?);
        assert_ne!(proto("/A")?, proto("/B")?);

        // Each prototype resolves its own variant content.
        assert_eq!(stage.value_at("/A.picked", 0.0)?, Some(sdf::Value::Double(1.0)));
        assert_eq!(stage.value_at("/B.picked", 0.0)?, Some(sdf::Value::Double(2.0)));
        assert_eq!(stage.value_at("/C.picked", 0.0)?, Some(sdf::Value::Double(1.0)));
        Ok(())
    }

    /// A prototype is populated when at least one of its instances is in the
    /// population mask (spec 11.3.3): the synthetic `/__Prototype_N` namespace is
    /// never named in a user mask, yet its shared content stays readable through
    /// the masked instance.
    #[test]
    fn prototype_visible_under_mask() -> Result<()> {
        let stage = Stage::builder()
            .population_mask(StagePopulationMask::new(["/A"]))
            .open(&fixture_path("instancing_shared.usda"))?;

        // /A is in the mask and is an instance; its prototype is reachable.
        assert!(stage.prim_at("/A").is_instance()?);
        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");

        // The prototype's shared content is readable even though /__Prototype_N
        // is never named in the mask, because instance /A is.
        let child = proto.append_path("Child")?;
        assert!(stage.prim_at(child.clone()).is_valid()?);
        assert_eq!(
            stage.value_at(child.append_property("size")?, 0.0)?,
            Some(sdf::Value::Double(5.0))
        );

        // A prototype with no masked instance stays hidden: /B (and so the
        // prototype it would otherwise expose) is outside the mask.
        assert!(!stage.population_mask().includes(&sdf::path("/B")?));
        Ok(())
    }

    /// A prototype's namespace can contain a nested instance: that nested prim
    /// is itself an instance and mints its own prototype, and a prim beneath it
    /// is an instance proxy of the nested prototype rather than plain prototype
    /// content (spec 11.3.3).
    #[test]
    fn nested_instance_in_prototype() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_nested_in_prototype.usda"))?;

        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");

        // The proxy chain through the instance namespace resolves the nested
        // value (/A/Nested is itself an instance).
        assert!(stage.prim_at("/A/Nested").is_instance()?);
        assert_eq!(stage.value_at("/A/Nested/Leaf.v", 0.0)?, Some(sdf::Value::Double(3.0)));

        // Inside the prototype namespace, the nested prim is an instance and
        // mints its own, distinct prototype.
        let nested = stage.prim_at(proto.append_path("Nested")?);
        assert!(nested.is_instance()?);
        let nested_proto = nested.prototype()?.expect("nested prim is an instance");
        assert_ne!(nested_proto, proto);

        // A prim beneath the nested instance (inside the prototype namespace) is
        // an instance proxy of the nested prototype — previously this was
        // reported as plain prototype content.
        let leaf = stage.prim_at(proto.append_path("Nested")?.append_path("Leaf")?);
        assert!(leaf.is_instance_proxy()?);
        let in_proto = leaf.prim_in_prototype()?.expect("Leaf is an instance proxy");
        assert_eq!(in_proto.path(), &nested_proto.append_path("Leaf")?);
        Ok(())
    }

    /// An instance's descendant is an instance proxy that maps to a prim in the
    /// shared prototype; the instance root and non-instanced prims are not
    /// proxies (spec 11.3.3).
    #[test]
    fn instance_proxy_api() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

        assert!(!stage.prim_at("/A").is_instance_proxy()?);
        assert!(stage.prim_at("/A/Child").is_instance_proxy()?);

        let proto = stage.prim_at("/A").prototype()?.expect("A is an instance");
        let in_proto = stage
            .prim_at("/A/Child")
            .prim_in_prototype()?
            .expect("Child is an instance proxy");
        assert_eq!(in_proto.path(), &proto.append_path("Child")?);
        assert!(in_proto.is_in_prototype());

        // A prim in the prototype namespace is in a prototype, not a proxy.
        assert!(!in_proto.is_instance_proxy()?);

        // A nonexistent path under an instance is not a proxy, and has no prim in
        // the prototype.
        assert!(!stage.prim_at("/A/Missing").is_instance_proxy()?);
        assert!(stage.prim_at("/A/Missing").prim_in_prototype()?.is_none());
        Ok(())
    }

    /// Local opinions on an instance's descendants are discarded; values come
    /// from the arc (spec 11.3.3).
    #[test]
    fn instance_descendant_ignores_local_override() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing.usda"))?;

        // Instance: the local `over Child { size = 999 }` is ignored.
        assert_eq!(
            stage.value_at("/Instance/Child.size", 0.0)?,
            Some(sdf::Value::Double(1.0))
        );

        // Non-instance: the local override wins as usual.
        assert_eq!(
            stage.value_at("/NonInstance/Child.size", 0.0)?,
            Some(sdf::Value::Double(999.0))
        );
        Ok(())
    }

    #[test]
    fn instance_descendant_ignores_local_arc() -> Result<()> {
        let stage = Stage::open(&fixture_path("instancing_local_arc.usda"))?;

        // The local `over Child (references = </Other/Child>)` carries its own
        // arc; both the local opinion and the node that arc spawns are
        // discarded, so the value comes from the prototype, not /Other/Child.
        assert_eq!(stage.value_at("/A/Child.v", 0.0)?, Some(sdf::Value::Double(1.0)));
        Ok(())
    }

    #[test]
    fn model_hierarchy() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(stage.prim_at("/World").kind()?, Some("assembly".to_string()));
        assert!(stage.prim_at("/World").is_model()?);
        assert!(stage.prim_at("/World").is_group()?);

        assert!(stage.prim_at("/World/Group").is_model()?);
        assert!(stage.prim_at("/World/Group").is_group()?);
        assert!(stage.prim_at("/World/Group/Component").is_model()?);
        assert!(stage.prim_at("/World/Group/Component").is_component()?);

        assert!(!stage.prim_at("/World/Group/Subcomponent").is_model()?);
        assert!(stage.prim_at("/World/Group/Subcomponent").is_subcomponent()?);

        assert_eq!(
            stage.prim_at("/World/InvalidComponentParent/Component").kind()?,
            Some("component".to_string())
        );
        assert!(!stage.prim_at("/World/InvalidComponentParent/Component").is_model()?);
        assert!(!stage
            .prim_at("/World/InvalidComponentParent/Component")
            .is_component()?);
        Ok(())
    }

    #[test]
    fn prim_status_bits() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(
            stage.prim_status("/World/ClassParent/Child")?,
            PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::ABSTRACT
        );

        assert_eq!(
            stage.prim_status("/World/Instance")?,
            PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::INSTANCE
        );
        Ok(())
    }

    #[test]
    fn traverse_default() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        let mut prims = Vec::new();
        stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;

        assert!(prims.contains(&"/World".to_string()));
        assert!(prims.contains(&"/World/ActiveParent".to_string()));
        assert!(prims.contains(&"/World/ActiveParent/Child".to_string()));
        assert!(prims.contains(&"/World/Instance".to_string()));

        assert!(!prims.contains(&"/World/InactiveParent".to_string()));
        assert!(!prims.contains(&"/World/InactiveParent/Child".to_string()));
        assert!(!prims.contains(&"/World/OverOnly".to_string()));
        assert!(!prims.contains(&"/World/OverParent".to_string()));
        assert!(!prims.contains(&"/World/OverParent/Child".to_string()));
        assert!(!prims.contains(&"/World/ClassParent".to_string()));
        assert!(!prims.contains(&"/World/ClassParent/Child".to_string()));
        Ok(())
    }

    #[test]
    fn traverse_all_predicate() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        let mut prims = Vec::new();
        stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

        assert!(prims.contains(&"/World/InactiveParent".to_string()));
        assert!(prims.contains(&"/World/InactiveParent/Child".to_string()));
        assert!(prims.contains(&"/World/OverOnly".to_string()));
        assert!(prims.contains(&"/World/OverParent/Child".to_string()));
        assert!(prims.contains(&"/World/ClassParent".to_string()));
        assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
        Ok(())
    }

    #[test]
    fn custom_predicate() -> Result<()> {
        let stage = open_stage_queries_fixture()?;
        let predicate = PrimPredicate::new(PrimStatus::ACTIVE | PrimStatus::DEFINED, PrimStatus::empty());

        let mut prims = Vec::new();
        stage.traverse(predicate, |p| prims.push(p.as_str().to_string()))?;

        assert!(prims.contains(&"/World/ClassParent".to_string()));
        assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
        assert!(!prims.contains(&"/World/InactiveParent".to_string()));
        assert!(!prims.contains(&"/World/OverOnly".to_string()));
        Ok(())
    }

    // --- Stage-tier authoring ---

    fn in_memory_stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    #[test]
    fn define_prim() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/World")?.set_type_name("Xform")?;
        stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        assert_eq!(stage.spec_type("/World")?, Some(sdf::SpecType::Prim));
        assert_eq!(stage.spec_type("/World/Mesh")?, Some(sdf::SpecType::Prim));
        assert_eq!(
            stage.field::<sdf::Value>("/World", sdf::FieldKey::TypeName)?,
            Some(sdf::Value::Token("Xform".into())),
        );
        Ok(())
    }

    /// `Stage::custom_layer_data` reads the root layer's `customLayerData`
    /// dictionary (C++ `UsdStage::GetRootLayer()->GetCustomLayerData`).
    #[test]
    fn custom_layer_data() -> Result<()> {
        let stage = in_memory_stage()?;
        assert!(stage.custom_layer_data()?.is_none());

        let dict = sdf::Value::Dictionary([("tool".to_string(), sdf::Value::String("rs".into()))].into());
        stage.with_target_layer_at(&sdf::Path::abs_root(), |layer, _| {
            layer.pseudo_root_mut()?.add(sdf::FieldKey::CustomLayerData, dict);
            let mut cl = sdf::ChangeList::new();
            cl.entry_mut(&sdf::Path::abs_root())
                .info_changed
                .insert(sdf::FieldKey::CustomLayerData.as_str());
            Ok(cl)
        })?;

        let Some(sdf::Value::Dictionary(read)) = stage.custom_layer_data()? else {
            panic!("customLayerData should resolve to a dictionary");
        };
        assert_eq!(read.get("tool"), Some(&sdf::Value::String("rs".into())));
        Ok(())
    }

    #[test]
    fn authoring_invalidates_cached_miss() -> Result<()> {
        let stage = in_memory_stage()?;
        assert!(!stage.has_spec("/World")?);

        stage.define_prim("/World")?.set_type_name("Xform")?;

        assert!(stage.has_spec("/World")?);
        assert_eq!(
            stage.field::<sdf::Value>("/World", sdf::FieldKey::TypeName)?,
            Some(sdf::Value::Token("Xform".into())),
        );
        Ok(())
    }

    #[test]
    fn override_prim() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.override_prim("/A/B")?;
        assert_eq!(
            stage.field::<sdf::Value>("/A", sdf::FieldKey::Specifier)?,
            Some(sdf::Value::Specifier(sdf::Specifier::Over)),
        );
        assert_eq!(
            stage.field::<sdf::Value>("/A/B", sdf::FieldKey::Specifier)?,
            Some(sdf::Value::Specifier(sdf::Specifier::Over)),
        );
        Ok(())
    }

    #[test]
    fn create_attribute() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/Sphere")?.set_type_name("Sphere")?;
        stage.create_attribute("/Sphere.radius", "double")?;
        assert_eq!(stage.spec_type("/Sphere.radius")?, Some(sdf::SpecType::Attribute));
        assert_eq!(
            stage.field::<sdf::Value>("/Sphere.radius", sdf::FieldKey::TypeName)?,
            Some(sdf::Value::Token("double".into())),
        );
        assert_eq!(
            stage.field::<sdf::Value>("/Sphere.radius", sdf::FieldKey::Custom)?,
            Some(sdf::Value::Bool(true)),
        );
        Ok(())
    }

    #[test]
    fn create_relationship() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
        stage
            .create_relationship("/Mesh.material:binding")?
            .set_variability(sdf::Variability::Uniform)?;
        assert_eq!(
            stage.spec_type("/Mesh.material:binding")?,
            Some(sdf::SpecType::Relationship)
        );
        assert_eq!(
            stage.field::<sdf::Value>("/Mesh.material:binding", sdf::FieldKey::Custom)?,
            Some(sdf::Value::Bool(true)),
        );
        Ok(())
    }

    #[test]
    fn author_default_prim() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.set_default_prim("World")?;
        stage.define_prim("/World")?.set_type_name("Xform")?;
        assert_eq!(stage.default_prim().as_deref(), Some("World"));
        Ok(())
    }

    /// `defaultPrim` writes target the root layer regardless of `EditTarget`
    /// (mirrors C++ `UsdStage::SetDefaultPrim` going through `GetRootLayer`).
    /// In-memory root with a file-loaded session layer; setting the edit
    /// target to the read-only session layer must not block the write.
    #[test]
    fn default_prim_targets_root() -> Result<()> {
        let session = fixture_path("session_layer.usda");
        let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
        stage.set_edit_target(EditTarget::for_layer(nth_identifier(&stage, 0)))?; // session layer
        stage.set_default_prim("World")?;
        assert_eq!(stage.default_prim().as_deref(), Some("World"));
        Ok(())
    }

    #[test]
    fn default_prim_rejects_path() -> Result<()> {
        let stage = in_memory_stage()?;
        let err = stage.set_default_prim("/World").unwrap_err();
        assert!(matches!(
            err,
            StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. })
        ));
        Ok(())
    }

    /// Modern OpenUSD allows nested `defaultPrim` values like `"World/Char"`.
    /// The write contract must match what the read path will accept.
    #[test]
    fn default_prim_accepts_nested() -> Result<()> {
        let stage = in_memory_stage()?;
        stage.set_default_prim("World/Mesh")?;
        assert_eq!(stage.default_prim().as_deref(), Some("World/Mesh"));
        Ok(())
    }

    #[test]
    fn read_only_rejects_authoring() -> Result<()> {
        let stage = Stage::open(&composition_path("subLayer/sublayer_same_folder.usda"))?;
        let err = stage.define_prim("/X").err().expect("expected ReadOnly error");
        assert!(matches!(
            err,
            StageAuthoringError::Layer(sdf::AuthoringError::ReadOnly { .. })
        ));
        Ok(())
    }

    #[test]
    fn read_only_default_prim() -> Result<()> {
        let stage = Stage::open(&composition_path("subLayer/sublayer_same_folder.usda"))?;
        let err = stage.set_default_prim("World").unwrap_err();
        assert!(matches!(
            err,
            StageAuthoringError::Layer(sdf::AuthoringError::ReadOnly { .. })
        ));
        Ok(())
    }

    #[test]
    fn edit_target_out_of_range() -> Result<()> {
        let stage = in_memory_stage()?;
        let err = stage
            .set_edit_target(EditTarget::for_layer("missing-layer"))
            .unwrap_err();
        assert!(matches!(err, StageAuthoringError::LayerNotFound { .. }));
        Ok(())
    }

    /// Exercises `StageBuilder::in_memory`'s session-layer branch: the
    /// anonymous root must end up at `session_layer_count`, the edit target
    /// must point there, and authoring on the in-memory root must work
    /// (with the session layer remaining read-only).
    #[test]
    fn in_memory_session_layer() -> Result<()> {
        let session = fixture_path("session_layer.usda");
        let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
        assert!(stage.has_session_layer());
        assert_eq!(stage.layer_count(), 2);
        assert_eq!(stage.edit_target().layer_identifier(), nth_identifier(&stage, 1));
        stage.define_prim("/World")?.set_type_name("Xform")?;
        assert_eq!(stage.spec_type("/World")?, Some(sdf::SpecType::Prim));
        Ok(())
    }

    /// A local edit target maps scene paths to themselves, so authoring is
    /// unchanged from the bare-`layer_index` behavior.
    #[test]
    fn edit_target_local_is_identity() -> Result<()> {
        let target = EditTarget::for_layer("test");
        let path = sdf::path("/A/B")?;
        assert_eq!(target.map_to_spec_path(&path), Some(path));
        Ok(())
    }

    /// A variant edit target rewrites scene paths into the `{set=sel}`
    /// namespace; paths outside the variant prim map to themselves.
    #[test]
    fn variant_target_maps_selection() -> Result<()> {
        let target = EditTarget::for_local_direct_variant("test", sdf::path("/Prim{set=sel}")?);
        assert_eq!(
            target.map_to_spec_path(&sdf::path("/Prim/child")?),
            Some(sdf::path("/Prim{set=sel}child")?)
        );
        assert_eq!(
            target.map_to_spec_path(&sdf::path("/Prim.attr")?),
            Some(sdf::path("/Prim{set=sel}.attr")?)
        );
        assert_eq!(
            target.map_to_spec_path(&sdf::path("/Other")?),
            Some(sdf::path("/Other")?)
        );
        Ok(())
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
            use sdf::AbstractData;
            let layers = stage.layers();
            let root_id = layers.id_of(&root).unwrap();
            layers.layer(root_id).spec_type(&sdf::path("/Prim{set=sel}child")?)
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
            use sdf::AbstractData;
            let layers = stage.layers();
            let root_id = layers.id_of(&root).unwrap();
            layers.layer(root_id).spec_type(&sdf::path("/Prim{set=sel}.size")?)
        };
        assert_eq!(landed, Some(sdf::SpecType::Attribute));
        Ok(())
    }

    /// `edit_context` restores the previous edit target when the guard drops.
    #[test]
    fn edit_context_restores_on_drop() -> Result<()> {
        let session = fixture_path("session_layer.usda");
        let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
        assert_eq!(stage.edit_target().layer_identifier(), nth_identifier(&stage, 1));
        {
            let _ctx = stage.edit_context(EditTarget::for_layer(nth_identifier(&stage, 0)))?;
            assert_eq!(stage.edit_target().layer_identifier(), nth_identifier(&stage, 0));
        }
        assert_eq!(stage.edit_target().layer_identifier(), nth_identifier(&stage, 1));
        Ok(())
    }

    /// The guard restores the target even when the scope exits early via `?`.
    #[test]
    fn edit_context_restores_on_error() -> Result<()> {
        let session = fixture_path("session_layer.usda");
        let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
        assert_eq!(stage.edit_target().layer_identifier(), nth_identifier(&stage, 1));
        let authored: std::result::Result<(), StageAuthoringError> = (|| {
            let _ctx = stage.edit_context(EditTarget::for_layer(nth_identifier(&stage, 0)))?;
            // Layer 0 is the read-only session layer; the write fails and `?`
            // returns from this closure with the guard still in scope.
            stage.define_prim("/X")?;
            Ok(())
        })();
        assert!(authored.is_err());
        assert_eq!(stage.edit_target().layer_identifier(), nth_identifier(&stage, 1));
        Ok(())
    }

    /// A bad target is rejected at `edit_context`, leaving the current target
    /// unchanged.
    #[test]
    fn edit_context_rejects_bad_target() -> Result<()> {
        let stage = in_memory_stage()?;
        let before = stage.edit_target().layer_identifier().to_string();
        let result = stage.edit_context(EditTarget::for_layer("missing-layer"));
        assert!(matches!(result, Err(StageAuthoringError::LayerNotFound { .. })));
        assert_eq!(stage.edit_target().layer_identifier(), before);
        Ok(())
    }

    /// Authoring the variant-owning prim itself through a variant target maps
    /// to the bare variant selection, which is not a prim — it must error, not
    /// panic.
    #[test]
    fn define_prim_at_variant_leaf_errors() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.edit_target().layer_identifier().to_string();
        stage.define_prim("/Prim")?;
        stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
        // `/Prim` maps to the variant selection `/Prim{set=sel}`.
        assert!(matches!(
            stage.define_prim("/Prim"),
            Err(StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. }))
        ));
        Ok(())
    }

    /// A significant edit inside a variant must invalidate the composed
    /// (variant-stripped) prim, whose cache key is not on the variant path's
    /// ancestor chain.
    #[test]
    fn variant_edit_invalidates_stripped_path() -> Result<()> {
        let stage = in_memory_stage()?;
        let root = stage.edit_target().layer_identifier().to_string();
        stage.define_prim("/Prim")?;

        // Cache a composed miss at the scene path.
        assert_eq!(stage.spec_type("/Prim/child")?, None);
        assert!(stage.is_indexed(&sdf::path("/Prim/child")?));

        // Author the child inside the variant: `/Prim/child` -> `/Prim{set=sel}child`.
        stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
        stage.define_prim("/Prim/child")?;

        // The stripped composed key must be dropped so the next query rebuilds.
        assert!(!stage.is_indexed(&sdf::path("/Prim/child")?));
        Ok(())
    }

    // --- Value clips (spec 12.3.4) ---

    fn clip_asset(name: &str) -> String {
        format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets/{name}/entry.usd",
            manifest_dir()
        )
    }

    fn value_f64(stage: &Stage, attr: &str, time: f64) -> Option<f64> {
        match stage.value_at(attr, time).expect("value_at") {
            Some(sdf::Value::Float(v)) => Some(v as f64),
            Some(sdf::Value::Double(v)) => Some(v),
            Some(sdf::Value::Int64(v)) => Some(v as f64),
            _ => None,
        }
    }

    fn write_clip_scene(
        dir: &std::path::Path,
        root_body: &str,
        manifest_body: &str,
        clip_body: &str,
    ) -> Result<String> {
        std::fs::write(dir.join("root.usda"), root_body)?;
        std::fs::write(dir.join("manifest.usda"), manifest_body)?;
        std::fs::write(dir.join("clip.usda"), clip_body)?;
        Ok(dir.join("root.usda").to_string_lossy().into_owned())
    }

    /// A clip overrides a referenced attribute that has no local opinion: the
    /// clip's samples win over the reference's (spec 12.3.4.5).
    #[test]
    fn clip_basic_overrides_reference() -> Result<()> {
        let stage = Stage::open(&clip_asset("clip_basic"))?;
        // clip.usd authors size = stage time; the reference authors negatives.
        assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(10.0));
        assert_eq!(value_f64(&stage, "/Model.size", 7.0), Some(7.0)); // interpolated
        Ok(())
    }

    /// Local time samples beat clips; a clip beats a referenced attribute that
    /// has no local opinion (spec 12.3.4.5).
    #[test]
    fn clip_strength_local_vs_reference() -> Result<()> {
        let stage = Stage::open(&clip_asset("clip_advanced"))?;
        // `local` has a local opinion → local wins (10, not the clip's -10).
        assert_eq!(value_f64(&stage, "/Model.local", 10.0), Some(10.0));
        // `ref` has no local opinion → the clip wins (-10, not the reference's 10).
        assert_eq!(value_f64(&stage, "/Model.ref", 10.0), Some(-10.0));
        Ok(())
    }

    #[test]
    fn clip_local_default_wins() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = write_clip_scene(
            dir.path(),
            r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float localDefault = 3
}
"#,
            r#"#usda 1.0
def "Model"
{
    float localDefault
}
"#,
            r#"#usda 1.0
def "Model"
{
    float localDefault.timeSamples = {
        0: 7
    }
}
"#,
        )?;

        let stage = Stage::open(&root)?;
        assert_eq!(value_f64(&stage, "/Model.localDefault", 0.0), Some(3.0));
        Ok(())
    }

    #[test]
    fn clip_skips_missing_attr() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = write_clip_scene(
            dir.path(),
            r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
}
"#,
            r#"#usda 1.0
def "Model"
{
    float ghost
}
"#,
            r#"#usda 1.0
def "Model"
{
    float ghost.timeSamples = {
        0: 7
    }
}
"#,
        )?;

        let stage = Stage::open(&root)?;
        assert_eq!(stage.spec_type("/Model.ghost")?, None);
        assert_eq!(stage.value_at("/Model.ghost", 0.0)?, None);
        Ok(())
    }

    #[test]
    fn clip_anchor_sublayer() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::create_dir(dir.path().join("sub"))?;
        std::fs::write(
            dir.path().join("root.usda"),
            r#"#usda 1.0
(
    subLayers = [@./sub/weak.usda@]
)

over "Model" (
    clips = {
        dictionary default = {
            double2[] times = [(0, 0)]
        }
    }
)
{
}
"#,
        )?;
        std::fs::write(
            dir.path().join("sub").join("weak.usda"),
            r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size
}
"#,
        )?;
        std::fs::write(
            dir.path().join("sub").join("manifest.usda"),
            r#"#usda 1.0
def "Model"
{
    float size
}
"#,
        )?;
        std::fs::write(
            dir.path().join("sub").join("clip.usda"),
            r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 7
    }
}
"#,
        )?;

        let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
        assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(7.0));
        Ok(())
    }

    #[test]
    fn clip_anchor_reference() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::create_dir(dir.path().join("asset"))?;
        std::fs::write(
            dir.path().join("root.usda"),
            r#"#usda 1.0
def "ShotModel" (
    references = @./asset/model.usda@</Model>
)
{
}
"#,
        )?;
        std::fs::write(
            dir.path().join("asset").join("model.usda"),
            r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size
}
"#,
        )?;
        std::fs::write(
            dir.path().join("asset").join("manifest.usda"),
            r#"#usda 1.0
def "Model"
{
    float size
}
"#,
        )?;
        std::fs::write(
            dir.path().join("asset").join("clip.usda"),
            r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 7
    }
}
"#,
        )?;

        let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
        assert_eq!(value_f64(&stage, "/ShotModel.size", 0.0), Some(7.0));
        Ok(())
    }

    #[test]
    fn clip_metadata_retimed() -> Result<()> {
        let dir = tempfile::tempdir()?;
        std::fs::write(
            dir.path().join("root.usda"),
            r#"#usda 1.0
(
    subLayers = [@./weak.usda@ (offset = 10)]
)
"#,
        )?;
        std::fs::write(
            dir.path().join("weak.usda"),
            r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
            double2[] times = [(0, 0), (5, 5)]
        }
    }
)
{
    float size
}
"#,
        )?;
        std::fs::write(
            dir.path().join("manifest.usda"),
            r#"#usda 1.0
def "Model"
{
    float size
}
"#,
        )?;
        std::fs::write(
            dir.path().join("clip.usda"),
            r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 0,
        5: 5
    }
}
"#,
        )?;

        let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
        assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(0.0));
        assert_eq!(value_f64(&stage, "/Model.size", 15.0), Some(5.0));
        Ok(())
    }

    #[test]
    fn clip_initial_jump() -> Result<()> {
        let dir = tempfile::tempdir()?;
        let root = write_clip_scene(
            dir.path(),
            r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
            double2[] times = [(0, 0), (0, 25), (10, 35)]
        }
    }
)
{
    float size
}
"#,
            r#"#usda 1.0
def "Model"
{
    float size
}
"#,
            r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 0.0,
        25: 25.0,
        35: 35.0
    }
}
"#,
        )?;

        let stage = Stage::open(&root)?;
        assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(25.0));
        assert_eq!(value_f64(&stage, "/Model.size", 5.0), Some(30.0));
        Ok(())
    }

    /// Active-clip selection switches clips by stage time and maps stage time
    /// to clip time through the timing curve (spec 12.3.4.3, 12.3.4.4).
    #[test]
    fn clip_multi_active_switch() -> Result<()> {
        let stage = Stage::open(&clip_asset("clip_multi"))?;
        // Stage 10 → clip1 at clip time 10 → -10.
        assert_eq!(value_f64(&stage, "/Model_1.size", 10.0), Some(-10.0));
        // Stage 22 → clip2 active, clip time 6 → -26.
        assert_eq!(value_f64(&stage, "/Model_1.size", 22.0), Some(-26.0));
        Ok(())
    }

    /// Clip set strength falls back to name order when `clipSets` is unauthored
    /// (spec 12.3.4.1): `clip_a` outranks `clip_b` regardless of text order.
    #[test]
    fn clip_sets_default_order() -> Result<()> {
        let stage = Stage::open(&clip_asset("clip_sets"))?;
        // clip_a (primPath /ClipA) wins: attr at stage 0 → 10, not 100.
        assert_eq!(value_f64(&stage, "/DefaultOrderTest.attr", 0.0), Some(10.0));
        assert_eq!(value_f64(&stage, "/DefaultOrderTest.attr", 1.0), Some(20.0));
        Ok(())
    }

    /// The timing curve maps stage time to clip time, including a jump
    /// discontinuity at stage 20 (spec 12.3.4.4, 12.3.4.8).
    #[test]
    fn clip_timings_curve() -> Result<()> {
        let stage = Stage::open(&clip_asset("clip_timings"))?;
        assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(10.0));
        assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(15.0));
        assert_eq!(value_f64(&stage, "/Model.size", 20.0), Some(10.0)); // jump → "at and after"
        assert_eq!(value_f64(&stage, "/Model.size", 30.0), Some(15.0));
        Ok(())
    }

    /// A weak sublayer carrying one opinion, for the sublayer-mutation tests.
    fn opinion_layer(identifier: &str, value: f64) -> Result<sdf::Layer> {
        let mut layer = sdf::Layer::new_anonymous(identifier);
        layer
            .create_attribute("/A.x", "double", sdf::Variability::Varying, true)?
            .set_default(sdf::Value::Double(value));
        Ok(layer)
    }

    /// The parent layer's authored `subLayers` asset paths.
    fn authored_sublayers(stage: &Stage) -> Vec<String> {
        let root = stage.root_layer();
        root.pseudo_root()
            .and_then(|pr| pr.sublayers().map(<[String]>::to_vec))
            .unwrap_or_default()
    }

    /// `insert_sub_layer` both composes the new layer's opinion and authors the
    /// parent's `subLayers` metadata, so the edit persists on save.
    #[test]
    fn insert_sub_layer_authors_metadata() -> Result<()> {
        let stage = Stage::builder().make_stage(vec![sdf::Layer::new_anonymous("root.usda")], 0, Vec::new());

        stage.insert_sub_layer(
            "root.usda",
            0,
            opinion_layer("weak.usda", 5.0)?,
            sdf::LayerOffset::IDENTITY,
        )?;

        assert_eq!(stage.value_at("/A.x", 0.0)?, Some(sdf::Value::Double(5.0)));
        assert_eq!(authored_sublayers(&stage), vec!["weak.usda".to_string()]);
        Ok(())
    }

    /// `ensure_layer` must not clobber an already-loaded node: re-inserting a
    /// layer whose identifier is already in the graph keeps the existing node's
    /// data (and therefore its derived sublayer children), not the fresh empty
    /// layer passed in.
    #[test]
    fn insert_sub_layer_keeps_loaded_node() -> Result<()> {
        // root → mid → leaf, all loaded up front so `mid` has a derived child
        // edge to `leaf` and `leaf`'s opinion composes.
        let mut root = sdf::Layer::new_anonymous("root.usda");
        root.pseudo_root_mut()?.set_sublayers(["mid.usda"]);
        let mut mid = sdf::Layer::new_anonymous("mid.usda");
        mid.pseudo_root_mut()?.set_sublayers(["leaf.usda"]);
        let leaf = opinion_layer("leaf.usda", 5.0)?;

        let stage = Stage::builder().make_stage(vec![root, mid, leaf], 0, Vec::new());
        assert_eq!(stage.value_at("/A.x", 0.0)?, Some(sdf::Value::Double(5.0)));

        // Re-insert `mid` by identifier, passing a fresh empty layer. The graph
        // must keep the loaded `mid` (whose `subLayers` still names `leaf`), so
        // `leaf`'s opinion survives the rebuild.
        stage.insert_sub_layer(
            "root.usda",
            0,
            sdf::Layer::new_anonymous("mid.usda"),
            sdf::LayerOffset::IDENTITY,
        )?;
        assert_eq!(
            stage.value_at("/A.x", 0.0)?,
            Some(sdf::Value::Double(5.0)),
            "the already-loaded mid layer's child edge to leaf must survive re-insertion"
        );
        Ok(())
    }

    /// `remove_sub_layer` drops both the composed opinion and the parent's
    /// authored `subLayers` entry.
    #[test]
    fn remove_sub_layer_clears_metadata() -> Result<()> {
        let stage = Stage::builder().make_stage(vec![sdf::Layer::new_anonymous("root.usda")], 0, Vec::new());
        stage.insert_sub_layer(
            "root.usda",
            0,
            opinion_layer("weak.usda", 5.0)?,
            sdf::LayerOffset::IDENTITY,
        )?;
        assert_eq!(stage.value_at("/A.x", 0.0)?, Some(sdf::Value::Double(5.0)));

        assert!(
            stage.remove_sub_layer("root.usda", "weak.usda")?,
            "a sublayer was removed"
        );

        assert_eq!(
            stage.value_at("/A.x", 0.0)?,
            None,
            "the removed sublayer's opinion is gone"
        );
        assert!(
            authored_sublayers(&stage).is_empty(),
            "the removed sublayer's subLayers entry is gone"
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
        let mut root = sdf::Layer::new_anonymous("root.usda");
        root.pseudo_root_mut()?.set_sublayers(["sub.usda"]);
        let child = opinion_layer("dir/sub.usda", 5.0)?;
        let stage = Stage::builder().make_stage(vec![root, child], 0, Vec::new());
        assert_eq!(stage.value_at("/A.x", 0.0)?, Some(sdf::Value::Double(5.0)));

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
            stage.value_at("/A.x", 0.0)?,
            None,
            "the removed sublayer's opinion is gone"
        );
        assert!(
            authored_sublayers(&stage).is_empty(),
            "the authored subLayers entry is gone"
        );
        Ok(())
    }

    /// Inserting under a read-only parent fails with `ReadOnly` and leaves the
    /// graph untouched — no orphan node for the would-be sublayer.
    #[test]
    fn insert_sub_layer_read_only_parent() -> Result<()> {
        let data = crate::usda::parser::Parser::new("#usda 1.0\n")
            .parse()
            .expect("parse usda");
        let ro_root = sdf::Layer::new("root.usda", Box::new(crate::usda::TextReader::from_data(data)));
        let stage = Stage::builder().make_stage(vec![ro_root], 0, Vec::new());
        let before = stage.layer_count();

        let err = stage
            .insert_sub_layer(
                "root.usda",
                0,
                opinion_layer("weak.usda", 5.0)?,
                sdf::LayerOffset::IDENTITY,
            )
            .unwrap_err();

        assert!(matches!(
            err,
            StageAuthoringError::Layer(sdf::AuthoringError::ReadOnly { .. })
        ));
        assert_eq!(
            stage.layer_count(),
            before,
            "a failed insert must not leave an orphan node"
        );
        Ok(())
    }

    /// Inserting under a parent that is not in the stage fails with
    /// `LayerNotFound` and adds no node.
    #[test]
    fn insert_sub_layer_missing_parent() -> Result<()> {
        let stage = Stage::builder().make_stage(vec![sdf::Layer::new_anonymous("root.usda")], 0, Vec::new());

        let err = stage
            .insert_sub_layer(
                "nope.usda",
                0,
                opinion_layer("weak.usda", 5.0)?,
                sdf::LayerOffset::IDENTITY,
            )
            .unwrap_err();

        assert!(matches!(err, StageAuthoringError::LayerNotFound { .. }));
        assert_eq!(stage.layer_count(), 1, "no node added for a missing parent");
        Ok(())
    }

    /// A dependency shared by the session and root collections appears twice in
    /// the concatenated layer vec; the graph collapses it to one node and keeps
    /// `all_ids` / `layer_count` / the root-session split in sync with the map.
    #[test]
    fn from_layers_dedups_order() {
        let layers = vec![
            sdf::Layer::new_anonymous("session.usda"),
            sdf::Layer::new_anonymous("shared.usda"),
            sdf::Layer::new_anonymous("root.usda"),
            sdf::Layer::new_anonymous("shared.usda"),
        ];
        let stage = Stage::builder().make_stage(layers, 2, Vec::new());

        assert_eq!(
            stage.layer_count(),
            3,
            "the duplicate shared layer collapses to one node"
        );
        let ids = stage.layers().all_ids().to_vec();
        let unique: std::collections::HashSet<_> = ids.iter().copied().collect();
        assert_eq!(ids.len(), unique.len(), "order carries no duplicate id");
        assert_eq!(
            stage.root_layer().identifier(),
            "root.usda",
            "the root stays the first non-session layer after dedup"
        );
    }

    /// When the stage root shares an identifier with a session layer, the root
    /// slot collapses onto the session node — but the root must still resolve to
    /// that shared layer, not slip to the next dependency or vanish.
    #[test]
    fn from_layers_root_shared_with_session() {
        let layers = vec![
            sdf::Layer::new_anonymous("session.usda"),
            sdf::Layer::new_anonymous("shared.usda"),
            sdf::Layer::new_anonymous("shared.usda"), // root slot, same id as session layer 1
            sdf::Layer::new_anonymous("dep.usda"),
        ];
        let stage = Stage::builder().make_stage(layers, 2, Vec::new());

        assert_eq!(stage.layer_count(), 3, "the shared root/session layer is one node");
        assert_eq!(
            stage.root_layer().identifier(),
            "shared.usda",
            "the root resolves to the shared layer, not the next dependency"
        );
    }
}
