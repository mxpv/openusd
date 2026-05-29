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
//! - [`StageBuilder::on_error`] sets a callback for recoverable composition
//!   errors (missing layers, arc cycles, etc.).
//! - [`StageBuilder::variant_fallbacks`] provides a
//!   [`VariantFallbackMap`](crate::pcp::VariantFallbackMap) with preferred
//!   selections for variant sets that have no authored opinion.
//! - [`StageBuilder::initial_load_set`] controls whether payload arcs are
//!   loaded during stage population.
//! - [`StageBuilder::population_mask`] limits the prim working set exposed by
//!   stage queries and traversal.
//!
//! [LIVERPS]: https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html

use std::cell::{Cell, RefCell};

use anyhow::Result;
use bitflags::bitflags;

use crate::{ar, layer, pcp, sdf};

use super::interp::{self, InterpolationType};

/// A recoverable error encountered during stage composition.
///
/// Wraps errors from both layer collection ([`layer::Error`]) and prim
/// composition ([`pcp::Error`]). The error handler provided via
/// [`StageBuilder::on_error`] decides whether to skip and continue or abort.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum CompositionError {
    /// Error during layer collection (e.g. unresolved asset path).
    #[error(transparent)]
    Layer(#[from] layer::Error),
    /// Error during prim composition (e.g. missing defaultPrim, arc cycle).
    #[error(transparent)]
    Pcp(#[from] pcp::Error),
}

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
    }
}

/// Predicate used to filter prim traversal by resolved status bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrimPredicate {
    required: PrimStatus,
    rejected: PrimStatus,
}

impl PrimPredicate {
    /// Status bits inherited from a prim's ancestors. Missing any of these on a
    /// parent guarantees that no descendant can have them either, enabling
    /// subtree pruning during traversal.
    const INHERITED_REQUIRED: PrimStatus = PrimStatus::ACTIVE.union(PrimStatus::LOADED).union(PrimStatus::DEFINED);

    /// Status bits that, once set on an ancestor, are inherited by every descendant.
    const INHERITED_REJECTED: PrimStatus = PrimStatus::ABSTRACT;

    /// Match every composed prim.
    pub const ALL: Self = Self::new(PrimStatus::empty(), PrimStatus::empty());

    /// OpenUSD-style default traversal predicate.
    ///
    /// Matches prims that are active, loaded, defined, and not abstract.
    pub const DEFAULT: Self = Self::new(Self::INHERITED_REQUIRED, Self::INHERITED_REJECTED);

    /// Creates a predicate with required and rejected status bits.
    pub const fn new(required: PrimStatus, rejected: PrimStatus) -> Self {
        Self { required, rejected }
    }

    /// Returns `true` if `status` satisfies the predicate.
    pub const fn matches(self, status: PrimStatus) -> bool {
        status.contains(self.required) && !status.intersects(self.rejected)
    }

    /// Returns the set of status bits this predicate actually consults.
    fn consulted_bits(self) -> PrimStatus {
        self.required.union(self.rejected)
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
    /// `/Prim{set=sel}/Child`.
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

/// Identifies which layer in a [`Stage`] receives authored opinions.
///
/// Minimal subset of C++ `UsdEditTarget` — this is not yet a full
/// implementation. C++ `UsdEditTarget` also carries a `PcpMapFunction` so
/// authoring can be routed *through* a composition arc (writing into a
/// specific variant, reference, or specialize). The Rust version currently
/// stores only a `layer_index`; the path mapping is the identity, so every
/// authoring call writes to the target layer using the composed path
/// verbatim. The TODOs below track what still needs to land before this
/// reaches parity.
//
// TODO: carry a `pcp::NodeIndex` so variant / specialize edit contexts can
// route writes inside a variant through `inverse(map_to_root)` (the math
// already exists in `pcp::MapFunction`). Required to mirror C++
// `UsdEditTarget(UsdPrim, UsdEditTarget::Reference)` flows used by variant
// authoring.
//
// TODO: provide an RAII guard (`UsdEditContext` analog) that scopes a target
// switch and restores the previous target on `Drop`. Lets callers write
// `let _ctx = stage.edit_at(variant)?;` and have authoring routed for the
// scope of the block.
//
// TODO: validate target by `pcp::LayerStackIdentifier` instead of a bare
// `usize` so an `EditTarget` constructed against one stage can't be applied
// to another, and so layer reordering (when supported) doesn't silently
// retarget writes.
//
// TODO: add convenience constructors like `EditTarget::root(&stage)` /
// `EditTarget::session(&stage)` so callers don't have to do
// `session_layer_count`-arithmetic to address common slots.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EditTarget {
    layer_index: usize,
}

impl EditTarget {
    /// Edit target pointing at the layer with the given index in the stage's
    /// layer stack. Session layers occupy the first `session_layer_count`
    /// slots; the root layer sits at `session_layer_count`.
    //
    // TODO: replace the raw `usize` constructor once the
    // `LayerStackIdentifier`-based validation above lands. The bare index
    // is convenient but offers no guard against cross-stage misuse.
    pub const fn for_layer_index(layer_index: usize) -> Self {
        Self { layer_index }
    }

    /// Returns the layer index this target writes to.
    pub const fn layer_index(self) -> usize {
        self.layer_index
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

    /// The edit target's layer index is out of range for this stage.
    #[error("edit target layer index {index} is out of range ({count} layers)")]
    LayerOutOfRange {
        /// The offending index.
        index: usize,
        /// The current number of layers.
        count: usize,
    },
}

/// A composed USD stage.
///
/// Owns the loaded layer stack and provides composed access to prims,
/// properties, and metadata. Composition indices are built lazily and
/// cached in the [`Cache`](crate::pcp::Cache).
pub struct Stage {
    /// Lazily-built composition graph caching per-prim indices and contexts.
    graph: RefCell<pcp::Cache>,
    /// Initial payload loading behavior for this stage.
    initial_load_set: InitialLoadSet,
    /// Population mask limiting stage-visible prims.
    population_mask: StagePopulationMask,
    /// PCP error handler wrapping the user's unified callback.
    on_composition_error: Box<dyn Fn(pcp::Error) -> Result<()>>,
    /// Stage-level interpolation mode for time-sampled attributes
    /// (AOUSD §12.5). Defaults to [`InterpolationType::Linear`] per
    /// spec.
    interpolation_type: Cell<InterpolationType>,
    /// Where authored opinions land. Defaults to the root layer.
    edit_target: Cell<EditTarget>,
}

impl Stage {
    /// Opens a stage from a root layer file using the [`ar::DefaultResolver`].
    ///
    /// Any unresolvable transitive dependency causes an immediate error.
    /// For custom resolver or error handling, use [`Stage::builder`].
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
    /// let stage = usd::Stage::builder()
    ///     .on_error(|err| {
    ///         eprintln!("warning: {err}");
    ///         Ok(())
    ///     })
    ///     .open("scene.usda")
    ///     .unwrap();
    /// ```
    pub fn builder() -> StageBuilder<ar::DefaultResolver> {
        StageBuilder::new()
    }

    /// Returns the current edit target — the layer that authoring methods
    /// write into.
    pub fn edit_target(&self) -> EditTarget {
        self.edit_target.get()
    }

    /// Replace the current edit target. Subsequent authoring calls write to
    /// the new target's layer.
    ///
    /// Validates that `target.layer_index()` is in range so a bad index
    /// surfaces here, not on some later unrelated authoring call.
    pub fn set_edit_target(&self, target: EditTarget) -> Result<(), StageAuthoringError> {
        let count = self.graph.borrow().layer_count();
        let index = target.layer_index;
        if index >= count {
            return Err(StageAuthoringError::LayerOutOfRange { index, count });
        }

        self.edit_target.set(target);
        Ok(())
    }

    /// Author a `def` prim spec at `path` on the edit target's layer and
    /// return a [`Prim`] handle. Mirrors C++ `UsdStage::DefinePrim`. The
    /// returned handle lets callers chain field setters (`set_type_name`,
    /// `set_active`, `set_kind`, …) and child-property authoring
    /// (`create_attribute`, `create_relationship`).
    pub fn define_prim(&self, path: impl Into<sdf::Path>) -> Result<super::Prim<'_>, StageAuthoringError> {
        let path = path.into();
        let layer_path = path.clone();
        self.with_target_layer(|layer| {
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
    pub fn override_prim(&self, path: impl Into<sdf::Path>) -> Result<super::Prim<'_>, StageAuthoringError> {
        let path = path.into();
        let layer_path = path.clone();
        self.with_target_layer(|layer| {
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
    ) -> Result<super::Attribute<'_>, StageAuthoringError> {
        let path = path.into();
        let type_name = type_name.into();
        let layer_path = path.clone();
        self.with_target_layer(|layer| {
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
    pub fn create_relationship(
        &self,
        path: impl Into<sdf::Path>,
    ) -> Result<super::Relationship<'_>, StageAuthoringError> {
        let path = path.into();
        let layer_path = path.clone();
        self.with_target_layer(|layer| {
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

    /// Borrow the edit target's layer, hand it to `f`, then drive cache
    /// invalidation from the [`sdf::ChangeList`] the closure returns.
    ///
    /// Callers must drop any typed spec view inside the closure — the closure
    /// can't return a borrow from `&mut layer`. The returned [`sdf::ChangeList`]
    /// describes what was authored; an empty list means "no mutation
    /// happened" and skips invalidation.
    ///
    /// On any post-mutation error the cache falls back to "blow the world".
    /// The one error we can short-circuit is [`sdf::AuthoringError::ReadOnly`],
    /// which is detected before any layer state changes.
    pub(super) fn with_target_layer<F>(&self, f: F) -> Result<bool, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer) -> Result<sdf::ChangeList, sdf::AuthoringError>,
    {
        let target = self.edit_target.get();
        let mut cache = self.graph.borrow_mut();
        let count = cache.layer_count();
        let index = target.layer_index;
        let result = {
            let layer = cache
                .layer_mut(index)
                .ok_or(StageAuthoringError::LayerOutOfRange { index, count })?;
            f(layer)
        };
        Self::finalize_layer(&mut cache, index, result)
    }

    /// Borrow the stage's root layer, hand it to `f`, then drive cache
    /// invalidation from the closure's [`sdf::ChangeList`]. See
    /// [`Stage::with_target_layer`] for the contract.
    fn with_root_layer<F>(&self, f: F) -> Result<(), StageAuthoringError>
    where
        F: FnOnce(&mut sdf::Layer) -> Result<sdf::ChangeList, sdf::AuthoringError>,
    {
        let mut cache = self.graph.borrow_mut();
        let index = cache.session_layer_count();
        let count = cache.layer_count();
        let result = {
            let layer = cache
                .layer_mut(index)
                .ok_or(StageAuthoringError::LayerOutOfRange { index, count })?;
            f(layer)
        };
        Self::finalize_layer(&mut cache, index, result).map(|_| ())
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
        cache: &mut pcp::Cache,
        layer_index: usize,
        result: Result<sdf::ChangeList, sdf::AuthoringError>,
    ) -> Result<bool, StageAuthoringError> {
        match result {
            Ok(cl) if cl.is_empty() => Ok(false),
            Ok(cl) => {
                let mut changes = pcp::Changes::new();
                changes.did_change(cache, &[(layer_index, cl)]);
                changes.apply(cache);
                Ok(true)
            }
            Err(e) => {
                if !matches!(e, sdf::AuthoringError::ReadOnly { .. }) {
                    // Conservatively drop every cached index on
                    // post-mutation failure (the layer may be in a
                    // partial state). `SIGNIFICANT` alone is enough —
                    // `apply` routes it through `clear_all_indices` and
                    // the layer-stack precomputed maps (sublayer stacks,
                    // relocates) cannot have been affected by a failing
                    // prim/property edit.
                    let mut changes = pcp::Changes::new();
                    changes.layer_stack |= pcp::LayerStackChanges::SIGNIFICANT;
                    changes.apply(cache);
                }
                Err(StageAuthoringError::Layer(e))
            }
        }
    }

    /// Returns the number of layers in the stage (including session layers).
    pub fn layer_count(&self) -> usize {
        self.graph.borrow().layer_count()
    }

    /// Returns `true` when the composition cache currently holds a prim
    /// index at `path`. Useful for verifying surgical invalidation and
    /// for callers that want to observe cache occupancy.
    pub fn is_indexed(&self, path: &sdf::Path) -> bool {
        self.graph.borrow().is_indexed(path)
    }

    /// Total number of cached prim indices.
    pub fn indexed_count(&self) -> usize {
        self.graph.borrow().indexed_count()
    }

    /// Returns the layer identifiers in strength order (session layers first,
    /// then root layer and its sublayers).
    pub fn layer_identifiers(&self) -> Vec<String> {
        self.graph.borrow().layer_identifiers()
    }

    /// Returns `true` if the stage has a session layer.
    pub fn has_session_layer(&self) -> bool {
        self.graph.borrow().session_layer_count() > 0
    }

    /// Returns the stage's initial payload loading behavior.
    pub const fn initial_load_set(&self) -> InitialLoadSet {
        self.initial_load_set
    }

    /// Returns the population mask used by this stage.
    pub const fn population_mask(&self) -> &StagePopulationMask {
        &self.population_mask
    }

    /// Returns the session layer identifier, if one was provided.
    pub fn session_layer(&self) -> Option<String> {
        let cache = self.graph.borrow();
        if cache.session_layer_count() > 0 {
            cache.layer_identifier(0).map(str::to_owned)
        } else {
            None
        }
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    ///
    /// When a session layer is present, `defaultPrim` is still read from
    /// the root layer (not the session layer), matching C++ behavior.
    pub fn default_prim(&self) -> Option<String> {
        self.graph.borrow().default_prim()
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
    /// Resolution order:
    /// 1. If the attribute authors `timeSamples`, apply AOUSD §12.5
    ///    interpolation over them.
    /// 2. Otherwise fall back to the attribute's `default` value.
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
        if let Some(samples) = self.time_samples(&attr_path)? {
            return Ok(interp::evaluate(&samples, time, self.interpolation_type.get()));
        }
        let default = self.field::<sdf::Value>(attr_path, sdf::FieldKey::Default)?;
        Ok(default.and_then(|v| match v {
            sdf::Value::ValueBlock | sdf::Value::None => None,
            other => Some(other),
        }))
    }

    /// Returns the composed list of root prim names (children of the pseudo-root).
    pub fn root_prims(&self) -> Result<Vec<String>> {
        let root = sdf::Path::abs_root();
        let children = self.try_or_handle(|cache| cache.prim_children(&root))?;
        Ok(self.filter_child_names(&root, children))
    }

    /// Returns the composed list of child prim names for a given prim path.
    ///
    /// Merges `primChildren` across all layers that have a spec at the given
    /// path, collecting the union of child names while preserving the order
    /// from the strongest layer.
    pub fn prim_children(&self, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
        let path = path.into().prim_path();
        if !self.population_mask.includes(&path) {
            return Ok(Vec::new());
        }
        let children = self.try_or_handle(|cache| cache.prim_children(&path))?;
        Ok(self.filter_child_names(&path, children))
    }

    /// Returns the composed list of property names for a given prim path.
    pub fn prim_properties(&self, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
        let path = path.into().prim_path();
        if !self.population_mask.includes(&path) {
            return Ok(Vec::new());
        }
        self.try_or_handle(|cache| cache.prim_properties(&path))
    }

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    pub fn has_spec(&self, path: impl Into<sdf::Path>) -> Result<bool> {
        let path = path.into();
        if !self.population_mask.includes(&path.prim_path()) {
            return Ok(false);
        }
        self.try_or_handle(|cache| cache.has_spec(&path))
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub fn spec_type(&self, path: impl Into<sdf::Path>) -> Result<Option<sdf::SpecType>> {
        let path = path.into();
        if !self.population_mask.includes(&path.prim_path()) {
            return Ok(None);
        }
        self.try_or_handle(|cache| cache.spec_type(&path))
    }

    /// Resolves a field value by walking the prim index from strongest to weakest.
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
    /// # Example
    ///
    /// ```ignore
    /// let active: Option<bool> = stage.field(&prim, sdf::FieldKey::Active)?;
    /// let raw: Option<sdf::Value> = stage.field(&prim, sdf::FieldKey::Active)?;
    /// ```
    pub fn field<T>(&self, path: impl Into<sdf::Path>, field: impl AsRef<str>) -> Result<Option<T>>
    where
        T: TryFrom<sdf::Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        let path = path.into();
        if !self.population_mask.includes(&path.prim_path()) {
            return Ok(None);
        }
        let raw = self.try_or_handle(|cache| cache.resolve_field(&path, field.as_ref()))?;
        match raw {
            Some(value) => Ok(Some(T::try_from(value)?)),
            None => Ok(None),
        }
    }

    /// Returns the composed `apiSchemas` list for a prim, flattened across all
    /// contributing layer opinions.
    ///
    /// Property paths are coerced to their owning prim — `api_schemas` is a
    /// prim-level field. This matches how [`Stage::specifier`] and
    /// [`Stage::kind`] handle their inputs.
    ///
    /// Multi-apply schema instances (e.g. `PhysicsLimitAPI:rotZ`) are included
    /// as-is; callers that need to match only the base name should strip the
    /// instance suffix themselves.
    pub fn api_schemas(&self, prim: &sdf::Path) -> Result<Vec<String>> {
        let prim = prim.prim_path();
        if !self.population_mask.includes(&prim) {
            return Ok(Vec::new());
        }
        self.try_or_handle(|cache| cache.api_schemas(&prim))
    }

    /// Returns `true` when `name` appears in the prim's composed `apiSchemas` list.
    ///
    /// For multi-apply schemas pass the full instance name (e.g.
    /// `"PhysicsLimitAPI:rotZ"`), not just the base name.
    pub fn has_api_schema(&self, prim: &sdf::Path, name: &str) -> Result<bool> {
        Ok(self.api_schemas(prim)?.iter().any(|s| s == name))
    }

    /// Returns the composed `connectionPaths` list for an attribute path,
    /// folding list-op edits (prepend / append / add / delete) across every
    /// contributing layer. Mirrors C++ `UsdAttribute::GetConnections`. Returns
    /// an empty list for non-property paths or attributes with no authored
    /// connections.
    pub fn connection_paths(&self, attr: &sdf::Path) -> Result<Vec<sdf::Path>> {
        if !self.population_mask.includes(&attr.prim_path()) {
            return Ok(Vec::new());
        }
        self.try_or_handle(|cache| cache.connection_paths(attr))
    }

    /// Returns the composed `typeName` for a prim, if set.
    pub fn type_name(&self, prim: &sdf::Path) -> Result<Option<String>> {
        self.field::<String>(prim, "typeName")
    }

    /// Returns the composed specifier for a prim, if one resolves.
    pub fn specifier(&self, prim: impl Into<sdf::Path>) -> Result<Option<sdf::Specifier>> {
        self.field::<sdf::Specifier>(prim.into().prim_path(), sdf::FieldKey::Specifier)
    }

    /// Returns the composed `kind` metadata for a prim, if authored.
    pub fn kind(&self, prim: impl Into<sdf::Path>) -> Result<Option<String>> {
        self.field::<String>(prim.into().prim_path(), sdf::FieldKey::Kind)
    }

    /// Returns `true` if the prim and all ancestors are active.
    ///
    /// Missing `active` opinions default to `true`; a non-existent prim returns
    /// `false`.
    pub fn is_active(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == sdf::Path::abs_root() {
            return Ok(true);
        }
        if !self.has_spec(&prim)? {
            return Ok(false);
        }
        for path in Self::prim_ancestors_inclusive(prim) {
            if self
                .field::<bool>(&path, sdf::FieldKey::Active)?
                .is_some_and(|active| !active)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns `true` if the prim is loaded.
    pub fn is_loaded(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if !self.is_active(&prim)? {
            return Ok(false);
        }
        if self.initial_load_set.load_payloads() {
            return Ok(true);
        }
        for path in Self::prim_ancestors_inclusive(prim) {
            if self.has_payload(&path)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns `true` if the prim and all ancestors have defining specifiers.
    ///
    /// `def` and `class` are defining. `over`, missing specs, and missing
    /// specifier opinions are not defining.
    pub fn is_defined(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == sdf::Path::abs_root() {
            return Ok(true);
        }
        if !self.has_spec(&prim)? {
            return Ok(false);
        }
        for path in Self::prim_ancestors_inclusive(prim) {
            if !matches!(self.specifier(path)?, Some(sdf::Specifier::Def | sdf::Specifier::Class)) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns `true` if the prim or any ancestor resolves to `class`.
    pub fn is_abstract(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == sdf::Path::abs_root() || !self.has_spec(&prim)? {
            return Ok(false);
        }
        for path in Self::prim_ancestors_inclusive(prim) {
            if self.specifier(path)? == Some(sdf::Specifier::Class) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Returns `true` if the prim index contains at least one composition arc.
    pub fn has_composition_arc(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if !self.population_mask.includes(&prim) {
            return Ok(false);
        }
        self.try_or_handle(|cache| cache.has_composition_arc(&prim))
    }

    /// Returns `true` if `instanceable` resolves to true and the prim has a composition arc.
    pub fn is_instance(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == sdf::Path::abs_root() || !self.has_spec(&prim)? {
            return Ok(false);
        }
        if !self.field::<bool>(&prim, sdf::FieldKey::Instanceable)?.unwrap_or(false) {
            return Ok(false);
        }
        self.has_composition_arc(&prim)
    }

    /// Returns `true` if the prim is in the contiguous model hierarchy.
    ///
    /// A model prim has `kind` equal to `group`, `assembly`, or `component`.
    /// Any ancestor below the pseudo-root must have `kind` equal to `group` or
    /// `assembly`; `subcomponent` is intentionally not part of the hierarchy.
    pub fn is_model(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        Ok(self.model_kind(prim.into())?.is_some())
    }

    /// Returns `true` if the prim is a group-like model (`group` or `assembly`).
    pub fn is_group(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        Ok(matches!(self.model_kind(prim.into())?, Some("group" | "assembly")))
    }

    /// Returns `true` if the prim is a component model in a valid model hierarchy.
    pub fn is_component(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        Ok(self.model_kind(prim.into())? == Some("component"))
    }

    /// Returns `true` if the prim has `kind = "subcomponent"`.
    pub fn is_subcomponent(&self, prim: impl Into<sdf::Path>) -> Result<bool> {
        Ok(self.kind(prim)?.as_deref() == Some("subcomponent"))
    }

    /// Returns the resolved stage status bits for a prim.
    pub fn prim_status(&self, prim: impl Into<sdf::Path>) -> Result<PrimStatus> {
        self.prim_status_masked(&prim.into().prim_path(), PrimStatus::all())
    }

    /// Computes only the status bits set in `mask`. Bits outside `mask` are
    /// left unset. Used by traversal so unused checks (e.g. INSTANCE, MODEL
    /// for default traversal) are skipped.
    fn prim_status_masked(&self, prim: &sdf::Path, mask: PrimStatus) -> Result<PrimStatus> {
        let mut status = PrimStatus::empty();
        if mask.contains(PrimStatus::ACTIVE) {
            status.set(PrimStatus::ACTIVE, self.is_active(prim)?);
        }
        if mask.contains(PrimStatus::LOADED) {
            status.set(PrimStatus::LOADED, self.is_loaded(prim)?);
        }
        if mask.contains(PrimStatus::DEFINED) {
            status.set(PrimStatus::DEFINED, self.is_defined(prim)?);
        }
        if mask.contains(PrimStatus::ABSTRACT) {
            status.set(PrimStatus::ABSTRACT, self.is_abstract(prim)?);
        }
        if mask.contains(PrimStatus::INSTANCE) {
            status.set(PrimStatus::INSTANCE, self.is_instance(prim)?);
        }
        if mask.contains(PrimStatus::MODEL) {
            status.set(PrimStatus::MODEL, self.is_model(prim)?);
        }
        Ok(status)
    }

    /// Returns the model-hierarchy `kind` for the prim — `Some("group" | "assembly" | "component")`
    /// when the prim and all ancestors form a contiguous model hierarchy, else `None`.
    fn model_kind(&self, prim: sdf::Path) -> Result<Option<&'static str>> {
        let prim = prim.prim_path();
        if prim == sdf::Path::abs_root() || !self.has_spec(&prim)? {
            return Ok(None);
        }
        let leaf = match self.kind(&prim)?.as_deref() {
            Some("group") => "group",
            Some("assembly") => "assembly",
            Some("component") => "component",
            _ => return Ok(None),
        };
        let Some(parent) = prim.parent() else {
            return Ok(Some(leaf));
        };
        for ancestor in Self::prim_ancestors_inclusive(parent) {
            if !matches!(self.kind(ancestor)?.as_deref(), Some("group" | "assembly")) {
                return Ok(None);
            }
        }
        Ok(Some(leaf))
    }

    fn has_payload(&self, prim: &sdf::Path) -> Result<bool> {
        let payload = self.field::<sdf::Value>(prim, sdf::FieldKey::Payload)?;
        Ok(match payload {
            Some(sdf::Value::Payload(payload)) => Self::payload_has_target(&payload),
            Some(sdf::Value::PayloadListOp(op)) => op.reduced().flatten().iter().any(Self::payload_has_target),
            _ => false,
        })
    }

    fn payload_has_target(payload: &sdf::Payload) -> bool {
        !payload.asset_path.is_empty() || !payload.prim_path.is_empty()
    }

    fn filter_child_names(&self, parent: &sdf::Path, children: Vec<String>) -> Vec<String> {
        if self.population_mask.is_all() {
            return children;
        }
        children
            .into_iter()
            .filter(|name| {
                parent
                    .append_path(name.as_str())
                    .is_ok_and(|child| self.population_mask.includes(&child))
            })
            .collect()
    }

    /// Iterates the prim path and its ancestors from leaf to root, stopping
    /// before the pseudo-root. Assumes `start` is already a prim path.
    fn prim_ancestors_inclusive(start: sdf::Path) -> impl Iterator<Item = sdf::Path> {
        std::iter::successors(Some(start), sdf::Path::parent).take_while(|p| *p != sdf::Path::abs_root())
    }

    /// Calls `f` with a mutable reference to the composition cache. If `f`
    /// returns a [`pcp::Error`], the error handler decides whether to skip
    /// (returning a default value) or abort (propagating the error).
    fn try_or_handle<T: Default>(&self, f: impl FnOnce(&mut pcp::Cache) -> Result<T>) -> Result<T> {
        match f(&mut self.graph.borrow_mut()) {
            Ok(val) => Ok(val),
            Err(e) => match e.downcast::<pcp::Error>() {
                Ok(pcp_err) => {
                    (self.on_composition_error)(pcp_err)?;
                    Ok(T::default())
                }
                Err(other) => Err(other),
            },
        }
    }

    /// Traverses composed prims matching the default predicate.
    ///
    /// The default predicate matches OpenUSD's usual traversal region:
    /// active, loaded, defined, and not abstract.
    pub fn traverse(&self, visitor: impl FnMut(&sdf::Path)) -> Result<()> {
        self.traverse_with_predicate(PrimPredicate::DEFAULT, visitor)
    }

    /// Traverses all composed prims depth-first, calling `visitor` for each.
    pub fn traverse_all(&self, visitor: impl FnMut(&sdf::Path)) -> Result<()> {
        self.traverse_with_predicate(PrimPredicate::ALL, visitor)
    }

    /// Traverses composed prims depth-first, visiting prims that match `predicate`.
    ///
    /// Descendants are pruned when inherited status bits make it impossible for
    /// them to match, such as below inactive, unloaded, undefined, or abstract
    /// prims when the predicate excludes those regions.
    pub fn traverse_with_predicate(&self, predicate: PrimPredicate, mut visitor: impl FnMut(&sdf::Path)) -> Result<()> {
        let needed = predicate.consulted_bits();
        let mut stack = vec![sdf::Path::abs_root()];

        while let Some(path) = stack.pop() {
            if path != sdf::Path::abs_root() {
                let status = self.prim_status_masked(&path, needed)?;
                if predicate.matches(status) {
                    visitor(&path);
                }
                if predicate.prunes_descendants(status) {
                    continue;
                }
            }

            let children = self.prim_children(&path)?;
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

/// Default composition error handler that treats all errors as fatal.
type StrictErrorHandler = fn(CompositionError) -> Result<()>;

/// Converts a composition error into a hard failure.
fn strict_composition_error(e: CompositionError) -> Result<()> {
    Err(anyhow::anyhow!("{e}"))
}

/// Builder for configuring and opening a [`Stage`].
///
/// Created via [`Stage::builder`]. Allows setting a custom asset resolver
/// and an error handler for recoverable composition failures.
pub struct StageBuilder<
    R: ar::Resolver = ar::DefaultResolver,
    E: Fn(CompositionError) -> Result<()> = StrictErrorHandler,
> {
    resolver: R,
    on_error: E,
    variant_fallbacks: pcp::VariantFallbackMap,
    session_layer: Option<String>,
    initial_load_set: InitialLoadSet,
    population_mask: StagePopulationMask,
    interpolation_type: InterpolationType,
}

impl StageBuilder {
    fn new() -> Self {
        Self {
            resolver: ar::DefaultResolver::new(),
            on_error: strict_composition_error,
            variant_fallbacks: pcp::VariantFallbackMap::new(),
            session_layer: None,
            initial_load_set: InitialLoadSet::LoadAll,
            population_mask: StagePopulationMask::all(),
            interpolation_type: InterpolationType::default(),
        }
    }
}

impl<R: ar::Resolver, E: Fn(CompositionError) -> Result<()>> StageBuilder<R, E> {
    /// Sets a custom asset resolver.
    pub fn resolver<R2: ar::Resolver>(self, resolver: R2) -> StageBuilder<R2, E> {
        StageBuilder {
            resolver,
            on_error: self.on_error,
            variant_fallbacks: self.variant_fallbacks,
            session_layer: self.session_layer,
            initial_load_set: self.initial_load_set,
            population_mask: self.population_mask,
            interpolation_type: self.interpolation_type,
        }
    }

    /// Sets a callback invoked when a recoverable composition error occurs.
    ///
    /// Return `Ok(())` to skip the problematic dependency and continue,
    /// or `Err(...)` to abort composition.
    ///
    /// By default, all composition errors are fatal.
    pub fn on_error<E2: Fn(CompositionError) -> Result<()>>(self, handler: E2) -> StageBuilder<R, E2> {
        StageBuilder {
            resolver: self.resolver,
            on_error: handler,
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
        E: 'static,
    {
        let session_layers = self.collect_optional_session_layers()?;
        let root_layers = self.collect_layers(root_path)?;
        let session_layer_count = session_layers.len();
        let layers: Vec<sdf::Layer> = session_layers.into_iter().chain(root_layers).collect();
        Ok(self.make_stage(layers, session_layer_count))
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
        E: 'static,
    {
        let identifier = identifier.into();
        let session_layers = self.collect_optional_session_layers()?;
        let session_layer_count = session_layers.len();
        let layers: Vec<sdf::Layer> = session_layers
            .into_iter()
            .chain(std::iter::once(sdf::Layer::new_anonymous(identifier)))
            .collect();
        Ok(self.make_stage(layers, session_layer_count))
    }

    /// Collect layers reachable from `path`, honoring the builder's
    /// resolver, error handler, payload-loading flag, and population mask.
    fn collect_layers(&self, path: &str) -> Result<Vec<sdf::Layer>> {
        let include_prim_dependency = |p: &sdf::Path| self.population_mask.includes(p);
        let collector = layer::Collector::new(&self.resolver)
            .load_payloads(self.initial_load_set.load_payloads())
            .on_error(|e| (self.on_error)(CompositionError::Layer(e)));
        if self.population_mask.is_all() {
            collector.collect(path)
        } else {
            collector.prim_dependency_filter(&include_prim_dependency).collect(path)
        }
    }

    /// Collect the configured session layer (and its dependencies), if any.
    fn collect_optional_session_layers(&self) -> Result<Vec<sdf::Layer>> {
        match self.session_layer.as_deref() {
            Some(p) => self.collect_layers(p),
            None => Ok(Vec::new()),
        }
    }

    /// Assemble a [`Stage`] from already-collected layers. Shared
    /// construction tail for [`StageBuilder::open`] and
    /// [`StageBuilder::in_memory`]; any new `Stage` field must be wired in
    /// here once.
    fn make_stage(self, layers: Vec<sdf::Layer>, session_layer_count: usize) -> Stage
    where
        R: 'static,
        E: 'static,
    {
        let on_error = self.on_error;
        let load_payloads = self.initial_load_set.load_payloads();
        let stack = pcp::LayerStack::new(layers, session_layer_count, Box::new(self.resolver), load_payloads);
        let on_composition_error = Box::new(move |e: pcp::Error| on_error(CompositionError::Pcp(e)));
        let edit_target = EditTarget::for_layer_index(session_layer_count);
        Stage {
            graph: RefCell::new(pcp::Cache::new(stack, self.variant_fallbacks)),
            initial_load_set: self.initial_load_set,
            population_mask: self.population_mask,
            on_composition_error,
            interpolation_type: Cell::new(self.interpolation_type),
            edit_target: Cell::new(edit_target),
        }
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

    fn fixture_path(relative: &str) -> String {
        format!("{}/fixtures/{relative}", manifest_dir())
    }

    // --- Basic stage opening (vendor/usd-wg-assets) ---

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
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;

        assert_eq!(prims, vec!["/World", "/World/CubeActive"]);

        Ok(())
    }

    /// Exhaustive traversal should preserve raw composed hierarchy traversal.
    #[test]
    fn traverse_all_visits_every_composed_prim() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let mut prims = Vec::new();
        stage.traverse_all(|p| prims.push(p.as_str().to_string()))?;

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
        let base_red = sdf::Value::Vec3fVec(vec![[1.0, 0.0, 0.0]]);
        assert_ne!(value, base_red, "stronger layer opinion should win over weaker");

        Ok(())
    }

    /// A prim defined only in the stronger sublayer should appear in composed
    /// children alongside prims from the weaker layer.
    #[test]
    fn sublayer_children_union() -> Result<()> {
        let path = fixture_path("sublayer_override.usda");
        let stage = Stage::open(&path)?;

        let children = stage.prim_children("/World")?;
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
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;
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
        let children = stage.prim_children("/World/MyPrim")?;
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
        let children = stage.prim_children("/World")?;
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
        let children = stage.prim_children("/World/RefPrim")?;
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
        let props = stage.prim_properties("/World/cubeWithoutSetColor")?;
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
        let green = sdf::Value::Vec3fVec(vec![[0.0, 0.8, 0.0]]);
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
        let children = stage.prim_children("/World")?;
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
        let red = sdf::Value::Vec3fVec(vec![[0.8, 0.0, 0.0]]);
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
        let children = stage.prim_children("/Instance")?;
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
        let a_children = stage.prim_children("/Prim")?;
        assert!(
            a_children.contains(&"A".to_string()),
            "first-level child: got {a_children:?}"
        );

        let b_children = stage.prim_children("/Prim/A")?;
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
        let children = stage.prim_children("/Leaf")?;
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

        let children = stage.prim_children("/World")?;
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
        let schemas = stage.api_schemas(&geo)?;
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
        let schemas = stage.api_schemas(&sdf::Path::new("/World/Geo")?)?;
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
        let schemas = stage.api_schemas(&sdf::Path::new("/World/Geo")?)?;
        assert_eq!(schemas, vec!["C".to_string(), "B".to_string(), "A".to_string()]);
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
            stage.api_schemas(&geo)?,
            vec!["LocalAPI".to_string(), "BaseAPI".to_string()],
        );
        assert!(stage.has_api_schema(&geo, "BaseAPI")?);
        assert!(stage.has_api_schema(&geo, "LocalAPI")?);
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
            stage.api_schemas(&geo)?,
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
        let schemas = stage.api_schemas(&geo)?;
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
        assert_eq!(stage.api_schemas(&prop)?, stage.api_schemas(&prim)?);
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
        let conns = stage.connection_paths(&sdf::Path::new("/Mat.inputs:in")?)?;
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
        assert_eq!(stage.connection_paths(&input)?, vec![output.clone()]);

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

        let stage = Stage::builder().make_stage(vec![strong, weak], 0);
        let attr = crate::usd::Attribute::new(&stage, input.clone());

        assert_eq!(attr.get_connections()?, vec![target.clone()]);
        assert!(attr.remove_connection(&target)?);
        assert!(attr.get_connections()?.is_empty());

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

        let stage = Stage::builder().make_stage(vec![strong, weak], 0);
        let attr = crate::usd::Attribute::new(&stage, input.clone());
        let attr = attr.add_connection(target.clone())?;

        assert_eq!(attr.get_connections()?, vec![target.clone()]);
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

        let stage = Stage::builder().make_stage(vec![strong, weak], 0);
        let attr = crate::usd::Attribute::new(&stage, input.clone());

        assert!(attr.remove_connection(&target)?);
        assert!(attr.get_connections()?.is_empty());
        let attr = attr.add_connection(target.clone())?;

        assert_eq!(attr.get_connections()?, vec![target.clone()]);
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
        assert!(stage.api_schemas(&props)?.is_empty());
        Ok(())
    }

    #[test]
    fn has_api_schema_matches_applied() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let geo = sdf::Path::new("/World/Geo")?;
        assert!(stage.has_api_schema(&geo, "MaterialBindingAPI")?);
        assert!(!stage.has_api_schema(&geo, "SkelRootAPI")?);
        Ok(())
    }

    #[test]
    fn type_name_returns_prim_type() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        assert_eq!(
            stage.type_name(&sdf::Path::new("/World/Geo")?)?,
            Some("Mesh".to_string())
        );
        assert_eq!(stage.type_name(&sdf::Path::new("/World")?)?, Some("Xform".to_string()));
        Ok(())
    }

    fn open_stage_queries_fixture() -> Result<Stage> {
        Stage::open("fixtures/stage_queries.usda")
    }

    #[test]
    fn active_loaded() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert!(stage.is_active("/World/ActiveParent/Child")?);
        assert!(stage.is_loaded("/World/ActiveParent/Child")?);

        assert!(!stage.is_active("/World/InactiveParent")?);
        assert!(!stage.is_active("/World/InactiveParent/Child")?);
        assert!(!stage.is_loaded("/World/InactiveParent/Child")?);

        assert!(!stage.is_active("/World/Missing")?);
        Ok(())
    }

    #[test]
    fn load_none() -> Result<()> {
        let path = composition_path("payload/payload_same_folder.usda");

        let loaded = Stage::open(&path)?;
        assert_eq!(loaded.layer_count(), 2);
        assert!(loaded.is_loaded("/World")?);
        assert_eq!(loaded.prim_children("/World")?, vec!["Cube"]);

        let unloaded = Stage::builder()
            .initial_load_set(InitialLoadSet::LoadNone)
            .open(&path)?;
        assert_eq!(unloaded.initial_load_set(), InitialLoadSet::LoadNone);
        assert_eq!(unloaded.layer_count(), 1);
        assert!(!unloaded.is_loaded("/World")?);
        assert_eq!(unloaded.prim_children("/World")?, Vec::<String>::new());

        let mut prims = Vec::new();
        unloaded.traverse(|p| prims.push(p.as_str().to_string()))?;
        assert!(prims.is_empty());
        Ok(())
    }

    #[test]
    fn mask_traverse() -> Result<()> {
        let stage = Stage::builder()
            .population_mask(StagePopulationMask::new(["/World/ActiveParent/Child"]))
            .open("fixtures/stage_queries.usda")?;

        assert_eq!(stage.root_prims()?, vec!["World"]);
        assert_eq!(stage.prim_children("/World")?, vec!["ActiveParent"]);
        assert_eq!(stage.prim_children("/World/ActiveParent")?, vec!["Child"]);

        assert!(stage.has_spec("/World")?);
        assert!(stage.has_spec("/World/ActiveParent/Child")?);
        assert!(!stage.has_spec("/World/Group")?);
        assert_eq!(stage.kind("/World/Group")?, None);

        let mut prims = Vec::new();
        stage.traverse_all(|p| prims.push(p.as_str().to_string()))?;
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
        assert_eq!(stage.prim_children("/World")?, vec!["cube"]);
        assert!(!stage.has_spec("/World/invalid_reference")?);
        Ok(())
    }

    #[test]
    fn defined_abstract() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(stage.specifier("/World/OverOnly")?, Some(sdf::Specifier::Over));
        assert!(stage.is_defined("/World/ActiveParent/Child")?);
        assert!(!stage.is_defined("/World/OverOnly")?);
        assert!(!stage.is_defined("/World/OverParent/Child")?);

        assert!(stage.is_defined("/World/ClassParent/Child")?);
        assert!(stage.is_abstract("/World/ClassParent")?);
        assert!(stage.is_abstract("/World/ClassParent/Child")?);
        assert!(!stage.is_abstract("/World/ActiveParent/Child")?);
        Ok(())
    }

    #[test]
    fn instance_flag() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert!(stage.has_composition_arc("/World/Instance")?);
        assert!(stage.is_instance("/World/Instance")?);

        assert!(!stage.has_composition_arc("/World/InstanceableNoArc")?);
        assert!(!stage.is_instance("/World/InstanceableNoArc")?);
        Ok(())
    }

    #[test]
    fn model_hierarchy() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(stage.kind("/World")?, Some("assembly".to_string()));
        assert!(stage.is_model("/World")?);
        assert!(stage.is_group("/World")?);

        assert!(stage.is_model("/World/Group")?);
        assert!(stage.is_group("/World/Group")?);
        assert!(stage.is_model("/World/Group/Component")?);
        assert!(stage.is_component("/World/Group/Component")?);

        assert!(!stage.is_model("/World/Group/Subcomponent")?);
        assert!(stage.is_subcomponent("/World/Group/Subcomponent")?);

        assert_eq!(
            stage.kind("/World/InvalidComponentParent/Component")?,
            Some("component".to_string())
        );
        assert!(!stage.is_model("/World/InvalidComponentParent/Component")?);
        assert!(!stage.is_component("/World/InvalidComponentParent/Component")?);
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
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;

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
        stage.traverse_with_predicate(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

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
        stage.traverse_with_predicate(predicate, |p| prims.push(p.as_str().to_string()))?;

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
        stage.set_edit_target(EditTarget::for_layer_index(0))?; // session layer
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
        let err = stage.set_edit_target(EditTarget::for_layer_index(99)).unwrap_err();
        assert!(matches!(err, StageAuthoringError::LayerOutOfRange { .. }));
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
        assert_eq!(stage.edit_target().layer_index(), 1);
        stage.define_prim("/World")?.set_type_name("Xform")?;
        assert_eq!(stage.spec_type("/World")?, Some(sdf::SpecType::Prim));
        Ok(())
    }
}
