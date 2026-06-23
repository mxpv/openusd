//! Lazily-built cache of per-prim composition indices.
//!
//! The [`IndexCache`] is the primary interface between [`Stage`](crate::usd::Stage)
//! and the composition engine. It caches one [`PrimEntry`] per composed prim —
//! the [`PrimIndex`] plus the [`CompositionContext`] its children inherit — so
//! ancestor composition is never recomputed.
//!
//! Relocates (`layerRelocates`) are composed by the indexer as `ArcType::Relocate`
//! nodes; the cache applies each node's layer-stack relocates while folding the
//! child-name list (`compute_prim_child_names`), renaming or hiding relocated
//! sources and exposing targets in place.

use std::collections::{HashMap, HashSet};
use std::mem;

use anyhow::Result;

use crate::ar::ResolvedPath;
use crate::sdf;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{LayerOffset, Path, SpecType, Value};
use crate::tf::Token;

use super::clip::{ClipSet, ResolvedClipSet};
use super::dependencies::Dependencies;
use super::instancing::PrototypeRegistry;
use super::layer_graph::{LayerGraph, LayerStackId};
use super::prim_graph::{ArcType, Node, NodeFlags, NodeId};
use super::prim_index::{AncestorArc, CompositionContext, Demand, PrimEntry, PrimIndex};
use super::prim_resolve::InvalidTargetKind;
use super::relocates::{apply_child_relocates, chain_through_relocates, effective_relocates};
use super::{Error, LayerId, MapFunction, VariantFallbackMap};

/// Lazily-built composition graph.
///
/// Caches a [`PrimEntry`] per composed prim. When a prim is queried for the
/// first time, its index is built using the parent's cached context (if
/// available). During depth-first traversal, parents are always composed before
/// children, so the context chain is always populated.
///
/// An optional [`VariantFallbackMap`] provides fallback selections for variant
/// sets that have no authored opinion. Authored selections always take priority;
/// fallbacks are tried in order, and a set with no applicable fallback stays
/// unselected.
///
/// Recoverable composition errors are retained in
/// [`Self::composition_errors`], while operational failures are returned to the
/// caller.
pub struct IndexCache {
    /// Per-prim composition records ([`PrimEntry`]), keyed by composed path. A
    /// [`sdf::PathTable`] so [`Self::drop_index_subtree`] erases an invalidated
    /// subtree by namespace walk rather than a full scan. `pub(super)` so the
    /// instancing pass ([`super::instancing`]) can reach composed indices through
    /// [`Self::cached`].
    pub(super) entries: sdf::PathTable<PrimEntry>,
    /// Reverse `(layer, site) → prim_index_paths` map for surgical invalidation.
    deps: Dependencies,
    /// Variant fallback selections tried when no authored selection exists.
    variant_fallbacks: VariantFallbackMap,
    /// Whether payload arcs are expanded during composition, from the stage's
    /// [`InitialLoadSet`](crate::usd::InitialLoadSet). Seeds every root build's
    /// [`CompositionContext`] (see [`root_parent_context`](Self::root_parent_context)).
    load_payloads: bool,
    /// Lazily-loaded value-clip and manifest layers, keyed by resolved
    /// identifier. Clip layers do not participate in composition (spec
    /// 12.3.4), so they are held here rather than in the [`LayerGraph`](super::layer_graph::LayerGraph).
    clip_layers: HashMap<String, sdf::Layer>,
    /// Shared-prototype registry for scene-graph instancing (spec 11.3.3),
    /// internal machinery driven by the instancing glue in
    /// [`super::instancing`] (a second `impl IndexCache`). Callers go through
    /// the cache's facade methods (`is_instance` / `prototype_of` /
    /// `is_prototype` / …), never this field. Affected entries are dropped by
    /// [`Self::invalidate_prototypes`] on a prim-level change, or the whole
    /// registry by [`Self::clear_all_indices`] on a layer-stack rebuild.
    pub(super) prototypes: PrototypeRegistry,
    /// Memoized instance-proxy / prototype-descendant redirections (spec
    /// 11.3.3): a prim path mapped to the path that actually composes it
    /// ([`effective_path`](Self::effective_path) walks the namespace to find an
    /// enclosing instance, which is otherwise repeated on every descendant
    /// query). A non-redirected prim caches an identity entry, so the common
    /// non-instanced case skips the walk too. An entry holds only while the
    /// prototype registry that produced it is unchanged: it is cleared wholesale
    /// when prototypes are invalidated ([`Self::invalidate_prototypes`] /
    /// [`Self::clear_all_indices`]), and the subtree under a freshly
    /// minted `/__Prototype_N` is dropped at registration (a synthetic
    /// descendant queried before the mint cached an identity that must now
    /// redirect into the prototype namespace).
    //
    // TODO(rayon): a per-prim parallel composition driver would share this map
    // read-mostly; the entries are write-once until invalidation, so a
    // concurrent reader needs only a shared snapshot rather than a lock on the
    // hot path. Keep population off the critical section when that lands.
    pub(super) redirected_prims: HashMap<Path, Path>,
    /// One-shot errors from layer collection that the [`LayerGraph`](super::layer_graph::LayerGraph)
    /// cannot regenerate (e.g. `UnresolvedSublayer`). Set once at construction;
    /// never cleared, since nothing recomputes them.
    collection_errors: Vec<Error>,
    /// Transient errors produced by on-demand target / property-stack queries
    /// (invalid external targets, inconsistent property types). Cleared on any
    /// index invalidation so they never go stale across an edit; they are
    /// recomputed on the next query.
    //
    // TODO: repeated queries on the same conflicting property re-append within a
    // session (no intervening edit) and duplicate. Settle this by computing the
    // conflicts once at index build and having queries read them.
    query_errors: Vec<Error>,
    /// Paths whose [`ensure_index`](Self::ensure_index) call is still on the
    /// stack. Pre-caching an inherit/specialize target (and that target's own
    /// targets) re-enters `ensure_index`; a cyclic class hierarchy (e.g. two
    /// prims that inherit each other) would otherwise recurse forever before any
    /// of them is inserted into `entries`. Re-entry for an in-progress path
    /// returns early, so the cycle-closing arc simply finds no cached target and
    /// drops out of composition.
    in_progress: HashSet<Path>,
    /// An empty index returned by [`cached`](Self::cached) for a path left
    /// uncached because its build demanded a not-yet-loaded layer. A query
    /// reading it gets empty results, which the stage's query loop discards
    /// before recomposing with the demanded layer loaded.
    empty_index: PrimIndex,
    /// [`Demand`]s a build raised for a target layer that is not yet loaded,
    /// returned up from the indexer (via `BuildOutput`) and accumulated here
    /// across the builds run in a pass. [`Stage::with_cache`](crate::usd::Stage)
    /// drains it, opens the layers, and recomposes. A plain `Vec` mutated through
    /// `&mut self` — pcp keeps no interior mutability. `pub(super)` so the
    /// instancing pass can detect a demand fired mid-redirect (see
    /// [`effective_path`](Self::effective_path)).
    pub(super) pending_loads: Vec<Demand>,
    /// Monotonic counter bumped once per applied change batch
    /// ([`Changes::apply`](super::Changes::apply)), the single funnel every
    /// authoring and layer-stack edit passes through. Cached views that resolve
    /// values once and replay them (e.g. [`Stage::attribute_query`]) snapshot
    /// this and rebuild when it advances, so an edit to any opinion — even a
    /// value-only edit that leaves the prim index intact — invalidates them.
    ///
    /// It does not capture lazy prototype materialization, which can change what
    /// resolves under a synthetic `/__Prototype_N` path without an edit (see
    /// [`register_prototype`](Self::register_prototype)). A cached view must not
    /// rely on this counter alone for paths that may be empty pending such
    /// materialization.
    ///
    /// [`Stage::attribute_query`]: crate::usd::Stage::attribute_query
    revision: u64,
}

enum FieldValue {
    NotAuthored,
    Authored(Option<Value>),
}

/// The resolved source of an attribute's value at a time code, the cacheable
/// half of [`IndexCache::value_at`]. A cached view
/// ([`Stage::attribute_query`](crate::usd::Stage::attribute_query)) resolves
/// this once — paying the opinion walk and the one sample-map clone — then
/// replays it across many time codes.
pub(crate) enum AttributeValueSource {
    /// A time-independent value: a `default` opinion (local or fallback), or
    /// `None` when the attribute is unauthored, masked out, or blocked. The
    /// same value resolves at every time code.
    Static(Option<Value>),
    /// A time-sampled source — the matched map and its node's layer offset.
    /// Interpolated per query in layer time via `offset.inverse().apply(time)`,
    /// matching [`PrimIndex::resolve_value_at`](super::PrimIndex::resolve_value_at).
    TimeSamples {
        samples: sdf::TimeSampleMap,
        offset: LayerOffset,
    },
    /// Value clips are authoritative for this attribute (spec 12.3.4). Clip
    /// resolution selects a different clip layer per time, so a cached view
    /// falls back to [`IndexCache::value_at`] for every query rather than
    /// snapshotting a single source.
    Clips,
}

/// Collapses the spec sentinels for "no value" ([`Value::ValueBlock`] and
/// [`Value::None`]) to `None`, passing any real value through as `Some`. An
/// authored block stops fall-through to weaker sources yet presents as absent.
fn block_to_none(value: Value) -> Option<Value> {
    match value {
        Value::ValueBlock | Value::None => None,
        other => Some(other),
    }
}

/// The attribute's path inside a clip set's namespace: the `attr_prim + suffix`
/// path with the clip anchor prim replaced by the set's `base` prim (spec
/// 12.3.4.1.1.1). `anchor` is an ancestor of `attr_prim`, so the replacement
/// lands on a path boundary; the fallback keeps the path unchanged if it ever
/// is not a prefix.
fn clip_attr_path(anchor: &Path, base: &Path, attr_prim: &Path, suffix: &str) -> Result<Path> {
    let attr = Path::new(&format!("{attr_prim}{suffix}"))?;
    Ok(attr.replace_prefix(anchor, base).unwrap_or(attr))
}

impl IndexCache {
    /// Creates a new composition cache. The layer data lives in a separate
    /// [`LayerGraph`] owned by the [`Stage`](crate::usd::Stage) and passed to each
    /// query. `collection_errors` are the one-shot errors from layer collection
    /// the graph cannot regenerate (e.g. `UnresolvedSublayer`); per-prim build
    /// errors join them as indices are composed. The regenerable layer-graph
    /// diagnostics (sublayer cycles, invalid relocates) live on the
    /// [`LayerGraph`] and are read through [`LayerGraph::errors`].
    pub(crate) fn new(
        variant_fallbacks: VariantFallbackMap,
        load_payloads: bool,
        collection_errors: Vec<Error>,
    ) -> Self {
        Self {
            entries: sdf::PathTable::new(),
            deps: Dependencies::default(),
            variant_fallbacks,
            load_payloads,
            clip_layers: HashMap::new(),
            prototypes: PrototypeRegistry::default(),
            redirected_prims: HashMap::new(),
            collection_errors,
            query_errors: Vec::new(),
            in_progress: HashSet::new(),
            empty_index: PrimIndex::default(),
            pending_loads: Vec::new(),
            revision: 0,
        }
    }

    /// Hands the [`Demand`]s the builds run so far raised (for target layers not
    /// yet loaded) to `buf`, taking `buf`'s storage in exchange. The stage's
    /// query loop passes a buffer it reuses across passes, so the two queues
    /// ping-pong without reallocating: it opens the returned layers and
    /// recomposes until a pass demands nothing.
    pub(crate) fn swap_pending_loads(&mut self, buf: &mut Vec<Demand>) {
        mem::swap(&mut self.pending_loads, buf);
    }

    /// The current composition revision (see the [`revision`](Self::revision)
    /// field). Advances once per applied change batch.
    pub(crate) fn revision(&self) -> u64 {
        self.revision
    }

    /// Advances the composition revision, invalidating cached views that
    /// snapshot it. Called once per [`Changes::apply`](super::Changes::apply).
    pub(super) fn bump_revision(&mut self) {
        self.revision += 1;
    }

    /// Returns the recoverable composition errors encountered so far: the
    /// one-shot collection errors, the current per-prim build errors, and the
    /// transient query errors.
    pub(crate) fn composition_errors(&self) -> Vec<Error> {
        self.collection_errors
            .iter()
            .chain(self.entries.iter().flat_map(|(_, entry)| entry.errors.iter()))
            .chain(&self.query_errors)
            .cloned()
            .collect()
    }

    /// Records one-shot collection errors raised while opening a layer on demand
    /// — a missing sublayer of a reference/payload target the stage's load
    /// barrier reached. Joins the errors from root-stack collection so
    /// [`composition_errors`](Self::composition_errors) reports a lazily-loaded
    /// stack's diagnostics too. Each demanded target opens once, so a given error
    /// is recorded once.
    pub(crate) fn record_collection_errors(&mut self, errors: impl IntoIterator<Item = Error>) {
        self.collection_errors.extend(errors);
    }

    #[cfg(test)]
    fn take_composition_errors(&mut self) -> Vec<Error> {
        let errors = self.composition_errors();
        self.collection_errors.clear();
        self.query_errors.clear();
        for (_, entry) in self.entries.iter_mut() {
            entry.errors.clear();
        }
        errors
    }

    /// Loads a value-clip or manifest layer referenced by `asset_path`,
    /// anchored to the layer `anchor_layer` (the layer that authored the
    /// clip metadata). Layers are loaded on demand through the graph's
    /// resolver and cached by resolved identifier; clip layers never enter the
    /// composition [`LayerGraph`] (spec 12.3.4).
    ///
    /// Returns `Ok(None)` when the asset path cannot be resolved.
    pub(crate) fn clip_layer(
        &mut self,
        graph: &LayerGraph,
        asset_path: &str,
        anchor_layer: LayerId,
    ) -> Result<Option<&sdf::Layer>> {
        // Anchor the clip asset path to the authoring layer's location so
        // relative paths resolve like any other dependency.
        let anchor = graph.anchor_location(Some(anchor_layer));
        let clip_id = graph.layer_registry().create_identifier(asset_path, anchor.as_ref());

        if !self.clip_layers.contains_key(&clip_id) {
            let Some(data) = graph.layer_registry().open(&clip_id)? else {
                return Ok(None);
            };
            self.clip_layers
                .insert(clip_id.clone(), sdf::Layer::new(clip_id.clone(), data));
        }

        Ok(self.clip_layers.get(&clip_id))
    }

    /// Resolves an attribute's value at `time`, honoring value clips
    /// (spec 12.3.4). Strength ordering:
    ///
    /// 1. Local (`Root` arc) `timeSamples` win over clips.
    /// 2. Value clips anchored on the attribute's prim or an ancestor.
    /// 3. The strongest remaining `timeSamples` (across reference/payload arcs).
    /// 4. The strongest authored `default`.
    ///
    /// `interp` applies the stage's interpolation policy to a sample map at a
    /// given time; it is supplied by the caller so this layer stays free of any
    /// interpolation policy.
    ///
    /// [`Self::resolve_value_source`] mirrors this strength order to cache the
    /// winning source for replay; keep the two in sync when the order changes.
    pub(crate) fn value_at(
        &mut self,
        graph: &LayerGraph,
        attr_path: &Path,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        let Some((prim, suffix)) = self.ensure_attr_index(graph, attr_path)? else {
            return Ok(None);
        };
        let local_layers = graph.local_layers();

        // TODO: only the default-sourced returns below resolve their `asset`
        // values (via `anchor_asset_paths`); values from time samples
        // (`resolve_value_at`) and value clips (`resolve_clip_value`) are
        // returned with `evaluated_path` and `resolved_path` unset. To close
        // this, those resolvers must surface the contributing layer/node so it
        // can be anchored and its expression variables composed — note a clip
        // value anchors against the *clip layer*, not a host-stack opinion, so
        // it cannot reuse `asset_context` directly. Asset-valued time samples
        // and clips are rare in practice.

        // 1) Local time samples take precedence over clip data.
        if let Some(value) =
            self.cached(&prim)
                .resolve_value_at(graph, Some(&suffix), Some(&local_layers), time, interp)?
        {
            return Ok(value);
        }

        // 2) Local defaults also take precedence over clip data.
        if let FieldValue::Authored(value) =
            self.resolve_local_field_value(graph, &prim, &suffix, FieldKey::Default.as_str(), &local_layers)?
        {
            return Ok(self.anchor_asset_paths(graph, &prim, FieldKey::Default.as_str(), Some(&suffix), value));
        }

        // 3) Value clips, anchored on this prim or an ancestor. A clip set that
        //    owns the attribute resolves it authoritatively: an authored value
        //    block stops fall-through to weaker sources but presents as `None`,
        //    matching the local-default handling above and the default below.
        if let Some(value) = self.resolve_clip_value(graph, &prim, &suffix, time, interp)? {
            return Ok(block_to_none(value));
        }

        // 4) Remaining time samples (reference/payload arcs), retimed.
        if let Some(value) = self
            .cached(&prim)
            .resolve_value_at(graph, Some(&suffix), None, time, interp)?
        {
            return Ok(value);
        }

        // 5) Fall back to the strongest authored default.
        let default = self
            .cached(&prim)
            .resolve_field(FieldKey::Default.as_str(), graph, Some(&suffix))?;
        let default = self.anchor_asset_paths(graph, &prim, FieldKey::Default.as_str(), Some(&suffix), default);
        Ok(default.and_then(block_to_none))
    }

    /// Resolves the cacheable value source for an attribute (the source half of
    /// [`Self::value_at`]), so a [`Stage::attribute_query`] can replay it across
    /// time codes. Walks the same strength order as `value_at`, stopping at the
    /// first authoritative source. When value clips claim the attribute the
    /// source is [`AttributeValueSource::Clips`]: the query then falls back to
    /// `value_at` per call, since clip resolution is time-dependent.
    ///
    /// [`Stage::attribute_query`]: crate::usd::Stage::attribute_query
    pub(crate) fn resolve_value_source(
        &mut self,
        graph: &LayerGraph,
        attr_path: &Path,
    ) -> Result<AttributeValueSource> {
        let Some((prim, suffix)) = self.ensure_attr_index(graph, attr_path)? else {
            return Ok(AttributeValueSource::Static(None));
        };
        let local_layers = graph.local_layers();

        // 1) Local time samples take precedence over clip data.
        if let Some((samples, offset)) =
            self.cached(&prim)
                .resolve_time_samples_with_offset(graph, Some(&suffix), Some(&local_layers))?
        {
            return Ok(AttributeValueSource::TimeSamples { samples, offset });
        }

        // 2) Local defaults also take precedence over clip data.
        if let FieldValue::Authored(value) =
            self.resolve_local_field_value(graph, &prim, &suffix, FieldKey::Default.as_str(), &local_layers)?
        {
            let value = self.anchor_asset_paths(graph, &prim, FieldKey::Default.as_str(), Some(&suffix), value);
            return Ok(AttributeValueSource::Static(value));
        }

        // 3) Value clips, anchored on this prim or an ancestor, resolve
        //    authoritatively but per-time; defer them to `value_at`. The gate is
        //    clip participation (`clip_sample_times` returns `Some` exactly when
        //    a set sources the attribute), so a clip-bearing prim's non-clip
        //    attributes fall through to the cached arc / default tiers below.
        if self.clip_sample_times(graph, &prim, &suffix)?.is_some() {
            return Ok(AttributeValueSource::Clips);
        }

        // 4) Remaining time samples (reference/payload arcs).
        if let Some((samples, offset)) =
            self.cached(&prim)
                .resolve_time_samples_with_offset(graph, Some(&suffix), None)?
        {
            return Ok(AttributeValueSource::TimeSamples { samples, offset });
        }

        // 5) Fall back to the strongest authored default.
        let default = self
            .cached(&prim)
            .resolve_field(FieldKey::Default.as_str(), graph, Some(&suffix))?;
        let default = self.anchor_asset_paths(graph, &prim, FieldKey::Default.as_str(), Some(&suffix), default);
        Ok(AttributeValueSource::Static(default.and_then(block_to_none)))
    }

    /// Resolves an attribute's composed sample times, retimed to stage time and
    /// including value-clip contributions (the introspection counterpart of
    /// [`Self::value_at`], spec 12.3.4). `None` when no source has samples or the
    /// prim is masked out.
    ///
    /// This MUST report the times of whichever source [`Self::value_at`] would
    /// resolve the value from, so it walks the same precedence: local
    /// `timeSamples`, then a local `default` (a constant — no sample times),
    /// then clips, then arc `timeSamples`. Keep the tiers here in lockstep with
    /// `value_at`; the `clip_*` / `has_local_default` checks mirror its branches
    /// 1-4, and the consistency tests in `tests/stage.rs` pin the agreement.
    pub(crate) fn time_sample_times(&mut self, graph: &LayerGraph, attr_path: &Path) -> Result<Option<Vec<f64>>> {
        let Some((prim, suffix)) = self.ensure_attr_index(graph, attr_path)? else {
            return Ok(None);
        };
        let local_layers = graph.local_layers();
        if let Some(times) = self
            .cached(&prim)
            .resolve_time_sample_times(graph, Some(&suffix), Some(&local_layers))?
        {
            return Ok(Some(times));
        }
        // A local `default` opinion resolves to a constant value that shadows
        // clips and arc time samples (`value_at` branch 2), so the attribute has
        // no sample times.
        if self.has_local_default(graph, &prim, &suffix, &local_layers)? {
            return Ok(None);
        }
        // Value clips own the attribute when a set participates, reporting every
        // active-window boundary so a held window's switch point agrees with
        // where `value_at` changes. The participation rule (manifest declares,
        // or manifest-less with an authored sample) is the same one `clip_value_at`
        // applies per-time, but computed independently there — the two must stay
        // in agreement; the consistency tests in `tests/stage.rs` pin it.
        //
        // TODO: a manifest-less set reports only its own boundaries/samples here,
        // but `clip_value_at` falls through to weaker sources (arc `timeSamples`)
        // inside a fully-empty active window. Arc samples landing in such a gap
        // window are served by `value_at` yet absent from this list. Closing the
        // gap means unioning weaker-source sample times that fall within active
        // windows the clip set authors nothing for — a clip/arc tier crossing
        // tied to the broader `clip_value_at` unification.
        if let Some(times) = self.clip_sample_times(graph, &prim, &suffix)? {
            return Ok(Some(times));
        }
        self.cached(&prim).resolve_time_sample_times(graph, Some(&suffix), None)
    }

    /// Resolves the number of composed sample times for an attribute, including
    /// value-clip contributions. Mirrors [`Self::time_sample_times`]'s source
    /// order; keeps the count-only fast path for the common `timeSamples` case
    /// and only materializes the time list when value clips own the attribute.
    /// Zero when no source has samples or the prim is masked out.
    pub(crate) fn num_time_samples(&mut self, graph: &LayerGraph, attr_path: &Path) -> Result<usize> {
        Ok(self.time_sample_summary(graph, attr_path)?.0)
    }

    /// Whether an attribute's value may vary over time, the introspection behind
    /// [`Attribute::value_might_be_time_varying`]. True when the winning value
    /// source has more than one composed sample, or when that source is a value-
    /// clip set whose schedule alone can vary the value
    /// ([`ClipSet::may_be_time_varying`]). Resolving the source first keeps a
    /// constant local `default` / `timeSamples` from being reported as
    /// time-varying merely because it shadows a multi-clip set.
    ///
    /// [`Attribute::value_might_be_time_varying`]: crate::usd::Attribute::value_might_be_time_varying
    pub(crate) fn value_might_be_time_varying(&mut self, graph: &LayerGraph, attr_path: &Path) -> Result<bool> {
        let (count, clip_may_vary) = self.time_sample_summary(graph, attr_path)?;
        Ok(count > 1 || clip_may_vary)
    }

    /// The composed sample-time count for an attribute plus, when the winning
    /// source is a value-clip set, whether that set's schedule can vary the value
    /// ([`ClipSet::may_be_time_varying`]). Walks [`Self::value_at`]'s source
    /// precedence in one pass — local `timeSamples`, local `default` (constant),
    /// clips, then arc `timeSamples` — so [`Self::num_time_samples`] and
    /// [`Self::value_might_be_time_varying`] share a single resolution. `(0,
    /// false)` when no source has samples or the prim is masked out.
    fn time_sample_summary(&mut self, graph: &LayerGraph, attr_path: &Path) -> Result<(usize, bool)> {
        let Some((prim, suffix)) = self.ensure_attr_index(graph, attr_path)? else {
            return Ok((0, false));
        };
        let local_layers = graph.local_layers();
        if let Some(count) = self
            .cached(&prim)
            .resolve_time_sample_count(graph, Some(&suffix), Some(&local_layers))?
        {
            return Ok((count, false));
        }
        // A local `default` shadows clips and arc samples (see
        // [`Self::time_sample_times`]), so the attribute has no time samples.
        if self.has_local_default(graph, &prim, &suffix, &local_layers)? {
            return Ok((0, false));
        }
        if let Some((times, may_vary)) = self.clip_introspection(graph, &prim, &suffix)? {
            return Ok((times.len(), may_vary));
        }
        let arc = self
            .cached(&prim)
            .resolve_time_sample_count(graph, Some(&suffix), None)?
            .unwrap_or(0);
        Ok((arc, false))
    }

    /// Whether a `default` opinion is authored for the attribute in the root
    /// layer stack. Such a local default resolves to a constant value that
    /// shadows weaker time-varying sources (clips, arc `timeSamples`), matching
    /// [`Self::value_at`]'s branch 2 — so the attribute reports no sample times.
    fn has_local_default(
        &self,
        graph: &LayerGraph,
        prim: &Path,
        suffix: &str,
        local_layers: &HashSet<LayerId>,
    ) -> Result<bool> {
        Ok(matches!(
            self.resolve_local_field_value(graph, prim, suffix, FieldKey::Default.as_str(), local_layers)?,
            FieldValue::Authored(_)
        ))
    }

    /// Whether `resolved` declares the attribute at `clip_path` through its
    /// manifest. A manifest that lists the attribute makes the set own it
    /// authoritatively (spec 12.3.4.6), gap-filling rather than falling through
    /// to weaker sources. A manifest-less set returns `false` here: its
    /// ownership is per-time, resolved by each caller's own sample handling.
    /// This is the shared manifest-declaration predicate behind
    /// [`Self::clip_value_at`] and [`Self::clip_set_participates`].
    fn clip_set_declares(&mut self, graph: &LayerGraph, resolved: &ResolvedClipSet, clip_path: &Path) -> Result<bool> {
        match resolved.set.manifest_asset.as_deref() {
            Some(asset) => {
                let layer = resolved.manifest_layer.unwrap_or(resolved.asset_layer);
                Ok(matches!(self.clip_layer(graph, asset, layer)?,
                            Some(opened) if opened.data().has_spec(clip_path)))
            }
            None => Ok(false),
        }
    }

    /// Whether the resolved clip `set` participates in sourcing the attribute at
    /// `clip_path`, returning each clip's in-clip authored sample times when it
    /// does and `None` when it does not. A set participates when its manifest
    /// declares the attribute ([`Self::clip_set_declares`]), or — manifest-less —
    /// when a clip the `active` schedule selects authors a sample for it. The
    /// single participation predicate behind [`Self::first_participating_clip_set`].
    ///
    /// Participation tracks what [`Self::clip_value_at`] can reach: it selects a
    /// clip only through [`ClipSet::active_clip`], so a set with no `active`
    /// schedule sources nothing, and a manifest-less set is sourced only by the
    /// clips its schedule names — an authored-but-unscheduled clip is never read.
    fn clip_set_participates(
        &mut self,
        graph: &LayerGraph,
        resolved: &ResolvedClipSet,
        clip_path: &Path,
    ) -> Result<Option<Vec<Vec<f64>>>> {
        let set = &resolved.set;
        let declared = self.clip_set_declares(graph, resolved, clip_path)?;
        // A manifest that does not declare the attribute does not source it.
        if set.manifest_asset.is_some() && !declared {
            return Ok(None);
        }
        // With no active schedule no clip is ever selected, so the set sources
        // nothing regardless of what its clips author.
        if set.active.is_empty() {
            return Ok(None);
        }
        let mut per_clip: Vec<Vec<f64>> = Vec::with_capacity(set.asset_paths.len());
        for asset in &set.asset_paths {
            per_clip.push(self.clip_in_clip_times(graph, asset.as_str(), resolved.asset_layer, clip_path)?);
        }
        // A manifest-less set sources the attribute only where a *scheduled* clip
        // authors a sample; if no `active` entry names a sampled clip, value_at
        // falls through to weaker sources, so the set does not participate.
        let scheduled_sample = set
            .active
            .iter()
            .any(|&(_, index)| per_clip.get(index).is_some_and(|s| !s.is_empty()));
        if !declared && !scheduled_sample {
            return Ok(None);
        }
        Ok(Some(per_clip))
    }

    /// Searches `attr_prim` and its ancestors nearest-first for the first
    /// value-clip set that participates in sourcing `attr_prim + suffix`,
    /// applying `f` to it (and its per-clip sample times) and returning the
    /// result; `None` when no set participates. Centralizes the ancestor walk
    /// and per-set participation check so every clip introspection shares one
    /// notion of ownership.
    fn first_participating_clip_set<T>(
        &mut self,
        graph: &LayerGraph,
        attr_prim: &Path,
        suffix: &str,
        f: impl Fn(&ClipSet, Vec<Vec<f64>>) -> T,
    ) -> Result<Option<T>> {
        let mut anchor = attr_prim.clone();
        loop {
            let sets = {
                self.ensure_index(graph, &anchor)?;
                self.cached(&anchor).resolve_clip_sets(graph)?
            };
            for resolved in &sets {
                let base = resolved.set.prim_path.clone().unwrap_or_else(|| anchor.clone());
                let clip_path = clip_attr_path(&anchor, &base, attr_prim, suffix)?;
                if let Some(per_clip) = self.clip_set_participates(graph, resolved, &clip_path)? {
                    return Ok(Some(f(&resolved.set, per_clip)));
                }
            }
            match anchor.parent() {
                Some(parent) if !parent.is_abs_root() => anchor = parent,
                _ => return Ok(None),
            }
        }
    }

    /// The value-clip introspection for `attr_prim + suffix` from the first
    /// participating set: its stage sample times (spec 12.3.4) and whether its
    /// schedule alone can vary the value ([`ClipSet::may_be_time_varying`]).
    /// `None` when no clip set sources the attribute; `Some` exactly when a set
    /// participates, so [`Self::clip_sample_times`] doubles as the clip gate for
    /// [`Self::resolve_value_source`]. The sample-time vector may be empty for a
    /// participating set that contributes no discrete times.
    fn clip_introspection(
        &mut self,
        graph: &LayerGraph,
        attr_prim: &Path,
        suffix: &str,
    ) -> Result<Option<(Vec<f64>, bool)>> {
        self.first_participating_clip_set(graph, attr_prim, suffix, |set, per_clip| {
            (set.stage_sample_times(&per_clip), set.may_be_time_varying())
        })
    }

    /// The stage times a value-clip set contributes for `attr_prim + suffix`, or
    /// `None` when no clip set sources the attribute. Drops the time-varying flag
    /// from [`Self::clip_introspection`] for callers that need only the times.
    fn clip_sample_times(&mut self, graph: &LayerGraph, attr_prim: &Path, suffix: &str) -> Result<Option<Vec<f64>>> {
        Ok(self
            .clip_introspection(graph, attr_prim, suffix)?
            .map(|(times, _)| times))
    }

    /// The in-clip authored sample times for `clip_path` in a single clip layer,
    /// or empty when the layer is unresolved or authors no samples there.
    fn clip_in_clip_times(
        &mut self,
        graph: &LayerGraph,
        asset: &str,
        anchor_layer: LayerId,
        clip_path: &Path,
    ) -> Result<Vec<f64>> {
        Ok(self
            .clip_time_samples(graph, asset, anchor_layer, clip_path)?
            .map(|samples| samples.iter().map(|(t, _)| *t).collect())
            .unwrap_or_default())
    }

    /// Redirects `attr_path` through [`Self::effective_path`] and ensures the
    /// owning prim's index is composed, returning the owned prim path and
    /// property suffix for a subsequent [`Self::cached`] lookup. `None` when no
    /// spec exists at the path (absent or masked out).
    fn ensure_attr_index(&mut self, graph: &LayerGraph, attr_path: &Path) -> Result<Option<(Path, String)>> {
        let attr_path = &self.effective_path(graph, attr_path)?;
        if !self.has_spec_at(graph, attr_path)? {
            return Ok(None);
        }
        let prim = attr_path.prim_path();
        let suffix = attr_path.property_suffix().to_owned();
        self.ensure_index(graph, &prim)?;
        Ok(Some((prim, suffix)))
    }

    fn resolve_local_field_value(
        &self,
        graph: &LayerGraph,
        prim: &Path,
        suffix: &str,
        field: &str,
        local_layers: &HashSet<LayerId>,
    ) -> Result<FieldValue> {
        let Some(index) = self.index_at(prim) else {
            return Ok(FieldValue::NotAuthored);
        };

        for node in index.nodes() {
            let query_path = Path::new(&format!("{}{suffix}", node.path))?;
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                if !local_layers.contains(&layer) {
                    continue;
                }
                let Some(value) = graph.layer(layer).data().try_field(&query_path, field)? else {
                    continue;
                };
                return Ok(FieldValue::Authored(block_to_none(value.into_owned())));
            }
        }

        Ok(FieldValue::NotAuthored)
    }

    /// Resolves a clip value for `attr_path` at `time` by searching the
    /// attribute's prim and then its ancestors, nearest first — a nearer clip
    /// set overrides one on an ancestor (spec 12.3.4.5).
    fn resolve_clip_value(
        &mut self,
        graph: &LayerGraph,
        attr_prim: &Path,
        suffix: &str,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        let mut anchor_prim = attr_prim.clone();
        loop {
            if let Some(value) = self.clip_value_at(graph, &anchor_prim, attr_prim, suffix, time, interp)? {
                return Ok(Some(value));
            }
            match anchor_prim.parent() {
                Some(parent) if !parent.is_abs_root() => anchor_prim = parent,
                _ => return Ok(None),
            }
        }
    }

    /// Looks for a clip set anchored on `anchor_prim` that provides a value for
    /// the attribute `attr_prim + suffix` at `time`. Returns the interpolated
    /// clip value, or `None` when no applicable clip set is found.
    fn clip_value_at(
        &mut self,
        graph: &LayerGraph,
        anchor_prim: &Path,
        attr_prim: &Path,
        suffix: &str,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        // Gather the clip sets, then drop the index borrow so
        // clip layers can be loaded through `&mut self`.
        let sets = {
            self.ensure_index(graph, anchor_prim)?;
            let index = self.cached(anchor_prim);
            let sets = index.resolve_clip_sets(graph)?;
            if sets.is_empty() {
                return Ok(None);
            }
            sets
        };

        for resolved in &sets {
            let set = &resolved.set;
            let base = set.prim_path.clone().unwrap_or_else(|| anchor_prim.clone());
            let clip_path = clip_attr_path(anchor_prim, &base, attr_prim, suffix)?;

            // Resolve the manifest once: its declaration gates the set and its
            // default later fills a gap (spec 12.3.4.6).
            let manifest = set
                .manifest_asset
                .as_deref()
                .map(|asset| (asset, resolved.manifest_layer.unwrap_or(resolved.asset_layer)));

            // A manifest, when authored, declares which attributes the clips
            // provide. A set whose manifest does not declare this attribute is
            // skipped. A set that *does* declare it owns the attribute's
            // time-varying value (spec 12.3.4.6): a gap in the active clip
            // resolves to a manifest default or a value block, never to a
            // weaker value source.
            let manifest_declared = self.clip_set_declares(graph, resolved, &clip_path)?;
            if manifest.is_some() && !manifest_declared {
                continue;
            }

            let Some(active) = set.active_clip(time) else {
                continue;
            };
            let Some(asset) = set.asset_paths.get(active) else {
                continue;
            };
            let clip_time = set.map_stage_to_clip(time);

            if let Some(value) = self.clip_sample_at(
                graph,
                asset.as_str(),
                resolved.asset_layer,
                &clip_path,
                clip_time,
                interp,
            )? {
                return Ok(Some(value));
            }

            // The active clip has no sample at `clip_time`. Only a
            // manifest-declared attribute gets the gap-filling treatment;
            // without a manifest there is no assurance this set owns the
            // attribute, so fall through to weaker value sources.
            if !manifest_declared {
                continue;
            }

            // (a) Manifest default: synthesize a sample at the clip's active
            //     time (spec 12.3.4.6). Reached only when the manifest declared
            //     the attribute, so the manifest asset is authored.
            if let Some((asset, layer)) = manifest {
                if let Some(value) = self.manifest_default(graph, asset, layer, &clip_path)? {
                    return Ok(Some(value));
                }
            }

            // (b) interpolateMissingClipValues: interpolate the gap across the
            //     nearest surrounding clips (spec 12.3.4.7).
            if set.interpolate_missing {
                if let Some(value) = self.interpolate_missing_value(graph, resolved, &clip_path, time, interp)? {
                    return Ok(Some(value));
                }
            }

            // (c) No default and nothing to interpolate: the manifest-declared
            //     attribute is authoritatively absent — a value block — which
            //     must not fall through to weaker sources (spec 12.3.4.6).
            return Ok(Some(Value::ValueBlock));
        }

        Ok(None)
    }

    /// Reads the `timeSamples` map authored for `clip_path` in a single clip
    /// layer, or `None` when the layer is unresolved or authors no samples
    /// there. The shared read behind [`Self::clip_sample_at`] (which
    /// interpolates) and [`Self::clip_in_clip_times`] (which lists the times).
    fn clip_time_samples(
        &mut self,
        graph: &LayerGraph,
        asset: &str,
        anchor_layer: LayerId,
        clip_path: &Path,
    ) -> Result<Option<sdf::TimeSampleMap>> {
        Ok(match self.clip_layer(graph, asset, anchor_layer)? {
            Some(layer) => match layer.data().try_field(clip_path, FieldKey::TimeSamples.as_str())? {
                Some(value) => match value.into_owned() {
                    Value::TimeSamples(samples) => Some(samples),
                    _ => None,
                },
                None => None,
            },
            None => None,
        })
    }

    /// Reads the time samples for `clip_path` from a single clip layer and
    /// interpolates at `clip_time`. Returns `None` when the layer is
    /// unresolved or the attribute has no time samples there.
    fn clip_sample_at(
        &mut self,
        graph: &LayerGraph,
        asset: &str,
        anchor_layer: LayerId,
        clip_path: &Path,
        clip_time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        Ok(self
            .clip_time_samples(graph, asset, anchor_layer, clip_path)?
            .and_then(|samples| interp(&samples, clip_time)))
    }

    /// Reads the manifest's authored `default` for `clip_path` (spec 12.3.4.6):
    /// when the active clip has a gap, the manifest default stands in as the
    /// sample value. Returns `None` when the manifest is unresolved or holds no
    /// usable default for the attribute.
    fn manifest_default(
        &mut self,
        graph: &LayerGraph,
        manifest: &str,
        manifest_layer: LayerId,
        clip_path: &Path,
    ) -> Result<Option<Value>> {
        let value = match self.clip_layer(graph, manifest, manifest_layer)? {
            Some(layer) => layer
                .data()
                .try_field(clip_path, FieldKey::Default.as_str())?
                .map(|value| value.into_owned()),
            None => None,
        };
        Ok(value.and_then(block_to_none))
    }

    /// Fills a gap in the active clip by interpolating across the nearest
    /// surrounding clips that contribute a value (spec 12.3.4.7). Each
    /// contributing clip is anchored on the stage timeline at the active stage
    /// time it owns and valued by its sample there; `interp` then brackets
    /// `time` between the nearest such anchors, exactly as if the clips' samples
    /// formed one virtual sample map. The forward bracket is the next
    /// contributing clip's start time and the backward bracket the previous
    /// one's, matching the C++ resolver. When only one side contributes, its
    /// value is held across the gap.
    fn interpolate_missing_value(
        &mut self,
        graph: &LayerGraph,
        resolved: &ResolvedClipSet,
        clip_path: &Path,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Value>> {
        let set = &resolved.set;
        let anchor = resolved.asset_layer;
        // Position of the active clip among the `active` entries at `time`.
        let active_pos = set.active.iter().rposition(|&(stage, _)| stage <= time).unwrap_or(0);

        // Forward: nearest later clip that contributes, anchored at its start.
        let mut upper = None;
        for &(stage, idx) in set.active.iter().skip(active_pos + 1) {
            if let Some(asset) = set.asset_paths.get(idx) {
                let clip_time = set.map_stage_to_clip(stage);
                if let Some(value) = self.clip_sample_at(graph, asset.as_str(), anchor, clip_path, clip_time, interp)? {
                    upper = Some((stage, value));
                    break;
                }
            }
        }

        // Backward: nearest earlier clip that contributes, anchored at its start.
        let mut lower = None;
        for &(stage, idx) in set.active[..active_pos].iter().rev() {
            if let Some(asset) = set.asset_paths.get(idx) {
                let clip_time = set.map_stage_to_clip(stage);
                if let Some(value) = self.clip_sample_at(graph, asset.as_str(), anchor, clip_path, clip_time, interp)? {
                    lower = Some((stage, value));
                    break;
                }
            }
        }

        Ok(match (lower, upper) {
            (Some((lt, lv)), Some((ut, uv))) => interp(&vec![(lt, lv), (ut, uv)], time),
            (Some((_, value)), None) | (None, Some((_, value))) => Some(value),
            (None, None) => None,
        })
    }

    /// Read-only access to the dependency map for change-driven invalidation.
    pub(super) fn dependencies(&self) -> &Dependencies {
        &self.deps
    }

    /// Returns `true` if a composed prim index is currently cached at `path`.
    pub fn is_indexed(&self, path: &Path) -> bool {
        self.entries.contains_key(path)
    }

    /// Borrows the composed index at `path`, or `None` when no entry is cached.
    ///
    /// The projection out of the per-prim [`PrimEntry`] store, used where an
    /// absent entry must be distinguished from a present one. Callers that want
    /// the empty-index fallback for an uncached path use [`cached`](Self::cached).
    fn index_at(&self, path: &Path) -> Option<&PrimIndex> {
        self.entries.get(path).map(|entry| &entry.index)
    }

    /// Borrows the cached index at `path`.
    ///
    /// Callers use this where composition has already guaranteed the index is
    /// present (a prim's index is built before any query that reads it, and
    /// children build after their parents). When the build was left uncached
    /// because it demanded a not-yet-loaded layer, an empty index is returned:
    /// the query reads empty results and the stage's query loop discards them,
    /// recomposing once the demanded layer is loaded. Absence is therefore always
    /// the transient demanded-layer case — never a logic error — under the
    /// loop's guarantee that a demanded build is retried.
    pub(super) fn cached(&self, path: &Path) -> &PrimIndex {
        self.index_at(path).unwrap_or(&self.empty_index)
    }

    /// Number of cached prim indices.
    pub fn indexed_count(&self) -> usize {
        self.entries.len()
    }

    /// Caches a fully composed `index` at `path` with the `context` its children
    /// inherit and its recoverable build `errors`, and registers its
    /// dependencies. The single insertion point for the per-prim [`PrimEntry`]
    /// store, shared by the ordinary [`build_index`](Self::build_index) path and
    /// the materialized-prototype path (which has no spec to build from, so it
    /// passes no errors).
    pub(super) fn cache_index(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        index: PrimIndex,
        context: CompositionContext,
        errors: Vec<Error>,
    ) {
        self.deps.add(path, &index, graph);
        self.entries.insert(path.clone(), PrimEntry { index, context, errors });
    }

    /// The composition context for a namespace-root prim: empty except for the
    /// stage's variant fallbacks. Used to seed the root of an ordinary build and
    /// of a materialized prototype.
    pub(super) fn root_parent_context(&self) -> CompositionContext {
        CompositionContext {
            variant_fallbacks: self.variant_fallbacks.clone(),
            load_payloads: self.load_payloads,
            ..Default::default()
        }
    }

    /// Drop a single prim's cached entry (its index, child context, and build
    /// errors) along with its dependency registrations. The transient query
    /// errors are cleared too — they may reference the dropped prim and are
    /// recomputed on the next query.
    pub(super) fn drop_index(&mut self, path: &Path) {
        self.entries.remove(path);
        self.deps.remove(path);
        self.query_errors.clear();
    }

    /// Drops every cached index that recorded a
    /// [`MalformedLayer`](Error::MalformedLayer) error so it recomposes and
    /// re-demands the target. The arc to an unreadable target was dropped, so
    /// these indices carry no dependency on it and an ordinary layer-stack
    /// invalidation misses them; the stage calls this when an edit clears the
    /// graph's recorded load failures, since the target may now be readable.
    pub(crate) fn drop_load_failed_indices(&mut self) {
        let failed: Vec<Path> = self
            .entries
            .iter()
            .filter(|(_, entry)| entry.errors.iter().any(|e| matches!(e, Error::MalformedLayer { .. })))
            .map(|(path, _)| path.clone())
            .collect();
        if failed.is_empty() {
            return;
        }
        for path in failed {
            self.drop_index(&path);
        }
        self.bump_revision();
    }

    /// Spec-tier change consumer (C++ `Pcp_RescanForSpecs`): refresh, in place,
    /// which sites contribute opinions after an inert spec add or remove at
    /// `(layer, path)`.
    ///
    /// Such an edit authors no arc and no significant field, so it usually only
    /// flips each node's `has_specs` flag at the site. Every cached index that
    /// reads the site (the local prim and every dependent, found through the
    /// reverse dependency map) has the flag recomputed from live layer data with
    /// no rebuild. An index is dropped — to be rebuilt on the next query — only
    /// when an in-place refresh cannot make it current: the local prim holds no
    /// node at the site (a prior "no spec here" result), or a dependent had
    /// *culled* the site as an empty arc target that the spec now fills in, which
    /// must un-cull and graft the target's subtree.
    pub(super) fn rescan_specs(&mut self, graph: &LayerGraph, layer: LayerId, path: &Path) {
        for prim in self.deps.exact_lookup(layer, path) {
            let rebuild = if let Some(index) = self.entries.get_mut(&prim).map(|entry| &mut entry.index) {
                let refresh = index.refresh_has_specs_at(layer, path, graph);
                // The local prim is one of its own dependents (it reads its own
                // site). Drop it when it carries no contributing node there; drop
                // any index whose culled site the spec just filled in.
                refresh.needs_rebuild || (prim == *path && !refresh.contributing)
            } else {
                false
            };
            if rebuild {
                self.drop_index(&prim);
            }
        }
        self.query_errors.clear();
    }

    /// Drop a prim's cached index and every namespace descendant. Used by
    /// [`change::Changes`](super::change::Changes) when a significant change
    /// touches `prefix` — the topology may have changed for the entire
    /// subtree, so every dependent index is invalidated.
    ///
    /// Walking the `prefix` subtree of the [`sdf::PathTable`] yields the removed
    /// entries, whose paths forward the cleanup to the parallel `deps` map; each
    /// removed [`PrimEntry`] already carries its own index, context, and errors.
    pub(super) fn drop_index_subtree(&mut self, prefix: &Path) {
        // `Path::has_prefix("")` returns `true` for every absolute path, so
        // a default-constructed `Path` would silently wipe the entire
        // cache without any layer-stack rebuild — almost certainly a
        // caller bug. Catch it loudly in debug builds; the absolute root
        // (`/`) is the legitimate "blow everything" prefix.
        debug_assert!(
            !prefix.is_empty(),
            "drop_index_subtree called with empty prefix — use Path::abs_root() to drop everything",
        );
        for (victim, _) in self.entries.remove_subtree(prefix) {
            self.deps.remove(&victim);
        }
        self.query_errors.clear();
    }

    /// Drop every cached index, context, and dependency entry — plus the
    /// shared-prototype registry and its redirection memo — without touching the
    /// layer stack's precomputed state. Use this for a layer-stack rebuild, where
    /// every cached prim must be re-evaluated; clearing the registry here (rather
    /// than dropping each `/__Prototype_N` subtree first) avoids re-scanning the
    /// cache per prototype only to wipe it wholesale.
    pub(super) fn clear_all_indices(&mut self) {
        self.entries.clear();
        self.deps.clear();
        self.query_errors.clear();
        self.prototypes.clear();
        self.redirected_prims.clear();
    }

    /// Invalidates the cache after a layer-set change restructures only some
    /// prims: advances the composition revision (so cached value views rebuild)
    /// and drops just the cached indices that read one of the `affected` layers,
    /// via [`drop_indices_touching_layers`](Self::drop_indices_touching_layers).
    /// Used for a layer-muting toggle and for a demanded layer that introduces
    /// relocates; in both cases the graph's precomputed layer-stack state is
    /// rebuilt by the mutation itself, so the cache is all that remains. Matches
    /// the final composed result of a
    /// [`clear_all_indices`](Self::clear_all_indices) with less recomposition.
    pub(crate) fn invalidate_layers(&mut self, graph: &LayerGraph, affected: &HashSet<LayerId>) {
        self.bump_revision();
        self.drop_indices_touching_layers(graph, affected);
    }

    /// Drop every cached prim index whose composition reads one of the
    /// `affected` layers — together with its namespace descendants and any
    /// prototype the drops touch — leaving indices that read none of them
    /// cached. The incremental counterpart of [`clear_all_indices`](Self::clear_all_indices)
    /// for a layer-muting change: muting or unmuting a layer can only restructure
    /// prims that compose against a layer stack containing it (C++ `PcpChanges`
    /// layer-stack fanout), so the rest of the cache stays warm.
    ///
    /// `affected` is [`LayerGraph::mute_fanout`](super::layer_graph::LayerGraph)'s
    /// result: the toggled layer and every layer whose subtree contains it. A
    /// node's layer stack lists the members it resolved against, and a stack
    /// contains the toggled layer iff its root does, so an index whose dependency
    /// nodes touch an `affected` layer is exactly one whose composition the toggle
    /// can change. An index that skipped a reference/payload arc because the
    /// target root was muted keeps no node for it, so its recorded muted targets
    /// (see [`PrimIndex::muted_external_targets`]) are checked too — without that,
    /// unmuting the target could not find the index to recompose.
    fn drop_indices_touching_layers(&mut self, graph: &LayerGraph, affected: &HashSet<LayerId>) {
        if affected.is_empty() {
            return;
        }
        // Collect the roots first: `drop_index_subtree` mutates `entries`, and a
        // dropped subtree may hold further matches that would be revisited.
        //
        // TODO(perf): this scans every cached index (the reverse `Dependencies`
        // map can't scope it — an index that skipped a muted target keeps no node
        // for it, so it registered no dependency site to find it by), and the
        // per-victim `drop_index_subtree` below is itself an O(n) cache scan. The
        // scan's per-index predicate is independent (`TODO(rayon)`); the drops
        // could batch into one prefix-filtered pass.
        let victims: Vec<Path> = self
            .entries
            .iter()
            .filter(|(_, entry)| {
                // A cached node resolves its `LayerStackId` against the
                // already-mutated graph here, so the two prongs are both needed and
                // complementary; correctness rests on the invariant that whenever a
                // node's stack contained a toggled layer, one of these holds:
                //   * the frozen `representative` (the stack's strongest member,
                //     recorded at composition) is in `affected` — this catches a
                //     toggle of a `Sublayer(L)` stack's own root `L`, whose live
                //     stack now resolves empty so the member scan would miss it;
                //   * a surviving resolved member is in `affected` — this catches a
                //     toggle deeper in the stack (e.g. a root sublayer on a stage
                //     with session layers, where the representative is a session
                //     layer outside the fanout but the root layer remains and is in
                //     `affected`).
                // The invariant holds because [`mute_fanout`](super::layer_graph::LayerGraph)'s
                // `ancestors_including` puts every layer whose subtree contains the
                // toggled one into `affected` (so a sublayer stack's root is always
                // in it), and the root anchor covers session-layer mutes. Pinned by
                // `mute_sublayer_drops_root_stack_index` / `mute_keeps_independent_index`;
                // do not narrow to a representative-only check.
                entry.index.dependency_nodes().any(|node| {
                    affected.contains(&node.layer_id())
                        || graph
                            .layer_stack(node.layer_stack_id())
                            .iter()
                            .any(|&(li, _)| affected.contains(&li))
                }) || entry
                    .index
                    .muted_external_targets()
                    .iter()
                    .any(|li| affected.contains(li))
            })
            .map(|(path, _)| path.clone())
            .collect();
        // Evict prototypes whose instances or roots are among the victims, as the
        // prim-tier path in [`Changes::apply`](super::change::Changes::apply) does.
        self.invalidate_prototypes(&victims);
        for path in &victims {
            self.drop_index_subtree(path);
        }
    }

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    pub fn has_spec(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        let path = &self.effective_path(graph, path)?;
        self.has_spec_at(graph, path)
    }

    /// Resolves a value over the composition nodes of a property's owning prim,
    /// strongest first, reading each contributing layer live. `path` must be a
    /// property path: it is re-anchored onto each node's prim (crossing the
    /// `.` separator) and `probe` is called with that node's layer and the
    /// re-anchored property path; the first `Some` wins.
    ///
    /// Reading live — rather than from a property-keyed index — keeps results
    /// correct after a property spec is authored, since authoring a property
    /// never reshapes the owning prim's composition graph (the prim index
    /// stays valid).
    fn find_property_node<T>(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        mut probe: impl FnMut(&sdf::Layer, &Path) -> Option<T>,
    ) -> Result<Option<T>> {
        let prim_path = path.prim_path();
        self.ensure_index(graph, &prim_path)?;
        let Some(index) = self.index_at(&prim_path) else {
            return Ok(None);
        };
        for node in index.nodes() {
            let Some(prop_path) = path.replace_prefix(&prim_path, &node.path) else {
                continue;
            };
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                if let Some(found) = probe(graph.layer(layer), &prop_path) {
                    return Ok(Some(found));
                }
            }
        }
        Ok(None)
    }

    /// Like [`Self::has_spec`], but assumes `path` has already been redirected
    /// through [`Self::effective_path`]. Callers that redirected the path
    /// themselves (e.g. [`Self::value_at`]) use this to avoid redirecting twice.
    fn has_spec_at(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_property_path() {
            return Ok(self
                .find_property_node(graph, path, |layer, p| layer.data().has_spec(p).then_some(()))?
                .is_some());
        }
        self.ensure_index(graph, path)?;
        Ok(self.index_at(path).is_some_and(|idx| !idx.is_empty()))
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    ///
    /// For a property path the type is read live from the owning prim's
    /// composition nodes (see [`Self::find_property_node`]) rather than from a
    /// property-keyed index, so a property spec added after this path was first
    /// queried is picked up instead of a stale cached `None`.
    pub fn spec_type(&mut self, graph: &LayerGraph, path: &Path) -> Result<Option<SpecType>> {
        let path = &self.effective_path(graph, path)?;
        if path.is_property_path() {
            return self.find_property_node(graph, path, |layer, p| layer.data().spec_type(p));
        }
        self.ensure_index(graph, path)?;
        let Some(index) = self.index_at(path) else {
            return Ok(None);
        };
        for node in index.nodes() {
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                if let Some(ty) = graph.layer(layer).data().spec_type(&node.path) {
                    return Ok(Some(ty));
                }
            }
        }
        Ok(None)
    }

    /// Returns `true` if the composed prim index contains any non-local arc.
    pub(crate) fn has_composition_arc(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        self.ensure_index(graph, path)?;
        Ok(self.index_at(path).is_some_and(|index| index.has_composition_arc()))
    }

    /// Captures the target layer identifier and namespace mapping of the
    /// strongest node on `prim_path` whose arc satisfies `matches`, for building
    /// an arc-based edit target (C++ `UsdEditTarget(UsdPrim, ...)`).
    ///
    /// Considers only nodes that author a spec and are not permission-denied, in
    /// strength order. Returns `None` when none match. The mapping is the node's
    /// `map_to_root` with variant selections stripped (the
    /// [`map_to_root_for_targets`](PrimIndex::map_to_root_for_targets) form), so
    /// it is oriented spec → scene and ready to query in reverse for authoring.
    ///
    /// An instance-proxy path redirects to its shared prototype (the same
    /// [`effective_path`](Self::effective_path) redirection value resolution
    /// uses), so the arc captured is the prototype's, not an instance-local
    /// opinion that composition discards. The returned mapping is therefore
    /// oriented in the prototype's namespace, not the proxy's.
    pub(crate) fn edit_target_node_info(
        &mut self,
        graph: &LayerGraph,
        prim_path: &Path,
        matches: impl Fn(ArcType) -> bool,
    ) -> Result<Option<(String, MapFunction, Option<String>)>> {
        let prim_path = self.effective_path(graph, prim_path)?.prim_path();
        self.ensure_index(graph, &prim_path)?;
        let Some(index) = self.index_at(&prim_path) else {
            return Ok(None);
        };
        Ok(index.nodes().find_map(|node| {
            (matches(node.arc) && node.has_specs() && !node.is_permission_denied()).then(|| {
                // The identifier of the layer stack the node composes in: `None`
                // for the stage root stack, the referenced asset's root layer for
                // a sublayer stack. The edit target carries this so its authoring
                // stack is known exactly rather than re-inferred from layer
                // membership (ambiguous when a referenced asset is also a root
                // sublayer).
                let stack_root = match node.layer_stack_id() {
                    LayerStackId::Root => None,
                    LayerStackId::Sublayer(root) => Some(graph.identifier(root).to_string()),
                };
                (
                    graph.identifier(node.layer_id()).to_string(),
                    index.map_to_root_for_targets(node),
                    stack_root,
                )
            })
        }))
    }

    /// Resolves a field value from the strongest opinion across all composition nodes.
    ///
    /// Layer metadata authored on the pseudo-root is resolved directly from
    /// the root layer and does not compose with sublayers or arcs. The
    /// pseudo-root's `primChildren` field remains a child-list query and is
    /// handled by normal composition.
    pub fn resolve_field(&mut self, graph: &LayerGraph, path: &Path, field: &str) -> Result<Option<Value>> {
        let path = &self.effective_path(graph, path)?;
        if path.is_abs_root() && field != ChildrenKey::PrimChildren.as_str() {
            return self.root_layer_field(graph, field);
        }

        if path.is_property_path() {
            let prim_path = path.prim_path();
            let prop_suffix = path.property_suffix();
            self.ensure_index(graph, &prim_path)?;
            let value = self.cached(&prim_path).resolve_field(field, graph, Some(prop_suffix))?;
            Ok(self.anchor_asset_paths(graph, &prim_path, field, Some(prop_suffix), value))
        } else {
            self.ensure_index(graph, path)?;
            let value = self.cached(path).resolve_field(field, graph, None)?;
            Ok(self.anchor_asset_paths(graph, path, field, None, value))
        }
    }

    /// Fills the resolved path on any `asset` / `asset[]` value just resolved,
    /// anchoring each authored path against the layer of the strongest opinion
    /// (C++ `UsdStage::_MakeResolvedAssetPaths`). Non-asset values pass through;
    /// asset paths nested inside a dictionary value are not recursed into, only
    /// top-level `asset` / `asset[]` fields are resolved.
    ///
    /// TODO(perf): each asset read re-runs `Resolver::resolve` (a filesystem
    /// hit); a per-(layer, path) resolution cache would avoid repeating it.
    fn anchor_asset_paths(
        &self,
        graph: &LayerGraph,
        prim_path: &Path,
        field: &str,
        prop_suffix: Option<&str>,
        value: Option<Value>,
    ) -> Option<Value> {
        match value? {
            Value::AssetPath(asset) => {
                let needs_expr = sdf::expr::is_expression(asset.as_str());
                let (anchor, vars) = self.asset_context(graph, prim_path, field, prop_suffix, needs_expr);
                Some(Value::AssetPath(Self::resolve_asset_path(
                    graph,
                    asset,
                    anchor.as_ref(),
                    &vars,
                )))
            }
            Value::AssetPathVec(assets) => {
                let needs_expr = assets.iter().any(|a| sdf::expr::is_expression(a.as_str()));
                let (anchor, vars) = self.asset_context(graph, prim_path, field, prop_suffix, needs_expr);
                let resolved = assets
                    .into_iter()
                    .map(|asset| Self::resolve_asset_path(graph, asset, anchor.as_ref(), &vars))
                    .collect();
                Some(Value::AssetPathVec(resolved))
            }
            other => Some(other),
        }
    }

    /// The inputs for resolving `field`'s asset value, taken from its strongest
    /// opinion: the resolved location of that opinion's layer (the anchor for a
    /// relative path) and, when `needs_expr` is set, the `expressionVariables`
    /// in scope at that opinion's node. Computed once so every element of an
    /// `asset[]` reuses it; the variables are read only when an authored path
    /// is actually an expression.
    fn asset_context(
        &self,
        graph: &LayerGraph,
        prim_path: &Path,
        field: &str,
        prop_suffix: Option<&str>,
        needs_expr: bool,
    ) -> (Option<ResolvedPath>, HashMap<String, Value>) {
        let Some(index) = self.index_at(prim_path) else {
            return (None, HashMap::new());
        };
        let Some((layer, node)) = index.strongest_opinion(field, graph, prop_suffix) else {
            return (None, HashMap::new());
        };
        let anchor = graph.anchor_location(Some(layer));
        let vars = if needs_expr {
            index.composed_expr_vars(node, graph)
        } else {
            HashMap::new()
        };
        (anchor, vars)
    }

    /// Resolves `asset` against `anchor` (its source layer's resolved location)
    /// and returns it with the evaluated and resolved paths recorded.
    ///
    /// A variable expression is evaluated against `expr_vars` to the path used
    /// as input to resolution (C++ `SdfAssetPath::GetAssetPath`); a malformed
    /// or non-string expression leaves both derived paths unset. Resolution
    /// owns the derived paths: the result is rebuilt from the authored path so
    /// any prior evaluated/resolved path is discarded.
    ///
    /// TODO: a failed expression is dropped silently, unlike a reference/payload
    /// arc asset-path expression which records `Error::InvalidExpression`
    /// (`prim_index::resolve_arc_asset_path`). Surfacing it needs an error
    /// channel through value resolution (`value_at` returns `Result<Option>` but
    /// this runs after the value is produced).
    fn resolve_asset_path(
        graph: &LayerGraph,
        asset: sdf::AssetPath,
        anchor: Option<&ResolvedPath>,
        expr_vars: &HashMap<String, Value>,
    ) -> sdf::AssetPath {
        let mut asset = sdf::AssetPath::new(asset.into_string());
        if asset.is_empty() {
            return asset;
        }
        // The per-element `is_expression` is load-bearing for `asset[]`: the
        // caller's `needs_expr` is true if *any* element is an expression, so a
        // plain element in a mixed array must still skip evaluation.
        let identifier = if sdf::expr::is_expression(asset.as_str()) {
            let Ok(evaluated) = sdf::expr::evaluate_asset_path(asset.as_str(), expr_vars) else {
                return asset;
            };
            let identifier = graph.layer_registry().create_identifier(&evaluated, anchor);
            asset.set_evaluated_path(evaluated);
            identifier
        } else {
            graph.layer_registry().create_identifier(asset.as_str(), anchor)
        };
        if let Some(resolved) = graph.layer_registry().resolve(&identifier) {
            asset.set_resolved_path(resolved.to_string_lossy().into_owned());
        }
        asset
    }

    /// Returns the composed `apiSchemas` list for a prim.
    pub fn api_schemas(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<Token>> {
        let path = self.effective_path(graph, &path.prim_path())?;
        self.ensure_index(graph, &path)?;
        self.cached(&path)
            .resolve_token_list_op(FieldKey::ApiSchemas, graph, None)
    }

    /// Resolves the `clipSets` strength-ordering list-op on the prim at `path`,
    /// folding the list-op edits across every contributing layer (spec 12.2.6).
    /// `None` when `clipSets` is unauthored (clip sets fall back to name order).
    pub fn clip_sets_list_op(&mut self, graph: &LayerGraph, path: &Path) -> Result<Option<sdf::StringListOp>> {
        let path = self.effective_path(graph, &path.prim_path())?;
        self.ensure_index(graph, &path)?;
        self.cached(&path).clip_sets_list_op(graph)
    }

    /// Returns the composed `connectionPaths` list for an attribute path,
    /// folding list-op edits (prepend / append / add / delete) across every
    /// contributing layer. Non-property paths trivially return an empty list.
    pub fn connection_paths(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<Path>> {
        self.property_targets(graph, path, FieldKey::ConnectionPaths)
    }

    /// Returns the composed raw `targetPaths` list for a relationship path,
    /// folding list-op edits (prepend / append / add / delete) across every
    /// contributing layer. Non-property paths trivially return an empty list.
    ///
    /// These are the raw targets (the resolved `targetPaths` list op, spec
    /// 12.4); target forwarding — recursively chasing relationship-to-
    /// relationship chains — is not applied here.
    pub fn relationship_targets(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<Path>> {
        self.property_targets(graph, path, FieldKey::TargetPaths)
    }

    /// Returns the forwarded `targetPaths` for a relationship (spec 12.4):
    /// a target that resolves to a relationship is replaced, recursively, by
    /// that relationship's own forwarded targets. Every other target is kept
    /// as-is — prim paths, attribute paths, and any target that does not
    /// resolve to a relationship (a dangling or unloaded path). This matches
    /// C++ `UsdRelationship::GetForwardedTargets`, which forwards only through
    /// live relationships. Cycles are broken (each relationship is followed
    /// once) and duplicates collapse, keeping first occurrence.
    ///
    /// The walk uses an explicit stack rather than recursion (mirroring
    /// [`crate::usd::ConnectionGraph::resolve_chain`]) so a deep relationship
    /// chain cannot overflow the call stack.
    ///
    /// `is_populated` reports whether a prim is inside the stage's working set.
    /// A target relationship on a prim outside the set is not followed — its
    /// raw targets would be empty under the population mask anyway — so the
    /// forwarded result never leaks scene the mask excludes (it stays
    /// consistent with [`Self::relationship_targets`] on that path).
    pub fn forwarded_relationship_targets(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        is_populated: &dyn Fn(&Path) -> bool,
    ) -> Result<Vec<Path>> {
        let mut out = Vec::new();
        let mut emitted = HashSet::new();
        let mut followed = HashSet::new();
        followed.insert(path.clone());

        // Seed with the queried relationship's raw targets. Targets are pushed
        // reversed so the strongest (first) target is popped and resolved
        // first, preserving authored order in `out`.
        let mut stack: Vec<Path> = self.relationship_targets(graph, path)?.into_iter().rev().collect();
        while let Some(target) = stack.pop() {
            // Only property targets can be relationships; a prim-path target is
            // always terminal. Classify property targets by composed spec type.
            let is_relationship =
                target.is_property_path() && matches!(self.spec_type(graph, &target)?, Some(SpecType::Relationship));
            if is_relationship {
                // Don't follow a relationship the mask excludes; a masked-out
                // prim contributes no composed targets.
                if !is_populated(&target.prim_path()) {
                    continue;
                }
                if !followed.insert(target.clone()) {
                    continue; // already followed — break the cycle
                }
                stack.extend(self.relationship_targets(graph, &target)?.into_iter().rev());
            } else if emitted.insert(target.clone()) {
                out.push(target);
            }
        }
        Ok(out)
    }

    /// Composes a path-list-op property field (`connectionPaths` or
    /// `targetPaths`) by folding list-op edits across every contributing layer
    /// and mapping targets through composition arcs into the stage namespace.
    /// Both fields follow generic list-op value resolution (spec 12.2.6).
    fn property_targets(&mut self, graph: &LayerGraph, path: &Path, field: FieldKey) -> Result<Vec<Path>> {
        self.compose_property_paths(graph, path, field, false)
    }

    /// Composes a path-list-op property field into stage namespace. With
    /// `deleted` it returns the field's deleted entries (the `delete`-op paths);
    /// otherwise the resolved targets/connections. On an instance proxy both
    /// resolve against the shared prototype's subtree and map the
    /// prototype-namespace results back to the queried instance (spec 11.3.4
    /// under 11.3.3).
    fn compose_property_paths(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        field: FieldKey,
        deleted: bool,
    ) -> Result<Vec<Path>> {
        if !path.is_property_path() {
            return Ok(Vec::new());
        }
        let prim = path.prim_path();
        let prop_suffix = path.property_suffix().to_owned();
        let anchor = self.redirect_anchor(graph, &prim)?;

        let resolved_prim = match &anchor {
            Some((origin, canonical)) => prim.replace_prefix(origin, canonical).unwrap_or_else(|| prim.clone()),
            None => prim.clone(),
        };
        self.ensure_index(graph, &resolved_prim)?;
        // A connection/relationship target authored in a class that translates but
        // names a different instance of that class is dropped from that class
        // node's contribution (C++ `_TargetInClassAndTargetsInstance`). The cache
        // precomputes the cross-prim instance set; the per-node target walk
        // consults it so a valid stronger opinion for the same path survives.
        let instance_targets = if deleted {
            HashSet::new()
        } else {
            self.compute_instance_targets(graph, &resolved_prim, field, &prop_suffix)?
        };

        // The resolved-targets walk translates each target through its
        // contributing node's map (relocates folded in), so it needs no separate
        // relocate-chaining. The deleted-paths walk has no per-node origin, so it
        // still chains every entry through the prim's effective relocates.
        let index = self.cached(&resolved_prim);
        let (mut targets, invalid) = if deleted {
            (
                index.resolve_path_list_op_deleted(field, graph, Some(&prop_suffix))?,
                Vec::new(),
            )
        } else {
            index.resolve_path_list_op_validated(field, graph, Some(&prop_suffix), &instance_targets)?
        };
        if deleted && graph.has_relocates() {
            let relocates = effective_relocates(graph, &resolved_prim, &self.entries);
            for target in &mut targets {
                *target = chain_through_relocates(target, &relocates, None);
            }
        }

        // Targets dropped during composition are reported in authored order, the
        // `invalid` list already honoring list-op composition (a target shadowed
        // by a stronger explicit, or retracted by a delete, is not reported).
        let is_connection = matches!(field, FieldKey::ConnectionPaths);
        for inv in invalid {
            self.query_errors.push(match inv.kind {
                InvalidTargetKind::External => Error::InvalidExternalTargetPath {
                    is_connection,
                    target: inv.target,
                    property: inv.property,
                    layer: graph.identifier(inv.layer).to_string(),
                    arc: inv.arc,
                    arc_root: inv.arc_root,
                    composing: prim.clone(),
                },
                InvalidTargetKind::Instance => Error::InvalidInstanceTargetPath {
                    is_connection,
                    target: inv.target,
                    property: inv.property,
                    layer: graph.identifier(inv.layer).to_string(),
                    composing: prim.clone(),
                },
            });
        }

        // Targets resolved in the shared prototype's namespace map back to the
        // queried instance (spec 11.3.4 under 11.3.3).
        if let Some((origin, target_prefix)) = &anchor {
            for target in &mut targets {
                if let Some(remapped) = target.replace_prefix(target_prefix, origin) {
                    *target = remapped;
                }
            }
        }
        Ok(targets)
    }

    /// Computes the cross-prim set of connection/relationship targets authored in
    /// a class (an inherit node) that name a *different* instance of that class
    /// (C++ `_TargetInClassAndTargetsInstance`), keyed by the `(target, property)`
    /// node-namespace pair the target walk matches on.
    ///
    /// This is the purely structural fact "is this class target an instance
    /// target"; list-op composition (delete / explicit shadowing) and the actual
    /// dropping/reporting are left to `resolve_path_list_op_validated`, which
    /// consults this set per node contribution. A target inside the class itself
    /// (`connectionPathInsideInheritedClass`) is never an instance target.
    fn compute_instance_targets(
        &mut self,
        graph: &LayerGraph,
        resolved_prim: &Path,
        field: FieldKey,
        prop_suffix: &str,
    ) -> Result<HashSet<(Path, Path)>> {
        // Phase 1: gather candidates that translate, releasing the index borrow
        // before the cross-prim composition in phase 2.
        let mut candidates: Vec<InstanceCandidate> = Vec::new();
        let mut seen: HashSet<(Path, Path)> = HashSet::new();
        {
            let index = self.cached(resolved_prim);
            for node in index.nodes() {
                if node.arc != ArcType::Inherit || !node.has_specs() || node.is_permission_denied() {
                    continue;
                }
                let class_path = node.path_at_introduction();
                let members = graph.layer_stack(node.layer_stack_id());
                let class_layers: Vec<LayerId> = members.iter().map(|(l, _)| *l).collect();
                let map = index.map_to_root_for_targets(node);
                let property = Path::new(&format!("{}{prop_suffix}", node.path))?;
                for &(layer, _) in members {
                    let Some(value) = graph.layer(layer).data().try_field(&property, field.as_str())? else {
                        continue;
                    };
                    let list_op = match value.into_owned() {
                        Value::PathListOp(op) => op,
                        Value::PathVec(paths) => sdf::PathListOp::explicit(paths),
                        _ => continue,
                    };
                    for path in list_op.iter() {
                        let target = property.make_absolute(path);
                        // A target inside the class itself is a normal within-class
                        // target (C++ `connectionPathInsideInheritedClass`); only a
                        // target that translates can name an instance.
                        if target.prim_path().has_prefix(&class_path) {
                            continue;
                        }
                        if !seen.insert((target.clone(), property.clone())) {
                            continue;
                        }
                        let Some(translated) = map.translate_to_target(&target) else {
                            continue;
                        };
                        candidates.push(InstanceCandidate {
                            target,
                            property: property.clone(),
                            translated,
                            class_layers: class_layers.clone(),
                            class_path: class_path.clone(),
                        });
                    }
                }
            }
        }

        // Phase 2: compose each target prim for the cross-prim inherit check.
        let mut instance_targets: HashSet<(Path, Path)> = HashSet::new();
        for c in candidates {
            let target_prim = c.translated.prim_path();
            self.ensure_index(graph, &target_prim)?;
            if target_prim_inherits_class(self.cached(&target_prim), graph, &c.class_layers, &c.class_path) {
                instance_targets.insert((c.target, c.property));
            }
        }
        Ok(instance_targets)
    }

    /// Composes a relationship's target paths together with the paths its
    /// list-op deletes, returned as `(targets, deleted)` (C++
    /// `PcpBuildFilteredTargetIndex` and its `deletedPaths` out-param). Both are
    /// mapped into stage namespace; a non-property path yields two empty lists.
    pub fn compute_relationship_target_paths(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
    ) -> Result<(Vec<Path>, Vec<Path>)> {
        self.compute_target_paths(graph, path, FieldKey::TargetPaths)
    }

    /// Composes an attribute's connection paths together with the paths its
    /// list-op deletes (the connection analog of
    /// [`Self::compute_relationship_target_paths`]).
    pub fn compute_attribute_connection_paths(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
    ) -> Result<(Vec<Path>, Vec<Path>)> {
        self.compute_target_paths(graph, path, FieldKey::ConnectionPaths)
    }

    /// Composes both the resolved and the deleted entries of a path-list-op
    /// property field. TODO(perf): C++ surfaces both from a single target-index
    /// build; this composes the field twice.
    fn compute_target_paths(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        field: FieldKey,
    ) -> Result<(Vec<Path>, Vec<Path>)> {
        let targets = self.compose_property_paths(graph, path, field, false)?;
        let deleted = self.compose_property_paths(graph, path, field, true)?;
        Ok((targets, deleted))
    }

    /// Returns pseudo-root stage metadata, composing session-layer opinions
    /// over the root layer (strongest first).
    ///
    /// Unlike [`Self::root_layer_field`] — which is root-layer-only for the
    /// spec 12.2.7 fields such as `defaultPrim` — general stage metadata
    /// (e.g. `renderSettingsPrimPath`) honors a session-layer override,
    /// matching C++ `UsdStage::GetMetadata`. A [`Value::ValueBlock`] in a
    /// stronger layer blocks weaker opinions.
    pub fn stage_metadata(&self, graph: &LayerGraph, field: &str) -> Result<Option<Value>> {
        let root = Path::abs_root();
        // Walk session layers then the root layer so the session opinion wins,
        // skipping muted session layers (the root is never muted).
        let layer_ids = graph
            .session_layers()
            .iter()
            .copied()
            .chain(graph.root_id())
            .filter(|&id| !graph.is_muted(id))
            .collect::<Vec<_>>();
        for id in layer_ids {
            let layer = graph.layer(id);
            match layer.data().try_field(&root, field)? {
                Some(value) if matches!(value.as_ref(), Value::ValueBlock) => return Ok(None),
                Some(value) => return Ok(Some(value.into_owned())),
                None => {}
            }
        }
        Ok(None)
    }

    /// Returns pseudo-root layer metadata from the root layer only.
    ///
    /// Session-layer and sublayer opinions are intentionally ignored here,
    /// matching spec 12.2.7.
    fn root_layer_field(&self, graph: &LayerGraph, field: &str) -> Result<Option<Value>> {
        let root = Path::abs_root();
        let Some(root_layer) = graph.root_layer() else {
            return Ok(None);
        };
        let Some(value) = root_layer.data().try_field(&root, field)? else {
            return Ok(None);
        };
        if matches!(value.as_ref(), Value::ValueBlock) {
            return Ok(None);
        }
        Ok(Some(value.into_owned()))
    }

    /// Returns the composed list of child names for a prim path (C++
    /// `PcpPrimIndex::ComputePrimChildNames`'s `nameOrder` out-param).
    pub fn prim_children(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<Token>> {
        Ok(self.compute_prim_child_names(graph, path)?.0)
    }

    /// Composes a prim's child names alongside the names prohibited at it (C++
    /// `PcpPrimIndex::ComputePrimChildNames` / `_ComposePrimChildNames`, whose
    /// `nameOrder` and `prohibitedNames` out-params this returns as a pair).
    ///
    /// The composition graph is walked weakest-to-strongest. At each contributing
    /// node, the relocates authored in that node's layer stack are applied to the
    /// names contributed so far (`relocates::apply_child_relocates`) — a child renamed
    /// within the same parent keeps the source's position, a child relocated to a
    /// different parent is removed, and a child relocated in from elsewhere is
    /// appended in the normative element order (spec §8.2) — and then the node's own `primChildren` /
    /// `primOrder` compose over the running order (mirroring C++
    /// `_ComposePrimChildNamesAtNode`). Every relocation source becomes a
    /// prohibited name, removed from the final order.
    ///
    /// Within a node, the contributing layers fold weakest-first: each appends
    /// its not-yet-seen names in authored order, then its `primOrder` opinion
    /// reshuffles the running list, so several sublayers can contribute partial
    /// orderings. The recursive build already grafts inherit/specialize/reference
    /// targets with their subtrees, so a single structural walk covers class
    /// children. On an instance prim, locally-authored children are dropped (spec
    /// 11.3.3) so the children come only from the composition arcs.
    pub fn compute_prim_child_names(&mut self, graph: &LayerGraph, path: &Path) -> Result<(Vec<Token>, Vec<Token>)> {
        let path = self.effective_path(graph, path)?;
        self.ensure_index(graph, &path)?;

        // An instance prim's children come only from its composition arcs;
        // opinions authored at the instance's own namespace — the local root and
        // the ancestral references above the instanceable arc — are discarded
        // (spec 11.3.3). The instance prim's own index is otherwise left intact.
        let drop_local = self.is_instance(graph, &path)?;

        let index = self.cached(&path);
        // The instance-local partition is keyed by the prim's own namespace depth
        // ([`PrimIndex::instance_local_nodes`]); empty when not dropping locals.
        let local = if drop_local {
            index.instance_local_nodes(path.prim_element_count() as u16)
        } else {
            Vec::new()
        };

        let has_relocates = graph.has_relocates();
        let mut name_order: Vec<Token> = Vec::new();
        let mut name_set: HashSet<Token> = HashSet::new();
        let mut prohibited: HashSet<Token> = HashSet::new();

        // Contributing nodes are walked in reverse strength order (weak-to-
        // strong) — the order in which C++ `_ComposePrimChildNames` finishes each
        // node, visiting every descendant before its ancestor. A non-contributing
        // node (inert or culled) is skipped (C++ `_ComposePrimChildNamesAtNode`'s
        // `CanContributeSpecs` guard): an inert relocate placeholder or salted-
        // earth source must not inject names or relocates at its site.
        let nodes = index
            .nodes_with_ids()
            .filter(|(id, node)| !(node.is_inert() || node.is_culled() || drop_local && local[id.idx()]))
            .map(|(_, node)| node)
            .rev();

        for node in nodes {
            // Apply this node's layer-stack relocates to the names contributed so
            // far, then compose the node's own children on top. A relocation
            // source is always a namespace child introduced by a composition arc
            // (a strictly weaker node), so by the time this node's relocates run
            // the source name is already in `name_order`; the relocates therefore
            // correctly run before this node's own `primChildren` fold.
            //
            // The pairs are chained within the node's layer stack
            // (`combined_relocates`, C++ `GetRelocatesSourceToTarget`): a same-
            // parent chain `A -> B`, `B -> C` resolves `A` straight to `C`, so the
            // intermediate `B` (a prohibited source) does not survive as the final
            // name. TODO(perf): `combined_relocates` rescans and re-allocates the
            // node's layer-stack relocates on every contributing node (here and in
            // the indexer's arc-map fold), gated on `has_relocates`. Precompute it
            // once per distinct ambient (keyed by the layer-id sequence) in
            // `LayerGraph::recompute_relocates`, alongside `sublayer_stacks`, so
            // this becomes a lookup (C++ caches these on `PcpLayerStack`).
            if has_relocates {
                let pairs = graph.combined_relocates(node.layer_stack_id());
                apply_child_relocates(&node.path, &pairs, &mut name_order, &mut name_set, &mut prohibited);
            }
            // The node's contributing layers fold weakest-first; `layer_stack()`
            // is strongest-first, so it is reversed here. Only the layer index is
            // needed (the offset `layers()` folds in is irrelevant to name
            // composition), so the borrowed slice is reversed in place.
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter().rev() {
                let layer_data = graph.layer(layer);
                append_unseen_names(
                    layer_data,
                    &node.path,
                    ChildrenKey::PrimChildren,
                    &mut name_order,
                    &mut name_set,
                );
                if let Ok(Value::TokenVec(order)) = layer_data
                    .data()
                    .get_field(&node.path, FieldKey::PrimOrder.as_str())
                    .map(|v| v.into_owned())
                {
                    sdf::apply_ordering(&mut name_order, &order);
                }
            }
        }

        // Names relocated away cannot reappear here (C++ removes the prohibited
        // set from the composed order after the walk).
        if !prohibited.is_empty() {
            name_order.retain(|name| !prohibited.contains(name));
        }
        let mut prohibited: Vec<Token> = prohibited.into_iter().collect();
        // Order the prohibited set the same way as the child names (spec §8.2),
        // so the two outputs of this function stay consistent.
        prohibited.sort_by(|a, b| sdf::element_cmp(a.as_str(), b.as_str()));
        Ok((name_order, prohibited))
    }

    /// Returns the composed list of property names for a prim path.
    ///
    /// Merges `propertyChildren` weakest-to-strongest. `propertyOrder` is not
    /// applied: USD value resolution ignores `reorder properties` (C++
    /// `_ComposePrimPropertyNames` passes a null order field in USD mode), so
    /// composed property order follows authoring order alone.
    pub fn prim_properties(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<Token>> {
        let path = &self.effective_path(graph, path)?;
        self.composed_property_names(graph, path)
    }

    /// Pushes a [`Error::InconsistentPropertyType`] for each composed property of
    /// `prim_path` whose specs mix attribute and relationship kinds (C++
    /// `PcpErrorInconsistentPropertyType`). C++ reports the conflict on each
    /// property-index composition; the dump's property-name pass (here) and
    /// property-stack pass ([`property_stack`](Self::property_stack)) each compose
    /// it, so the error surfaces once per pass.
    fn report_property_type_conflicts(&mut self, graph: &LayerGraph, prim_path: &Path, names: &[Token]) {
        let Some(index) = self.index_at(prim_path) else {
            return;
        };
        let mut conflicts = Vec::new();
        for name in names {
            let Ok(prop_path) = prim_path.append_property(name) else {
                continue;
            };
            conflicts.extend(self.compose_property_specs(graph, index, prim_path, &prop_path).1);
        }
        self.query_errors.append(&mut conflicts);
    }

    /// Walks a property's specs strongest-first across the prim's composition
    /// graph, returning its `(layer identifier, spec path)` stack and the
    /// inconsistent-spec-type errors. The first spec's kind (attribute vs
    /// relationship) is the defining type; weaker specs of the other kind are
    /// inconsistent (C++ `PcpErrorInconsistentPropertyType`) — dropped from the
    /// stack and reported. `prop_path` is the property in `prim_path`'s namespace.
    fn compose_property_specs(
        &self,
        graph: &LayerGraph,
        index: &PrimIndex,
        prim_path: &Path,
        prop_path: &Path,
    ) -> (Vec<(String, Path)>, Vec<Error>) {
        let mut stack = Vec::new();
        let mut conflicts = Vec::new();
        let mut defining: Option<(SpecType, String, Path)> = None;
        for node in index.nodes() {
            let Some(p) = prop_path.replace_prefix(prim_path, &node.path) else {
                continue;
            };
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                let Some(spec_type) = graph.layer(layer).data().spec_type(&p) else {
                    continue;
                };
                match &defining {
                    None => defining = Some((spec_type, graph.identifier(layer).to_string(), p.clone())),
                    Some((def_type, def_layer, def_path)) if *def_type != spec_type => {
                        conflicts.push(Error::InconsistentPropertyType {
                            property: prop_path.clone(),
                            defining_layer: def_layer.clone(),
                            defining_path: def_path.clone(),
                            defining_is_attribute: *def_type == SpecType::Attribute,
                            conflicting_layer: graph.identifier(layer).to_string(),
                            conflicting_path: p.clone(),
                            conflicting_is_attribute: spec_type == SpecType::Attribute,
                            composing: prim_path.clone(),
                        });
                        continue;
                    }
                    Some(_) => {}
                }
                stack.push((graph.identifier(layer).to_string(), p.clone()));
            }
        }
        (stack, conflicts)
    }

    /// Returns the composed [`PrimIndex`] for a prim, building it if needed (C++
    /// `UsdPrim::GetPrimIndex` / `PcpCache::ComputePrimIndex`). The borrow is
    /// tied to the cache, so callers reach it through the borrowing
    /// [`PrimIndexRef`](crate::usd::PrimIndexRef) view.
    pub fn index(&mut self, graph: &LayerGraph, path: &Path) -> Result<&PrimIndex> {
        let path = self.effective_path(graph, &path.prim_path())?;
        self.ensure_index(graph, &path)?;
        Ok(self.cached(&path))
    }

    /// Returns the prim stack: each `(layer identifier, spec path)` site that
    /// contributes a prim spec, strongest first. Backs C++
    /// `UsdPrim::GetPrimStack` (each per-site node fans out into one entry per
    /// contributing layer in its layer stack, since every member authored a
    /// prim spec).
    pub fn prim_stack(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<(String, Path)>> {
        let path = self.effective_path(graph, &path.prim_path())?;
        self.ensure_index(graph, &path)?;
        let index = self.cached(&path);
        let mut stack = Vec::new();
        for node in index.nodes() {
            // A node may carry its full site layer stack; only the layers that
            // author a spec at its path belong in the prim stack.
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                if graph.layer(layer).data().has_spec(&node.path) {
                    stack.push((graph.identifier(layer).to_string(), node.path.clone()));
                }
            }
        }
        Ok(stack)
    }

    /// Returns the property stack for a property path: each `(layer identifier,
    /// spec path)` site that authors a property spec, strongest first. Backs
    /// C++ `UsdProperty::GetPropertyStack`. A non-property path yields an empty
    /// stack.
    pub fn property_stack(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<(String, Path)>> {
        let path = self.effective_path(graph, path)?;
        if !path.is_property_path() {
            return Ok(Vec::new());
        }
        let prim_path = path.prim_path();
        self.ensure_index(graph, &prim_path)?;
        let Some(index) = self.index_at(&prim_path) else {
            return Ok(Vec::new());
        };
        let (stack, mut conflicts) = self.compose_property_specs(graph, index, &prim_path, &path);
        // These transient conflicts are cleared on any index invalidation, so
        // they never go stale across an edit; repeated `property_stack` queries
        // on the same conflicting property without an intervening edit still
        // re-append within a session (the `query_errors` TODO).
        self.query_errors.append(&mut conflicts);
        Ok(stack)
    }

    /// Returns the variant selections composed onto a prim, as `(set,
    /// selection)` pairs sorted by set name. Backs C++
    /// `UsdVariantSets::GetAllVariantSelections`. These are the effective
    /// selections — authored, fallback, or default — read from the variant
    /// selection sites composed into the index, so they match the variant
    /// branches that actually contribute opinions.
    pub fn variant_selections(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<(String, String)>> {
        let path = self.effective_path(graph, &path.prim_path())?;
        self.ensure_index(graph, &path)?;
        Ok(self.cached(&path).variant_selections())
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    ///
    /// When session layers are present, `defaultPrim` is read from the
    /// first non-session layer (the root layer), matching C++ behavior.
    pub fn default_prim(&self, graph: &LayerGraph) -> Option<Token> {
        let root = Path::abs_root();
        let value = graph
            .root_layer()?
            .data()
            .get_field(&root, FieldKey::DefaultPrim.as_str())
            .ok()?;
        value.into_owned().try_as_token()
    }

    /// Collects ancestor arcs from all cached ancestors of `path`.
    ///
    /// Returns references into the cached contexts, avoiding allocation
    /// of `AncestorArc` (which contains `MapFunction` with a `Vec`).
    fn collect_ancestor_arcs(&self, path: &Path) -> Vec<&AncestorArc> {
        let mut arcs = Vec::new();
        let mut p = Some(path.clone());
        while let Some(pp) = p {
            if let Some(ctx) = self.entries.get(&pp).map(|entry| &entry.context) {
                arcs.extend(&ctx.ancestor_arcs);
            }
            p = pp.parent();
        }
        arcs
    }

    /// Pre-caches inherit/specialize targets declared in the prim's layer
    /// data. Reads inherit paths from each layer, resolves them to composed
    /// namespace using ancestor arcs, and ensures those targets are cached.
    fn precache_inherit_targets(&mut self, graph: &LayerGraph, path: &Path) {
        let Some(parent) = path.parent() else {
            return;
        };
        let Some(parent_index) = self.index_at(&parent) else {
            return;
        };

        let ancestor_arcs = self.collect_ancestor_arcs(&parent);

        // Scan each parent composition node for inherit/specialize targets: the
        // parent's own path in that node's namespace, and the prim's path there
        // (the node's path extended by the prim name). A layer that authors the
        // prim directly contributes to the parent at the parent path, so it is
        // already covered here — no separate all-layers scan of the prim path is
        // needed.
        let mut nodes_to_scan: Vec<(Path, LayerId)> = Vec::new();
        for node in parent_index.nodes() {
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                nodes_to_scan.push((node.path.clone(), layer));
                if let Some(name) = path.name() {
                    if let Ok(child_in_node) = node.path.append_path(name) {
                        nodes_to_scan.push((child_in_node, layer));
                    }
                }
            }
        }

        let mut targets_to_cache = Vec::new();
        for (scan_path, scan_layer) in &nodes_to_scan {
            for field in [FieldKey::InheritPaths, FieldKey::Specializes] {
                let Ok(val) = graph.layer(*scan_layer).data().get_field(scan_path, field.as_str()) else {
                    continue;
                };
                let Value::PathListOp(list_op) = val.into_owned() else {
                    continue;
                };
                for target in &list_op.flatten() {
                    // Anchor a relative inherit/specialize target at the path it
                    // is authored on (the scanned node's namespace), matching the
                    // indexer's `path.make_absolute`. Anchoring at the
                    // composed parent would mis-resolve `../` targets by a level.
                    let raw = scan_path.make_absolute(target);
                    // Try composed-namespace versions via ancestor arcs.
                    for a in &ancestor_arcs {
                        if let Some(composed) = a.map.map_source_to_target(&raw) {
                            if composed != raw && !targets_to_cache.contains(&composed) {
                                targets_to_cache.push(composed);
                            }
                        }
                    }
                    if !targets_to_cache.contains(&raw) {
                        targets_to_cache.push(raw);
                    }
                }
            }
        }

        for target in targets_to_cache {
            self.precache_path(graph, &target);
            // Recursively precache the target's own inherit targets.
            if self.entries.contains_key(&target) {
                self.precache_inherit_targets(graph, &target);
            }
        }
    }

    /// Returns the `(node, error)` pair for each direct composition arc on
    /// `path` whose target site is `permission = private` (spec 10.3.3).
    ///
    /// A direct arc is a reference/inherit/payload/specialize authored at this
    /// prim — its node sits at the prim's own namespace depth and is not an
    /// implied class. Mirroring C++ `_AddArc` + `_InertSubtree`, the caller
    /// surfaces the error and marks the node's subtree
    /// [`PERMISSION_DENIED`](NodeFlags::PERMISSION_DENIED), so the arc stops
    /// contributing to value resolution while staying visible structurally
    /// (`nodes`, `has_spec`, child names are unchanged).
    fn detect_arc_permissions(&self, graph: &LayerGraph, path: &Path, index: &PrimIndex) -> Vec<(NodeId, Error)> {
        let depth = path.prim_element_count() as u16;
        let mut denials = Vec::new();
        for (id, node) in index.nodes_with_ids() {
            let is_direct_arc = matches!(
                node.arc,
                ArcType::Inherit | ArcType::Specialize | ArcType::Reference | ArcType::Payload
            ) && node.namespace_depth() == depth
                && !node.flags().contains(NodeFlags::IMPLIED_CLASS);
            if is_direct_arc && self.target_is_private(graph, node) {
                denials.push((
                    id,
                    Error::ArcPermissionDenied {
                        site_path: path.clone(),
                        arc: node.arc,
                        target_path: node.path.clone(),
                    },
                ));
            }
        }
        denials
    }

    /// Returns `true` when the strongest `permission` opinion at a direct arc's
    /// target site (read across the node's contributing layers) is `private`.
    fn target_is_private(&self, graph: &LayerGraph, node: &Node) -> bool {
        for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
            if let Ok(Some(value)) = graph
                .layer(layer)
                .data()
                .try_field(&node.path, FieldKey::Permission.as_str())
            {
                return matches!(value.as_ref(), Value::Permission(sdf::Permission::Private));
            }
        }
        false
    }

    // ------------------------------------------------------------------
    // Core composition
    // ------------------------------------------------------------------

    /// Ensures the prim index for `path` is built and cached.
    ///
    /// When LIVRPS composition produces an empty index (no layer has a direct
    /// spec at the composed path), parent composition nodes are checked for
    /// child specs at their respective paths. This handles prims that only
    /// exist through ancestor inherit, specialize, or reference arcs.
    pub(super) fn ensure_index(&mut self, graph: &LayerGraph, path: &Path) -> Result<()> {
        if self.entries.contains_key(path) {
            return Ok(());
        }
        // Composing a prim whose ancestor is still mid-build cannot seed from that
        // ancestor's opinions. This happens only when pre-caching an
        // inherit/specialize target that is a namespace descendant of an
        // in-progress ancestor (a prim inheriting its own descendant). The
        // descendant may be more than one level down (`/A` inheriting `/A/B/C`),
        // so every strict ancestor is checked, not just the parent. Defer without
        // caching an under-seeded result; a later query composes it correctly once
        // the ancestor is cached, and the cycle-closing arc finds no cached target.
        if path.strict_ancestors().any(|a| self.in_progress.contains(&a)) {
            return Ok(());
        }
        // A re-entrant call for a path already mid-build is a class-hierarchy
        // cycle reached through inherit/specialize pre-caching. Bail out: the
        // outer build finishes, and the cycle-closing arc finds no cached target.
        if !self.in_progress.insert(path.clone()) {
            return Ok(());
        }
        let result = self.build_index(graph, path);
        self.in_progress.remove(path);
        result
    }

    /// Builds and caches the index for `path`, assuming `path` is already
    /// recorded in [`in_progress`](Self::in_progress) (see [`ensure_index`](Self::ensure_index)).
    fn build_index(&mut self, graph: &LayerGraph, path: &Path) -> Result<()> {
        // Snapshot the demand queue so a reference/payload arc to a not-yet-loaded
        // layer — demanded by this build or by a pre-cached ancestor below — is
        // detected after the build and keeps the incomplete index out of the cache.
        let pending_before = self.pending_loads.len();
        // Compose ancestors first so the parent's `CompositionContext` (and
        // its `within_instance` flag, spec 11.3.3) is available. Composition
        // is a pure function of the layer stack, path, and parent context, so
        // building ancestors eagerly only fixes the parent context — it does
        // not change any prim's resolved opinions.
        if let Some(parent) = path.parent() {
            if !parent.is_abs_root() && !self.entries.contains_key(&parent) {
                self.precache_path(graph, &parent);
            }
        }

        // Pre-cache inherit/specialize targets so the indexer can
        // find them. This handles the timing issue where a target prim is
        // in a sibling subtree that hasn't been traversed yet.
        self.precache_inherit_targets(graph, path);

        let parent_ctx = path
            .parent()
            .and_then(|p| self.entries.get(&p))
            .map(|entry| entry.context.clone())
            .unwrap_or_else(|| self.root_parent_context());

        // TODO(rayon): `build_with_cache` is a pure function of `graph`,
        // `&parent_ctx`, and `&self.entries`, so sibling prims compose
        // independently and this is the natural per-prim `par_iter` boundary.
        // The blocker is the shared `self.entries` map that inherit/specialize
        // targets read mid-build — parallelizing the driver needs a concurrent
        // map or a topological (targets-first) build order.
        let (mut index, mut build_errors, pending_loads) =
            match PrimIndex::build_with_cache(path, graph, &parent_ctx, &self.entries) {
                Ok(result) => result,
                Err(e) => return Err(e.into()),
            };
        self.pending_loads.extend(pending_loads);
        // A reference/payload arc demanded a layer that is not yet loaded — here,
        // or in a pre-cached ancestor that then seeded this build incompletely —
        // so this index is incomplete: leave `path` uncached for the stage's query
        // loop to load and recompose. Returning before `cache_index` keeps a
        // partial index — and the transient errors composed without the missing
        // layer — out of the cache entirely.
        if self.pending_loads.len() > pending_before {
            return Ok(());
        }
        // Retain recoverable composition errors recorded during the build (e.g.
        // an unresolvable arc). An invalid opinion at a
        // relocation source is reported "while composing" this prim, so stamp its
        // path — the indexer may have recorded it deep in a sub-index build whose
        // own site path differs.
        for error in &mut build_errors {
            match error {
                Error::OpinionAtRelocationSource { composing, .. } => *composing = path.clone(),
                Error::ProhibitedRelocationSource { composing, .. } => *composing = path.clone(),
                Error::ArcCycle(info) => info.composing = path.clone(),
                _ => {}
            }
        }
        // `build_errors` accumulates every error for this prim (the build errors
        // above plus the permission denials below) and is carried into the prim's
        // cache entry at the end, replacing any prior entry, so a rebuild never
        // duplicates and a fixed prim drops its stale errors.

        // Inside an instance, local opinions on descendants are discarded
        // (spec 11.3.3): the subtree is composed purely from the arcs the
        // instance brings in. This is enforced at composition time — the indexer
        // marks the local root site inert for any prim whose parent context is
        // `within_instance`, so the local arcs are never followed — rather than
        // pruned afterwards, which would leave the nodes those local arcs spawned.

        // Arc permissions (spec 10.3.3, C++ `_AddArc` + `_InertSubtree`). A
        // direct arc to a `permission = private` site is reported and its target
        // path recorded; an ancestor's denied targets arrive on `parent_ctx`.
        // Every node reached through a denied arc — its grafted subtree here, or
        // the same arc extended to this descendant prim — is then inerted: it
        // stays visible structurally but contributes no opinions to value
        // resolution. This runs before deriving instance state below so a
        // private target's `instanceable`/arc opinions are already inert.
        let mut denied_prefixes = parent_ctx.denied_prefixes.clone();
        for (node_id, error) in self.detect_arc_permissions(graph, path, &index) {
            let target = index.node(node_id).path.clone();
            if !denied_prefixes.contains(&target) {
                denied_prefixes.push(target);
            }
            build_errors.push(error);
        }
        index.mark_permission_denied_under(&denied_prefixes);

        // Inside an instance, the ancestral references the instance prim is
        // nested under contribute opinions at the instance's own namespace that
        // must not leak into the shared subtree (spec 11.3.3). The indexer
        // already inerted the local root for an instance descendant; this inerts
        // those outer references too (the C++ `!HasTransitiveDirectDependency`
        // nodes), leaving only the instanceable arc, its descendants, and the
        // implied classes. Runs before deriving instance state below so the
        // suppressed opinions are already inert.
        if let Some(depth) = parent_ctx.instance_depth {
            index.mark_instance_local_inert(depth);
        }

        // This prim is an instance when its composition declares
        // `instanceable = true` and carries an arc; its descendants then
        // inherit `within_instance`. A nested instance therefore re-arms the
        // flag for its own subtree. Computed from the freshly built index (after
        // permission inerting, so it agrees with a later `Prim::is_instance`)
        // to avoid re-entering `ensure_index` for `path`.
        let is_instance = index.has_composition_arc()
            && matches!(
                index.resolve_field(FieldKey::Instanceable.as_str(), graph, None)?,
                Some(Value::Bool(true))
            );

        let mut child_context = index.context_for_children(graph, &parent_ctx);
        // A nested instance re-arms the depth to its own (deeper) level, so an
        // inner instance's descendants drop opinions above its instanceable arc
        // rather than the outer instance's.
        child_context.instance_depth = if is_instance {
            Some(path.prim_element_count() as u16)
        } else {
            parent_ctx.instance_depth
        };
        child_context.denied_prefixes = denied_prefixes;
        self.cache_index(graph, path, index, child_context, build_errors);
        // Report inconsistent property types once per prim composition (C++
        // `PcpErrorInconsistentPropertyType`); a later property-stack query
        // reports the conflict again, matching C++'s per-pass reporting.
        // TODO(perf): this composes property names on every prim build to find a
        // rare conflict; gate it on a cheaper signal (e.g. a node carrying both
        // attribute and relationship specs) before scanning.
        let names = self.composed_property_names(graph, path)?;
        self.report_property_type_conflicts(graph, path, &names);
        Ok(())
    }

    /// Ensures a path and all its ancestors are cached (built on the fly if needed).
    fn precache_path(&mut self, graph: &LayerGraph, path: &Path) {
        let mut to_build = Vec::new();
        let mut p = Some(path.clone());
        while let Some(pp) = p {
            if pp == Path::abs_root() || self.entries.contains_key(&pp) {
                break;
            }
            to_build.push(pp.clone());
            p = pp.parent();
        }
        for pp in to_build.into_iter().rev() {
            let _ = self.ensure_index(graph, &pp);
        }
    }

    /// Composes a prim's property names across its composition index, folding
    /// `propertyChildren` weakest-to-strongest (C++ `_ComposePrimPropertyNames`).
    ///
    /// Nodes are visited weakest first (the reverse of strength order), and
    /// within each node its contributing layers weakest first; each layer appends
    /// its not-yet-seen names in authored order, so a name keeps its weakest
    /// position. `propertyOrder` is not applied — USD value resolution ignores
    /// `reorder properties` — so composed property order follows authoring order
    /// alone. The recursive build already grafts inherit/specialize/reference
    /// targets with their subtrees, so this single structural walk covers class
    /// properties with no separate target rediscovery.
    fn composed_property_names(&mut self, graph: &LayerGraph, path: &Path) -> Result<Vec<Token>> {
        self.ensure_index(graph, path)?;

        let index = self.cached(path);
        let mut result: Vec<Token> = Vec::new();
        let mut seen: HashSet<Token> = HashSet::new();

        // Fold weakest-to-strongest across both nodes and, within each node, its
        // layers: contributing nodes in reverse strength order, and `layer_stack()`
        // (strongest first) reversed in place. `seen` dedups names in O(1) while
        // `result` preserves the weakest-position order.
        for node in index.nodes().rev() {
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter().rev() {
                let layer_data = graph.layer(layer);
                append_unseen_names(
                    layer_data,
                    &node.path,
                    ChildrenKey::PropertyChildren,
                    &mut result,
                    &mut seen,
                );
            }
        }

        Ok(result)
    }
}

/// Appends a layer's not-yet-seen `field` children (`primChildren` /
/// `propertyChildren`) to `order` in authored order, recording each in `seen`.
/// A name already present keeps its weaker position. Shared by the prim- and
/// property-name folds (C++ `PcpComposeSiteChildNames`'s append step).
fn append_unseen_names(
    layer: &sdf::Layer,
    path: &Path,
    field: ChildrenKey,
    order: &mut Vec<Token>,
    seen: &mut HashSet<Token>,
) {
    if let Ok(Value::TokenVec(names)) = layer.data().get_field(path, field.as_str()).map(|v| v.into_owned()) {
        for name in names {
            if seen.insert(name.clone()) {
                order.push(name);
            }
        }
    }
}

/// A class-node target that translates, gathered by
/// [`IndexCache::compute_instance_targets`] for the cross-prim instance check.
struct InstanceCandidate {
    /// The authored target, in the authoring (class) node's namespace.
    target: Path,
    /// The owning property, in the authoring node's namespace.
    property: Path,
    /// The target translated to the root namespace (C++
    /// `PcpTranslatePathFromNodeToRoot`).
    translated: Path,
    /// The class node's layer-stack layers, for the cross-prim instance check.
    class_layers: Vec<LayerId>,
    /// The class path, in the node's namespace (the inherit's introduction path).
    class_path: Path,
}

/// Whether `index` (a composed target prim) inherits the class at `class_path`
/// from the same `class_layers` layer stack (C++
/// `_TargetInClassAndTargetsInstance`'s node scan): the target names an instance
/// of the class.
fn target_prim_inherits_class(
    index: &PrimIndex,
    graph: &LayerGraph,
    class_layers: &[LayerId],
    class_path: &Path,
) -> bool {
    index.all_nodes().any(|n| {
        n.arc == ArcType::Inherit
            && graph
                .layer_stack(n.layer_stack_id())
                .iter()
                .map(|(l, _)| *l)
                .eq(class_layers.iter().copied())
            && n.path.has_prefix(class_path)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    /// Builds a stack with the root and the full transitive closure of its
    /// sublayers, references, and payloads collected in, so composition can
    /// resolve them directly without the stage's on-demand load loop (clip
    /// layers are still opened lazily by the cache).
    fn collected_stack(path: &str) -> (LayerGraph, IndexCache) {
        let registry = sdf::LayerRegistry::default();
        let layers = registry.collect_with_arcs(path).expect("collect layers");
        let graph = LayerGraph::from_layers(layers, 0, registry);
        (graph, IndexCache::new(VariantFallbackMap::new(), true, Vec::new()))
    }

    /// Parses in-memory USDA text into a single `root.usda` layer.
    fn parse_layer(text: &str) -> sdf::Layer {
        parse_named_layer("root.usda", text)
    }

    /// Parses in-memory USDA text into a layer with the given identifier, so a
    /// test can build a multi-layer stack whose `subLayers` resolve by name.
    fn parse_named_layer(identifier: &str, text: &str) -> sdf::Layer {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        sdf::Layer::new(identifier, Box::new(sdf::Data::from_specs(data)))
    }

    /// Builds a one-layer graph + cache from in-memory USDA text, for
    /// composition cases that need no on-disk asset.
    fn in_memory_stack(text: &str) -> (LayerGraph, IndexCache) {
        let graph = LayerGraph::from_layers(vec![parse_layer(text)], 0, sdf::LayerRegistry::default());
        (graph, IndexCache::new(VariantFallbackMap::new(), true, Vec::new()))
    }

    /// Run `f` as one atomic transaction on `layer` and return the recorded change
    /// list, the test-side spelling of an [`sdf::Layer`] edit. Captures the record
    /// the way any observer would — through an `after_commit` sink — since `edit`
    /// itself returns only whether anything changed.
    fn edit_layer(
        layer: &mut sdf::Layer,
        f: impl FnOnce(&mut sdf::LayerEdit<'_>) -> Result<(), sdf::AuthoringError>,
    ) -> Result<sdf::ChangeList, sdf::AuthoringError> {
        let captured = std::rc::Rc::new(std::cell::RefCell::new(sdf::ChangeList::new()));
        let slot = captured.clone();
        let id = layer.add_sink(move |_: &str, changes: &sdf::ChangeList| {
            slot.replace(changes.clone());
        });
        let result = layer.edit(f);
        layer.remove_sink(id);
        match result {
            Ok(_) => Ok(std::rc::Rc::try_unwrap(captured).expect("sink dropped").into_inner()),
            Err(sdf::EditError::Author(e)) => Err(e),
            Err(sdf::EditError::Rejected(_)) => panic!("no layer sink to veto in tests"),
        }
    }

    /// Builds a one-layer graph + cache whose root is loaded from a real path,
    /// so the resolver can anchor clip asset paths relative to it.
    fn single_layer_stack(path: &str) -> (LayerGraph, IndexCache) {
        let registry = sdf::LayerRegistry::default();
        let id = registry.create_identifier(path, None);
        let data = registry.open(path).expect("open root").expect("root resolves");
        let graph = LayerGraph::from_layers(vec![sdf::Layer::new(id, data)], 0, registry);
        (graph, IndexCache::new(VariantFallbackMap::new(), true, Vec::new()))
    }

    /// `clip_layer` loads a clip layer relative to the authoring layer, caches
    /// it (clip layers never enter the composition stack), and reports an
    /// unresolvable path as `None`.
    #[test]
    fn loads_and_caches_clip_layer() -> Result<()> {
        let root = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets/clip_basic/usda/root.usda",
            manifest_dir()
        );
        let (graph, mut cache) = single_layer_stack(&root);
        let root_id = graph.root_id().expect("root layer");

        {
            let clip = cache
                .clip_layer(&graph, "./clip.usda", root_id)?
                .expect("clip resolves");
            assert!(clip.identifier.contains("clip.usda"));
            assert!(clip.data().has_spec(&sdf::path("/Model.size")?));
        }

        // Second lookup is a cache hit; a bogus path resolves to None.
        assert!(cache.clip_layer(&graph, "./clip.usda", root_id)?.is_some());
        assert!(cache.clip_layer(&graph, "./does_not_exist.usda", root_id)?.is_none());
        Ok(())
    }

    /// A prim inheriting its own grand-descendant (`/A` inherits `/A/B/C`) is a
    /// cycle whose arc is dropped, but composing `/A` must not cache an
    /// under-seeded `/A/B/C`. The inherit-target precache builds `/A/B/C` while
    /// `/A` is in progress, and its parent `/A/B` is not the in-progress prim, so
    /// the deferral guard must check every ancestor, not just the parent. `/A/B`
    /// references `</Lib/Ref>`, so a correctly-seeded `/A/B/C` exposes the
    /// reference's `mark` property.
    #[test]
    fn grandchild_inherit_target_seeds_ancestors() -> Result<()> {
        let text = r#"#usda 1.0
def "Lib" {
    def "Ref" {
        def "C" { custom string mark = "from-ref" }
    }
}
def "A" (
    inherits = </A/B/C>
)
{
    def "B" (
        references = </Lib/Ref>
    )
    {
    }
}
"#;
        let (graph, mut cache) = in_memory_stack(text);
        // Compose /A first so its inherit-target precache runs before /A/B/C is
        // queried; the precache must not leave a stale, parentless /A/B/C cached.
        cache.ensure_index(&graph, &sdf::path("/A")?)?;
        assert!(
            cache
                .prim_properties(&graph, &sdf::path("/A/B/C")?)?
                .iter()
                .any(|t| t.as_str() == "mark"),
            "/A/B/C must inherit the reference's `mark` via /A/B even when reached through /A's precache"
        );
        Ok(())
    }

    /// A child reachable only through a chain of local-class inherits composes
    /// its own inherited grandchildren: `SymArmRig` inherits `_Class_ArmRig`
    /// (whose `ArmRegion` over inherits `Body/_class_Region`), so
    /// `SymArmRig/ArmRegion` must expose `Region`.
    #[test]
    fn inherited_child_chain_composes() -> Result<()> {
        let root = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             TrickyLocalClassHierarchyWithRelocates_root/usda/root.usd",
            manifest_dir()
        );
        let (graph, mut cache) = collected_stack(&root);
        let arm_region = sdf::path("/C_1/ArmsRig/SymArmRig/ArmRegion")?;
        assert!(
            cache
                .prim_children(&graph, &arm_region)?
                .iter()
                .any(|t| t.as_str() == "Region"),
            "deep local-class inherit chain must surface the inherited grandchild"
        );
        Ok(())
    }

    /// Child names fold weakest-to-strongest, reapplying each layer's
    /// `primOrder` as it merges. `sub.usda` (weaker) authors `a b c` reordered
    /// to `c b a`; `root.usda` (stronger) adds `d` and reorders `a d`. The fold
    /// yields `[c, b, a, d]` — a strongest-`primOrder`-wins union would instead
    /// give `[a, d, b, c]`.
    #[test]
    fn child_names_fold_weak_to_strong() -> Result<()> {
        let root = format!("{}/fixtures/child_order_fold/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);
        let children = cache.prim_children(&graph, &sdf::path("/P")?)?;
        assert_eq!(
            children.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
            ["c", "b", "a", "d"]
        );
        Ok(())
    }

    /// A direct inherit to a `permission = private` class is reported as a
    /// non-fatal `ArcPermissionDenied` (spec 10.3.3), while the private class
    /// stays in the prim stack — C++ keeps the node and only records the error.
    /// Ground truth: `ErrorPermissionDenied_root` (`/Model` inherits the
    /// private `/_PrivateClass`).
    #[test]
    fn inherit_private_class_reports_arc() -> Result<()> {
        let root = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             ErrorPermissionDenied_root/usda/root.usd",
            manifest_dir()
        );
        let (graph, mut cache) = collected_stack(&root);
        let model = sdf::path("/Model")?;
        let private = sdf::path("/_PrivateClass")?;
        cache.ensure_index(&graph, &model)?;

        // Structural visibility is unchanged: the private class still composes
        // into the prim stack (it is inerted for value resolution, not removed).
        assert!(
            cache.cached(&model).nodes().any(|n| n.path == private),
            "private inherited class must remain in the prim stack"
        );

        // The direct inherit-to-private arc is queued for the stage to surface.
        let pending = cache.take_composition_errors();
        assert!(
            pending.iter().any(|e| matches!(
                e,
                Error::ArcPermissionDenied { site_path, arc, target_path }
                    if *site_path == model && *arc == ArcType::Inherit && *target_path == private
            )),
            "expected ArcPermissionDenied for /Model -> /_PrivateClass, got {pending:?}"
        );
        Ok(())
    }

    /// A direct inherit to a private class is inerted (C++ `_InertSubtree`): the
    /// inherited opinion is dropped from value resolution, yet the class stays
    /// in the prim stack and `has_spec`. A public inherit is the control.
    #[test]
    fn private_inherit_inerts_opinions() -> Result<()> {
        let root = format!("{}/fixtures/permission_private_inherit/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);

        // Control: a public inherit contributes its opinion.
        assert_eq!(
            cache.resolve_field(&graph, &sdf::path("/ViaPublic.attr")?, FieldKey::Default.as_str())?,
            Some(Value::Double(1.0)),
            "public inherited opinion must contribute"
        );

        // The private inherit is inerted: no opinion reaches value resolution,
        // but the class node and the property stay structurally present.
        let via_private = sdf::path("/ViaPrivate")?;
        let private_class = sdf::path("/PrivateClass")?;
        assert_eq!(
            cache.resolve_field(&graph, &sdf::path("/ViaPrivate.attr")?, FieldKey::Default.as_str())?,
            None,
            "private inherited opinion must not contribute to value resolution"
        );
        assert!(
            cache.cached(&via_private).nodes().any(|n| n.path == private_class),
            "private class stays in the prim stack"
        );
        assert!(
            cache.has_spec(&graph, &sdf::path("/ViaPrivate.attr")?)?,
            "the inherited attr stays structurally present"
        );
        Ok(())
    }

    /// The denial propagates to descendant prims composed separately: a child
    /// inherited through the private arc (an extended, not direct, arc) is
    /// inerted too, while the public child's opinion still resolves and the
    /// child name stays visible.
    #[test]
    fn private_inherit_inerts_descendants() -> Result<()> {
        let root = format!("{}/fixtures/permission_private_inherit/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);

        // Control: the public inherited child contributes its opinion.
        assert_eq!(
            cache.resolve_field(
                &graph,
                &sdf::path("/ViaPublic/Child.cattr")?,
                FieldKey::Default.as_str()
            )?,
            Some(Value::Double(2.0)),
            "public inherited child opinion must contribute"
        );

        // The private inherited child is inerted, but stays visible: the child
        // name is exposed and the property has a spec.
        assert_eq!(
            cache.resolve_field(
                &graph,
                &sdf::path("/ViaPrivate/Child.cattr")?,
                FieldKey::Default.as_str()
            )?,
            None,
            "private inherited child opinion must not contribute"
        );
        assert!(
            cache
                .prim_children(&graph, &sdf::path("/ViaPrivate")?)?
                .iter()
                .any(|t| t.as_str() == "Child"),
            "the inherited child name stays visible"
        );
        Ok(())
    }

    /// A private arc that authors `instanceable = true` is inerted before
    /// instance state is derived, so the prim is not treated as an instance and
    /// its local child opinions survive (the descendant subtree is not composed
    /// as a discarded-local instance subtree).
    #[test]
    fn private_instanceable_arc_not_instance() -> Result<()> {
        let root = format!("{}/fixtures/permission_private_inherit/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);

        let host = sdf::path("/InstHost")?;
        assert!(
            !cache.is_instance(&graph, &host)?,
            "a private (inerted) instanceable arc must not make the prim an instance"
        );
        assert_eq!(
            cache.resolve_field(&graph, &sdf::path("/InstHost/Local.lattr")?, FieldKey::Default.as_str())?,
            Some(Value::Double(7.0)),
            "the local child opinion must survive (within_instance not armed)"
        );
        Ok(())
    }

    /// A relocated prim's index carries relocate nodes (tagged
    /// `RELOCATE_SOURCE`) whose grafted source subtree forms a consistent
    /// tree: every stored parent link is mirrored by the parent's child list.
    #[test]
    fn relocate_nodes_form_subtree() -> Result<()> {
        use super::super::prim_graph::NodeFlags;

        let root = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             BasicRelocateToAnimInterface_root/usda/root.usd",
            manifest_dir()
        );
        let (graph, mut cache) = collected_stack(&root);
        let path = sdf::path("/Model/Anim/Path")?;
        cache.ensure_index(&graph, &path)?;
        let index = cache.cached(&path);

        // The relocate source node is composed inert (salted earth, C++
        // `rootNodeShouldContributeSpecs == false`): its own site contributes
        // nothing — its ancestral children carry the relocated opinions — so it
        // is retained in the arena but skipped by `nodes`/`all_nodes`.
        assert!(
            index
                .arena()
                .iter()
                .any(|n| n.flags().contains(NodeFlags::RELOCATE_SOURCE)),
            "relocated prim has a relocate source node"
        );
        for (id, node) in index.nodes_with_ids() {
            if let Some(parent) = node.parent() {
                assert!(
                    index.children(parent).contains(&id),
                    "relocate node {id:?} parent {parent:?} missing it as a child"
                );
            }
        }
        Ok(())
    }

    /// A relocate source spanning several sublayers keeps every member in the
    /// per-site relocate node — the weaker sublayer opinion must not be lost.
    /// `/World/Src` (authored in both `root.usda` and `sub.usda`) relocates to
    /// `/World/Dst`, whose relocate node must carry both layers.
    #[test]
    fn relocate_source_spans_sublayers() -> Result<()> {
        use super::super::prim_graph::NodeFlags;

        let root = format!("{}/fixtures/relocate_multilayer/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);
        let path = sdf::path("/World/Dst")?;
        cache.ensure_index(&graph, &path)?;
        let index = cache.cached(&path);

        // The relocate source node is composed inert (salted earth), so it is
        // retained in the arena but skipped by `nodes`/`all_nodes`.
        let relocate = index
            .arena()
            .iter()
            .find(|n| n.flags().contains(NodeFlags::RELOCATE_SOURCE))
            .expect("relocated prim has a relocate source node");
        let layers: Vec<LayerId> = graph
            .layer_stack(relocate.layer_stack_id())
            .iter()
            .map(|&(li, _)| li)
            .collect();
        let expected: Vec<LayerId> = graph.root_layer_stack().iter().map(|&(id, _)| id).collect();
        assert_eq!(
            layers, expected,
            "relocate node folds both authoring sublayers, strongest first"
        );
        Ok(())
    }

    /// A cross-hierarchy relocation source is registered as a dependency of the
    /// relocated prim even though its node is inert. `/Source/Inner` relocates to
    /// `/Dest/Moved`; the source's ancestors (`/Source`) are not ancestors of the
    /// target, so only the source-site registration lets an edit at `/Source/Inner`
    /// invalidate `/Dest/Moved`.
    #[test]
    fn relocate_source_registers_dependency() -> Result<()> {
        let root = format!("{}/fixtures/relocate_cross_hierarchy/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);
        let dst = sdf::path("/Dest/Moved")?;
        cache.ensure_index(&graph, &dst)?;

        let src = sdf::path("/Source/Inner")?;
        assert!(
            cache
                .dependencies()
                .lookup_with_ancestors(graph.root_id().unwrap(), &src)
                .contains(&dst),
            "an edit at relocation source /Source/Inner must invalidate /Dest/Moved"
        );
        Ok(())
    }

    /// A recoverable composition error on an ancestor must not erase a
    /// descendant's own opinions. `/A` references a missing layer — an error the
    /// cache records and continues past — yet `/A/B`'s local opinion still
    /// composes, rather than the child caching an empty index.
    #[test]
    fn ancestor_error_keeps_child_opinions() -> Result<()> {
        let text = r#"#usda 1.0
def "A" (
    references = @nonexistent.usd@
)
{
    def "B"
    {
        custom string marker = "ok"
    }
}
"#;
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        let layer = sdf::Layer::new("root.usda", Box::new(sdf::Data::from_specs(data)));
        let graph = LayerGraph::from_layers(vec![layer], 0, sdf::LayerRegistry::default());
        let mut cache = IndexCache::new(VariantFallbackMap::new(), true, Vec::new());

        let child = sdf::path("/A/B")?;
        cache.ensure_index(&graph, &child)?;
        assert!(
            !cache.cached(&child).is_empty(),
            "child local opinion must survive the ancestor's unresolved reference"
        );
        assert!(
            cache
                .take_composition_errors()
                .iter()
                .any(|e| matches!(e, Error::UnresolvedLayer { .. })),
            "the ancestor's unresolved reference is recorded"
        );
        Ok(())
    }

    /// A prim's recoverable build error is keyed by its path and replaced on
    /// rebuild, so dropping and recomposing the index (as a layer-stack edit
    /// does via `clear_all_indices` + re-query) does not duplicate it, and a
    /// prim that composes cleanly leaves no stale error behind.
    #[test]
    fn prim_errors_replace_on_rebuild() -> Result<()> {
        let (graph, mut cache) =
            in_memory_stack("#usda 1.0\ndef \"A\" (\n    references = @nonexistent.usd@\n)\n{\n}\n");
        let a = sdf::path("/A")?;
        let unresolved = |c: &IndexCache| {
            c.composition_errors()
                .iter()
                .filter(|e| matches!(e, Error::UnresolvedLayer { .. }))
                .count()
        };

        cache.ensure_index(&graph, &a)?;
        assert_eq!(unresolved(&cache), 1, "the unresolved reference is recorded once");

        // Drop and rebuild — the bookkeeping a SIGNIFICANT layer-stack edit
        // performs (clear_all_indices then a re-query). The error must not double.
        cache.drop_index(&a);
        cache.ensure_index(&graph, &a)?;
        assert_eq!(
            unresolved(&cache),
            1,
            "rebuilding replaces the prim's error, not appends"
        );

        // A prim with no error leaves no entry, so its (absent) errors can't go stale.
        let (clean_graph, mut clean_cache) = in_memory_stack("#usda 1.0\ndef \"A\" {}\n");
        clean_cache.ensure_index(&clean_graph, &a)?;
        assert!(
            clean_cache.composition_errors().is_empty(),
            "a cleanly composing prim records no error"
        );
        Ok(())
    }

    /// A reference whose asset path is a variable expression that fails to
    /// evaluate (here a non-string result) is recoverable: the broken arc is
    /// skipped and recorded as `InvalidExpression`, while the prim's own local
    /// opinion still composes — it does not abort the whole prim index.
    #[test]
    fn invalid_expression_arc_recoverable() -> Result<()> {
        let text = r#"#usda 1.0
def "A" (
    references = @`42`@
)
{
    custom string marker = "ok"
}
"#;
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        let layer = sdf::Layer::new("root.usda", Box::new(sdf::Data::from_specs(data)));
        let graph = LayerGraph::from_layers(vec![layer], 0, sdf::LayerRegistry::default());
        let mut cache = IndexCache::new(VariantFallbackMap::new(), true, Vec::new());

        let a = sdf::path("/A")?;
        cache.ensure_index(&graph, &a)?;
        let interp = |_: &sdf::TimeSampleMap, _: f64| None;
        assert_eq!(
            cache.value_at(&graph, &sdf::path("/A.marker")?, 0.0, &interp)?,
            Some(Value::String("ok".to_string())),
            "the prim's local opinion survives the broken expression arc"
        );
        assert!(
            cache
                .take_composition_errors()
                .iter()
                .any(|e| matches!(e, Error::InvalidExpression { .. })),
            "the invalid asset-path expression is recorded as a recoverable error"
        );
        Ok(())
    }

    /// A connection authored in a class that targets another instance of the
    /// class but is removed by a stronger `delete` must not emit a spurious
    /// instance-target diagnostic: `classify_inherit_targets` only reports targets
    /// that survive list-op composition, so a deleted target is neither dropped
    /// again nor reported.
    #[test]
    fn class_instance_target_deleted_no_error() -> Result<()> {
        let text = r#"#usda 1.0
def "Scope"
{
    class "LocalClass"
    {
        double y
        double x
        add double x.connect = </Scope/Instance_2.y>
        delete double x.connect = </Scope/Instance_2.y>
    }

    def "Instance_1" (inherits = </Scope/LocalClass>) {}
    def "Instance_2" (inherits = </Scope/LocalClass>) {}
}
"#;
        let (graph, mut cache) = in_memory_stack(text);
        let (targets, _) = cache.compute_attribute_connection_paths(&graph, &sdf::path("/Scope/Instance_1.x")?)?;
        assert!(targets.is_empty(), "the deleted connection target composes to nothing");
        let errors = cache.take_composition_errors();
        assert!(
            !errors.iter().any(|e| matches!(
                e,
                Error::InvalidInstanceTargetPath { .. } | Error::InvalidExternalTargetPath { .. }
            )),
            "a class target removed by a stronger delete must not be reported: {errors:?}"
        );
        Ok(())
    }

    /// An instance-target invalid contribution from a class node drops only that
    /// node's contribution: a stronger local opinion authoring the same target
    /// validly keeps it, while the class's invalid opinion is still reported.
    #[test]
    fn class_instance_target_kept_by_stronger_local() -> Result<()> {
        let text = r#"#usda 1.0
def "Scope"
{
    class "LocalClass"
    {
        double y
        double x
        add double x.connect = </Scope/Instance_2.y>
    }

    def "Instance_1" (inherits = </Scope/LocalClass>)
    {
        add double x.connect = </Scope/Instance_2.y>
    }

    def "Instance_2" (inherits = </Scope/LocalClass>) {}
}
"#;
        let (graph, mut cache) = in_memory_stack(text);
        let (targets, _) = cache.compute_attribute_connection_paths(&graph, &sdf::path("/Scope/Instance_1.x")?)?;
        assert_eq!(
            targets,
            vec![sdf::path("/Scope/Instance_2.y")?],
            "the stronger local connection keeps the target even though the class's is invalid"
        );
        let errors = cache.take_composition_errors();
        assert!(
            errors
                .iter()
                .any(|e| matches!(e, Error::InvalidInstanceTargetPath { .. })),
            "the class node's instance-target contribution is still reported: {errors:?}"
        );
        Ok(())
    }

    /// A reference's asset-path expression authored inside a referenced layer
    /// is evaluated against the composed expression variables, with the
    /// referencing layer stack overriding the referenced one (C++
    /// `PcpExpressionVariables`). The root sets `TARGET = "right.usda"`,
    /// overriding mid.usda's local `TARGET = "wrong.usda"`, so `/Model` resolves
    /// through mid to right.usda — collection must load right.usda for the arc
    /// to compose rather than the locally-named wrong.usda.
    #[test]
    fn expr_vars_compose_across_reference() -> Result<()> {
        let root = format!("{}/fixtures/expr_vars_compose/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);
        let interp = |_: &sdf::TimeSampleMap, _: f64| None;
        assert_eq!(
            cache.value_at(&graph, &sdf::path("/Model.source")?, 0.0, &interp)?,
            Some(Value::String("right".to_string())),
            "the referencing layer's TARGET override resolves the nested reference to right.usda"
        );
        Ok(())
    }

    /// A template clip set (`templateAssetPath` + start/end/stride) is
    /// expanded to explicit clips and resolves end to end through
    /// `value_at` (spec 12.3.4.1.3): `clip.1.usda` drives t=1, `clip.2.usda`
    /// drives t=2.
    #[test]
    fn resolves_template_clip_values() -> Result<()> {
        let root = format!("{}/fixtures/clip_template/root.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);
        // Exact-match sampler: each clip authors a single sample at its frame.
        let interp =
            |samples: &sdf::TimeSampleMap, t: f64| samples.iter().find(|(time, _)| *time == t).map(|(_, v)| v.clone());

        let size =
            |cache: &mut IndexCache, t: f64| cache.value_at(&graph, &sdf::path("/Model.size").unwrap(), t, &interp);
        assert_eq!(size(&mut cache, 1.0)?, Some(sdf::Value::Double(10.0)));
        assert_eq!(size(&mut cache, 2.0)?, Some(sdf::Value::Double(20.0)));
        Ok(())
    }

    /// A template clip set authored in a sublayer with a layer offset has its
    /// derived schedule retimed into stage time (spec 12.3.4): the offset of 10
    /// shifts `clip.1`'s frame to stage t=11 and `clip.2`'s to t=12.
    #[test]
    fn template_clip_schedule_retimed_by_offset() -> Result<()> {
        let root = format!("{}/fixtures/clip_template_offset/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);
        let size =
            |cache: &mut IndexCache, t: f64| cache.value_at(&graph, &sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 11.0)?, Some(Value::Double(10.0)));
        assert_eq!(size(&mut cache, 12.0)?, Some(Value::Double(20.0)));
        Ok(())
    }

    /// When a stronger layer authors explicit `assetPaths` and a weaker
    /// sublayer authors `templateAssetPath` for the same set, the explicit
    /// paths win (spec 12.3.4.1.3) and must anchor on the layer that authored
    /// them: `@./clip.usda@` resolves next to the root, not the sublayer.
    #[test]
    fn explicit_asset_paths_anchor_over_template() -> Result<()> {
        let root = format!("{}/fixtures/clip_asset_anchor/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);
        let size =
            |cache: &mut IndexCache, t: f64| cache.value_at(&graph, &sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(42.0)));
        Ok(())
    }

    /// Exact-match sampler: a clip resolves only at a frame it authors.
    fn exact(samples: &sdf::TimeSampleMap, t: f64) -> Option<Value> {
        samples.iter().find(|(time, _)| *time == t).map(|(_, v)| v.clone())
    }

    /// Linear sampler over `float` samples, held outside the sample range.
    fn lerp(samples: &sdf::TimeSampleMap, t: f64) -> Option<Value> {
        let as_f = |v: &Value| match v {
            Value::Float(f) => *f as f64,
            Value::Double(d) => *d,
            _ => 0.0,
        };
        let first = samples.first()?;
        if t <= first.0 {
            return Some(first.1.clone());
        }
        let last = samples.last()?;
        if t >= last.0 {
            return Some(last.1.clone());
        }
        let w = samples.windows(2).find(|w| t >= w[0].0 && t <= w[1].0)?;
        let f = (t - w[0].0) / (w[1].0 - w[0].0);
        Some(Value::Double(as_f(&w[0].1) + (as_f(&w[1].1) - as_f(&w[0].1)) * f))
    }

    /// A gap in the active clip falls to the manifest's authored default
    /// (spec 12.3.4.6): `t=0` is sampled from the clip, `t=10` (no sample)
    /// resolves to the manifest default `99.0`.
    #[test]
    fn missing_clip_value_uses_manifest_default() -> Result<()> {
        let root = format!("{}/fixtures/clip_missing_default/root.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);
        let size =
            |cache: &mut IndexCache, t: f64| cache.value_at(&graph, &sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(5.0)));
        assert_eq!(size(&mut cache, 10.0)?, Some(Value::Float(99.0)));
        Ok(())
    }

    /// A manifest-declared attribute with no default and a gap is
    /// authoritatively absent (spec 12.3.4.6): the clip owns the attribute, so
    /// the gap blocks fall-through to the referenced time samples (`777.0`) and
    /// resolves to `None` rather than the weaker value.
    #[test]
    fn missing_clip_value_without_default_blocks() -> Result<()> {
        let root = format!("{}/fixtures/clip_missing_block/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);
        let size =
            |cache: &mut IndexCache, t: f64| cache.value_at(&graph, &sdf::path("/Model.size").unwrap(), t, &exact);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(5.0)));
        assert_eq!(size(&mut cache, 10.0)?, None);
        Ok(())
    }

    /// `resolve_value_source` gates clips precisely: on a clip-bearing prim, an
    /// attribute the manifest declares (`size`) resolves as
    /// [`AttributeValueSource::Clips`], while a sibling the manifest does not
    /// declare (`extra`) falls through to its referenced `timeSamples` rather
    /// than being routed conservatively through the per-call clip path.
    #[test]
    fn value_source_skips_undeclared_clip_attr() -> Result<()> {
        let root = format!("{}/fixtures/clip_undeclared_arc/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);

        assert!(matches!(
            cache.resolve_value_source(&graph, &sdf::path("/Model.size")?)?,
            AttributeValueSource::Clips
        ));
        // `extra` is not in the manifest, so the clip set does not own it; the
        // source is the reference's time samples, queryable on the fast path.
        let AttributeValueSource::TimeSamples { samples, .. } =
            cache.resolve_value_source(&graph, &sdf::path("/Model.extra")?)?
        else {
            panic!("undeclared clip attribute must resolve as arc time samples");
        };
        assert_eq!(samples.as_slice(), &[(3.0, Value::Double(42.0))]);
        Ok(())
    }

    /// A manifest-less clip holds its value across its active interval, so it
    /// owns the attribute even at times where it authors no sample inside that
    /// interval. `resolve_value_source` must agree with `value_at` here: clip0
    /// (active over stage `[0, 10)`) authors only at clip-time 50, yet holds
    /// `50.0` at stage 5, so the source is `Clips` (deferring to `value_at`) and
    /// must not collapse to the reference's weaker `999.0` time sample — the
    /// divergence a discrete sample-time gate would cache.
    #[test]
    fn value_source_clips_held_manifestless() -> Result<()> {
        let root = format!("{}/fixtures/clip_manifestless_held/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&root);

        assert_eq!(
            cache.value_at(&graph, &sdf::path("/Model.size")?, 5.0, &lerp)?,
            Some(Value::Double(50.0))
        );
        assert!(matches!(
            cache.resolve_value_source(&graph, &sdf::path("/Model.size")?)?,
            AttributeValueSource::Clips
        ));
        Ok(())
    }

    /// `clip_sample_times` reports every active-window boundary of a
    /// participating set and `None` when no set sources the attribute. The
    /// manifest-less held set contributes only clip1's boundary at 10 (clip0's
    /// sole sample maps to stage 50, outside its `[0, 10)` window). A
    /// manifest that omits an attribute does not source it: `extra` returns
    /// `None`, falling through to the arc.
    #[test]
    fn clip_sample_times_boundaries() -> Result<()> {
        let held = format!("{}/fixtures/clip_manifestless_held/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&held);
        assert_eq!(
            cache.clip_sample_times(&graph, &sdf::path("/Model")?, ".size")?,
            Some(vec![10.0])
        );

        let arc = format!("{}/fixtures/clip_undeclared_arc/root.usda", manifest_dir());
        let (graph, mut cache) = collected_stack(&arc);
        assert!(cache
            .clip_sample_times(&graph, &sdf::path("/Model")?, ".extra")?
            .is_none());
        Ok(())
    }

    /// With `interpolateMissingClipValues`, a gap is filled by interpolating
    /// across the surrounding contributing clips (spec 12.3.4.7): the empty
    /// middle clip at `t=15` interpolates `0.0` (t=0 clip) and `100.0`
    /// (t=20 clip) to `75.0`.
    #[test]
    fn interpolate_missing_clip_values_across_clips() -> Result<()> {
        let root = format!("{}/fixtures/clip_missing_interp/root.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);
        let size =
            |cache: &mut IndexCache, t: f64| cache.value_at(&graph, &sdf::path("/Model.size").unwrap(), t, &lerp);
        assert_eq!(size(&mut cache, 0.0)?, Some(Value::Double(0.0)));
        assert_eq!(size(&mut cache, 15.0)?, Some(Value::Double(75.0)));
        assert_eq!(size(&mut cache, 20.0)?, Some(Value::Double(100.0)));
        Ok(())
    }

    /// Instances sharing a prototype compose their subtree once: every
    /// instance's descendants redirect into the shared prototype namespace, so
    /// the descendant is indexed under `/__Prototype_N` and never under an
    /// instance's own path (spec 11.3.3).
    #[test]
    fn instances_share_prototype() -> Result<()> {
        let root = format!("{}/fixtures/instancing_shared.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);
        let interp = |_: &sdf::TimeSampleMap, _: f64| None;

        // Query /A first so it mints /__Prototype_0 for its key.
        let size = |cache: &mut IndexCache, p: &str| cache.value_at(&graph, &sdf::path(p).unwrap(), 0.0, &interp);
        assert_eq!(size(&mut cache, "/A/Child.size")?, Some(sdf::Value::Double(5.0)));
        assert_eq!(size(&mut cache, "/B/Child.size")?, Some(sdf::Value::Double(5.0)));
        assert_eq!(size(&mut cache, "/C/Child.size")?, Some(sdf::Value::Double(9.0)));

        // /A and /B share /__Prototype_0; /C uses /__Prototype_1. The shared
        // subtree composes once in each prototype namespace, and no instance's
        // own descendant path is ever indexed.
        assert!(cache.is_indexed(&sdf::path("/__Prototype_0/Child")?));
        assert!(cache.is_indexed(&sdf::path("/__Prototype_1/Child")?));
        assert!(!cache.is_indexed(&sdf::path("/A/Child")?));
        assert!(!cache.is_indexed(&sdf::path("/B/Child")?));
        assert!(!cache.is_indexed(&sdf::path("/C/Child")?));
        Ok(())
    }

    /// Reading a deep instance-proxy value composes the shared prototype subtree
    /// once: the instance-ness check on an intermediate proxy prim redirects to
    /// the shared `/__Prototype_N` index instead of composing a throwaway literal
    /// index per instance, so no intermediate proxy path is ever indexed (spec
    /// 11.3.3).
    #[test]
    fn proxy_descendants_share_prototype() -> Result<()> {
        let root = format!("{}/fixtures/instancing_deep.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);
        let interp = |_: &sdf::TimeSampleMap, _: f64| None;
        let v = |cache: &mut IndexCache, p: &str| cache.value_at(&graph, &sdf::path(p).unwrap(), 0.0, &interp);

        // Reading the deep value walks the proxy ancestors (/A/Mid, /B/Mid),
        // testing each for instance-ness.
        assert_eq!(v(&mut cache, "/A/Mid/Leaf.v")?, Some(sdf::Value::Double(1.0)));
        assert_eq!(v(&mut cache, "/B/Mid/Leaf.v")?, Some(sdf::Value::Double(1.0)));

        // The shared subtree composes once, under the prototype namespace.
        assert!(cache.is_indexed(&sdf::path("/__Prototype_0/Mid")?));
        assert!(cache.is_indexed(&sdf::path("/__Prototype_0/Mid/Leaf")?));
        // No intermediate proxy prim is composed literally at an instance path.
        for p in ["/A/Mid", "/B/Mid", "/A/Mid/Leaf", "/B/Mid/Leaf"] {
            assert!(!cache.is_indexed(&sdf::path(p)?), "{p} must not be indexed literally");
        }
        Ok(())
    }

    /// A nested instance inside a prototype namespace mints its own prototype and
    /// its descendants redirect onto it: both an outer proxy (`/A/Nested/Leaf`)
    /// and the prototype-namespace path (`/__Prototype_0/Nested/Leaf`) resolve
    /// through the nested prototype, so the nested descendant never composes in
    /// place under the outer prototype (spec 11.3.3).
    #[test]
    fn nested_prototype_proxy_redirects() -> Result<()> {
        let root = format!("{}/fixtures/instancing_nested_in_prototype.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);
        let interp = |_: &sdf::TimeSampleMap, _: f64| None;
        let v = |cache: &mut IndexCache, p: &str| cache.value_at(&graph, &sdf::path(p).unwrap(), 0.0, &interp);

        // /A mints /__Prototype_0 (for /Outer); the nested instance mints
        // /__Prototype_1 (for /Inner). Both the outer proxy and the
        // prototype-namespace path resolve the nested leaf.
        assert_eq!(v(&mut cache, "/A/Nested/Leaf.v")?, Some(sdf::Value::Double(3.0)));
        assert_eq!(
            v(&mut cache, "/__Prototype_0/Nested/Leaf.v")?,
            Some(sdf::Value::Double(3.0))
        );

        // Both redirect to the nested prototype; neither the prototype-namespace
        // nested descendant nor the outer proxy is composed in place.
        assert!(cache.is_indexed(&sdf::path("/__Prototype_1/Leaf")?));
        assert!(!cache.is_indexed(&sdf::path("/__Prototype_0/Nested/Leaf")?));
        assert!(!cache.is_indexed(&sdf::path("/A/Nested/Leaf")?));

        // The nested instance reached via the instance namespace (/A/Nested) and
        // via the prototype namespace (/__Prototype_0/Nested) is the same shared
        // composition, so both resolve to one nested prototype — exactly two
        // prototypes total, not three.
        assert_eq!(
            cache.prototype_of(&graph, &sdf::path("/A/Nested")?)?,
            cache.prototype_of(&graph, &sdf::path("/__Prototype_0/Nested")?)?,
        );
        assert_eq!(cache.prototypes().len(), 2);
        Ok(())
    }

    /// A reference nested inside the prototype (below the instanceable arc) is
    /// shared (spec 11.3.3): its opinions reach the instance through the direct
    /// instanceable arc, so they survive in the instance's child names and
    /// descendants. The nested arc is authored in the referenced namespace, so
    /// its namespace depth is shallow — a flat `namespace_depth < instance_depth`
    /// test would wrongly drop it as an outer reference; the structural trunk
    /// partition keeps it because its parent (the prototype root) is not on the
    /// instance trunk.
    #[test]
    fn nested_reference_in_prototype_shared() -> Result<()> {
        let root = format!("{}/fixtures/instancing_nested_reference.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);
        let inst = sdf::path("/World/Inst")?;

        // The instance is at namespace depth 2 and is a real instance.
        assert!(cache.is_instance(&graph, &inst)?, "/World/Inst resolves as an instance");

        // Child names come from the shared prototype: ProtoChild from /Proto and
        // OtherChild from the nested /Other reference (the leaked case the flat
        // depth proxy dropped).
        let children = cache.prim_children(&graph, &inst)?;
        assert!(
            children.iter().any(|t| t.as_str() == "ProtoChild"),
            "prototype child must appear: {children:?}"
        );
        assert!(
            children.iter().any(|t| t.as_str() == "OtherChild"),
            "nested-reference child must appear: {children:?}"
        );

        // The nested reference's opinions resolve on the shared descendant.
        let interp = |_: &sdf::TimeSampleMap, _: f64| None;
        assert_eq!(
            cache.value_at(&graph, &sdf::path("/World/Inst/OtherChild.size")?, 0.0, &interp)?,
            Some(Value::Double(7.0)),
            "nested-reference descendant value survives in the shared subtree"
        );
        assert_eq!(
            cache.value_at(&graph, &sdf::path("/World/Inst.otherAttr")?, 0.0, &interp)?,
            Some(Value::Double(5.0)),
            "nested-reference attribute survives on the instance root"
        );
        Ok(())
    }

    /// `instances_of` is sorted by path, so the result is independent of the
    /// order instances were registered (spec 11.3.3).
    #[test]
    fn instances_of_sorted() -> Result<()> {
        let root = format!("{}/fixtures/instancing_shared.usda", manifest_dir());
        let (graph, mut cache) = single_layer_stack(&root);

        // Register /B before /A so registration order is [/B, /A].
        let proto = cache.prototype_of(&graph, &sdf::path("/B")?)?.unwrap();
        assert_eq!(cache.prototype_of(&graph, &sdf::path("/A")?)?, Some(proto.clone()));

        // The returned instances are still sorted by path.
        assert_eq!(cache.instances_of(&proto), vec![sdf::path("/A")?, sdf::path("/B")?]);
        Ok(())
    }

    /// A significant change (here, flipping `instanceable`) clears the
    /// prototype registry so stale instance-to-prototype mappings do not
    /// persist (spec 11.3.3).
    #[test]
    fn instance_change_invalidates_prototypes() -> Result<()> {
        let root = format!("{}/fixtures/instancing_shared.usda", manifest_dir());
        let (mut graph, mut cache) = single_layer_stack(&root);
        let root_id = graph.root_id().unwrap();

        assert!(cache.prototype_of(&graph, &sdf::path("/A")?)?.is_some());
        assert!(!cache.prototypes().is_empty());

        let mut cl = sdf::ChangeList::new();
        cl.entry_mut(&sdf::path("/A")?)
            .info_changed
            .insert(sdf::FieldKey::Instanceable.as_str().into());
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(root_id, &cl)]);
        changes.apply(&mut cache, &mut graph);

        assert!(cache.prototypes().is_empty());
        Ok(())
    }

    /// A plain inert `over` authored after a prim was queried as empty must
    /// become visible: the spec-tier rescan refreshes the cached site's
    /// `has_specs` in place (or drops a nodeless stale index), so the next
    /// query sees the spec without a significant subtree rebuild.
    #[test]
    fn inert_add_recomposes() -> Result<()> {
        let (mut graph, mut cache) = in_memory_stack("#usda 1.0\ndef \"A\" {}\n");
        let root_id = graph.root_id().unwrap();

        // Query a prim no layer authors: cached as an empty index.
        assert!(!cache.has_spec(&graph, &sdf::path("/Foo")?)?);

        // Author an inert `over "Foo"` into the root layer.
        let node = graph.get_mut(root_id).unwrap();
        edit_layer(&mut node.layer, |e| {
            sdf::PrimSpec::new(e.data_mut(), "/Foo", sdf::Specifier::Over, "")?;
            Ok(())
        })?;

        // Drive the inert add through the change pipeline.
        let mut cl = sdf::ChangeList::new();
        cl.entry_mut(&sdf::path("/Foo")?).flags = sdf::ChangeFlags::ADD_INERT_PRIM;
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(root_id, &cl)]);
        changes.apply(&mut cache, &mut graph);

        // The spec-tier rescan made the new opinion visible.
        assert!(cache.has_spec(&graph, &sdf::path("/Foo")?)?);
        Ok(())
    }

    /// An `over` authored together with a composition arc recomposes despite
    /// the inert specifier: the change record surfaces `references` in
    /// `info_changed` (only the auto-stamped `specifier` folds into the add), so
    /// the classifier treats the inert add as significant.
    #[test]
    fn inert_add_with_arc_recomposes() -> Result<()> {
        let (mut graph, mut cache) = in_memory_stack("#usda 1.0\ndef \"Class\" { int x = 5 }\n");
        let root_id = graph.root_id().unwrap();
        let inst = sdf::path("/Inst")?;

        // Query /Inst before it exists: cached as empty, composing no arc.
        assert!(!cache.has_composition_arc(&graph, &inst)?);

        // Author `over "Inst" ( references = </Class> )` through the recording proxy.
        let cl = edit_layer(&mut graph.get_mut(root_id).unwrap().layer, |l| {
            let data = l.data_mut();
            data.create_spec(inst.clone(), sdf::SpecType::Prim);
            data.set_field(
                &inst,
                sdf::FieldKey::Specifier.as_str(),
                Value::Specifier(sdf::Specifier::Over),
            );
            let refs = sdf::ReferenceListOp::explicit([sdf::Reference {
                prim_path: sdf::path("/Class").unwrap(),
                ..Default::default()
            }]);
            data.set_field(&inst, sdf::FieldKey::References.as_str(), Value::ReferenceListOp(refs));
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(root_id, &cl)]);
        changes.apply(&mut cache, &mut graph);

        // The reference is composed, not skipped by an in-place spec refresh.
        assert!(cache.has_composition_arc(&graph, &inst)?);
        Ok(())
    }

    /// Erasing an `over` that carried a composition arc recomposes: the change
    /// record carries the removed `references` field, so the classifier
    /// treats the inert removal as significant and the arc is torn down.
    #[test]
    fn inert_remove_of_arc_recomposes() -> Result<()> {
        let (mut graph, mut cache) =
            in_memory_stack("#usda 1.0\ndef \"Class\" { int x = 5 }\nover \"Inst\" ( references = </Class> ) {}\n");
        let root_id = graph.root_id().unwrap();
        let inst = sdf::path("/Inst")?;

        // The reference composes initially.
        assert!(cache.has_composition_arc(&graph, &inst)?);

        // Erase the /Inst spec through the recording proxy and drive the removal.
        let cl = edit_layer(&mut graph.get_mut(root_id).unwrap().layer, |l| {
            l.data_mut().erase_spec(&inst);
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(root_id, &cl)]);
        changes.apply(&mut cache, &mut graph);

        // The arc is gone, not left dangling by an in-place spec refresh.
        assert!(!cache.has_composition_arc(&graph, &inst)?);
        Ok(())
    }

    /// Authoring a spec at a previously-empty arc target recomposes a dependent
    /// that had culled the arc: the spec-tier rescan drops the dependent so its
    /// rebuild un-culls the reference, which an in-place `has_specs` flip cannot.
    #[test]
    fn inert_add_unculls_dependent() -> Result<()> {
        // /A references a prim the base layer does not define, so the reference
        // is culled until the target is authored.
        let root = parse_named_layer(
            "root.usd",
            "#usda 1.0\ndef \"A\" ( references = @base.usd@</Empty> ) {}\n",
        );
        let base = parse_named_layer("base.usd", "#usda 1.0\ndef \"Other\" {}\n");
        let mut graph = LayerGraph::from_layers(vec![root, base], 0, sdf::LayerRegistry::default());
        let base_id = graph.id_of("base.usd").unwrap();
        let mut cache = IndexCache::new(VariantFallbackMap::new(), true, Vec::new());
        let a = sdf::path("/A")?;

        // The empty target makes /A's reference culled — no composition arc.
        assert!(!cache.has_composition_arc(&graph, &a)?);

        // Author `over "Empty"` into the base layer so the target now exists.
        let cl = edit_layer(&mut graph.get_mut(base_id).unwrap().layer, |l| {
            let data = l.data_mut();
            data.create_spec(sdf::path("/Empty").unwrap(), sdf::SpecType::Prim);
            data.set_field(
                &sdf::path("/Empty").unwrap(),
                sdf::FieldKey::Specifier.as_str(),
                Value::Specifier(sdf::Specifier::Over),
            );
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(base_id, &cl)]);
        // The inert add routes through the spec tier (not a significant fanout),
        // so the rescan's un-cull path is what recomposes /A.
        assert!(changes
            .cache
            .did_change_specs
            .contains(&(base_id, sdf::path("/Empty")?)));
        changes.apply(&mut cache, &mut graph);

        // The reference un-culled: /A now composes the arc.
        assert!(cache.has_composition_arc(&graph, &a)?);
        Ok(())
    }

    /// The same un-cull path works for an empty *inherit* target: authoring the
    /// class via an inert `over` recomposes the dependent, since the spec-tier
    /// rescan now sees the inherit as culled and rebuilds rather than flipping
    /// `has_specs` in place.
    #[test]
    fn inert_add_unculls_inherit() -> Result<()> {
        // /A inherits a class the layer does not define, so the inherit is culled
        // until the class is authored.
        let root = parse_named_layer("root.usd", "#usda 1.0\ndef \"A\" ( inherits = </_class_Foo> ) {}\n");
        let mut graph = LayerGraph::from_layers(vec![root], 0, sdf::LayerRegistry::default());
        let root_id = graph.id_of("root.usd").unwrap();
        let mut cache = IndexCache::new(VariantFallbackMap::new(), true, Vec::new());
        let a = sdf::path("/A")?;

        // The empty class makes /A's inherit culled — no composition arc.
        assert!(!cache.has_composition_arc(&graph, &a)?);

        // Author `over "_class_Foo"` so the class now exists.
        let cl = edit_layer(&mut graph.get_mut(root_id).unwrap().layer, |l| {
            sdf::PrimSpecMut::over(l.data_mut(), "/_class_Foo")?;
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(root_id, &cl)]);
        assert!(changes
            .cache
            .did_change_specs
            .contains(&(root_id, sdf::path("/_class_Foo")?)));
        changes.apply(&mut cache, &mut graph);

        // The inherit un-culled: /A now composes the arc.
        assert!(cache.has_composition_arc(&graph, &a)?);
        Ok(())
    }

    /// An empty *specialize* target un-culls the same way: the culled
    /// copy-to-root node carries the dependency, so authoring the class
    /// recomposes the dependent.
    #[test]
    fn inert_add_unculls_specialize() -> Result<()> {
        let root = parse_named_layer("root.usd", "#usda 1.0\ndef \"A\" ( specializes = </_class_Foo> ) {}\n");
        let mut graph = LayerGraph::from_layers(vec![root], 0, sdf::LayerRegistry::default());
        let root_id = graph.id_of("root.usd").unwrap();
        let mut cache = IndexCache::new(VariantFallbackMap::new(), true, Vec::new());
        let a = sdf::path("/A")?;

        assert!(!cache.has_composition_arc(&graph, &a)?);

        let cl = edit_layer(&mut graph.get_mut(root_id).unwrap().layer, |l| {
            sdf::PrimSpecMut::over(l.data_mut(), "/_class_Foo")?;
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(root_id, &cl)]);
        assert!(changes
            .cache
            .did_change_specs
            .contains(&(root_id, sdf::path("/_class_Foo")?)));
        changes.apply(&mut cache, &mut graph);

        assert!(cache.has_composition_arc(&graph, &a)?);
        Ok(())
    }

    /// A descendant under an empty ancestral variant selection carries the
    /// variant as a culled node and reports no live composition arc. The parent's
    /// local variant arc is culled when its `{set=sel}` site authors nothing, and
    /// the ancestral seed clones that culled node down to the descendant — so the
    /// cull reaches descendants without a separate path. `has_composition_arc`
    /// stays gated on `has_specs`, so the spec-less variant never counts as a
    /// composition arc.
    #[test]
    fn empty_ancestral_variant_culled() -> Result<()> {
        // /A selects a variant its set never authors; /A/Child is authored
        // directly, so it composes under the empty ancestral selection.
        let (graph, mut cache) = in_memory_stack(
            "#usda 1.0\ndef \"A\" (\n    variantSets = \"v\"\n    variants = { string v = \"missing\" }\n) {\n  def \"Child\" { custom double x = 1 }\n  variantSet \"v\" = {\n    \"present\" {}\n  }\n}\n",
        );
        let child = sdf::path("/A/Child")?;

        // The child composes from its own opinion, not the empty variant.
        assert!(!cache.has_composition_arc(&graph, &child)?);
        let index = cache.index_at(&child).expect("child index");
        assert!(
            index.all_nodes().any(|n| n.arc == ArcType::Variant && n.is_culled()),
            "the empty ancestral variant target is culled"
        );
        assert!(
            index.nodes().all(|n| n.arc != ArcType::Variant),
            "the culled variant contributes nothing to resolution"
        );
        Ok(())
    }

    /// Removing the final spec at an inherit target re-culls it. The contributing
    /// node loses its last spec, so the spec-tier rescan rebuilds and the now-empty
    /// target composes as a culled node — the same representation as an
    /// always-empty target, which keeps a later re-add on the un-cull rebuild path
    /// rather than an in-place flip that would skip grafting.
    #[test]
    fn inert_remove_reculls_inherit() -> Result<()> {
        // /A inherits a class that exists only as an inert `over`, so the inherit
        // node contributes a spec.
        let (mut graph, mut cache) =
            in_memory_stack("#usda 1.0\ndef \"A\" ( inherits = </_class_Foo> ) {}\nover \"_class_Foo\" {}\n");
        let root_id = graph.root_id().unwrap();
        let a = sdf::path("/A")?;

        // The class exists, so /A composes the inherit.
        assert!(cache.has_composition_arc(&graph, &a)?);

        // Erase the class's only spec — a purely inert removal.
        let cl = edit_layer(&mut graph.get_mut(root_id).unwrap().layer, |l| {
            l.data_mut().erase_spec(&sdf::path("/_class_Foo").unwrap());
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(root_id, &cl)]);
        assert!(changes
            .cache
            .did_change_specs
            .contains(&(root_id, sdf::path("/_class_Foo")?)));
        changes.apply(&mut cache, &mut graph);

        // The emptied inherit composes as a culled node, just like an always-empty
        // target — the rescan rebuilt rather than flipping `has_specs` in place.
        assert!(!cache.has_composition_arc(&graph, &a)?);
        let index = cache.index_at(&a).expect("index rebuilt on query");
        assert!(
            index.all_nodes().any(|n| n.arc == ArcType::Inherit && n.is_culled()),
            "the emptied inherit target re-culled"
        );
        Ok(())
    }

    /// A reference to a *nested* missing target also recomposes when the target
    /// is authored. A sub-root target is grafted as a non-culled spec-less node
    /// (not the root case's culled node), so the spec-tier rescan refreshes its
    /// `has_specs` in place — no separate empty-target cull is needed.
    #[test]
    fn inert_add_recomposes_subroot_target() -> Result<()> {
        let root = parse_named_layer(
            "root.usd",
            "#usda 1.0\ndef \"A\" ( references = @base.usd@</Parent/Empty> ) {}\n",
        );
        let base = parse_named_layer("base.usd", "#usda 1.0\ndef \"Other\" {}\n");
        let mut graph = LayerGraph::from_layers(vec![root, base], 0, sdf::LayerRegistry::default());
        let base_id = graph.id_of("base.usd").unwrap();
        let mut cache = IndexCache::new(VariantFallbackMap::new(), true, Vec::new());
        let a = sdf::path("/A")?;

        // The missing nested target makes /A's reference contribute nothing.
        assert!(!cache.has_composition_arc(&graph, &a)?);

        // Author the nested target through the recording proxy.
        let cl = edit_layer(&mut graph.get_mut(base_id).unwrap().layer, |l| {
            l.data_mut()
                .create_spec(sdf::path("/Parent/Empty").unwrap(), sdf::SpecType::Prim);
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(base_id, &cl)]);
        changes.apply(&mut cache, &mut graph);

        // /A now composes the reference.
        assert!(cache.has_composition_arc(&graph, &a)?);
        Ok(())
    }

    /// Removing an inert `over` carrying `active = false` reactivates the prim:
    /// the change record carries the removed `active` field, so the classifier
    /// treats the removal as significant, the subtree recomposes from the weaker
    /// `def`, and `active` resolves to its default — the subtree is not left
    /// inactive after the opinion is gone.
    #[test]
    fn inert_remove_of_active_reactivates() -> Result<()> {
        // A strong layer deactivates /World with an inert over; the weak layer
        // it sublayers defines /World and its child.
        let strong = parse_named_layer(
            "strong.usda",
            "#usda 1.0\n(\n    subLayers = [@weak.usda@]\n)\nover \"World\" ( active = false ) {}\n",
        );
        let weak = parse_named_layer("weak.usda", "#usda 1.0\ndef \"World\" {\n  def \"Child\" {}\n}\n");
        let mut graph = LayerGraph::from_layers(vec![strong, weak], 0, sdf::LayerRegistry::default());
        let strong_id = graph.root_id().unwrap();
        let mut cache = IndexCache::new(VariantFallbackMap::new(), true, Vec::new());

        let world = sdf::path("/World")?;
        let has_child = |cache: &mut IndexCache, graph: &LayerGraph| -> Result<bool> {
            Ok(cache
                .prim_children(graph, &world)?
                .iter()
                .any(|c| c.as_str() == "Child"))
        };

        // The over is in effect: `active` resolves false, the child still composes.
        assert_eq!(
            cache.resolve_field(&graph, &world, sdf::FieldKey::Active.as_str())?,
            Some(Value::Bool(false))
        );
        assert!(has_child(&mut cache, &graph)?);

        // Erase the over spec on the strong layer and drive the change the
        // layer derives from it.
        let cl = edit_layer(&mut graph.get_mut(strong_id).unwrap().layer, |l| {
            l.data_mut().erase_spec(&world);
            Ok(())
        })
        .unwrap();
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(&cache, &[(strong_id, &cl)]);
        changes.apply(&mut cache, &mut graph);

        // The active=false opinion is gone — the prim reactivates by default —
        // and the def-composed subtree survives.
        assert_eq!(
            cache.resolve_field(&graph, &world, sdf::FieldKey::Active.as_str())?,
            None
        );
        assert!(cache.has_spec(&graph, &world)?);
        assert!(has_child(&mut cache, &graph)?);
        Ok(())
    }

    /// Authors a `layerRelocates` edit on the root layer and drives it through
    /// the change pipeline, returning the graph's diagnostics afterward.
    fn relocate_edit(graph: &mut LayerGraph, cache: &mut IndexCache, text: &str) -> Vec<Error> {
        let root_id = graph.root_id().unwrap();
        graph.get_mut(root_id).expect("root layer exists").layer = parse_layer(text);
        let mut cl = sdf::ChangeList::new();
        cl.entry_mut(&Path::abs_root())
            .info_changed
            .insert(sdf::FieldKey::LayerRelocates.as_str().into());
        let mut changes = crate::pcp::Changes::new();
        changes.did_change(cache, &[(root_id, &cl)]);
        changes.apply(cache, graph);
        graph.errors()
    }

    /// A `layerRelocates` edit that authors an invalid relocate after stage
    /// creation must surface an `InvalidRelocate` diagnostic from the graph,
    /// which the recompute path refreshes in place.
    #[test]
    fn invalid_relocate_edit_surfaces_error() -> Result<()> {
        let (mut graph, mut cache) = in_memory_stack("#usda 1.0\ndef \"A\" {}\n");
        // No relocates authored yet, so the graph holds no diagnostics.
        assert!(graph.errors().is_empty());

        // Author an invalid relocate (the target is an ancestor of the source).
        let errors = relocate_edit(
            &mut graph,
            &mut cache,
            "#usda 1.0\n(\n    relocates = { </A/B/C>: </A> }\n)\ndef \"A\" {}\n",
        );
        assert!(
            errors.iter().any(|e| matches!(e, Error::InvalidRelocate { .. })),
            "an invalid relocate authored after construction must be retained"
        );
        Ok(())
    }

    /// Re-authoring a valid relocate over an invalid one clears the diagnostic,
    /// and recomputing the same state twice does not duplicate it — the graph's
    /// relocate-error bucket is replaced wholesale on every rebuild.
    #[test]
    fn relocate_error_clears_and_dedups() -> Result<()> {
        let (mut graph, mut cache) = in_memory_stack("#usda 1.0\ndef \"A\" {}\n");

        // Author an invalid relocate, then the same edit twice: still exactly one.
        let invalid = "#usda 1.0\n(\n    relocates = { </A/B/C>: </A> }\n)\ndef \"A\" {}\n";
        let _ = relocate_edit(&mut graph, &mut cache, invalid);
        let errors = relocate_edit(&mut graph, &mut cache, invalid);
        assert_eq!(
            errors
                .iter()
                .filter(|e| matches!(e, Error::InvalidRelocate { .. }))
                .count(),
            1,
            "recomputing the same invalid relocate must not duplicate the diagnostic"
        );

        // Re-author a valid relocate; the stale invalid diagnostic disappears.
        let valid = "#usda 1.0\n(\n    relocates = { </A/B>: </A/C> }\n)\ndef \"A\" {}\n";
        let errors = relocate_edit(&mut graph, &mut cache, valid);
        assert!(
            !errors.iter().any(|e| matches!(e, Error::InvalidRelocate { .. })),
            "fixing the relocate must clear the diagnostic"
        );
        Ok(())
    }
}
