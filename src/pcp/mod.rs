//! Prim Cache Population (PCP) — the composition engine.
//!
//! This module implements USD's composition algorithm, which merges opinions
//! from multiple layers into a single composed scene graph. It is the Rust
//! equivalent of [Pixar's PCP module](https://openusd.org/dev/api/pcp_page_front.html).
//!
//! # LIVERPS strength ordering
//!
//! USD composes opinions using seven arc types, ordered by strength
//! (mnemonic "liver-peas"):
//!
//! 1. **L**ocal — direct opinions in the root layer stack (sublayers)
//! 2. **I**nherits — opinions from class prims (`inherits = </Class>`)
//! 3. **V**ariants — opinions from the selected variant (`variants = { string v = "sel" }`)
//! 4. **R**elocates — non-destructive namespace remapping (`relocates = { </Src>: </Tgt> }`)
//! 5. **R**eferences — opinions from referenced layers (`references = @model.usd@</Prim>`)
//! 6. **P**ayloads — like references but deferred (`payload = @heavy.usd@</Prim>`)
//! 7. **S**pecializes — like inherits but weakest (`specializes = </Base>`)
//!
//! Within each arc type, opinions are ordered by layer strength (root layer
//! strongest, deepest sublayer weakest).
//!
//! # Relocates
//!
//! Relocates are non-destructive namespace remapping authored via
//! `relocates = { </Source>: </Target> }` in a layer's metadata. They
//! allow moving prims in the composed namespace without modifying the
//! underlying layers. The `Cache` handles relocates at the scene graph
//! level:
//!
//! - `layerRelocates` are extracted from each layer's pseudoroot at
//!   construction and mapped into the composed namespace through each
//!   layer's namespace mapping.
//! - When composing a prim that is a relocate target, the cache finds the
//!   pre-relocation source path, builds a full composition index for it,
//!   and merges the resulting nodes as `Relocate` arc nodes. Each grafted
//!   node carries the source site's full layer stack, so a relocate source
//!   spanning several sublayers keeps every member, not just the strongest.
//! - Prim children are adjusted to hide relocated source children and
//!   expose target children, including children created by relocates
//!   within referenced layers.
//!
//! # Module structure
//!
//! | Item | C++ equivalent | Description |
//! |------|---------------|-------------|
//! | `LayerStack` | `PcpLayerStack` | Layers and precomputed sublayer stacks bundled into a single unit. |
//! | `cache` | `PcpCache` | Lazily-built composition cache. Main interface for [`Stage`](crate::usd::Stage). Owns a `LayerStack`. |
//! | [`Error`] | `PcpErrorBase` | Composition errors: arc cycles, unresolved layers, missing/invalid `defaultPrim`, arc-to-private-site permission denials. |
//! | `index` | `PcpPrimIndex` | Per-prim composition support: the [`PrimIndex`] type with its build/relocate entry points, the [`CompositionContext`](index::CompositionContext) that flows parent-to-child, and the value-resolution helpers the `builder` drives. |
//! | `builder` | `Pcp_PrimIndexer` | Task-queue composition engine: grows the graph node-by-node by draining a priority task queue. The sole composition path. |
//! | `graph` | `PcpPrimIndex` / `PcpNodeRef` | Arena-backed `PrimIndexGraph` of [`Node`]s with parent/child and origin links, plus the strength-order projection. |
//! | `resolve` | — | Value resolution over a composed [`PrimIndex`]: the per-field strength-ordered opinion walk (spec section 12). |
//! | `mapping` | `PcpMapFunction` | Namespace mapping between composition arcs — each [`Node`] carries `map_to_parent` and `map_to_root`. |
//! | [`VariantFallbackMap`] | `PcpVariantFallbackMap` | Maps variant set names to ordered fallback selections, used when no selection is authored. |
//! | `rel` | — | [`Relocates`](rel::Relocates): isolated relocate state and logic. Owned by `Cache`, receives external data through parameters. |
//!
//! Layer collection lives in [`crate::layer`] (analogous to `PcpLayerStack`).
//!
//! # Architecture
//!
//! Each [`PrimIndex`](index::PrimIndex) is an arena-backed, single-rooted tree
//! of [`Node`]s: a synthetic, inert root owns every otherwise-parentless node,
//! so the graph is one tree rather than a forest. Nodes carry two namespace
//! mappings: `map_to_parent` (translates paths to the parent node's namespace)
//! and `map_to_root` (translates directly to the root namespace). These
//! [`MapFunction`]s are the foundation for namespace remapping across
//! composition arcs (including relocates). After construction, a separate
//! projection orders the nodes strongest-to-weakest — a pre-order DFS of
//! strength-ordered children followed by the globally-weak specializes band —
//! so value resolution is a linear scan.
//!
//! Composition is driven by a [`CompositionContext`](index::CompositionContext)
//! that flows from parent prims to children. The context carries:
//!
//! - Variant selections from all ancestors, so descendant prims resolve
//!   variant sets without recomputing ancestor composition.
//! - Arc mappings from ancestors, recording how composed paths map to
//!   paths in other layers. Used for descendant namespace remapping and
//!   implied inherit propagation.
//!
//! # Variant fallbacks
//!
//! A [`VariantFallbackMap`] can be provided when opening a stage via
//! [`StageBuilder::variant_fallbacks`](crate::usd::StageBuilder::variant_fallbacks).
//! When a prim has a variant set but no authored selection, the engine tries
//! each fallback in order. The first fallback matching an existing variant in
//! the set is used; if none match, the set stays unselected. Authored
//! selections always take priority over fallbacks.
//!
//! The [`Cache`](cache::Cache) stores both the [`PrimIndex`](index::PrimIndex)
//! and the [`CompositionContext`](index::CompositionContext) for each composed
//! prim. During depth-first traversal, parents are always composed before
//! children, so the context chain is always populated. Each per-prim build
//! takes only shared references, making it suitable for future parallel
//! execution.
//!
//! Composition errors ([`Error`]) are returned from [`Cache`](cache::Cache)
//! methods and handled by the [`Stage`](crate::usd::Stage)'s error callback.
//! The callback decides whether to skip the broken arc and continue or
//! abort composition entirely.
//!
//! # Cache invalidation
//!
//! When a layer is authored, only the prim indices observably affected by
//! the write are dropped from the cache. The pipeline mirrors C++
//! `PcpChanges`:
//!
//! 1. The authoring callsite returns an [`sdf::ChangeList`](crate::sdf::ChangeList)
//!    describing what it just did (the path, flag bits for spec adds/removes,
//!    field names in `info_changed`).
//! 2. [`Changes::did_change`] reads the change list and classifies each
//!    entry into one of three tiers:
//!    - Significant — graph topology may be wrong. Drop the index and every
//!      namespace descendant. Triggered by composition-arc fields
//!      (`references`, `payload`, `inheritPaths`, `specializes`,
//!      `variantSetNames`, `variantSelection`, `instanceable`, `specifier`,
//!      `active`) and by non-inert prim adds/removes.
//!    - Prim — local rebuild only, descendants survive. Currently collapsed
//!      into significant; the field exists for a future finer-grained split.
//!    - Spec — graph is fine, only the spec stack changed. No-op while the
//!      cache doesn't memoize the stacks; reserved for the future split.
//!
//!    Layer-stack-tier flags (sublayers, sublayer offsets, `layerRelocates`,
//!    `defaultPrim`) cause the whole stack to be marked significant — every
//!    cached index is dropped because composition topology may have shifted.
//!
//! 3. [`Changes::apply`] surgically removes the affected entries from the
//!    cache. Indices rebuild lazily on next access.
//!
//! A reverse `(layer_index, site_path) → prim_index_paths` map (the
//! `Dependencies` table internal to the cache) makes step 2 cheap: every
//! [`PrimIndex`](index::PrimIndex) registers its observed sites when it
//! finishes building, and the classifier looks up dependents — including
//! ancestors of the changed site, since an arc at `/Foo` makes `/Foo/Bar`'s
//! composition transitively dependent on `/Foo`.
//!
//! Property-tier authoring (attribute values, time samples, relationship
//! targets) never invalidates the prim graph: those queries read live
//! layer data on every call.
//!
//! # Remaining work
//!
//! The task-queue [`Builder`](builder) (C++ `Pcp_PrimIndexer`) is the sole
//! composition engine: it composes LIVRPS, value resolution, relocates,
//! variants, instancing, value clips, and surgical invalidation. The recursive
//! builder and the cache relocate post-pass have been removed. The remaining
//! gaps are tracked asset-by-asset in `SKIP_PCP_COMPLIANCE`
//! (`tests/composition.rs`).
//!
//! ## Composition gaps (suppressed compliance assets)
//!
//! - Specializes/inherit authored inside a selected variant. A class arc whose
//!   target resolves to a variant-selection path is left uncomposed
//!   (`eval_class_arcs` skips it); it needs C++ `_DetermineInheritPath`'s
//!   strip/re-add of the selection together with the specializes-copy-to-root
//!   and reference strength interaction (`SpecializesAndVariants4`).
//! - "Spooky" relocated opinions. When a relocation source is reached through a
//!   variant, a symmetric rig, or a multi-relocation chain, its deeper opinions
//!   must still contribute through the relocate arc; `eval_node_relocations`
//!   composes the source as a nested sub-index where variants are deferred, so a
//!   variant-gated source opinion is missed. Cross-arc implied relocations (C++
//!   `_EvalImpliedRelocations`'s graft) are likewise unported
//!   (`eval_implied_relocations`'s `TODO(relocates)`).
//! - `timeCodesPerSecond`-derived layer-offset scaling (spec 12.x), residual
//!   implied/nested-class ordering, and prototype-redirection in the instancing
//!   dump.
//!
//! ## Permissions (`permission = private`)
//!
//! A *direct* arc (a reference/inherit/payload/specialize authored at the prim)
//! to a private target is denied: every node reached through it is marked
//! [`NodeFlags::PERMISSION_DENIED`] so it stops contributing to value
//! resolution while staying visible structurally, and the denial is reported as
//! [`Error::ArcPermissionDenied`] (C++ `_AddArc` + `_InertSubtree`). The denied
//! target paths flow down the `CompositionContext` so descendant prims composed
//! separately (where the arc is *extended*, not authored) are inerted too. One
//! piece is still missing:
//!
//! - Connection / relationship-target validity. A connection or
//!   relationship target pointing at a site private relative to where the
//!   target is authored is invalid and must be dropped (C++
//!   `_EnforcePermissions` plus connection/target validation). This needs a
//!   value-resolution surface for target validity and is its own multi-commit
//!   effort. `NodeFlags::PERMISSION_PRIVATE` / `RESTRICTED` are reserved for it.
//!
//! ## Ordered prim children — relocates during the fold
//!
//! Child names fold weakest-to-strongest with `primOrder` reapplied per layer
//! (mirroring C++ `PcpComposeSiteChildNames`). Composed *opinions* now apply
//! relocates during the build (the builder's relocate arcs), but the child-name
//! list still applies them once *after* the fold (`Cache::prim_children` →
//! `Relocates::apply_relocates_to_children`) rather than per layer stack during
//! it, so a scene combining multi-sublayer `primOrder` with relocates can order
//! children differently from C++. Folding relocates into the per-node child-name
//! merge is the remaining piece.
//!
//! ## Structural specializes
//!
//! Specializes global weakness (spec 10.4.1) is realized by copying specializes
//! nodes under the local root (C++ `_PropagateNodeToRoot`, the builder's
//! `propagate_node_to_root`): specialize is the weakest arc, so
//! `finalize_strength_order`'s plain DFS already places the globally-weak band
//! last and orders it with the faithful `PcpCompareSiblingNodeStrength`.
//!
//! ## Lower-priority / opportunistic
//!
//! - Cross-prim parallelism. `Cache::ensure_index` composes prims one at a
//!   time; each build is a pure function of `&LayerStack`, the parent context,
//!   and the cached indices, so sibling prims could compose in parallel (see
//!   the `TODO(rayon)`). The blocker is the shared `indices` map that
//!   inherit/specialize targets read mid-build — it needs a concurrent map or a
//!   targets-first build order. The [`PrimIndex`] is already `Send + Sync`;
//!   keep it so.
//! - Materialize empty inherit / specialize / variant targets as culled nodes.
//!   Only empty external reference/payload targets are materialized today; an
//!   editor that wants those class/variant arcs visible would need the same
//!   treatment for them.
//! - Finer-grained change classification. `Changes::did_change` collapses the
//!   prim and spec tiers into the significant tier (drop the index and every
//!   descendant). A finer split would rebuild less on a local edit.
//!
//! See <https://openusd.org/release/glossary.html#livrps-strength-ordering>

pub(crate) mod builder;
pub(crate) mod cache;
pub(crate) mod change;
pub(crate) mod clip;
pub(crate) mod deps;
pub(crate) mod graph;
pub(crate) mod index;
mod mapping;
mod rel;
pub(crate) mod resolve;

use std::collections::{HashMap, HashSet};

use crate::ar::Resolver;
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, AbstractData, Path, Value};

pub(crate) use cache::Cache;
pub(crate) use change::Changes;
pub use change::{CacheChanges, LayerStackChanges};
pub use graph::{ArcType, Node, NodeFlags, NodeId};
pub use index::PrimIndex;
pub use mapping::MapFunction;

/// Maps variant set names to ordered lists of fallback selections.
///
/// When a prim has a variant set but no authored selection, the composition
/// engine tries each fallback in order; a set with no applicable fallback stays
/// unselected.
///
/// This is the Rust equivalent of C++ `PcpVariantFallbackMap`.
///
/// # Example
///
/// ```
/// use openusd::pcp::VariantFallbackMap;
///
/// let fallbacks = VariantFallbackMap::new()
///     .add("shadingComplexity", ["full", "simple"])
///     .add("renderQuality", ["high", "medium", "low"]);
/// ```
#[derive(Debug, Clone, Default)]
pub struct VariantFallbackMap(HashMap<String, Vec<String>>);

impl VariantFallbackMap {
    /// Creates an empty variant fallback map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds fallback selections for a variant set.
    ///
    /// The selections are tried in order — the first one matching an existing
    /// variant in the set is used.
    pub fn add(mut self, set_name: impl Into<String>, selections: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.0
            .insert(set_name.into(), selections.into_iter().map(Into::into).collect());
        self
    }

    /// Returns the fallback selections for a variant set.
    ///
    /// Returns an empty slice if no fallbacks are registered for the set.
    pub fn get(&self, set_name: &str) -> &[String] {
        self.0.get(set_name).map(Vec::as_slice).unwrap_or_default()
    }

    /// Returns `true` if no fallbacks have been registered.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Precomputed sublayer stacks, keyed by root layer index.
///
/// Each entry maps a root layer to its full sublayer stack. Each entry pairs
/// a layer index with the effective layer offset for that layer relative to
/// the stack's root (composed through nested sublayers per spec 10.3.1.1).
/// The stack root itself has [`sdf::LayerOffset::IDENTITY`].
pub(crate) type SublayerStacks = HashMap<usize, Vec<(usize, sdf::LayerOffset)>>;

/// Loaded layers with precomputed sublayer ordering.
///
/// Bundles the layers (each carrying its own identifier and data) with the
/// precomputed sublayer stacks into a single unit passed through the
/// composition engine. Corresponds to a simplified C++ `PcpLayerStack`.
pub(crate) struct LayerStack {
    /// Layers in strength order (session layers first, then root layer).
    /// Each [`sdf::Layer`] bundles its resolved identifier and backing data.
    pub layers: Vec<sdf::Layer>,
    /// Precomputed sublayer stacks keyed by root layer index.
    pub sublayer_stacks: SublayerStacks,
    /// Number of session layers at the front of the layer stack.
    pub session_layer_count: usize,
    /// Whether payload arcs should be expanded during prim index construction.
    pub load_payloads: bool,
    /// Whether any layer authors `layerRelocates`, precomputed once for the
    /// stack. The builder reads this to gate its relocate passes
    /// (`eval_node_relocations` and the prohibited-prim elision) without
    /// rescanning every layer per prim.
    pub(crate) has_relocates: bool,
    /// Per-layer authored `layerRelocates` pairs `(source, target)` in that
    /// layer's own namespace, keyed by layer index; empty when no layer
    /// relocates. The task-queue builder reads these to compose relocate arcs in
    /// a node's layer stack (C++ `PcpLayerStack::GetIncrementalRelocates*`).
    pub(crate) layer_relocates: HashMap<usize, Vec<(Path, Path)>>,
    /// Resolver used to anchor relative asset paths when locating layers.
    pub(crate) resolver: Box<dyn Resolver>,
}

impl LayerStack {
    /// Creates a new layer stack, precomputing sublayer ordering.
    pub fn new(
        layers: Vec<sdf::Layer>,
        session_layer_count: usize,
        resolver: Box<dyn Resolver>,
        load_payloads: bool,
    ) -> Self {
        let sublayer_stacks: SublayerStacks = (0..layers.len())
            .map(|i| (i, Self::build_sublayer_stack(i, &layers, &*resolver)))
            .collect();
        let has_relocates = Self::compute_has_relocates(&layers);
        let layer_relocates = rel::extract_layer_relocates(&layers);
        Self {
            layers,
            sublayer_stacks,
            session_layer_count,
            load_payloads,
            has_relocates,
            layer_relocates,
            resolver,
        }
    }

    /// Returns the relocation source for `target` if a layer in `ambient`
    /// relocates a prim onto it (C++ `GetIncrementalRelocatesTargetToSource`,
    /// the as-authored pairs without chaining). The strongest layer (earliest in
    /// `ambient`) wins a collision; a deletion (`</Src>: <>`, empty target)
    /// relocate has no target to key on and is skipped. The C++ memoized map is
    /// not materialized — the layers are scanned per query.
    // TODO(perf): memoize the incremental relocates per layer stack (C++
    // `PcpLayerStack`) instead of rescanning per query.
    pub(crate) fn relocation_source(&self, ambient: &[(usize, sdf::LayerOffset)], target: &Path) -> Option<Path> {
        for &(layer, _) in ambient {
            let Some(pairs) = self.layer_relocates.get(&layer) else {
                continue;
            };
            if let Some((source, _)) = pairs.iter().find(|(_, t)| !t.is_empty() && t == target) {
                return Some(source.clone());
            }
        }
        None
    }

    /// Builds the relocation [`MapFunction`] applying at `path` in the layer
    /// stack `ambient` (C++ `PcpLayerStack::GetExpressionForRelocatesAtPath` and
    /// `_FilterRelocationsForPath`): every relocate whose source lies at or below
    /// `path`, chained so a relocated prim that is itself relocated reaches its
    /// final target, plus the `(/, /)` identity catch-all. Returns `None` when no
    /// relocate affects `path`.
    ///
    /// Composition arcs fold this onto their map (C++ `_CreateMapExpressionForArc`)
    /// so opinions brought in across the arc land at their post-relocation paths.
    ///
    /// `exclude_source` drops the relocate whose source is exactly that path. A
    /// relocate-source sub-index passes its own root: the relocation that moves
    /// the source is applied by the relocate arc node's own map when the
    /// sub-index is grafted, not by the source's own internal arcs.
    ///
    // TODO(perf): the relocate chain is recomputed per arc here (via
    // `combined_relocates`) and per query in `rel::Relocates`. C++ memoizes the
    // combined/incremental relocates on `PcpLayerStack`; cache them per layer
    // stack instead of rescanning on every fold.
    pub(crate) fn relocates_expression_at(
        &self,
        ambient: &[(usize, sdf::LayerOffset)],
        path: &Path,
        exclude_source: Option<&Path>,
    ) -> Option<MapFunction> {
        let mut pairs: Vec<(Path, Path)> = self
            .combined_relocates(ambient)
            .into_iter()
            .filter(|(source, target)| !target.is_empty() && source.has_prefix(path) && Some(source) != exclude_source)
            .collect();
        if pairs.is_empty() {
            return None;
        }
        pairs.push((Path::abs_root(), Path::abs_root()));
        Some(MapFunction::new(pairs))
    }

    /// Chains the per-layer authored relocates of `ambient` into a single
    /// source→target map (C++ `PcpLayerStack::GetRelocatesSourceToTarget`): the
    /// strongest layer wins a duplicate source, and a target that is itself a
    /// relocation source is followed to the final target.
    fn combined_relocates(&self, ambient: &[(usize, sdf::LayerOffset)]) -> Vec<(Path, Path)> {
        let mut pairs: Vec<(Path, Path)> = Vec::new();
        for &(layer, _) in ambient {
            let Some(layer_pairs) = self.layer_relocates.get(&layer) else {
                continue;
            };
            for (source, target) in layer_pairs {
                if !pairs.iter().any(|(s, _)| s == source) {
                    pairs.push((source.clone(), target.clone()));
                }
            }
        }
        // Follow chains: a target that is itself relocated (at or below another
        // relocate's source) maps onward to its final location.
        let snapshot = pairs.clone();
        for (source, target) in pairs.iter_mut() {
            if target.is_empty() {
                continue;
            }
            *target = rel::chain_through_relocates(target, &snapshot, Some(source));
        }
        pairs
    }

    /// Whether a layer in `ambient` authors a relocate whose SOURCE is `source`
    /// (the incremental source→target direction's key test, used for the
    /// salted-earth prohibition). Includes deletion (empty-target) relocates:
    /// their source is still a prohibited relocation source.
    pub(crate) fn is_relocation_source(&self, ambient: &[(usize, sdf::LayerOffset)], source: &Path) -> bool {
        ambient.iter().any(|&(layer, _)| {
            self.layer_relocates
                .get(&layer)
                .is_some_and(|pairs| pairs.iter().any(|(s, _)| s == source))
        })
    }

    /// Re-derives the cached relocate state — [`has_relocates`](Self::has_relocates)
    /// and [`layer_relocates`](Self::layer_relocates) — from the current layers.
    /// Called after a `layerRelocates` edit that does not rebuild the sublayer
    /// precomputation (which would refresh both itself); keeping them in sync is
    /// what re-enables and re-targets the builder's relocate passes.
    pub(crate) fn recompute_relocate_data(&mut self) {
        self.has_relocates = Self::compute_has_relocates(&self.layers);
        self.layer_relocates = rel::extract_layer_relocates(&self.layers);
    }

    /// Whether any layer authors `layerRelocates` at its pseudo-root.
    fn compute_has_relocates(layers: &[sdf::Layer]) -> bool {
        let root = sdf::Path::abs_root();
        layers.iter().any(|l| {
            l.data()
                .has_field(&root, sdf::schema::FieldKey::LayerRelocates.as_str())
        })
    }

    /// Returns the number of layers.
    pub fn len(&self) -> usize {
        self.layers.len()
    }

    /// Returns `true` if there are no layers.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.layers.is_empty()
    }

    /// Returns the layer at the given index.
    pub fn layer(&self, index: usize) -> &sdf::Layer {
        &self.layers[index]
    }

    /// Mutable access to a layer in the stack, for authoring writes routed
    /// through [`Cache::layer_mut`]. Returns `None` for an out-of-range index.
    /// Callers route invalidation through
    /// [`change::Changes::apply`](super::change::Changes::apply) so only the
    /// affected prim indices are dropped.
    fn layer_mut(&mut self, index: usize) -> Option<&mut sdf::Layer> {
        self.layers.get_mut(index)
    }

    /// Recompute the precomputed `sublayer_stacks` map from the current layers.
    /// Used by
    /// [`Cache::recompute_layer_stack`](super::cache::Cache::recompute_layer_stack)
    /// after authoring touched `subLayers` / `subLayerOffsets`.
    fn calc_precomputed(&mut self) {
        self.sublayer_stacks = (0..self.layers.len())
            .map(|i| (i, Self::build_sublayer_stack(i, &self.layers, &*self.resolver)))
            .collect();
        self.recompute_relocate_data();
    }

    /// Returns the root layer (the first non-session layer), if any.
    ///
    /// Per spec 12.2.7, layer metadata authored on the pseudo-root resolves
    /// from this layer only and does not compose with sublayers or arcs.
    pub fn root_layer(&self) -> Option<&sdf::Layer> {
        self.layers.get(self.session_layer_count)
    }

    /// Assembles the stage's root layer stack: the session layers (identity
    /// offset) followed by the root layer and its sublayers with their
    /// effective offsets (spec 10.3.1). This is the set of layers a top-level
    /// prim index scans for local opinions; referenced layer stacks are reached
    /// only by following arcs.
    pub(crate) fn root_layer_stack(&self) -> Vec<(usize, sdf::LayerOffset)> {
        let mut stack = Vec::new();
        for i in 0..self.session_layer_count {
            stack.push((i, sdf::LayerOffset::IDENTITY));
        }
        let root = self.session_layer_count;
        if let Some(sublayers) = self.sublayer_stacks.get(&root) {
            stack.extend_from_slice(sublayers);
        }
        stack
    }

    /// Returns the layer identifier at the given index.
    pub fn identifier(&self, index: usize) -> &str {
        &self.layers[index].identifier
    }

    /// Returns the layer indices + effective offsets for a sublayer stack
    /// rooted at `root_layer`. Each entry's offset is composed from the
    /// root through all nested sublayers per spec 10.3.1.1.
    ///
    /// The walk is depth-first pre-order — a layer is emitted before its own
    /// sublayers and before its later siblings — matching C++
    /// `PcpLayerStack::_BuildLayerStack`, so a nested sublayer is stronger than
    /// the next sibling at the parent level. The same layer may appear more than
    /// once (a diamond of sublayers); only a layer that sublayers itself,
    /// directly or transitively, is a cycle and is skipped. Cycle detection is
    /// therefore over the current ancestor chain, not every layer seen.
    /// The sublayer stack for `root_layer`: the stack's precomputed one when
    /// present, else freshly built. TODO(perf): the cache hit clones the stored
    /// `Vec`; returning a `Cow` would let callers borrow it.
    pub(crate) fn sublayer_stack(&self, root_layer: usize) -> Vec<(usize, sdf::LayerOffset)> {
        self.sublayer_stacks
            .get(&root_layer)
            .cloned()
            .unwrap_or_else(|| Self::build_sublayer_stack(root_layer, &self.layers, &*self.resolver))
    }

    pub(crate) fn build_sublayer_stack(
        root_layer: usize,
        layers: &[sdf::Layer],
        resolver: &dyn Resolver,
    ) -> Vec<(usize, sdf::LayerOffset)> {
        let mut stack: Vec<(usize, sdf::LayerOffset)> = Vec::new();
        let mut ancestors: HashSet<usize> = HashSet::new();
        Self::collect_sublayers(
            root_layer,
            sdf::LayerOffset::IDENTITY,
            layers,
            resolver,
            &mut stack,
            &mut ancestors,
        );
        stack
    }

    /// Appends `idx` and its sublayer subtree to `stack` in depth-first
    /// pre-order. `ancestors` holds the layers on the path from the root to
    /// `idx`; a sublayer already on that path is a cycle (C++
    /// `PcpErrorSublayerCycle`) and is skipped, while a layer reached off the
    /// path is a permitted duplicate and is expanded again.
    fn collect_sublayers(
        idx: usize,
        effective: sdf::LayerOffset,
        layers: &[sdf::Layer],
        resolver: &dyn Resolver,
        stack: &mut Vec<(usize, sdf::LayerOffset)>,
        ancestors: &mut HashSet<usize>,
    ) {
        stack.push((idx, effective));
        ancestors.insert(idx);

        let root = Path::abs_root();
        if let Ok(Value::StringVec(sub_paths)) = layers[idx]
            .get(&root, FieldKey::SubLayers.as_str())
            .map(|v| v.into_owned())
        {
            // Offsets live in a parallel field; missing entries fall back to
            // the identity offset per spec 16.2.18.3.
            let offsets: Vec<sdf::LayerOffset> = layers[idx]
                .get(&root, FieldKey::SubLayerOffsets.as_str())
                .ok()
                .and_then(|v| match v.into_owned() {
                    Value::LayerOffsetVec(v) => Some(v),
                    _ => None,
                })
                .unwrap_or_default();

            for (i, sub_path) in sub_paths.into_iter().enumerate() {
                let Some(sub_idx) = index::find_layer(&sub_path, layers, resolver) else {
                    continue;
                };
                if ancestors.contains(&sub_idx) {
                    continue;
                }
                let local = offsets.get(i).copied().unwrap_or_default().sanitized();
                let child = effective.concatenate(&local);
                Self::collect_sublayers(sub_idx, child, layers, resolver, stack, ancestors);
            }
        }

        ancestors.remove(&idx);
    }
}

/// An error encountered while building a [`PrimIndex`](index::PrimIndex).
///
/// These errors represent recoverable composition failures — a missing
/// layer or invalid metadata does not have to be fatal. The error handler
/// provided via [`StageBuilder::on_error`](crate::usd::StageBuilder::on_error)
/// decides whether to skip the broken arc and continue, or abort.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// A composition arc cycle was detected.
    #[error("composition arc cycle at {path} (depth {depth})")]
    ArcCycle {
        /// The prim path where the cycle was detected.
        path: Path,
        /// Recursion depth when the cycle was detected.
        depth: usize,
    },

    /// A layer referenced by a composition arc was not found among loaded layers.
    #[error("unresolved {arc:?} layer @{asset_path}@ at {site_path}")]
    UnresolvedLayer {
        /// The asset path that could not be matched.
        asset_path: String,
        /// The composition arc type that introduced this dependency.
        arc: ArcType,
        /// The prim path where the arc was authored.
        site_path: Path,
    },

    /// An external reference/payload targets a layer without specifying a prim
    /// path, but the target layer has no `defaultPrim` metadata.
    #[error("{arc:?} target @{layer_id}@ has no defaultPrim (at {site_path})")]
    MissingDefaultPrim {
        /// Identifier of the target layer.
        layer_id: String,
        /// The composition arc type.
        arc: ArcType,
        /// The prim path where the arc was authored.
        site_path: Path,
    },

    /// The `defaultPrim` metadata on a target layer has an invalid or
    /// unexpected value.
    #[error("{arc:?} target @{layer_id}@ has invalid defaultPrim (at {site_path})")]
    InvalidDefaultPrim {
        /// Identifier of the target layer.
        layer_id: String,
        /// The composition arc type.
        arc: ArcType,
        /// The prim path where the arc was authored.
        site_path: Path,
    },

    /// A direct composition arc (a reference/inherit/payload/specialize
    /// authored at the prim) targets a site whose composed permission is
    /// `private` (spec 10.3.3). C++ records `PcpErrorArcPermissionDenied`; the
    /// arc is reported but the node is retained, so this is recoverable.
    #[error("{arc:?} arc at {site_path} targets private site {target_path}")]
    ArcPermissionDenied {
        /// The prim where the arc is authored.
        site_path: Path,
        /// The composition arc type.
        arc: ArcType,
        /// The private site the arc targets.
        target_path: Path,
    },

    /// Unexpected internal failure surfaced during composition (typically I/O
    /// or value-decoding errors from the underlying layer data).
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;

    fn layer(id: &str, text: &str) -> sdf::Layer {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        sdf::Layer::new(id, Box::new(crate::usda::TextReader::from_data(data)))
    }

    /// `recompute_relocate_data` re-derives both the cached flag and the
    /// per-layer relocate pairs from the current layers. A `layerRelocates` edit
    /// reaches the stack through `Cache::recompute_relocates`, which does not
    /// rebuild the sublayer precomputation, so both must be refreshed there or
    /// the builder keeps reading stale relocate state.
    #[test]
    fn recompute_relocate_data_syncs() {
        let plain = layer("root.usd", "#usda 1.0\ndef \"A\" {}\n");
        let mut stack = LayerStack::new(vec![plain], 0, Box::new(DefaultResolver::new()), true);
        assert!(!stack.has_relocates, "a stack with no layerRelocates starts clear");
        assert!(stack.layer_relocates.is_empty(), "no relocate pairs to start");

        // Author layerRelocates onto the layer (as an in-place edit would) and
        // refresh the state the way `recompute_relocates` now does.
        stack.layers[0] = layer(
            "root.usd",
            "#usda 1.0\n(\n    relocates = { </A>: </B> }\n)\ndef \"A\" {}\n",
        );
        stack.recompute_relocate_data();
        assert!(
            stack.has_relocates,
            "recompute picks up the newly authored layerRelocates"
        );
        assert_eq!(
            stack.relocation_source(&[(0, sdf::LayerOffset::default())], &Path::new("/B").unwrap()),
            Some(Path::new("/A").unwrap()),
            "recompute re-extracts the per-layer relocate pairs the builder reads"
        );
    }
}
