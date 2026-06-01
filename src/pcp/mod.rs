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
//! | `index` | `PcpPrimIndex` | Per-prim composition tree: an arena-backed, single-rooted tree of [`Node`]s with parent/child and origin links, plus a strength-order projection. |
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
//! the set is used; if none match, the first variant in the set is the default.
//! Authored selections always take priority over fallbacks.
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
//! The engine covers LIVRPS, value resolution, relocates, variants,
//! instancing, value clips, and surgical invalidation. The sections below
//! document the known gaps and current limits.
//!
//! ## Permissions (`permission = private`)
//!
//! A *direct* arc (a reference/inherit/payload/specialize authored at the prim)
//! to a private target is denied: its node subtree is marked
//! [`NodeFlags::PERMISSION_DENIED`] so it stops contributing to value
//! resolution while staying visible structurally, and the denial is reported as
//! [`Error::ArcPermissionDenied`] (C++ `_AddArc` + `_InertSubtree`). Two pieces
//! are still missing:
//!
//! - Descendant propagation. The inerting in `Cache::ensure_index` marks only
//!   the arc's subtree *within the prim's own index*. A private target's
//!   children that compose as separate descendant prims — where the arc is
//!   *extended* to the descendant rather than authored there, so the per-prim
//!   detector does not match it — are not inerted. The fix is to carry the
//!   denial down the lazy per-prim builds, e.g. on the `CompositionContext`.
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
//! (mirroring C++ `PcpComposeSiteChildNames`). Relocates are still applied once
//! *after* the fold rather than per layer stack *during* it, so a scene that
//! combines multi-sublayer `primOrder` with relocates can order children
//! differently from C++. Folding relocates into the per-node merge is the
//! remaining piece, intertwined with the relocates-in-build work below.
//!
//! ## Relocates composed during the build
//!
//! Relocate nodes are grafted *after* the build and spliced into the finalized
//! strength projection (`Cache` → `Relocates`, `splice_relocate`), bypassing
//! the DFS and the strength comparator. A unified model would compose relocates
//! *during* the build so the DFS orders them like any other arc and the splice
//! can be deleted. This is intertwined with relocate source-resolution in the
//! `rel` module and is a multi-commit effort; the relocate compliance tests are
//! the guard. No observable change is intended.
//!
//! ## Structural specializes
//!
//! Specializes global weakness (spec 10.4.1) is realized in the *projection*:
//! `finalize_strength_order` appends specialize-flagged nodes as a globally-weak
//! band, and `compute_specialize_chain_depths` recovers each node's chain
//! position with a per-path-maximum heuristic. The *tree* still nests specialize
//! subtrees where they were composed; C++ `_EvalImpliedSpecializes` physically
//! copies them to be children of the root. Re-parenting specialize subtree roots
//! to the synthetic root on the final index would let the plain DFS place them
//! at the weak end (dropping the projection's specialize partition) and let the
//! chain depth be read straight from the parent chain (dropping the heuristic).
//! The catch: the cache hands out a stored index as a graft source, so
//! re-parenting it in place would flatten nesting downstream — this needs care
//! to apply only to indices that will not be grafted. No observable change is
//! intended.
//!
//! ## Compliance coverage against the reference `pcp.txt` dumps
//!
//! The vendor composition suite ships a `pcp.txt` baseline per asset
//! (`vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/*/`)
//! that records the fully composed result — prim stack, property stacks, child
//! names, variant selections, and reported errors. Today the integration suite
//! checks prim/property/child *existence* through the `Stage`, and only a
//! handful of `pcp::index` tests assert exact node order against these dumps.
//! A harness that parses every `pcp.txt` and diffs the composed prim stack /
//! property stack / child-name order / variant selections against it would turn
//! these baselines into a systematic compliance gate, catching ordering,
//! permission, and strength regressions the existence checks miss.
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

pub(crate) mod cache;
pub(crate) mod change;
pub(crate) mod clip;
pub(crate) mod deps;
pub(crate) mod index;
mod mapping;
mod rel;

use std::collections::{HashMap, HashSet, VecDeque};

use crate::ar::Resolver;
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, AbstractData, Path, Value};

pub(crate) use cache::Cache;
pub(crate) use change::Changes;
pub use change::{CacheChanges, LayerStackChanges};
pub use index::{ArcType, Node, NodeFlags, NodeId, PrimIndex};
pub use mapping::MapFunction;

/// Maps variant set names to ordered lists of fallback selections.
///
/// When a prim has a variant set but no authored selection, the composition
/// engine tries each fallback in order before falling back to the first
/// variant defined in the set.
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
        Self {
            layers,
            sublayer_stacks,
            session_layer_count,
            load_payloads,
            resolver,
        }
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
        let mut seen = HashSet::new();
        let mut stack = Vec::new();
        for i in 0..self.session_layer_count {
            stack.push((i, sdf::LayerOffset::IDENTITY));
            seen.insert(i);
        }
        let root = self.session_layer_count;
        if let Some(sublayers) = self.sublayer_stacks.get(&root) {
            for &(i, offset) in sublayers {
                if seen.insert(i) {
                    stack.push((i, offset));
                }
            }
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
    pub(crate) fn build_sublayer_stack(
        root_layer: usize,
        layers: &[sdf::Layer],
        resolver: &dyn Resolver,
    ) -> Vec<(usize, sdf::LayerOffset)> {
        let mut stack: Vec<(usize, sdf::LayerOffset)> = vec![(root_layer, sdf::LayerOffset::IDENTITY)];
        let mut seen: HashSet<usize> = HashSet::new();
        seen.insert(root_layer);
        // BFS so offsets compose with their direct parent sublayer.
        let mut queue: VecDeque<(usize, sdf::LayerOffset)> = VecDeque::new();
        queue.push_back((root_layer, sdf::LayerOffset::IDENTITY));

        while let Some((idx, parent_effective)) = queue.pop_front() {
            let root = Path::abs_root();
            let Ok(value) = layers[idx].get(&root, FieldKey::SubLayers.as_str()) else {
                continue;
            };
            let Value::StringVec(sub_paths) = value.into_owned() else {
                continue;
            };

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
                if !seen.insert(sub_idx) {
                    continue;
                }
                let local = offsets.get(i).copied().unwrap_or_default().sanitized();
                let effective = parent_effective.concatenate(&local);
                stack.push((sub_idx, effective));
                queue.push_back((sub_idx, effective));
            }
        }

        stack
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
