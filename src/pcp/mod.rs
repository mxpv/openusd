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
//! underlying layers. They are split between the indexer and the cache:
//!
//! - `layerRelocates` are extracted from each layer's pseudoroot at
//!   construction and mapped into the composed namespace through each
//!   layer's namespace mapping.
//! - When composing a prim that is a relocate target, the indexer
//!   (`eval_node_relocations`) finds the pre-relocation source path, composes
//!   it as a sub-index, and grafts the result as a `Relocate` arc node. Each
//!   grafted node carries the source site's full layer stack, so a relocate
//!   source spanning several sublayers keeps every member, not just the
//!   strongest.
//! - Child names are folded per composition node: each node's layer-stack
//!   relocates (chained within the layer stack) rename, remove, or add direct
//!   children, and every relocation source becomes a prohibited name
//!   (`IndexCache::compute_prim_child_names` → `relocates::apply_child_relocates`).
//!
//! # Module structure
//!
//! | Item | C++ equivalent | Description |
//! |------|---------------|-------------|
//! | `layer_graph` | `PcpLayerStack` | The loaded layers and their sublayer DAG, keyed by the graph-minted [`LayerId`] handle (physical layer storage). Owns the composed-stack registry (`layer_stack`). Owned by [`Stage`](crate::usd::Stage), passed to each build by shared reference. Sublayer edges are always derived from `subLayers` metadata, the single source of truth. |
//! | `layer_stack` | `PcpLayerStack` identity | Composed-stack identity ([`LayerStackId`]) and the registry of source-keyed instances (`LayerStackRegistry`): a [`LayerId`] names a physical layer, a [`LayerStackId`] a composed view under an expression-variable override source (`VarsSource`, the C++ `PcpExpressionVariablesSource`), so a `${VAR}` sublayer reached from two var-authoring sources resolves independently. |
//! | `index_cache` | `PcpCache` | Lazily-built composition cache (`IndexCache`). Main interface for [`Stage`](crate::usd::Stage). Borrows the `layer_graph` per query. |
//! | `instancing` | `Pcp` instancing | Scene-graph instancing (spec 11.3.3): the `PrototypeRegistry` object (owned by `IndexCache`) plus the composition glue (`is_instance`, the `effective_path` redirection that maps an instance proxy's subtree onto the shared `/__Prototype_N` namespace) as a second `IndexCache` impl. |
//! | [`Error`] | `PcpErrorBase` | Composition errors: arc cycles, unresolved layers, missing/invalid `defaultPrim`. |
//! | `prim_index` | `PcpPrimIndex` | Per-prim composition support: the [`PrimIndex`] type with its build entry points (`build_with_cache` / `build_with_cache_in`) and the [`CompositionContext`](prim_index::CompositionContext) that flows parent-to-child. |
//! | `compose_site` | `PcpComposeSite` | Site field composition: the list-op primitives (`compose_references_in`, `collect_payloads_in`, `compose_arc_list_in`) the `prim_indexer` drives to read a node's arc fields across its layer stack, plus the asset-path anchoring and time-codes retiming they fold in. |
//! | `prim_indexer` | `Pcp_PrimIndexer` | Task-queue composition engine (`Indexer`): grows the graph node-by-node by draining a priority task queue. The sole composition path. |
//! | `prim_graph` | `PcpPrimIndex` / `PcpNodeRef` | Arena-backed `PrimIndexGraph` of [`Node`]s with parent/child and origin links, plus the strength-order projection. |
//! | `prim_resolve` | — | Value resolution over a composed [`PrimIndex`]: the per-field strength-ordered opinion walk (spec section 12). |
//! | `mapping` | `PcpMapFunction` | Namespace mapping between composition arcs — each [`Node`] carries `map_to_parent` and `map_to_root`. |
//! | [`VariantFallbackMap`] | `PcpVariantFallbackMap` | Maps variant set names to ordered fallback selections, used when no selection is authored. |
//! | `load_rules` | `UsdStageLoadRules` | Per-path payload-inclusion policy ([`LoadRules`]/[`Rule`]): nearest-ancestor-with-lookahead rule resolution, plus the `IndexCache` glue that turns a rule change into per-build payload-expansion decisions and bounded cache invalidation. |
//! | `relocates` | — | Stateless relocate free functions (effective relocates, transitive chaining, child-name folding). Layer-authored pairs and stack-effective queries are read from `LayerGraph`; all data is passed through parameters. |
//! | `dependencies` | `Pcp_Dependencies` | Reverse `(LayerId, site) → prim-index paths` map (`Dependencies`) driving surgical change fanout. |
//!
//! Layer loading lives in [`sdf::LayerRegistry`](crate::sdf::LayerRegistry); the
//! loaded layers and their sublayer DAG are held in [`layer_graph::LayerGraph`].
//!
//! # Architecture
//!
//! Each [`PrimIndex`](prim_index::PrimIndex) is an arena-backed, single-rooted tree
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
//! Composition is driven by a [`CompositionContext`](prim_index::CompositionContext)
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
//! The [`IndexCache`](index_cache::IndexCache) stores both the [`PrimIndex`](prim_index::PrimIndex)
//! and the [`CompositionContext`](prim_index::CompositionContext) for each composed
//! prim. During depth-first traversal, parents are always composed before
//! children, so the context chain is always populated. Each per-prim build
//! takes only shared references, making it suitable for future parallel
//! execution.
//!
//! Recoverable composition errors ([`Error`]) are retained by the cache and
//! exposed through [`Stage::composition_errors`](crate::usd::Stage::composition_errors).
//! Operational failures are returned to the caller.
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
//!    - Spec — graph topology is fine, only a spec stack changed. An inert spec
//!      add/remove rescans `has_specs` in place over the memoized per-node spec
//!      stack and keeps the index.
//!
//!    Layer-stack-tier flags (`subLayers`, sublayer offsets,
//!    `timeCodesPerSecond`, `expressionVariables`, `layerRelocates`,
//!    `defaultPrim`) recompose the affected layer stacks and drop only the
//!    indices that read them (`IndexCache::invalidate_layers`), not the whole
//!    cache.
//!
//! 3. [`Changes::apply`] surgically removes the affected entries from the
//!    cache. Indices rebuild lazily on next access.
//!
//! A reverse `(LayerId, site_path) → prim_index_paths` map (the
//! `Dependencies` table internal to the cache) makes step 2 cheap: every
//! [`PrimIndex`](prim_index::PrimIndex) registers its observed sites when it
//! finishes building, and the classifier looks up dependents — including
//! ancestors of the changed site, since an arc at `/Foo` makes `/Foo/Bar`'s
//! composition transitively dependent on `/Foo`.
//!
//! Property-tier authoring (attribute values, time samples) never invalidates
//! the prim graph: those queries read live layer data on every call. A
//! `targetPaths`/`connectionPaths` edit likewise leaves the graph intact,
//! clearing only the per-property resolved-target memo (keyed by path and
//! target kind) so resolved targets recompute on next read.
//!
//! Layer muting ([`Stage::mute_layer`](crate::usd::Stage::mute_layer) /
//! [`unmute_layer`](crate::usd::Stage::unmute_layer)) recomposes incrementally
//! rather than clearing the cache: the toggle drops only the indices whose
//! composition reads a layer stack containing the (un)muted layer.
//! `LayerGraph::mute_fanout` derives that layer set — the toggled layer, every
//! layer whose subtree contains it, and the root layer when the stage root
//! stack is touched — and `IndexCache`'s layer-muting drop evicts the indices a
//! node (or a recorded muted reference/payload target) ties to it.
//!
//! # Relationship and connection targets
//!
//! A relationship/connection target translates through the contributing node's
//! `map_to_root` ([`MapFunction`]) — the bidirectional invertibility check
//! ([`translate_to_target`](mapping::MapFunction::translate_to_target),
//! C++ `PcpMapFunction::_Map` / `PcpTranslatePathFromNodeToRoot`) and the
//! relocates folded into each arc map (C++ `_CreateMapExpressionForArc` /
//! `GetExpressionForRelocatesAtPath`), including nested relocate chains
//! (`LayerGraph::combined_relocates`) and the *block* a relocate to an
//! out-of-scope prim leaves in the composed map. There is no separate
//! relocate-chaining or escaped-source pass for resolved targets; the
//! deleted-path walk still chains through the prim's effective relocates because
//! it has no per-node origin.
//!
//! A relationship/connection authored in a class that targets a *different*
//! instance of that class is dropped with the "is authored in a class but refers
//! to an instance of that class" message (C++ `PcpErrorInvalidInstanceTargetPath`);
//! the *self* instance keeps the generic out-of-scope message, and a self target
//! reachable through the class's own relocates is kept at its pre-relocation path
//! (the invertibility check yields all three outcomes). The cross-prim "target
//! inherits the class" check (C++ `_TargetInClassAndTargetsInstance`) is
//! `IndexCache::compute_instance_targets`; the per-node target walk in
//! `resolve_path_list_op_validated` drops each invalid contribution from its own
//! node only, so a valid stronger opinion for the same path survives.
//!
//! # Permissions (`permission = private`)
//!
//! `permission` is `sdf`-level metadata only ([`sdf::Permission`]); composition
//! and value resolution never read it. C++'s own arc-, prim-, and
//! target-permission enforcement (`_AddArc`'s privacy check, `_EnforcePermissions`,
//! `_TargetIsPermitted`) is compiled out for `Usd`-mode `PcpCache`s — the mode
//! `UsdStage`, and therefore this crate, always uses — so a real stage never
//! denies an arc or filters a target on `permission`. This is a deliberate
//! parity choice, not a gap: editing `permission` is an ordinary metadata change
//! with no composition effect.
//!
//! # Ordered prim children
//!
//! Child names fold weakest-to-strongest with `primOrder` reapplied per layer
//! (mirroring C++ `PcpComposeSiteChildNames`). Relocates apply per node during
//! that fold (`IndexCache::compute_prim_child_names` → `relocates::apply_child_relocates`,
//! the port of C++ `_ComposePrimChildNamesAtNode`): at each node its layer
//! stack's relocates rename, remove, or add direct children — a renamed child
//! keeps the source's position — and every relocation source becomes a prohibited
//! name removed from the final order.
//!
//! # Structural specializes
//!
//! Specializes global weakness (spec 10.4.1) is realized by copying specializes
//! nodes under the local root (C++ `_PropagateNodeToRoot`, the indexer's
//! `propagate_node_to_root`): specialize is the weakest arc, so
//! `finalize_strength_order`'s plain DFS already places the globally-weak band
//! last and orders it with the C++ `PcpCompareSiblingNodeStrength` comparison.
//!
//! # Remaining work
//!
//! - Cross-prim parallelism: `IndexCache::ensure_index` composes prims serially.
//!   Each build is a pure function of `&LayerGraph`, the parent context, and the
//!   cached indices (`TODO(rayon)`), but the shared `indices` map that
//!   inherit/specialize targets read mid-build first needs a concurrent map or a
//!   targets-first build order. [`PrimIndex`] is already `Send + Sync`.
//! - Resolving `asset` values sourced from time samples or value clips:
//!   `IndexCache::value_at` evaluates expressions and anchors only
//!   default-sourced asset paths (filling their `evaluated_path` /
//!   `resolved_path`); a time-sample or clip value is returned unresolved
//!   because the resolvers do not surface the layer/node of the contributing
//!   sample.
//! - Surfacing asset-path expression failures during value resolution: a
//!   malformed or non-string expression in an `asset` value is dropped silently
//!   (`IndexCache::resolve_asset_path` returns it unevaluated), unlike a
//!   reference/payload arc, which records [`Error::InvalidExpression`]. Value
//!   resolution needs an error channel to report it.
//! - Releasing a muted layer's memory: `LayerGraph` keeps a muted layer's node
//!   interned so unmute is a rebuild; C++ drops its references. The node and its
//!   backing data are retained for the life of the graph.
//! - Muted sublayer diagnostics: the loader (`LayerRegistry::open_stack`) reports
//!   every missing/unreadable sublayer raw, unaware of muting; the stage reports
//!   only those a muted-aware check finds contributing
//!   (`LayerGraph::sublayer_error_contributes` over `effective_layers`, the members
//!   of every composed stack) and applies it at report time
//!   (`Stage::composition_errors`). The raw diagnostics are never discarded, and the
//!   effective set is a pure function of the muted set and the composed stacks — not
//!   of which prim indices are cached — so a diagnostic's visibility is
//!   deterministic: muting a branch suppresses it and unmuting restores it, for both
//!   the root layer stack and reference/payload target stacks, and it never flickers
//!   as the cache warms.
//!   Remaining — precise target-diagnostic liveness: a reference/payload target
//!   whose only arc becomes muted (the arc's authoring opinion is muted, but the
//!   target root itself is not) stays interned with a non-empty stack, so its own
//!   missing-sublayer diagnostic keeps reporting even though no unmuted arc reaches
//!   it — a conservative over-report. Resolving it precisely means attaching
//!   collection diagnostics to composition sites / stack instances so their
//!   visibility tracks index lifetime and recomposition, rather than deriving it
//!   from the composed-stack set.
//! - Masked cold prototype queries: a query on a `/__Prototype_N` path under a
//!   non-default population mask resolves to empty until an instance sharing
//!   that prototype has been composed (which registers the prototype). The
//!   registry is populated lazily as instances compose, and `Stage::mask_includes`
//!   cannot map a synthetic prototype path back to an instance to compose before
//!   the registry knows it, so a query that addresses the prototype namespace
//!   before any instance is touched reads the default. Reaching the prototype
//!   through an instance (`Prim::prototype`, or any instance-proxy query) first
//!   registers it, after which masked prototype-content queries (including those
//!   behind a lazily-loaded payload) resolve correctly.
//! - Runtime variable-selected sublayers: an `expressionVariables` edit (or a
//!   mute that exposes a different variable) on an already-composed stack's
//!   root — the session/stage root, or an interned reference/payload target —
//!   can newly select a `${VAR}` sublayer that was never opened. Recomposition
//!   re-resolves the stack's stored context and membership, but membership can
//!   only include layers already present in the graph, so the newly-selected
//!   layer stays out until something else loads it. The open-time paths load
//!   the initial selection (`StageBuilder::session_expression_variables` for
//!   the root stack, the load barrier's contextual open for a target), and a
//!   change that *removes* a variable drops the sublayer it selected; loading
//!   a newly-selected one at runtime needs an on-demand sublayer-load output
//!   from graph recomposition. The same gap covers two open-time shapes: a
//!   target that joined the graph through another stack (e.g. as a root-stack
//!   sublayer) and is then demanded under an empty context is not reopened
//!   (`LayerGraph::needs_contextual_open`), so a sublayer selected by its own
//!   variables stays unloaded; and the stage's own root layer is deliberately
//!   never reopened (it may be in-memory or carry unsaved edits), so a
//!   sublayer newly selected by a back-reference's carried context stays
//!   unloaded too.
//! - Reclaiming stale contextual stack instances: the registry is append-only,
//!   and a variable-source flip — a source stack's authored variables becoming
//!   a no-op under its seed, or ceasing to be one — re-keys the sources
//!   downstream arcs carry, so the old-keyed instance is never matched again,
//!   yet the rebuild keeps re-resolving it; a long editing session accretes
//!   registry memory and rebuild cost. A plain variable value edit strands
//!   nothing (the seed is read live from the source instance, so the keyed
//!   instance refreshes in place). Reclamation needs liveness tracking: cached
//!   prim-index nodes hold stable `LayerStackId`s, so an instance cannot be
//!   dropped while any index references it.
//!
//! See <https://openusd.org/release/glossary.html#livrps-strength-ordering>

use std::collections::HashMap;

pub(crate) mod change;
pub(crate) mod clip;
mod compose_site;
pub(crate) mod dependencies;
pub(crate) mod index_cache;
mod index_store;
pub(crate) mod instancing;
pub(crate) mod layer_graph;
pub(crate) mod layer_stack;
pub(crate) mod load_rules;
mod mapping;
pub(crate) mod prim_graph;
pub(crate) mod prim_index;
pub(crate) mod prim_indexer;
pub(crate) mod prim_resolve;
mod relocates;

use crate::sdf::schema::FieldKey;
use crate::sdf::{self, Path, Value};

pub(crate) use change::{Changes, LayerStackChanges};
pub(crate) use index_cache::{AttributeValueSource, IndexCache};
pub(crate) use layer_graph::{LayerGraph, MuteChange, StackIdentity};
pub use layer_graph::{LayerId, LayerStackIdentifier};
pub(crate) use layer_stack::LayerStackId;
pub use load_rules::{LoadRules, Rule};
pub use mapping::MapFunction;
pub use prim_graph::{ArcType, Node, NodeFlags, NodeId};
pub(crate) use prim_index::Demand;
pub use prim_index::PrimIndex;
pub(crate) use relocates::{analyze_relocate_occurrences, first_unrepresentable_relocate, BatchRelocate};

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

/// The effective time-codes-per-second of a layer for offset retiming (spec
/// 12.3.2): the authored `timeCodesPerSecond`, else `framesPerSecond`, else the
/// 24.0 default. When a sublayer or reference/payload target has a different
/// effective rate than the layer that introduces it, the arc retimes by
/// `introducing / target`, folded into the composed [`sdf::LayerOffset`]'s scale.
pub(crate) fn effective_time_codes_per_second(layer: &sdf::Layer) -> f64 {
    // Read directly from the layer's `AbstractData`: this must work for any
    // backend (text, crate, in-memory), whereas the `PseudoRootSpec` accessors
    // require the concrete in-memory `Data` backing a `Layer` may not have.
    let root = Path::abs_root();
    let read = |key: FieldKey| -> Option<f64> {
        match layer.data().try_field(&root, key.as_str()).ok()??.into_owned() {
            Value::Double(v) => Some(v),
            Value::Float(v) => Some(v as f64),
            _ => None,
        }
    };
    let rate = read(FieldKey::TimeCodesPerSecond)
        .or_else(|| read(FieldKey::FramesPerSecond))
        .unwrap_or(24.0);
    // A non-positive or non-finite authored rate is degenerate. Fall back to the
    // 24.0 default so the retiming ratio stays finite and positive: the sublayer
    // offset path folds this scale into the composed offset without re-running
    // `LayerOffset::sanitized` (the scale > 0 guard), so an `inf`/`NaN`/negative
    // rate here would otherwise corrupt downstream value resolution.
    if rate.is_finite() && rate > 0.0 {
        rate
    } else {
        24.0
    }
}

/// The kind of authored field a composition-time variable expression came
/// from (C++ `PcpErrorVariableExpressionError`'s context), carried by
/// [`Error::InvalidExpression`] to name the failing site in diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, strum::Display)]
#[strum(serialize_all = "lowercase")]
pub enum ExpressionContext {
    /// A reference's asset path.
    Reference,
    /// A payload's asset path.
    Payload,
    /// A variant selection.
    Variant,
}

/// An error encountered while building a [`PrimIndex`](prim_index::PrimIndex).
///
/// These errors represent composition diagnostics. Recoverable failures skip
/// the broken opinion and are retained by [`Stage`](crate::usd::Stage).
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// A composition arc cycle was detected (C++ `PcpErrorArcCycle`). The arc
    /// closing the cycle is dropped so the rest of the prim still composes;
    /// `.0.hops` is the chain of arcs from the composing prim to the cycle-closing
    /// (CANNOT) arc, for the diagnostic.
    #[error("composition arc cycle at {}", .0.composing)]
    ArcCycle(CycleChain),

    /// A layer referenced by a composition arc was not found among loaded layers
    /// (C++ "Could not open asset … for {arc}").
    #[error("unresolved {arc:?} layer @{asset_path}@ at {site_path}")]
    UnresolvedLayer {
        /// The asset path that could not be matched.
        asset_path: String,
        /// The composition arc type that introduced this dependency.
        arc: ArcType,
        /// Identifier of the layer that authored the arc.
        introduced_by: String,
        /// The prim path where the arc was authored.
        site_path: Path,
    },

    /// A reference/payload target resolved but its layer could not be read or
    /// parsed (C++ "could not open asset … for {arc}"). The arc is dropped while
    /// the rest of the prim still composes; `reason` carries the underlying
    /// read/parse failure, surfaced once the stage's load barrier records the
    /// target failed.
    #[error("malformed {arc:?} layer @{asset_path}@ at {site_path}: {reason}")]
    MalformedLayer {
        /// The asset path whose target layer could not be read.
        asset_path: String,
        /// The composition arc type that introduced this dependency.
        arc: ArcType,
        /// Identifier of the layer that authored the arc.
        introduced_by: String,
        /// The prim path where the arc was authored.
        site_path: Path,
        /// The underlying read or parse error.
        reason: String,
    },

    /// A reference or payload targets a muted layer (C++ `PcpErrorMutedAssetPath`).
    /// A muted target contributes no opinions, so the arc is dropped while the rest
    /// of the prim still composes. Recorded whether or not the target was ever
    /// loaded.
    #[error("muted {arc:?} layer @{asset_path}@ at {site_path}")]
    MutedAssetPath {
        /// The asset path naming the muted target, anchored to its authoring layer.
        asset_path: String,
        /// The composition arc type that introduced this dependency.
        arc: ArcType,
        /// Identifier of the layer that authored the arc.
        introduced_by: String,
        /// The prim path where the arc was authored.
        site_path: Path,
    },

    /// A reference/payload resolved its target layer, but the named prim path
    /// authors no spec there (C++ `PcpErrorUnresolvedPrimPath`). The arc is
    /// dropped while the rest of the prim still composes.
    #[error("unresolved {arc:?} prim path @{target_layer}@<{prim_path}> at {site_path}")]
    UnresolvedPrimPath {
        /// The composition arc type.
        arc: ArcType,
        /// Identifier of the resolved target layer that lacks the prim.
        target_layer: String,
        /// The prim path that authors no spec in the target layer.
        prim_path: Path,
        /// Identifier of the layer that authored the arc.
        introduced_by: String,
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

    /// A composition-time variable expression failed to parse or did not
    /// evaluate to a string (C++ `PcpErrorVariableExpressionError`); the
    /// [`context`](Self::InvalidExpression::context) field names the kind of
    /// opinion that carried it. The opinion is skipped and the rest of the
    /// prim still composes, so this is recoverable.
    #[error("invalid {context} expression {expression} in {source_layer} at {site_path}: {message}")]
    InvalidExpression {
        /// The raw, unevaluated backtick expression.
        expression: String,
        /// The kind of authored field the expression came from.
        context: ExpressionContext,
        /// Identifier of the layer that authored the expression.
        source_layer: String,
        /// The prim path where the expression was authored.
        site_path: Path,
        /// The parse or evaluation failure.
        message: String,
    },

    /// A composition arc (inherit/specialize/reference/payload/relocate) targets
    /// a prim that is the source of a relocation — a prohibited child of its
    /// parent (C++ `PcpErrorArcToProhibitedChild`): allowing it would resurrect the
    /// opinions the relocation moved away. The arc is dropped. Reported while
    /// composing the prim that authored the arc (`composing`, stamped by the
    /// cache).
    #[error("{arc:?} at {site} targets prohibited relocation source {target}")]
    ProhibitedRelocationSource {
        /// The composition arc type.
        arc: ArcType,
        /// The prim that authored the arc.
        site: Path,
        /// Identifier of the layer that authored the arc.
        site_layer: String,
        /// The prohibited arc target.
        target: Path,
        /// Identifier of the layer containing the target.
        target_layer: String,
        /// The relocation source making the target prohibited.
        reloc_source: Path,
        /// Identifier of the layer authoring the relocation.
        reloc_layer: String,
        /// The prim being composed when the arc was followed.
        composing: Path,
    },

    /// A relationship target or attribute connection authored across a
    /// composition arc names a path outside that arc's namespace scope (C++
    /// `PcpErrorInvalidExternalTargetPath`). The target cannot translate through
    /// the arc, so it is dropped. Reported while composing the owning prim.
    #[error("invalid external target {target} on {property}")]
    InvalidExternalTargetPath {
        /// Whether this is an attribute connection.
        is_connection: bool,
        /// The dropped target path.
        target: Path,
        /// The owning property path.
        property: Path,
        /// Identifier of the authoring layer.
        layer: String,
        /// The composition arc crossed by the opinion.
        arc: ArcType,
        /// The arc's root in composed namespace.
        arc_root: Path,
        /// The prim being composed when the target was found.
        composing: Path,
    },

    /// A relationship target or attribute connection authored in a class (an
    /// inherit/specialize node) names an *instance* of that class rather than a
    /// path within the class (C++ `PcpErrorInvalidInstanceTargetPath`). Pointing
    /// at a specific instance breaks the invertibility of path translation, so
    /// the target is dropped. The *self* instance (the one being composed) keeps
    /// the generic [`InvalidExternalTargetPath`](Self::InvalidExternalTargetPath)
    /// "outside scope" message instead. Reported while composing the owning prim.
    #[error("class target {target} on {property} names an instance of the class")]
    InvalidInstanceTargetPath {
        /// Whether this is an attribute connection.
        is_connection: bool,
        /// The dropped target path, in the authoring node's namespace.
        target: Path,
        /// The owning property path, in the authoring node's namespace.
        property: Path,
        /// Identifier of the authoring (class) layer.
        layer: String,
        /// The prim being composed when the target was found.
        composing: Path,
    },

    /// A property composes specs of inconsistent types — an attribute spec and a
    /// relationship spec at the same path (C++ `PcpErrorInconsistentPropertyType`).
    /// The strongest (defining) spec's type wins; weaker specs of the other type
    /// are ignored. Reported while composing the owning prim (`.composing`).
    #[error("inconsistent spec types for property {property}")]
    InconsistentPropertyType {
        /// The composed property path.
        property: Path,
        /// Identifier of the defining spec's layer.
        defining_layer: String,
        /// The defining spec's path.
        defining_path: Path,
        /// Whether the defining spec is an attribute.
        defining_is_attribute: bool,
        /// Identifier of the conflicting spec's layer.
        conflicting_layer: String,
        /// The conflicting spec's path.
        conflicting_path: Path,
        /// Whether the conflicting spec is an attribute.
        conflicting_is_attribute: bool,
        /// The prim being composed when the conflict was found.
        composing: Path,
    },

    /// A layer authors a direct opinion at a relocation source path, which is
    /// invalid and ignored (C++ `PcpErrorOpinionAtRelocationSource`): once a prim
    /// is relocated, its source location must be empty. Reported while composing
    /// the prim that follows the relocation (`composing`); the cache stamps that
    /// path when collecting the build's errors.
    #[error("invalid opinion at relocation source {source_path} in layer {layer}")]
    OpinionAtRelocationSource {
        /// The relocation source path carrying the invalid opinion.
        source_path: Path,
        /// Identifier of the layer authoring the invalid opinion.
        layer: String,
        /// The prim being composed when the relocation was followed.
        composing: Path,
    },

    /// A sublayer asset path could not be resolved while building a layer stack
    /// (C++ `PcpErrorInvalidSublayerPath`). The missing sublayer is skipped.
    #[error("unresolved sublayer @{asset_path}@ introduced by @{introduced_by}@")]
    UnresolvedSublayer {
        /// The unresolved authored asset path.
        asset_path: String,
        /// Identifier of the layer that authored the sublayer.
        introduced_by: String,
    },

    /// A sublayer resolved but its layer could not be read or parsed. Only the
    /// bad sublayer is dropped; the layer that declared it (and the rest of the
    /// stack) still composes, matching C++ `SdfLayer`, which opens the parent and
    /// reports the unreadable sublayer.
    #[error("malformed sublayer @{asset_path}@ introduced by @{introduced_by}@: {reason}")]
    MalformedSublayer {
        /// The authored asset path whose layer could not be read.
        asset_path: String,
        /// Identifier of the layer that authored the sublayer.
        introduced_by: String,
        /// The underlying read or parse error.
        reason: String,
    },

    /// A layer's `subLayers` form a cycle — a layer includes itself, directly or
    /// transitively (C++ `PcpErrorSublayerCycle`). Detected while building the
    /// stage root layer stack; the cyclic sublayer is skipped and the rest of the
    /// stack still composes. `root_layer` is the layer whose sublayer list
    /// re-introduces `seen_layer`.
    #[error("sublayer cycle: {root_layer} re-includes {seen_layer}")]
    SublayerCycle {
        /// Identifier of the layer whose `subLayers` closes the cycle.
        root_layer: String,
        /// Identifier of the already-seen layer the cycle re-includes.
        seen_layer: String,
    },

    /// Several relocations in a layer stack move different sources to the same
    /// target (C++ `PcpErrorInvalidSameTargetRelocations`). All of them are
    /// invalid and dropped.
    #[error("multiple relocations target {target}")]
    SameTargetRelocations {
        /// The shared target path.
        target: Path,
        /// Source paths and their authoring layer identifiers.
        sources: Vec<(Path, String)>,
    },

    /// Two relocations in a layer stack conflict — one's target is another's
    /// source, or one's source/target is a descendant of another's source (C++
    /// `PcpErrorInvalidConflictingRelocation`). The relocate is dropped; `reason`
    /// is the specific rule violated.
    #[error("conflicting relocation from {source_path} to {target_path}")]
    ConflictingRelocation {
        /// The reported relocate's source.
        source_path: Path,
        /// The reported relocate's target.
        target_path: Path,
        /// Identifier of the reported relocate's layer.
        layer: String,
        /// The conflicting relocate's source.
        other_source_path: Path,
        /// The conflicting relocate's target.
        other_target_path: Path,
        /// Identifier of the conflicting relocate's layer.
        other_layer: String,
        /// The conflict rule violated.
        reason: RelocateConflictReason,
    },

    /// An authored relocate that breaks a structural rule — source and target
    /// identical or nested, or a root-prim source — is invalid and ignored (C++
    /// `PcpErrorInvalidAuthoredRelocates`). It is dropped while the layer stack
    /// still composes. `reason` is the specific rule violated.
    #[error("invalid relocate from {source_path} to {target_path} authored in {layer}: {reason}")]
    InvalidRelocate {
        /// The relocate source path.
        source_path: Path,
        /// The relocate target path.
        target_path: Path,
        /// Identifier of the layer that authored the relocate.
        layer: String,
        /// The structural rule the relocate violates.
        reason: InvalidRelocateReason,
    },
}

impl From<sdf::layer_registry::Error> for Error {
    /// Lifts a layer-registry load error into a composition error: a sublayer
    /// that failed to resolve while opening a layer stack (the root stack or a
    /// reference/payload target reached on demand) is an
    /// [`UnresolvedSublayer`](Error::UnresolvedSublayer); a sublayer that
    /// resolved but could not be read is a [`MalformedSublayer`](Error::MalformedSublayer).
    fn from(error: sdf::layer_registry::Error) -> Self {
        match error {
            sdf::layer_registry::Error::UnresolvedAsset {
                asset_path,
                referencing_layer,
            } => Error::UnresolvedSublayer {
                asset_path,
                introduced_by: referencing_layer,
            },
            sdf::layer_registry::Error::UnreadableAsset {
                asset_path,
                referencing_layer,
                reason,
            } => Error::MalformedSublayer {
                asset_path,
                introduced_by: referencing_layer,
                reason,
            },
        }
    }
}

/// Structural rule violated by an authored relocate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum InvalidRelocateReason {
    /// A root prim cannot be relocated.
    #[error("Root prims cannot be the source of a relocate.")]
    RootPrimSource,
    /// A relocate cannot target its source.
    #[error("The target of a relocate cannot be the same as its source.")]
    SourceEqualsTarget,
    /// A relocate target cannot contain its source.
    #[error("The target of a relocate cannot be an ancestor of its source.")]
    TargetIsAncestor,
    /// A relocate source cannot contain its target.
    #[error("The target of a relocate cannot be a descendant of its source.")]
    TargetIsDescendant,
}

/// Pairwise rule violated by two relocates in one layer stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, thiserror::Error)]
pub enum RelocateConflictReason {
    /// One relocate targets another relocate's source.
    #[error("The target of a relocate cannot be the source of another relocate in the same layer stack.")]
    TargetIsSource,
    /// One relocate sources another relocate's target.
    #[error("The source of a relocate cannot be the target of another relocate in the same layer stack.")]
    SourceIsTarget,
    /// One relocate targets a descendant of another relocate's source.
    #[error("The target of a relocate cannot be a descendant of the source of another relocate.")]
    TargetDescendant,
    /// One relocate sources a descendant of another relocate's source.
    #[error("The source of a relocate cannot be a descendant of the source of another relocate.")]
    SourceDescendant,
}

/// A composition arc cycle ([`Error::ArcCycle`]). The chain reads from the
/// composing prim (`composing`, in the `root_layer`) through each `hops` site;
/// the last hop is the arc that closes the cycle and is dropped.
#[derive(Debug, Clone, PartialEq)]
pub struct CycleChain {
    /// The prim being composed when the cycle was detected (the chain root).
    pub composing: Path,
    /// Identifier of the layer the composing prim's root node resolves in.
    pub root_layer: String,
    /// Each arc in the cycle chain, in order; the final entry is the dropped,
    /// cycle-closing arc.
    pub hops: Vec<CycleHop>,
}

/// One arc in a composition cycle chain ([`CycleChain::hops`]): the arc type and
/// the `(layer, path)` site it reaches.
#[derive(Debug, Clone, PartialEq)]
pub struct CycleHop {
    /// The arc reaching this site (selects "references" / "inherits from" / …).
    pub arc: ArcType,
    /// Identifier of the layer the site resolves in.
    pub layer: String,
    /// The site path, in that layer's namespace.
    pub path: Path,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn layer(id: &str, text: &str) -> sdf::Layer {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        sdf::Layer::new(id, Box::new(sdf::Data::from_specs(data)))
    }

    fn relocate_count(graph: &LayerGraph) -> usize {
        graph
            .all_ids()
            .iter()
            .filter(|&&id| !graph.get(id).unwrap().relocates.is_empty())
            .count()
    }

    /// `recompute_relocates` re-derives both the cached flag and the per-layer
    /// relocate pairs from the current layer data. A `layerRelocates` edit reaches
    /// the graph through `IndexCache::recompute_relocates`, so both must be refreshed
    /// there or the indexer keeps reading stale relocate state.
    #[test]
    fn recompute_relocate_data_syncs() {
        let plain = layer("root.usd", "#usda 1.0\ndef \"A\" {}\n");
        let mut graph = LayerGraph::from_layers(vec![plain], 0, sdf::LayerRegistry::default());
        let id = graph.root_id().expect("root layer");
        assert!(!graph.has_relocates(), "a graph with no layerRelocates starts clear");
        assert!(
            graph.get(id).unwrap().relocates.is_empty(),
            "no relocate pairs to start"
        );

        // Author layerRelocates onto the layer (as an in-place edit would) and
        // refresh the state the way `recompute_relocates` now does. The source is
        // a non-root prim — a root prim cannot be a relocate source.
        graph.get_mut(id).unwrap().layer = layer(
            "root.usd",
            "#usda 1.0\n(\n    relocates = { </Grp/A>: </Grp/B> }\n)\ndef \"Grp\" {\n    def \"A\" {}\n}\n",
        );
        graph.recompute_relocates();
        assert!(
            graph.has_relocates(),
            "recompute picks up the newly authored layerRelocates"
        );
        assert_eq!(
            graph.relocation_source(graph.root_layer_stack_id(), &Path::new("/Grp/B").unwrap()),
            Some(Path::new("/Grp/A").unwrap()),
            "recompute re-extracts the per-layer relocate pairs the indexer reads"
        );
    }

    #[test]
    fn sublayer_relocate_conflict() {
        let root = layer(
            "root.usda",
            r#"#usda 1.0
(
    subLayers = [@sub.usda@]
    relocates = { </World/A>: </World/C> }
)
"#,
        );
        let sub = layer(
            "sub.usda",
            r#"#usda 1.0
(
    relocates = { </World/B>: </World/C> }
)
"#,
        );
        let graph = LayerGraph::from_layers(vec![root, sub], 0, sdf::LayerRegistry::default());

        assert!(
            graph
                .errors()
                .iter()
                .any(|error| matches!(error, Error::SameTargetRelocations { .. })),
            "relocates in one sublayer stack must conflict"
        );
        assert_eq!(
            graph.relocation_source(graph.root_layer_stack_id(), &Path::new("/World/C").unwrap()),
            None,
            "every relocate sharing the target is dropped"
        );
    }

    #[test]
    fn duplicate_sublayer_relocate() {
        let root = layer(
            "root.usda",
            r#"#usda 1.0
(
    subLayers = [@sub.usda@, @sub.usda@]
)
"#,
        );
        let sub = layer(
            "sub.usda",
            r#"#usda 1.0
(
    relocates = { </Ref/Orig>: </Ref/Geom> }
)
"#,
        );
        let graph = LayerGraph::from_layers(vec![root, sub], 0, sdf::LayerRegistry::default());

        assert!(
            !graph
                .errors()
                .iter()
                .any(|error| matches!(error, Error::SameTargetRelocations { .. })),
            "a repeated sublayer has one authored relocate occurrence"
        );
        assert_eq!(
            graph.relocation_source(graph.root_layer_stack_id(), &Path::new("/Ref/Geom").unwrap()),
            Some(Path::new("/Ref/Orig").unwrap())
        );
    }

    #[test]
    fn duplicate_source_conflict() {
        let root = layer(
            "root.usda",
            r#"#usda 1.0
(
    subLayers = [@sub.usda@]
    relocates = {
        </World/A>: </World/T>,
        </World/B>: </World/T>
    }
)
"#,
        );
        let sub = layer(
            "sub.usda",
            r#"#usda 1.0
(
    relocates = { </World/A>: </World/U> }
)
"#,
        );
        let mut graph = LayerGraph::from_layers(vec![root, sub], 0, sdf::LayerRegistry::default());

        assert_eq!(
            graph.relocation_source(graph.root_layer_stack_id(), &Path::new("/World/U").unwrap()),
            None,
            "weaker duplicate source must stay dropped even when the stronger occurrence conflicts"
        );
        let sub = graph.id_of("sub.usda").expect("sub layer");
        // The sub-stack handle is minted on demand at the load barrier in
        // production; this direct relocate query composes nothing, so mint it via
        // `intern_external` under the root context.
        let sub_stack = graph.intern_external(sub, LayerStackId::ROOT).0;
        assert_eq!(
            graph.relocation_source(sub_stack, &Path::new("/World/U").unwrap()),
            Some(Path::new("/World/A").unwrap()),
            "duplicate-source dropping is scoped to the stack being composed"
        );
    }

    #[test]
    fn unrelated_relocates_coexist() {
        let first = layer(
            "first.usda",
            r#"#usda 1.0
(
    relocates = { </World/A>: </World/C> }
)
"#,
        );
        let second = layer(
            "second.usda",
            r#"#usda 1.0
(
    relocates = { </World/B>: </World/C> }
)
"#,
        );
        let graph = LayerGraph::from_layers(vec![first, second], 0, sdf::LayerRegistry::default());

        assert!(
            !graph
                .errors()
                .iter()
                .any(|error| matches!(error, Error::SameTargetRelocations { .. })),
            "relocates in unrelated layer stacks do not conflict"
        );
        assert_eq!(relocate_count(&graph), 2);
    }

    /// `effective_time_codes_per_second` reads the authored rate but clamps a
    /// degenerate one (zero / negative / non-finite) back to the 24.0 default,
    /// so the retiming ratio folded into sublayer offsets stays finite and
    /// positive (the fold runs without re-`sanitized`-ing the result).
    #[test]
    fn effective_tcps_clamps_degenerate() {
        let header = |meta: &str| format!("#usda 1.0\n(\n{meta}\n)\ndef \"A\" {{}}\n");
        let tcps = |meta: &str| effective_time_codes_per_second(&layer("l.usd", &header(meta)));

        assert_eq!(tcps("    timeCodesPerSecond = 48"), 48.0, "authored rate is used");
        assert_eq!(
            tcps("    framesPerSecond = 12"),
            12.0,
            "framesPerSecond is the fallback"
        );
        assert_eq!(tcps(""), 24.0, "unset rate defaults to 24");
        assert_eq!(
            tcps("    timeCodesPerSecond = 0"),
            24.0,
            "zero rate clamps to the default"
        );
        assert_eq!(
            tcps("    timeCodesPerSecond = -24"),
            24.0,
            "negative rate clamps to the default"
        );
    }
}
