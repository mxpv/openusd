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
//! underlying layers. They are split between the builder and the cache:
//!
//! - `layerRelocates` are extracted from each layer's pseudoroot at
//!   construction and mapped into the composed namespace through each
//!   layer's namespace mapping.
//! - When composing a prim that is a relocate target, the builder
//!   (`eval_node_relocations`) finds the pre-relocation source path, composes
//!   it as a sub-index, and grafts the result as a `Relocate` arc node. Each
//!   grafted node carries the source site's full layer stack, so a relocate
//!   source spanning several sublayers keeps every member, not just the
//!   strongest.
//! - Child names are folded per composition node: each node's layer-stack
//!   relocates (chained within the layer stack) rename, remove, or add direct
//!   children, and every relocation source becomes a prohibited name
//!   (`Cache::compute_prim_child_names` → `rel::apply_child_relocates`).
//!
//! # Module structure
//!
//! | Item | C++ equivalent | Description |
//! |------|---------------|-------------|
//! | `LayerStack` | `PcpLayerStack` | Layers and precomputed sublayer stacks bundled into a single unit. |
//! | `cache` | `PcpCache` | Lazily-built composition cache. Main interface for [`Stage`](crate::usd::Stage). Owns a `LayerStack`. |
//! | [`Error`] | `PcpErrorBase` | Composition errors: arc cycles, unresolved layers, missing/invalid `defaultPrim`, arc-to-private-site permission denials. |
//! | `index` | `PcpPrimIndex` | Per-prim composition support: the [`PrimIndex`] type with its build entry points (`build_with_cache` / `build_with_cache_in`), the [`CompositionContext`](index::CompositionContext) that flows parent-to-child, and the arc-composition helpers (`compose_references_in`, `collect_payloads_in`, etc.) the `builder` drives. |
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
//! ## Composition gaps
//!
//! One compliance asset is still suppressed in `SKIP_PCP_COMPLIANCE`
//! (`tests/composition.rs`):
//!
//! - Instance-target-path validation (`ErrorInvalidInstanceTargetPath`). A
//!   relationship/connection authored in a class that targets a *different*
//!   instance of that class is invalid with its own "is authored in a class but
//!   refers to an instance of that class" message (C++
//!   `PcpErrorInvalidInstanceTargetPath`); the *self* instance keeps the generic
//!   out-of-scope message. This needs a cross-prim check that the target prim
//!   inherits the class, and it depends on the faithful relocate-target
//!   translation below (the symmetric-rig case keeps a class connection target at
//!   its pre-relocation path). A step-by-step plan lives in
//!   `docs/plans/error-invalid-instance-target-path.md`.
//!
//! Two relocate approximations remain even though their former compliance assets
//! now reproduce byte-for-byte — they are the deeper work the suppressed asset
//! above needs:
//!
//! - Relocate-target translation. A relationship/connection target naming a
//!   pre-relocation source is remapped by a global `chain_through_relocates` over
//!   relocates discovered by scanning whichever prims are already cached, so the
//!   result is traversal-order-dependent (the `TODO` at
//!   `Cache::compose_property_paths`), with a layer-difference proxy in
//!   `resolve_path_list_op_validated` standing in for the exact rule. The
//!   faithful form folds relocates into each node's arc maps, so a target is
//!   retimed only by the Relocate arcs in its own chain (C++
//!   `PcpBuildFilteredTargetIndex` / `PcpTranslatePathFromNodeToRoot`).
//! - Cross-arc implied relocations (C++ `_EvalImpliedRelocations`'s graft) are
//!   unported (`eval_implied_relocations`'s `TODO(relocates)`). The per-node
//!   child-name fold otherwise reproduces the symmetric-rig and
//!   multi-relocation-chain cases.
//!
//! Beyond the compliance assets, the instancing dump still redirects prototypes
//! through aliases rather than composing dedicated prototype prims. Goldens that
//! can never be reproduced byte-for-byte — pxr-internal C++ warnings or Python
//! tracebacks emitted by the reference test framework — stay on the looser
//! existence check in `UNREPRODUCIBLE_GOLDEN`.
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
//! (mirroring C++ `PcpComposeSiteChildNames`). Relocates apply per node during
//! that fold (`Cache::compute_prim_child_names` → `rel::apply_child_relocates`,
//! the port of C++ `_ComposePrimChildNamesAtNode`): at each node its layer stack's
//! relocates rename, remove, or add direct children — a renamed child keeps the
//! source's position — and every relocation source becomes a prohibited name
//! removed from the final order, so a scene combining multi-sublayer `primOrder`
//! with relocates orders children as C++ does.
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
    pub(crate) layer_relocates: rel::LayerRelocates,
    /// Recoverable errors detected while assembling the layer stack — sublayer
    /// cycles and structurally invalid authored relocates (C++ errors surfaced
    /// while computing the layer stack). The [`Cache`](cache::Cache) drains these
    /// into its composition errors once at construction and again whenever a
    /// `subLayers`/`layerRelocates` edit recomputes them.
    pub(crate) layer_stack_errors: Vec<Error>,
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
        // Keep the sublayer-cycle errors from the stage-root build; the other
        // per-layer builds detect their own subtrees' cycles, which would
        // duplicate the root's, so they share one discarded `scratch` sink.
        let mut layer_stack_errors = Vec::new();
        let mut scratch = Vec::new();
        let sublayer_stacks: SublayerStacks = (0..layers.len())
            .map(|i| {
                let errors = if i == session_layer_count {
                    &mut layer_stack_errors
                } else {
                    &mut scratch
                };
                (i, Self::build_sublayer_stack(i, &layers, &*resolver, errors))
            })
            .collect();
        let has_relocates = Self::compute_has_relocates(&layers);
        let (layer_relocates, relocate_errors) =
            rel::extract_layer_relocates(&layers, &sublayer_stacks, session_layer_count);
        layer_stack_errors.extend(relocate_errors);
        Self {
            layers,
            sublayer_stacks,
            session_layer_count,
            load_payloads,
            has_relocates,
            layer_relocates,
            layer_stack_errors,
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

    /// The as-authored relocates of `ambient`, strongest layer first with
    /// duplicate sources dropped (C++ `PcpLayerStack::GetIncrementalRelocates*`,
    /// the per-layer-stack relocates keyed by their authored source). Unlike
    /// [`combined_relocates`](Self::combined_relocates) the pairs are not chained:
    /// each keeps its authored source and target. The unchained form is the base
    /// `combined_relocates` chains on top of.
    fn incremental_relocates(&self, ambient: &[(usize, sdf::LayerOffset)]) -> Vec<(Path, Path)> {
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
        pairs
    }

    /// Chains the per-layer authored relocates of `ambient` into a single
    /// source→target map (C++ `PcpLayerStack::GetRelocatesSourceToTarget`): the
    /// strongest layer wins a duplicate source, and a target that is itself a
    /// relocation source is followed to the final target. This is the form the
    /// per-node child-name relocate classification consumes, so a same-parent
    /// chain resolves to its final target in one pass.
    pub(crate) fn combined_relocates(&self, ambient: &[(usize, sdf::LayerOffset)]) -> Vec<(Path, Path)> {
        let mut pairs = self.incremental_relocates(ambient);
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
        self.relocation_source_layer(ambient, source).is_some()
    }

    /// Identifier of the strongest layer in `ambient` that authors a relocate
    /// whose SOURCE is `source`, or `None` if none does. Names the layer in the
    /// prohibited-relocation-source diagnostic.
    pub(crate) fn relocation_source_layer(&self, ambient: &[(usize, sdf::LayerOffset)], source: &Path) -> Option<&str> {
        ambient.iter().find_map(|&(layer, _)| {
            self.layer_relocates
                .get(&layer)
                .filter(|pairs| pairs.iter().any(|(s, _)| s == source))
                .map(|_| self.layers[layer].identifier.as_str())
        })
    }

    /// Re-derives the cached relocate state — [`has_relocates`](Self::has_relocates),
    /// [`layer_relocates`](Self::layer_relocates), and the relocate-extraction
    /// portion of [`layer_stack_errors`](Self::layer_stack_errors) — from the
    /// current layers. Called after a `layerRelocates` edit that does not rebuild
    /// the sublayer precomputation (which would refresh both itself); keeping
    /// them in sync is what re-enables and re-targets the builder's relocate passes.
    pub(crate) fn recompute_relocate_data(&mut self) {
        self.has_relocates = Self::compute_has_relocates(&self.layers);
        let (layer_relocates, relocate_errors) =
            rel::extract_layer_relocates(&self.layers, &self.sublayer_stacks, self.session_layer_count);
        self.layer_relocates = layer_relocates;
        // Drop every error `extract_layer_relocates` can produce before re-adding
        // the fresh set, so a resolved conflict clears and a surviving one is not
        // duplicated across recomputes.
        self.layer_stack_errors.retain(|e| {
            !matches!(
                e,
                Error::InvalidRelocate { .. }
                    | Error::SameTargetRelocations { .. }
                    | Error::ConflictingRelocation { .. }
            )
        });
        self.layer_stack_errors.extend(relocate_errors);
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
        // Refresh the sublayer-cycle errors from the stage-root build (the other
        // builds share one discarded `scratch` sink); `recompute_relocate_data`
        // then keeps these and re-appends the invalid-relocate errors.
        let mut layer_stack_errors = Vec::new();
        let mut scratch = Vec::new();
        self.sublayer_stacks = (0..self.layers.len())
            .map(|i| {
                let errors = if i == self.session_layer_count {
                    &mut layer_stack_errors
                } else {
                    &mut scratch
                };
                (i, Self::build_sublayer_stack(i, &self.layers, &*self.resolver, errors))
            })
            .collect();
        self.layer_stack_errors = layer_stack_errors;
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
            .unwrap_or_else(|| Self::build_sublayer_stack(root_layer, &self.layers, &*self.resolver, &mut Vec::new()))
    }

    /// Builds the sublayer stack rooted at `root_layer`, recording any sublayer
    /// cycle it encounters into `errors` as [`Error::SublayerCycle`]. Callers that
    /// only need the stack pass a throwaway `errors` vec; the layer stack keeps
    /// the errors from the stage-root build (see [`new`](Self::new)).
    pub(crate) fn build_sublayer_stack(
        root_layer: usize,
        layers: &[sdf::Layer],
        resolver: &dyn Resolver,
        errors: &mut Vec<Error>,
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
            errors,
        );
        stack
    }

    /// Appends `idx` and its sublayer subtree to `stack` in depth-first
    /// pre-order. `ancestors` holds the layers on the path from the root to
    /// `idx`; a sublayer already on that path is a cycle (C++
    /// `PcpErrorSublayerCycle`): it is skipped and recorded in `errors` (the
    /// message pairs `idx`, the layer whose `subLayers` closes the cycle, with the
    /// re-included `sub_idx`), while a layer reached off the path is a permitted
    /// duplicate and is expanded again.
    #[allow(clippy::too_many_arguments)]
    fn collect_sublayers(
        idx: usize,
        effective: sdf::LayerOffset,
        layers: &[sdf::Layer],
        resolver: &dyn Resolver,
        stack: &mut Vec<(usize, sdf::LayerOffset)>,
        ancestors: &mut HashSet<usize>,
        errors: &mut Vec<Error>,
    ) {
        stack.push((idx, effective));
        ancestors.insert(idx);

        let root = Path::abs_root();
        if let Ok(Value::StringVec(sub_paths)) = layers[idx]
            .get(&root, FieldKey::SubLayers.as_str())
            .map(|v| v.into_owned())
        {
            // The parent's effective rate is fixed across its sublayers, so it
            // is read once for the per-hop `timeCodesPerSecond` retiming below.
            let parent_tcps = effective_time_codes_per_second(&layers[idx]);
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
                    errors.push(Error::SublayerCycle {
                        root_layer: layers[idx].identifier.clone(),
                        seen_layer: layers[sub_idx].identifier.clone(),
                    });
                    continue;
                }
                // Fold the time-codes-per-second retiming for this hop into the
                // sublayer's scale (spec 12.3.2): a sublayer whose rate differs
                // from its parent retimes by `parent / child`. Offset is unscaled.
                let ratio = parent_tcps / effective_time_codes_per_second(&layers[sub_idx]);
                let local = offsets
                    .get(i)
                    .copied()
                    .unwrap_or_default()
                    .sanitized()
                    .concatenate(&sdf::LayerOffset::scale_only(ratio));
                let child = effective.concatenate(&local);
                Self::collect_sublayers(sub_idx, child, layers, resolver, stack, ancestors, errors);
            }
        }

        ancestors.remove(&idx);
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
        match layer.try_get(&root, key.as_str()).ok()??.into_owned() {
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

/// An error encountered while building a [`PrimIndex`](index::PrimIndex).
///
/// These errors represent composition diagnostics. Recoverable failures skip
/// the broken opinion and are retained by [`Stage`](crate::usd::Stage).
#[derive(Debug, Clone, thiserror::Error)]
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

    /// A reference/payload asset path is a variable expression that failed to
    /// parse or did not evaluate to a string (C++ `PcpErrorVariableExpression`).
    /// The arc is skipped and the rest of the prim still composes, so this is
    /// recoverable.
    #[error("invalid {arc:?} asset-path expression {expression} at {site_path}: {message}")]
    InvalidExpression {
        /// The raw, unevaluated backtick expression.
        expression: String,
        /// The composition arc type.
        arc: ArcType,
        /// The prim path where the arc was authored.
        site_path: Path,
        /// The parse or evaluation failure.
        message: String,
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
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
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
        // refresh the state the way `recompute_relocates` now does. The source is
        // a non-root prim — a root prim cannot be a relocate source.
        stack.layers[0] = layer(
            "root.usd",
            "#usda 1.0\n(\n    relocates = { </Grp/A>: </Grp/B> }\n)\ndef \"Grp\" {\n    def \"A\" {}\n}\n",
        );
        stack.recompute_relocate_data();
        assert!(
            stack.has_relocates,
            "recompute picks up the newly authored layerRelocates"
        );
        assert_eq!(
            stack.relocation_source(&[(0, sdf::LayerOffset::default())], &Path::new("/Grp/B").unwrap()),
            Some(Path::new("/Grp/A").unwrap()),
            "recompute re-extracts the per-layer relocate pairs the builder reads"
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
        let stack = LayerStack::new(vec![root, sub], 0, Box::new(DefaultResolver::new()), true);

        assert!(
            stack
                .layer_stack_errors
                .iter()
                .any(|error| matches!(error, Error::SameTargetRelocations { .. })),
            "relocates in one sublayer stack must conflict"
        );
        assert!(
            stack.layer_relocates.is_empty(),
            "every relocate sharing the target is dropped"
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
        let stack = LayerStack::new(vec![first, second], 0, Box::new(DefaultResolver::new()), true);

        assert!(
            !stack
                .layer_stack_errors
                .iter()
                .any(|error| matches!(error, Error::SameTargetRelocations { .. })),
            "relocates in unrelated layer stacks do not conflict"
        );
        assert_eq!(stack.layer_relocates.len(), 2);
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
