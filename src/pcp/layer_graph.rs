//! Layer DAG: the loaded layers and their sublayer structure.
//!
//! [`LayerGraph`] owns every [`sdf::Layer`] a stage depends on and the sublayer
//! edges between them, keyed by the stable [`LayerId`]. It is the Rust
//! analog of C++ `PcpLayerStack` for the layer-ownership half of composition;
//! the composition index itself lives in [`IndexCache`](super::index_cache::IndexCache).
//!
//! Holding layers here (rather than inside the cache) lets a [`Stage`] borrow
//! the layer data and the composition index independently. Composition reads
//! the graph through a shared `&LayerGraph` parameter, so every per-prim build
//! stays a pure function of `(graph, context, cached indices)`.
//!
//! A composed sublayer stack (the depth-first pre-order walk of a root's sublayer
//! edges, with offsets composed) is interned in the
//! [`LayerStackRegistry`](super::layer_stack::LayerStackRegistry) of the
//! [`layer_stack`](super::layer_stack) module and addressed by a [`LayerStackId`];
//! only composition roots get an instance, so a sublayer-only layer participates
//! through its root's members rather than its own stack. The edges are always
//! derived from each layer's `subLayers` metadata by
//! [`recompute_sublayers`](LayerGraph::recompute_sublayers): both an ordinary
//! `subLayers` authoring edit and the public
//! [`Stage::insert_layer`](crate::usd::Stage::insert_layer) /
//! [`remove_layer`](crate::usd::Stage::remove_layer) route through it, so
//! editing `subLayers` updates the edges and the metadata stays the single
//! source of truth — no DFS on every query, and no edge that fails to persist on
//! save.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::mem;
use std::path;

use crate::ar::ResolvedPath;
use crate::sdf::expr;
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, LayerOffset, Path, RelocateList, Value};

use super::layer_stack::{ExprVarId, LayerStackId, LayerStackRegistry};
use super::mapping::MapFunction;
#[cfg(test)]
use super::prim_index::Demand;
use super::relocates::{analyze_relocate_occurrences, chain_through_relocates, validate_layer_relocates};
use super::{effective_time_codes_per_second, Error};

/// A cheap, `Copy` handle identifying a layer within a `LayerGraph`.
///
/// Graph-assigned (interned) as layers are added, not derived from content, so
/// it is unique by construction — no hashing and no collision. It is opaque:
/// resolve it back to an identifier with
/// [`Stage::layer_identifier`](crate::usd::Stage::layer_identifier). Authoring
/// callers address layers by identifier string instead; this handle is what
/// composition introspection (the [`PrimIndex`](super::PrimIndex) nodes) hands
/// back.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct LayerId(u32);

impl LayerId {
    /// A sentinel never assigned to a real layer, for degenerate fallbacks (an
    /// empty layer stack's synthetic root, an unresolvable edit target).
    pub(crate) const INVALID: LayerId = LayerId(u32::MAX);

    /// Wraps a raw graph-assigned index. Only [`LayerGraph`] mints ids in
    /// production; tests use it to build synthetic handles.
    pub(crate) const fn from_raw(raw: u32) -> Self {
        Self(raw)
    }
}

/// Stable identity of a stage's root layer stack, by composition input.
///
/// The Rust analog of C++ `PcpLayerStackIdentifier`, which keys a
/// `PcpLayerStack` by `(rootLayer, sessionLayer, pathResolverContext)`. Two
/// stages opened from the same root and session under a resolver with the same
/// [`identity`](crate::ar::Resolver::identity) are the same composition input,
/// so their identifiers compare equal. Used to tag a stage-bound
/// [`EditTarget`](crate::usd::EditTarget) so one built against a stage's
/// composition is rejected by an unrelated stage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LayerStackIdentifier {
    /// Canonical identifier of the root layer.
    pub root_layer: String,
    /// Canonical identifier of the strongest session layer, if any.
    pub session_layer: Option<String>,
    /// The resolver's [`identity`](crate::ar::Resolver::identity) token — the
    /// configuration the stack's asset paths resolve under.
    pub resolver: String,
}

/// A layer's resolved sublayer edges in declared order: each child paired with
/// the effective layer offset for that hop (the authored `subLayerOffset` with
/// the time-codes-per-second retiming folded in, per spec 10.3.1.1 / 12.3.2).
type SublayerEdges = Vec<(LayerId, LayerOffset)>;

/// A single layer in the [`LayerGraph`].
pub(crate) struct LayerNode {
    /// The loaded layer (identifier + backing data + authoring surface).
    pub layer: sdf::Layer,
    /// This layer's context-free [`SublayerEdges`]: its `subLayers` resolved against
    /// the empty expression-variable set, so literal sublayers resolve and `${VAR}`
    /// sublayers drop out. Shared by every stack with no expression sublayer, where
    /// the members are context-independent; a stack with an expression sublayer
    /// re-resolves its subtree against the stack's variables in
    /// [`compose_stack_edges`](LayerGraph::compose_stack_edges) instead, so these are
    /// not duplicated per stack instance.
    pub children: SublayerEdges,
    /// Whether this layer authors at least one expression-valued (`${VAR}`)
    /// `subLayers` entry — a purely local property of its own `subLayers`, not its
    /// composed subtree. Recomputed by
    /// [`build_sublayer_edges`](LayerGraph::build_sublayer_edges), it lets
    /// [`has_expr_sublayer`](LayerGraph::has_expr_sublayer) decide whether a stack's
    /// members depend on the expression-variable context by reading a bool per
    /// member rather than re-decoding `subLayers`.
    pub has_expr_sublayer: bool,
    /// The structurally valid authored `layerRelocates` pairs `(source, target)`
    /// in this layer's own namespace. Stack queries apply duplicate-source and
    /// conflict rules for the ambient layer stack. Empty when the layer authors
    /// none.
    pub relocates: RelocateList,
}

impl LayerNode {
    /// A node wrapping `layer`, with no edges and no relocates. The sublayer
    /// edges, expression-sublayer flag, and relocates are filled in by
    /// [`LayerGraph::recompute_sublayers`].
    fn new(layer: sdf::Layer) -> Self {
        Self {
            layer,
            children: Vec::new(),
            has_expr_sublayer: false,
            relocates: Vec::new(),
        }
    }
}

/// The loaded layers and their sublayer DAG.
///
/// Corresponds to a simplified C++ `PcpLayerStack`: it owns the layers but not
/// the composed prim indices. Composition queries reach a layer by its
/// [`LayerId`] in O(1).
pub(crate) struct LayerGraph {
    /// Every layer, keyed by id.
    nodes: HashMap<LayerId, LayerNode>,
    /// Exact `identifier → id` index, so a layer is resolved by its canonical
    /// identifier (the public authoring surface) in O(1), and a re-added
    /// identifier collapses onto its existing id.
    by_identifier: HashMap<String, LayerId>,
    /// Next id to mint. Monotonic for the life of the graph, so a removed id is
    /// never reused for a different layer within a session.
    next_id: u32,
    /// All layer ids in collection order. Iteration order is deterministic, so
    /// identifier listing and sublayer-stack composition are stable. The
    /// first [`session_layer_count`](Self::session_layer_count) entries are the
    /// session layers, in strength order.
    order: Vec<LayerId>,
    /// Number of session layers at the front of [`order`](Self::order).
    session_layer_count: usize,
    /// The root layer's id (the first non-session layer), if any.
    root: Option<LayerId>,
    /// Canonical identifiers of the muted layers — the source of truth for muting
    /// (C++ `Pcp_MutedLayers`'s sorted id set), so a layer can be muted before it
    /// is loaded. A path is reduced to this canonical form by
    /// [`canonical_muted_id`](Self::canonical_muted_id) (the resolver, anchored
    /// against the root layer), so every spelling of one layer collapses to a
    /// single entry and a not-yet-loaded reference/payload target matches the
    /// identifier it will be interned under. Excludes the root layer's identifier,
    /// which cannot be muted. The root layer can be muted neither here nor in
    /// [`muted`](Self::muted).
    muted_identifiers: HashSet<String>,
    /// The interned ids of the [`muted_identifiers`](Self::muted_identifiers) that
    /// name a loaded layer, re-materialized on every stack rebuild and excluded
    /// when materializing the stacks (C++ `PcpLayerStack::_BuildLayerStack`). A
    /// muted layer and its whole sublayer subtree are pruned from every stack while
    /// staying interned, so unmute is a rebuild. Re-materializing on each rebuild
    /// lets a layer muted before it was loaded take effect the moment it is
    /// interned. Empty by default, leaving composition unchanged.
    muted: HashSet<LayerId>,
    /// Whether any node keeps structurally valid authored relocates. The indexer
    /// reads this to gate its relocate passes without rescanning.
    has_relocates: bool,
    /// Whether any node authors an expression-valued (`${VAR}`) `subLayers` entry.
    /// A false value lets [`has_expr_sublayer`](Self::has_expr_sublayer) short-circuit
    /// to `false` for the overwhelmingly common stage with no expression sublayers,
    /// so [`build_stack_members`](Self::build_stack_members) never scans a stack for
    /// them. Recomputed with the per-node flags by
    /// [`build_sublayer_edges`](Self::build_sublayer_edges).
    any_expr_sublayer: bool,
    /// Sublayer-cycle diagnostics reachable from the root layer, replaced wholesale
    /// by [`build_sublayer_edges`](Self::build_sublayer_edges) on every edge
    /// rebuild so a fixed cycle stops being reported and a recompute never
    /// duplicates one.
    cycle_errors: Vec<Error>,
    /// Validated-relocate diagnostics, replaced wholesale by
    /// [`recompute_relocates`](Self::recompute_relocates) on every relocate
    /// rebuild. Independent of [`cycle_errors`](Self::cycle_errors): a
    /// relocate-only edit refreshes these alone.
    relocate_errors: Vec<Error>,
    /// Loads layers: the resolver that anchors relative asset paths (its
    /// [`identity`](Resolver::identity) is the resolver component of the stack's
    /// [`layer_stack_id`](Self::layer_stack_id)) and the format registry.
    /// Composition opens a reference/payload target on demand through it.
    registry: sdf::LayerRegistry,
    /// Anchored asset paths whose target layer resolved but failed to read or
    /// parse, each mapped to the underlying error. Consulted at the
    /// reference/payload demand point so a target that cannot be opened is
    /// reported [`MalformedLayer`](Error::MalformedLayer) once (with the arc's
    /// site context and this reason) rather than re-demanded every pass — without
    /// it the demanding prim's index would never cache. Written only at the
    /// stage's load barrier through `&mut self`; read during composition, and
    /// cleared when an edit changes the layers so a now-readable asset is retried.
    failed_loads: HashMap<String, String>,
    /// Every composed layer stack against this graph — the stage root stack, plus
    /// each reference/payload target's stack under whatever inherited contexts have
    /// reached it (see [`LayerStackRegistry`]). The graph composes a stack's members
    /// (it owns the layers) through [`build_stack_members`](Self::build_stack_members)
    /// and hands them to the registry, which owns the storage and interning. A
    /// [`LayerStackId`] is an index into it.
    stacks: LayerStackRegistry,
    /// Memoized sublayer-path resolution, `parent layer → (authored sub-path →
    /// resolved identifier)`. [`resolve_edges`](Self::resolve_edges) anchors each
    /// relative `subLayers` entry against its parent through the resolver — a
    /// filesystem canonicalize — and re-runs the whole walk on every
    /// [`build_sublayer_edges`](Self::build_sublayer_edges), i.e. every `subLayers`
    /// edit. The `(parent, sub-path) → identifier` mapping is a pure function of
    /// the asset paths, so it is computed once and reused; the identifier is then
    /// looked up live with [`id_of`](Self::id_of), so the cache survives a layer
    /// being removed and re-added, and a target that interns on a later rebuild is
    /// picked up without re-resolving the path.
    sublayer_resolution: HashMap<LayerId, HashMap<String, String>>,
}

/// What a [`mute_layer`](LayerGraph::mute_layer) or
/// [`unmute_layer`](LayerGraph::unmute_layer) actually changed, returned only
/// when the muted set changed.
pub(crate) struct MuteChange {
    /// The canonical identifier whose muted state toggled — the one a mute
    /// inserted or an unmute removed. The stage notifies it, not the spelling the
    /// caller passed, so a listener mirroring the muted set stays in sync (C++
    /// reports the canonical id it toggled).
    pub(crate) changed: String,
    /// Layers whose cached prim indices the change can invalidate (see
    /// [`mute_fanout`](LayerGraph::mute_fanout)).
    pub(crate) affected: HashSet<LayerId>,
}

/// The layer stack a reference/payload arc to an external target should compose
/// against, the result of [`LayerGraph::external_stack_id`]. Centralizes the
/// stack-selection decision so the indexer and the load barrier do not each
/// re-encode it.
pub(crate) enum ExternalStack {
    /// The stack is composed and ready; compose the arc against this handle.
    Ready(LayerStackId),
    /// No instance exists yet for this `(target, context)`; the arc must record a
    /// [`Demand`](super::Demand) so the load barrier mints it (and opens any
    /// `${VAR}` sublayers the context resolves), after which the query re-runs.
    Demand,
}

impl LayerGraph {
    /// Builds the graph from collected layers in strength order (session layers
    /// first, then the root layer and the rest). The recoverable layer-stack
    /// errors it detects (sublayer cycles, invalid relocates) are stored on the
    /// graph and read back through [`errors`](Self::errors).
    /// An empty graph that opens layers through `registry`. Layers join via
    /// [`ensure_layer`](Self::ensure_layer); [`finalize`](Self::finalize) wires
    /// the sublayer DAG once they are all added. The stage builds a graph this way
    /// so it can attach a change sink to each layer as it joins;
    /// [`from_layers`](Self::from_layers) is the all-at-once convenience.
    pub(crate) fn new(registry: sdf::LayerRegistry) -> Self {
        Self {
            nodes: HashMap::new(),
            by_identifier: HashMap::new(),
            next_id: 0,
            order: Vec::new(),
            session_layer_count: 0,
            root: None,
            muted_identifiers: HashSet::new(),
            muted: HashSet::new(),
            has_relocates: false,
            any_expr_sublayer: false,
            cycle_errors: Vec::new(),
            relocate_errors: Vec::new(),
            registry,
            failed_loads: HashMap::new(),
            stacks: LayerStackRegistry::default(),
            sublayer_resolution: HashMap::new(),
        }
    }

    /// Set the session/root layers and wire the sublayer DAG from each layer's
    /// authored `subLayers` metadata (resolving relocates), after the layers have
    /// been added. `root` is the stage root layer's id and `session_layer_count`
    /// the number of distinct session layers at the front of the collection. The
    /// post-add half of construction, shared by [`from_layers`](Self::from_layers)
    /// and the stage builder, which adds layers one at a time.
    ///
    /// `session_count` counts only the distinct session-region layers that
    /// survive into [`order`](Self::order), so [`session_layers`](Self::session_layers)
    /// (which slices the prefix) never over-reads when the caller passed duplicate
    /// identifiers (the same dependency reached through both the session and root
    /// collections). `root` is captured at the original root slot rather than
    /// derived from `order`, so a root identifier that already appeared in the
    /// session collection still points at the right layer.
    pub(crate) fn finalize(&mut self, session_layer_count: usize, root: Option<LayerId>) {
        self.session_layer_count = session_layer_count;
        self.root = root;
        // A full pass returns no scoped set; finalize re-resolves every stack.
        let _ = self.build_sublayer_edges(None);
        self.mint_eager_target_stacks();
        self.recompute_relocates();
    }

    /// Adds `layer` as a node, minting a fresh [`LayerId`] and recording it in
    /// [`by_identifier`](Self::by_identifier) and [`order`](Self::order).
    /// Returns `(id, fresh)`: an identifier already present is left untouched
    /// (its existing node, children, and relocates survive) and reported as not
    /// fresh, so a re-added layer collapses onto its existing id.
    fn intern(&mut self, mut layer: sdf::Layer) -> (LayerId, bool) {
        if let Some(&id) = self.by_identifier.get(layer.identifier()) {
            return (id, false);
        }
        let id = LayerId::from_raw(self.next_id);
        self.next_id += 1;
        self.by_identifier.insert(layer.identifier().to_string(), id);
        // A layer's content is composed fresh as it joins the graph, so any
        // change record left by prior write-through edits must not survive to
        // be drained by a later transaction the stage runs on it.
        layer.discard_changes();
        self.nodes.insert(id, LayerNode::new(layer));
        self.order.push(id);
        (id, true)
    }

    /// Resolves every layer's `subLayers` into [`LayerNode::children`] — the
    /// context-free edges — folding the per-hop time-codes-per-second retiming into
    /// each edge offset. Replaces [`cycle_errors`](Self::cycle_errors) with the
    /// sublayer-cycle errors reachable from the root layer (C++
    /// `PcpErrorSublayerCycle`).
    ///
    /// A layer stack's expression variables come from its root layer, not its
    /// sublayers (C++ `PcpExpressionVariables`), so `children` carry no
    /// expression-variable context: each layer's `subLayers` resolve independently
    /// against the empty variable set, a literal sublayer resolving and an
    /// expression (`${VAR}`) sublayer dropping out. Expression sublayers are
    /// resolved per-stack against the stack's variables in
    /// [`compose_stack_edges`](Self::compose_stack_edges); the shared context-free
    /// `children` feed only the stacks that have none.
    ///
    /// Returns the affected layer set for a scoped edit (the layers whose composed
    /// edges changed, unioned with `edited`) so the caller can scope cache eviction
    /// to the same stacks the re-resolution touched; `None` for a full pass.
    fn build_sublayer_edges(&mut self, edited: Option<&HashSet<LayerId>>) -> Option<HashSet<LayerId>> {
        // Refresh the expression-sublayer flags first, so the stack rebuild below
        // reads them through `has_expr_sublayer` for its `collect_plain` fast-path
        // gate.
        self.recompute_expr_sublayer_flags();
        // Edges are resolved into a side buffer so the immutable `resolve_edges`
        // borrow does not clash with the per-node mutation that applies them.
        let mut all_edges: Vec<(LayerId, SublayerEdges)> = Vec::with_capacity(self.nodes.len());
        // Take the resolution cache out so `resolve_edges` (which borrows `self`
        // immutably) can fill it; it carries forward across rebuilds, so a
        // `subLayers` edit only resolves paths it has not seen before.
        let mut resolution = mem::take(&mut self.sublayer_resolution);

        // Each layer's context-free edges depend only on its own `subLayers`
        // resolved against the empty variable set, so one per-layer pass builds them
        // all.
        let empty = HashMap::new();
        for &id in &self.order {
            let edges = self.resolve_edges(id, &empty, &mut resolution);
            all_edges.push((id, edges));
        }
        self.sublayer_resolution = resolution;

        // Apply the composed edges. A full pass (`None`, at finalize or after a load
        // that can extend a stack with a newly opened member) re-resolves every
        // stack, so the edges are assigned outright. For an edit, the layers whose
        // composed edges actually changed — folded together with the authored layers
        // (`edited`) — scope the stack re-resolution to the affected instances: the
        // edge diff catches a layer whose own `subLayers` resolution changed, while
        // `edited` catches an authored `${VAR}` sublayer or `expressionVariables` edit
        // that shifts a stack's members without changing its plain edges.
        let affected = match edited {
            None => {
                for (id, edges) in all_edges {
                    self.nodes.get_mut(&id).expect("edge source exists").children = edges;
                }
                None
            }
            Some(edited) => {
                let mut changed: HashSet<LayerId> = HashSet::new();
                for (id, edges) in all_edges {
                    let node = self.nodes.get_mut(&id).expect("edge source exists");
                    if node.children != edges {
                        node.children = edges;
                        changed.insert(id);
                    }
                }
                changed.extend(edited);
                Some(changed)
            }
        };

        self.rebuild_sublayer_stacks(affected.as_ref());
        self.recompute_cycle_errors();
        affected
    }

    /// Resolves `id`'s `subLayers` into `(child, effective offset)` edges,
    /// evaluating each expression (`${VAR}`) path against `context` — the stack's
    /// single expression-variable set, or the empty set for the shared context-free
    /// [`LayerNode::children`]. Reads only `id`'s own `subLayers`/`subLayerOffsets`;
    /// `id`'s own `expressionVariables` do not contribute — only the stack root's do
    /// (C++ `PcpExpressionVariables`), and the caller has already folded them into
    /// `context`.
    fn resolve_edges(
        &self,
        id: LayerId,
        context: &HashMap<String, Value>,
        resolution: &mut HashMap<LayerId, HashMap<String, String>>,
    ) -> SublayerEdges {
        let root_path = Path::abs_root();
        let node = &self.nodes[&id];
        let Ok(Value::StringVec(sub_paths)) = node
            .layer
            .data()
            .get_field(&root_path, FieldKey::SubLayers.as_str())
            .map(|v| v.into_owned())
        else {
            return Vec::new();
        };
        let offsets: Vec<LayerOffset> = node
            .layer
            .data()
            .get_field(&root_path, FieldKey::SubLayerOffsets.as_str())
            .ok()
            .and_then(|v| match v.into_owned() {
                Value::LayerOffsetVec(v) => Some(v),
                _ => None,
            })
            .unwrap_or_default();

        let parent_tcps = effective_time_codes_per_second(&node.layer);
        let mut edges = Vec::with_capacity(sub_paths.len());
        for (i, sub_path) in sub_paths.into_iter().enumerate() {
            let sub_path = if expr::is_expression(&sub_path) {
                match expr::evaluate_asset_path(&sub_path, context) {
                    Ok(resolved) => resolved,
                    // An unevaluable expression resolves to no edge; the layer it
                    // would name is left out of the stack.
                    Err(_) => continue,
                }
            } else {
                sub_path
            };
            let Some(sub_id) = self.resolve_sublayer(id, &sub_path, resolution) else {
                continue;
            };
            let ratio = parent_tcps / effective_time_codes_per_second(&self.nodes[&sub_id].layer);
            let effective = offsets
                .get(i)
                .copied()
                .unwrap_or_default()
                .sanitized()
                .concatenate(&LayerOffset::scale_only(ratio));
            edges.push((sub_id, effective));
        }
        edges
    }

    /// Resolves an authored `subLayers` entry `sub_path` against its parent layer
    /// `parent` to the interned sublayer (the memoizing form of
    /// [`find_relative`](Self::find_relative) for the per-rebuild
    /// [`resolve_edges`](Self::resolve_edges) walk). The anchored identifier — the
    /// asset USD resolves the relative entry to — is tried first; only when no
    /// layer is interned there does it fall back to the bare authored string, so a
    /// filesystem-backed parent never resolves to an unrelated layer interned
    /// under the bare string, while an in-memory layer keyed under that literal
    /// name (no filesystem anchor) still resolves.
    ///
    /// The anchored identifier is a pure function of the asset paths, so it is
    /// memoized in `cache` whether or not it currently names an interned layer:
    /// the resolver's filesystem canonicalize then runs once per `(parent,
    /// sub_path)`, while the live [`id_of`](Self::id_of) below still tracks
    /// interning, so a target that interns on a later rebuild is picked up without
    /// re-resolving the path (see [`sublayer_resolution`](Self::sublayer_resolution)).
    fn resolve_sublayer(
        &self,
        parent: LayerId,
        sub_path: &str,
        cache: &mut HashMap<LayerId, HashMap<String, String>>,
    ) -> Option<LayerId> {
        let sub_path = without_dot_segments(sub_path);
        if let Some(anchored) = cache.get(&parent).and_then(|paths| paths.get(sub_path.as_ref())) {
            return self.anchored_or_bare(anchored, &sub_path);
        }
        let anchored = self
            .registry
            .create_identifier_anchored(&sub_path, self.real_path(parent));
        let sub_id = self.anchored_or_bare(&anchored, &sub_path);
        cache.entry(parent).or_default().insert(sub_path.into_owned(), anchored);
        sub_id
    }

    /// Replaces [`cycle_errors`](Self::cycle_errors) with the sublayer cycles
    /// reachable from the root layer through non-muted edges. Run after an edge
    /// rebuild and after a mute change, since muting a layer breaks any cycle
    /// running through it.
    fn recompute_cycle_errors(&mut self) {
        let mut errors = Vec::new();
        if let Some(root) = self.root {
            let mut ancestors: HashSet<LayerId> = HashSet::new();
            // Detect cycles over the same edges the root stack's members are built
            // from: a stack with an expression sublayer resolves against its single
            // variable set — the root instance's stored composed variables, which
            // `rebuild_sublayer_stacks` refreshed just before this runs — so a
            // `${VAR}` sublayer pointing back at the root or an ancestor is caught;
            // otherwise the context-free `children` are the root's edges.
            //
            // TODO(perf): a stage with an expression sublayer recomputes the root's
            // stack edges here after `rebuild_sublayer_stacks` already resolved them
            // for the members; threading the edge map through both would remove the
            // duplication.
            if self.has_expr_sublayer(root) {
                let mut resolution = mem::take(&mut self.sublayer_resolution);
                let stack_vars = self.stacks.expression_variables(LayerStackId::ROOT);
                let edges = self.compose_stack_edges(root, stack_vars, &mut resolution);
                self.sublayer_resolution = resolution;
                self.detect_cycles(
                    root,
                    |id| edges.get(&id).map_or(&[][..], |e| e.as_slice()),
                    &mut ancestors,
                    &mut errors,
                );
            } else {
                let nodes = &self.nodes;
                self.detect_cycles(
                    root,
                    |id| nodes.get(&id).map_or(&[][..], |n| n.children.as_slice()),
                    &mut ancestors,
                    &mut errors,
                );
            }
            // A sublayer reached twice off-path (a diamond) can report the same cycle
            // twice; report each physical `(root_layer, seen_layer)` pair once.
            let mut seen = HashSet::new();
            errors.retain(|error| match error {
                Error::SublayerCycle { root_layer, seen_layer } => {
                    seen.insert((root_layer.clone(), seen_layer.clone()))
                }
                _ => true,
            });
        }
        self.cycle_errors = errors;
    }

    /// Refreshes the registry's composed stacks from the current edges. Run after
    /// any edge mutation so [`layer_stack`](Self::layer_stack) and its callers read
    /// up-to-date members, keeping every [`LayerStackId`] stable so a handle held by
    /// a surviving prim index stays valid.
    ///
    /// The stage root stack (registry instance 0) and every already-interned target
    /// stack — plain and contextual — are re-resolved in place. A reference/payload
    /// target a `subLayers` edit cannot have minted yet is left for the demand path
    /// ([`intern_external`](Self::intern_external)). Work stays proportional to the
    /// composed stacks rather than the sum over every layer (O(n²) for a deep
    /// chain): a sublayer-only layer participates through its root's stack, never its
    /// own.
    fn rebuild_sublayer_stacks(&mut self, affected: Option<&HashSet<LayerId>>) {
        // Re-resolve the muted identifiers to ids first, so a layer muted before
        // it was loaded takes effect the moment a later edit interns it and
        // rebuilds the stacks.
        self.resolve_muted_ids();

        // The stage root stack (session layers at identity offset minus a muted
        // session subtree, then the root layer and its sublayers) is rebuilt on a
        // full pass, or when an edited layer is one of its members — an edit
        // elsewhere leaves it unchanged. A not-yet-built root (finalize) always
        // rebuilds.
        let rebuild_root = match affected {
            None => true,
            Some(affected) => self
                .stacks
                .member_set(LayerStackId::ROOT)
                .is_none_or(|members| !members.is_disjoint(affected)),
        };
        if rebuild_root {
            let pruned = self.muted_session_subtree();
            let mut root_members: Vec<(LayerId, LayerOffset)> = self
                .session_layers()
                .iter()
                .filter(|id| !pruned.contains(id))
                .map(|&id| (id, LayerOffset::IDENTITY))
                .collect();
            // The root layer is never muted (the Stage API rejects it). Its
            // `${VAR}` sublayers resolve against the session's composed
            // expression variables — the session is part of the root layer stack
            // — so seed the member computation with them: the root stack is a
            // contextual stack whose edges resolve fresh, not the context-free
            // shared `children`. `pruned` (the muted session subtree) is excluded
            // from those variables, matching the members filter above. With no
            // root layer, the stack's composed variables are the session's own.
            let session_vars = self.session_expression_variables();
            let (members, expr_vars) = match self.root {
                Some(root) => self.build_stack_members(root, &session_vars),
                None => (Vec::new(), session_vars),
            };
            root_members.extend(members);
            self.stacks.set_root(root_members, expr_vars);
        }

        // Re-resolve each already-interned target stack (plain and contextual)
        // whose members or composed variables an edited layer contributes to; a
        // full pass (`None`) re-resolves them all.
        for (id, root, vars) in self.stacks.target_rebuild_specs(affected) {
            let (members, expr_vars) = self.build_stack_members(root, &vars);
            self.stacks.set_composed(id, members, expr_vars);
        }
    }

    /// Mints a plain stack instance for every sublayer-DAG root that lacks one — a
    /// reference/payload target interned eagerly by `from_layers` rather than through
    /// the demand path. Run once at [`finalize`](Self::finalize): a production target
    /// loads after finalize and is minted by
    /// [`intern_external`](Self::intern_external) under its own context, so it never
    /// reaches here, and an edit-time recompose never re-mints a never-queried plain
    /// instance for a contextual-only target.
    fn mint_eager_target_stacks(&mut self) {
        let empty = self.stacks.empty_context();
        let sublayered: HashSet<LayerId> = self
            .order
            .iter()
            .flat_map(|&id| self.nodes[&id].children.iter().map(|&(child, _)| child))
            .collect();
        let dag_roots: Vec<LayerId> = self
            .order
            .iter()
            .copied()
            .filter(|&id| {
                !sublayered.contains(&id) && Some(id) != self.root && self.stacks.lookup_target(id, empty).is_none()
            })
            .collect();
        for root in dag_roots {
            let (members, expr_vars) = self.build_stack_members(root, &HashMap::new());
            self.stacks.intern_target(root, empty, members, expr_vars);
        }
    }

    /// The session-region ids muting removes from the root stack: every muted
    /// session layer plus the sublayer descendants it would otherwise carry in.
    /// The session prefix is a flat list, so unlike the root portion (built by
    /// the subtree-pruning [`collect_sublayers`]) it needs the subtree computed
    /// explicitly. Descendants are confined to the session region.
    fn muted_session_subtree(&self) -> HashSet<LayerId> {
        // The common no-mute case allocates nothing and walks nothing. This runs
        // on every stack rebuild (every `subLayers` edit, not just mutes).
        if self.muted.is_empty() {
            return HashSet::new();
        }
        let session: HashSet<LayerId> = self.session_layers().iter().copied().collect();
        let muted_roots = session.iter().copied().filter(|&id| self.is_muted(id));
        // A muted session layer carries in the session descendants its `${VAR}`
        // sublayers resolve to, so the subtree is walked over the session's real
        // edges — the context-free `children` drop every expression sublayer. The
        // session region resolves against the root stack's structural variables (the
        // stage root layer's own overlaid by the session root's own, read regardless
        // of muting), the same set the loader opened it with: muting removes a subtree
        // without changing which layers compose it.
        let session_vars = self.root_stack_structural_vars();
        // TODO(perf): this uses a scratch resolution map and resolves every session
        // layer, where the walk only needs those reachable from a muted root. Passing
        // the shared `sublayer_resolution` cache (this method's only caller,
        // `rebuild_sublayer_stacks`, holds `&mut self`) would skip re-canonicalizing
        // paths already resolved, and resolving lazily from the muted roots would skip
        // the unreachable layers. It runs only on an edit while a layer is muted, over
        // the small session region, so neither is pressing.
        let mut resolution = HashMap::new();
        let session_edges: HashMap<LayerId, Vec<LayerId>> = session
            .iter()
            .map(|&id| {
                let children = self
                    .resolve_edges(id, &session_vars, &mut resolution)
                    .into_iter()
                    .map(|(child, _)| child)
                    .collect();
                (id, children)
            })
            .collect();
        muted_subtree(&session, muted_roots, |id| {
            session_edges.get(id).cloned().unwrap_or_default()
        })
    }

    /// Depth-first cycle scan recording [`Error::SublayerCycle`] for any edge
    /// that re-enters a layer already on the path from the root. Runs on an
    /// explicit work stack so a deep chain does not overflow the native stack; an
    /// `Exit` frame pops the layer back out of the `ancestors` path after its
    /// subtree. `children_of` supplies a layer's resolved edges — the shared
    /// context-free [`LayerNode::children`], or a stack's expression-resolved edges
    /// — and a sublayer diamond re-scans off-path rather than looking like a cycle.
    fn detect_cycles<'e>(
        &self,
        root: LayerId,
        children_of: impl Fn(LayerId) -> &'e [(LayerId, LayerOffset)],
        ancestors: &mut HashSet<LayerId>,
        errors: &mut Vec<Error>,
    ) {
        enum Step {
            Enter(LayerId),
            Exit(LayerId),
        }
        let mut work = vec![Step::Enter(root)];
        while let Some(step) = work.pop() {
            let id = match step {
                Step::Exit(id) => {
                    ancestors.remove(&id);
                    continue;
                }
                Step::Enter(id) => id,
            };
            ancestors.insert(id);
            work.push(Step::Exit(id));
            // Iterate forward to record cycle errors in declared order, gathering
            // the non-cycle children; they are pushed reversed so they pop in
            // declared order.
            let mut to_visit = Vec::new();
            for &(child, _) in children_of(id) {
                // A muted child is pruned from every stack, so a cycle through it
                // never composes and is not reported.
                if self.is_muted(child) {
                    continue;
                }
                if ancestors.contains(&child) {
                    errors.push(Error::SublayerCycle {
                        root_layer: self.nodes[&id].layer.identifier().to_string(),
                        seen_layer: self.nodes[&child].layer.identifier().to_string(),
                    });
                    continue;
                }
                to_visit.push(child);
            }
            for &child in to_visit.iter().rev() {
                work.push(Step::Enter(child));
            }
        }
    }

    /// Read-only access to a layer node.
    pub(crate) fn get(&self, id: LayerId) -> Option<&LayerNode> {
        self.nodes.get(&id)
    }

    /// Mutable access to a layer node, for routed authoring writes.
    pub(crate) fn get_mut(&mut self, id: LayerId) -> Option<&mut LayerNode> {
        self.nodes.get_mut(&id)
    }

    /// Borrow the layers named by `ids` together, in `ids` order, skipping any
    /// id with no live layer. Used to open a transaction on each layer of a
    /// batched edit so they commit all-or-nothing.
    pub(crate) fn layers_mut(&mut self, ids: &[LayerId]) -> Vec<(LayerId, &mut sdf::Layer)> {
        let want: HashSet<LayerId> = ids.iter().copied().collect();
        let mut by_id: HashMap<LayerId, &mut sdf::Layer> = self
            .nodes
            .iter_mut()
            .filter(|(id, _)| want.contains(id))
            .map(|(id, node)| (*id, &mut node.layer))
            .collect();
        ids.iter()
            .filter_map(|id| by_id.remove(id).map(|layer| (*id, layer)))
            .collect()
    }

    /// The layer with the given id. Panics if the id is unknown.
    pub(crate) fn layer(&self, id: LayerId) -> &sdf::Layer {
        &self.nodes[&id].layer
    }

    /// The identifier of the layer with the given id. Panics if unknown.
    pub(crate) fn identifier(&self, id: LayerId) -> &str {
        self.nodes[&id].layer.identifier()
    }

    /// The resolved physical location of the layer with the given id — the
    /// anchor for the relative asset paths it authors (C++
    /// `SdfLayer::GetRealPath`). Equals the identifier except for a package,
    /// whose real path is its package-relative default layer. Panics if
    /// unknown.
    pub(crate) fn real_path(&self, id: LayerId) -> &str {
        self.nodes[&id].layer.real_path()
    }

    /// Whether a layer with this id is present.
    pub(crate) fn contains(&self, id: LayerId) -> bool {
        self.nodes.contains_key(&id)
    }

    /// The registry that opens reference/payload targets on demand.
    pub(crate) fn layer_registry(&self) -> &sdf::LayerRegistry {
        &self.registry
    }

    /// The location that anchors the relative asset paths authored in the layer
    /// `anchor`: its resolved [`real_path`](Self::real_path), recorded when the
    /// loader opened it. Returns `None` when there is no anchor layer or it is
    /// anonymous (no resolvable location, C++ `SdfLayer::GetRealPath` is
    /// empty).
    pub(crate) fn anchor_location(&self, anchor: Option<LayerId>) -> Option<ResolvedPath> {
        let layer = &self.nodes[&anchor?].layer;
        (!layer.is_anonymous()).then(|| ResolvedPath::new(layer.real_path()))
    }

    /// Records that the layer at `asset_path` resolved but could not be read or
    /// parsed (`reason`), so composition stops demanding it and reports it
    /// [`MalformedLayer`](Error::MalformedLayer). Called from the stage's load
    /// barrier when an on-demand open fails.
    pub(crate) fn mark_load_failed(&mut self, asset_path: &str, reason: String) {
        self.failed_loads.insert(asset_path.to_string(), reason);
    }

    /// The layer stack a reference/payload arc to external `root` should compose
    /// against, given the arc-carrying stack `context` — whose composed
    /// expression variables are the arc's full inherited context. Every target
    /// stack is keyed by that context, so this is a plain `(root, seed)` lookup
    /// on its interned id. Read-only: the indexer runs against `&LayerGraph`
    /// and cannot mint, so a not-yet-built stack returns
    /// [`ExternalStack::Demand`] for the load barrier to resolve through
    /// [`intern_external`](Self::intern_external).
    pub(crate) fn external_stack_id(&self, root: LayerId, context: LayerStackId) -> ExternalStack {
        self.resolve_target_stack(root, self.stacks.expr_id(context))
    }

    /// The `(root, seed)` resolve policy shared by the read path
    /// ([`external_stack_id`](Self::external_stack_id)) and the mint path
    /// ([`intern_target_stack`](Self::intern_target_stack)): collapse to the
    /// root stack when the context is the root stack's own
    /// ([`collapses_to_root`](Self::collapses_to_root)), else the interned
    /// `(root, seed)` instance, else [`ExternalStack::Demand`].
    fn resolve_target_stack(&self, root: LayerId, seed: ExprVarId) -> ExternalStack {
        if self.collapses_to_root(root, seed) {
            return ExternalStack::Ready(LayerStackId::ROOT);
        }
        match self.stacks.lookup_target(root, seed) {
            Some(id) => ExternalStack::Ready(id),
            None => ExternalStack::Demand,
        }
    }

    /// Whether an arc to `root` under the context `seed` composes against the stage
    /// root stack itself: the target is the stage root layer, no session layers
    /// separate the two identities (C++ `PcpLayerStackIdentifier` equality), and
    /// the arriving context is exactly the root stack's own composed context (an
    /// id comparison — an indexer-originated context is the arc-carrying stack's
    /// composed set, so a back-reference from inside the root stack matches).
    /// A differing context — a back-reference through a stack that authored its
    /// own variables — instead mints a contextual instance rooted at the stage
    /// root layer, keeping the outer variables in force. The id check is
    /// sufficient, not necessary: an authoring query may supply a context that
    /// composes to the root's set without being it, minting a duplicate-identity
    /// instance whose members and variables equal the root stack's — harmless, and
    /// rebuilt uniformly with every other target.
    fn collapses_to_root(&self, root: LayerId, seed: ExprVarId) -> bool {
        self.session_layer_count == 0 && self.root == Some(root) && seed == self.stacks.expr_id(LayerStackId::ROOT)
    }

    /// Builds and interns the layer stack for a reference/payload arc to `root`
    /// demanded under the context of the stack `context` (the `&mut self`
    /// counterpart to [`external_stack_id`](Self::external_stack_id)), returning
    /// its handle and whether a new instance was created so the load barrier can
    /// drive a re-run. Idempotent. Called from the load barrier once the target
    /// and the sublayers its context resolves have been interned.
    pub(crate) fn intern_external(&mut self, root: LayerId, context: LayerStackId) -> (LayerStackId, bool) {
        self.intern_target_stack(root, self.stacks.expr_id(context))
    }

    /// Whether the load barrier must (re)open `root`'s sublayers for a
    /// reference/payload demanded under the context of the stack `context`: the
    /// inherited context selects a contextual stack that is not yet built, so its
    /// `${VAR}` sublayers — possibly nested below a literal sublayer an earlier
    /// context left unopened — need loading. A context-free arc, a target with no
    /// `${VAR}` sublayer (a keying-only demand the barrier interns without
    /// reloading), or a context already built needs no reopen.
    ///
    /// The stage's own root layer is never reopened: its stack is already loaded,
    /// and the layer may be in-memory or carry unsaved edits a disk re-read would
    /// discard. A back-reference to it interns from the loaded graph; a `${VAR}`
    /// sublayer its carried context newly selects stays subject to the runtime
    /// variable-selected sublayer limitation (see the module docs).
    pub(crate) fn needs_contextual_open(&self, root: LayerId, context: LayerStackId) -> bool {
        self.root != Some(root)
            && !self.stacks.expression_variables(context).is_empty()
            && self.has_expr_sublayer(root)
            && matches!(self.external_stack_id(root, context), ExternalStack::Demand)
    }

    /// The inherited expression-variable context the stack `id` resolved against —
    /// empty for the root stack and for a context-free target. Captured into an
    /// edit target so authoring reconstructs the same contextual stack later.
    pub(crate) fn stack_seed_vars(&self, id: LayerStackId) -> HashMap<String, Value> {
        self.stacks.instance_seed_vars(id)
    }

    /// The handle for the stack rooted at `root` under the explicit variable map
    /// `vars`, interning it if it has not been composed yet — for an authoring
    /// query (an edit target reconstructing a captured context) that must resolve
    /// to the exact stack rather than a fallback.
    pub(crate) fn ensure_external_stack(&mut self, root: LayerId, vars: &HashMap<String, Value>) -> LayerStackId {
        let seed = self.stacks.intern_context(vars);
        self.intern_target_stack(root, seed).0
    }

    /// The single mint policy for an external target stack: resolve through the
    /// shared policy ([`resolve_target_stack`](Self::resolve_target_stack)) and,
    /// on [`ExternalStack::Demand`], compose the members and variables under the
    /// seed and intern a fresh instance. Distinct contexts to the same target
    /// intern distinct instances even when their members are identical — the
    /// instance carries the context, so sharing would drop it.
    fn intern_target_stack(&mut self, root: LayerId, seed: ExprVarId) -> (LayerStackId, bool) {
        if let ExternalStack::Ready(id) = self.resolve_target_stack(root, seed) {
            return (id, false);
        }
        let seed_vars = self.stacks.context_vars(seed);
        let (members, expr_vars) = self.build_stack_members(root, &seed_vars);
        (self.stacks.intern_target(root, seed, members, expr_vars), true)
    }

    /// Whether any layer in `root`'s plain sublayer subtree authors an
    /// expression-valued `${VAR}` `subLayers` entry — the only sublayer whose
    /// resolution depends on the expression-variable context inherited across a
    /// reference/payload arc. The load barrier reads this to decide whether a
    /// demanded context must (re)open the target's sublayers
    /// ([`needs_contextual_open`](Self::needs_contextual_open)), and
    /// [`stack_members_uncached`](Self::stack_members_uncached) to gate a stack
    /// onto the context-free `collect_plain` fast path. The whole subtree is
    /// scanned so an expression sublayer nested below the target root — under a
    /// literal sublayer — is still caught.
    ///
    /// The walk reads the current [`LayerNode::children`] rather than a registry
    /// stack's interned members: those members can predate the edit driving a stack
    /// rebuild (they are replaced only after every stack is recomposed), so scanning
    /// them would miss a freshly added expression branch and wrongly gate the stack
    /// onto `collect_plain`. The children (and the per-node flags) are already
    /// rebuilt by [`build_sublayer_edges`](Self::build_sublayer_edges) before the
    /// rebuild reads this. Muted layers (and any subtree reached only through them)
    /// are skipped, matching the composed members: an expression sublayer that
    /// mutes out contributes nothing, so a demand for a target that only reaches
    /// one skips the reopen. [`any_expr_sublayer`](Self::any_expr_sublayer)
    /// short-circuits the common stage with no expression sublayer at all to
    /// `O(1)`.
    //
    // TODO(perf): this runs a fresh subtree walk (allocating a work stack + visited
    // set) per empty-seed stack rebuilt in `rebuild_sublayer_stacks` once any layer
    // authors an expression sublayer. A transitive per-node "subtree authors one"
    // flag computed with the local flags would make it an `O(1)` field read.
    pub(crate) fn has_expr_sublayer(&self, root: LayerId) -> bool {
        if !self.any_expr_sublayer {
            return false;
        }
        let mut work = vec![root];
        let mut visited = HashSet::new();
        while let Some(id) = work.pop() {
            if self.is_muted(id) || !visited.insert(id) {
                continue;
            }
            let Some(node) = self.nodes.get(&id) else { continue };
            if node.has_expr_sublayer {
                return true;
            }
            work.extend(node.children.iter().map(|&(child, _)| child));
        }
        false
    }

    /// Recomputes the exact [`LayerNode::has_expr_sublayer`] flags and their
    /// graph-level union [`any_expr_sublayer`](Self::any_expr_sublayer) from each
    /// layer's own `subLayers`. Run on every edge rebuild so an edit that adds or
    /// removes the last expression `subLayers` entry is reflected exactly.
    //
    // TODO(perf): this re-decodes each layer's `subLayers`, which `resolve_edges`
    // already decodes (and already runs `is_expression` over) in the same
    // `build_sublayer_edges` pass. Returning the flag from `resolve_edges` and
    // folding it in as `children` are applied would drop this second decode.
    fn recompute_expr_sublayer_flags(&mut self) {
        let root_path = Path::abs_root();
        let mut any = false;
        for node in self.nodes.values_mut() {
            let has = matches!(
                node.layer.data().get_field(&root_path, FieldKey::SubLayers.as_str()),
                Ok(subs) if matches!(&*subs, Value::StringVec(paths) if paths.iter().any(|p| expr::is_expression(p)))
            );
            node.has_expr_sublayer = has;
            any |= has;
        }
        self.any_expr_sublayer = any;
    }

    /// The cached composer for a rebuild: composes the stack's expression
    /// variables ([`composed_stack_vars`](Self::composed_stack_vars)), then
    /// expands members against them via the [`stack_members_uncached`] policy
    /// with the graph's shared sublayer-resolution cache threaded through, so a
    /// `subLayers` edit only re-canonicalizes paths it has not seen before.
    /// Returns both so the caller stores them on the stack instance together.
    /// Read-only queries call [`stack_members_uncached`] directly with a scratch
    /// cache ([`sublayer_stack`]).
    ///
    /// [`stack_members_uncached`]: Self::stack_members_uncached
    /// [`sublayer_stack`]: Self::sublayer_stack
    fn build_stack_members(
        &mut self,
        root: LayerId,
        seed_vars: &HashMap<String, Value>,
    ) -> (Vec<(LayerId, LayerOffset)>, HashMap<String, Value>) {
        let stack_vars = self.composed_stack_vars(root, seed_vars);
        let mut resolution = mem::take(&mut self.sublayer_resolution);
        let members = self.stack_members_uncached(root, &stack_vars, &mut resolution);
        self.sublayer_resolution = resolution;
        (members, stack_vars)
    }

    /// The composed expression variables of a stack rooted at `root` under
    /// `seed_vars`: the root layer's own `expressionVariables` overlaid by the
    /// seed, the seed winning (C++ `PcpExpressionVariables`). The loader
    /// validated the `expressionVariables` read at open time; this
    /// composition-time read of the same already-loaded layer cannot abort, so
    /// an unreadable field degrades to no variables.
    fn composed_stack_vars(&self, root: LayerId, seed_vars: &HashMap<String, Value>) -> HashMap<String, Value> {
        expr::stack_expression_variables(self.nodes[&root].layer.data(), seed_vars).unwrap_or_default()
    }

    /// The single member-expansion policy for every "stack rooted at `root` under
    /// the composed variables `stack_vars`" query, cached
    /// ([`build_stack_members`](Self::build_stack_members)) or on demand
    /// ([`sublayer_stack`](Self::sublayer_stack)): resolves `root`'s subtree and
    /// composes offsets, pruning muted layers, sharing [`collect_sublayers`].
    ///
    /// A stack with no expression sublayer ([`has_expr_sublayer`](Self::has_expr_sublayer)
    /// false) walks the shared context-free [`LayerNode::children`], resolved once
    /// per `subLayers` edit. A stack with one re-resolves its subtree against
    /// `stack_vars` ([`compose_stack_edges`](Self::compose_stack_edges)) so every
    /// `${VAR}` sublayer resolves the same way throughout the stack (C++
    /// `PcpExpressionVariables`). `resolution` memoizes sublayer path
    /// canonicalization — the graph's cache on a rebuild, a scratch map on a read
    /// query.
    fn stack_members_uncached(
        &self,
        root: LayerId,
        stack_vars: &HashMap<String, Value>,
        resolution: &mut HashMap<LayerId, HashMap<String, String>>,
    ) -> Vec<(LayerId, LayerOffset)> {
        if !self.has_expr_sublayer(root) {
            return self.collect_plain(root);
        }
        let edges = self.compose_stack_edges(root, stack_vars, resolution);
        let muted = &self.muted;
        let mut members = Vec::new();
        let mut ancestors = HashSet::new();
        collect_sublayers(
            root,
            LayerOffset::IDENTITY,
            &mut members,
            &mut ancestors,
            |id| muted.contains(&id),
            |id| edges.get(&id).map_or(&[][..], |e| e.as_slice()),
        );
        members
    }

    /// Resolves the sublayer edges of the stack rooted at `root` against
    /// `stack_vars`, the stack's single composed expression-variable set, into a
    /// per-`LayerId` edge map. Every `${VAR}` sublayer in the stack resolves
    /// against that one set (C++ `PcpExpressionVariables`); a sublayer's own
    /// `expressionVariables` contribute nothing. Unlike the shared context-free
    /// [`LayerNode::children`], these edges carry the stack's variables.
    /// `resolution` memoizes sublayer path canonicalization.
    fn compose_stack_edges(
        &self,
        root: LayerId,
        stack_vars: &HashMap<String, Value>,
        resolution: &mut HashMap<LayerId, HashMap<String, String>>,
    ) -> HashMap<LayerId, SublayerEdges> {
        let mut edges: HashMap<LayerId, SublayerEdges> = HashMap::new();
        let mut visited: HashSet<LayerId> = HashSet::new();
        let mut work = vec![root];
        while let Some(id) = work.pop() {
            if !visited.insert(id) {
                continue;
            }
            let resolved = self.resolve_edges(id, stack_vars, resolution);
            for &(child, _) in resolved.iter().rev() {
                work.push(child);
            }
            edges.insert(id, resolved);
        }
        edges
    }

    /// The session layer's own `expressionVariables` — the overrides the root stage
    /// stack composes over the stage root layer's own (C++ `PcpExpressionVariables`
    /// reads the root and session layers, not their sublayers). Seeds the root
    /// layer's `${VAR}` sublayer resolution (see
    /// [`rebuild_sublayer_stacks`](Self::rebuild_sublayer_stacks)). Empty when the
    /// session root authors none, the common case that keeps the root on the
    /// sessionless path.
    ///
    /// The session root is the first session layer; a muted session root contributes
    /// nothing, matching the members the root stack drops. The session root is
    /// `order[0]`, the top of the session region, so muting drops it exactly when it
    /// is itself muted.
    fn session_expression_variables(&self) -> HashMap<String, Value> {
        match self.session_layers().first() {
            Some(&session_root) if !self.is_muted(session_root) => {
                expr::read_expression_variables(self.nodes[&session_root].layer.data())
                    .map(|dict| dict.into_owned())
                    .unwrap_or_default()
            }
            _ => HashMap::new(),
        }
    }

    /// The stage root stack's expression variables read regardless of muting: the
    /// stage root layer's own overlaid by the session root's own (session wins). The
    /// structural walks — [`muted_session_subtree`](Self::muted_session_subtree) and
    /// [`expression_ancestry_edges`](Self::expression_ancestry_edges) — resolve the
    /// root stage stack's `${VAR}` sublayers against this one set (both regions of a
    /// single stack, C++ `PcpExpressionVariables`), so muting a layer leaves the walk's
    /// edges unchanged: the ancestor/subtree set is identical before a mute and after
    /// the matching unmute. The composition context a muted session root drops out of
    /// is [`stack_expression_variables`](Self::stack_expression_variables).
    fn root_stack_structural_vars(&self) -> HashMap<String, Value> {
        let session = match self.session_layers().first() {
            Some(&session_root) => expr::read_expression_variables(self.nodes[&session_root].layer.data())
                .map(|dict| dict.into_owned())
                .unwrap_or_default(),
            None => HashMap::new(),
        };
        match self.root {
            Some(root) => {
                expr::stack_expression_variables(self.nodes[&root].layer.data(), &session).unwrap_or_default()
            }
            None => session,
        }
    }

    /// The composed expression variables of the layer stack `id` (C++
    /// `PcpExpressionVariables`, stored on the stack like C++
    /// `PcpLayerStack::GetExpressionVariables`): its root layer's own
    /// `expressionVariables` overlaid by the inherited overrides — the arc's seed
    /// for a target, the session root's own for the stage root stack. This is the
    /// single set the stack's `${VAR}` sublayer paths, reference/payload asset
    /// paths, and value-time asset attributes all resolve against; a sublayer of
    /// the root contributes nothing. The same value the stack's members were
    /// resolved with ([`build_stack_members`](Self::build_stack_members)), so
    /// membership and asset-path resolution never diverge. Panics on an unminted
    /// handle — composition only reads stacks the graph has built.
    pub(crate) fn stack_expression_variables(&self, id: LayerStackId) -> &HashMap<String, Value> {
        self.stacks.expression_variables(id)
    }

    /// The context-free members of the stack rooted at `root`, composing offsets and
    /// pruning muted layers over the shared [`LayerNode::children`]. The fast path
    /// [`stack_members_uncached`](Self::stack_members_uncached) takes when the stack
    /// has no expression sublayer ([`has_expr_sublayer`](Self::has_expr_sublayer)).
    fn collect_plain(&self, root: LayerId) -> Vec<(LayerId, LayerOffset)> {
        let muted = &self.muted;
        let nodes = &self.nodes;
        let mut members = Vec::new();
        let mut ancestors = HashSet::new();
        collect_sublayers(
            root,
            LayerOffset::IDENTITY,
            &mut members,
            &mut ancestors,
            |id| muted.contains(&id),
            |id| nodes.get(&id).map_or(&[][..], |n| n.children.as_slice()),
        );
        members
    }

    /// Whether a prior on-demand open of `asset_path` failed to read or parse the
    /// target layer.
    pub(crate) fn load_failed(&self, asset_path: &str) -> bool {
        self.failed_loads.contains_key(asset_path)
    }

    /// The read/parse error from a prior failed on-demand open of `asset_path`,
    /// or `None` if it never failed.
    pub(crate) fn load_failure_reason(&self, asset_path: &str) -> Option<&str> {
        self.failed_loads.get(asset_path).map(String::as_str)
    }

    /// Forgets every recorded load failure so a now-readable asset is demanded
    /// again, returning whether any were recorded. Called when an edit changes
    /// the layers.
    pub(crate) fn clear_failed_loads(&mut self) -> bool {
        if self.failed_loads.is_empty() {
            return false;
        }
        self.failed_loads.clear();
        true
    }

    /// Whether any layer keeps structurally valid authored relocates.
    pub(crate) fn has_relocates(&self) -> bool {
        self.has_relocates
    }

    /// Number of layers in the graph.
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the graph has no layers.
    #[allow(dead_code)]
    pub(crate) fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Number of session layers.
    pub(crate) fn session_layer_count(&self) -> usize {
        self.session_layer_count
    }

    /// The session-layer ids in strength order.
    pub(crate) fn session_layers(&self) -> &[LayerId] {
        &self.order[..self.session_layer_count]
    }

    /// The root layer's id (the first non-session layer), if any.
    pub(crate) fn root_id(&self) -> Option<LayerId> {
        self.root
    }

    /// The root layer (the first non-session layer), if any. Per spec 12.2.7,
    /// pseudo-root layer metadata resolves from this layer alone.
    pub(crate) fn root_layer(&self) -> Option<&sdf::Layer> {
        self.root.map(|id| self.layer(id))
    }

    /// All layer ids in collection order (session layers first).
    pub(crate) fn all_ids(&self) -> &[LayerId] {
        &self.order
    }

    /// Layer identifiers in collection order (root-stack first).
    pub(crate) fn identifiers(&self) -> Vec<String> {
        self.identifiers_of(self.order.iter().copied())
    }

    /// Maps a sequence of layer ids to their identifiers, in order.
    pub(crate) fn identifiers_of(&self, ids: impl IntoIterator<Item = LayerId>) -> Vec<String> {
        ids.into_iter().map(|id| self.identifier(id).to_string()).collect()
    }

    /// The identifiers of the stage's root layer stack (session layers, the root
    /// layer, and its sublayers) in strength order. Backs C++
    /// `UsdStage::GetLayerStack`.
    pub(crate) fn root_layer_stack_identifiers(&self) -> Vec<String> {
        self.identifiers_of(self.root_layer_stack().iter().map(|&(id, _)| id))
    }

    /// The layer ids + effective offsets of the plain sublayer stack rooted at
    /// `root_layer` (spec 10.3.1.1) — its sublayer edges resolved with no inherited
    /// expression-variable context (the layer's own `expressionVariables` still
    /// apply), the depth-first pre-order walk with offsets composed through nested
    /// sublayers. A layer that sublayers itself transitively is a cycle and is
    /// skipped; an off-path duplicate is expanded again. Empty for an unknown layer.
    ///
    /// The empty-seed query goes through the same expansion policy as a rebuilt
    /// stack ([`stack_members_uncached`](Self::stack_members_uncached)): it reads the
    /// registry's interned plain instance when one exists, and otherwise composes on
    /// demand with a scratch resolution cache — so a sublayer diamond whose shared
    /// layer resolves `${VAR}` differently per arm expands per ancestry here exactly
    /// as it does in the interned members. Because the seed is empty, a variable a
    /// layer inherits only from a parent that sublayers it is not in scope — those
    /// members appear in the parent's stack, not in the layer's own.
    pub(crate) fn sublayer_stack(&self, root_layer: LayerId) -> Cow<'_, [(LayerId, LayerOffset)]> {
        if let Some(id) = self.stacks.lookup_target(root_layer, self.stacks.empty_context()) {
            return Cow::Borrowed(self.stacks.members(id));
        }
        if !self.nodes.contains_key(&root_layer) {
            return Cow::Borrowed(&[]);
        }
        // Only a `${VAR}` sublayer reads the stack's variables — with no
        // inherited context they are the root layer's own; the plain fast path
        // never touches them.
        let stack_vars = if self.has_expr_sublayer(root_layer) {
            self.composed_stack_vars(root_layer, &HashMap::new())
        } else {
            HashMap::new()
        };
        let mut resolution = HashMap::new();
        Cow::Owned(self.stack_members_uncached(root_layer, &stack_vars, &mut resolution))
    }

    /// The stage's root layer stack (registry instance 0): session layers (identity
    /// offset) followed by the root layer and its sublayers with their effective
    /// offsets (spec 10.3.1). The set of layers a top-level prim index scans for
    /// local opinions.
    pub(crate) fn root_layer_stack(&self) -> &[(LayerId, LayerOffset)] {
        self.stacks.members(LayerStackId::ROOT)
    }

    /// The handle for the stage root layer stack, the ambient a top-level prim
    /// composes against.
    pub(crate) fn root_layer_stack_id(&self) -> LayerStackId {
        LayerStackId::ROOT
    }

    /// Resolves a [`LayerStackId`] back to its members (the `(layer id, effective
    /// offset)` pairs in strength order) from the registry. Empty for a stack whose
    /// root is unknown or muted.
    pub(crate) fn layer_stack(&self, id: LayerStackId) -> &[(LayerId, LayerOffset)] {
        self.stacks.members(id)
    }

    /// The strongest (representative) layer of the stack `id` — its
    /// [`layer_stack`](Self::layer_stack)'s first member — or [`LayerId::INVALID`]
    /// when the stack is empty (an unknown or muted root).
    pub(crate) fn layer_stack_root(&self, id: LayerStackId) -> LayerId {
        self.stacks
            .members(id)
            .first()
            .map(|&(li, _)| li)
            .unwrap_or(LayerId::INVALID)
    }

    /// Whether the stack `id` is the stage root layer stack.
    pub(crate) fn is_root_stack(&self, id: LayerStackId) -> bool {
        self.stacks.is_root(id)
    }

    /// The reference/payload target a non-root stack `id` is rooted at, used to name
    /// the authoring stack for an edit target.
    pub(crate) fn stack_target_root(&self, id: LayerStackId) -> LayerId {
        self.stacks.target_root(id)
    }

    /// The layer ids of the stage's root layer stack, as a set (C++ "local"
    /// layers, spec 12.3.4.5). Opinions from these outrank value-clip data.
    pub(crate) fn local_layers(&self) -> HashSet<LayerId> {
        self.stacks.member_set(LayerStackId::ROOT).cloned().unwrap_or_default()
    }

    /// Rebuilds the sublayer edges and relocate data from the current layer
    /// data, refreshing both [`cycle_errors`](Self::cycle_errors) and
    /// [`relocate_errors`](Self::relocate_errors). Called after a
    /// `subLayers`/`subLayerOffsets` edit, where the graph's edges may be stale.
    ///
    /// `edited` names the layers whose root metadata the edit authored; together
    /// with the edges the rebuild finds changed, it scopes the stack re-resolution
    /// to the instances the change can affect. Pass `None` for a load, where a
    /// newly opened layer can join a stack the changed-edge set cannot name, so
    /// every stack is re-resolved.
    ///
    /// Returns the affected layer set the caller drops cached indices against: the
    /// layers whose composed edges shifted (unioned with `edited`) plus those whose
    /// relocate pairs changed, so eviction covers exactly the stacks the rebuild
    /// re-resolved. Empty when `edited` is `None` apart from the relocate set (a
    /// full pass scopes nothing).
    pub(crate) fn recompute_sublayers(&mut self, edited: Option<&HashSet<LayerId>>) -> HashSet<LayerId> {
        let mut affected = self.build_sublayer_edges(edited).unwrap_or_default();
        affected.extend(self.recompute_relocates());
        affected
    }

    /// Re-derives every node's structurally valid relocate pairs from its
    /// current layer data, replacing [`relocate_errors`](Self::relocate_errors)
    /// with the recoverable relocate diagnostics (C++
    /// `PcpErrorInvalidAuthoredRelocates` and conflict diagnostics). Run once at
    /// construction and again whenever a `subLayers`/`layerRelocates` edit
    /// lands.
    ///
    /// Returns the layers whose cached relocate pairs changed, so a mute toggle
    /// can fan out to the prims reading them (see
    /// [`recompose_for_mute_with_fanout`](Self::recompose_for_mute_with_fanout))
    /// without a separate before/after snapshot. Validation reads only authored
    /// layer data, so each layer's new pairs are moved out of `relocates` into
    /// the node cache.
    pub(crate) fn recompute_relocates(&mut self) -> HashSet<LayerId> {
        let (mut relocates, errors) = validate_layer_relocates(self);
        self.has_relocates = false;
        let mut changed = HashSet::new();
        for &id in &self.order {
            let pairs = relocates.remove(&id).unwrap_or_default();
            self.has_relocates |= !pairs.is_empty();
            let node = self.nodes.get_mut(&id).expect("layer node exists");
            if node.relocates != pairs {
                changed.insert(id);
            }
            node.relocates = pairs;
        }
        self.relocate_errors = errors;
        changed
    }

    /// The current layer-graph diagnostics — sublayer cycles
    /// ([`cycle_errors`](Self::cycle_errors)) followed by relocate errors
    /// ([`relocate_errors`](Self::relocate_errors)). Always reflects the present
    /// graph state: a fixed cycle or relocate stops appearing and a recompute
    /// never duplicates one, since each bucket is replaced wholesale on rebuild.
    pub(crate) fn errors(&self) -> Vec<Error> {
        self.cycle_errors.iter().chain(&self.relocate_errors).cloned().collect()
    }

    /// The ordered layer-id stacks, one per sublayer stack (one rooted at each
    /// layer) plus the stage root stack. Used to scope relocate conflicts and
    /// duplicate-source strength to a single layer stack (C++
    /// `Pcp_ComputeRelocationsForLayerStack`).
    pub(crate) fn relocate_conflict_scopes(&self) -> Vec<Vec<LayerId>> {
        let mut scopes: Vec<Vec<LayerId>> = self
            .order
            .iter()
            .map(|&id| self.sublayer_stack(id).iter().map(|&(layer, _)| layer).collect())
            .collect();
        scopes.push(self.root_layer_stack().iter().map(|&(id, _)| id).collect());
        scopes
    }

    /// The relocation source for `target` if a layer in `ambient` relocates a
    /// prim onto it (C++ `GetIncrementalRelocatesTargetToSource`). The strongest
    /// layer wins a collision; a deletion relocate has no target and is skipped.
    pub(crate) fn relocation_source(&self, ambient: LayerStackId, target: &Path) -> Option<Path> {
        self.incremental_relocate_entries(ambient)
            .into_iter()
            .find_map(|(source, relocate_target, _)| {
                (!relocate_target.is_empty() && relocate_target == *target).then_some(source)
            })
    }

    /// The relocation [`MapFunction`] applying at `path` in the layer stack
    /// `ambient` (C++ `PcpLayerStack::GetExpressionForRelocatesAtPath`): every
    /// relocate whose source lies at or below `path`, chained, plus the `(/, /)`
    /// identity catch-all. `None` when no relocate affects `path`. `exclude_source`
    /// drops the relocate whose source is exactly that path.
    pub(crate) fn relocates_expression_at(
        &self,
        ambient: LayerStackId,
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

    /// The stack-effective relocates of `ambient`, strongest layer first, after
    /// duplicate-source and conflict dropping (C++ `GetIncrementalRelocates*`).
    /// Not chained.
    fn incremental_relocate_entries(&self, ambient: LayerStackId) -> Vec<(Path, Path, LayerId)> {
        let mut entries: Vec<(Path, Path, LayerId)> = Vec::new();
        for &(layer, _) in self.layer_stack(ambient).iter() {
            let Some(node) = self.nodes.get(&layer) else {
                continue;
            };
            for (source, target) in &node.relocates {
                entries.push((source.clone(), target.clone(), layer));
            }
        }
        let pairs: RelocateList = entries
            .iter()
            .map(|(source, target, _)| (source.clone(), target.clone()))
            .collect();
        let status = analyze_relocate_occurrences(&pairs);
        entries
            .into_iter()
            .zip(status)
            .filter_map(|(entry, status)| status.is_active().then_some(entry))
            .collect()
    }

    /// Chains the per-layer authored relocates of `ambient` into a single
    /// source→target map (C++ `GetRelocatesSourceToTarget`): a target that is
    /// itself a relocation source follows on to the final target, and a relocate
    /// authored *under* another's target contributes a combined
    /// pre-relocation-source → final-target pair so a single map application
    /// reaches the final location through nested relocates.
    pub(crate) fn combined_relocates(&self, ambient: LayerStackId) -> RelocateList {
        let mut pairs: RelocateList = self
            .incremental_relocate_entries(ambient)
            .into_iter()
            .map(|(source, target, _)| (source, target))
            .collect();
        let snapshot = pairs.clone();
        for (source, target) in pairs.iter_mut() {
            if target.is_empty() {
                continue;
            }
            *target = chain_through_relocates(target, &snapshot, Some(source));
        }

        // Nested relocates: a relocate `s2 → t2` whose source `s2` lies under
        // another's target `t1` (from `s1 → t1`) means content moved to `t1` is
        // moved on. Express that as a pair from the pre-relocation source
        // (`s1` + the suffix of `s2` below `t1`) straight to `t2`, so one map
        // application covers the whole chain. Iterated to a fixpoint over chains
        // of any depth; bounded by the relocate count.
        // TODO(perf): this is O(relocates⁴) with the linear `.any` membership
        // scans (a `HashSet<Path>` of seen sources would cut it); relocate counts
        // are tiny in practice, and the per-ambient cache TODO at
        // `IndexCache::compose_property_paths` would amortize it away.
        for _ in 0..pairs.len() {
            let mut added: Vec<(Path, Path)> = Vec::new();
            for (s1, t1) in &pairs {
                if t1.is_empty() {
                    continue;
                }
                for (s2, t2) in &pairs {
                    if s2 == s1 {
                        continue;
                    }
                    let Some(combined) = s2.replace_prefix(t1, s1) else {
                        continue;
                    };
                    // `combined == s2` is already excluded by the `pairs`
                    // membership check (`s2` is in `pairs`).
                    if !pairs.iter().any(|(s, _)| *s == combined) && !added.iter().any(|(s, _)| *s == combined) {
                        added.push((combined, t2.clone()));
                    }
                }
            }
            if added.is_empty() {
                break;
            }
            pairs.extend(added);
        }
        pairs
    }

    /// Whether a layer in `ambient` authors a relocate whose SOURCE is `source`
    /// (the salted-earth prohibition test). Includes deletion relocates.
    pub(crate) fn is_relocation_source(&self, ambient: LayerStackId, source: &Path) -> bool {
        self.relocation_source_layer(ambient, source).is_some()
    }

    /// Identifier of the strongest layer in `ambient` that authors a relocate
    /// whose SOURCE is `source`, or `None`.
    pub(crate) fn relocation_source_layer(&self, ambient: LayerStackId, source: &Path) -> Option<&str> {
        self.incremental_relocate_entries(ambient)
            .into_iter()
            .find_map(|(relocate_source, _, layer)| {
                (relocate_source == *source).then(|| self.layer(layer).identifier())
            })
    }

    /// Ensures `layer` is present as a graph node, returning `(id, fresh)` where
    /// `fresh` is `true` when the layer newly joined the graph. An already-loaded
    /// layer (matched by identifier) is left untouched (its existing children and
    /// relocates survive, since the same layer may be sublayered from several
    /// places) and reported as not fresh; an absent one joins with a freshly
    /// minted id. Callers key one-time per-layer setup (e.g. attaching a change
    /// aggregator) off `fresh` so a re-added identifier is not set up twice.
    ///
    /// The node must exist before a `subLayers` edit naming its asset path is
    /// rebuilt, so that [`build_sublayer_edges`](Self::build_sublayer_edges)'s
    /// [`find_relative`](Self::find_relative) resolves the path to it.
    pub(crate) fn ensure_layer(&mut self, layer: sdf::Layer) -> (LayerId, bool) {
        self.intern(layer)
    }

    /// The id of the layer interned under exactly `identifier` (the canonical,
    /// resolver-produced form), or `None`. An authored relative path must be
    /// anchored to its canonical identifier first (see
    /// [`find_relative`](Self::find_relative)); this is the exact registry lookup
    /// the anchored path then resolves through, and the authoring surface keys a
    /// layer this way.
    pub(crate) fn id_of(&self, identifier: &str) -> Option<LayerId> {
        self.by_identifier.get(identifier).copied()
    }

    /// The layer interned under the resolver-anchored identifier `anchored`, or —
    /// when nothing is interned there — under the bare authored `normalized` path.
    /// Anchoring wins so a relative path against a filesystem-backed layer never
    /// resolves to an unrelated layer interned under the bare string, while an
    /// in-memory layer keyed under that literal name (no filesystem anchor) still
    /// resolves. The shared lookup behind [`find_relative`](Self::find_relative)
    /// and [`resolve_sublayer`](Self::resolve_sublayer).
    fn anchored_or_bare(&self, anchored: &str, normalized: &str) -> Option<LayerId> {
        self.id_of(anchored).or_else(|| self.id_of(normalized))
    }

    /// Resolves `asset_path` as authored in `anchor`, anchoring it through the
    /// resolver to a canonical identifier, then looking that up exactly (C++
    /// `SdfLayer::FindRelativeToLayer`). The resolver owns anchoring and
    /// canonicalization, so a `..` path or a symlinked leaf resolves to the same
    /// canonical identifier the load path (`LayerRegistry::open_sublayers`)
    /// interned the layer under — the lookup is an exact registry hit that agrees
    /// with the load path by construction.
    ///
    /// The anchored identifier — the asset USD resolves a relative path to — is
    /// tried first. Only when no layer is interned there does it fall back to the
    /// bare authored string, which lets an in-memory layer keyed under that
    /// literal name (with no filesystem location to anchor against) resolve.
    /// Anchoring first means a relative path against a filesystem-backed layer
    /// never resolves to an unrelated layer that merely happens to be interned
    /// under the bare string.
    pub(crate) fn find_relative(&self, asset_path: &str, anchor: LayerId) -> Option<LayerId> {
        let asset_path = without_dot_segments(asset_path);
        let anchored = self
            .registry
            .create_identifier_anchored(&asset_path, self.real_path(anchor));
        self.anchored_or_bare(&anchored, &asset_path)
    }

    /// Mutes the layer with the given identifier so it contributes no opinions to
    /// composition (C++ `PcpCache::RequestLayerMuting`), recomposing the
    /// muting-dependent graph state. Returns what changed (see [`MuteChange`]), or
    /// `None` when nothing did: the identifier was already muted, or it resolves to
    /// the root layer, which cannot be muted ("would lead to empty layer stacks").
    ///
    /// The layer need not be loaded; the canonical identifier is stored and takes
    /// effect the moment a later edit interns a matching layer (see
    /// [`rebuild_sublayer_stacks`](Self::rebuild_sublayer_stacks), which
    /// re-materializes the interned muted ids).
    pub(crate) fn mute_layer(&mut self, identifier: String) -> Option<MuteChange> {
        let canonical = self.canonical_muted_id(&identifier, self.anchor_location(self.root).as_ref());
        if self.is_root_identifier(&canonical) || !self.muted_identifiers.insert(canonical.clone()) {
            return None;
        }
        let affected = self.recompose_for_mute_with_fanout(&canonical);
        Some(MuteChange {
            changed: canonical,
            affected,
        })
    }

    /// Unmutes the layer with the given identifier, restoring its opinions and
    /// recomposing. Returns what changed (see [`MuteChange`]), or `None` when the
    /// identifier was not muted. The identifier is canonicalized the same way
    /// muting canonicalized it, so any spelling of one layer unmutes it.
    pub(crate) fn unmute_layer(&mut self, identifier: &str) -> Option<MuteChange> {
        let canonical = self.canonical_muted_id(identifier, self.anchor_location(self.root).as_ref());
        if !self.muted_identifiers.remove(&canonical) {
            return None;
        }
        let affected = self.recompose_for_mute_with_fanout(&canonical);
        Some(MuteChange {
            changed: canonical,
            affected,
        })
    }

    /// Recomposes the muting-dependent graph state for a just-changed muted set
    /// and returns the layers whose cached prim indices the toggle of the layer
    /// with canonical identifier `canonical` can invalidate: the structural
    /// [`mute_fanout`](Self::mute_fanout) plus any layer whose cached relocate
    /// pairs the recompose changed.
    ///
    /// Relocate extraction omits muted layers and refreshes diagnostics in the
    /// graph. Any layer whose cached relocate pairs change is added to the
    /// fanout so dependent prims rebuild against the current stack state.
    fn recompose_for_mute_with_fanout(&mut self, canonical: &str) -> HashSet<LayerId> {
        let mut affected = self.mute_fanout(canonical);
        affected.extend(self.recompose_for_mute());
        affected
    }

    /// The interned layers a (un)mute of the layer with canonical identifier
    /// `canonical` can invalidate: the layer itself and every layer whose
    /// `subLayers` subtree contains it. Empty when no loaded layer has that
    /// identifier — muting a not-yet-loaded layer changes no composed index.
    ///
    /// A composed prim index is affected by toggling the layer exactly when one
    /// of its nodes resolves against a layer stack containing it, and a sublayer
    /// stack contains a layer iff its root layer does, so the set's members are
    /// the stack roots whose nodes a dependent index would list. Both the
    /// identifier lookup and the subtree edges are independent of the muted set,
    /// so the set is identical whether computed before muting or after unmuting.
    ///
    /// The stage root layer stack is the one stack that is not a single sublayer
    /// subtree: it glues the session layers (and their subtrees) onto the root
    /// layer's subtree. A toggle anywhere in it can change every prim that
    /// composes locally against it, and such a prim always retains the root layer
    /// in its composition (the root layer is never muted), so when a session
    /// layer is in the set the root layer is added as the anchor a dependent
    /// index is found through.
    fn mute_fanout(&self, canonical: &str) -> HashSet<LayerId> {
        let Some(id) = self.id_of(canonical) else {
            return HashSet::new();
        };
        let mut affected = self.ancestors_including(id);
        if let Some(root) = self.root {
            if self.session_layers().iter().any(|s| affected.contains(s)) {
                affected.insert(root);
            }
        }
        affected
    }

    /// Every layer whose `subLayers` subtree contains `target`, including
    /// `target` itself. Derived from the sublayer edges, which `subLayers`
    /// metadata is the single source of truth for and which muting never alters,
    /// so the result does not depend on the current muted set. A `${VAR}` sublayer
    /// is absent from the context-free [`LayerNode::children`], so the edges only a
    /// stack's variables resolve are supplied by
    /// [`expression_ancestry_edges`](Self::expression_ancestry_edges).
    fn ancestors_including(&self, target: LayerId) -> HashSet<LayerId> {
        let mut found = HashSet::from([target]);
        let expr_edges = self.expression_ancestry_edges();
        // The sublayer DAG holds one node per loaded layer, so growing the set to
        // a fixpoint — add any layer with a child already in it, until it stops
        // growing — is cheaper than materializing a reverse-edge index.
        let mut growing = true;
        while growing {
            growing = false;
            for (&id, node) in &self.nodes {
                if found.contains(&id) {
                    continue;
                }
                let reaches = node.children.iter().any(|&(child, _)| found.contains(&child))
                    || expr_edges
                        .get(&id)
                        .is_some_and(|children| children.iter().any(|c| found.contains(c)));
                if reaches {
                    found.insert(id);
                    growing = true;
                }
            }
        }
        found
    }

    /// The sublayer edges only a stack's expression variables resolve, keyed by the
    /// parent layer — the supplement the context-free [`LayerNode::children`] omit, so
    /// [`ancestors_including`](Self::ancestors_including) still finds a stack root whose
    /// `${VAR}` sublayer selects the target. Each stack's subtree is resolved against
    /// its own variables (the root stack's structural variables for the stage root
    /// stack's root and session regions, a seed for a target), read regardless of
    /// muting so the ancestor set is identical before a mute and after the matching
    /// unmute.
    fn expression_ancestry_edges(&self) -> HashMap<LayerId, Vec<LayerId>> {
        let mut edges: HashMap<LayerId, Vec<LayerId>> = HashMap::new();
        if !self.any_expr_sublayer {
            return edges;
        }
        // The (root, composed variables) of every stack whose subtree can hold an
        // expression edge: the stage root stack — both its root region and its
        // session region, each resolved against the structural root-stack
        // variables so a session sublayer sees the stage root's variables too —
        // and every interned target stack under its composed set (the target
        // root's own variables overlaid by its seed,
        // [`composed_stack_vars`](Self::composed_stack_vars), the same set its
        // `${VAR}` sublayer edges resolve against).
        let mut specs: Vec<(LayerId, HashMap<String, Value>)> = Vec::new();
        let structural = self.root_stack_structural_vars();
        if let Some(root) = self.root {
            specs.push((root, structural.clone()));
        }
        if let Some(&session_root) = self.session_layers().first() {
            specs.push((session_root, structural.clone()));
        }
        specs.extend(
            self.stacks
                .target_rebuild_specs(None)
                .into_iter()
                .map(|(_, root, seed)| (root, self.composed_stack_vars(root, &seed))),
        );
        let mut resolution = HashMap::new();
        for (root, vars) in specs {
            if !self.has_expr_sublayer(root) {
                continue;
            }
            for (parent, resolved) in self.compose_stack_edges(root, &vars, &mut resolution) {
                edges
                    .entry(parent)
                    .or_default()
                    .extend(resolved.into_iter().map(|(child, _)| child));
            }
        }
        edges
    }

    /// Seeds the muted set from `identifiers` (open-time muting), then recomposes
    /// once — cheaper than a `mute_layer` per identifier, which would recompose on
    /// each. Canonicalizes each against the root layer and drops any that names the
    /// root (which cannot be muted); identical canonical ids collapse in the set,
    /// so [`muted_layers`](Self::muted_layers) lists each muted layer once.
    pub(crate) fn set_muted_identifiers(&mut self, identifiers: impl IntoIterator<Item = String>) {
        let root_anchor = self.anchor_location(self.root);
        for identifier in identifiers {
            let canonical = self.canonical_muted_id(&identifier, root_anchor.as_ref());
            if !self.is_root_identifier(&canonical) {
                self.muted_identifiers.insert(canonical);
            }
        }
        self.recompose_for_mute();
    }

    /// Whether the layer named by this identifier is muted, matching by canonical
    /// identifier anchored against the root layer (C++ `PcpCache::IsLayerMuted`),
    /// so any spelling of one layer reads alike.
    pub(crate) fn is_layer_muted(&self, identifier: &str) -> bool {
        if self.muted_identifiers.is_empty() {
            return false;
        }
        let canonical = self.canonical_muted_id(identifier, self.anchor_location(self.root).as_ref());
        self.muted_identifiers.contains(&canonical)
    }

    /// Whether any layer identifier is muted at all. A cheap gate so the per-arc
    /// mute check skips its anchoring work on the common unmuted stage.
    pub(crate) fn has_muted_layers(&self) -> bool {
        !self.muted_identifiers.is_empty()
    }

    /// The muted-set identifier matched by the reference/payload target
    /// `asset_path`, anchored against `anchor` (the layer that authored the arc),
    /// or `None` when it names no muted layer. Matched by the canonical identifier
    /// the target would be interned under (C++ `Pcp_MutedLayers::IsLayerMuted`,
    /// anchored against the containing layer; see
    /// [`Indexer::arc_target_muted`](super::prim_indexer)). Unlike
    /// [`is_muted`](Self::is_muted), this matches before the layer is interned, so
    /// the on-demand loader can recognize a muted target and skip opening it, and
    /// the returned identifier is the muted-set entry an unmute toggles, so a
    /// not-yet-loaded target can record it as its unmute-fanout trace.
    pub(crate) fn muted_asset_id(&self, asset_path: &str, anchor: Option<&ResolvedPath>) -> Option<String> {
        if self.muted_identifiers.is_empty() {
            return None;
        }
        let canonical = self.canonical_muted_id(asset_path, anchor);
        self.muted_identifiers.contains(&canonical).then_some(canonical)
    }

    /// The layers of every composed stack — the effectively-present set the stage
    /// filters muted collection diagnostics against (see
    /// [`sublayer_error_contributes`](Self::sublayer_error_contributes)). Read from
    /// the composed stacks (muting has pruned their muted subtrees), so it is a pure
    /// function of the muted set and the graph, independent of which prim indices
    /// are cached — a diagnostic's visibility does not change as the cache warms.
    pub(crate) fn effective_layers(&self) -> HashSet<LayerId> {
        self.stacks.member_layers()
    }

    /// Whether a collection diagnostic still contributes to composition once muting
    /// is applied, so the stage keeps it (the loader reports every load failure raw,
    /// unaware of muting). A non-sublayer error always survives. A missing or
    /// unreadable sublayer survives only when its referencing layer is `effective`
    /// (a member of some composed stack) and the sublayer it names is not itself
    /// muted; otherwise muting prunes it and the raw diagnostic is spurious. The
    /// `effective` set is a pure function of the muted set and the graph, so the
    /// decision is deterministic across queries and independent of load order.
    pub(crate) fn sublayer_error_contributes(&self, error: &Error, effective: &HashSet<LayerId>) -> bool {
        let (asset_path, introduced_by) = match error {
            Error::UnresolvedSublayer {
                asset_path,
                introduced_by,
            }
            | Error::MalformedSublayer {
                asset_path,
                introduced_by,
                ..
            } => (asset_path, introduced_by),
            _ => return true,
        };
        let Some(referrer) = self.id_of(introduced_by) else {
            return true;
        };
        effective.contains(&referrer)
            && self
                .muted_asset_id(asset_path, self.anchor_location(Some(referrer)).as_ref())
                .is_none()
    }

    /// The muted layer identifiers, sorted for a deterministic result.
    pub(crate) fn muted_layers(&self) -> Vec<String> {
        let mut ids: Vec<String> = self.muted_identifiers.iter().cloned().collect();
        ids.sort();
        ids
    }

    /// Whether the layer with this id is muted, i.e. excluded from every stack.
    /// A muted layer contributes nothing to composition — not its opinions, its
    /// stage metadata, or its diagnostics.
    pub(crate) fn is_muted(&self, id: LayerId) -> bool {
        self.muted.contains(&id)
    }

    /// Refreshes every muting-dependent piece of graph state after the muted set
    /// changes: the sublayer stacks (rebuilding re-resolves the muted ids), the
    /// sublayer-cycle diagnostics (a cycle through a muted layer no longer
    /// composes), and the relocates, whose validation and conflict scopes both
    /// drop muted layers. Returns the layers whose cached relocate pairs changed
    /// (from [`recompute_relocates`](Self::recompute_relocates)).
    fn recompose_for_mute(&mut self) -> HashSet<LayerId> {
        // A mute toggles the muted set rather than the sublayer edges, so the
        // edge-diff scoping `build_sublayer_edges` uses does not apply; re-resolve
        // every instance (an unmuted layer rejoins stacks whose members no longer
        // list it, which a member-set scope would miss). `rebuild_sublayer_stacks`
        // refreshes the muted set and recomputes the root's session-seeded members,
        // so muting a session layer that supplies a root `${VAR}` sublayer's variable
        // re-resolves that sublayer out of (or into, among interned layers) the root
        // stack.
        self.rebuild_sublayer_stacks(None);
        self.recompute_cycle_errors();
        self.recompute_relocates()
    }

    /// Re-materializes [`muted`](Self::muted) — the interned ids of the muted
    /// canonical identifiers — at the start of every stack rebuild, so it reflects
    /// the currently-loaded layers (a layer muted before it was loaded takes effect
    /// the moment a later edit interns it). The root is never present: its
    /// identifier is rejected before any entry is inserted (see
    /// [`is_root_identifier`](Self::is_root_identifier)).
    fn resolve_muted_ids(&mut self) {
        // TODO: reclaim a muted layer's memory. C++ drops its references; here
        // the node stays interned so unmute is a rebuild and nothing is freed.
        // The common unmuted stage rebuilds stacks often, so leave `muted` (already
        // empty) untouched rather than reallocating it each time.
        if self.muted_identifiers.is_empty() {
            self.muted.clear();
            return;
        }
        self.muted = self.muted_identifiers.iter().filter_map(|id| self.id_of(id)).collect();
    }

    /// Whether `canonical` is the root layer's identifier, which cannot be muted
    /// ("would lead to empty layer stacks"). The single authority for rejecting a
    /// request to mute the root, regardless of the spelling the caller supplied.
    fn is_root_identifier(&self, canonical: &str) -> bool {
        self.root.is_some_and(|root| self.identifier(root) == canonical)
    }

    /// The canonical identifier a muted-layer path resolves to (C++
    /// `Pcp_MutedLayers::_GetCanonicalLayerId`). A path is reduced to the
    /// identifier its layer is interned under (see [`intern`](Self::intern)): with
    /// no filesystem `anchor` — an in-memory or anonymous root — a relative path
    /// has nothing to resolve against and an added layer keeps its bare
    /// identifier, so the path passes through. Every other path is canonicalized
    /// through the registry against `anchor`, the form a filesystem asset is
    /// interned under; an anonymous identifier passes through there too (the
    /// registry keeps an `anon:` id as its own canonical form).
    ///
    /// `anchor` is the layer the path is anchored against: the root layer for the
    /// mute/unmute/query API, the arc's authoring layer for a reference/payload
    /// target. Keying the muted set on this makes two spellings of one layer
    /// collapse to a single entry and lets a not-yet-loaded target match the
    /// identifier it will be interned under. The result is a pure function of
    /// `(path, anchor)`, independent of which layers are currently loaded — so the
    /// same physical layer never keys under different strings by load order.
    fn canonical_muted_id(&self, path: &str, anchor: Option<&ResolvedPath>) -> String {
        if anchor.is_none() {
            return path.to_string();
        }
        self.registry.create_identifier(path, anchor)
    }
}

/// The elements pruned by muting: each muted root and everything reachable from
/// it through `children_of`, restricted to `scope`. The single rule for the
/// effective session stack — a muted session layer and the whole subtree it
/// sublayers contribute nothing — shared by graph composition (walking a stack's
/// resolved sublayer edges over [`LayerId`]s) and open-time collection (walking
/// the collected layers' authored sublayer paths over identifiers), so the two
/// cannot disagree on which session layers are effective.
pub(crate) fn muted_subtree<T: Clone + Eq + Hash>(
    scope: &HashSet<T>,
    muted_roots: impl IntoIterator<Item = T>,
    children_of: impl Fn(&T) -> Vec<T>,
) -> HashSet<T> {
    let mut pruned = HashSet::new();
    let mut pending: Vec<T> = muted_roots.into_iter().filter(|id| scope.contains(id)).collect();
    while let Some(id) = pending.pop() {
        if !pruned.insert(id.clone()) {
            continue;
        }
        for child in children_of(&id) {
            if scope.contains(&child) {
                pending.push(child);
            }
        }
    }
    pruned
}

/// Depth-first pre-order walk of a sublayer subtree, composing each hop's offset
/// and pruning muted layers, the shared traversal behind every composed stack.
/// `children_of` supplies a layer's resolved sublayer edges — the shared
/// context-free [`LayerNode::children`], or a stack's expression-resolved edges —
/// so both build paths stay locked together. Runs on an explicit work stack so a
/// deep chain does not overflow the native stack; an `Exit` frame pops the layer
/// back out of the `ancestors` path after its subtree. A layer that sublayers
/// itself transitively is a cycle and is skipped; an off-path duplicate (a sublayer
/// diamond) is expanded again.
fn collect_sublayers<'a>(
    root: LayerId,
    effective: LayerOffset,
    members: &mut Vec<(LayerId, LayerOffset)>,
    ancestors: &mut HashSet<LayerId>,
    is_muted: impl Fn(LayerId) -> bool,
    children_of: impl Fn(LayerId) -> &'a [(LayerId, LayerOffset)],
) {
    enum Step {
        Enter(LayerId, LayerOffset),
        Exit(LayerId),
    }
    let mut work = vec![Step::Enter(root, effective)];
    while let Some(step) = work.pop() {
        let (id, effective) = match step {
            Step::Exit(id) => {
                ancestors.remove(&id);
                continue;
            }
            Step::Enter(id, effective) => (id, effective),
        };
        // A muted layer contributes nothing: skip it and its whole subtree.
        if is_muted(id) {
            continue;
        }
        members.push((id, effective));
        ancestors.insert(id);
        work.push(Step::Exit(id));
        for &(child, edge_offset) in children_of(id).iter().rev() {
            if !ancestors.contains(&child) {
                work.push(Step::Enter(child, effective.concatenate(&edge_offset)));
            }
        }
    }
}

/// `asset_path` with its `.` (current-directory) segments dropped, rendered with
/// `/` separators: `./a` and `a/./b` become `a` and `a/b`. Segments are split on
/// any separator the platform accepts — `/` everywhere, and `\` on Windows — so
/// this matches the `std::path::Components` normalization the resolver applies
/// when it anchors a relative path (`LayerRegistry::create_identifier` via
/// `TfNormPath`). A dot-relative spelling therefore reduces to the same bare key
/// the anchored identifier drops its `.` to — `./sub.usda` on any platform, or
/// `.\sub.usda` on Windows — and the bare fallback in `anchored_or_bare` finds an
/// in-memory layer interned under `sub.usda`. A path with no `.` segment is
/// returned unchanged.
fn without_dot_segments(asset_path: &str) -> Cow<'_, str> {
    if !asset_path.split(path::is_separator).any(|segment| segment == ".") {
        return Cow::Borrowed(asset_path);
    }
    let kept: Vec<&str> = asset_path
        .split(path::is_separator)
        .filter(|segment| *segment != ".")
        .collect();
    Cow::Owned(kept.join("/"))
}

#[cfg(test)]
impl LayerGraph {
    /// Mints the layer stack each demand resolves against, once its target
    /// layer is interned: `id_of` the demanded asset, then
    /// [`intern_external`](Self::intern_external) under the demand's context.
    /// The demand drain the test harnesses run in place of the stage's load
    /// barrier (whose own mint loop additionally re-checks contextual opens for
    /// targets that joined mid-pass); their fixtures load every layer up front,
    /// so a demand only ever needs interning. Returns whether any new instance
    /// was created, so the caller re-runs the composition pass that recorded
    /// the demands.
    pub(crate) fn intern_demanded(&mut self, demands: &[Demand]) -> bool {
        let mut newly_interned = false;
        for demand in demands {
            if let Some(root) = self.id_of(demand.asset_path.as_str()) {
                newly_interned |= self.intern_external(root, demand.context).1;
            }
        }
        newly_interned
    }
}

#[cfg(test)]
mod tests {
    use std::io;
    use std::path::Path as FsPath;

    use super::*;
    use crate::ar;

    /// Author through a layer's `edit` API and commit, for building test fixtures.
    fn edit_layer(layer: &mut sdf::Layer, f: impl FnOnce(&mut sdf::LayerEdit<'_>)) {
        layer
            .edit(|e| {
                f(e);
                Ok(())
            })
            .expect("authored");
    }

    impl LayerGraph {
        /// Build a graph from `layers` in one step: intern each, then
        /// [`finalize`](Self::finalize). The first `session_layer_count` layers
        /// are the session layers; the next is the root. A test convenience — the
        /// stage builds its graph through [`new`](Self::new) +
        /// [`ensure_layer`](Self::ensure_layer) so it can attach a change sink to
        /// each layer as it joins.
        pub(crate) fn from_layers(
            layers: Vec<sdf::Layer>,
            session_layer_count: usize,
            registry: sdf::LayerRegistry,
        ) -> Self {
            let mut graph = Self::new(registry);
            let mut root = None;
            let mut session_count = 0;
            for (i, layer) in layers.into_iter().enumerate() {
                let (id, fresh) = graph.intern(layer);
                if i == session_layer_count {
                    root = Some(id);
                }
                if fresh && i < session_layer_count {
                    session_count += 1;
                }
            }
            graph.finalize(session_count, root);
            graph
        }

        /// The id of a loaded layer whose identifier ends with the path component
        /// `leaf` (its file name), or `None`. A test convenience for locating a
        /// layer in a stack built from on-disk assets, where the identifier is the
        /// full resolved path rather than the authored leaf; production code keys
        /// layers by canonical identifier ([`id_of`](Self::id_of)) or anchors an
        /// authored path first ([`find_relative`](Self::find_relative)).
        pub(crate) fn find_by_leaf(&self, leaf: &str) -> Option<LayerId> {
            self.order
                .iter()
                .copied()
                .find(|&id| FsPath::new(self.identifier(id)).ends_with(leaf))
        }
    }

    /// A `root → sub → leaf` sublayer chain, each layer named verbatim so the
    /// authored `subLayers` entries resolve by exact identifier match.
    fn chain_graph() -> LayerGraph {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["sub.usda"]);
        });
        let mut sub = sdf::Layer::new_in_memory("sub.usda");
        edit_layer(&mut sub, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["leaf.usda"]);
        });
        let leaf = sdf::Layer::new_in_memory("leaf.usda");
        LayerGraph::from_layers(vec![root, sub, leaf], 0, sdf::LayerRegistry::default())
    }

    /// Muting a sublayer drops it and its whole subtree from `sublayer_stack`,
    /// `root_layer_stack`, and `local_layers`; unmuting restores them.
    #[test]
    fn muted_excludes_subtree() {
        let mut graph = chain_graph();
        let root = graph.root_id().unwrap();
        let sub = graph.id_of("sub.usda").unwrap();
        let leaf = graph.id_of("leaf.usda").unwrap();

        let ids: Vec<LayerId> = graph.sublayer_stack(root).iter().map(|&(id, _)| id).collect();
        assert_eq!(ids, vec![root, sub, leaf]);
        assert_eq!(graph.root_layer_stack().len(), 3);

        assert!(graph.mute_layer("sub.usda".to_string()).is_some());
        let ids: Vec<LayerId> = graph.sublayer_stack(root).iter().map(|&(id, _)| id).collect();
        assert_eq!(ids, vec![root], "the muted sublayer and its subtree are pruned");
        assert_eq!(graph.root_layer_stack().len(), 1);
        assert_eq!(graph.local_layers(), HashSet::from([root]));

        assert!(graph.unmute_layer("sub.usda").is_some());
        let ids: Vec<LayerId> = graph.sublayer_stack(root).iter().map(|&(id, _)| id).collect();
        assert_eq!(ids, vec![root, sub, leaf], "unmuting restores the subtree");
        assert_eq!(graph.local_layers(), HashSet::from([root, sub, leaf]));
    }

    /// Muting the root layer is rejected: `mute_layer` reports no change and the
    /// root stack is unchanged.
    #[test]
    fn muted_root_ignored() {
        let mut graph = chain_graph();
        assert!(
            graph.mute_layer("root.usda".to_string()).is_none(),
            "the root layer cannot be muted"
        );
        assert!(!graph.is_layer_muted("root.usda"));
        assert_eq!(graph.root_layer_stack().len(), 3);
    }

    /// Muting a layer in a sublayer cycle clears the cycle diagnostic, since the
    /// muted branch no longer composes; unmuting brings it back.
    #[test]
    fn muted_cycle_clears_error() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["a.usda"]);
        });
        let mut a = sdf::Layer::new_in_memory("a.usda");
        edit_layer(&mut a, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["b.usda"]);
        });
        let mut b = sdf::Layer::new_in_memory("b.usda");
        edit_layer(&mut b, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["a.usda"]);
        });
        let mut graph = LayerGraph::from_layers(vec![root, a, b], 0, sdf::LayerRegistry::default());
        assert!(!graph.errors().is_empty(), "the a → b → a sublayer cycle is reported");

        assert!(graph.mute_layer("b.usda".to_string()).is_some());
        assert!(
            graph.errors().is_empty(),
            "muting a layer in the cycle clears the diagnostic"
        );

        assert!(graph.unmute_layer("b.usda").is_some());
        assert!(!graph.errors().is_empty(), "unmuting restores the cycle diagnostic");
    }

    /// Authors an `expressionVariables` dictionary on a layer's pseudo-root.
    fn set_expr_var(layer: &mut sdf::Layer, name: &str, value: &str) {
        edit_layer(layer, |e| {
            let dict = HashMap::from([(name.to_string(), Value::String(value.to_string()))]);
            e.pseudo_root_mut()
                .unwrap()
                .set(FieldKey::ExpressionVariables.as_str(), Value::Dictionary(dict));
        });
    }

    /// A variable authored on a **sublayer** is ignored: a layer stack's expression
    /// variables come from its root layer, not its sublayers (C++
    /// `PcpExpressionVariables`). `a` sublayers the root and authors `V`, but `b`'s
    /// `${V}` sublayer resolves against the stack root's variables (none here), so it
    /// does not resolve and `leaf` never enters the stack.
    #[test]
    fn sublayer_var_ignored() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["a.usda"]);
        });
        let mut a = sdf::Layer::new_in_memory("a.usda");
        set_expr_var(&mut a, "V", "leaf");
        edit_layer(&mut a, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["b.usda"]);
        });
        let mut b = sdf::Layer::new_in_memory("b.usda");
        edit_layer(&mut b, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let leaf = sdf::Layer::new_in_memory("leaf.usda");

        let graph = LayerGraph::from_layers(vec![root, a, b, leaf], 0, sdf::LayerRegistry::default());
        let root = graph.root_id().unwrap();
        let leaf = graph.id_of("leaf.usda").unwrap();
        let ids: Vec<LayerId> = graph.sublayer_stack(root).iter().map(|&(id, _)| id).collect();
        assert!(
            !ids.contains(&leaf),
            "`a` is a sublayer, so its `V` is ignored and `b`'s ${{V}} does not resolve: {ids:?}",
        );
    }

    /// A `${VAR}` root sublayer resolved by a session variable back onto the root
    /// is a cycle, and it is reported: the session-seeded root edges feed cycle
    /// detection, not just member collection, so the diagnostic surfaces rather
    /// than the edge being silently pruned.
    #[test]
    fn session_var_sublayer_cycle() {
        let mut session = sdf::Layer::new_in_memory("session.usda");
        set_expr_var(&mut session, "WHICH", "root");
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${WHICH}.usda"`"#]);
        });
        let graph = LayerGraph::from_layers(vec![session, root], 1, sdf::LayerRegistry::default());
        assert!(
            graph.errors().iter().any(|e| matches!(e, Error::SublayerCycle { .. })),
            "the session-resolved self-sublayer is reported as a cycle: {:?}",
            graph.errors()
        );
    }

    /// Muting a session layer that supplies a root `${VAR}` sublayer's variable
    /// re-resolves the root edges: the sublayer it selected drops, rather than the
    /// muted layer continuing to resolve it.
    #[test]
    fn mute_session_drops_sublayer() {
        let mut session = sdf::Layer::new_in_memory("session.usda");
        set_expr_var(&mut session, "WHICH", "a");
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${WHICH}.usda"`"#]);
        });
        let a = sdf::Layer::new_in_memory("a.usda");
        let mut graph = LayerGraph::from_layers(vec![session, root, a], 1, sdf::LayerRegistry::default());
        let a_id = graph.id_of("a.usda").unwrap();
        let in_root = |g: &LayerGraph| g.root_layer_stack().iter().any(|&(id, _)| id == a_id);

        assert!(
            in_root(&graph),
            "the session's WHICH=a resolves the root sublayer to a.usda"
        );
        graph.mute_layer("session.usda".to_string());
        assert!(
            !in_root(&graph),
            "muting the session layer drops the variable, so the root sublayer no longer resolves"
        );
    }

    /// A variable authored on a session **sublayer** is ignored; only the session
    /// root layer's own reaches the root stack (C++ `PcpExpressionVariables` reads
    /// the session layer, not its sublayers). The mirror — the session root itself
    /// authoring the variable — does apply.
    #[test]
    fn session_sublayer_var_ignored() {
        let sublayer_authored = |on_root: bool| -> bool {
            let mut session = sdf::Layer::new_in_memory("session.usda");
            if on_root {
                set_expr_var(&mut session, "V", "leaf");
            }
            edit_layer(&mut session, |e| {
                e.pseudo_root_mut().unwrap().set_sublayers(["session_sub.usda"]);
            });
            let mut session_sub = sdf::Layer::new_in_memory("session_sub.usda");
            if !on_root {
                set_expr_var(&mut session_sub, "V", "leaf");
            }
            let mut root = sdf::Layer::new_in_memory("root.usda");
            edit_layer(&mut root, |e| {
                e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
            });
            let leaf = sdf::Layer::new_in_memory("leaf.usda");
            let graph =
                LayerGraph::from_layers(vec![session, session_sub, root, leaf], 2, sdf::LayerRegistry::default());
            let leaf_id = graph.id_of("leaf.usda").unwrap();
            graph.root_layer_stack().iter().any(|&(id, _)| id == leaf_id)
        };
        assert!(
            !sublayer_authored(false),
            "a session sublayer's V is ignored, so the root's `${{V}}` does not resolve",
        );
        assert!(
            sublayer_authored(true),
            "the session root's own V applies, so the root's `${{V}}` resolves",
        );
    }

    /// A stack uses its **root** layer's own variables. `a` authors `V` and
    /// sublayers `b`; a stack rooted at `a` resolves `b`'s `${V}` sublayer to `leaf`
    /// (`a` is that stack's root). A stack rooted at `b` does not: `b` authors no
    /// variables, and `a` — which merely sublayers `b` — contributes none (C++
    /// `PcpExpressionVariables`). The result is independent of `b` being interned
    /// before `a`.
    #[test]
    fn stack_root_var_applies() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut a = sdf::Layer::new_in_memory("a.usda");
        set_expr_var(&mut a, "V", "leaf");
        edit_layer(&mut a, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["b.usda"]);
        });
        let mut b = sdf::Layer::new_in_memory("b.usda");
        edit_layer(&mut b, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let leaf = sdf::Layer::new_in_memory("leaf.usda");

        // `root` sublayers none of them, so `a`/`b`/`leaf` are an orphan subtree;
        // `b` precedes `a` in collection order.
        let graph = LayerGraph::from_layers(vec![root, b, a, leaf], 0, sdf::LayerRegistry::default());
        let a_id = graph.id_of("a.usda").unwrap();
        let b_id = graph.id_of("b.usda").unwrap();
        let leaf_id = graph.id_of("leaf.usda").unwrap();

        let a_stack: Vec<LayerId> = graph.sublayer_stack(a_id).iter().map(|&(id, _)| id).collect();
        assert!(
            a_stack.contains(&leaf_id),
            "`a`'s stack threads `a`'s `V` into `b`, so `b`'s ${{V}} resolves to `leaf`: {a_stack:?}",
        );
        let b_stack: Vec<LayerId> = graph.sublayer_stack(b_id).iter().map(|&(id, _)| id).collect();
        assert!(
            !b_stack.contains(&leaf_id),
            "`b`'s own stack has no inherited context, so its ${{V}} stays unresolved: {b_stack:?}",
        );
    }

    /// A deep single-sublayer chain composes without overflowing the native
    /// stack: the edge walk, the cycle scan, and the stack collection all run on
    /// explicit stacks. Each layer sublayers the next; the root's composed
    /// sublayer stack contains the whole chain. Only the root's stack is
    /// precomputed (the chain has one sublayer-DAG root), so this is O(n).
    #[test]
    fn deep_sublayer_chain_no_overflow() {
        const DEPTH: usize = 50_000;
        let mut layers = Vec::with_capacity(DEPTH);
        for i in 0..DEPTH {
            let mut layer = sdf::Layer::new_in_memory(format!("layer{i}.usda"));
            if i + 1 < DEPTH {
                edit_layer(&mut layer, |e| {
                    e.pseudo_root_mut()
                        .unwrap()
                        .set_sublayers([format!("layer{}.usda", i + 1)]);
                });
            }
            layers.push(layer);
        }
        let graph = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let root_id = graph.root_id().unwrap();
        assert_eq!(graph.sublayer_stack(root_id).len(), DEPTH, "the whole chain composes");
    }

    /// `sublayer_stack` composes a non-precomputed layer's stack on demand: a
    /// layer that is sublayered (so not a sublayer-DAG root, not precomputed)
    /// still reports its own stack when queried — the case of a layer that is both
    /// sublayered and used as a reference/payload target.
    #[test]
    fn sublayer_stack_computed_on_demand() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["a.usda"]);
        });
        let mut a = sdf::Layer::new_in_memory("a.usda");
        edit_layer(&mut a, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["b.usda"]);
        });
        let b = sdf::Layer::new_in_memory("b.usda");

        let graph = LayerGraph::from_layers(vec![root, a, b], 0, sdf::LayerRegistry::default());
        let a_id = graph.id_of("a.usda").unwrap();
        let b_id = graph.id_of("b.usda").unwrap();
        // `a` is sublayered by root, so it is not a precomputed DAG root.
        let ids: Vec<LayerId> = graph.sublayer_stack(a_id).iter().map(|&(id, _)| id).collect();
        assert_eq!(ids, vec![a_id, b_id], "a's stack composes on demand");
    }

    /// A `${VAR}` sublayer on a reference/payload target resolves against the
    /// expression variables inherited across the arc, held on the target's
    /// context-keyed stack instance. The plain
    /// [`sublayer_stack`](LayerGraph::sublayer_stack) (no inherited context) cannot
    /// resolve it; the instance interned for the arc's context can.
    #[test]
    fn contextual_var_sublayer() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let over = sdf::Layer::new_in_memory("over.usda");

        let mut graph = LayerGraph::from_layers(vec![root, target, over], 0, sdf::LayerRegistry::default());
        let target = graph.id_of("target.usda").unwrap();
        let over = graph.id_of("over.usda").unwrap();

        let ids: Vec<LayerId> = graph.sublayer_stack(target).iter().map(|&(id, _)| id).collect();
        assert!(
            !ids.contains(&over),
            "the plain (no-context) stack cannot resolve `${{V}}`"
        );

        let vars = HashMap::from([("V".to_string(), Value::String("over".to_string()))]);
        let id = graph.ensure_external_stack(target, &vars);
        let ids: Vec<LayerId> = graph.layer_stack(id).iter().map(|&(id, _)| id).collect();
        assert!(
            ids.contains(&over),
            "the contextual instance resolves the `${{V}}` sublayer edge"
        );
    }

    /// The same `${VAR}`-sublayer target reached through two different inherited
    /// contexts resolves its sublayer independently: each context gets its own stack
    /// instance with its own resolved member.
    #[test]
    fn contextual_var_sublayer_per_context() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let a = sdf::Layer::new_in_memory("a.usda");
        let b = sdf::Layer::new_in_memory("b.usda");

        let mut graph = LayerGraph::from_layers(vec![root, target, a, b], 0, sdf::LayerRegistry::default());
        let target = graph.id_of("target.usda").unwrap();
        let a = graph.id_of("a.usda").unwrap();
        let b = graph.id_of("b.usda").unwrap();

        let va = HashMap::from([("V".to_string(), Value::String("a".to_string()))]);
        let vb = HashMap::from([("V".to_string(), Value::String("b".to_string()))]);
        let ia = graph.ensure_external_stack(target, &va);
        let ib = graph.ensure_external_stack(target, &vb);
        assert_ne!(ia, ib, "different contexts get distinct instances");

        let members = |id| {
            graph
                .layer_stack(id)
                .iter()
                .map(|&(layer, _)| layer)
                .collect::<Vec<_>>()
        };
        assert!(
            members(ia).contains(&a) && !members(ia).contains(&b),
            "V=a resolves a.usda"
        );
        assert!(
            members(ib).contains(&b) && !members(ib).contains(&a),
            "V=b resolves b.usda"
        );
    }

    /// Every target stack is keyed by its full inherited context, even when the
    /// context cannot change its members — here the target's only expression
    /// sublayer is muted. The two contexts intern distinct instances with equal
    /// members, and each instance carries its own composed expression variables
    /// (the context an asset attribute inside the target evaluates against).
    #[test]
    fn muted_expr_sublayer_per_context() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        edit_layer(&mut target, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["muted_expr.usda"]);
        });
        let mut muted_expr = sdf::Layer::new_in_memory("muted_expr.usda");
        edit_layer(&mut muted_expr, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });

        let mut graph = LayerGraph::from_layers(vec![root, target, muted_expr], 0, sdf::LayerRegistry::default());
        graph.mute_layer("muted_expr.usda".to_string());
        let target = graph.id_of("target.usda").unwrap();

        let va = HashMap::from([("V".to_string(), Value::String("a".to_string()))]);
        let vb = HashMap::from([("V".to_string(), Value::String("b".to_string()))]);
        let ia = graph.ensure_external_stack(target, &va);
        let ib = graph.ensure_external_stack(target, &vb);
        assert_ne!(ia, ib, "each context gets its own instance");
        assert_eq!(
            graph.layer_stack(ia),
            graph.layer_stack(ib),
            "the muted expression sublayer leaves both contexts' members equal"
        );
        assert_eq!(
            graph.stack_expression_variables(ia),
            &va,
            "the instance carries its context"
        );
        assert_eq!(
            graph.stack_expression_variables(ib),
            &vb,
            "the instance carries its context"
        );
    }

    /// The stored composed set is the target root's own variables overlaid by the
    /// seed (seed winning), and an `expressionVariables` edit on the target root
    /// refreshes it through the scoped rebuild.
    #[test]
    fn stored_composed_refreshed() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        set_expr_var(&mut target, "V", "a");
        let mut graph = LayerGraph::from_layers(vec![root, target], 0, sdf::LayerRegistry::default());
        let target = graph.id_of("target.usda").unwrap();

        let seed = HashMap::from([("W".to_string(), Value::String("x".to_string()))]);
        let id = graph.ensure_external_stack(target, &seed);
        assert_eq!(
            graph.stack_expression_variables(id),
            &HashMap::from([
                ("V".to_string(), Value::String("a".to_string())),
                ("W".to_string(), Value::String("x".to_string())),
            ]),
            "the stored set is the target's own V overlaid by the seed's W"
        );

        set_expr_var(&mut graph.nodes.get_mut(&target).unwrap().layer, "V", "b");
        graph.recompute_sublayers(Some(&HashSet::from([target])));
        assert_eq!(
            graph.stack_expression_variables(id),
            &HashMap::from([
                ("V".to_string(), Value::String("b".to_string())),
                ("W".to_string(), Value::String("x".to_string())),
            ]),
            "editing the target root's V refreshes the stored set in place"
        );
    }

    /// An `expressionVariables` edit on a muted target root still refreshes the
    /// instance's stored composed set: the muted root's member set is empty
    /// (disjoint from every edit), so the rebuild filter must match the target
    /// root itself, not only the members.
    #[test]
    fn muted_target_root_edit() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        set_expr_var(&mut target, "V", "a");
        let mut graph = LayerGraph::from_layers(vec![root, target], 0, sdf::LayerRegistry::default());
        graph.mute_layer("target.usda".to_string());
        let target = graph.id_of("target.usda").unwrap();

        let id = graph.ensure_external_stack(target, &HashMap::new());
        assert!(graph.layer_stack(id).is_empty(), "the muted root empties the stack");
        assert_eq!(
            graph.stack_expression_variables(id),
            &HashMap::from([("V".to_string(), Value::String("a".to_string()))]),
            "the muted root's own variables still compose the stored set"
        );

        set_expr_var(&mut graph.nodes.get_mut(&target).unwrap().layer, "V", "b");
        graph.recompute_sublayers(Some(&HashSet::from([target])));
        assert_eq!(
            graph.stack_expression_variables(id),
            &HashMap::from([("V".to_string(), Value::String("b".to_string()))]),
            "the edit reaches the instance even though its member set is empty"
        );
    }

    /// A back-reference to a sessionless stage root collapses to the ROOT
    /// instance only when the arriving context is the root stack's own composed
    /// context; a differing context mints a contextual instance rooted at the
    /// stage root layer that keeps the extra variables in force.
    #[test]
    fn root_backref_identity() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        set_expr_var(&mut root, "V", "r");
        let mut graph = LayerGraph::from_layers(vec![root], 0, sdf::LayerRegistry::default());
        let root = graph.root_id().unwrap();

        let own = HashMap::from([("V".to_string(), Value::String("r".to_string()))]);
        let id = graph.ensure_external_stack(root, &own);
        assert_eq!(id, LayerStackId::ROOT, "the root stack's own context collapses to ROOT");

        let carried = HashMap::from([
            ("V".to_string(), Value::String("r".to_string())),
            ("EXTRA".to_string(), Value::String("e".to_string())),
        ]);
        let id = graph.ensure_external_stack(root, &carried);
        assert_ne!(
            id,
            LayerStackId::ROOT,
            "a context-bearing back-reference stays contextual"
        );
        assert_eq!(
            graph.stack_expression_variables(id),
            &carried,
            "the contextual instance keeps the carried variables"
        );
    }

    /// Two distinct source stacks carrying equal composed maps into the same
    /// target share one instance: the registry keys by the composed context's
    /// value, so the interned seed ids coincide. (C++ keys by the override
    /// source instead and may keep two stacks; see the module's parity notes.)
    #[test]
    fn equal_context_shared_target() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut s1 = sdf::Layer::new_in_memory("s1.usda");
        set_expr_var(&mut s1, "V", "x");
        let mut s2 = sdf::Layer::new_in_memory("s2.usda");
        set_expr_var(&mut s2, "V", "x");
        let target = sdf::Layer::new_in_memory("target.usda");
        let mut graph = LayerGraph::from_layers(vec![root, s1, s2, target], 0, sdf::LayerRegistry::default());
        let s1 = graph.id_of("s1.usda").unwrap();
        let s2 = graph.id_of("s2.usda").unwrap();
        let target = graph.id_of("target.usda").unwrap();

        let s1_stack = graph.ensure_external_stack(s1, &HashMap::new());
        let s2_stack = graph.ensure_external_stack(s2, &HashMap::new());
        assert_ne!(s1_stack, s2_stack, "the sources are distinct stacks");

        let (t1, fresh1) = graph.intern_external(target, s1_stack);
        let (t2, fresh2) = graph.intern_external(target, s2_stack);
        assert!(fresh1 && !fresh2, "the second equal context reuses the first instance");
        assert_eq!(t1, t2, "equal composed maps share one target instance");
        assert_eq!(
            graph.stack_expression_variables(t1),
            &HashMap::from([("V".to_string(), Value::String("x".to_string()))]),
        );
    }

    /// A `${VAR}` sublayer selected by a reference target's own variable appears
    /// in the expression ancestry edges: the edge resolves against the target
    /// stack's composed variables (its root's own overlaid by the seed), so mute
    /// fanout can find the target root from the selected sublayer.
    #[test]
    fn target_own_var_ancestry_edge() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        set_expr_var(&mut target, "V", "sub");
        edit_layer(&mut target, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let sub = sdf::Layer::new_in_memory("sub.usda");
        let mut graph = LayerGraph::from_layers(vec![root, target, sub], 0, sdf::LayerRegistry::default());
        let target = graph.id_of("target.usda").unwrap();
        let sub = graph.id_of("sub.usda").unwrap();
        graph.ensure_external_stack(target, &HashMap::new());

        let edges = graph.expression_ancestry_edges();
        assert!(
            edges.get(&target).is_some_and(|children| children.contains(&sub)),
            "the target's own V resolves the `${{V}}` ancestry edge: {edges:?}"
        );
    }

    /// The stage's own root layer is never contextually reopened: a
    /// context-bearing back-reference to a root with a `${VAR}` sublayer interns
    /// from the loaded graph instead of demanding a disk re-read, which would
    /// fail for an in-memory root and discard unsaved edits for a dirty one.
    #[test]
    fn root_never_reopened() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let mut src = sdf::Layer::new_in_memory("src.usda");
        set_expr_var(&mut src, "V", "x");
        let mut graph = LayerGraph::from_layers(vec![root, src], 0, sdf::LayerRegistry::default());
        let root = graph.root_id().unwrap();
        let src = graph.id_of("src.usda").unwrap();

        let ctx = graph.ensure_external_stack(src, &HashMap::new());
        assert!(
            !graph.needs_contextual_open(root, ctx),
            "a context-bearing back-reference to the stage root must not trigger a reopen"
        );
    }

    /// The arms of a sublayer diamond: `x_arm` and `y_arm` each author a conflicting
    /// `V` on themselves and sublayer `shared`, whose `${V}` sublayer resolves
    /// against the stack root's variables — not these sublayer-authored ones. Add
    /// them under a root that sublayers `[x_arm.usda, y_arm.usda]`.
    fn diamond_arms() -> Vec<sdf::Layer> {
        let mut x_arm = sdf::Layer::new_in_memory("x_arm.usda");
        set_expr_var(&mut x_arm, "V", "x_leaf");
        edit_layer(&mut x_arm, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["shared.usda"]);
        });
        let mut y_arm = sdf::Layer::new_in_memory("y_arm.usda");
        set_expr_var(&mut y_arm, "V", "y_leaf");
        edit_layer(&mut y_arm, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["shared.usda"]);
        });
        let mut shared = sdf::Layer::new_in_memory("shared.usda");
        edit_layer(&mut shared, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let x_leaf = sdf::Layer::new_in_memory("x_leaf.usda");
        let y_leaf = sdf::Layer::new_in_memory("y_leaf.usda");
        vec![x_arm, y_arm, shared, x_leaf, y_leaf]
    }

    /// A sublayer diamond whose two arms author conflicting `${V}` values resolves
    /// to neither leaf: the arms are sublayers, so their `V` is ignored (a stack's
    /// variables come from its root, C++ `PcpExpressionVariables`) and `shared`'s
    /// `${V}` has nothing to resolve against. The public `sublayer_stack` query and
    /// the composed `root_layer_stack` agree, both going through the one stack-level
    /// expansion.
    #[test]
    fn diamond_sublayer_vars_ignored() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["x_arm.usda", "y_arm.usda"]);
        });
        let mut layers = vec![root];
        layers.extend(diamond_arms());
        let graph = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let x_leaf = graph.id_of("x_leaf.usda").unwrap();
        let y_leaf = graph.id_of("y_leaf.usda").unwrap();

        let ids: Vec<LayerId> = graph.root_layer_stack().iter().map(|&(id, _)| id).collect();
        assert!(
            !ids.contains(&x_leaf) && !ids.contains(&y_leaf),
            "the arms' `V` is sublayer-authored, so `${{V}}` resolves to neither leaf: {ids:?}",
        );

        let root_id = graph.root_id().unwrap();
        let queried: Vec<LayerId> = graph.sublayer_stack(root_id).iter().map(|&(id, _)| id).collect();
        assert_eq!(queried, ids, "sublayer_stack matches the composed root stack");
    }

    /// Overrides win over the stack root's own variables, but an unrelated override
    /// leaves the root's variable in place (C++ `PcpExpressionVariables`). A
    /// reference target authoring `V=a` and a `${V}` sublayer resolves to `b` under
    /// an arc override `V=b`, and back to `a` under an unrelated override.
    #[test]
    fn override_precedence() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        set_expr_var(&mut target, "V", "a");
        edit_layer(&mut target, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let a = sdf::Layer::new_in_memory("a.usda");
        let b = sdf::Layer::new_in_memory("b.usda");
        let mut graph = LayerGraph::from_layers(vec![root, target, a, b], 0, sdf::LayerRegistry::default());
        let target = graph.id_of("target.usda").unwrap();
        let a_id = graph.id_of("a.usda").unwrap();
        let b_id = graph.id_of("b.usda").unwrap();

        let members = |graph: &LayerGraph, id: LayerStackId| -> Vec<LayerId> {
            graph.layer_stack(id).iter().map(|&(l, _)| l).collect()
        };

        let over = HashMap::from([("V".to_string(), Value::String("b".to_string()))]);
        let id = graph.ensure_external_stack(target, &over);
        let m = members(&graph, id);
        assert!(
            m.contains(&b_id) && !m.contains(&a_id),
            "override V=b wins over the root's V=a: {m:?}"
        );

        let unrelated = HashMap::from([("OTHER".to_string(), Value::String("z".to_string()))]);
        let id = graph.ensure_external_stack(target, &unrelated);
        let m = members(&graph, id);
        assert!(
            m.contains(&a_id) && !m.contains(&b_id),
            "an unrelated override keeps the root's V=a: {m:?}"
        );
    }

    /// A `${VAR}` sublayer resolved by a **root**-authored variable back to an
    /// ancestor is a cycle, and it is reported once. The root authors `BACK=root`
    /// and sublayers `a`, whose `${BACK}` sublayer resolves to `root.usda`, closing a
    /// `root → a → root` cycle. Each layer still composes once.
    #[test]
    fn root_var_sublayer_cycle() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        set_expr_var(&mut root, "BACK", "root");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["a.usda"]);
        });
        let mut a = sdf::Layer::new_in_memory("a.usda");
        edit_layer(&mut a, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${BACK}.usda"`"#]);
        });

        let graph = LayerGraph::from_layers(vec![root, a], 0, sdf::LayerRegistry::default());
        let root_id = graph.root_id().unwrap();
        let a_id = graph.id_of("a.usda").unwrap();

        let cycles = graph
            .errors()
            .iter()
            .filter(|e| matches!(e, Error::SublayerCycle { .. }))
            .count();
        assert_eq!(cycles, 1, "the root<->a cycle is reported once: {:?}", graph.errors());

        let ids: Vec<LayerId> = graph.root_layer_stack().iter().map(|&(id, _)| id).collect();
        assert_eq!(
            ids.iter().filter(|&&id| id == root_id).count(),
            1,
            "root composes once: {ids:?}"
        );
        assert_eq!(
            ids.iter().filter(|&&id| id == a_id).count(),
            1,
            "a composes once: {ids:?}"
        );
    }

    /// Editing the **stack root**'s `expressionVariables` re-resolves its `${V}`
    /// sublayer: the root is a member of its stack, so the scoped rebuild recomposes
    /// it. (A sublayer's variables would be ignored; only the root's apply.)
    #[test]
    fn edit_root_var_rebuilds() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        set_expr_var(&mut root, "V", "leaf");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let leaf = sdf::Layer::new_in_memory("leaf.usda");
        let leaf2 = sdf::Layer::new_in_memory("leaf2.usda");
        let mut graph = LayerGraph::from_layers(vec![root, leaf, leaf2], 0, sdf::LayerRegistry::default());
        let root_id = graph.root_id().unwrap();
        let leaf = graph.id_of("leaf.usda").unwrap();
        let leaf2 = graph.id_of("leaf2.usda").unwrap();

        let ids: Vec<LayerId> = graph.root_layer_stack().iter().map(|&(id, _)| id).collect();
        assert!(
            ids.contains(&leaf) && !ids.contains(&leaf2),
            "the root's V starts at leaf: {ids:?}"
        );

        set_expr_var(&mut graph.nodes.get_mut(&root_id).unwrap().layer, "V", "leaf2");
        graph.recompute_sublayers(Some(&HashSet::from([root_id])));

        let ids: Vec<LayerId> = graph.root_layer_stack().iter().map(|&(id, _)| id).collect();
        assert!(
            ids.contains(&leaf2) && !ids.contains(&leaf),
            "the edit to the root's V re-resolves `${{V}}` to leaf2: {ids:?}",
        );
    }

    /// A plain target stack, rebuilt after an edit adds a branch reaching an
    /// expression sublayer, picks it up: `has_expr_sublayer` gates on the current
    /// `children`, and the branch's `${V}` resolves against the target root's own
    /// variable.
    #[test]
    fn plain_target_new_branch() {
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut target = sdf::Layer::new_in_memory("target.usda");
        set_expr_var(&mut target, "V", "leaf");
        edit_layer(&mut target, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["base.usda"]);
        });
        let base = sdf::Layer::new_in_memory("base.usda");
        let mut expr_mid = sdf::Layer::new_in_memory("expr_mid.usda");
        edit_layer(&mut expr_mid, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers([r#"`"${V}.usda"`"#]);
        });
        let leaf = sdf::Layer::new_in_memory("leaf.usda");
        let mut graph = LayerGraph::from_layers(
            vec![root, target, base, expr_mid, leaf],
            0,
            sdf::LayerRegistry::default(),
        );
        let target_id = graph.id_of("target.usda").unwrap();
        let base_id = graph.id_of("base.usda").unwrap();
        let leaf = graph.id_of("leaf.usda").unwrap();

        // `target` is a DAG root, so its plain stack is interned; no expression
        // sublayer is reachable yet.
        let ids: Vec<LayerId> = graph.sublayer_stack(target_id).iter().map(|&(id, _)| id).collect();
        assert!(!ids.contains(&leaf), "no expression branch reachable yet: {ids:?}");

        // Add the expression branch under `base` and rebuild with `base` edited: it
        // is a member of the interned target stack, so that stack rebuilds.
        edit_layer(&mut graph.nodes.get_mut(&base_id).unwrap().layer, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["expr_mid.usda"]);
        });
        graph.recompute_sublayers(Some(&HashSet::from([base_id])));

        let ids: Vec<LayerId> = graph.sublayer_stack(target_id).iter().map(|&(id, _)| id).collect();
        assert!(
            ids.contains(&leaf),
            "the rebuilt target reaches `${{V}}` and resolves it against the target root's V: {ids:?}",
        );
    }

    /// A sublayer interned after the first edge build is picked up on the next
    /// rebuild. `resolve_edges` resolves the authored `./leaf.usda` through the
    /// memoizing [`resolve_sublayer`](LayerGraph::resolve_sublayer) and looks the
    /// resolved identifier up live, so a target missing at first resolves once it
    /// is interned — the cache never pins the earlier miss.
    #[test]
    fn rebuild_resolves_newly_interned_sublayer() {
        let mut root = sdf::Layer::new_in_memory("root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["./leaf.usda"]);
        });
        let mut graph = LayerGraph::from_layers(vec![root], 0, sdf::LayerRegistry::default());
        let root_id = graph.root_id().unwrap();
        assert_eq!(
            graph.sublayer_stack(root_id).len(),
            1,
            "the not-yet-interned sublayer contributes no edge"
        );

        graph.ensure_layer(sdf::Layer::new_in_memory("leaf.usda"));
        graph.recompute_sublayers(None);
        let leaf = graph.id_of("leaf.usda").unwrap();
        let ids: Vec<LayerId> = graph.sublayer_stack(root_id).iter().map(|&(id, _)| id).collect();
        assert_eq!(
            ids,
            vec![root_id, leaf],
            "the newly interned sublayer resolves on rebuild"
        );
    }

    /// Relocate conflicts are scoped to the stack being composed. A layer that is
    /// weak in one stack can still contribute when referenced as its own stack.
    #[test]
    fn mute_keeps_relocate_scope() {
        let reloc = |id: &str, source: &str, target: &str| {
            let mut layer = sdf::Layer::new_in_memory(id);
            edit_layer(&mut layer, |e| {
                e.set_relocates(vec![(Path::new(source).unwrap(), Path::new(target).unwrap())])
                    .unwrap();
            });
            layer
        };
        let root = sdf::Layer::new_in_memory("root.usda");
        let mut combo = sdf::Layer::new_in_memory("combo.usda");
        edit_layer(&mut combo, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["s1.usda", "s2.usda"]);
        });
        // s1 and s2 relocate different sources to the same target, conflicting
        // within combo's stack so both are dropped while combo is present.
        let s1 = reloc("s1.usda", "/W/A", "/W/C");
        let s2 = reloc("s2.usda", "/W/B", "/W/C");
        let mut graph = LayerGraph::from_layers(vec![root, combo, s1, s2], 0, sdf::LayerRegistry::default());
        let combo_id = graph.id_of("combo.usda").unwrap();
        let s1_id = graph.id_of("s1.usda").unwrap();
        let s2_id = graph.id_of("s2.usda").unwrap();
        // The sub-stack handles are minted on demand at the load barrier in
        // production; these direct relocate queries compose nothing, so mint them via
        // `ensure_external_stack`. The handles stay valid across the mute below (the
        // registry refreshes instances in place).
        let combo_stack = graph.ensure_external_stack(combo_id, &HashMap::new());
        let s1_stack = graph.ensure_external_stack(s1_id, &HashMap::new());
        let s2_stack = graph.ensure_external_stack(s2_id, &HashMap::new());

        assert_eq!(
            graph.relocation_source(combo_stack, &Path::new("/W/C").unwrap()),
            None,
            "combo's stack drops the same-target relocates"
        );
        assert_eq!(
            graph.relocation_source(s1_stack, &Path::new("/W/C").unwrap()),
            Some(Path::new("/W/A").unwrap()),
            "s1's own stack keeps its authored relocate active"
        );

        let change = graph
            .mute_layer("combo.usda".to_string())
            .expect("muting combo changed the set");
        assert_eq!(
            change.affected,
            HashSet::from([combo_id]),
            "muting combo affects only stacks that include combo"
        );
        assert_eq!(
            graph.relocation_source(s2_stack, &Path::new("/W/C").unwrap()),
            Some(Path::new("/W/B").unwrap()),
            "s2's own stack keeps its authored relocate active"
        );
    }

    /// An authored relative path anchors against its parent's identifier and
    /// resolves to the layer interned under the canonical (absolute) identifier
    /// the load path would have produced; an unrelated leaf resolves to `None`.
    /// On-disk files are used so the resolver canonicalizes the `./` and bare
    /// spellings to the same absolute identifier the sublayer is interned under.
    #[test]
    fn find_relative_resolves_authored() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("root.usda"), b"#usda 1.0\n").unwrap();
        std::fs::write(tmp.path().join("sub.usda"), b"#usda 1.0\n").unwrap();
        let canonical = |leaf: &str| {
            tmp.path()
                .join(leaf)
                .canonicalize()
                .unwrap()
                .to_string_lossy()
                .into_owned()
        };

        let graph = LayerGraph::from_layers(
            vec![
                sdf::Layer::new(canonical("root.usda"), Box::new(sdf::Data::new())),
                sdf::Layer::new(canonical("sub.usda"), Box::new(sdf::Data::new())),
            ],
            0,
            sdf::LayerRegistry::default(),
        );
        let root_id = graph.root_id().unwrap();
        let sub_id = graph.id_of(&canonical("sub.usda")).unwrap();

        assert_eq!(graph.find_relative("sub.usda", root_id), Some(sub_id));
        assert_eq!(graph.find_relative("./sub.usda", root_id), Some(sub_id));
        assert_eq!(graph.find_relative("missing.usda", root_id), None);
    }

    /// When anchoring finds no interned layer, resolution falls back to the bare
    /// authored string, so an in-memory graph keyed by literal identifiers still
    /// composes. A directory-bearing parent (`/proj/root.usda`) anchors the bare
    /// `sub.usda` to `/proj/sub.usda`; with nothing interned there, the fallback
    /// matches the child interned under the literal `sub.usda`.
    #[test]
    fn find_relative_falls_back_to_bare_interned() {
        let mut root = sdf::Layer::new_in_memory("/proj/root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["sub.usda"]);
        });
        let sub = sdf::Layer::new_in_memory("sub.usda");

        let graph = LayerGraph::from_layers(vec![root, sub], 0, sdf::LayerRegistry::default());
        let root_id = graph.root_id().unwrap();
        let sub_id = graph.id_of("sub.usda").unwrap();

        assert_eq!(graph.find_relative("sub.usda", root_id), Some(sub_id));
        let ids: Vec<LayerId> = graph.sublayer_stack(root_id).iter().map(|&(id, _)| id).collect();
        assert_eq!(
            ids,
            vec![root_id, sub_id],
            "the bare-named sublayer edge forms via the bare-id fallback"
        );
    }

    /// When both the anchored target and an unrelated layer interned under the
    /// bare authored string are present, the anchored identifier wins: a relative
    /// sublayer resolves to the asset USD anchors it to, not to the colliding
    /// bare-named layer. On-disk files give the parent a real location so its
    /// relative `sub.usda` canonicalizes to the interned anchored layer.
    #[test]
    fn find_relative_prefers_anchored_over_bare_collision() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("root.usda"), b"#usda 1.0\n").unwrap();
        std::fs::write(tmp.path().join("sub.usda"), b"#usda 1.0\n").unwrap();
        let canonical = |leaf: &str| {
            tmp.path()
                .join(leaf)
                .canonicalize()
                .unwrap()
                .to_string_lossy()
                .into_owned()
        };

        let graph = LayerGraph::from_layers(
            vec![
                sdf::Layer::new(canonical("root.usda"), Box::new(sdf::Data::new())),
                sdf::Layer::new(canonical("sub.usda"), Box::new(sdf::Data::new())),
                // An unrelated layer interned under the bare authored string.
                sdf::Layer::new("sub.usda", Box::new(sdf::Data::new())),
            ],
            0,
            sdf::LayerRegistry::default(),
        );
        let root_id = graph.root_id().unwrap();
        let anchored_id = graph.id_of(&canonical("sub.usda")).unwrap();

        assert_eq!(
            graph.find_relative("sub.usda", root_id),
            Some(anchored_id),
            "the relative entry resolves to the anchored on-disk asset, not the colliding bare layer",
        );
    }

    /// A leading `./` is normalized before resolution, so a dot-relative entry
    /// resolves to a bare-interned child. Anchoring `./sub.usda` against
    /// `/proj/root.usda` yields `/proj/sub.usda`; with nothing interned there, the
    /// normalized bare `sub.usda` matches via the fallback.
    #[test]
    fn find_relative_strips_dot() {
        let mut root = sdf::Layer::new_in_memory("/proj/root.usda");
        edit_layer(&mut root, |e| {
            e.pseudo_root_mut().unwrap().set_sublayers(["./sub.usda"]);
        });
        let sub = sdf::Layer::new_in_memory("sub.usda");

        let graph = LayerGraph::from_layers(vec![root, sub], 0, sdf::LayerRegistry::default());
        let root_id = graph.root_id().unwrap();
        let sub_id = graph.id_of("sub.usda").unwrap();

        assert_eq!(graph.find_relative("./sub.usda", root_id), Some(sub_id));
        assert_eq!(
            graph.find_relative("././sub.usda", root_id),
            Some(sub_id),
            "repeated leading `./` is normalized too"
        );
        let ids: Vec<LayerId> = graph.sublayer_stack(root_id).iter().map(|&(id, _)| id).collect();
        assert_eq!(
            ids,
            vec![root_id, sub_id],
            "the dot-relative entry resolves to the bare-interned child"
        );
    }

    /// `.` path segments are dropped, anywhere in an asset path, rendered with
    /// `/` separators — matching the resolver's anchored normalization so the
    /// exact and anchored lookups agree. On Windows a `\`-spelled `.` segment is
    /// recognized too, since `std::path` (and thus the resolver) treats `\` as a
    /// separator there.
    #[test]
    fn dot_segments_normalized() {
        assert_eq!(&*without_dot_segments("./sub.usda"), "sub.usda");
        assert_eq!(&*without_dot_segments("././sub.usda"), "sub.usda");
        assert_eq!(&*without_dot_segments("dir/./sub.usda"), "dir/sub.usda");
        assert_eq!(&*without_dot_segments("/abs/./path"), "/abs/path");
        assert_eq!(
            &*without_dot_segments("sub.usda"),
            "sub.usda",
            "no `.` segment is unchanged"
        );
        #[cfg(windows)]
        {
            assert_eq!(&*without_dot_segments(".\\sub.usda"), "sub.usda");
            assert_eq!(&*without_dot_segments("dir\\.\\sub.usda"), "dir/sub.usda");
        }
    }

    /// `find_relative` follows the resolver's canonicalization rather than raw
    /// path matching: a resolver that aliases an authored `link.usda` to a fixed
    /// canonical leaf resolves the authored name to the layer interned under that
    /// different leaf — what a symlinked or repository-aliased sublayer needs.
    #[test]
    fn find_relative_follows_resolver_canonicalization() {
        let registry = sdf::LayerRegistry::new(Box::new(LinkResolver {
            inner: ar::DefaultResolver::new(),
        }));
        let graph = LayerGraph::from_layers(
            vec![
                sdf::Layer::new("/canonical/root.usda", Box::new(sdf::Data::new())),
                sdf::Layer::new("/canonical/real.usda", Box::new(sdf::Data::new())),
            ],
            0,
            registry,
        );
        let root_id = graph.root_id().unwrap();
        let real_id = graph.id_of("/canonical/real.usda").unwrap();

        assert_eq!(
            graph.find_relative("link.usda", root_id),
            Some(real_id),
            "the authored leaf resolves through the resolver to the canonical layer"
        );
    }

    /// A resolver whose `create_identifier` aliases an authored `link.usda` to a
    /// fixed canonical leaf, modeling a symlinked or repository-aliased asset the
    /// resolver canonicalizes away. Every other path falls through to the default
    /// filesystem behavior.
    struct LinkResolver {
        inner: ar::DefaultResolver,
    }

    impl ar::Resolver for LinkResolver {
        fn create_identifier(&self, asset_path: &str, anchor: Option<&ResolvedPath>) -> String {
            if asset_path.ends_with("link.usda") {
                "/canonical/real.usda".to_string()
            } else {
                self.inner.create_identifier(asset_path, anchor)
            }
        }
        fn resolve(&self, asset_path: &str) -> Option<ResolvedPath> {
            self.inner.resolve(asset_path)
        }
        fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ResolvedPath> {
            self.inner.resolve_for_new_asset(asset_path)
        }
        fn open_asset(&self, resolved_path: &ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
            self.inner.open_asset(resolved_path)
        }
    }
}
