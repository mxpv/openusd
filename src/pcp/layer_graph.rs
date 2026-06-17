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
//! Each layer's sublayer stack (the depth-first pre-order walk of its sublayer
//! edges, with offsets composed) is precomputed once per edge rebuild and cached
//! in [`sublayer_stacks`](LayerGraph::sublayer_stacks), mirroring C++
//! `PcpLayerStack`. The edges are always derived from each layer's `subLayers`
//! metadata by [`recompute_sublayers`](LayerGraph::recompute_sublayers): both an
//! ordinary `subLayers` authoring edit and the public
//! [`Stage::insert_layer`](crate::usd::Stage::insert_layer) /
//! [`remove_layer`](crate::usd::Stage::remove_layer) route through it, so
//! editing `subLayers` updates the edges and the metadata stays the single
//! source of truth — no DFS on every query, and no edge that fails to persist on
//! save.

use std::collections::{HashMap, HashSet};

use crate::ar::{ResolvedPath, Resolver};
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, LayerOffset, Path, RelocateList, Value};

use super::mapping::MapFunction;
use super::prim_index::find_layer_id;
use super::relocates::{chain_through_relocates, validate_layer_relocates};
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

/// Internal handle to one of a [`LayerGraph`]'s canonical layer stacks: the
/// stage root layer stack, or the sublayer stack rooted at a single layer.
///
/// Every composition [`Node`](super::prim_graph::Node) sits on one of these
/// stacks — a top-level prim and its relocate/variant/class arcs scan the root
/// stack, a reference or payload scans the target asset's sublayer stack — so a
/// node stores this `Copy` handle instead of cloning the stack's members. The
/// graph owns the members in [`root_stack`](LayerGraph::root_stack) and
/// [`sublayer_stacks`](LayerGraph::sublayer_stacks); resolve a handle back to
/// them with [`LayerGraph::layer_stack`].
///
/// Keyed by the stack's root (the stage root, or a layer id), so a handle stays
/// valid across a mute or `subLayers` rebuild even though the resolved members
/// change. Unlike [`LayerStackIdentifier`], this is not a cross-stage identity
/// key — it is only meaningful within the [`LayerGraph`] that minted it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) enum LayerStackId {
    /// The stage root layer stack (session layers, the root layer, its sublayers).
    Root,
    /// The sublayer stack rooted at this layer.
    Sublayer(LayerId),
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

/// A single layer in the [`LayerGraph`].
pub(crate) struct LayerNode {
    /// The loaded layer (identifier + backing data + authoring surface).
    pub layer: sdf::Layer,
    /// Sublayer edges in declared order, each paired with the effective layer
    /// offset for that hop (the authored `subLayerOffset` with the
    /// time-codes-per-second retiming folded in, per spec 10.3.1.1 / 12.3.2).
    pub children: Vec<(LayerId, LayerOffset)>,
    /// The validated authored `layerRelocates` pairs `(source, target)` in this
    /// layer's own namespace (conflicting and structurally invalid pairs already
    /// dropped). Empty when the layer authors none.
    pub relocates: RelocateList,
}

impl LayerNode {
    /// A node wrapping `layer`, with no edges and no relocates. The sublayer
    /// edges and relocates are filled in by
    /// [`LayerGraph::recompute_sublayers`].
    fn new(layer: sdf::Layer) -> Self {
        Self {
            layer,
            children: Vec::new(),
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
    /// asset-path resolution (`find`) and identifier listing are stable. The
    /// first [`session_layer_count`](Self::session_layer_count) entries are the
    /// session layers, in strength order.
    order: Vec<LayerId>,
    /// Number of session layers at the front of [`order`](Self::order).
    session_layer_count: usize,
    /// The root layer's id (the first non-session layer), if any.
    root: Option<LayerId>,
    /// Muted layer identifiers — the source of truth for muting (C++
    /// `PcpCache`'s muted-layer set), kept by identifier so a layer can be muted
    /// before it is loaded. Excludes the root layer's identifier, which cannot be
    /// muted. The root layer can be muted neither here nor in
    /// [`muted`](Self::muted).
    muted_identifiers: HashSet<String>,
    /// The interned ids of [`muted_identifiers`](Self::muted_identifiers),
    /// re-resolved on every stack rebuild and excluded when materializing the
    /// stacks (C++ `PcpLayerStack::_BuildLayerStack`). A muted layer and its whole
    /// sublayer subtree are pruned from every stack while staying interned, so
    /// unmute is a rebuild. Re-resolving on each rebuild lets a layer muted before
    /// it was loaded take effect the moment it is interned. Empty by default,
    /// leaving composition unchanged.
    muted: HashSet<LayerId>,
    /// Precomputed sublayer stack for each layer (its DFS pre-order with offsets
    /// composed), rebuilt by [`rebuild_sublayer_stacks`](Self::rebuild_sublayer_stacks)
    /// whenever the edges change. Avoids re-walking the edges per query.
    sublayer_stacks: HashMap<LayerId, Vec<(LayerId, LayerOffset)>>,
    /// Precomputed stage root layer stack — session layers (identity offset)
    /// then the root layer and its sublayers — rebuilt alongside
    /// [`sublayer_stacks`](Self::sublayer_stacks). Every per-prim build reads it,
    /// so caching it avoids re-allocating the same Vec per prim.
    root_stack: Vec<(LayerId, LayerOffset)>,
    /// Whether any node authors validated relocates. The indexer reads this to
    /// gate its relocate passes without rescanning.
    has_relocates: bool,
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
    /// Resolver used to locate and anchor relative asset paths. Its
    /// [`identity`](Resolver::identity) is the resolver component of the stack's
    /// [`layer_stack_id`](Self::layer_stack_id).
    resolver: Box<dyn Resolver>,
    /// Whether payload arcs should be expanded during composition.
    load_payloads: bool,
}

impl LayerGraph {
    /// Builds the graph from collected layers in strength order (session layers
    /// first, then the root layer and the rest). The recoverable layer-stack
    /// errors it detects (sublayer cycles, invalid relocates) are stored on the
    /// graph and read back through [`errors`](Self::errors).
    /// An empty graph that resolves asset paths through `resolver`. Layers join
    /// via [`ensure_layer`](Self::ensure_layer); [`finalize`](Self::finalize)
    /// wires the sublayer DAG once they are all added. The stage builds a graph
    /// this way so it can attach a change sink to each layer as it joins;
    /// [`from_layers`](Self::from_layers) is the all-at-once convenience.
    pub(crate) fn new(resolver: Box<dyn Resolver>, load_payloads: bool) -> Self {
        Self {
            nodes: HashMap::new(),
            by_identifier: HashMap::new(),
            next_id: 0,
            order: Vec::new(),
            session_layer_count: 0,
            root: None,
            muted_identifiers: HashSet::new(),
            muted: HashSet::new(),
            sublayer_stacks: HashMap::new(),
            root_stack: Vec::new(),
            has_relocates: false,
            cycle_errors: Vec::new(),
            relocate_errors: Vec::new(),
            resolver,
            load_payloads,
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
        self.build_sublayer_edges();
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

    /// Resolves every layer's `subLayers` into [`LayerNode::children`] edges,
    /// folding the per-hop time-codes-per-second retiming into each edge offset.
    /// Replaces [`cycle_errors`](Self::cycle_errors) with the sublayer-cycle
    /// errors reachable from the root layer (C++ `PcpErrorSublayerCycle`).
    fn build_sublayer_edges(&mut self) {
        // Start from a clean slate so a rebuild after a `subLayers` edit does not
        // accumulate stale edges.
        for node in self.nodes.values_mut() {
            node.children.clear();
        }
        let root_path = Path::abs_root();
        // Edges are resolved into a side buffer so the immutable `find` borrow
        // does not clash with the per-node mutation.
        let mut all_edges: Vec<(LayerId, Vec<(LayerId, LayerOffset)>)> = Vec::new();
        for &id in &self.order {
            let node = &self.nodes[&id];
            let parent_tcps = effective_time_codes_per_second(&node.layer);
            let Ok(Value::StringVec(sub_paths)) = node
                .layer
                .data()
                .get_field(&root_path, FieldKey::SubLayers.as_str())
                .map(|v| v.into_owned())
            else {
                continue;
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

            let mut edges = Vec::new();
            for (i, sub_path) in sub_paths.into_iter().enumerate() {
                let Some(sub_id) = self.find(&sub_path) else {
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
            all_edges.push((id, edges));
        }

        for (id, edges) in all_edges {
            self.nodes.get_mut(&id).expect("edge source exists").children = edges;
        }

        self.rebuild_sublayer_stacks();
        self.recompute_cycle_errors();
    }

    /// Replaces [`cycle_errors`](Self::cycle_errors) with the sublayer cycles
    /// reachable from the root layer through non-muted edges. Run after an edge
    /// rebuild and after a mute change, since muting a layer breaks any cycle
    /// running through it.
    fn recompute_cycle_errors(&mut self) {
        let mut errors = Vec::new();
        if let Some(root) = self.root {
            let mut ancestors = HashSet::new();
            self.detect_cycles(root, &mut ancestors, &mut errors);
        }
        self.cycle_errors = errors;
    }

    /// Recomputes the cached sublayer stack for every layer from the current
    /// edges. Run after any edge mutation so [`sublayer_stack`](Self::sublayer_stack)
    /// and its callers read up-to-date stacks.
    fn rebuild_sublayer_stacks(&mut self) {
        // Re-resolve the muted identifiers to ids first, so a layer muted before
        // it was loaded takes effect the moment a later edit interns it and
        // rebuilds the stacks.
        self.resolve_muted_ids();
        // Collect into a local map under the immutable `collect_sublayers` borrow,
        // then swap it in.
        let stacks: HashMap<LayerId, Vec<(LayerId, LayerOffset)>> = self
            .order
            .iter()
            .map(|&id| {
                let mut stack = Vec::new();
                let mut ancestors = HashSet::new();
                self.collect_sublayers(id, LayerOffset::IDENTITY, &mut stack, &mut ancestors);
                (id, stack)
            })
            .collect();
        self.sublayer_stacks = stacks;

        // The stage root stack reads from the just-rebuilt per-layer stacks, so
        // recompute it here too (session layers at identity offset, then the
        // root layer and its sublayers). Muting a session layer prunes its whole
        // sublayer subtree, mirroring the root portion's `collect_sublayers`.
        let pruned = self.muted_session_subtree();
        let mut root_stack: Vec<(LayerId, LayerOffset)> = self
            .session_layers()
            .iter()
            .filter(|id| !pruned.contains(id))
            .map(|&id| (id, LayerOffset::IDENTITY))
            .collect();
        if let Some(root) = self.root {
            // The root layer is never muted (the Stage API rejects it), and
            // `collect_sublayers` would prune it defensively if it ever were.
            root_stack.extend_from_slice(self.sublayer_stack(root));
        }
        self.root_stack = root_stack;
    }

    /// The session-region ids muting removes from the root stack: every muted
    /// session layer plus the sublayer descendants it would otherwise carry in.
    /// The session prefix is a flat list, so unlike the root portion (built by
    /// the subtree-pruning [`collect_sublayers`](Self::collect_sublayers)) it
    /// needs the subtree computed explicitly. Descendants are confined to the
    /// session region.
    fn muted_session_subtree(&self) -> HashSet<LayerId> {
        // The common no-mute case allocates nothing and walks nothing. This runs
        // on every stack rebuild (every `subLayers` edit, not just mutes).
        if self.muted.is_empty() {
            return HashSet::new();
        }
        let session: HashSet<LayerId> = self.session_layers().iter().copied().collect();
        let mut pruned = HashSet::new();
        let mut pending: Vec<LayerId> = session.iter().copied().filter(|id| self.is_muted(*id)).collect();
        while let Some(id) = pending.pop() {
            if !pruned.insert(id) {
                continue;
            }
            for &(child, _) in &self.nodes[&id].children {
                if session.contains(&child) {
                    pending.push(child);
                }
            }
        }
        pruned
    }

    /// Depth-first cycle scan recording [`Error::SublayerCycle`] for any edge
    /// that re-enters a layer already on the path from the root.
    fn detect_cycles(&self, id: LayerId, ancestors: &mut HashSet<LayerId>, errors: &mut Vec<Error>) {
        ancestors.insert(id);
        for &(child, _) in &self.nodes[&id].children {
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
            self.detect_cycles(child, ancestors, errors);
        }
        ancestors.remove(&id);
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

    /// Whether a layer with this id is present.
    pub(crate) fn contains(&self, id: LayerId) -> bool {
        self.nodes.contains_key(&id)
    }

    /// The resolver used to anchor relative asset paths.
    pub(crate) fn resolver(&self) -> &dyn Resolver {
        self.resolver.as_ref()
    }

    /// Resolves the location of the layer `anchor`, used to anchor the relative
    /// asset paths authored there. Returns `None` when there is no anchor layer
    /// or it cannot itself be resolved. Resolve a layer once and reuse the
    /// result to anchor every asset path it authors (see
    /// [`Resolver::create_identifier`]).
    pub(crate) fn anchor_location(&self, anchor: Option<LayerId>) -> Option<ResolvedPath> {
        anchor.and_then(|layer| self.resolver().resolve(self.identifier(layer)))
    }

    /// Whether payload arcs should be expanded during composition.
    pub(crate) fn load_payloads(&self) -> bool {
        self.load_payloads
    }

    /// Whether any layer authors validated relocates.
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

    /// Finds the id of a layer whose identifier matches `asset_path`, by exact
    /// or suffix match, then by resolver anchoring for parent-relative paths.
    /// Iterates in collection order so the result is deterministic.
    pub(crate) fn find(&self, asset_path: &str) -> Option<LayerId> {
        find_layer_id(asset_path, &self.order, |id| self.layer(id), self.resolver.as_ref())
    }

    /// The layer ids + effective offsets of the sublayer stack rooted at
    /// `root_layer` (spec 10.3.1.1): the depth-first pre-order walk of its
    /// sublayer edges with offsets composed through nested sublayers, read from
    /// the precomputed cache. A layer that sublayers itself transitively is a
    /// cycle and is skipped; an off-path duplicate is expanded again. Empty for
    /// an unknown layer. Callers needing an owned copy call `.to_vec()`.
    pub(crate) fn sublayer_stack(&self, root_layer: LayerId) -> &[(LayerId, LayerOffset)] {
        self.sublayer_stacks
            .get(&root_layer)
            .map(Vec::as_slice)
            .unwrap_or_default()
    }

    fn collect_sublayers(
        &self,
        id: LayerId,
        effective: LayerOffset,
        stack: &mut Vec<(LayerId, LayerOffset)>,
        ancestors: &mut HashSet<LayerId>,
    ) {
        // A muted layer contributes nothing: skip it and its whole subtree, so a
        // muted sublayer (or a muted root handed to `sublayer_stack`) prunes the
        // entire branch rather than just the one node.
        if self.is_muted(id) {
            return;
        }
        stack.push((id, effective));
        ancestors.insert(id);
        for &(child, edge_offset) in &self.nodes[&id].children {
            if ancestors.contains(&child) {
                continue;
            }
            self.collect_sublayers(child, effective.concatenate(&edge_offset), stack, ancestors);
        }
        ancestors.remove(&id);
    }

    /// The stage's root layer stack: session layers (identity offset) followed by
    /// the root layer and its sublayers with their effective offsets (spec
    /// 10.3.1). The set of layers a top-level prim index scans for local opinions.
    /// Read from the precomputed cache; callers needing an owned copy call
    /// `.to_vec()`.
    pub(crate) fn root_layer_stack(&self) -> &[(LayerId, LayerOffset)] {
        &self.root_stack
    }

    /// The handle for the stage root layer stack, the ambient a top-level prim
    /// composes against.
    pub(crate) fn root_layer_stack_id(&self) -> LayerStackId {
        LayerStackId::Root
    }

    /// The handle for the sublayer stack rooted at `root`, the ambient a
    /// reference or payload to that layer composes against.
    pub(crate) fn sublayer_stack_id(&self, root: LayerId) -> LayerStackId {
        LayerStackId::Sublayer(root)
    }

    /// Resolves a [`LayerStackId`] back to its members (the `(layer id, effective
    /// offset)` pairs in strength order), reading the precomputed
    /// [`root_stack`](Self::root_stack) or [`sublayer_stacks`](Self::sublayer_stacks).
    /// Empty for the sublayer stack of an unknown or muted root layer.
    pub(crate) fn layer_stack(&self, id: LayerStackId) -> &[(LayerId, LayerOffset)] {
        match id {
            LayerStackId::Root => &self.root_stack,
            LayerStackId::Sublayer(root) => self.sublayer_stack(root),
        }
    }

    /// The strongest (representative) layer of the stack `id` — its
    /// [`layer_stack`](Self::layer_stack)'s first member — or
    /// [`LayerId::INVALID`] when the stack is empty (an unknown or muted root).
    pub(crate) fn layer_stack_root(&self, id: LayerStackId) -> LayerId {
        self.layer_stack(id)
            .first()
            .map(|&(li, _)| li)
            .unwrap_or(LayerId::INVALID)
    }

    /// The layer ids of the stage's root layer stack, as a set (C++ "local"
    /// layers, spec 12.3.4.5). Opinions from these outrank value-clip data.
    pub(crate) fn local_layers(&self) -> HashSet<LayerId> {
        self.root_layer_stack().iter().map(|&(id, _)| id).collect()
    }

    /// Rebuilds the sublayer edges and the validated relocate data from the
    /// current layer data, refreshing both [`cycle_errors`](Self::cycle_errors)
    /// and [`relocate_errors`](Self::relocate_errors). Called after a `subLayers`
    /// / `subLayerOffsets` edit, where the graph's edges may be stale.
    pub(crate) fn recompute_sublayers(&mut self) {
        self.build_sublayer_edges();
        self.recompute_relocates();
    }

    /// Re-derives every node's validated relocate pairs from its current layer
    /// data, replacing [`relocate_errors`](Self::relocate_errors) with the
    /// recoverable relocate diagnostics (C++ `PcpErrorInvalidAuthoredRelocates`
    /// and conflict diagnostics). Run once at construction and again whenever a
    /// `subLayers`/`layerRelocates` edit lands.
    ///
    /// Returns the layers whose validated relocates changed, so a mute toggle
    /// can fan out to the prims reading them (see
    /// [`recompose_for_mute_with_fanout`](Self::recompose_for_mute_with_fanout))
    /// without a separate before/after snapshot. Validation reads only authored
    /// layer data, so each layer's new pairs are moved out of `validated` rather
    /// than cloned.
    pub(crate) fn recompute_relocates(&mut self) -> HashSet<LayerId> {
        let (mut validated, errors) = validate_layer_relocates(self);
        self.has_relocates = false;
        let mut changed = HashSet::new();
        for &id in &self.order {
            let pairs = validated.remove(&id).unwrap_or_default();
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

    /// The set of layer-id sets, one per sublayer stack (one rooted at each
    /// layer) plus the stage root stack. Used to scope relocate conflicts to
    /// within a single layer stack (C++ `Pcp_ComputeRelocationsForLayerStack`).
    pub(crate) fn relocate_conflict_scopes(&self) -> Vec<HashSet<LayerId>> {
        let mut scopes: Vec<HashSet<LayerId>> = self
            .order
            .iter()
            .map(|&id| self.sublayer_stack(id).iter().map(|&(l, _)| l).collect())
            .collect();
        scopes.push(self.local_layers());
        scopes
    }

    /// The relocation source for `target` if a layer in `ambient` relocates a
    /// prim onto it (C++ `GetIncrementalRelocatesTargetToSource`). The strongest
    /// layer wins a collision; a deletion relocate has no target and is skipped.
    pub(crate) fn relocation_source(&self, ambient: LayerStackId, target: &Path) -> Option<Path> {
        for &(layer, _) in self.layer_stack(ambient) {
            let Some(node) = self.nodes.get(&layer) else {
                continue;
            };
            if let Some((source, _)) = node.relocates.iter().find(|(_, t)| !t.is_empty() && t == target) {
                return Some(source.clone());
            }
        }
        None
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

    /// The as-authored relocates of `ambient`, strongest layer first, duplicate
    /// sources dropped (C++ `GetIncrementalRelocates*`). Not chained.
    fn incremental_relocates(&self, ambient: LayerStackId) -> RelocateList {
        let mut pairs: RelocateList = Vec::new();
        for &(layer, _) in self.layer_stack(ambient) {
            let Some(node) = self.nodes.get(&layer) else {
                continue;
            };
            for (source, target) in &node.relocates {
                if !pairs.iter().any(|(s, _)| s == source) {
                    pairs.push((source.clone(), target.clone()));
                }
            }
        }
        pairs
    }

    /// Chains the per-layer authored relocates of `ambient` into a single
    /// source→target map (C++ `GetRelocatesSourceToTarget`): a target that is
    /// itself a relocation source follows on to the final target, and a relocate
    /// authored *under* another's target contributes a combined
    /// pre-relocation-source → final-target pair so a single map application
    /// reaches the final location through nested relocates.
    pub(crate) fn combined_relocates(&self, ambient: LayerStackId) -> RelocateList {
        let mut pairs = self.incremental_relocates(ambient);
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
        self.layer_stack(ambient).iter().find_map(|&(layer, _)| {
            self.nodes
                .get(&layer)
                .filter(|node| node.relocates.iter().any(|(s, _)| s == source))
                .map(|node| node.layer.identifier())
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
    /// `find()` resolves the path to it.
    pub(crate) fn ensure_layer(&mut self, layer: sdf::Layer) -> (LayerId, bool) {
        self.intern(layer)
    }

    /// The id of the layer whose canonical identifier is exactly `identifier`,
    /// or `None`. The exact-match counterpart to the asset-path
    /// [`find`](Self::find); the authoring surface resolves a layer this way.
    pub(crate) fn id_of(&self, identifier: &str) -> Option<LayerId> {
        self.by_identifier.get(identifier).copied()
    }

    /// Mutes the layer with the given identifier so it contributes no opinions to
    /// composition (C++ `PcpCache::RequestLayerMuting`), recomposing the
    /// muting-dependent graph state. Returns the layers whose cached prim indices
    /// the mute can invalidate (see [`mute_fanout`](Self::mute_fanout)), or `None`
    /// when nothing changed: the identifier was already muted, or it resolves to
    /// the root layer, which cannot be muted ("would lead to empty layer stacks").
    ///
    /// The layer need not be loaded; the identifier is stored and takes effect
    /// the moment a later edit interns a matching layer (see
    /// [`rebuild_sublayer_stacks`](Self::rebuild_sublayer_stacks), which
    /// re-resolves the muted identifiers).
    pub(crate) fn mute_layer(&mut self, identifier: String) -> Option<HashSet<LayerId>> {
        if self.resolves_to_root(&identifier) || !self.muted_identifiers.insert(identifier.clone()) {
            return None;
        }
        Some(self.recompose_for_mute_with_fanout(&identifier))
    }

    /// Unmutes the layer with the given identifier, restoring its opinions and
    /// recomposing. Returns the layers whose cached prim indices the unmute can
    /// invalidate (see [`mute_fanout`](Self::mute_fanout)), or `None` when the
    /// identifier was not muted.
    pub(crate) fn unmute_layer(&mut self, identifier: &str) -> Option<HashSet<LayerId>> {
        if !self.muted_identifiers.remove(identifier) {
            return None;
        }
        Some(self.recompose_for_mute_with_fanout(identifier))
    }

    /// Recomposes the muting-dependent graph state for a just-changed muted set
    /// and returns the layers whose cached prim indices the toggle of
    /// `identifier` can invalidate: the structural [`mute_fanout`](Self::mute_fanout)
    /// plus any layer whose validated relocates the recompose changed.
    ///
    /// Relocate conflicts are scoped per layer stack
    /// ([`relocate_conflict_scopes`](Self::relocate_conflict_scopes)), so muting a
    /// layer can re-validate the relocates of a layer *outside* the muted subtree
    /// — two relocates that conflicted only by co-occurring in the muted layer's
    /// stack become valid once it is pruned. A prim composing against such a layer
    /// through a separate arc keeps no muted layer in its node stacks, so the
    /// structural fanout alone would leave it cached with the old relocate
    /// structure. The recompose reports exactly the layers whose validated
    /// relocates flipped, and the prims that read them are then found by their
    /// node stacks.
    fn recompose_for_mute_with_fanout(&mut self, identifier: &str) -> HashSet<LayerId> {
        let mut affected = self.mute_fanout(identifier);
        affected.extend(self.recompose_for_mute());
        affected
    }

    /// The interned layers a (un)mute of `identifier` can invalidate: the layer
    /// it resolves to and every layer whose `subLayers` subtree contains it.
    /// Empty when the identifier names no loaded layer — muting a not-yet-loaded
    /// layer changes no composed index.
    ///
    /// A composed prim index is affected by toggling `identifier` exactly when
    /// one of its nodes resolves against a layer stack containing the toggled
    /// layer, and a sublayer stack contains a layer iff its root layer does, so
    /// the set's members are the stack roots whose nodes a dependent index would
    /// list. Both identifier resolution and the subtree edges are independent of
    /// the muted set, so the set is identical whether computed before muting or
    /// after unmuting.
    ///
    /// The stage root layer stack is the one stack that is not a single sublayer
    /// subtree: it glues the session layers (and their subtrees) onto the root
    /// layer's subtree. A toggle anywhere in it can change every prim that
    /// composes locally against it, and such a prim always retains the root layer
    /// in its composition (the root layer is never muted), so when a session
    /// layer is in the set the root layer is added as the anchor a dependent
    /// index is found through.
    fn mute_fanout(&self, identifier: &str) -> HashSet<LayerId> {
        let root_anchor = self.anchor_location(self.root);
        let Some(id) = self.resolve_muted_id(identifier, root_anchor.as_ref()) else {
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
    /// so the result does not depend on the current muted set.
    fn ancestors_including(&self, target: LayerId) -> HashSet<LayerId> {
        let mut found = HashSet::from([target]);
        // The sublayer DAG holds one node per loaded layer, so growing the set to
        // a fixpoint — add any layer with a child already in it, until it stops
        // growing — is cheaper than materializing a reverse-edge index.
        let mut growing = true;
        while growing {
            growing = false;
            for (&id, node) in &self.nodes {
                if !found.contains(&id) && node.children.iter().any(|&(child, _)| found.contains(&child)) {
                    found.insert(id);
                    growing = true;
                }
            }
        }
        found
    }

    /// Seeds the muted set from `identifiers` (open-time muting), dropping any
    /// that resolve to the root layer, then recomposes once. Cheaper than a
    /// `mute_layer` per identifier, which would recompose on each.
    pub(crate) fn set_muted_identifiers(&mut self, identifiers: impl IntoIterator<Item = String>) {
        for identifier in identifiers {
            if !self.resolves_to_root(&identifier) {
                self.muted_identifiers.insert(identifier);
            }
        }
        self.recompose_for_mute();
    }

    /// Whether the layer with this identifier is muted.
    pub(crate) fn is_layer_muted(&self, identifier: &str) -> bool {
        self.muted_identifiers.contains(identifier)
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
    /// drop muted layers. Returns the layers whose validated relocates changed
    /// (from [`recompute_relocates`](Self::recompute_relocates)).
    fn recompose_for_mute(&mut self) -> HashSet<LayerId> {
        self.rebuild_sublayer_stacks();
        self.recompute_cycle_errors();
        self.recompute_relocates()
    }

    /// Re-resolves [`muted_identifiers`](Self::muted_identifiers) to interned ids.
    /// Run at the start of every stack rebuild so the id set always reflects the
    /// currently-loaded layers. The set never resolves to the root layer, since
    /// the root is rejected before any identifier is inserted (see
    /// [`resolves_to_root`](Self::resolves_to_root)).
    fn resolve_muted_ids(&mut self) {
        // TODO: reclaim a muted layer's memory. C++ drops its references; here
        // the node stays interned so unmute is a rebuild and nothing is freed.
        // TODO: match C++ `Pcp_MutedLayers::_GetCanonicalLayerId` identifier
        // canonicalization — anchor a relative path per containing layer (not
        // only against the root) and strip file-format target args before
        // matching. Until then, two spellings of the same loaded layer (e.g. an
        // authored relative sublayer path and its canonical identifier) can each
        // be muted as a separate entry, so unmuting one spelling leaves the layer
        // muted through the other; muting and unmuting should key on the resolved
        // id once resolution canonicalizes reliably.
        if self.muted_identifiers.is_empty() {
            self.muted.clear();
            return;
        }
        let root_anchor = self.anchor_location(self.root);
        self.muted = self
            .muted_identifiers
            .iter()
            .filter_map(|identifier| self.resolve_muted_id(identifier, root_anchor.as_ref()))
            .collect();
    }

    /// Whether `identifier` resolves to the root layer, by the same exact-then-
    /// root-anchored matching muting uses. The single authority for rejecting a
    /// request to mute the root, regardless of the spelling the caller supplies.
    fn resolves_to_root(&self, identifier: &str) -> bool {
        match self.root {
            Some(root) => self.resolve_muted_id(identifier, self.anchor_location(self.root).as_ref()) == Some(root),
            None => false,
        }
    }

    /// Resolves a muted-layer identifier to an interned id: exact canonical match
    /// first, then the resolver-anchored form against the root layer.
    fn resolve_muted_id(&self, identifier: &str, root_anchor: Option<&ResolvedPath>) -> Option<LayerId> {
        if let Some(id) = self.id_of(identifier) {
            return Some(id);
        }
        let anchored = self.resolver.create_identifier(identifier, root_anchor);
        self.id_of(&anchored)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;

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
            resolver: Box<dyn Resolver>,
            load_payloads: bool,
        ) -> Self {
            let mut graph = Self::new(resolver, load_payloads);
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
        LayerGraph::from_layers(vec![root, sub, leaf], 0, Box::new(DefaultResolver::new()), true)
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
        let mut graph = LayerGraph::from_layers(vec![root, a, b], 0, Box::new(DefaultResolver::new()), true);
        assert!(!graph.errors().is_empty(), "the a → b → a sublayer cycle is reported");

        assert!(graph.mute_layer("b.usda".to_string()).is_some());
        assert!(
            graph.errors().is_empty(),
            "muting a layer in the cycle clears the diagnostic"
        );

        assert!(graph.unmute_layer("b.usda").is_some());
        assert!(!graph.errors().is_empty(), "unmuting restores the cycle diagnostic");
    }

    /// Muting a layer whose stack scopes a relocate conflict re-validates the
    /// relocates of layers outside its subtree, so the returned fanout must
    /// include those layers — a prim composing against one of them through a
    /// separate arc keeps no muted layer in its node stacks and would otherwise
    /// stay cached with the pre-mute relocate structure.
    #[test]
    fn mute_fanout_includes_relocate_revalidated() {
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
        let mut graph = LayerGraph::from_layers(vec![root, combo, s1, s2], 0, Box::new(DefaultResolver::new()), true);
        let (s1_id, s2_id) = (graph.id_of("s1.usda").unwrap(), graph.id_of("s2.usda").unwrap());
        assert!(
            graph.get(s1_id).unwrap().relocates.is_empty(),
            "the same-target conflict drops s1's relocate up front"
        );

        let affected = graph
            .mute_layer("combo.usda".to_string())
            .expect("muting combo changed the set");
        assert!(
            affected.contains(&s1_id) && affected.contains(&s2_id),
            "muting the conflict scope re-validates s1/s2, so both must be in the fanout"
        );
        assert!(
            !graph.get(s1_id).unwrap().relocates.is_empty(),
            "s1's relocate is valid again once combo's stack no longer scopes the conflict"
        );
    }
}
