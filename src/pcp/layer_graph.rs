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
//! [`Stage::insert_sub_layer`](crate::usd::Stage::insert_sub_layer) /
//! [`remove_sub_layer`](crate::usd::Stage::remove_sub_layer) route through it, so
//! editing `subLayers` updates the edges and the metadata stays the single
//! source of truth — no DFS on every query, and no edge that fails to persist on
//! save.

use std::collections::{HashMap, HashSet};

use crate::ar::Resolver;
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, AbstractData, LayerOffset, Path, RelocateList, Value};

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
    /// Resolver used to anchor relative asset paths when locating layers.
    resolver: Box<dyn Resolver>,
    /// Whether payload arcs should be expanded during composition.
    load_payloads: bool,
}

impl LayerGraph {
    /// Builds the graph from collected layers in strength order (session layers
    /// first, then the root layer and the rest). The recoverable layer-stack
    /// errors it detects (sublayer cycles, invalid relocates) are stored on the
    /// graph and read back through [`errors`](Self::errors).
    pub(crate) fn from_layers(
        layers: Vec<sdf::Layer>,
        session_layer_count: usize,
        resolver: Box<dyn Resolver>,
        load_payloads: bool,
    ) -> Self {
        let mut graph = Self {
            nodes: HashMap::new(),
            by_identifier: HashMap::new(),
            next_id: 0,
            order: Vec::with_capacity(layers.len()),
            session_layer_count: 0,
            root: None,
            sublayer_stacks: HashMap::new(),
            root_stack: Vec::new(),
            has_relocates: false,
            cycle_errors: Vec::new(),
            relocate_errors: Vec::new(),
            resolver,
            load_payloads,
        };

        // Mint ids and collapse duplicate identifiers (the same layer reached
        // two ways, e.g. a dependency shared by the session and root
        // collections), keeping the first occurrence.
        //
        // `session_count` tracks only the distinct session-region layers that
        // survive into `order`, so `session_layers()` (which slices the prefix)
        // can never over-read even if the caller passes duplicate identifiers
        // within the session region. The root id is captured from the original
        // root slot's `intern`, not derived from `order` afterward: if the root
        // identifier already appeared in the session collection, the root
        // occurrence collapses onto that node and `intern` returns its id, so
        // `root` still points at the right layer instead of slipping to the next
        // dependency.
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
        graph.session_layer_count = session_count;
        graph.root = root;

        graph.build_sublayer_edges();
        graph.recompute_relocates();
        graph
    }

    /// Adds `layer` as a node, minting a fresh [`LayerId`] and recording it in
    /// [`by_identifier`](Self::by_identifier) and [`order`](Self::order).
    /// Returns `(id, fresh)`: an identifier already present is left untouched
    /// (its existing node, children, and relocates survive) and reported as not
    /// fresh, so a re-added layer collapses onto its existing id.
    fn intern(&mut self, layer: sdf::Layer) -> (LayerId, bool) {
        if let Some(&id) = self.by_identifier.get(layer.identifier()) {
            return (id, false);
        }
        let id = LayerId::from_raw(self.next_id);
        self.next_id += 1;
        self.by_identifier.insert(layer.identifier().to_string(), id);
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
                .get(&root_path, FieldKey::SubLayers.as_str())
                .map(|v| v.into_owned())
            else {
                continue;
            };
            let offsets: Vec<LayerOffset> = node
                .layer
                .get(&root_path, FieldKey::SubLayerOffsets.as_str())
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

        // Replace the cycle diagnostics reachable from the root layer, matching
        // the stage-root build in the previous layer-stack model.
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
        // root layer and its sublayers).
        let mut root_stack: Vec<(LayerId, LayerOffset)> = self
            .session_layers()
            .iter()
            .map(|&id| (id, LayerOffset::IDENTITY))
            .collect();
        if let Some(root) = self.root {
            root_stack.extend_from_slice(self.sublayer_stack(root));
        }
        self.root_stack = root_stack;
    }

    /// Depth-first cycle scan recording [`Error::SublayerCycle`] for any edge
    /// that re-enters a layer already on the path from the root.
    fn detect_cycles(&self, id: LayerId, ancestors: &mut HashSet<LayerId>, errors: &mut Vec<Error>) {
        ancestors.insert(id);
        for &(child, _) in &self.nodes[&id].children {
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
    pub(crate) fn recompute_relocates(&mut self) {
        let (validated, errors) = validate_layer_relocates(self);
        self.has_relocates = false;
        for &id in &self.order {
            let pairs = validated.get(&id).cloned().unwrap_or_default();
            self.has_relocates |= !pairs.is_empty();
            self.nodes.get_mut(&id).expect("layer node exists").relocates = pairs;
        }
        self.relocate_errors = errors;
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
    pub(crate) fn relocation_source(&self, ambient: &[(LayerId, LayerOffset)], target: &Path) -> Option<Path> {
        for &(layer, _) in ambient {
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
        ambient: &[(LayerId, LayerOffset)],
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
    fn incremental_relocates(&self, ambient: &[(LayerId, LayerOffset)]) -> RelocateList {
        let mut pairs: RelocateList = Vec::new();
        for &(layer, _) in ambient {
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
    pub(crate) fn combined_relocates(&self, ambient: &[(LayerId, LayerOffset)]) -> RelocateList {
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
    pub(crate) fn is_relocation_source(&self, ambient: &[(LayerId, LayerOffset)], source: &Path) -> bool {
        self.relocation_source_layer(ambient, source).is_some()
    }

    /// Identifier of the strongest layer in `ambient` that authors a relocate
    /// whose SOURCE is `source`, or `None`.
    pub(crate) fn relocation_source_layer(&self, ambient: &[(LayerId, LayerOffset)], source: &Path) -> Option<&str> {
        ambient.iter().find_map(|&(layer, _)| {
            self.nodes
                .get(&layer)
                .filter(|node| node.relocates.iter().any(|(s, _)| s == source))
                .map(|node| node.layer.identifier())
        })
    }

    /// Ensures `layer` is present as a graph node, returning its id. An
    /// already-loaded layer (matched by identifier) is left untouched (its
    /// existing children and relocates survive, since the same layer may be
    /// sublayered from several places); an absent one joins the graph with a
    /// freshly minted id.
    ///
    /// The node must exist before a `subLayers` edit naming its asset path is
    /// rebuilt, so that [`build_sublayer_edges`](Self::build_sublayer_edges)'s
    /// `find()` resolves the path to it.
    pub(crate) fn ensure_layer(&mut self, layer: sdf::Layer) -> LayerId {
        self.intern(layer).0
    }

    /// The id of the layer whose canonical identifier is exactly `identifier`,
    /// or `None`. The exact-match counterpart to the asset-path
    /// [`find`](Self::find); the authoring surface resolves a layer this way.
    pub(crate) fn id_of(&self, identifier: &str) -> Option<LayerId> {
        self.by_identifier.get(identifier).copied()
    }
}
