//! Per-prim composition index (`PcpPrimIndex` equivalent).
//!
//! A [`PrimIndex`] records the strength-ordered list of layer specs that
//! contribute opinions to a single composed prim. See the
//! [module-level docs](super) for the full composition overview.

use std::collections::hash_map::Entry;
use std::collections::HashMap;

use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{self, Path, Value};

use super::layer_stack::LayerStackId;
use super::mapping::MapFunction;
use super::prim_graph::{ArcType, Node, NodeFlags, NodeId, PrimIndexGraph, SpecSite};
use super::prim_indexer::BuildResult;
use super::{Error, LayerGraph, LayerId, VariantFallbackMap};

/// Composition index for a single prim.
///
/// Holds the composition tree as a node arena plus a strength-order
/// projection. Value resolution walks [`nodes`](Self::nodes) (strongest first)
/// and takes the first opinion found; tree structure is reached through
/// [`root`](Self::root) / [`children`](Self::children).
#[derive(Debug, Clone, Default)]
pub struct PrimIndex {
    /// Composition graph: node arena plus strength-order projection.
    graph: PrimIndexGraph,
    /// Strength-ordered prim spec stack: one [`SpecSite`] per `(node, layer)`
    /// that authors a spec at its node's path, strongest first, so value
    /// resolution and the `prim_stack` / `property_stack` introspection read this
    /// precomputed list. Built by [`finalize_spec_stack`](Self::finalize_spec_stack)
    /// and rebuilt by the spec-tier change refresh; read through the filtered
    /// [`live_spec_sites`](Self::live_spec_sites) view. It is a resolution-time
    /// artifact, kept off [`PrimIndexGraph`] so the indexer's structural seed
    /// clone does not carry it.
    spec_stack: Vec<SpecSite>,
    /// Arena handles sorted by node path: the spec-tier refresh's site index.
    /// Every node sitting at a given path forms one contiguous run, found by
    /// binary search in [`nodes_at`](Self::nodes_at), so
    /// [`refresh_has_specs_at`](Self::refresh_has_specs_at) reaches a changed
    /// site's nodes without scanning the whole arena. A permutation of handles
    /// like the graph's strength order, holding [`NodeId`]s only — it clones no
    /// paths, so it stays cheap against the heap-backed [`Path`](crate::sdf::Path).
    /// Built once per composition by [`build_path_order`](Self::build_path_order)
    /// and carried with the index; the spec-tier refresh changes only flags, never
    /// structure, so it stays valid across an in-place refresh. Lists every arena
    /// node — inert, culled, and the synthetic root — so the refresh sees each
    /// site's full candidate set. Like [`spec_stack`](Self::spec_stack), it is kept
    /// off [`PrimIndexGraph`] so the indexer's seed clone does not carry it.
    path_order: Vec<NodeId>,
}

/// The cache's per-prim composition record: the composed [`PrimIndex`], the
/// [`CompositionContext`] its children inherit, and the recoverable errors
/// recorded while building it.
///
/// [`IndexCache`](super::index_cache::IndexCache) stores one of these per
/// composed prim in a single [`sdf::PathTable`], so a prim's index, its child
/// context, and its errors are inserted and dropped together as one unit. The
/// builder and relocate evaluation receive the table to read already-composed
/// indices; they touch only [`index`](Self::index).
pub(crate) struct PrimEntry {
    /// The composed prim index.
    pub index: PrimIndex,
    /// The context propagated from this prim to its children.
    pub context: CompositionContext,
    /// Recoverable composition errors recorded while building [`index`](Self::index),
    /// replaced wholesale on each rebuild so they always reflect the current
    /// composition.
    pub errors: Vec<Error>,
}

/// Outcome of [`PrimIndex::refresh_has_specs_at`]: what the spec-tier rescan
/// must do with the index after refreshing the affected nodes' `has_specs`.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct SpecRefresh {
    /// A contributing (non-culled) node at the site was refreshed in place.
    pub contributing: bool,
    /// The index must be rebuilt rather than refreshed in place: a culled node at
    /// the site gained a spec (un-cull and graft the target's subtree), or a
    /// contributing arc target lost its last spec (cull it like an always-empty
    /// target).
    pub needs_rebuild: bool,
}

/// A reference/payload arc's demand for a not-yet-loaded target layer, carried
/// out of the indexer (in [`BuildOutput`](super::prim_indexer::BuildOutput)) to
/// the stage's load barrier. The bare asset path alone loses the authoring
/// context the barrier needs: the referencing layer stack's expression
/// variables must overlay the target's own when the target's `subLayers` paths
/// are evaluated, so the right sublayer loads (a `${VAR}` inherited across the
/// arc resolves against the referrer's value, not only the target's local one).
#[derive(Debug, Clone)]
pub(crate) struct Demand {
    /// Anchored asset path of the not-yet-loaded reference/payload target.
    pub asset_path: String,
    /// Expression variables composed at the authoring node, overlaid on the
    /// target's own when its `subLayers` paths are evaluated (the referrer,
    /// closer to the root, wins).
    pub expr_vars: HashMap<String, Value>,
}

impl PrimIndex {
    /// Returns `true` if no layers contribute opinions for this prim.
    ///
    /// A prim with no opinions still owns the synthetic, inert tree root, and
    /// may own culled arc nodes kept only for structure, so emptiness is the
    /// absence of any node that contributes to value resolution. A node carrying
    /// its full site stack but authoring no spec at its path (an ancestral site
    /// cloned to a child with no local opinion) likewise contributes nothing.
    pub fn is_empty(&self) -> bool {
        !self
            .graph
            .iter()
            .any(|node| !node.is_inert() && !node.is_culled() && node.has_specs())
    }

    /// Returns `true` if any node that contributes opinions was introduced by a
    /// composition arc. Inert placeholders (the synthetic root, class
    /// placeholders, and the inert relocation-source / implied-relocate nodes),
    /// culled arc nodes (empty targets), and spec-less full-stack nodes do not
    /// count: they add no shared content, so a prim that only references an empty
    /// target — or only carries an inert relocate placeholder — is not treated as
    /// composed for instancing.
    pub(crate) fn has_composition_arc(&self) -> bool {
        self.arena()
            .iter()
            .any(|node| node.arc != ArcType::Root && !node.is_inert() && !node.is_culled() && node.has_specs())
    }

    /// Iterates the nodes in strength order (strongest first).
    ///
    /// This is the order value resolution uses: it walks the strength-order
    /// projection, so specializes appear last (spec 10.4.1) regardless of where
    /// they sit in the arena. Inert and culled nodes are skipped — they
    /// contribute no opinions. The iterator is cheap and re-creatable; call it
    /// again for another pass rather than collecting.
    pub fn nodes(&self) -> impl DoubleEndedIterator<Item = &Node> + Clone + '_ {
        self.all_nodes().filter(|node| !node.is_culled())
    }

    /// Iterates every retained node in strength order, including culled arc
    /// nodes (an arc whose target authors no spec). Skips inert nodes — the
    /// synthetic root and the non-contributing class placeholders implied-class
    /// propagation adds. Used for composition introspection and change tracking,
    /// where the full arc structure matters even where it contributes no
    /// opinions; value resolution uses [`nodes`](Self::nodes) instead.
    pub fn all_nodes(&self) -> impl DoubleEndedIterator<Item = &Node> + Clone + '_ {
        self.ordered_nodes().filter(|node| !node.is_inert())
    }

    /// Iterates the nodes whose sites must be tracked as dependencies of this
    /// prim. Like [`all_nodes`](Self::all_nodes) but also surfaces inert
    /// relocation-source nodes: their source site contributes no opinions yet an
    /// edit there must recompose the relocated prim, so change tracking needs the
    /// reverse-map entry.
    pub(crate) fn dependency_nodes(&self) -> impl Iterator<Item = &Node> + '_ {
        self.ordered_nodes()
            .filter(|node| !node.is_inert() || node.is_relocate_source())
    }

    /// Layer ids of reference/payload target roots this prim's composition
    /// resolved to but skipped because they were muted. Their arcs grafted no
    /// node, so these are the dependency on a muted target that toggling the mute
    /// must fan out to (see
    /// [`PrimIndexGraph::muted_external_targets`](super::prim_graph::PrimIndexGraph)).
    pub(crate) fn muted_external_targets(&self) -> &[LayerId] {
        &self.graph.muted_external_targets
    }

    /// Iterates the spec stack's live contributing sites — those whose node is
    /// neither inert nor culled, the same structural filter
    /// [`nodes`](Self::nodes) applies — each paired with its resolved node. The
    /// single home for that filter, shared by every spec-stack consumer (value
    /// resolution adds `!is_permission_denied()`; the `prim_stack` /
    /// `property_stack` introspection keeps denied sites).
    pub(crate) fn live_spec_sites(&self) -> impl Iterator<Item = (&SpecSite, &Node)> + '_ {
        self.spec_stack.iter().filter_map(|site| {
            let node = self.node(site.node);
            (!node.is_inert() && !node.is_culled()).then_some((site, node))
        })
    }

    /// Iterates every node in strength order, unfiltered — the shared projection
    /// the filtered public node iterators build on.
    fn ordered_nodes(&self) -> impl DoubleEndedIterator<Item = &Node> + Clone + '_ {
        let nodes = &self.graph.nodes;
        self.graph.strength_order.iter().map(move |id| &nodes[id.idx()])
    }

    /// Iterates `(handle, node)` pairs in strength order. Used by the subtree
    /// graft, which needs each node's [`NodeId`] to rebuild parent links. The
    /// inert synthetic root is skipped, so a grafted target's real roots become
    /// orphans that re-parent under the destination's own root.
    pub(crate) fn nodes_with_ids(&self) -> impl DoubleEndedIterator<Item = (NodeId, &Node)> + '_ {
        let nodes = &self.graph.nodes;
        self.graph
            .strength_order
            .iter()
            .map(move |&id| (id, &nodes[id.idx()]))
            .filter(|(_, node)| !node.is_inert())
    }

    /// Returns the node arena in insertion (structural) order, indexed by
    /// [`NodeId`]. Use [`nodes`](Self::nodes) for strength-ordered resolution.
    pub(crate) fn arena(&self) -> &[Node] {
        &self.graph.nodes
    }

    /// Returns the underlying composition graph. The task-queue indexer clones a
    /// parent prim's graph as the seed for its child's index (C++
    /// `_BuildInitialPrimIndexFromAncestor`).
    pub(crate) fn graph(&self) -> &PrimIndexGraph {
        &self.graph
    }

    /// Returns the root of the composition tree, or `None` when empty.
    ///
    /// The root is the synthetic, inert node created first during the build;
    /// every contributing node descends from it.
    pub fn root(&self) -> Option<NodeId> {
        self.graph.root.is_valid().then_some(self.graph.root)
    }

    /// Marks every node whose path lies under one of `prefixes`
    /// [`PERMISSION_DENIED`](NodeFlags::PERMISSION_DENIED), so value resolution
    /// skips their opinions while they stay visible structurally — the C++
    /// `_InertSubtree` behavior for a direct arc to a `permission = private`
    /// site (spec 10.3.3). The prefixes are the denied arcs' target paths, so a
    /// node reached through such an arc (its grafted subtree, an implied-class
    /// copy, or an arc extended to a descendant prim) is inerted uniformly.
    pub(crate) fn mark_permission_denied_under(&mut self, prefixes: &[Path]) {
        if prefixes.is_empty() {
            return;
        }
        for node in &mut self.graph.nodes {
            if prefixes.iter().any(|prefix| node.path.has_prefix(prefix)) {
                node.flags |= NodeFlags::PERMISSION_DENIED;
            }
        }
    }

    /// Recomputes `has_specs` from live layer data for every node sitting at
    /// site `(layer, path)`, reporting what the caller must do next.
    ///
    /// The spec-tier change rescan (C++ `Pcp_RescanForSpecs`) calls this after
    /// an inert spec add or remove, which flips only whether a site contributes
    /// an opinion — never the graph structure — so a contributing node's flag is
    /// refreshed in place without rebuilding or re-finalizing strength order. A
    /// node matches when its site path is `path` and `layer` is one of its
    /// contributing layers; its refreshed flag reflects whether any layer in its
    /// stack still authors a spec there.
    ///
    /// Two transitions are the exception, both handled by rebuilding rather than
    /// flipping in place ([`SpecRefresh::needs_rebuild`]): a *culled* node that
    /// gains a spec (un-culling it must graft the target's subtree), and a
    /// contributing arc target that loses its last spec (it must cull to match an
    /// always-empty target, so a later re-add takes the un-cull path).
    //
    // Reaches the site's nodes through the [`path_order`](Self::path_order) site
    // index ([`nodes_at`](Self::nodes_at)), so its cost scales with the number of
    // nodes at the site.
    //
    // Each node's `layer_stack` handle is resolved against the live `graph`,
    // which is sound because this rescan runs only on the spec-tier
    // (non-significant) change path: an inert spec add/remove never edits
    // `subLayers`, so the resolved members equal the node's composition-time
    // stack. A path that rebuilds sublayer stacks goes through the significant
    // branch, which drops the cached index instead of refreshing it.
    pub(crate) fn refresh_has_specs_at(&mut self, layer: LayerId, path: &Path, graph: &LayerGraph) -> SpecRefresh {
        let mut refresh = SpecRefresh::default();
        // `to_vec` copies the small candidate run of handles, releasing the
        // `path_order` borrow so the loop can mutate `graph.nodes` in place.
        for id in self.nodes_at(path).to_vec() {
            let node = &mut self.graph.nodes[id.idx()];
            let stack = node.layer_stack;
            if !graph.layer_stack(stack).iter().any(|&(li, _)| li == layer) {
                continue;
            }
            let has_specs = stack_has_spec(graph, stack, path);
            if node.is_culled() {
                // An empty arc target the spec just filled in: rebuild so the
                // arc un-culls and grafts the target's subtree.
                refresh.needs_rebuild |= has_specs && !node.has_specs;
            } else {
                refresh.contributing = true;
                // An arc target that just lost its last spec must re-cull to
                // match an always-empty target, so a later re-add takes the
                // un-cull rebuild path. The local root and inert placeholders
                // never cull.
                let lost_last_spec = node.has_specs && !has_specs;
                let cullable = node.arc != ArcType::Root && !node.is_inert();
                refresh.needs_rebuild |= lost_last_spec && cullable;
            }
            node.has_specs = has_specs;
        }
        refresh
    }

    /// Arena handles of every node sitting at `path`, in path order (empty when
    /// none) — the spec-tier refresh's candidate set. Binary-searches the
    /// [`path_order`](Self::path_order) projection for the contiguous run of nodes
    /// at the site.
    fn nodes_at(&self, path: &Path) -> &[NodeId] {
        let nodes = &self.graph.nodes;
        let lo = self.path_order.partition_point(|&id| nodes[id.idx()].path < *path);
        let hi = self.path_order.partition_point(|&id| nodes[id.idx()].path <= *path);
        &self.path_order[lo..hi]
    }

    /// Rebuilds the memoized [`spec stack`](SpecSite): the strength-ordered
    /// list of `(node, layer)` sites that author a spec at their node's path,
    /// each with the layer's time offset folded to root (the C++ `PcpPrimIndex`
    /// spec stack). Value resolution ([`opinions`](Self::opinions)) and the
    /// `prim_stack` / `property_stack` introspection read it as their precomputed
    /// candidate sites.
    ///
    /// A site is recorded where the layer authors the prim spec at the node's
    /// path (`has_spec`). A property spec requires its owning prim spec, so this
    /// is also the candidate set for property reads; an orphan property spec (one
    /// whose owning prim spec is absent, reachable only through malformed backend
    /// data) is not represented.
    ///
    /// Run by the index builder (the single composition seam) and by the
    /// spec-tier change refresh. It walks every strength-ordered node, gated on
    /// [`has_specs`](super::prim_graph::Node::has_specs) — a node with no spec on
    /// any member contributes nothing — and leaves the stack *unfiltered* by the
    /// inert / culled / permission-denied flags: those are flipped after the
    /// graph is finalized (an instance-local or permission inerting, often on a
    /// clone), so a pre-filtered stack would go stale. Consumers apply the live
    /// flag filter through [`live_spec_sites`](Self::live_spec_sites).
    ///
    /// The folded offset is stable across the refresh and across
    /// [`rebase_root`](Self::rebase_root): the spec tier never edits
    /// subLayers/offsets (those drop the index), and a rebase re-anchors only the
    /// path side of each map, leaving `map_to_root().time_offset()` intact.
    ///
    /// TODO(perf): re-reads `has_spec` per member, duplicating the indexer's own
    /// `has_specs` pass — the build could emit the spec-authoring layers it
    /// already scans. It also rebuilds the whole stack on each call; the spec-tier
    /// refresh ([`IndexCache::rescan_specs`](super::index_cache::IndexCache::rescan_specs))
    /// calls it once per affected index per change round, so splicing in only the
    /// entries of the nodes a changed site touches ([`nodes_at`](Self::nodes_at))
    /// would replace the full rebuild.
    pub(crate) fn finalize_spec_stack(&mut self, graph: &LayerGraph) {
        let mut stack = Vec::new();
        for &id in &self.graph.strength_order {
            let node = &self.graph.nodes[id.idx()];
            if !node.has_specs {
                continue;
            }
            let arc_offset = node.map_to_root.time_offset();
            for &(layer, sub) in graph.layer_stack(node.layer_stack).iter() {
                if graph.layer(layer).data().has_spec(&node.path) {
                    stack.push(SpecSite {
                        node: id,
                        layer,
                        offset: arc_offset.concatenate(&sub),
                    });
                }
            }
        }
        self.spec_stack = stack;
    }

    /// Builds [`path_order`](Self::path_order) from the finalized arena: arena
    /// handles sorted by their node's path, so the nodes at any path form a
    /// contiguous, binary-searchable run. The sort is stable, so equal-path nodes
    /// keep their arena order. Run once per composition alongside
    /// [`finalize_spec_stack`](Self::finalize_spec_stack); the spec-tier refresh
    /// changes only flags, so it reuses this projection unchanged.
    ///
    /// TODO(perf): built eagerly per composition (like `strength_order` and the
    /// spec stack), so a read-only stage that never runs a spec-tier refresh — and
    /// the common single-node prim — still pays the `Vec<NodeId>` and the sort. It
    /// could build lazily on the first
    /// [`refresh_has_specs_at`](Self::refresh_has_specs_at) (an empty order on a
    /// node-bearing index signals "not yet built"), or skip the projection for
    /// arenas small enough that a linear scan over the arena wins.
    fn build_path_order(&mut self) {
        let nodes = &self.graph.nodes;
        let mut order: Vec<NodeId> = (0..nodes.len() as u32).map(NodeId).collect();
        order.sort_by(|&a, &b| nodes[a.idx()].path.cmp(&nodes[b.idx()].path));
        self.path_order = order;
    }

    /// Classifies each node as instance-local (`true`) or shared (`false`) for an
    /// enclosing instance at `instance_depth` (spec 11.3.3), indexed by
    /// [`NodeId`] arena position. The shared nodes are the prototype subtree; the
    /// instance-local nodes are the opinions authored at the instance's own
    /// namespace, which an instance's child names, descendants, and instance key
    /// must drop.
    ///
    /// This is the C++ `!PcpNodeRef::HasTransitiveDirectDependency` partition.
    /// Instance-local = the local root plus the contiguous *trunk* of ancestral
    /// references/payloads the instance prim is nested under — the outer arcs
    /// reaching down to, but stopping above, the instanceable arc. The
    /// instanceable arc (the first reference/payload introduced at the instance's
    /// own depth) and everything below it stay shared, as do the implied classes
    /// (class-based arcs).
    ///
    /// Trunk membership is structural, not a flat depth test: a node is on the
    /// trunk only if it is a reference/payload introduced above the instance
    /// (`namespace_depth < instance_depth`) *and* its parent is also on the
    /// trunk. The parent check is what keeps a reference or payload nested
    /// *inside* the prototype (below the instanceable arc) shared — such an arc
    /// is authored in the referenced layer's namespace, so its `namespace_depth`
    /// is shallow and would otherwise be misread as an outer arc.
    ///
    /// The arena is append-only with each node's parent preceding it, so one
    /// forward pass propagates trunk-ness parent→child.
    pub(crate) fn instance_local_nodes(&self, instance_depth: u16) -> Vec<bool> {
        let nodes = &self.graph.nodes;
        let mut local = vec![false; nodes.len()];
        for (i, node) in nodes.iter().enumerate() {
            // The single forward pass only reads an already-computed parent
            // entry; a parent inserted after its child would be read as a stale
            // `false`, silently leaking an instance-local arc into the prototype.
            debug_assert!(
                node.parent.is_none_or(|p| p.idx() < i),
                "instance partition requires every node's parent to precede it in the arena"
            );
            local[i] = match node.arc {
                // The local site (and the synthetic root) is always instance-local.
                ArcType::Root => true,
                ArcType::Reference | ArcType::Payload => {
                    node.namespace_depth < instance_depth && node.parent.is_some_and(|p| local[p.idx()])
                }
                _ => false,
            };
        }
        local
    }

    /// Inerts the instance-namespace opinions on a prim composed inside an
    /// instance (spec 11.3.3), so value resolution sees only the shared subtree
    /// the instance brings in. `instance_depth` is the nearest enclosing
    /// instance prim's namespace depth; the partition is
    /// [`instance_local_nodes`](Self::instance_local_nodes).
    ///
    /// Each node is inerted individually, not its subtree: the implied classes a
    /// dropped reference helped derive are children in the graph yet stay shared.
    /// (The local root is also inerted earlier by the indexer via
    /// [`CompositionContext::within_instance`](super::prim_index::CompositionContext::within_instance).)
    pub(crate) fn mark_instance_local_inert(&mut self, instance_depth: u16) {
        let local = self.instance_local_nodes(instance_depth);
        for (node, &is_local) in self.graph.nodes.iter_mut().zip(local.iter()) {
            if is_local {
                node.flags |= NodeFlags::INERT;
            }
        }
    }

    /// Re-anchors this index's composed (root) namespace from `from` to `to`,
    /// used when a prototype is materialized from a canonical instance's subtree
    /// onto its `/__Prototype_N` root (spec 11.3.3): every node's `map_to_root` /
    /// `map_to_parent` has its composed-namespace target side moved from `from`
    /// to `to`, so target translation lands in the prototype namespace rather
    /// than the seeding instance's.
    ///
    /// `node.path` is deliberately left untouched — it is the site path in the
    /// node's own *layer* namespace, where value resolution reads specs (see
    /// [`PrimIndex::opinions`]). A contributing node whose spec lives beneath the
    /// instance's path (e.g. a selected variant at `/A{v=x}`) must keep that path
    /// so the lookup hits the real spec; rewriting it to `/__Prototype_N{v=x}`
    /// would query a layer location that does not exist.
    ///
    /// Only map targets change; node paths, arc types, namespace depths, origins,
    /// and sibling numbers are untouched, so the strength-order projection stays
    /// valid without re-finalizing.
    pub(crate) fn rebase_root(&mut self, from: &Path, to: &Path) {
        for node in &mut self.graph.nodes {
            node.map_to_root = node.map_to_root.rebase_target(from, to);
            node.map_to_parent = node.map_to_parent.rebase_target(from, to);
        }
    }

    /// Returns the node behind a handle.
    pub fn node(&self, id: NodeId) -> &Node {
        &self.graph.nodes[id.idx()]
    }

    /// Returns the structural parent of a node, or `None` for a root.
    pub fn parent(&self, id: NodeId) -> Option<NodeId> {
        self.node(id).parent
    }

    /// Returns the structural children of a node, in strength order.
    pub fn children(&self, id: NodeId) -> &[NodeId] {
        &self.node(id).children
    }

    /// Renders the composition tree for debugging (C++ `PcpPrimIndex::DumpToString`).
    ///
    /// Walks depth-first from the synthetic root, four spaces of indent per
    /// depth, with children in strength order. Each line carries the arc type,
    /// layer index, node path, strength rank, and any non-identity time offset,
    /// origin, or flags. Layers are shown by index (the index owns no layer
    /// identifiers); the output is deterministic, which makes it a useful
    /// structural harness. The graph is a single rooted tree: the inert
    /// synthetic root is the sole parent-less node, and every contributing node
    /// descends from it.
    pub fn dump_to_string(&self) -> String {
        use std::fmt::Write as _;

        let mut rank = vec![0usize; self.graph.nodes.len()];
        for (r, id) in self.graph.strength_order.iter().enumerate() {
            rank[id.idx()] = r;
        }

        let mut out = String::new();
        let mut stack: Vec<(NodeId, usize)> = self
            .graph
            .strength_order
            .iter()
            .rev()
            .filter(|id| self.node(**id).parent.is_none())
            .map(|&id| (id, 0))
            .collect();

        while let Some((id, depth)) = stack.pop() {
            let node = self.node(id);
            let _ = write!(
                out,
                "{:indent$}{:?} [{:?}] {} #{}",
                "",
                node.arc,
                node.layer_id(),
                node.path,
                rank[id.idx()],
                indent = depth * 4
            );
            let offset = node.map_to_root.time_offset();
            if !offset.is_identity() {
                let _ = write!(out, " offset=({},{})", offset.offset, offset.scale);
            }
            // Show origin only when it differs from the structural parent —
            // i.e. for implied classes and grafts. A direct arc always origins
            // on its parent, so printing it there is redundant noise.
            if let Some(origin) = node.origin {
                if Some(origin) != node.parent {
                    let _ = write!(out, " origin={}", origin.0);
                }
            }
            if !node.flags.is_empty() {
                let _ = write!(out, " {:?}", node.flags);
            }
            out.push('\n');

            // Push children in reverse so the strongest sibling pops first.
            for &child in node.children.iter().rev() {
                stack.push((child, depth + 1));
            }
        }
        out
    }

    /// Appends a node to the end of the composition graph, weakest in strength.
    ///
    /// Test-only scaffolding for assembling synthetic indices; production
    /// composition appends through [`PrimIndexGraph::add_child`] or the
    /// relocate grafts so structural links are populated.
    #[cfg(test)]
    pub(crate) fn push_node(&mut self, node: Node) {
        let id = NodeId(self.graph.nodes.len() as u32);
        // Keep `path_order` a valid sorted projection so a synthetic index built
        // through this helper drives `nodes_at` and the spec-tier refresh the same
        // way a composed one does. The new handle is the highest arena index, so it
        // sorts after any equal-path node, matching the stable `build_path_order`.
        let at = self
            .path_order
            .partition_point(|&nid| self.graph.nodes[nid.idx()].path <= node.path);
        self.graph.nodes.push(node);
        self.graph.strength_order.push(id);
        self.path_order.insert(at, id);
    }

    /// Builds a prim index for a root prim with no cached ancestors (a test
    /// convenience over [`build_with_cache`](Self::build_with_cache)). A child
    /// prim must instead be built through a cache holding its ancestors, since
    /// the indexer seeds a child from its cached parent.
    #[cfg(test)]
    pub(crate) fn build_with_context(path: &Path, stack: &LayerGraph, ctx: &CompositionContext) -> BuildResult<Self> {
        Self::build_with_cache(path, stack, ctx, &sdf::PathTable::new()).map(|(index, _errors, _pending)| index)
    }

    /// Like [`build_with_context`](Self::build_with_context) but with access to
    /// previously-composed prim indices. Cached indices are checked before
    /// building from scratch, ensuring inherit/specialize targets use the
    /// fully-composed result (including ancestor-propagated specs).
    ///
    /// The third tuple element is the [`Demand`]s a reference/payload arc raised
    /// for a target that is not yet loaded; non-empty means the returned index
    /// is incomplete and must not be cached, so the caller loads those layers
    /// and recomposes.
    pub(crate) fn build_with_cache(
        path: &Path,
        stack: &LayerGraph,
        ctx: &CompositionContext,
        cached_indices: &sdf::PathTable<PrimEntry>,
    ) -> BuildResult<(Self, Vec<Error>, Vec<Demand>)> {
        Self::build_with_cache_in(path, stack, ctx, cached_indices, stack.root_layer_stack_id())
    }

    /// Builds a prim index whose root `L` site scans the given `ambient` layer
    /// stack rather than the stage's root layer stack.
    ///
    /// `ambient` is the layer stack the prim is composed in: the root layer
    /// stack for a stage prim, or a referenced asset's sublayer stack for an
    /// arc target reached within that reference. When `ambient` is the stage
    /// root layer stack ([`LayerStackId::ROOT`]) the shared `cached_indices`
    /// (keyed by stage path) apply; an arc-target sublayer stack is composed
    /// fresh.
    pub(crate) fn build_with_cache_in(
        path: &Path,
        stack: &LayerGraph,
        ctx: &CompositionContext,
        cached_indices: &sdf::PathTable<PrimEntry>,
        ambient: LayerStackId,
    ) -> BuildResult<(Self, Vec<Error>, Vec<Demand>)> {
        if ambient == LayerStackId::ROOT {
            if let Some(cached) = cached_indices.get(path) {
                return Ok((cached.index.clone(), Vec::new(), Vec::new()));
            }
        }
        // The task-queue indexer is the sole composition path. A genuine cycle
        // surfaces as `Error::ArcCycle`; an unresolvable arc is recorded in the
        // returned errors and skipped. A `None` graph means an unestablished seed
        // or the runaway nesting backstop, which composes to an empty prim index.
        let indexer = super::prim_indexer::Indexer::new(stack, ctx, cached_indices, ambient);
        let super::prim_indexer::BuildOutput {
            graph,
            errors,
            pending_loads,
        } = indexer.build(path)?;
        let mut index = PrimIndex {
            graph: graph.unwrap_or_default(),
            spec_stack: Vec::new(),
            path_order: Vec::new(),
        };
        // Build the memoized spec stack and the path-order site index here, the
        // single seam every freshly composed index passes through, so value
        // resolution and the spec-tier refresh read them without a separate
        // finalize step. The later permission / instance-local inerting only flips
        // flags (which consumers filter live) and `rebase_root` retargets maps
        // without moving node paths, so both projections stay valid; a
        // materialized prototype clones an index that already carries them.
        index.finalize_spec_stack(stack);
        index.build_path_order();
        Ok((index, errors, pending_loads))
    }

    /// Returns the composition context derived from this prim's index.
    ///
    /// Child prims use this context to inherit ancestor arc mappings and
    /// variant selections without recomputing them.
    pub(crate) fn context_for_children(
        &self,
        stack: &LayerGraph,
        parent_ctx: &CompositionContext,
    ) -> CompositionContext {
        // Gather variant selections from this prim's nodes; ancestor selections
        // outrank this prim's local fallbacks.
        let selections = resolve_variant_selections_in(
            self.nodes(),
            stack,
            &parent_ctx.variant_fallbacks,
            &parent_ctx.selections,
        );

        // Build ancestor arcs: record every non-Root node so children can
        // remap through it. We use map_to_root (not map_to_parent) because
        // ancestor propagation needs to translate all the way to the composed
        // namespace. An arc is kept even when its path mapping is a no-op
        // (e.g. a reference whose target shares the prim's path): it still
        // crosses into another layer, so a child must follow it to reach the
        // referenced layer's descendants. Root nodes are skipped — the child's
        // own root `L` site rescans the root layer stack.
        let mut ancestor_arcs = parent_ctx.ancestor_arcs.clone();
        // Record each non-Root node's namespace mapping so a descendant prim can
        // translate a relative inherit/specialize target authored at this prim
        // into the composed namespace (cache `precache_inherit_targets`).
        for (_, node) in self.nodes_with_ids() {
            if node.arc != ArcType::Root {
                ancestor_arcs.push(AncestorArc {
                    map: node.map_to_root.clone(),
                });
            }
        }

        // Merge parent's selections (weaker) with this prim's (stronger).
        let mut merged_selections = parent_ctx.selections.clone();
        for (k, v) in selections {
            merged_selections.entry(k).or_insert(v);
        }

        CompositionContext {
            selections: merged_selections,
            ancestor_arcs,
            variant_fallbacks: parent_ctx.variant_fallbacks.clone(),
            // Inherited from the parent; the cache additionally sets this when
            // the current prim itself resolves as an instance.
            instance_depth: parent_ctx.instance_depth,
            // Carried forward; the cache appends this prim's own denied targets.
            denied_prefixes: parent_ctx.denied_prefixes.clone(),
            // A stage-wide policy, propagated unchanged to every descendant.
            load_payloads: parent_ctx.load_payloads,
        }
    }

    /// The variant selections composed onto this prim, as `(set, selection)`
    /// pairs sorted by set name. Collected from every node whose site path is a
    /// variant selection path (`/Prim{set=sel}`), strongest first, mirroring the
    /// C++ `testPcpCompositionResults` dump (which walks the node graph and
    /// records `node.path.GetVariantSelection()` for each
    /// `IsPrimVariantSelectionPath` node). This is purely structural — whatever
    /// variant branches the build grafted in, regardless of whether the
    /// selection was authored, a fallback, or a default — so it stays consistent
    /// with the variant sites shown in the prim stack.
    pub(crate) fn variant_selections(&self) -> Vec<(String, String)> {
        let mut selections: HashMap<String, String> = HashMap::new();
        for node in self.all_nodes() {
            if !node.path.is_prim_variant_selection_path() {
                continue;
            }
            if let Some(sdf::PathElement::Variant { set, selection }) = node.path.last_element() {
                selections
                    .entry(set.to_string())
                    .or_insert_with(|| selection.to_string());
            }
        }
        let mut out: Vec<(String, String)> = selections.into_iter().collect();
        out.sort();
        out
    }
}

// ---------------------------------------------------------------------------
// Composition context: flows from parent to child prim
// ---------------------------------------------------------------------------

/// Composition context carried from parent prims to children.
///
/// Contains accumulated variant selections, arc mappings, and variant
/// fallbacks that enable single-pass composition without cross-prim
/// post-processing.
#[derive(Debug, Clone)]
pub(crate) struct CompositionContext {
    /// Variant selections accumulated from all ancestor compositions.
    /// First-opinion-wins: strongest ancestor's selection takes priority.
    pub selections: HashMap<String, String>,
    /// Ancestor composition arcs with namespace mappings.
    /// Used for descendant namespace remapping and implied inherit propagation.
    pub ancestor_arcs: Vec<AncestorArc>,
    /// Variant fallback selections for sets without authored opinions.
    /// Propagated unchanged from the stage configuration.
    pub variant_fallbacks: VariantFallbackMap,
    /// Namespace depth of the nearest enclosing instance prim (spec 11.3.3),
    /// or `None` when this prim is not inside an instance. Set by the cache once
    /// an ancestor resolves as an instance and inherited by every deeper prim; a
    /// nested instance re-arms it to its own (deeper) depth. Opinions authored at
    /// the instance's own namespace — its local root and the ancestral
    /// references introduced above it (at a shallower namespace depth) — are
    /// discarded, so the subtree composes only from the arcs the instance brings
    /// in (the instanceable arc and below, plus its implied classes).
    pub instance_depth: Option<u16>,
    /// Target-namespace paths an ancestor's direct arc to a `permission =
    /// private` site denied (spec 10.3.3). A node whose path lies under one of
    /// these prefixes was reached through that denied arc, so the cache marks
    /// it `PERMISSION_DENIED` even in descendant prims composed separately
    /// (where the arc is extended, not authored here).
    pub denied_prefixes: Vec<Path>,
    /// Whether payload arcs are expanded during composition, from the stage's
    /// [`InitialLoadSet`](crate::usd::InitialLoadSet). Propagated unchanged from
    /// the root context to every descendant, a sibling of `variant_fallbacks`.
    /// Defaults to `true` (C++ `UsdStage::LoadAll`); the stage sets `false` for
    /// `LoadNone`.
    pub load_payloads: bool,
}

impl Default for CompositionContext {
    fn default() -> Self {
        Self {
            selections: HashMap::new(),
            ancestor_arcs: Vec::new(),
            variant_fallbacks: VariantFallbackMap::new(),
            instance_depth: None,
            denied_prefixes: Vec::new(),
            // Compose payloads unless the stage opts out (C++ `UsdStage::LoadAll`).
            load_payloads: true,
        }
    }
}

impl CompositionContext {
    /// `true` when this prim is composed inside an instance (spec 11.3.3), so
    /// its local opinions are discarded. Equivalent to `instance_depth.is_some()`.
    pub fn within_instance(&self) -> bool {
        self.instance_depth.is_some()
    }
}

/// Records an ancestor composition arc for descendant namespace remapping.
///
/// When `/Rig` inherits `/_class` which references `ref.usd /CharRig`,
/// the ancestor arcs record the namespace mappings `/_class → /Rig` and
/// `/CharRig → /Rig`. Children of `/Rig` use these to find their
/// composition sites in other layers via [`MapFunction`] methods.
#[derive(Debug, Clone)]
pub(crate) struct AncestorArc {
    /// Namespace mapping from this arc's source to the composed namespace.
    /// Convention: source is the arc target's namespace, target is composed.
    pub map: MapFunction,
}

// ---------------------------------------------------------------------------
// Shared helpers (used by the `Indexer` and Stage)
// ---------------------------------------------------------------------------

/// Whether any layer in `stack` authors a spec at `path` (C++
/// `PcpNode::HasSpecs`). The canonical definition of a node's `has_specs`, used
/// both when the indexer builds a node and when [`PrimIndex::refresh_has_specs_at`]
/// refreshes one after an inert spec edit, so the two never drift.
pub(super) fn stack_has_spec(graph: &LayerGraph, stack: LayerStackId, path: &Path) -> bool {
    graph
        .layer_stack(stack)
        .iter()
        .any(|&(li, _)| graph.layer(li).data().has_spec(path))
}

/// Resolves variant selections across a prim's composition nodes.
///
/// Precedence: `seed` selections inherited from the composition context win
/// first — a selection authored on a referencing prim is stronger than the
/// referenced layer's own opinion (spec 12.2), so it beats both an explicit
/// selection authored on a node here and the target's own default. Each set the
/// seed did not fix then takes its explicit node selection, nodes ordered by arc
/// type; any still-unselected set defaults to its fallback, then to its first
/// variant.
///
/// TODO: two approximations remain in the node ordering and the seed.
/// - Nodes are ordered by `ArcType` alone, not the full node-strength
///   comparator (arc type plus ancestry / origin / namespace depth). When two
///   nodes in different subtrees author the same set, arc type can pick the
///   wrong one. The full comparator needs `NodeId`/graph access and the
///   strength projection, which is not finalized while the build still calls
///   this, so the arc-type order is the build-time approximation.
/// - The seed accumulates selections by set name down the whole namespace, so a
///   namespace ancestor's selection for its *own* same-named variant set leaks
///   onto a descendant prim that has an independent set of that name,
///   overriding the descendant's local selection. Distinguishing an arc seed
///   from a namespace-ancestor seed would fix it.
fn resolve_variant_selections_in<'a>(
    nodes: impl Iterator<Item = &'a Node> + Clone,
    graph: &LayerGraph,
    variant_fallbacks: &VariantFallbackMap,
    seed: &HashMap<String, String>,
) -> HashMap<String, String> {
    let mut selections: HashMap<String, String> = HashMap::new();

    // Seed selections come from the composition context — a selection already
    // resolved on a stronger site (a referencing prim, or a namespace ancestor)
    // that this build is weaker than. They rank above this site's own opinions:
    // a `complexity=high` authored on the referencing layer stack must beat the
    // `complexity=low` the referenced layer authored locally (spec 12.2, the
    // referencing arc is stronger than the referenced opinion).
    for (set_name, selection) in seed {
        selections.entry(set_name.clone()).or_insert_with(|| selection.clone());
    }

    // Order nodes by arc strength so an explicit selection authored on a
    // stronger arc wins (spec 12.2): a selection on an inherited class beats
    // one on the referenced prim it is inherited into. `sort_by_key` is stable,
    // so nodes of equal arc strength keep their composition order. The arena's
    // strength projection is not finalized during the build, so order here by
    // the arc type directly.
    let mut ordered: Vec<&Node> = nodes.collect();
    ordered.sort_by_key(|n| n.arc);

    // Gather explicit selections for sets the seed did not already fix. Each
    // node fans out into its layer stack, strongest sublayer first.
    for node in &ordered {
        for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter() {
            if let Ok(value) = graph
                .layer(layer)
                .data()
                .get_field(&node.path, FieldKey::VariantSelection.as_str())
            {
                if let Value::VariantSelectionMap(map) = value.into_owned() {
                    for (set_name, selection) in map {
                        selections.entry(set_name).or_insert(selection);
                    }
                }
            }
        }
    }

    // For variant sets without an explicit selection, apply a configured
    // fallback if one names an existing variant. With no applicable fallback the
    // set stays unselected (C++ `_EvalNodeFallbackVariant`); there is no implicit
    // first-variant default, matching the indexer.
    for node in &ordered {
        for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter() {
            let data = graph.layer(layer).data();
            let Ok(value) = data.get_field(&node.path, ChildrenKey::VariantSetChildren.as_str()) else {
                continue;
            };
            let Value::TokenVec(set_names) = value.into_owned() else {
                continue;
            };
            for set_name in set_names {
                let Entry::Vacant(entry) = selections.entry(set_name.into()) else {
                    continue;
                };
                let set_path = node.path.append_variant_selection(entry.key(), "");
                let Ok(val) = data.get_field(&set_path, ChildrenKey::VariantChildren.as_str()) else {
                    continue;
                };
                let Value::TokenVec(variants) = val.into_owned() else {
                    continue;
                };
                // Use the first configured fallback that exists in this set.
                let fallbacks = variant_fallbacks.get(entry.key());
                if let Some(fb) = fallbacks.iter().find(|fb| variants.iter().any(|v| v == fb.as_str())) {
                    entry.insert(fb.clone());
                }
            }
        }
    }

    selections
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
pub(crate) mod tests {
    use std::cmp::Ordering;

    use super::*;

    use anyhow::Result;

    use crate::sdf::LayerOffset;

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

    /// Loads a root layer and the full transitive closure of its sublayers,
    /// references, and payloads into a `Vec<sdf::Layer>` for PrimIndex::build —
    /// the layer set composition would have loaded on demand had it been driven
    /// through a stage.
    fn load_layers(path: &str) -> Result<Vec<sdf::Layer>> {
        sdf::LayerRegistry::default().collect_with_arcs(path)
    }

    /// Builds a prim index for a given path string.
    fn build(stack: &mut LayerGraph, prim: &str) -> PrimIndex {
        build_with_fallbacks(stack, prim, VariantFallbackMap::new())
    }

    /// Composes `prim` and every namespace ancestor top-down into a cache,
    /// applying `fallbacks`, and returns the target prim's fully-composed index.
    /// The task-queue indexer seeds a child prim from its cached parent, so the
    /// ancestors are composed first (mirroring the cache's `ensure_index`),
    /// threading each prim's child context to the next. Shared with the
    /// `prim_indexer` test suite.
    ///
    /// Takes `&mut LayerGraph` to mirror the stage's load barrier: a build that
    /// reaches an external arc whose layer stack is not yet interned records a
    /// [`Demand`], which this mints through [`LayerGraph::intern_external`] before
    /// re-running (the test fixtures load every layer up front, so a demand only
    /// ever needs interning, never loading).
    pub(crate) fn build_with_fallbacks(stack: &mut LayerGraph, prim: &str, fallbacks: VariantFallbackMap) -> PrimIndex {
        let path = Path::from(prim);

        // Namespace chain from the topmost prim down to `path`.
        let mut chain: Vec<Path> = Vec::new();
        let mut p = Some(path.clone());
        while let Some(pp) = p {
            if pp == Path::abs_root() {
                break;
            }
            chain.push(pp.clone());
            p = pp.parent();
        }
        chain.reverse();

        loop {
            let mut cache: sdf::PathTable<PrimEntry> = sdf::PathTable::new();
            let mut parent_ctx = CompositionContext {
                variant_fallbacks: fallbacks.clone(),
                ..CompositionContext::default()
            };
            let mut last = None;
            let mut pending: Vec<Demand> = Vec::new();
            for ancestor in &chain {
                let (index, _errors, demands) =
                    PrimIndex::build_with_cache(ancestor, stack, &parent_ctx, &cache).expect("index build failed");
                pending.extend(demands);
                parent_ctx = index.context_for_children(stack, &parent_ctx);
                cache.insert(
                    ancestor.clone(),
                    PrimEntry {
                        index: index.clone(),
                        context: CompositionContext::default(),
                        errors: Vec::new(),
                    },
                );
                last = Some(index);
            }
            // Mint the layer stacks the demands resolved against and re-run, the way
            // the stage's load barrier does. The `progress` guard terminates if a
            // demand cannot be satisfied (e.g. an unresolvable target).
            let mut progress = false;
            for demand in &pending {
                if let Some(root) = stack.id_of(demand.asset_path.as_str()) {
                    progress |= stack.intern_external(root, &demand.expr_vars).1;
                }
            }
            if !progress {
                return last.expect("a non-empty namespace chain");
            }
        }
    }

    /// Helper: loads layers and builds a [`LayerGraph`].
    fn load_stack(path: &str) -> anyhow::Result<LayerGraph> {
        let layers = load_layers(path)?;
        Ok(LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default()))
    }

    /// Builds a single-layer stack from in-memory `root.usd` data.
    fn one_layer_stack(root: Box<dyn sdf::AbstractData>) -> LayerGraph {
        let layers = vec![sdf::Layer::new("root.usd", root)];
        LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default())
    }

    /// Builds a two-layer stack from in-memory `root.usd` + `ref.usd` data.
    fn two_layer_stack(root: Box<dyn sdf::AbstractData>, refl: Box<dyn sdf::AbstractData>) -> LayerGraph {
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("ref.usd", refl)];
        LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default())
    }

    #[test]
    fn single_layer_root_node() -> Result<()> {
        let mut stack = load_stack(&composition_path("active.usda"))?;
        let index = build(&mut stack, "/World");

        assert_eq!(index.nodes().count(), 1);
        assert_eq!(index.nodes().next().unwrap().layer_id(), stack.all_ids()[0]);
        assert_eq!(index.nodes().next().unwrap().arc, ArcType::Root);
        Ok(())
    }

    #[test]
    fn sublayer_site_layer_order() -> Result<()> {
        let mut stack = load_stack(&fixture_path("sublayer_override.usda"))?;
        let index = build(&mut stack, "/World");

        let ns: Vec<_> = index.nodes().collect();
        assert_eq!(ns.len(), 1, "one per-site node spans both sublayers");
        assert_eq!(ns[0].arc, ArcType::Root);
        let layers: Vec<LayerId> = stack
            .layer_stack(ns[0].layer_stack_id())
            .iter()
            .map(|&(li, _)| li)
            .collect();
        let expected: Vec<LayerId> = stack.root_layer_stack().iter().map(|&(id, _)| id).collect();
        assert_eq!(layers, expected, "stronger sublayer first");
        Ok(())
    }

    #[test]
    fn prim_only_in_stronger_layer() -> Result<()> {
        let mut stack = load_stack(&fixture_path("sublayer_override.usda"))?;
        let index = build(&mut stack, "/World/Sphere");

        assert_eq!(index.nodes().count(), 1);
        assert_eq!(index.nodes().next().unwrap().layer_id(), stack.all_ids()[0]);
        Ok(())
    }

    #[test]
    fn nonexistent_prim_empty_index() -> Result<()> {
        let mut stack = load_stack(&composition_path("active.usda"))?;
        let index = build(&mut stack, "/DoesNotExist");

        assert!(index.is_empty());
        Ok(())
    }

    #[test]
    fn reference_arc_present() -> Result<()> {
        let mut stack = load_stack(&fixture_path("ref_external.usda"))?;
        let index = build(&mut stack, "/World/MyPrim");

        assert!(index.nodes().any(|n| n.arc == ArcType::Reference));
        Ok(())
    }

    /// The path-order site index resolves each site to exactly the arena nodes at
    /// that path, including a path holding several nodes (the prim site carries the
    /// synthetic root and the local root) and the reference target at its own
    /// namespace path, and nothing for an absent path.
    #[test]
    fn path_order_resolves_sites() -> Result<()> {
        let root = parse_usda("#usda 1.0\ndef \"A\" ( references = @base.usd@</B> ) {\n  custom double x = 1\n}\n");
        let base = parse_usda("#usda 1.0\ndef \"B\" { custom double y = 2 }\n");
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("base.usd", base)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/A");

        // For every site, the index must resolve exactly the arena nodes whose path
        // matches; a direct arena filter is the ground truth. An off-by-one in the
        // binary-search bounds would drop a node from the run or pull in one from an
        // adjacent path, and the exact set comparison catches either.
        for p in ["/A", "/B"].into_iter().map(Path::from) {
            let mut expected: Vec<NodeId> = index
                .arena()
                .iter()
                .enumerate()
                .filter(|(_, n)| n.path == p)
                .map(|(i, _)| NodeId(i as u32))
                .collect();
            let mut got = index.nodes_at(&p).to_vec();
            expected.sort();
            got.sort();
            assert_eq!(got, expected, "site index resolves {p} to its arena nodes");
        }

        // The prim site holds more than one node (the synthetic root and the local
        // root), so the loop above exercised the contiguous multi-node run the
        // two-bound binary search exists to return — not just single-node sites.
        assert!(
            index.nodes_at(&Path::from("/A")).len() >= 2,
            "the prim's own site carries the synthetic root and the local root"
        );

        // The reference target keeps its own namespace path /B.
        assert!(
            index
                .nodes_at(&Path::from("/B"))
                .iter()
                .any(|&id| index.node(id).arc == ArcType::Reference),
            "the reference node is indexed at its target path"
        );

        // An absent path resolves to no nodes.
        assert!(index.nodes_at(&Path::from("/Nope")).is_empty());
        Ok(())
    }

    #[test]
    fn empty_reference_target_culled() -> Result<()> {
        // /A references a prim the target layer never defines.
        let root = parse_usda("#usda 1.0\ndef \"A\" ( references = @base.usd@</Empty> ) {\n  custom double x = 1\n}\n");
        let base = parse_usda("#usda 1.0\ndef \"Other\" {}\n");
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("base.usd", base)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/A");

        // The empty target is retained as a culled node so an editor sees the
        // arc, but value resolution skips it and the prim is not composed.
        assert!(
            index.all_nodes().any(|n| n.arc == ArcType::Reference && n.is_culled()),
            "empty reference target kept as a culled node"
        );
        assert!(
            index.nodes().all(|n| n.arc != ArcType::Reference),
            "culled reference contributes no opinion to resolution"
        );
        assert!(
            !index.has_composition_arc(),
            "an empty reference does not compose the prim"
        );
        assert!(!index.is_empty(), "the prim's own opinions remain");
        Ok(())
    }

    #[test]
    fn empty_inherit_target_culled() -> Result<()> {
        // /A inherits a class the layer never defines.
        let root = parse_usda("#usda 1.0\ndef \"A\" ( inherits = </_class_Missing> ) {\n  custom double x = 1\n}\n");
        let index = build(&mut one_layer_stack(root), "/A");

        // The empty class is retained as a culled node so an editor sees the arc,
        // but value resolution skips it and the prim is not composed.
        assert!(
            index.all_nodes().any(|n| n.arc == ArcType::Inherit && n.is_culled()),
            "empty inherit target kept as a culled node"
        );
        assert!(
            index.nodes().all(|n| n.arc != ArcType::Inherit),
            "culled inherit contributes no opinion to resolution"
        );
        assert!(
            !index.has_composition_arc(),
            "an empty inherit does not compose the prim"
        );
        assert!(!index.is_empty(), "the prim's own opinions remain");
        Ok(())
    }

    #[test]
    fn empty_specialize_target_culled() -> Result<()> {
        // /A specializes a class the layer never defines.
        let root = parse_usda("#usda 1.0\ndef \"A\" ( specializes = </_class_Missing> ) {\n  custom double x = 1\n}\n");
        let index = build(&mut one_layer_stack(root), "/A");

        assert!(
            index.all_nodes().any(|n| n.arc == ArcType::Specialize && n.is_culled()),
            "empty specialize target kept as a culled node"
        );
        assert!(
            index.nodes().all(|n| n.arc != ArcType::Specialize),
            "culled specialize contributes no opinion to resolution"
        );
        assert!(
            !index.has_composition_arc(),
            "an empty specialize does not compose the prim"
        );
        assert!(!index.is_empty(), "the prim's own opinions remain");
        Ok(())
    }

    #[test]
    fn empty_variant_target_culled() -> Result<()> {
        // /A selects a variant its set never authors, so the `{v=missing}` site
        // has no spec.
        let root = parse_usda(
            "#usda 1.0\ndef \"A\" (\n    variantSets = \"v\"\n    variants = { string v = \"missing\" }\n) {\n  custom double own = 1\n  variantSet \"v\" = {\n    \"present\" { custom double x = 1 }\n  }\n}\n",
        );
        let index = build(&mut one_layer_stack(root), "/A");

        assert!(
            index.all_nodes().any(|n| n.arc == ArcType::Variant && n.is_culled()),
            "empty variant target kept as a culled node"
        );
        assert!(
            index.nodes().all(|n| n.arc != ArcType::Variant),
            "culled variant contributes no opinion to resolution"
        );
        assert!(
            !index.has_composition_arc(),
            "an empty variant does not compose the prim"
        );
        assert!(!index.is_empty(), "the prim's own opinions remain");
        Ok(())
    }

    /// An inherit that remaps through a reference ancestor arc into the
    /// referencing namespace is added as an implied-class node, flagged
    /// `IMPLIED_CLASS` with the originating inherit node recorded.
    #[test]
    fn implied_class_flagged() -> Result<()> {
        let root = parse_usda(
            "#usda 1.0\ndef \"Model\" ( references = @ref.usd@</Ref> ) {\n  over \"Class\" { custom string x = \"rootimplied\" }\n}\n",
        );
        let refl = parse_usda(
            "#usda 1.0\ndef \"Ref\" {\n  def \"Sub\" ( inherits = </Ref/Class> ) {}\n  class \"Class\" { custom string x = \"ref\" }\n}\n",
        );
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("ref.usd", refl)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());

        let index = build(&mut stack, "/Model/Sub");
        let implied = index
            .arena()
            .iter()
            .find(|n| n.path.as_str() == "/Model/Class")
            .expect("implied class node in the referencing namespace");
        assert!(
            implied.flags().contains(NodeFlags::IMPLIED_CLASS),
            "implied class node is flagged"
        );
        assert!(implied.origin().is_some(), "implied class records its origin");
        Ok(())
    }

    /// `PrimIndex` must stay `Send + Sync` so per-prim composition can run in
    /// parallel; the arena-handle representation (no `Rc`/`RefCell`) guarantees
    /// it. This fails to compile if a non-thread-safe field is ever added.
    #[test]
    fn prim_index_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<PrimIndex>();
        assert_send_sync::<Node>();
        assert_send_sync::<NodeId>();
    }

    /// A variant set defined in a referenced layer with the selection authored
    /// on the referencing prim must still produce the selected variant's node.
    /// This is exactly the LIVRPS-ordering gap `stabilize` exists to close: the
    /// variant set only becomes visible after the reference is composed.
    #[test]
    fn variant_from_external_reference() -> Result<()> {
        let root = parse_usda(
            "#usda 1.0\ndef \"Model\" (\n  references = @ref.usd@</Ref>\n  variants = { string v = \"b\" }\n) {}\n",
        );
        let refl = parse_usda(
            "#usda 1.0\ndef \"Ref\" (\n  add variantSets = \"v\"\n) {\n  variantSet \"v\" = {\n    \"a\" { custom string x = \"a\" }\n    \"b\" { custom string x = \"b\" }\n  }\n}\n",
        );
        let mut stack = two_layer_stack(root, refl);
        let index = build(&mut stack, "/Model");
        assert!(
            index
                .nodes()
                .any(|n| n.arc == ArcType::Variant && n.path.as_str().contains("{v=b}")),
            "selected variant from the referenced layer must be composed"
        );
        Ok(())
    }

    /// Like the above but the variant set arrives through an internal reference
    /// (same layer stack), which the indexer grafts via `merge_full_index`.
    #[test]
    fn variant_from_internal_reference() -> Result<()> {
        let root = parse_usda(
            "#usda 1.0\ndef \"Base\" (\n  add variantSets = \"v\"\n) {\n  variantSet \"v\" = {\n    \"a\" { custom string x = \"a\" }\n    \"b\" { custom string x = \"b\" }\n  }\n}\ndef \"Model\" (\n  references = </Base>\n  variants = { string v = \"b\" }\n) {}\n",
        );
        let mut stack = one_layer_stack(root);
        let index = build(&mut stack, "/Model");
        // The variant arrives grafted through the reference, so its node carries
        // the Reference arc; what matters is that the selected variant (v=b),
        // not the fallback (v=a), was composed.
        assert!(
            index.nodes().any(|n| n.path.as_str().contains("{v=b}")),
            "selected variant from the internal-reference target must be composed"
        );
        assert!(
            !index.nodes().any(|n| n.path.as_str().contains("{v=a}")),
            "fallback variant must not be composed when v=b is selected"
        );
        Ok(())
    }

    /// The selected variant itself contains a reference that brings in content.
    /// This exercises following arcs out of a late-discovered variant node.
    #[test]
    fn variant_contains_reference() -> Result<()> {
        let root = parse_usda(
            "#usda 1.0\ndef \"Model\" (\n  references = @ref.usd@</Ref>\n  variants = { string v = \"b\" }\n) {}\n",
        );
        let refl = parse_usda(
            "#usda 1.0\ndef \"Inner\" { custom string y = \"inner\" }\ndef \"Ref\" (\n  add variantSets = \"v\"\n) {\n  variantSet \"v\" = {\n    \"a\" {}\n    \"b\" ( references = </Inner> ) {}\n  }\n}\n",
        );
        let mut stack = two_layer_stack(root, refl);
        let index = build(&mut stack, "/Model");
        assert!(
            index
                .nodes()
                .any(|n| n.arc == ArcType::Variant && n.path.as_str().contains("{v=b}")),
            "selected variant node present"
        );
        assert!(
            index.nodes().any(|n| n.path.as_str() == "/Inner"),
            "reference inside the selected variant must be followed"
        );
        Ok(())
    }

    /// The indexer records structural parent/child links: a reference node hangs
    /// under a root node, and every stored parent agrees with its child list.
    #[test]
    fn structural_links_consistent() -> Result<()> {
        let mut stack = load_stack(&fixture_path("ref_external.usda"))?;
        let index = build(&mut stack, "/World/MyPrim");

        let root = index.root().expect("non-empty index has a root");
        assert_eq!(index.node(root).arc, ArcType::Root);

        // The reference is parented under a node, not orphaned. NodeId indexes
        // the arena (structural order), so enumerate the arena, not the strength
        // projection.
        let reference = index
            .arena()
            .iter()
            .position(|n| n.arc == ArcType::Reference)
            .map(|i| NodeId(i as u32))
            .expect("reference fixture has a reference node");
        let parent = index.parent(reference).expect("reference has a parent");
        assert!(index.children(parent).contains(&reference));

        // Every parent link is mirrored by the parent's children list.
        for (i, _) in index.arena().iter().enumerate() {
            let id = NodeId(i as u32);
            if let Some(parent) = index.parent(id) {
                assert!(
                    index.children(parent).contains(&id),
                    "node {i} parent {parent:?} missing it as a child"
                );
            }
        }
        Ok(())
    }

    /// The subtree graft keeps an inherit target's own composition nested: a
    /// reference brought in by the inherited class hangs under the grafted class
    /// node, not flattened onto the inheriting prim.
    #[test]
    fn graft_preserves_subtree() -> Result<()> {
        let root = parse_usda(
            "#usda 1.0\ndef \"Model\" ( inherits = </Class> ) {}\ndef \"Class\" ( references = @base.usd@</Base> ) {}\n",
        );
        let base = parse_usda("#usda 1.0\ndef \"Base\" {}\n");
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("base.usd", base)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());

        let index = build(&mut stack, "/Model");
        let find = |p: &str| {
            index
                .arena()
                .iter()
                .position(|n| n.path.as_str() == p)
                .map(|i| NodeId(i as u32))
        };
        let class = find("/Class").expect("inherited /Class node");
        let base = find("/Base").expect("grafted /Base node from /Class's reference");

        // /Base entered through /Class's own reference, so it must hang under the
        // grafted /Class node rather than be flattened onto /Model.
        assert_eq!(
            index.parent(base),
            Some(class),
            "reference subtree preserved under its inherit root"
        );
        // Grafted nodes record the inheriting node as their arc origin.
        assert!(index.node(base).origin().is_some(), "grafted node carries an origin");
        Ok(())
    }

    /// `dump_to_string` renders the composition tree depth-first with deeper
    /// nesting indented further: the grafted reference sits under the inherit,
    /// which sits under the root.
    #[test]
    fn dump_renders_tree() -> Result<()> {
        let root = parse_usda(
            "#usda 1.0\ndef \"Model\" ( inherits = </Class> ) {}\ndef \"Class\" ( references = @base.usd@</Base> ) {}\n",
        );
        let base = parse_usda("#usda 1.0\ndef \"Base\" {}\n");
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("base.usd", base)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/Model");

        let dump = index.dump_to_string();
        let line = |needle: &str| {
            dump.lines()
                .find(|l| l.contains(needle))
                .unwrap_or_else(|| panic!("dump missing {needle}: {dump}"))
        };
        let indent = |l: &str| l.len() - l.trim_start().len();

        // Every line carries a strength rank; nesting deepens with indentation.
        assert!(dump.lines().all(|l| l.contains('#')), "each line has a strength rank");
        assert!(line("/Model").starts_with("Root"), "root prim is the tree root");
        assert!(
            indent(line("/Class")) > indent(line("/Model")),
            "inherit nests under the root"
        );
        assert!(
            indent(line("/Base")) > indent(line("/Class")),
            "grafted reference nests under the inherit"
        );
        Ok(())
    }

    #[test]
    fn inherit_arc_present() -> Result<()> {
        let mut stack = load_stack(&composition_path("class_inherit.usda"))?;
        let index = build(&mut stack, "/World/cubeWithoutSetColor");

        assert!(index.nodes().any(|n| n.arc == ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn inherit_root_is_strongest() -> Result<()> {
        let mut stack = load_stack(&composition_path("class_inherit.usda"))?;
        let index = build(&mut stack, "/World/cubeWithSetColor");
        let arcs: Vec<_> = index.nodes().map(|n| n.arc).collect();

        assert_eq!(arcs[0], ArcType::Root);
        assert!(arcs.contains(&ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn variant_arc_with_selection() -> Result<()> {
        let path = format!(
            "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
            manifest_dir()
        );
        let mut stack = load_stack(&path)?;
        let index = build(&mut stack, "/World/Sphere");

        assert!(index.nodes().any(|n| n.arc == ArcType::Variant));

        let variant_node = index.nodes().find(|n| n.arc == ArcType::Variant).unwrap();
        assert_eq!(variant_node.path.as_str(), "/World/Sphere{size=small}");
        Ok(())
    }

    #[test]
    fn specialize_arc_present() -> Result<()> {
        let mut stack = load_stack(&composition_path("inherit_and_specialize.usda"))?;
        let index = build(&mut stack, "/World/cubeScene/specializes");

        assert!(index.nodes().any(|n| n.arc == ArcType::Specialize));
        Ok(())
    }

    /// External references with `./` relative paths and nested references
    /// should be followed recursively (diamond pattern: Root -> A,B -> C).
    #[test]
    fn reference_diamond_recursive() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/BasicReferenceDiamond_root/usda/root.usd",
            manifest_dir()
        );
        let mut stack = load_stack(&path)?;
        let index = build(&mut stack, "/Root");

        assert!(
            index
                .nodes()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/A"),
            "should have node from A.usd"
        );
        assert!(
            index
                .nodes()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/B"),
            "should have node from B.usd"
        );
        assert!(
            index
                .nodes()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/C"),
            "should have node from C.usd via nested reference"
        );

        let a_idx = stack.find_by_leaf("A.usd").unwrap();
        let a_attr_path = Path::new("/A.A_attr").unwrap();
        assert!(
            stack.layer(a_idx).data().has_spec(&a_attr_path),
            "A.usd should have spec at /A.A_attr"
        );
        Ok(())
    }

    /// Variant that introduces a specializes arc should propagate the
    /// specialized prim's variant opinions to the composing prim (C++
    /// `_DetermineInheritPath` strips the parent's variant selections before
    /// mapping the class arc and re-adds the nearest containing one).
    #[test]
    fn specializes_from_variant() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/SpecializesAndVariants_root/usda/root.usd",
            manifest_dir()
        );
        let mut stack = load_stack(&path)?;
        let index = build(&mut stack, "/B");

        assert!(
            index.nodes().any(|n| n.arc == ArcType::Specialize),
            "should have specialize node from variant"
        );
        assert!(
            index
                .nodes()
                .any(|n| n.path.as_str().contains("{nestedVariantSet=nestedVariant}")),
            "should have /A's variant node"
        );
        Ok(())
    }

    /// References inside variant specs should be collected as dependencies
    /// so the target layers are loaded. Descendant prims should then pick up
    /// inherit arcs from the referenced layer through ancestral propagation.
    #[test]
    fn variant_reference_and_inherit_propagation() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/BasicVariantWithConnections_root/usda/root.usd",
            manifest_dir()
        );
        let mut stack = load_stack(&path)?;

        assert!(
            stack.find_by_leaf("camera_perspective.usd").is_some(),
            "camera_perspective.usd should be collected from variant reference"
        );

        let index = build(&mut stack, "/main_cam/Lens");
        assert!(
            index.nodes().any(|n| n.path.as_str() == "/camera/_localclass_Lens"),
            "should have inherit node for _localclass_Lens"
        );
        Ok(())
    }

    /// Variant selections from inherited classes should propagate to
    /// the inheriting prim, including selections nested inside the
    /// class's own variant specs.
    #[test]
    fn inherited_variant_selection_propagation() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/TrickyVariantWeakerSelection2_root/usda/root.usd",
            manifest_dir()
        );
        let mut stack = load_stack(&path)?;
        let index = build(&mut stack, "/bob");

        assert!(
            index.nodes().any(|n| n.path.as_str().contains("{geotype=cube}")),
            "should have geotype=cube variant node from inherited selection"
        );
        Ok(())
    }

    // --- Error reporting ---

    fn parse_usda(text: &str) -> Box<dyn sdf::AbstractData> {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        Box::new(sdf::Data::from_specs(data))
    }

    /// A reference cycle is recorded as a recoverable `Error::ArcCycle` and the
    /// cycle-closing arc is skipped, rather than aborting the whole build (C++
    /// `_CheckForCycle` drops the arc and continues).
    #[test]
    fn arc_cycle_recorded() -> Result<()> {
        // A.usd references B.usd which references A.usd — cycle.
        let a = parse_usda(
            r#"#usda 1.0
(
    defaultPrim = "Root"
)
def "Root" (
    references = @b.usd@
)
{
}
"#,
        );
        let b = parse_usda(
            r#"#usda 1.0
(
    defaultPrim = "Root"
)
def "Root" (
    references = @a.usd@
)
{
}
"#,
        );
        let layers = vec![sdf::Layer::new("a.usd", a), sdf::Layer::new("b.usd", b)];
        let stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());

        let (_index, errors, _pending) = PrimIndex::build_with_cache(
            &Path::from("/Root"),
            &stack,
            &CompositionContext::default(),
            &sdf::PathTable::new(),
        )?;
        assert!(
            errors.iter().any(|e| matches!(e, Error::ArcCycle(_))),
            "expected a recorded ArcCycle error, got {errors:?}"
        );
        Ok(())
    }

    /// A cycle realized across stack frames — `/Root` references a sub-root prim
    /// in another layer that references back into `/Root` — is recorded as
    /// `ArcCycle`, not silently composed away. The sub-root target composes an
    /// ancestral sub-index in its own frame, so the back-reference is only caught
    /// by the cross-frame walk in `arc_target_in_bounds`.
    #[test]
    fn subroot_arc_cycle_recorded() -> Result<()> {
        let a = parse_usda(
            r#"#usda 1.0
(
    defaultPrim = "Root"
)
def "Root" (
    references = @b.usd@</Outer/Inner>
)
{
}
"#,
        );
        let b = parse_usda(
            r#"#usda 1.0
def "Outer"
{
    def "Inner" (
        references = @a.usd@
    )
    {
    }
}
"#,
        );
        let layers = vec![sdf::Layer::new("a.usd", a), sdf::Layer::new("b.usd", b)];
        let stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());

        let (_index, errors, _pending) = PrimIndex::build_with_cache(
            &Path::from("/Root"),
            &stack,
            &CompositionContext::default(),
            &sdf::PathTable::new(),
        )?;
        assert!(
            errors.iter().any(|e| matches!(e, Error::ArcCycle(_))),
            "expected a recorded ArcCycle error for a cross-frame cycle, got {errors:?}"
        );
        Ok(())
    }

    /// An unresolvable referenced layer is recorded as a recoverable
    /// `UnresolvedLayer` error and the arc is skipped, so the prim still composes
    /// its own local opinions instead of aborting.
    #[test]
    fn unresolved_layer_recorded() -> Result<()> {
        let layer = parse_usda(
            r#"#usda 1.0
def "Prim" (
    references = @nonexistent.usd@
)
{
    custom string marker = "ok"
}
"#,
        );
        let layers = vec![sdf::Layer::new("test.usda", layer)];
        let stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());

        let (index, errors, _pending) = PrimIndex::build_with_cache(
            &Path::from("/Prim"),
            &stack,
            &CompositionContext::default(),
            &sdf::PathTable::new(),
        )?;
        assert!(
            errors.iter().any(|e| matches!(e, Error::UnresolvedLayer { .. })),
            "expected a recorded UnresolvedLayer error, got {errors:?}"
        );
        assert!(
            !index.is_empty(),
            "the prim's local opinion must survive the skipped arc"
        );
        Ok(())
    }

    /// A reference to a layer without `defaultPrim` (and no explicit prim path)
    /// is recorded as a recoverable `MissingDefaultPrim` error and skipped.
    #[test]
    fn missing_default_prim_recorded() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "Prim" (
    references = @target.usda@
)
{
    custom string marker = "ok"
}
"#,
        );
        let target = parse_usda("#usda 1.0\ndef \"Foo\" {}\n");
        let layers = vec![
            sdf::Layer::new("root.usda", root),
            sdf::Layer::new("target.usda", target),
        ];
        let stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());

        let (index, errors, _pending) = PrimIndex::build_with_cache(
            &Path::from("/Prim"),
            &stack,
            &CompositionContext::default(),
            &sdf::PathTable::new(),
        )?;
        assert!(
            errors.iter().any(|e| matches!(e, Error::MissingDefaultPrim { .. })),
            "expected a recorded MissingDefaultPrim error, got {errors:?}"
        );
        assert!(
            !index.is_empty(),
            "the prim's local opinion must survive the skipped arc"
        );
        Ok(())
    }

    // --- Variant fallbacks ---

    /// Collects variant-arc paths from a prim index.
    fn variant_paths(index: &PrimIndex) -> Vec<String> {
        index
            .nodes()
            .filter(|n| n.arc == ArcType::Variant)
            .map(|n| n.path.as_str().to_string())
            .collect()
    }

    /// With no fallback and no authored selection, the set stays unselected — no
    /// variant arc is added (C++ `_EvalNodeFallbackVariant`; no implicit
    /// first-variant default).
    #[test]
    fn variant_no_selection_unselected() -> Result<()> {
        let mut stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let index = build(&mut stack, "/NoSelection");
        let paths = variant_paths(&index);
        assert!(
            paths.is_empty(),
            "no variant should be selected without an authored selection or fallback: got {paths:?}"
        );
        Ok(())
    }

    /// When a fallback map specifies "simple" as the preferred fallback, and no
    /// authored selection exists, the composition should select "simple".
    #[test]
    fn variant_fallback_overrides_default() -> Result<()> {
        let mut stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["simple"]);
        let index = build_with_fallbacks(&mut stack, "/NoSelection", fb);
        let paths = variant_paths(&index);
        assert!(
            paths.iter().any(|p| p.contains("{shadingComplexity=simple}")),
            "fallback should select 'simple': got {paths:?}"
        );
        assert!(
            !paths.iter().any(|p| p.contains("{shadingComplexity=full}")),
            "'full' should NOT be selected when fallback says 'simple'"
        );
        Ok(())
    }

    /// An authored selection should take priority over a variant fallback.
    #[test]
    fn variant_authored_selection_beats_fallback() -> Result<()> {
        let mut stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["none"]);
        let index = build_with_fallbacks(&mut stack, "/Root", fb);
        let paths = variant_paths(&index);
        assert!(
            paths.iter().any(|p| p.contains("{shadingComplexity=full}")),
            "authored selection 'full' should win over fallback 'none': got {paths:?}"
        );
        Ok(())
    }

    /// When the fallback specifies a variant name that doesn't exist in the set,
    /// it should be skipped and the next fallback (or default) should be used.
    #[test]
    fn variant_fallback_skips_nonexistent() -> Result<()> {
        let mut stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["ultra", "simple"]);
        let index = build_with_fallbacks(&mut stack, "/NoSelection", fb);
        let paths = variant_paths(&index);
        assert!(
            paths.iter().any(|p| p.contains("{shadingComplexity=simple}")),
            "should skip 'ultra' and use 'simple': got {paths:?}"
        );
        Ok(())
    }

    /// When every configured fallback names a variant that does not exist in the
    /// set, the set stays unselected — no variant arc is added.
    #[test]
    fn variant_fallback_all_invalid_unselected() -> Result<()> {
        let mut stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["ultra", "mega"]);
        let index = build_with_fallbacks(&mut stack, "/NoSelection", fb);
        let paths = variant_paths(&index);
        assert!(
            paths.is_empty(),
            "no variant should be selected when every fallback is invalid: got {paths:?}"
        );
        Ok(())
    }

    /// Exercises the node strength comparators on a hand-built tree, covering
    /// every key: arc type, namespace depth, and the sibling-number tiebreak,
    /// plus the ancestor-stronger rule for arbitrary nodes.
    #[test]
    fn node_strength_comparator() {
        let p = |s: &str| Path::from(s.to_string());
        let id = MapFunction::identity();
        let lid = LayerId::from_raw(0);
        let lsid = LayerStackId::from_raw(1);
        let mut g = PrimIndexGraph::default();
        let root = g.add_child(NodeId::INVALID, lsid, lid, p("/A"), ArcType::Root, id.clone(), false);
        let inh = g.add_child(root, lsid, lid, p("/Class"), ArcType::Inherit, id.clone(), false);
        let r1 = g.add_child(root, lsid, lid, p("/R1"), ArcType::Reference, id.clone(), false);
        let r2 = g.add_child(root, lsid, lid, p("/R2"), ArcType::Reference, id.clone(), false);

        // Arc type: an inherit outranks a reference.
        assert_eq!(g.compare_sibling_node_strength(inh, r1), Ordering::Less);
        // Sibling number breaks ties between same-arc siblings: earlier wins.
        assert_eq!(g.compare_sibling_node_strength(r1, r2), Ordering::Less);
        assert_eq!(g.compare_sibling_node_strength(r2, r1), Ordering::Greater);

        // Arbitrary nodes: an ancestor outranks its descendant.
        assert_eq!(g.compare_node_strength(root, inh), Ordering::Less);
        assert_eq!(g.compare_node_strength(inh, root), Ordering::Greater);
        // Cousins resolve through their diverging ancestors.
        assert_eq!(g.compare_node_strength(inh, r2), Ordering::Less);
        assert_eq!(g.compare_node_strength(r2, r2), Ordering::Equal);

        // Namespace depth: a deeper arc-introduction site is stronger.
        let deep = g.add_child(root, lsid, lid, p("/D"), ArcType::Reference, id.clone(), false);
        g.nodes[deep.idx()].namespace_depth = 5;
        assert_eq!(g.compare_sibling_node_strength(deep, r1), Ordering::Less);
    }

    #[test]
    fn arc_type_liverps_ordering() {
        assert!(ArcType::Root < ArcType::Inherit);
        assert!(ArcType::Inherit < ArcType::Variant);
        assert!(ArcType::Variant < ArcType::Relocate);
        assert!(ArcType::Relocate < ArcType::Reference);
        assert!(ArcType::Reference < ArcType::Payload);
        assert!(ArcType::Payload < ArcType::Specialize);
    }

    /// Helper: path into the spec supplemental composition test assets.
    fn spec_composition_path(relative: &str) -> String {
        format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/{relative}",
            manifest_dir()
        )
    }

    /// Helper: extracts filename from an identifier (e.g. "/path/to/root.usd" → "root.usd").
    fn layer_name(identifier: &str) -> &str {
        std::path::Path::new(identifier)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(identifier)
    }

    /// Formats a prim stack as a vec of (layer_name, path) pairs for assertion.
    fn prim_stack(index: &PrimIndex, stack: &LayerGraph) -> Vec<(String, String)> {
        index
            .nodes()
            .map(|n| {
                (
                    layer_name(stack.identifier(n.layer_id())).to_owned(),
                    n.path.to_string(),
                )
            })
            .collect()
    }

    /// Validates that specializes opinions are globally weaker than all other
    /// opinions. Matches the expected prim stack from the vendor test baseline
    /// (spec 10.4.1 — specializes global weakness).
    #[test]
    fn specialize_global_weakness_basic() -> Result<()> {
        let mut stack = load_stack(&spec_composition_path("BasicSpecializes_root/usda/root.usd"))?;
        let index = build(&mut stack, "/Root");

        // Expected from pcp.txt:
        //   root.usd  /Root          (Root)
        //   ref.usd   /Ref           (Reference)
        //   ref2.usd  /Ref           (Reference)
        //   root.usd  /Specializes   (Specialize — globally weak)
        //   ref.usd   /Specializes   (Specialize)
        //   ref2.usd  /Specializes   (Specialize)
        //   root.usd  /Base          (Specialize)
        //   ref.usd   /Base          (Specialize)
        //   ref2.usd  /Base          (Specialize)
        let ps = prim_stack(&index, &stack);
        assert_eq!(
            ps,
            vec![
                ("root.usd".into(), "/Root".into()),
                ("ref.usd".into(), "/Ref".into()),
                ("ref2.usd".into(), "/Ref".into()),
                ("root.usd".into(), "/Specializes".into()),
                ("ref.usd".into(), "/Specializes".into()),
                ("ref2.usd".into(), "/Specializes".into()),
                ("root.usd".into(), "/Base".into()),
                ("ref.usd".into(), "/Base".into()),
                ("ref2.usd".into(), "/Base".into()),
            ]
        );

        // Verify the specialize flag in strength order: first 3 nodes are
        // non-specialize, remaining 6 are specialize.
        let ns: Vec<_> = index.nodes().collect();
        for node in &ns[..3] {
            assert!(
                !node.introduced_by_specialize(),
                "node {:?} should not be specialize",
                node.path
            );
        }
        for node in &ns[3..] {
            assert!(
                node.introduced_by_specialize(),
                "node {:?} should be specialize",
                node.path
            );
        }

        Ok(())
    }

    /// Validates global weakness with multiple specializes arcs. Specializes
    /// opinions from both targets appear after all reference opinions.
    #[test]
    fn specialize_global_weakness_multiple() -> Result<()> {
        let mut stack = load_stack(&spec_composition_path("BasicSpecializes_root/usda/root.usd"))?;
        let index = build(&mut stack, "/MultipleSpecializes");

        // Non-specialize opinions must come before all specialize opinions.
        let first_spec = index
            .nodes()
            .position(|n| n.introduced_by_specialize())
            .expect("should have specialize nodes");
        assert!(first_spec >= 2, "at least Root + Reference before specializes");

        // All nodes after the first specialize must also be specialize.
        for node in index.nodes().skip(first_spec) {
            assert!(
                node.introduced_by_specialize(),
                "node {:?} should be globally weak",
                node.path
            );
        }
        Ok(())
    }

    /// Without references, specializes still appear after local opinions in
    /// the correct chain order.
    #[test]
    fn specialize_chain_ordering() -> Result<()> {
        let mut stack = load_stack(&spec_composition_path("BasicSpecializes_root/usda/root.usd"))?;
        let index = build(&mut stack, "/Basic");

        // Expected from pcp.txt:
        //   root.usd  /Basic               (Root)
        //   root.usd  /BasicSpecializes1   (Specialize)
        //   root.usd  /BasicSpecializes2   (Specialize)
        let ps = prim_stack(&index, &stack);
        assert_eq!(
            ps,
            vec![
                ("root.usd".into(), "/Basic".into()),
                ("root.usd".into(), "/BasicSpecializes1".into()),
                ("root.usd".into(), "/BasicSpecializes2".into()),
            ]
        );
        Ok(())
    }

    // -------------------------------------------------------------------
    // Layer time offsets — spec 10.3.1.1 / 10.3.2.1.2 / 10.3.2.2.2
    //
    // Verified against the upstream core-spec vendor golden
    // (`BasicTimeOffset_root/pcp.txt`). The fixture builds three arc
    // variants from root.usd:
    //   - /Root             : reference to A.usd (offset=10) which
    //                          sublayers B.usd (offset=20).
    //   - /PayloadRefPayload: payload to ref.usd (offset=10; scale=2) which
    //                          sublayers ref_sub.usd (offset=20). ref_sub's
    //                          /Ref has a payload to B.usd/Model.
    //   - /PayloadMultiRef  : payload to ref.usd (offset=10; scale=2) which
    //                          sublayers ref_sub.usd (offset=20). ref_sub's
    //                          /Ref2 has a reference to B.usd/Model.
    // -------------------------------------------------------------------

    /// Iterates `node`'s layer-stack members strongest first, each paired with
    /// its effective time offset to the root namespace: the node's arc offset
    /// (`map_to_root`) folded onto the member's sublayer offset. Unlike the
    /// memoized spec stack — which keeps only spec-authoring members — this lists
    /// every member, so [`offset_stack`] can assert the offset folding on layers
    /// that author no spec at the node's path.
    fn node_layer_offsets(node: &Node, graph: &LayerGraph) -> Vec<(LayerId, LayerOffset)> {
        let arc_offset = node.map_to_root().time_offset();
        graph
            .layer_stack(node.layer_stack_id())
            .iter()
            .map(|&(li, sub)| (li, arc_offset.concatenate(&sub)))
            .collect()
    }

    /// Returns `(layer_name, node_path, arc_type, offset, scale)` tuples for
    /// every node in the prim stack. The offset/scale values are the effective
    /// [`sdf::LayerOffset`] carried by the node — i.e., the composition of
    /// every arc offset and sublayer offset from the stage root down to this
    /// node's layer.
    fn offset_stack(index: &PrimIndex, stack: &LayerGraph) -> Vec<(String, String, ArcType, f64, f64)> {
        index
            .nodes()
            .flat_map(|n| {
                let path = n.path.to_string();
                let arc = n.arc;
                // One row per contributing sublayer, carrying that layer's
                // effective offset.
                node_layer_offsets(n, stack).into_iter().map(move |(li, off)| {
                    (
                        layer_name(stack.identifier(li)).to_owned(),
                        path.clone(),
                        arc,
                        off.offset,
                        off.scale,
                    )
                })
            })
            .collect()
    }

    fn basic_time_offset_stack() -> anyhow::Result<LayerGraph> {
        load_stack(&spec_composition_path("BasicTimeOffset_root/usda/root.usd"))
    }

    #[test]
    fn time_offset_reference_then_sublayer() -> anyhow::Result<()> {
        // /Root references A.usd (offset=10, scale=1).
        // A.usd sublayers B.usd (offset=20, scale=1).
        // Expected effective offsets (from pcp.txt):
        //   root.usd /Root  (0, 1)
        //   A.usd    /Model (10, 1)    [reference arc]
        //   B.usd    /Model (30, 1)    [sublayer of A]  = (10,1) ∘ (20,1)
        let mut stack = basic_time_offset_stack()?;
        let index = build(&mut stack, "/Root");
        assert_eq!(
            offset_stack(&index, &stack),
            vec![
                ("root.usd".into(), "/Root".into(), ArcType::Root, 0.0, 1.0),
                ("A.usd".into(), "/Model".into(), ArcType::Reference, 10.0, 1.0),
                ("B.usd".into(), "/Model".into(), ArcType::Reference, 30.0, 1.0),
            ]
        );
        Ok(())
    }

    #[test]
    fn time_offset_payload_with_scale_and_sublayer() -> anyhow::Result<()> {
        // /PayloadRefPayload payload = ref.usd (offset=10, scale=2).
        // ref.usd sublayers ref_sub.usd (offset=20, scale=1).
        // ref_sub's /Ref payload = B.usd/Model (no offset).
        // Expected from pcp.txt:
        //   root.usd    /PayloadRefPayload (0, 1)
        //   ref.usd     /Ref                (10, 2)    [payload arc; ref.usd has no /Ref spec → L empty]
        //   ref_sub.usd /Ref                (50, 2)    [sublayer of ref.usd: (10,2) ∘ (20,1) = (50, 2)]
        //   B.usd       /Model              (50, 2)    [payload from ref_sub.usd, default offset]
        let mut stack = basic_time_offset_stack()?;
        let index = build(&mut stack, "/PayloadRefPayload");
        let got = offset_stack(&index, &stack);

        // ref.usd has no /Ref spec (only ref_sub.usd does), so the
        // effective-offset chain surfaces at ref_sub.usd. Assert the
        // opinions that *must* be present with their effective offsets.
        assert!(
            got.contains(&("root.usd".into(), "/PayloadRefPayload".into(), ArcType::Root, 0.0, 1.0,)),
            "missing root opinion: got {got:?}"
        );
        assert!(
            got.contains(&("ref_sub.usd".into(), "/Ref".into(), ArcType::Payload, 50.0, 2.0)),
            "missing ref_sub /Ref payload opinion at (50,2): got {got:?}"
        );
        assert!(
            got.contains(&("B.usd".into(), "/Model".into(), ArcType::Payload, 50.0, 2.0)),
            "missing B.usd /Model payload opinion at (50,2): got {got:?}"
        );
        Ok(())
    }

    #[test]
    fn time_offset_payload_with_nested_reference() -> anyhow::Result<()> {
        // /PayloadMultiRef payload = ref.usd/Ref2 (offset=10, scale=2).
        // ref.usd sublayers ref_sub.usd (offset=20, scale=1).
        // ref_sub's /Ref2 references B.usd/Model (no offset).
        // Expected from pcp.txt:
        //   root.usd    /PayloadMultiRef (0, 1)
        //   ref_sub.usd /Ref2             (50, 2)
        //   B.usd       /Model            (50, 2)    [reference; scale carries through]
        let mut stack = basic_time_offset_stack()?;
        let index = build(&mut stack, "/PayloadMultiRef");
        let got = offset_stack(&index, &stack);

        assert!(
            got.contains(&("root.usd".into(), "/PayloadMultiRef".into(), ArcType::Root, 0.0, 1.0,)),
            "missing root opinion: got {got:?}"
        );
        assert!(
            got.contains(&("ref_sub.usd".into(), "/Ref2".into(), ArcType::Payload, 50.0, 2.0)),
            "missing ref_sub /Ref2 payload opinion: got {got:?}"
        );
        assert!(
            got.contains(&("B.usd".into(), "/Model".into(), ArcType::Reference, 50.0, 2.0)),
            "missing B.usd /Model ref opinion at (50,2): got {got:?}"
        );
        Ok(())
    }

    #[test]
    fn time_offset_descendant_inherits_parents_offset() -> anyhow::Result<()> {
        // /Root/Anim is a descendant of /Root, which references A.usd
        // (offset=10). A.usd sublayers B.usd (offset=20). /Model/Anim lives
        // in B.usd only.
        // Per pcp.txt, /Root/Anim should have:
        //   B.usd /Model/Anim (30, 1)    [effective: ref 10 ∘ sublayer 20]
        let mut stack = basic_time_offset_stack()?;
        let index = build(&mut stack, "/Root/Anim");
        let got = offset_stack(&index, &stack);

        assert!(
            got.contains(&("B.usd".into(), "/Model/Anim".into(), ArcType::Reference, 30.0, 1.0)),
            "missing /Model/Anim at effective (30, 1): got {got:?}"
        );
        Ok(())
    }

    /// `resolve_time_samples` must map authored layer times to stage times
    /// through the node's effective offset (spec 12.3.2.1): /Root references
    /// model.usd</Model> with offset=10, scale=2, so samples authored at layer
    /// times 1 and 5 resolve to stage times 12 and 20.
    #[test]
    fn time_samples_retimed_across_reference() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "Root" (
    references = @model.usd@</Model> (offset = 10; scale = 2)
)
{
}
"#,
        );
        let model = parse_usda(
            r#"#usda 1.0
def "Model"
{
    double radius.timeSamples = {
        1: 0.0,
        5: 1.0,
    }
}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root), sdf::Layer::new("model.usd", model)];
        let stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = PrimIndex::build_with_context(&Path::from("/Root"), &stack, &CompositionContext::default())?;

        let samples = index
            .resolve_time_samples(&stack, Some(".radius"))?
            .expect("retimed samples");
        let times: Vec<f64> = samples.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![12.0, 20.0]);
        Ok(())
    }

    /// `rebase_root` re-anchors only the path side of each map, so the spec
    /// stack's node ids and folded time offsets survive a prototype
    /// materialization. Value resolution over a materialized prototype reads
    /// those offsets, so this locks the invariant the instancing clone relies on.
    #[test]
    fn spec_stack_offsets_survive_rebase() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "Root" (
    references = @model.usd@</Model> (offset = 10; scale = 2)
)
{
}
"#,
        );
        let model = parse_usda("#usda 1.0\ndef \"Model\" { custom double radius = 1.0 }\n");
        let layers = vec![sdf::Layer::new("root.usda", root), sdf::Layer::new("model.usd", model)];
        let stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = PrimIndex::build_with_context(&Path::from("/Root"), &stack, &CompositionContext::default())?;

        let sites = |index: &PrimIndex| -> Vec<(NodeId, f64, f64)> {
            index
                .live_spec_sites()
                .map(|(s, _)| (s.node, s.offset.offset, s.offset.scale))
                .collect()
        };
        let before = sites(&index);
        assert!(
            before.iter().any(|&(_, off, scale)| off == 10.0 && scale == 2.0),
            "the referenced Model site carries the arc's (offset=10, scale=2): {before:?}"
        );

        let mut rebased = index.clone();
        rebased.rebase_root(&Path::from("/Root"), &Path::from("/__Prototype_1"));
        assert_eq!(
            before,
            sites(&rebased),
            "rebase_root must preserve spec-stack node ids and folded offsets"
        );
        Ok(())
    }

    // Spec §10.3.2.1.2 / §10.3.2.2.2 / §10.3.1.1: a layer offset with
    // `scale <= 0` is a composition error; the offset falls back to the
    // default `(0.0, 1.0)`.

    #[test]
    fn reference_offset_zero_scale_falls_back_to_identity() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "Root" (
    references = @model.usd@</Model> (offset = 10; scale = 0)
)
{
}
"#,
        );
        let model = parse_usda(
            r#"#usda 1.0
def "Model" {}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root), sdf::Layer::new("model.usd", model)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/Root");
        let got = offset_stack(&index, &stack);
        assert!(
            got.contains(&("model.usd".into(), "/Model".into(), ArcType::Reference, 0.0, 1.0)),
            "expected reference offset to fall back to identity for scale=0: got {got:?}"
        );
        Ok(())
    }

    #[test]
    fn payload_offset_negative_scale_falls_back_to_identity() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "Root" (
    payload = @model.usd@</Model> (offset = 5; scale = -2)
)
{
}
"#,
        );
        let model = parse_usda(
            r#"#usda 1.0
def "Model" {}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root), sdf::Layer::new("model.usd", model)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/Root");
        let got = offset_stack(&index, &stack);
        assert!(
            got.contains(&("model.usd".into(), "/Model".into(), ArcType::Payload, 0.0, 1.0)),
            "expected payload offset to fall back to identity for scale=-2: got {got:?}"
        );
        Ok(())
    }

    #[test]
    fn sublayer_offset_zero_scale_falls_back_to_identity() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
(
    subLayers = [
        @sub.usda@ (offset = 10; scale = 0)
    ]
)
def "Root" {}
"#,
        );
        let sub = parse_usda(
            r#"#usda 1.0
def "Root" {}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root), sdf::Layer::new("sub.usda", sub)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/Root");
        let got = offset_stack(&index, &stack);
        assert!(
            got.iter().any(|(name, path, _, off, scale)| name == "sub.usda"
                && path == "/Root"
                && *off == 0.0
                && *scale == 1.0),
            "expected sublayer offset to fall back to identity for scale=0: got {got:?}"
        );
        Ok(())
    }

    /// `clipSets` order folds list-op edits across layers (spec 12.2.6): the
    /// root's `prepend` and the sublayer's `append` both contribute, rather
    /// than the strongest opinion alone winning.
    #[test]
    fn clip_sets_order_folds_layers() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
(
    subLayers = [
        @sub.usda@
    ]
)
def "P" (
    prepend clipSets = ["a"]
)
{
}
"#,
        );
        let sub = parse_usda(
            r#"#usda 1.0
over "P" (
    append clipSets = ["b"]
)
{
}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root), sdf::Layer::new("sub.usda", sub)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/P");

        // Strongest-only resolution would drop the weaker "b"; folding keeps it.
        assert_eq!(
            index.clip_sets_order(&stack)?,
            Some(vec!["a".to_string(), "b".to_string()])
        );
        Ok(())
    }

    /// `clipSets` is unauthored across the stack: order resolves to `None` so
    /// clip sets fall back to name order (spec 12.3.4.1).
    #[test]
    fn clip_sets_order_unauthored() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "P" {}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/P");

        assert_eq!(index.clip_sets_order(&stack)?, None);
        Ok(())
    }

    /// An authored-but-empty `clipSets` (explicit `[]`) is distinct from an
    /// unauthored field: it composes to `Some([])`, meaning no clip sets are
    /// active, rather than `None` (name-order fallback). Matches C++
    /// `Usd_ClipSetDefinition`, which applies the list op over an empty base.
    #[test]
    fn clip_sets_order_authored_empty() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "P" (
    clipSets = []
)
{
}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/P");

        assert_eq!(index.clip_sets_order(&stack)?, Some(Vec::new()));
        Ok(())
    }

    /// A stronger `add` repeating a name a weaker layer `prepend`s must keep the
    /// set in the resolved order. Sequential list-op application (`compose_over`)
    /// keeps one copy; folding into a single list op via `combined_with` would
    /// leave the name in two buckets and `flatten` would drop it.
    #[test]
    fn clip_sets_order_overlapping_add_prepend() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
(
    subLayers = [
        @sub.usda@
    ]
)
def "P" (
    add clipSets = ["a"]
)
{
}
"#,
        );
        let sub = parse_usda(
            r#"#usda 1.0
over "P" (
    prepend clipSets = ["a"]
)
{
}
"#,
        );
        let layers = vec![sdf::Layer::new("root.usda", root), sdf::Layer::new("sub.usda", sub)];
        let mut stack = LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default());
        let index = build(&mut stack, "/P");

        assert_eq!(index.clip_sets_order(&stack)?, Some(vec!["a".to_string()]));
        // The list-op form (behind `ClipsAPI::clip_sets`) stays canonical, so
        // flattening it agrees with the resolved order rather than dropping "a".
        let list_op = index.clip_sets_list_op(&stack)?.expect("authored");
        assert_eq!(list_op.flatten(), vec!["a".to_string()]);
        Ok(())
    }
}
