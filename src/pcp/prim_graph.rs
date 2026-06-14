//! Composition graph: arena-backed node tree and strength ordering.
//!
//! [`PrimIndexGraph`] stores the composition [`Node`]s of a single prim in an
//! append-only arena plus a separate strength-order projection. See the
//! [module-level docs](super) for the composition overview and
//! [`PrimIndex`](crate::pcp::PrimIndex) for value resolution over the graph.

use std::cmp::Ordering;

use bitflags::bitflags;

use crate::sdf::Path;

use super::layer_graph::LayerStackId;
use super::mapping::MapFunction;
use super::LayerId;

/// Whether an arc introduces a class hierarchy node — an inherit or a
/// specializes (C++ `PcpIsClassBasedArc`).
pub(crate) fn is_class_based_arc(arc: ArcType) -> bool {
    matches!(arc, ArcType::Inherit | ArcType::Specialize)
}

/// The type of composition arc that introduced a [`Node`].
///
/// Variants are ordered by LIVERPS strength (strongest first). The
/// derived `PartialOrd`/`Ord` use the discriminant, so
/// `Root < Inherit < … < Specialize`.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArcType {
    /// Direct opinions from the root layer stack (sublayers).
    Root,
    /// Inherited from a class prim.
    Inherit,
    /// Contributed by a selected variant.
    Variant,
    /// Contributed by a relocate (non-destructive namespace remapping).
    Relocate,
    /// Brought in via a reference arc.
    Reference,
    /// Brought in via a payload arc.
    Payload,
    /// Contributed by a specializes arc (weakest).
    Specialize,
}

/// Stable handle to a [`Node`] within a [`PrimIndex`](crate::pcp::PrimIndex)'s
/// composition graph (C++ `PcpNodeRef`).
///
/// A handle stays valid for the life of the index: the node arena is only
/// ever appended to, never reordered, so a `NodeId` is safe to store in
/// another node's `parent`/`children`/`origin`. The sentinel value
/// [`INVALID`](Self::INVALID) represents the absence of a node.
///
/// `Ord` is by arena index, which the task queue uses for a deterministic
/// tiebreak among equal-priority tasks.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub(crate) u32);

impl NodeId {
    /// Sentinel: no node.
    pub const INVALID: Self = Self(u32::MAX);

    /// Returns `true` if this handle points to an actual node.
    pub fn is_valid(self) -> bool {
        self.0 != u32::MAX
    }

    /// Converts to a `usize` for indexing into the arena.
    pub(crate) fn idx(self) -> usize {
        self.0 as usize
    }
}

impl Default for NodeId {
    /// The default handle is the [`INVALID`](Self::INVALID) sentinel.
    fn default() -> Self {
        Self::INVALID
    }
}

bitflags! {
    /// Per-node composition state, mirroring the booleans carried by C++
    /// `PcpNodeRef`.
    ///
    /// Most bits are reserved for parity features not yet wired up; only the
    /// flags set during composition today affect resolution. Reserving the
    /// full surface now keeps later work from re-editing [`Node`].
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct NodeFlags: u16 {
        /// Contributes no opinions; kept only for graph structure.
        const INERT = 1 << 0;
        /// Hidden from value resolution but retained for change tracking.
        const CULLED = 1 << 1;
        /// Subtree namespace-restricted by a relocate.
        const RESTRICTED = 1 << 2;
        /// Blocked by `permission = private` on a stronger site.
        const PERMISSION_DENIED = 1 << 3;
        /// This site is itself `permission = private`.
        const PERMISSION_PRIVATE = 1 << 4;
        /// Children are prohibited (e.g. an unloaded payload).
        const PROHIBITED_CHILDREN = 1 << 5;
        /// Added by implied inherit/specialize propagation.
        const IMPLIED_CLASS = 1 << 6;
        /// Introduced by a directly-authored arc (not implied).
        const DIRECT = 1 << 7;
        /// Introduced through a specializes arc; globally weak (spec 10.4.1).
        const HAS_SPECIALIZES = 1 << 8;
        /// Introduced by a relocate.
        const RELOCATE_SOURCE = 1 << 9;
        /// Lies inside a selected variant branch.
        const VARIANT_BRANCH = 1 << 10;
    }
}

/// A single node in the composition graph (C++ `PcpNodeRef`).
///
/// Each node represents a site (layer + path) contributing opinions to a
/// composed prim. The identity fields (`layer_index`, `path`, `arc`)
/// define *what* this node contributes. The namespace mappings
/// (`map_to_parent`, `map_to_root`) translate paths across composition arcs.
/// The structure fields (`parent`, `children`, `origin`) record the node's
/// place in the composition tree; access them through
/// [`PrimIndex`](crate::pcp::PrimIndex).
#[derive(Debug, Clone)]
pub struct Node {
    /// Handle to the layer stack contributing opinions at this site (C++
    /// `PcpNode::GetLayerStack`). Resolve it to members through the owning layer
    /// graph's [`layer_stack`](crate::pcp::LayerGraph::layer_stack) rather than
    /// storing them on each node; for value resolution fold each member's
    /// sublayer offset onto this node's arc offset (`map_to_root.time_offset()`).
    pub(crate) layer_stack: LayerStackId,
    /// The strongest (representative) layer of [`layer_stack`](Self::layer_stack)
    /// (C++ `PcpNode::GetLayerStack()->GetLayers().front()`). Cached so structural
    /// identity ([`same_site`](PrimIndexGraph::same_site),
    /// [`node_using_site`](PrimIndexGraph::node_using_site)) and
    /// [`layer_id`](Self::layer_id) resolve without the layer graph; equals the
    /// first member of the resolved `layer_stack`.
    pub(crate) representative: LayerId,
    /// The path within that layer (may differ from composed path due to remapping).
    pub(crate) path: Path,
    /// The composition arc that introduced this node.
    pub(crate) arc: ArcType,
    /// Maps paths from this node's namespace to its parent's namespace.
    pub(crate) map_to_parent: MapFunction,
    /// Maps paths from this node's namespace directly to the root namespace.
    /// Computed as `parent.map_to_root.compose(self.map_to_parent)`.
    pub(crate) map_to_root: MapFunction,
    /// Structural parent in the composition tree, or `None` for a root node.
    pub(crate) parent: Option<NodeId>,
    /// Structural children, in the order they were introduced (strength order
    /// among siblings).
    pub(crate) children: Vec<NodeId>,
    /// Node that introduced this arc (C++ `GetOriginNode`): the parent for a
    /// direct arc (set at [`add_child`](PrimIndexGraph::add_child) time), or
    /// the propagated-from node for an implied class or graft. `None` only for
    /// the synthetic root, which has no parent.
    pub(crate) origin: Option<NodeId>,
    /// Namespace depth at which the introducing arc was authored (C++
    /// `PcpNode::GetNamespaceDepth`): the prim-element count of the parent
    /// site's path when this node was added. Used by implied inherits/specializes
    /// that propagate toward the root, and by
    /// [`depth_below_introduction`](Self::depth_below_introduction).
    pub(crate) namespace_depth: u16,
    /// This node's index among the same-arc-type siblings at its origin (C++
    /// `GetSiblingNumAtOrigin`): the arc number a class-based arc was authored
    /// with. Carried onto implied copies so their relative strength is preserved;
    /// reference/payload arcs leave it 0.
    pub(crate) sibling_num_at_origin: u16,
    /// Whether any layer in [`layer_stack`](Self::layer_stack) authors a spec at
    /// [`path`](Self::path) (C++ `PcpNode::HasSpecs`). Under the full-site-stack
    /// model a node may carry its whole layer stack yet author no spec at its
    /// path — a cloned ancestral site deepened to a child that has no opinion
    /// there. Such a node is kept for structure (it may still introduce arcs at
    /// the deepened path) but contributes nothing to value resolution and is not
    /// counted by [`is_empty`](crate::pcp::PrimIndex::is_empty). A culled node
    /// standing in for an empty arc target likewise carries `false`. Defaults to
    /// `true` for the common spec-bearing node; the indexer overwrites it (during
    /// its `has_specs` pass and at the empty-target cull) where a site authors
    /// nothing.
    pub(crate) has_specs: bool,
    /// Namespace depth at which this node's spec contribution was restricted (C++
    /// `PcpNode::GetSpecContributionRestrictedDepth`), or 0 when unrestricted.
    ///
    /// A relocate source / salted-earth root is restricted at its own depth
    /// (`path.element_count()`): its direct site contributes nothing, but the
    /// ancestral opinions above it — the "spooky ancestors" a relocation pulls
    /// through — still do. A non-zero depth allows ancestral opinions only at
    /// paths shallower than it (see
    /// [`node_can_contribute_ancestral`](crate::pcp::prim_indexer)). An inert node
    /// left at depth 0 is treated as fully restricted.
    pub(crate) restriction_depth: u16,
    /// Composition state bits (see [`NodeFlags`]).
    pub(crate) flags: NodeFlags,
}

impl Node {
    /// Builds a standalone node with no structural links.
    ///
    /// Callers that append through [`PrimIndexGraph::add_child`] have their
    /// `parent`/`children` populated by the indexer; the relocate inserts and
    /// grafts set the links explicitly afterward.
    pub(crate) fn new(
        layer_stack: LayerStackId,
        representative: LayerId,
        path: Path,
        arc: ArcType,
        map_to_parent: MapFunction,
        map_to_root: MapFunction,
        introduced_by_specialize: bool,
    ) -> Self {
        let flags = if introduced_by_specialize {
            NodeFlags::HAS_SPECIALIZES
        } else {
            NodeFlags::empty()
        };
        Self {
            layer_stack,
            representative,
            path,
            arc,
            map_to_parent,
            map_to_root,
            parent: None,
            children: Vec::new(),
            origin: None,
            namespace_depth: 0,
            sibling_num_at_origin: 0,
            has_specs: true,
            restriction_depth: 0,
            flags,
        }
    }

    /// Id of the strongest layer contributing at this site. A representative
    /// for callers that key on a single layer (dependencies, dumps); value
    /// resolution iterates the node's resolved layer-stack members instead.
    pub fn layer_id(&self) -> LayerId {
        self.representative
    }

    /// Handle to this node's layer stack (C++ `PcpNodeRef::GetLayerStack`).
    /// Resolve it to members through the owning
    /// [`LayerGraph::layer_stack`](crate::pcp::LayerGraph::layer_stack); for
    /// value resolution fold each member's sublayer offset onto this node's arc
    /// offset (`map_to_root.time_offset()`).
    pub(crate) fn layer_stack_id(&self) -> LayerStackId {
        self.layer_stack
    }

    /// The path within this node's layer stack (C++ `PcpNodeRef::GetPath`); may
    /// differ from the composed path due to arc remapping.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The composition arc that introduced this node (C++ `GetArcType`).
    pub fn arc(&self) -> ArcType {
        self.arc
    }

    /// Maps paths from this node's namespace to its parent's (C++
    /// `GetMapToParent`).
    pub fn map_to_parent(&self) -> &MapFunction {
        &self.map_to_parent
    }

    /// Maps paths from this node's namespace directly to the root namespace (C++
    /// `GetMapToRoot`).
    pub fn map_to_root(&self) -> &MapFunction {
        &self.map_to_root
    }

    /// Structural parent, or `None` for a root node.
    pub fn parent(&self) -> Option<NodeId> {
        self.parent
    }

    /// Structural children, in strength order among siblings.
    pub fn children(&self) -> &[NodeId] {
        &self.children
    }

    /// Node that introduced this arc (C++ `GetOriginNode`): the parent for a
    /// direct arc, the propagated-from node for an implied class or graft, or
    /// `None` for the synthetic root.
    pub fn origin(&self) -> Option<NodeId> {
        self.origin
    }

    /// Namespace depth at which the introducing arc was authored.
    pub fn namespace_depth(&self) -> u16 {
        self.namespace_depth
    }

    /// Number of namespace levels this node's site sits below the level at which
    /// its arc was introduced (C++ `PcpNode::GetDepthBelowIntroduction`): the
    /// node path's prim-element count minus its namespace depth. A direct arc
    /// node has depth 0; a node reached by extending that arc to a child has 1,
    /// and so on. Implied-class propagation uses this to tell a class's true
    /// namespace descendants from the arc that continues an ancestral chain.
    pub(crate) fn depth_below_introduction(&self) -> u16 {
        (self.path.prim_element_count() as u16).saturating_sub(self.namespace_depth)
    }

    /// This node's path at the level where its arc was introduced (C++
    /// `PcpNode::GetPathAtIntroduction`): the node path with its
    /// [`depth_below_introduction`](Self::depth_below_introduction) trailing
    /// elements stripped.
    pub(crate) fn path_at_introduction(&self) -> Path {
        let mut path = self.path.clone();
        for _ in 0..self.depth_below_introduction() {
            match path.parent() {
                Some(parent) => path = parent,
                None => break,
            }
        }
        path
    }

    /// Whether any layer in this node's stack authors a spec at its path (C++
    /// `PcpNode::HasSpecs`). A node carrying its full site layer stack may
    /// author nothing at a deepened child path; such a node contributes no
    /// opinions and is not counted as content.
    pub fn has_specs(&self) -> bool {
        self.has_specs
    }

    /// Composition state bits.
    pub fn flags(&self) -> NodeFlags {
        self.flags
    }

    /// True when this node contributes no opinions and is kept only for graph
    /// structure: the synthetic tree root, or a non-contributing class
    /// placeholder added by implied-class propagation (C++ `SetInert`).
    pub fn is_inert(&self) -> bool {
        self.flags.contains(NodeFlags::INERT)
    }

    /// True when this node is retained for composition structure (so an editor
    /// or change tracking can see its arc) but contributes no opinions to value
    /// resolution. Set on an arc whose target site authors no spec (C++
    /// `PcpPrimIndex` culling).
    pub fn is_culled(&self) -> bool {
        self.flags.contains(NodeFlags::CULLED)
    }

    /// True when this node was introduced through a specializes arc (directly
    /// or transitively), making it globally weak per spec section 10.4.1.
    pub(crate) fn introduced_by_specialize(&self) -> bool {
        self.flags.contains(NodeFlags::HAS_SPECIALIZES)
    }

    /// True when this node carries a relocation source site (C++
    /// `PcpNodeRef::IsRestricted` relocate placeholder). It is inert for value
    /// resolution, but its source site must still be tracked as a dependency so
    /// an edit there recomposes the relocated prim.
    pub(crate) fn is_relocate_source(&self) -> bool {
        self.flags.contains(NodeFlags::RELOCATE_SOURCE)
    }

    /// True when this node is a direct arc to a `permission = private` site, or
    /// lies in such an arc's subtree (spec 10.3.3). It stays visible
    /// structurally (`nodes`, `has_spec`, child names) but contributes no
    /// opinions to value resolution — the C++ `_InertSubtree` behavior.
    pub(crate) fn is_permission_denied(&self) -> bool {
        self.flags.contains(NodeFlags::PERMISSION_DENIED)
    }
}

/// Arena-based composition graph.
///
/// `nodes` is the node arena in insertion (structural) order: it is only ever
/// appended to, never reordered, so a [`NodeId`] (an index into it) stays
/// valid for the life of the index and is safe to store in another node's
/// `parent`/`children`/`origin`. Strongest-to-weakest strength order is a
/// separate projection, `strength_order`, holding the same handles permuted —
/// value resolution walks it, not the arena. Dereferencing the graph yields
/// the arena slice for the indexer's structural lookups.
///
/// `root` is the synthetic, inert tree root created by
/// [`init_root`](Self::init_root): every otherwise-parentless node attaches
/// under it, so the graph is a single rooted tree rather than a forest. It is
/// [`NodeId::INVALID`] for the hand-built test graphs that never call
/// `init_root`.
#[derive(Debug, Clone, Default)]
pub(crate) struct PrimIndexGraph {
    pub(crate) nodes: Vec<Node>,
    pub(crate) strength_order: Vec<NodeId>,
    pub(crate) root: NodeId,
    /// Layer ids of reference/payload target roots a composition arc resolved to
    /// but skipped because the target layer was muted (its sublayer stack came
    /// out empty). A muted target contributes no node, so without this the index
    /// keeps no trace of the dependency and unmuting the target could not find it
    /// to recompose; the change machinery reads it to fan a mute toggle out to
    /// such an index (see [`IndexCache`](super::index_cache::IndexCache)'s
    /// layer-muting drop). This serves only that recomposition fanout, not error
    /// reporting — surfacing a skipped muted arc as a diagnostic is the separate
    /// `PcpErrorMutedAssetPath` work the `prim_indexer` still defers.
    pub(crate) muted_external_targets: Vec<LayerId>,
}

impl PrimIndexGraph {
    /// Returns the prim's local root node — the `Root`-arc child of the
    /// synthetic inert root, carrying the prim's own (sublayer) opinions. An
    /// implied class anchors here so it ranks among the prim's direct arcs (C++
    /// `_AddClassBasedArc` adds it under the node owning the prim), regardless
    /// of how deep the arc that implied it sits or whether an ancestral arc was
    /// grafted as a separate root-level sibling. [`NodeId::INVALID`] when the
    /// prim has no local opinion (composed purely through arcs).
    pub(crate) fn local_root(&self) -> NodeId {
        if !self.root.is_valid() {
            return NodeId::INVALID;
        }
        self.nodes[self.root.idx()]
            .children
            .iter()
            .copied()
            .find(|&c| self.nodes[c.idx()].arc == ArcType::Root)
            .unwrap_or(NodeId::INVALID)
    }

    /// Creates the synthetic, inert tree root (C++ unified graph root) and
    /// records it as [`root`](Self::root). Must be the first node, so it takes
    /// [`NodeId`] 0.
    ///
    /// Its identity `map_to_parent`/`map_to_root` make re-parenting an
    /// otherwise-parentless node under it offset-neutral
    /// (`identity ∘ child.map_to_parent == child.map_to_parent`), so a former
    /// forest root keeps the `map_to_root` it had with no parent. The node is
    /// flagged [`INERT`](NodeFlags::INERT) and skipped by value resolution.
    pub(crate) fn init_root(&mut self, layer_stack: LayerStackId, representative: LayerId, path: Path) -> NodeId {
        debug_assert!(self.nodes.is_empty(), "synthetic root must be the first node");
        let id = NodeId(self.nodes.len() as u32);
        let depth = path.prim_element_count() as u16;
        let mut node = Node::new(
            layer_stack,
            representative,
            path,
            ArcType::Root,
            MapFunction::identity(),
            MapFunction::identity(),
            false,
        );
        node.namespace_depth = depth;
        node.flags |= NodeFlags::INERT;
        self.nodes.push(node);
        self.root = id;
        id
    }

    /// Appends a node to the graph, linking it under `parent`.
    ///
    /// `parent` identifies the structural parent in the composition graph. An
    /// [`INVALID`](NodeId::INVALID) `parent` attaches the node under the
    /// synthetic [`root`](Self::root) when one exists, keeping the graph a
    /// single tree; `map_to_root` then composes through that identity-mapped
    /// root, leaving it equal to `map_to_parent`. The new node is recorded in
    /// its parent's children and appended to the arena; the strength projection
    /// is built once at the end of the build by
    /// [`finalize_strength_order`](Self::finalize_strength_order). The returned
    /// handle stays valid for the life of the index.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add_child(
        &mut self,
        parent: NodeId,
        layer_stack: LayerStackId,
        representative: LayerId,
        path: Path,
        arc: ArcType,
        map_to_parent: MapFunction,
        introduced_by_specialize: bool,
    ) -> NodeId {
        // A caller-supplied `INVALID` parent means "a root site": the arc is
        // introduced at this prim. Such nodes re-parent under the synthetic
        // root for structure, but their namespace depth still derives from
        // their own path (the conceptual parent site), not the synthetic root.
        let root_site = !parent.is_valid();
        let struct_parent = if root_site { self.root } else { parent };

        let map_to_root = if struct_parent.is_valid() {
            self.nodes[struct_parent.idx()].map_to_root.compose(&map_to_parent)
        } else {
            map_to_parent.clone()
        };
        // Namespace depth is the prim-element count of the parent site path at
        // arc introduction (C++ `PcpNode_GetNonVariantPathElementCount`); a
        // root site uses its own path.
        let namespace_depth = if root_site {
            path.prim_element_count()
        } else {
            self.nodes[parent.idx()].path.prim_element_count()
        } as u16;
        let idx = NodeId(self.nodes.len() as u32);
        let mut node = Node::new(
            layer_stack,
            representative,
            path,
            arc,
            map_to_parent,
            map_to_root,
            introduced_by_specialize,
        );
        node.namespace_depth = namespace_depth;
        if struct_parent.is_valid() {
            node.parent = Some(struct_parent);
            // A directly-authored arc's origin is its parent (C++
            // `GetOriginNode`). Implied-class and graft propagation overwrite
            // this afterward; setting it here makes `origin` total.
            node.origin = Some(struct_parent);
            self.nodes[struct_parent.idx()].children.push(idx);
        }
        self.nodes.push(node);
        idx
    }

    /// Finds a non-inert, non-culled node already on this graph whose site
    /// matches `(root_layer, path)` (C++ `PcpPrimIndex_Graph::GetNodeUsingSite`).
    ///
    /// The representative layer index is the root sublayer of a node's layer
    /// stack, which uniquely identifies that stack, so matching it together with
    /// the path is equivalent to C++'s `layerStack == site.layerStack` test. The
    /// task-queue indexer uses this for opt-in duplicate-node skipping by the
    /// class-based arcs (inherits/specializes); reference/payload arcs keep
    /// diamonds.
    pub(crate) fn node_using_site(&self, root_layer: LayerId, path: &Path) -> Option<NodeId> {
        self.nodes
            .iter()
            .position(|node| {
                !node.flags.intersects(NodeFlags::INERT | NodeFlags::CULLED)
                    && node.layer_id() == root_layer
                    && &node.path == path
            })
            .map(|i| NodeId(i as u32))
    }

    /// Deepens every node's site path by one namespace element, from the parent
    /// prim to a child (C++ `PcpPrimIndex_Graph::AppendChildNameToAllSites`).
    ///
    /// A node sitting exactly at the parent path moves to `child_path`; every
    /// other node has the child name appended to its own (already deeper or
    /// arc-mapped) path. The namespace mappings are untouched — deepening does
    /// not change how paths translate across arcs, only the depth — so this does
    /// not require re-finalizing strength order. Used to adapt a cloned parent
    /// graph into the seed for its child's index.
    pub(crate) fn append_child_name_to_all_sites(&mut self, child_path: &Path) {
        let Some(parent_path) = child_path.parent() else {
            return;
        };
        let Some(child_name) = child_path.name() else {
            return;
        };
        for node in &mut self.nodes {
            if node.path == parent_path {
                node.path = child_path.clone();
            } else if let Ok(deeper) = node.path.append_path(child_name) {
                node.path = deeper;
            }
        }
    }

    /// Whether `x` is a namespace ancestor of `y` in the composition tree,
    /// walking `y` up its parent chain and stopping before the local root (C++
    /// `Task::PriorityOrder`'s `isAncestorAndDescendant`). The local root and the
    /// synthetic tree root are never reported as ancestors.
    pub(crate) fn is_ancestor_of(&self, x: NodeId, y: NodeId) -> bool {
        let root = self.local_root();
        let mut cur = y;
        while cur.is_valid() && cur != root && cur != self.root {
            if cur == x {
                return true;
            }
            cur = self.nodes[cur.idx()].parent.unwrap_or(NodeId::INVALID);
        }
        false
    }

    /// Collects the chain of nodes from `id` up to its tree root, node first
    /// and root last.
    fn chain_to_root(&self, id: NodeId) -> Vec<NodeId> {
        let mut chain = vec![id];
        let mut cur = id;
        while let Some(parent) = self.nodes[cur.idx()].parent {
            chain.push(parent);
            cur = parent;
        }
        chain
    }

    /// Compares two sibling nodes (nodes sharing a parent) by strength,
    /// porting C++ `PcpCompareSiblingNodeStrength`. Returns [`Ordering::Less`]
    /// when `a` is the stronger sibling.
    ///
    /// Keys, in priority order (spec 10.3): arc type (lower discriminant
    /// stronger); namespace depth (deeper stronger); origin strength (the
    /// stronger origin wins); finally the sibling arc number at the origin (C++
    /// `GetSiblingNumAtOrigin`, lower stronger). Two specializes use the
    /// specializes comparator ([`compare_specialize_siblings`]), which reads the
    /// copy-to-root structure [`propagate_node_to_root`](crate::pcp::prim_indexer)
    /// produces.
    pub(crate) fn compare_sibling_node_strength(&self, a: NodeId, b: NodeId) -> Ordering {
        let na = &self.nodes[a.idx()];
        let nb = &self.nodes[b.idx()];

        // 1. Arc type: lower discriminant (e.g. Inherit) is stronger.
        if na.arc != nb.arc {
            return na.arc.cmp(&nb.arc);
        }

        // Two specializes are copied under the local root (C++
        // `_PropagateNodeToRoot`), so they sort by the specializes branch of C++
        // `PcpCompareSiblingNodeStrength`, which reads that copy-to-root structure.
        if na.introduced_by_specialize() && nb.introduced_by_specialize() {
            return self.compare_specialize_siblings(a, b);
        }

        // 2. Namespace depth: a deeper arc-introduction site is stronger (C++
        // uses higher namespace depth).
        if na.namespace_depth != nb.namespace_depth {
            return nb.namespace_depth.cmp(&na.namespace_depth);
        }

        // 3. Origin strength, only when the two origins differ. `origin` is
        // total (C++ `GetOriginNode`): the node an implied arc was propagated
        // from, or the parent for a directly-authored arc, so two direct
        // siblings share an origin and fall through to the tiebreak below. The
        // synthetic root is the sole node without an origin; it stands in for
        // itself. C++ `_OriginIsStronger` walks the tree in strength order to
        // find which origin comes first; [`compare_node_strength`] is the
        // order-independent equivalent, well-defined here because it never reads
        // the strength projection being computed. It recurses only over
        // strictly-older nodes (an origin is always created before the node
        // carrying it), except when both nodes default to themselves (no origin
        // authored): recursing on the same `(a, b)` would not progress, so skip
        // straight to the sibling-number tiebreak.
        let oa = na.origin.unwrap_or(a);
        let ob = nb.origin.unwrap_or(b);
        if oa != ob && (oa != a || ob != b) {
            let ord = self.compare_node_strength(oa, ob);
            if ord != Ordering::Equal {
                return ord;
            }
        }

        // 4. Origin sibling arc number, then arena index (C++ `GetSiblingNumAtOrigin`,
        // with the arena index as the deterministic tiebreak where C++ returns equal).
        self.sibling_then_index(a, b)
    }

    /// Compares two specializes siblings under the copy-to-root model, porting
    /// the specializes branch of C++ `PcpCompareSiblingNodeStrength`. Returns
    /// [`Ordering::Less`] when `a` is stronger.
    // TODO(perf): invoked O(n log n) times from `finalize_strength_order`'s sort,
    // and `origin_root_node` / `origins_are_nested` / `namespace_depth_for_class_hierarchy`
    // re-walk origin/parent chains while `is_propagated_specializes` re-scans the
    // root's children (`local_root`) on each call. The per-node chain results
    // could be precomputed into a side table once before the sort.
    fn compare_specialize_siblings(&self, a: NodeId, b: NodeId) -> Ordering {
        let (a_root, a_hops) = self.origin_root_node(a);
        let (b_root, b_hops) = self.origin_root_node(b);

        // Origin namespace depth (skipped when the origin roots are nested arcs:
        // a specializes source must stay weaker than its target regardless of
        // namespace depth, C++ `_OriginsAreNestedArcs`).
        if !self.origins_are_nested(a_root, b_root) {
            let da = self.nodes[a.idx()].namespace_depth;
            let db = self.nodes[b.idx()].namespace_depth;
            if da != db {
                return db.cmp(&da);
            }
        }

        let oa = self.origin_of(a);
        let ob = self.origin_of(b);
        let a_authored = oa == self.parent_of(a);
        let b_authored = ob == self.parent_of(b);

        if oa == ob {
            // Same origin: either both authored arcs (fall through to sibling
            // number) or both copied to the root — the implied node (site differs
            // from its origin's) is the more local, stronger opinion.
            if !a_authored && !b_authored {
                return self
                    .implied_beats_propagated(a, oa, b, ob)
                    .unwrap_or_else(|| a.0.cmp(&b.0));
            }
        } else if a_root != b_root {
            // Different authored specialize arcs: order by the strength of the
            // origin roots. C++ `_OriginIsStronger` walks the tree in strength
            // order; [`compare_node_strength`] is the order-independent
            // equivalent, safe to call mid-sort (it never reads the projection).
            return self.compare_node_strength(a_root, b_root).then(a.0.cmp(&b.0));
        } else {
            // Same origin root, different origins: both children of the root.
            // First the namespace depth of the node that inherits/specializes the
            // class hierarchy the origin belongs to (accounts for specializes
            // implied to ancestral hierarchies).
            let a_depth = if a_authored {
                0
            } else {
                self.namespace_depth_for_class_hierarchy(oa)
            };
            let b_depth = if b_authored {
                0
            } else {
                self.namespace_depth_for_class_hierarchy(ob)
            };
            if a_depth != b_depth {
                return a_depth.cmp(&b_depth);
            }
            // Then the longer origin chain (implied further up, more local) wins.
            if a_hops != b_hops {
                return b_hops.cmp(&a_hops);
            }
            // An implied opinion local to the root layer stack beats a propagated
            // one (C++ `TrickySpecializesAndInherits3`).
            if !a_authored && !b_authored && self.same_layer_stack_as_root(a) && self.same_layer_stack_as_root(b) {
                if let Some(ord) = self.implied_beats_propagated(a, oa, b, ob) {
                    return ord;
                }
            }
            // Finally, order by the strength of the two origins themselves.
            return self.compare_node_strength(oa, ob).then(a.0.cmp(&b.0));
        }

        self.sibling_then_index(a, b)
    }

    /// When exactly one of `a`/`b` is an implied copy — its site differs from
    /// its origin's — and the other a propagated original, the implied node is
    /// the more local, stronger opinion (the implied-vs-propagated tiebreak in
    /// C++ `PcpCompareSiblingNodeStrength`). `None` when both or neither are
    /// implied.
    fn implied_beats_propagated(&self, a: NodeId, oa: NodeId, b: NodeId, ob: NodeId) -> Option<Ordering> {
        match (!self.same_site(a, oa), !self.same_site(b, ob)) {
            (true, false) => Some(Ordering::Less),
            (false, true) => Some(Ordering::Greater),
            _ => None,
        }
    }

    /// Sibling arc number at the origin (C++ `GetSiblingNumAtOrigin`, lower
    /// stronger), with the arena index as the final deterministic tiebreak.
    fn sibling_then_index(&self, a: NodeId, b: NodeId) -> Ordering {
        self.nodes[a.idx()]
            .sibling_num_at_origin
            .cmp(&self.nodes[b.idx()].sibling_num_at_origin)
            .then(a.0.cmp(&b.0))
    }

    /// Arc type of a node.
    fn arc_of(&self, id: NodeId) -> ArcType {
        self.nodes[id.idx()].arc
    }

    /// Structural parent, or [`NodeId::INVALID`] for a root node.
    fn parent_of(&self, id: NodeId) -> NodeId {
        self.nodes[id.idx()].parent.unwrap_or(NodeId::INVALID)
    }

    /// Introducing node (C++ `GetOriginNode`), or [`NodeId::INVALID`].
    fn origin_of(&self, id: NodeId) -> NodeId {
        self.nodes[id.idx()].origin.unwrap_or(NodeId::INVALID)
    }

    /// Whether two nodes carry the same site: same representative layer and path
    /// (C++ `GetSite() ==`).
    pub(crate) fn same_site(&self, a: NodeId, b: NodeId) -> bool {
        a.is_valid()
            && b.is_valid()
            && self.nodes[a.idx()].layer_id() == self.nodes[b.idx()].layer_id()
            && self.nodes[a.idx()].path == self.nodes[b.idx()].path
    }

    /// Whether `a`'s layer stack is the local root's layer stack (C++
    /// `GetLayerStack() == GetRootNode().GetLayerStack()`).
    fn same_layer_stack_as_root(&self, a: NodeId) -> bool {
        let root = self.local_root();
        root.is_valid() && self.nodes[a.idx()].layer_stack == self.nodes[root.idx()].layer_stack
    }

    /// Whether a node is a specializes node copied under the local root for
    /// strength ordering (C++ `Pcp_IsPropagatedSpecializesNode`): a specialize
    /// arc whose parent is the local root and whose site equals its origin's.
    pub(crate) fn is_propagated_specializes(&self, id: NodeId) -> bool {
        self.arc_of(id) == ArcType::Specialize
            && self.parent_of(id) == self.local_root()
            && self.same_site(id, self.origin_of(id))
    }

    /// Start of a node's origin chain and the number of hops to it (C++
    /// `PcpNodeRef::GetOriginRootNode`): follows `origin` while it differs from
    /// `parent` (an authored arc has `origin == parent`).
    fn origin_root_node(&self, id: NodeId) -> (NodeId, usize) {
        let mut cur = id;
        let mut hops = 0;
        loop {
            let origin = self.origin_of(cur);
            if !origin.is_valid() || origin == self.parent_of(cur) {
                break;
            }
            cur = origin;
            hops += 1;
        }
        (cur, hops)
    }

    /// Whether `a` is a descendant of `b` or vice versa in the mixed
    /// origin/parent chain (C++ `_OriginsAreNestedArcs`): a propagated
    /// specializes node walks up via its origin, every other node via its parent.
    fn origins_are_nested(&self, a: NodeId, b: NodeId) -> bool {
        self.is_nested_under(a, b) || self.is_nested_under(b, a)
    }

    fn is_nested_under(&self, x: NodeId, y: NodeId) -> bool {
        let mut n = x;
        while n.is_valid() {
            if n == y {
                return true;
            }
            n = if self.is_propagated_specializes(n) {
                self.origin_of(n)
            } else {
                self.parent_of(n)
            };
        }
        false
    }

    /// Namespace depth of the node that inherits or specializes the class
    /// hierarchy `n` belongs to (C++ `_GetNamespaceDepthForClassHierarchy`),
    /// skipping past relocate placeholders.
    fn namespace_depth_for_class_hierarchy(&self, n: NodeId) -> u16 {
        let (mut instance, _class) = self.starting_node_of_class_hierarchy(n);
        while instance.is_valid() && self.arc_of(instance) == ArcType::Relocate {
            instance = self.parent_of(instance);
        }
        if instance.is_valid() {
            self.nodes[instance.idx()].namespace_depth
        } else {
            0
        }
    }

    /// Walks up the chain of class arcs at the same depth-below-introduction from
    /// `n`, returning `(instance node, topmost class node)` (C++
    /// `Pcp_FindStartingNodeOfClassHierarchy`), stepping across a propagated
    /// specializes node via its origin.
    pub(crate) fn starting_node_of_class_hierarchy(&self, n: NodeId) -> (NodeId, NodeId) {
        let mut instance = n;
        if self.is_propagated_specializes(instance) {
            instance = self.origin_of(instance);
        }
        let mut class_node = NodeId::INVALID;
        let depth = self.nodes[instance.idx()].depth_below_introduction();
        while instance.is_valid()
            && is_class_based_arc(self.arc_of(instance))
            && self.nodes[instance.idx()].depth_below_introduction() == depth
        {
            class_node = instance;
            let parent = self.parent_of(instance);
            if !parent.is_valid() {
                break;
            }
            instance = parent;
            if self.is_propagated_specializes(instance) {
                instance = self.origin_of(instance);
            }
        }
        (instance, class_node)
    }

    /// The specializes node copied under the local root for `node`, if any (C++
    /// `_GetPropagatedSpecializesNode`): a local-root child whose origin is
    /// `node` and which is itself a propagated specializes node. Returns `None`
    /// for a non-specializes node.
    pub(crate) fn get_propagated_specializes_node(&self, node: NodeId) -> Option<NodeId> {
        if self.arc_of(node) != ArcType::Specialize {
            return None;
        }
        let root = self.local_root();
        if !root.is_valid() {
            return None;
        }
        self.nodes[root.idx()]
            .children
            .iter()
            .copied()
            .find(|&rc| self.origin_of(rc) == node && self.is_propagated_specializes(rc))
    }

    /// Compares two arbitrary nodes in the same tree by strength, porting C++
    /// `PcpCompareNodeStrength`. Returns [`Ordering::Less`] when `a` is stronger.
    ///
    /// Walks each node's chain to the shared root to find their lowest common
    /// ancestor. When one node is an ancestor of the other, the ancestor is
    /// stronger; otherwise the two diverging children are siblings, compared by
    /// [`compare_sibling_node_strength`](Self::compare_sibling_node_strength).
    pub(crate) fn compare_node_strength(&self, a: NodeId, b: NodeId) -> Ordering {
        if a == b {
            return Ordering::Equal;
        }
        let chain_a = self.chain_to_root(a);
        let chain_b = self.chain_to_root(b);

        // Walk both chains from the root downward (chains are leaf-first) until
        // they diverge. The last shared node is the lowest common ancestor.
        let mut ia = chain_a.len();
        let mut ib = chain_b.len();
        while ia > 0 && ib > 0 {
            let ca = chain_a[ia - 1];
            let cb = chain_b[ib - 1];
            if ca != cb {
                // First divergence: `ca` and `cb` are siblings under the LCA.
                return self.compare_sibling_node_strength(ca, cb);
            }
            ia -= 1;
            ib -= 1;
        }

        // One chain is a prefix of the other: the shorter (the ancestor) wins.
        match (ia, ib) {
            (0, 0) => Ordering::Equal,
            (0, _) => Ordering::Less,
            (_, 0) => Ordering::Greater,
            _ => Ordering::Equal,
        }
    }

    /// Rebuilds the strength-order projection as a pre-order DFS of the tree.
    /// The result runs strongest to weakest; reversing it gives weak-to-strong.
    ///
    /// Each node's `children` are first sorted by
    /// [`compare_sibling_node_strength`](Self::compare_sibling_node_strength), so
    /// the DFS yields strength order among siblings. Specializes are copied under
    /// the local root (C++ `_PropagateNodeToRoot` / `_EvalImpliedSpecializes`)
    /// and specialize is the weakest arc, so the DFS already trails the
    /// globally-weak band (spec 10.4.1) at the end.
    ///
    /// The comparator reads only arc type, namespace depth, origin chains, and
    /// arena order — never the projection being computed — so it is well-defined
    /// here.
    pub(crate) fn finalize_strength_order(&mut self) {
        if !self.root.is_valid() {
            return;
        }

        // Order every node's children by sibling strength. `children` is taken
        // out so the comparator can borrow the arena immutably during the sort.
        for i in 0..self.nodes.len() {
            let mut children = std::mem::take(&mut self.nodes[i].children);
            children.sort_by(|&a, &b| self.compare_sibling_node_strength(a, b));
            self.nodes[i].children = children;
        }

        // Pre-order DFS from the root: visit a node, then its children in
        // strength order. Pushing children reversed makes the strongest pop
        // first. Specializes were copied under the local root (C++
        // `_PropagateNodeToRoot`); specialize is the weakest arc, so those copies
        // and their subtrees sort last among the root's children and the DFS
        // already places the globally-weak band (spec 10.4.1) at the end.
        let mut dfs = Vec::with_capacity(self.nodes.len());
        let mut stack = vec![self.root];
        while let Some(id) = stack.pop() {
            dfs.push(id);
            for &child in self.nodes[id.idx()].children.iter().rev() {
                stack.push(child);
            }
        }
        self.strength_order = dfs;
    }
}

impl std::ops::Deref for PrimIndexGraph {
    /// Dereferences to the node arena in insertion (structural) order. The
    /// indexer relies on this for positional lookups while composing; strength
    /// order is reached through [`PrimIndex::nodes`].
    type Target = [Node];
    fn deref(&self) -> &[Node] {
        &self.nodes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(path: &str, namespace_depth: u16) -> Node {
        let mut n = Node::new(
            LayerStackId::Sublayer(LayerId::from_raw(0)),
            LayerId::from_raw(0),
            Path::from(path),
            ArcType::Inherit,
            MapFunction::identity(),
            MapFunction::identity(),
            false,
        );
        n.namespace_depth = namespace_depth;
        n
    }

    #[test]
    fn introduction_depth_and_path() {
        // An arc introduced at the prim's own level: depth 0, path unchanged.
        let direct = node("/Model", 1);
        assert_eq!(direct.depth_below_introduction(), 0);
        assert_eq!(direct.path_at_introduction(), Path::from("/Model"));

        // The same arc extended two levels into a child: depth 2, and the
        // introduction path strips the two trailing elements.
        let extended = node("/Model/Rig/Anim", 1);
        assert_eq!(extended.depth_below_introduction(), 2);
        assert_eq!(extended.path_at_introduction(), Path::from("/Model"));
    }
}
