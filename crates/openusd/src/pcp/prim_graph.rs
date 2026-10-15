//! Composition graph: arena-backed node tree and strength ordering.
//!
//! [`PrimIndexGraph`] stores the composition [`Node`]s of a single prim in an
//! append-only arena plus a separate strength-order projection. A prim's graph
//! shares the arena with its parent's until it adds a node of its own, and
//! holds each node's site path and contribution flags for itself. See the
//! [module-level docs](super) for the composition overview and
//! [`PrimIndex`](crate::pcp::PrimIndex) for value resolution over the graph.

use std::cmp::Ordering;
use std::collections::HashSet;
use std::sync::Arc;
use std::{fmt, iter, mem};

use bitflags::bitflags;

use crate::sdf::{LayerOffset, Path};

use super::LayerId;
use super::layer_stack::LayerStackId;
use super::mapping::MapFunction;

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

    /// This handle, or `None` for the [`INVALID`](Self::INVALID) sentinel.
    pub(crate) fn valid(self) -> Option<Self> {
        self.is_valid().then_some(self)
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
        /// A relocate node propagated up an ancestor arc rather than grafted at
        /// the relocation itself. See [`RelocateKind`].
        const PROPAGATED_RELOCATE = 1 << 11;
    }
}

/// The bits of [`NodeFlags`] each prim holds for itself ([`NodeSite`]),
/// because they say what a node contributes at that prim's depth. The rest
/// describe the arc, and a prim's children share them with it ([`NodeData`]).
const PER_PRIM: NodeFlags = NodeFlags::INERT
    .union(NodeFlags::CULLED)
    .union(NodeFlags::PROHIBITED_CHILDREN);

/// A single node in the composition graph (C++ `PcpNodeRef`): a view of one
/// node of a [`PrimIndex`](crate::pcp::PrimIndex), borrowed from the index.
///
/// Each node represents a site (layer stack + path) contributing opinions to
/// a composed prim. The identity getters ([`layer_id`](Self::layer_id),
/// [`path`](Self::path), [`arc`](Self::arc)) say *what* it contributes. The
/// namespace mappings ([`map_to_parent`](Self::map_to_parent),
/// [`map_to_root`](Self::map_to_root)) translate paths across composition
/// arcs. The links ([`parent`](Self::parent), [`children`](Self::children),
/// [`origin`](Self::origin)) record its place in the composition tree.
///
/// The view is `Copy`, and what a getter borrows lives as long as the index,
/// so `index.node(id).path()` outlives the view it was read through.
#[derive(Clone, Copy)]
pub struct Node<'a> {
    graph: &'a PrimIndexGraph,
    id: NodeId,
}

impl<'a> Node<'a> {
    fn data(self) -> &'a NodeData {
        &self.graph.shared.nodes[self.id.idx()]
    }

    fn site(self) -> &'a NodeSite {
        &self.graph.sites[self.id.idx()]
    }

    /// This node's handle in its index.
    pub fn id(self) -> NodeId {
        self.id
    }

    /// Id of the strongest layer contributing at this site. A representative
    /// for callers that key on a single layer (dependencies, dumps); value
    /// resolution iterates the node's resolved layer-stack members instead.
    pub fn layer_id(self) -> LayerId {
        self.data().representative
    }

    /// Handle to this node's layer stack (C++ `PcpNodeRef::GetLayerStack`).
    /// Resolve it to members through the owning
    /// [`LayerGraph::layer_stack`](crate::pcp::LayerGraph::layer_stack); for
    /// value resolution fold each member's sublayer offset onto this node's arc
    /// offset (`map_to_root.time_offset()`).
    pub(crate) fn layer_stack_id(self) -> LayerStackId {
        self.data().layer_stack
    }

    /// The path within this node's layer stack (C++ `PcpNodeRef::GetPath`); may
    /// differ from the composed path due to arc remapping.
    pub fn path(self) -> &'a Path {
        &self.site().path
    }

    /// The composition arc that introduced this node (C++ `GetArcType`).
    pub fn arc(self) -> ArcType {
        self.data().arc
    }

    /// Maps paths from this node's namespace to its parent's (C++
    /// `GetMapToParent`).
    pub fn map_to_parent(self) -> &'a MapFunction {
        &self.data().map_to_parent
    }

    /// Maps paths from this node's namespace directly to the root namespace (C++
    /// `GetMapToRoot`).
    pub fn map_to_root(self) -> &'a MapFunction {
        &self.data().map_to_root
    }

    /// Structural parent, or `None` for a root node.
    pub fn parent(self) -> Option<NodeId> {
        self.data().parent.valid()
    }

    /// Structural children, in strength order among siblings once the index is
    /// built.
    pub fn children(self) -> impl Iterator<Item = NodeId> + 'a {
        self.graph.children(self.id)
    }

    /// Node that introduced this arc (C++ `GetOriginNode`): the parent for a
    /// direct arc, the propagated-from node for an implied class or graft, or
    /// `None` for the synthetic root.
    pub fn origin(self) -> Option<NodeId> {
        self.data().origin.valid()
    }

    /// Namespace depth at which the introducing arc was authored (C++
    /// `PcpNode::GetNamespaceDepth`): the prim-element count of the parent
    /// site's path when this node was added.
    pub fn namespace_depth(self) -> u16 {
        self.data().namespace_depth
    }

    /// This node's index among the same-arc-type siblings at its origin (C++
    /// `GetSiblingNumAtOrigin`).
    pub(crate) fn sibling_num_at_origin(self) -> u16 {
        self.data().sibling_num_at_origin
    }

    /// Whether any layer in this node's stack authors a spec at its path (C++
    /// `PcpNode::HasSpecs`). A node carrying its full site layer stack may
    /// author nothing at a deepened child path; such a node contributes no
    /// opinions and is not counted as content.
    pub fn has_specs(self) -> bool {
        self.site().has_specs
    }

    /// How many of the node's stack's strongest layers are known to author no
    /// spec at its path: the position of the first that does, when the
    /// indexer found [`has_specs`](Self::has_specs) by probing them in order,
    /// and 0 otherwise. A layer before it holds no field at the path either.
    pub(crate) fn spec_from(self) -> u16 {
        let site = self.site();
        if site.has_specs { site.spec_from } else { 0 }
    }

    /// Namespace depth at which this node's spec contribution was restricted
    /// (C++ `PcpNode::GetSpecContributionRestrictedDepth`), or 0 when
    /// unrestricted.
    pub(crate) fn restriction_depth(self) -> u16 {
        self.site().restriction_depth
    }

    /// Composition state bits.
    pub fn flags(self) -> NodeFlags {
        self.data().flags | self.site().flags
    }

    /// True when this node contributes no opinions and is kept only for graph
    /// structure: the synthetic tree root, or a non-contributing class
    /// placeholder added by implied-class propagation (C++ `SetInert`).
    pub fn is_inert(self) -> bool {
        self.site().flags.contains(NodeFlags::INERT)
    }

    /// True when this node is retained for composition structure (so an editor
    /// or change tracking can see its arc) but contributes no opinions to value
    /// resolution. Set on an arc whose target site authors no spec (C++
    /// `PcpPrimIndex` culling).
    pub fn is_culled(self) -> bool {
        self.site().flags.contains(NodeFlags::CULLED)
    }

    /// True when this node carries a relocation source site (C++
    /// `PcpNodeRef::IsRestricted` relocate placeholder). It is inert for value
    /// resolution, but its source site must still be tracked as a dependency so
    /// an edit there recomposes the relocated prim.
    pub(crate) fn is_relocate_source(self) -> bool {
        self.data().flags.contains(NodeFlags::RELOCATE_SOURCE)
    }

    /// Which of the two relocate shapes this node is, or `None` when it is not
    /// a relocate arc at all.
    ///
    /// The kind is recorded when the node is built rather than inferred here,
    /// because every property that would betray it — the map, inertness, the
    /// parent link — is rewritten by grafting, propagation, or prototype
    /// rebasing.
    pub(crate) fn relocate_kind(self) -> Option<RelocateKind> {
        let data = self.data();
        let propagated = data.flags.contains(NodeFlags::PROPAGATED_RELOCATE);
        debug_assert!(
            !propagated || data.arc == ArcType::Relocate,
            "PROPAGATED_RELOCATE marks a node that is not a relocate arc",
        );
        (data.arc == ArcType::Relocate).then_some(if propagated {
            RelocateKind::Propagated
        } else {
            RelocateKind::Direct
        })
    }
}

impl fmt::Debug for Node<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("id", &self.id)
            .field("data", self.data())
            .field("site", self.site())
            .finish()
    }
}

/// Everything [`PrimIndexGraph::add_child`] needs to insert a node. The
/// fields with defaults are the ones most arcs leave alone.
#[derive(Debug, Clone)]
pub(crate) struct NodeDesc {
    /// Handle to the layer stack contributing opinions at the site.
    pub(crate) layer_stack: LayerStackId,
    /// The strongest layer of [`layer_stack`](Self::layer_stack).
    pub(crate) representative: LayerId,
    /// The site's path within that layer stack.
    pub(crate) path: Path,
    /// The composition arc introducing the node.
    pub(crate) arc: ArcType,
    /// Maps paths from the node's namespace to its parent's.
    pub(crate) map_to_parent: MapFunction,
    /// The node that introduced the arc, or `None` for the structural parent,
    /// which is the origin of a directly authored arc.
    pub(crate) origin: Option<NodeId>,
    /// The namespace depth the arc was introduced at, or `None` for the
    /// prim-element count of the parent site's path.
    pub(crate) namespace_depth: Option<u16>,
    /// The node's index among the same-arc-type siblings at its origin.
    pub(crate) sibling_num_at_origin: u16,
    /// Whether a layer of the stack authors a spec at the path.
    pub(crate) has_specs: bool,
    /// How many of the stack's strongest layers are known to author no spec
    /// at the path ([`Node::spec_from`]).
    pub(crate) spec_from: u16,
    /// The depth the node's spec contribution is restricted at, 0 for none.
    pub(crate) restriction_depth: u16,
    /// The node's state bits, of either half.
    pub(crate) flags: NodeFlags,
}

impl NodeDesc {
    /// A spec-bearing, unrestricted node for a directly authored arc.
    pub(crate) fn new(
        layer_stack: LayerStackId,
        representative: LayerId,
        path: Path,
        arc: ArcType,
        map_to_parent: MapFunction,
    ) -> Self {
        Self {
            layer_stack,
            representative,
            path,
            arc,
            map_to_parent,
            origin: None,
            namespace_depth: None,
            sibling_num_at_origin: 0,
            has_specs: true,
            spec_from: 0,
            restriction_depth: 0,
            flags: NodeFlags::empty(),
        }
    }
}

/// The half of a node that a prim's children share with it: the arc, the
/// links, the maps and the bits that describe the arc.
#[derive(Debug, Clone)]
struct NodeData {
    /// Handle to the layer stack contributing opinions at this site (C++
    /// `PcpNode::GetLayerStack`). Resolve it to members through the owning layer
    /// graph's [`layer_stack`](crate::pcp::LayerGraph::layer_stack) rather than
    /// storing them on each node. The stack also carries the composed
    /// expression variables this node's opinions resolve against
    /// (`LayerGraph::stack_variables`).
    layer_stack: LayerStackId,
    /// The strongest (representative) layer of [`layer_stack`](Self::layer_stack)
    /// (C++ `PcpNode::GetLayerStack()->GetLayers().front()`). Cached so
    /// [`Node::layer_id`] — the member handle dependencies and dumps key on —
    /// resolves without the layer graph. Structural identity
    /// ([`same_site`](PrimIndexGraph::same_site),
    /// [`node_using_site`](PrimIndexGraph::node_using_site)) keys on
    /// [`layer_stack`](Self::layer_stack) instead.
    representative: LayerId,
    /// The composition arc that introduced this node.
    arc: ArcType,
    /// Maps paths from this node's namespace to its parent's namespace.
    map_to_parent: MapFunction,
    /// Maps paths from this node's namespace directly to the root namespace.
    /// Computed as `parent.map_to_root.compose(self.map_to_parent)`.
    map_to_root: MapFunction,
    /// Structural parent, or [`NodeId::INVALID`] for a root node.
    parent: NodeId,
    /// Node that introduced this arc (C++ `GetOriginNode`): the parent for a
    /// direct arc, or the propagated-from node for an implied class or graft.
    /// [`NodeId::INVALID`] only for the synthetic root.
    origin: NodeId,
    /// The first of this node's children, or [`NodeId::INVALID`] for none. With
    /// [`last_child`](Self::last_child) and each child's
    /// [`next_sibling`](Self::next_sibling) it forms the child list (C++
    /// `_Node::_Indexes`): in insertion order while a graph is built, in
    /// strength order once it is finalized.
    first_child: NodeId,
    /// The last of this node's children, where an insert links.
    last_child: NodeId,
    /// The next child of this node's parent.
    next_sibling: NodeId,
    /// Namespace depth at which the introducing arc was authored (C++
    /// `PcpNode::GetNamespaceDepth`): the prim-element count of the parent
    /// site's path when this node was added. Used by implied
    /// inherits/specializes that propagate toward the root, and by
    /// [`PrimIndexGraph::depth_below_introduction`].
    namespace_depth: u16,
    /// This node's index among the same-arc-type siblings at its origin (C++
    /// `GetSiblingNumAtOrigin`): the arc number a class-based arc was authored
    /// with. Carried onto implied copies so their relative strength is preserved;
    /// reference/payload arcs leave it 0.
    sibling_num_at_origin: u16,
    /// The bits of [`NodeFlags`] outside [`PER_PRIM`].
    flags: NodeFlags,
}

/// The half of a node each prim holds for itself: where the node sits in that
/// prim's namespace, and what it contributes there.
///
/// C++ `PcpPrimIndex_Graph::_UnsharedData` holds the same, except that it
/// keeps `inert` with the shared node. Here [`INERT`](NodeFlags::INERT) is per
/// prim: a prim inside an instance inerts nodes it took from its parent, and
/// its graph still shares the parent's [`GraphData`].
#[derive(Debug, Clone)]
struct NodeSite {
    /// The path within the node's layer stack (may differ from the composed
    /// path due to remapping).
    path: Path,
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
    restriction_depth: u16,
    /// Whether any layer in the node's stack authors a spec at
    /// [`path`](Self::path) (C++ `PcpNode::HasSpecs`). Under the full-site-stack
    /// model a node may carry its whole layer stack yet author no spec at its
    /// path — a seeded ancestral site deepened to a child that has no opinion
    /// there. Such a node is kept for structure (it may still introduce arcs at
    /// the deepened path) but contributes nothing to value resolution and is not
    /// counted by [`is_empty`](crate::pcp::PrimIndex::is_empty). A culled node
    /// standing in for an empty arc target likewise carries `false`.
    has_specs: bool,
    /// How many of the stack's strongest layers are known to author no spec
    /// at [`path`](Self::path), where [`has_specs`](Self::has_specs) was
    /// established by probing them in order ([`Node::spec_from`]).
    spec_from: u16,
    /// The bits of [`NodeFlags`] inside [`PER_PRIM`].
    flags: NodeFlags,
}

/// How a [`Relocate`](ArcType::Relocate) node came to be, which decides how a
/// path translates through it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RelocateKind {
    /// Grafted at the relocation itself, carrying the source-to-target rename
    /// in its own map function.
    Direct,
    /// Propagated up an ancestor arc by `_EvalImpliedRelocations` so implied
    /// class arcs keep crossing the relocation. It holds the identity map, so
    /// the rename lives on the direct relocate it originated from and a path
    /// translates by stepping out into the parent's namespace.
    Propagated,
}

/// One contributing prim spec in a [`PrimIndex`](crate::pcp::PrimIndex)'s
/// memoized spec stack (C++ `PcpPrimIndex`'s spec stack): the node it came from,
/// the layer that authored it, and that layer's time offset folded to the root
/// namespace.
///
/// An entry exists for each `(node, layer)` where the layer authors a spec at
/// the node's path; the stack collects them in strength order. [`node`](Self::node)
/// indexes the arena; resolve it through
/// [`PrimIndex::node`](crate::pcp::PrimIndex::node). [`offset`](Self::offset) is
/// the member's sublayer offset composed onto the node's arc offset
/// (`map_to_root().time_offset()`), the value-resolution view of the member's
/// retiming to root. See [`PrimIndex::finalize_spec_stack`](crate::pcp::PrimIndex)
/// for how the stack is built and read.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SpecSite {
    /// The contributing node, by arena handle.
    pub(crate) node: NodeId,
    /// The layer that authored the spec at the node's path.
    pub(crate) layer: LayerId,
    /// The contributing layer's time offset folded to the root namespace.
    pub(crate) offset: LayerOffset,
}

/// The nodes of a composition graph with everything a prim's children take
/// from it unchanged: the arena of [`NodeData`], the strength order over it,
/// and the root.
#[derive(Debug, Clone, Default)]
struct GraphData {
    /// The node arena in insertion order.
    nodes: Vec<NodeData>,
    /// The arena's handles, strongest first.
    strength_order: Vec<NodeId>,
    /// The synthetic tree root, or [`NodeId::INVALID`] before
    /// [`PrimIndexGraph::init_root`].
    root: NodeId,
}

/// Arena-based composition graph.
///
/// The node arena is in insertion (structural) order: it is only ever
/// appended to, never reordered, so a [`NodeId`] (an index into it) stays
/// valid for the life of the index and is safe to store in another node's
/// links. Strongest-to-weakest strength order is a separate projection,
/// [`strength_order`](Self::strength_order), holding the same handles permuted
/// — value resolution walks it, not the arena.
///
/// A node is stored in two halves (C++ `PcpPrimIndex_Graph`'s node pool and
/// its unshared data). [`GraphData`] holds what a child prim's graph takes
/// from its parent's unchanged, behind an `Arc` both graphs hold until one of
/// them adds a node or rewrites a map. `sites` holds what each prim has of its
/// own, one [`NodeSite`] per node.
///
/// The root is the synthetic, inert tree root created by
/// [`init_root`](Self::init_root): every otherwise-parentless node attaches
/// under it, so the graph is a single rooted tree rather than a forest. It is
/// [`NodeId::INVALID`] for the hand-built test graphs that never call
/// `init_root`.
#[derive(Debug, Clone, Default)]
pub(crate) struct PrimIndexGraph {
    /// Nodes, links, maps and arc flags, shared with the graph this one was
    /// seeded from until either changes them ([`data_mut`](Self::data_mut)).
    shared: Arc<GraphData>,
    /// One entry per node of `shared`, by [`NodeId`].
    sites: Vec<NodeSite>,
    /// This index's dependencies that no `(layer, site)` registration can
    /// express, or `None` when it has none — the common case, which the single
    /// pointer keeps to one machine word.
    ///
    /// Shared, not owned: a child prim seeds from its parent's graph
    /// ([`Indexer::seed`](super::prim_indexer::Indexer)), so a referenced
    /// asset's whole subtree inherits one non-empty value. Copy-on-write through
    /// [`non_site_deps_mut`](Self::non_site_deps_mut) means only a descendant
    /// that records a dependency of its own pays for a copy.
    non_site_deps: Option<Arc<NonSiteDeps>>,
    /// Whether every node's children are sorted by
    /// [`compare_sibling_node_strength`](Self::compare_sibling_node_strength),
    /// the strength order is the pre-order walk of that tree, and both stay so
    /// when every site deepens by one name
    /// ([`append_child_name_to_all_sites`](Self::append_child_name_to_all_sites)).
    ///
    /// The comparator reads site paths only to ask whether two nodes' paths
    /// are equal and whether two nodes sit equally far below their
    /// introduction. A uniform append changes neither answer unless the graph
    /// holds a [`shallow_parent`](Self::shallow_parent);
    /// [`finalize_strength_order`](Self::finalize_strength_order) leaves the
    /// flag clear for such a graph. Inserting a node, or making room for one
    /// ([`reserve`](Self::reserve)), clears it. Writes to a node's per-prim
    /// half or its maps keep it, since the comparator reads none of them.
    finalized: bool,
    /// Whether some node was inserted with a namespace depth greater than its
    /// parent site's, so that its
    /// [`depth_below_introduction`](Self::depth_below_introduction) clamps at
    /// 0 and does not grow in step with the other nodes' as the graph deepens.
    shallow_parent: bool,
}

/// Dependencies of a prim index that no `(layer, site)` registration can
/// express, because the arc that created them grafted no node or because what
/// was read is layer metadata rather than a site.
///
/// [`Dependencies`](super::dependencies::Dependencies) registers all three so a
/// later edit can still find the index to recompose; each skipped arc is
/// separately surfaced as its own [`CompositionDiagnostic`](super::CompositionDiagnostic).
#[derive(Debug, Clone, Default)]
pub(crate) struct NonSiteDeps {
    /// Layer ids of reference/payload target roots a composition arc resolved to
    /// but skipped because the target layer was muted (its sublayer stack came
    /// out empty). A muted target contributes no node, so without this the index
    /// keeps no trace of the dependency and unmuting the target could not find it
    /// to recompose.
    pub(crate) muted_external: Vec<LayerId>,
    /// Canonical identifiers of reference/payload targets a composition arc
    /// resolved to but skipped because the target was muted *before it was ever
    /// loaded* — the target has no interned [`LayerId`], so
    /// [`muted_external`](Self::muted_external) cannot record it. The identifier
    /// is the one the muted set matched (C++ `Pcp_MutedLayers`), so unmuting that
    /// same canonical identifier fans the invalidation back to this index.
    pub(crate) muted_unloaded: Vec<String>,
    /// Layers whose `defaultPrim` a reference or payload consulted because the
    /// arc named no target prim.
    ///
    /// Recorded whether or not a default was found: when there is none the arc
    /// grafts no node at all, so this is the only trace that authoring the field
    /// later must recompose this prim. Held as a layer id because that is what
    /// the field is keyed by: the ancestral seed deepens every node path
    /// ([`append_child_name_to_all_sites`](PrimIndexGraph::append_child_name_to_all_sites)),
    /// which a site-shaped record would not survive.
    pub(crate) default_prim: Vec<LayerId>,
}

impl NonSiteDeps {
    /// Sorts and deduplicates every vector. One target reached through both a
    /// `references` and a `payload` arc, or through several sub-builds, records
    /// once.
    fn dedup(&mut self) {
        self.muted_external.sort_unstable();
        self.muted_external.dedup();
        self.muted_unloaded.sort_unstable();
        self.muted_unloaded.dedup();
        self.default_prim.sort_unstable();
        self.default_prim.dedup();
    }
}

impl PrimIndexGraph {
    /// Number of nodes in the arena.
    pub(crate) fn len(&self) -> usize {
        self.sites.len()
    }

    /// Whether the arena holds no node.
    pub(crate) fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    /// The synthetic tree root, or [`NodeId::INVALID`] before
    /// [`init_root`](Self::init_root).
    pub(crate) fn root(&self) -> NodeId {
        self.shared.root
    }

    /// The arena's handles, strongest first, as the last
    /// [`finalize_strength_order`](Self::finalize_strength_order) left them.
    pub(crate) fn strength_order(&self) -> &[NodeId] {
        &self.shared.strength_order
    }

    /// The node behind `id`.
    pub(crate) fn node(&self, id: NodeId) -> Node<'_> {
        debug_assert!(id.idx() < self.len(), "node handle out of range");
        Node { graph: self, id }
    }

    /// Every node, in arena (insertion) order.
    pub(crate) fn nodes(&self) -> impl DoubleEndedIterator<Item = Node<'_>> + ExactSizeIterator + Clone {
        (0..self.len() as u32).map(|i| Node {
            graph: self,
            id: NodeId(i),
        })
    }

    /// The children of `id`, first to last.
    pub(crate) fn children(&self, id: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        let nodes = &self.shared.nodes;
        iter::successors(nodes[id.idx()].first_child.valid(), move |child| {
            nodes[child.idx()].next_sibling.valid()
        })
    }

    /// The shared half for writing, taking a private copy first when another
    /// graph still holds it.
    fn data_mut(&mut self) -> &mut GraphData {
        Arc::make_mut(&mut self.shared)
    }

    /// The shared half for inserting `additional` nodes. When another graph
    /// still holds it, the private copy is made with room for them (a quarter
    /// of the arena when `additional` is 0, as C++
    /// `_DetachSharedNodePoolForNewNodes`), so the insert does not grow it
    /// again. The copy leaves the strength order behind: an insert makes it
    /// stale, and [`finalize_strength_order`](Self::finalize_strength_order)
    /// rebuilds it.
    fn data_for_insert(&mut self, additional: usize) -> &mut GraphData {
        if Arc::strong_count(&self.shared) > 1 {
            let shared = &*self.shared;
            let len = shared.nodes.len();
            let room = if additional == 0 { (len / 4).max(1) } else { additional };
            let mut nodes = Vec::with_capacity(len + room);
            nodes.extend(shared.nodes.iter().cloned());
            self.shared = Arc::new(GraphData {
                nodes,
                strength_order: Vec::new(),
                root: shared.root,
            });
        }
        self.finalized = false;
        Arc::get_mut(&mut self.shared).expect("no other graph holds the shared half")
    }

    /// Makes room for `additional` more nodes, copying the shared half once if
    /// another graph holds it. A graft calls this with its node count. It
    /// counts as the insert it prepares: the strength order is left to be
    /// sorted afresh.
    pub(crate) fn reserve(&mut self, additional: usize) {
        self.data_for_insert(additional).nodes.reserve(additional);
        self.sites.reserve(additional);
    }

    /// Sets per-prim `flags` on the node behind `id`. The flags that describe
    /// the arc are given at insertion ([`NodeDesc::flags`]).
    pub(crate) fn mark(&mut self, id: NodeId, flags: NodeFlags) {
        debug_assert!(PER_PRIM.contains(flags), "an arc flag is set as its node is inserted");
        self.sites[id.idx()].flags |= flags;
    }

    /// Records whether a layer of the node's stack authors a spec at its path,
    /// without recording which, so a reader probes the stack from its
    /// strongest layer.
    pub(crate) fn set_has_specs(&mut self, id: NodeId, has_specs: bool) {
        self.set_first_spec(id, has_specs.then_some(0));
    }

    /// Records the position in the node's stack of the strongest layer that
    /// authors a spec at its path, `None` when no layer does.
    pub(crate) fn set_first_spec(&mut self, id: NodeId, first: Option<u16>) {
        let site = &mut self.sites[id.idx()];
        site.has_specs = first.is_some();
        site.spec_from = first.unwrap_or(0);
    }

    /// Records the depth the node's spec contribution is restricted at.
    pub(crate) fn set_restriction_depth(&mut self, id: NodeId, depth: u16) {
        self.sites[id.idx()].restriction_depth = depth;
    }

    /// Rewrites every node's maps through `rebase`, which is given the
    /// node's `map_to_root` and `map_to_parent` in turn. The shared half
    /// becomes this graph's own. Returns how many nodes that copied: the arena
    /// when another graph held it, 0 otherwise.
    pub(crate) fn rebase_maps(&mut self, rebase: impl Fn(&MapFunction) -> MapFunction) -> usize {
        let copied = if Arc::strong_count(&self.shared) > 1 {
            self.len()
        } else {
            0
        };
        for node in &mut self.data_mut().nodes {
            node.map_to_root = rebase(&node.map_to_root);
            node.map_to_parent = rebase(&node.map_to_parent);
        }
        copied
    }

    /// Whether this graph and `other` hold one [`GraphData`].
    pub(crate) fn shares_data_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.shared, &other.shared)
    }

    /// How many distinct [`GraphData`] `graphs` hold between them.
    pub(crate) fn distinct_data<'a>(graphs: impl Iterator<Item = &'a Self>) -> usize {
        graphs
            .map(|graph| Arc::as_ptr(&graph.shared))
            .collect::<HashSet<_>>()
            .len()
    }

    /// The seed for the index of the child prim at `child_path`: this graph
    /// with every site deepened by the child's name
    /// ([`append_child_name_to_all_sites`](Self::append_child_name_to_all_sites)),
    /// holding the same shared half.
    pub(crate) fn seed_child(&self, child_path: &Path) -> Self {
        let mut uniform = true;
        let sites = match (child_path.parent(), child_path.name()) {
            (Some(parent_path), Some(child_name)) => self
                .sites
                .iter()
                .map(|site| {
                    let (path, deepened) = deepen(&site.path, &parent_path, child_path, child_name);
                    uniform &= deepened;
                    NodeSite { path, ..*site }
                })
                .collect(),
            _ => self.sites.clone(),
        };
        Self {
            shared: Arc::clone(&self.shared),
            sites,
            non_site_deps: self.non_site_deps.clone(),
            finalized: self.finalized && uniform,
            shallow_parent: self.shallow_parent,
        }
    }

    /// The recorded [`NonSiteDeps`], or `None` when this index has none.
    pub(crate) fn non_site_deps(&self) -> Option<&NonSiteDeps> {
        self.non_site_deps.as_deref()
    }

    /// The recorded [`NonSiteDeps`] as the shared handle, so a graph with none
    /// of its own can adopt another's without copying.
    pub(crate) fn non_site_deps_shared(&self) -> Option<&Arc<NonSiteDeps>> {
        self.non_site_deps.as_ref()
    }

    /// Takes `deps` as this graph's own, sharing the allocation. Only valid
    /// when it has none — [`non_site_deps_mut`](Self::non_site_deps_mut) is the
    /// copy-on-write path for merging into an existing value.
    pub(crate) fn adopt_non_site_deps(&mut self, deps: Arc<NonSiteDeps>) {
        debug_assert!(self.non_site_deps.is_none(), "adopting over recorded deps");
        self.non_site_deps = Some(deps);
    }

    /// The recorded [`NonSiteDeps`] for writing, materializing them on first use
    /// and taking a private copy if they are still shared with the ancestor this
    /// graph was seeded from.
    pub(crate) fn non_site_deps_mut(&mut self) -> &mut NonSiteDeps {
        Arc::make_mut(self.non_site_deps.get_or_insert_default())
    }

    /// Sorts and deduplicates the recorded [`NonSiteDeps`]. Called once per
    /// built graph.
    ///
    /// Deduplicates only what this build owns. A value still shared with the
    /// ancestor graph this one was seeded from was already finalized there, and
    /// taking a copy of it just to re-sort would defeat the sharing — the cost
    /// would land on every descendant of a prim with a non-site dependency.
    pub(crate) fn finalize_non_site_deps(&mut self) {
        if let Some(owned) = self.non_site_deps.as_mut().and_then(Arc::get_mut) {
            owned.dedup();
        }
    }

    /// Returns the prim's local root node — the `Root`-arc child of the
    /// synthetic inert root, carrying the prim's own (sublayer) opinions. An
    /// implied class anchors here so it ranks among the prim's direct arcs (C++
    /// `_AddClassBasedArc` adds it under the node owning the prim), regardless
    /// of how deep the arc that implied it sits or whether an ancestral arc was
    /// grafted as a separate root-level sibling. [`NodeId::INVALID`] when the
    /// prim has no local opinion (composed purely through arcs).
    pub(crate) fn local_root(&self) -> NodeId {
        let root = self.shared.root;
        if !root.is_valid() {
            return NodeId::INVALID;
        }
        self.children(root)
            .find(|&c| self.shared.nodes[c.idx()].arc == ArcType::Root)
            .unwrap_or_default()
    }

    /// Creates the synthetic, inert tree root (C++ unified graph root) and
    /// records it as the [`root`](Self::root). Must be the first node, so it
    /// takes [`NodeId`] 0.
    ///
    /// Its identity `map_to_parent`/`map_to_root` make re-parenting an
    /// otherwise-parentless node under it offset-neutral
    /// (`identity ∘ child.map_to_parent == child.map_to_parent`), so a former
    /// forest root keeps the `map_to_root` it had with no parent. The node is
    /// flagged [`INERT`](NodeFlags::INERT) and skipped by value resolution.
    pub(crate) fn init_root(&mut self, layer_stack: LayerStackId, representative: LayerId, path: Path) -> NodeId {
        debug_assert!(self.is_empty(), "synthetic root must be the first node");
        let mut desc = NodeDesc::new(
            layer_stack,
            representative,
            path,
            ArcType::Root,
            MapFunction::identity(),
        );
        desc.flags = NodeFlags::INERT;
        let id = self.add_child(NodeId::INVALID, desc);
        self.data_mut().root = id;
        id
    }

    /// Appends the node `desc` describes, linking it under `parent`.
    ///
    /// `parent` identifies the structural parent in the composition graph. An
    /// [`INVALID`](NodeId::INVALID) `parent` attaches the node under the
    /// synthetic [`root`](Self::root) when one exists, keeping the graph a
    /// single tree; `map_to_root` then composes through that identity-mapped
    /// root, leaving it equal to `map_to_parent`. The new node is linked last
    /// among its parent's children and appended to the arena; the strength
    /// projection is built once at the end of the build by
    /// [`finalize_strength_order`](Self::finalize_strength_order). The returned
    /// handle stays valid for the life of the index.
    pub(crate) fn add_child(&mut self, parent: NodeId, desc: NodeDesc) -> NodeId {
        // A caller-supplied `INVALID` parent means "a root site": the arc is
        // introduced at this prim. Such nodes re-parent under the synthetic
        // root for structure, but their namespace depth still derives from
        // their own path (the conceptual parent site), not the synthetic root.
        let root_site = !parent.is_valid();
        let struct_parent = if root_site { self.shared.root } else { parent };

        let map_to_root = if struct_parent.is_valid() {
            self.shared.nodes[struct_parent.idx()]
                .map_to_root
                .compose(&desc.map_to_parent)
        } else {
            desc.map_to_parent.clone()
        };
        // Namespace depth is the prim-element count of the parent site path at
        // arc introduction (C++ `PcpNode_GetNonVariantPathElementCount`); a
        // root site uses its own path.
        let parent_depth = struct_parent
            .valid()
            .map(|parent| self.sites[parent.idx()].path.prim_element_count() as u16);
        let namespace_depth = desc.namespace_depth.unwrap_or_else(|| match parent_depth {
            Some(depth) if !root_site => depth,
            _ => desc.path.prim_element_count() as u16,
        });
        self.shallow_parent |= parent_depth.is_some_and(|depth| depth < namespace_depth);
        let id = NodeId(self.len() as u32);
        let data = self.data_for_insert(0);
        if struct_parent.is_valid() {
            let last = mem::replace(&mut data.nodes[struct_parent.idx()].last_child, id);
            match last.valid() {
                Some(last) => data.nodes[last.idx()].next_sibling = id,
                None => data.nodes[struct_parent.idx()].first_child = id,
            }
        }
        data.nodes.push(NodeData {
            layer_stack: desc.layer_stack,
            representative: desc.representative,
            arc: desc.arc,
            map_to_parent: desc.map_to_parent,
            map_to_root,
            parent: struct_parent,
            // A directly-authored arc's origin is its parent (C++
            // `GetOriginNode`), which makes `origin` total.
            origin: desc.origin.unwrap_or(struct_parent),
            first_child: NodeId::INVALID,
            last_child: NodeId::INVALID,
            next_sibling: NodeId::INVALID,
            namespace_depth,
            sibling_num_at_origin: desc.sibling_num_at_origin,
            flags: desc.flags - PER_PRIM,
        });
        self.sites.push(NodeSite {
            path: desc.path,
            restriction_depth: desc.restriction_depth,
            has_specs: desc.has_specs,
            spec_from: desc.spec_from,
            flags: desc.flags & PER_PRIM,
        });
        id
    }

    /// Finds a non-inert, non-culled node already on this graph whose site
    /// matches `(layer_stack, path)` (C++ `PcpPrimIndex_Graph::GetNodeUsingSite`).
    ///
    /// Matches on the node's layer-stack handle directly (C++'s `layerStack ==
    /// site.layerStack` test). The task-queue indexer uses this for opt-in
    /// duplicate-node skipping by the class-based arcs (inherits/specializes);
    /// reference/payload arcs keep diamonds.
    pub(crate) fn node_using_site(&self, layer_stack: LayerStackId, path: &Path) -> Option<NodeId> {
        self.sites
            .iter()
            .zip(&self.shared.nodes)
            .position(|(site, node)| {
                !site.flags.intersects(NodeFlags::INERT | NodeFlags::CULLED)
                    && node.layer_stack == layer_stack
                    && &site.path == path
            })
            .map(|i| NodeId(i as u32))
    }

    /// Deepens every node's site path by one namespace element, from the parent
    /// prim to a child (C++ `PcpPrimIndex_Graph::AppendChildNameToAllSites`).
    ///
    /// A node sitting exactly at the parent path moves to `child_path`; every
    /// other node has the child name appended to its own (already deeper or
    /// arc-mapped) path. The namespace mappings are untouched — deepening does
    /// not change how paths translate across arcs, only the depth. Used to
    /// adapt a parent graph into the seed for its child's index. It writes
    /// only the per-prim half, so the two graphs go on sharing the rest.
    ///
    /// The strength order stays current (C++ notes the same of
    /// `AppendChildNameToAllSites`), unless a node could not take the name or
    /// the graph does not deepen uniformly; either leaves the next
    /// [`finalize_strength_order`](Self::finalize_strength_order) to sort
    /// afresh.
    pub(crate) fn append_child_name_to_all_sites(&mut self, child_path: &Path) {
        let Some(parent_path) = child_path.parent() else {
            return;
        };
        let Some(child_name) = child_path.name() else {
            return;
        };
        for site in &mut self.sites {
            let (path, deepened) = deepen(&site.path, &parent_path, child_path, child_name);
            site.path = path;
            self.finalized &= deepened;
        }
    }

    /// Whether `x` is a namespace ancestor of `y` in the composition tree,
    /// walking `y` up its parent chain and stopping before the local root (C++
    /// `Task::PriorityOrder`'s `isAncestorAndDescendant`). The local root and the
    /// synthetic tree root are never reported as ancestors.
    pub(crate) fn is_ancestor_of(&self, x: NodeId, y: NodeId) -> bool {
        let root = self.local_root();
        let mut cur = y;
        while cur.is_valid() && cur != root && cur != self.shared.root {
            if cur == x {
                return true;
            }
            cur = self.shared.nodes[cur.idx()].parent;
        }
        false
    }

    /// Collects the chain of nodes from `id` up to its tree root, node first
    /// and root last.
    fn chain_to_root(&self, id: NodeId) -> Vec<NodeId> {
        let mut chain = vec![id];
        let mut cur = id;
        while let Some(parent) = self.shared.nodes[cur.idx()].parent.valid() {
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
        let na = &self.shared.nodes[a.idx()];
        let nb = &self.shared.nodes[b.idx()];

        // 1. Arc type: lower discriminant (e.g. Inherit) is stronger.
        if na.arc != nb.arc {
            return na.arc.cmp(&nb.arc);
        }

        // Two specializes are copied under the local root (C++
        // `_PropagateNodeToRoot`), so they sort by the specializes branch of C++
        // `PcpCompareSiblingNodeStrength`, which reads that copy-to-root structure.
        if na.flags.contains(NodeFlags::HAS_SPECIALIZES) && nb.flags.contains(NodeFlags::HAS_SPECIALIZES) {
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
        let oa = na.origin.valid().unwrap_or(a);
        let ob = nb.origin.valid().unwrap_or(b);
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
            let da = self.shared.nodes[a.idx()].namespace_depth;
            let db = self.shared.nodes[b.idx()].namespace_depth;
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
            if !a_authored
                && !b_authored
                && self.same_layer_stack_as_root(a)
                && self.same_layer_stack_as_root(b)
                && let Some(ord) = self.implied_beats_propagated(a, oa, b, ob)
            {
                return ord;
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
        self.shared.nodes[a.idx()]
            .sibling_num_at_origin
            .cmp(&self.shared.nodes[b.idx()].sibling_num_at_origin)
            .then(a.0.cmp(&b.0))
    }

    /// Arc type of a node.
    fn arc_of(&self, id: NodeId) -> ArcType {
        self.shared.nodes[id.idx()].arc
    }

    /// Structural parent, or [`NodeId::INVALID`] for a root node.
    fn parent_of(&self, id: NodeId) -> NodeId {
        self.shared.nodes[id.idx()].parent
    }

    /// Introducing node (C++ `GetOriginNode`), or [`NodeId::INVALID`].
    fn origin_of(&self, id: NodeId) -> NodeId {
        self.shared.nodes[id.idx()].origin
    }

    /// Number of namespace levels a node's site sits below the level at which its
    /// arc was introduced (C++ `PcpNode::GetDepthBelowIntroduction`): the
    /// prim-element count of the *parent* site's path minus this node's
    /// [`namespace_depth`](Node::namespace_depth). A direct arc node has depth 0;
    /// a node reached by extending that arc into a child has 1, and so on.
    ///
    /// The measurement is anchored on the parent because a node's namespace depth
    /// records the parent site's depth at arc introduction, and deepening a graph
    /// to a child appends the same name to every site
    /// ([`append_child_name_to_all_sites`](Self::append_child_name_to_all_sites)).
    /// The parent's path therefore grows by exactly the number of levels the graph
    /// has been deepened since the arc was introduced, whatever namespace depth
    /// the arc's own target happens to sit at. A reference or payload whose target
    /// is shallower or deeper than the prim that authored it — `@ref@</Deep/Target>`
    /// on a root prim, say — is the case that distinguishes this from measuring on
    /// the node's own path.
    ///
    /// A root node has no parent and so is never below its introduction.
    pub(crate) fn depth_below_introduction(&self, id: NodeId) -> u16 {
        let parent = self.parent_of(id);
        if !parent.is_valid() {
            return 0;
        }
        (self.sites[parent.idx()].path.prim_element_count() as u16)
            .saturating_sub(self.shared.nodes[id.idx()].namespace_depth)
    }

    /// Whether a node's arc was introduced above the prim this graph composes
    /// (C++ `PcpNodeRef::IsDueToAncestor`), rather than authored on the prim
    /// itself: its [`depth_below_introduction`](Self::depth_below_introduction) is
    /// non-zero.
    pub(crate) fn is_due_to_ancestor(&self, id: NodeId) -> bool {
        self.depth_below_introduction(id) > 0
    }

    /// A node's path at the level where its arc was introduced (C++
    /// `PcpNode::GetPathAtIntroduction`): the node path with its
    /// [`depth_below_introduction`](Self::depth_below_introduction) trailing
    /// namespace levels stripped.
    pub(crate) fn path_at_introduction(&self, id: NodeId) -> Path {
        path_at_intro_depth(&self.sites[id.idx()].path, self.depth_below_introduction(id))
    }

    /// The path of the site that introduced a node's arc (C++
    /// `PcpNodeRef::GetIntroPath`): its parent's path at the level the arc was
    /// introduced, or the absolute root for a node with no parent.
    pub(crate) fn intro_path(&self, id: NodeId) -> Path {
        let parent = self.parent_of(id);
        if !parent.is_valid() {
            return Path::abs_root();
        }
        path_at_intro_depth(&self.sites[parent.idx()].path, self.depth_below_introduction(id))
    }

    /// Whether two nodes carry the same site: same layer stack and path
    /// (C++ `GetSite() ==`).
    pub(crate) fn same_site(&self, a: NodeId, b: NodeId) -> bool {
        a.is_valid()
            && b.is_valid()
            && self.shared.nodes[a.idx()].layer_stack == self.shared.nodes[b.idx()].layer_stack
            && self.sites[a.idx()].path == self.sites[b.idx()].path
    }

    /// Whether `a`'s layer stack is the local root's layer stack (C++
    /// `GetLayerStack() == GetRootNode().GetLayerStack()`).
    fn same_layer_stack_as_root(&self, a: NodeId) -> bool {
        let root = self.local_root();
        root.is_valid() && self.shared.nodes[a.idx()].layer_stack == self.shared.nodes[root.idx()].layer_stack
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
            self.shared.nodes[instance.idx()].namespace_depth
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
        let depth = self.depth_below_introduction(instance);
        while instance.is_valid()
            && is_class_based_arc(self.arc_of(instance))
            && self.depth_below_introduction(instance) == depth
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
        self.children(root)
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
    /// Each node's children are first sorted by
    /// [`compare_sibling_node_strength`](Self::compare_sibling_node_strength), so
    /// the DFS yields strength order among siblings. Specializes are copied under
    /// the local root (C++ `_PropagateNodeToRoot` / `_EvalImpliedSpecializes`)
    /// and specialize is the weakest arc, so the DFS already trails the
    /// globally-weak band (spec 10.4.1) at the end.
    ///
    /// The comparator reads only arc type, namespace depth, origin chains, and
    /// arena order — never the projection being computed — so it is well-defined
    /// here.
    ///
    /// Returns at once on a graph whose order is current (see the `finalized`
    /// field): one seeded from a finalized graph that gained no node. A graph
    /// that does sort writes the shared half only where the order moved, so
    /// one that sorts to the order it was seeded with goes on sharing.
    pub(crate) fn finalize_strength_order(&mut self) {
        let root = self.shared.root;
        if !root.is_valid() {
            return;
        }
        if self.finalized {
            debug_assert!(self.order_is_current(), "a finalized graph's strength order went stale");
            return;
        }
        let moved = self.unsorted();
        if !moved.is_empty() {
            let nodes = &mut self.data_mut().nodes;
            for (parent, children) in moved {
                nodes[parent.idx()].first_child = children.first().copied().unwrap_or_default();
                nodes[parent.idx()].last_child = children.last().copied().unwrap_or_default();
                for (at, &child) in children.iter().enumerate() {
                    nodes[child.idx()].next_sibling = children.get(at + 1).copied().unwrap_or_default();
                }
            }
        }
        let order = self.walk();
        if order != self.shared.strength_order {
            self.data_mut().strength_order = order;
        }
        self.finalized = !self.shallow_parent;
    }

    /// Marks culled every subtree that contributes no opinion to the prim (C++
    /// `_CullSubtreesWithNoOpinions`), children before their parents, so a
    /// node whose subtree is all culled culls in turn. See
    /// [`can_cull`](Self::can_cull) for the nodes that stay.
    ///
    /// Runs on a finalized graph: the walk reads the sorted child links.
    pub(crate) fn cull_subtrees_without_opinions(&mut self) {
        let root = self.shared.root;
        let local = self.local_root();
        if !root.is_valid() || !local.is_valid() {
            return;
        }
        let root_stack = self.shared.nodes[local.idx()].layer_stack;
        for id in self.walk().into_iter().rev() {
            if id != root && self.can_cull(id, root_stack) {
                self.sites[id.idx()].flags |= NodeFlags::CULLED;
            }
        }
    }

    /// Whether `id` contributes nothing to the prim and can be culled (C++
    /// `_NodeCanBeCulled`). A node stays when it:
    ///
    /// - is a [`Root`](ArcType::Root) node;
    /// - introduces its arc at this prim, so the arc stays discoverable for
    ///   dependencies even with an empty target;
    /// - is a subroot inherit in the root layer stack, which the composed
    ///   scene still holds as a base;
    /// - has a child that was not culled;
    /// - authors a spec it can contribute.
    ///
    /// C++ also keeps a node with symmetry, which this port does not compose,
    /// and one with value clips, which the caller rules out for the whole prim.
    fn can_cull(&self, id: NodeId, root_stack: LayerStackId) -> bool {
        let site = &self.sites[id.idx()];
        if site.flags.contains(NodeFlags::CULLED) {
            return true;
        }
        let data = &self.shared.nodes[id.idx()];
        if data.arc == ArcType::Root || self.depth_below_introduction(id) == 0 {
            return false;
        }
        if data.arc == ArcType::Inherit && data.layer_stack == root_stack {
            // The origin's introduction is what decides: an implied inherit
            // propagated from an ancestral one sits at a subroot path even when
            // the inherit it came from names a root prim.
            let origin = if data.origin == data.parent {
                id
            } else {
                self.origin_root_node(id).0
            };
            if !self.path_at_introduction(origin).is_root_prim() {
                return false;
            }
        }
        if self
            .children(id)
            .any(|child| !self.sites[child.idx()].flags.contains(NodeFlags::CULLED))
        {
            return false;
        }
        !site.has_specs || site.flags.contains(NodeFlags::INERT)
    }

    /// Which nodes [`erase`](Self::erase) may drop, by [`NodeId`]: the culled
    /// ones, less any a live node's origin chain reaches, and the parents of
    /// those (C++ `_ComputeEraseCulledNodeIndexMapping`). Strength ordering
    /// follows origins, so a chain that leads from a live node must stay whole.
    ///
    /// Three kinds of culled node stay too, each with its ancestors:
    ///
    /// - one that authors specs: content a relocation masks is culled where it
    ///   is elided, and the namespace editor reads it to tell a masking
    ///   relocate target;
    /// - one that introduces its arc at this prim: the indexer culls an empty
    ///   arc target as it adds it, where C++ never culls such a node, so the
    ///   arc stays discoverable (an absent payload still counts for the
    ///   instance key);
    /// - the parent of any node that stays: the indexer can compose a node
    ///   under a culled one, where C++ culls only whole subtrees.
    pub(crate) fn erasable(&self) -> Vec<bool> {
        let mut erasable: Vec<bool> = (0..self.len())
            .map(|i| {
                let site = &self.sites[i];
                site.flags.contains(NodeFlags::CULLED)
                    && !site.has_specs
                    && self.depth_below_introduction(NodeId(i as u32)) != 0
            })
            .collect();
        if !erasable.contains(&true) {
            return erasable;
        }
        // A climb stops at a kept ancestor, whose own climb covers the rest.
        for id in 0..self.len() {
            if !erasable[id] {
                let mut parent = self.parent_of(NodeId(id as u32));
                while parent.is_valid() && erasable[parent.idx()] {
                    erasable[parent.idx()] = false;
                    parent = self.parent_of(parent);
                }
            }
        }
        for id in 0..self.len() {
            if self.shared.nodes[id].origin.is_valid() {
                self.keep_origin_chain(NodeId(id as u32), &mut erasable);
            }
        }
        erasable
    }

    /// Clears `erasable` along the origin chain from `id` from the first live
    /// node on, together with the culled parents of each node it clears.
    fn keep_origin_chain(&self, id: NodeId, erasable: &mut [bool]) {
        let mut keep_rest = false;
        let mut at = id;
        loop {
            if !erasable[at.idx()] {
                keep_rest = true;
            } else if keep_rest {
                let mut parent = at;
                while parent.is_valid() && erasable[parent.idx()] {
                    erasable[parent.idx()] = false;
                    // A node kept for its child keeps its own origins too.
                    if parent != at {
                        self.keep_origin_chain(parent, erasable);
                    }
                    parent = self.parent_of(parent);
                }
            }
            let origin = self.origin_of(at);
            if !origin.is_valid() || origin == self.parent_of(at) {
                break;
            }
            at = origin;
        }
    }

    /// Drops the nodes `erase` marks, renumbering the rest in arena order and
    /// rewriting every link and the strength order to the new handles (C++
    /// `PcpPrimIndex_Graph::Finalize`'s culled-node erasure). The graph takes
    /// its own shared half.
    ///
    /// The kept nodes stay sorted: a parent's children keep their relative
    /// order, and the strength order is the old one with the dropped handles
    /// removed. A kept node's parent and origin are kept, which
    /// [`erasable`](Self::erasable) guarantees.
    ///
    /// Returns how many nodes that copied: the kept ones when another graph
    /// held the shared half, 0 otherwise.
    // TODO(perf): a shared half this graph alone holds is still rebuilt into a
    // fresh arena; it could be compacted in place.
    pub(crate) fn erase(&mut self, erase: &[bool]) -> usize {
        let mut remap = vec![NodeId::INVALID; self.len()];
        let mut next = 0u32;
        for (old, &drop) in erase.iter().enumerate() {
            if !drop {
                remap[old] = NodeId(next);
                next += 1;
            }
        }
        let map = |id: NodeId| if id.is_valid() { remap[id.idx()] } else { id };
        let shared = &*self.shared;
        let mut nodes: Vec<NodeData> = Vec::with_capacity(next as usize);
        for (old, data) in shared.nodes.iter().enumerate() {
            if erase[old] {
                continue;
            }
            debug_assert!(
                !data.parent.is_valid() || !erase[data.parent.idx()],
                "a kept node's parent is erased"
            );
            debug_assert!(
                !data.origin.is_valid() || !erase[data.origin.idx()],
                "a kept node's origin is erased"
            );
            let mut data = data.clone();
            data.parent = map(data.parent);
            data.origin = map(data.origin);
            data.first_child = NodeId::INVALID;
            data.last_child = NodeId::INVALID;
            data.next_sibling = NodeId::INVALID;
            nodes.push(data);
        }
        // Relink each kept parent's kept children in their old order.
        for (old, &drop) in erase.iter().enumerate() {
            if drop {
                continue;
            }
            let parent = remap[old];
            let mut prev = NodeId::INVALID;
            for child in self.children(NodeId(old as u32)).filter(|child| !erase[child.idx()]) {
                let child = remap[child.idx()];
                if prev.is_valid() {
                    nodes[prev.idx()].next_sibling = child;
                } else {
                    nodes[parent.idx()].first_child = child;
                }
                nodes[parent.idx()].last_child = child;
                prev = child;
            }
        }
        let strength_order = shared
            .strength_order
            .iter()
            .filter(|id| !erase[id.idx()])
            .map(|&id| remap[id.idx()])
            .collect();
        let root = map(shared.root);
        let copied = if Arc::strong_count(&self.shared) > 1 {
            nodes.len()
        } else {
            0
        };
        let mut kept = erase.iter();
        self.sites.retain(|_| !kept.next().copied().unwrap_or(false));
        self.shared = Arc::new(GraphData {
            nodes,
            strength_order,
            root,
        });
        copied
    }

    /// Gives back the room this graph's vectors hold beyond their nodes, for
    /// a graph that is done growing. Node data another graph also holds is
    /// left as it is.
    pub(crate) fn shrink_to_fit(&mut self) {
        self.sites.shrink_to_fit();
        if let Some(data) = Arc::get_mut(&mut self.shared) {
            data.nodes.shrink_to_fit();
        }
    }

    /// Each parent whose children are out of sibling-strength order, paired
    /// with them in order.
    fn unsorted(&self) -> Vec<(NodeId, Vec<NodeId>)> {
        let by_strength = |a: &NodeId, b: &NodeId| self.compare_sibling_node_strength(*a, *b);
        let mut moved = Vec::new();
        let mut children: Vec<NodeId> = Vec::new();
        let mut sorted: Vec<NodeId> = Vec::new();
        for node in self.nodes() {
            children.clear();
            children.extend(node.children());
            if children.len() < 2 {
                continue;
            }
            sorted.clone_from(&children);
            sorted.sort_by(by_strength);
            if sorted != children {
                moved.push((node.id(), sorted.clone()));
            }
        }
        moved
    }

    /// The pre-order walk of the tree from the root, each node's children in
    /// link order: the strength order once the links are sorted.
    fn walk(&self) -> Vec<NodeId> {
        // Specializes were copied under the local root (C++
        // `_PropagateNodeToRoot`); specialize is the weakest arc, so those
        // copies and their subtrees sort last among the root's children and
        // the walk places the globally-weak band (spec 10.4.1) at the end.
        let mut order = Vec::with_capacity(self.len());
        let mut stack = vec![self.shared.root];
        while let Some(id) = stack.pop() {
            order.push(id);
            extend_reversed(&mut stack, self.children(id));
        }
        order
    }

    /// Whether a sort would leave the child links and the strength order as
    /// they are. The check behind the skip in
    /// [`finalize_strength_order`](Self::finalize_strength_order).
    fn order_is_current(&self) -> bool {
        self.unsorted().is_empty() && self.walk() == self.shared.strength_order
    }
}

/// The path `site` takes when its graph deepens from `parent_path` to
/// `child_path`, whose last element is `child_name`, and whether it took the
/// name. A site at the parent path moves to the child path; any other has the
/// name appended, and keeps its path where it cannot take one.
fn deepen(site: &Path, parent_path: &Path, child_path: &Path, child_name: &str) -> (Path, bool) {
    if site == parent_path {
        return (child_path.clone(), true);
    }
    match site.append_path(child_name) {
        Ok(deeper) => (deeper, true),
        Err(_) => (site.clone(), false),
    }
}

/// Pushes `items` onto `stack` last to first, so the first pops first.
pub(crate) fn extend_reversed<T>(stack: &mut Vec<T>, items: impl Iterator<Item = T>) {
    let first = stack.len();
    stack.extend(items);
    stack[first..].reverse();
}

/// Strips `depth` namespace levels from `path` (C++ `_GetPathAtIntroDepth`).
/// A variant selection is not a namespace level, so the selections above each
/// stripped prim go with it, while those ancestral to the result stay.
fn path_at_intro_depth(path: &Path, depth: u16) -> Path {
    let mut path = path.clone();
    for _ in 0..depth {
        while path.is_variant_selection() {
            match path.parent() {
                Some(parent) => path = parent,
                None => return path,
            }
        }
        match path.parent() {
            Some(parent) => path = parent,
            None => break,
        }
    }
    path
}

#[cfg(test)]
mod tests {
    use super::*;

    impl PrimIndexGraph {
        /// Appends a parentless node and ranks it weakest in the strength
        /// order, or strongest when `strongest`, for a synthetic index that
        /// never runs [`finalize_strength_order`](Self::finalize_strength_order).
        pub(crate) fn push_detached(&mut self, desc: NodeDesc, strongest: bool) -> NodeId {
            debug_assert!(!self.root().is_valid(), "a detached node needs a graph with no root");
            let id = self.add_child(NodeId::INVALID, desc);
            let order = &mut self.data_mut().strength_order;
            let at = if strongest { 0 } else { order.len() };
            order.insert(at, id);
            id
        }
    }

    /// A spec-bearing node at `path` in the tests' one layer stack, mapped by
    /// the identity.
    fn desc(path: &str, arc: ArcType) -> NodeDesc {
        NodeDesc::new(
            LayerStackId::from_raw(1),
            LayerId::from_raw(0),
            Path::new(path).unwrap(),
            arc,
            MapFunction::identity(),
        )
    }

    /// A graph rooted at `local` carrying a single `arc` node onto `target`, as
    /// [`add_child`](PrimIndexGraph::add_child) would build it, then deepened by
    /// each name in `deepen`.
    fn arc_graph(local: &str, arc: ArcType, target: &str, deepen: &[&str]) -> (PrimIndexGraph, NodeId) {
        let stack = LayerStackId::from_raw(1);
        let layer = LayerId::from_raw(0);
        let mut g = PrimIndexGraph::default();
        g.init_root(stack, layer, Path::new(local).unwrap());
        let root = g.add_child(NodeId::INVALID, desc(local, ArcType::Root));
        let id = g.add_child(root, desc(target, arc));
        let mut prim = Path::new(local).unwrap();
        for name in deepen {
            prim = prim.append_path(*name).expect("child path");
            g.append_child_name_to_all_sites(&prim);
        }
        (g, id)
    }

    /// A finalized graph for `/Model` with one node of each arc kind the
    /// strength order treats differently: a reference, an inherit with the
    /// class implied across the reference, and a specialize under the root.
    fn model_graph() -> (PrimIndexGraph, NodeId) {
        let stack = LayerStackId::from_raw(1);
        let layer = LayerId::from_raw(0);
        let mut g = PrimIndexGraph::default();
        g.init_root(stack, layer, Path::new("/Model").unwrap());
        let local = g.add_child(NodeId::INVALID, desc("/Model", ArcType::Root));
        let reference = g.add_child(local, desc("/Ref", ArcType::Reference));
        let class = g.add_child(reference, desc("/Class", ArcType::Inherit));
        let mut implied = desc("/Class", ArcType::Inherit);
        implied.origin = Some(class);
        implied.flags = NodeFlags::IMPLIED_CLASS;
        g.add_child(local, implied);
        let mut special = desc("/Base", ArcType::Specialize);
        special.flags = NodeFlags::HAS_SPECIALIZES;
        g.add_child(local, special);
        g.finalize_strength_order();
        (g, local)
    }

    /// The children of every node and the strength order, for comparing two
    /// graphs' structure.
    fn structure(g: &PrimIndexGraph) -> (Vec<Vec<NodeId>>, Vec<NodeId>) {
        let children = g.nodes().map(|node| node.children().collect()).collect();
        (children, g.strength_order().to_vec())
    }

    /// Deepening every site by one name leaves the strength order current, so
    /// the next finalize has nothing to sort.
    #[test]
    fn append_keeps_order() {
        let (mut g, _) = model_graph();
        g.append_child_name_to_all_sites(&Path::new("/Model/Rig").unwrap());
        assert!(g.finalized, "a uniform append keeps the order");
        assert!(g.order_is_current(), "and a fresh sort agrees with it");
    }

    /// A node that cannot take the child name breaks the uniform append, and
    /// the graph sorts afresh.
    #[test]
    fn failed_append_reorders() {
        let (mut g, local) = model_graph();
        let property = desc("/Ref.attr", ArcType::Reference);
        g.add_child(local, property);
        g.finalize_strength_order();
        g.append_child_name_to_all_sites(&Path::new("/Model/Rig").unwrap());
        assert!(!g.finalized);
    }

    /// A node introduced deeper than its parent sits does not deepen in step
    /// with the rest, so an append leaves the order to be sorted afresh.
    #[test]
    fn shallow_parent_reorders() {
        let (mut g, local) = model_graph();
        let mut deep = desc("/Deep", ArcType::Reference);
        deep.namespace_depth = Some(5);
        g.add_child(local, deep);
        g.finalize_strength_order();
        assert!(!g.finalized, "the order would not survive a deepening");
        assert!(g.order_is_current());
    }

    /// Inserting a node leaves the order to be sorted afresh.
    #[test]
    fn insert_clears_order() {
        let (mut g, local) = model_graph();
        assert!(g.finalized);
        g.add_child(local, desc("/Other", ArcType::Reference));
        assert!(!g.finalized);
    }

    /// A child's own path, spec flag, restriction depth and per-prim flags are
    /// written without copying the data it shares, and leave its parent and
    /// its sibling as they were.
    #[test]
    fn site_writes_keep_sharing() {
        let (parent, local) = model_graph();
        let sibling = parent.clone();
        let mut child = parent.seed_child(&Path::new("/Model/Rig").unwrap());
        child.set_has_specs(local, false);
        child.set_restriction_depth(local, 3);
        child.mark(local, NodeFlags::INERT | NodeFlags::CULLED);
        child.finalize_strength_order();

        assert!(child.shares_data_with(&parent));
        assert_eq!(child.node(local).path().as_str(), "/Model/Rig");
        assert!(child.node(local).is_inert() && child.node(local).is_culled());
        for other in [&parent, &sibling] {
            let node = other.node(local);
            assert_eq!(node.path().as_str(), "/Model");
            assert!(node.has_specs());
            assert_eq!(node.restriction_depth(), 0);
            assert!(!node.is_inert() && !node.is_culled());
        }
    }

    /// Inserting a node gives the child its own data. The parent keeps its
    /// nodes, its sibling order and its strength order, also once the child
    /// has sorted a stronger arc in front of the ones it took over.
    #[test]
    fn insert_detaches() {
        let (parent, local) = model_graph();
        let before = structure(&parent);
        let mut child = parent.seed_child(&Path::new("/Model/Rig").unwrap());
        let added = child.add_child(local, desc("/Local", ArcType::Inherit));
        child.finalize_strength_order();

        assert!(!child.shares_data_with(&parent));
        assert_eq!(structure(&parent), before);
        assert_eq!(parent.len() + 1, child.len());
        assert!(child.strength_order().contains(&added));
    }

    /// A child whose deepening changes the order, with no node added, sorts
    /// its own copy. The parent keeps its sibling order and strength order.
    #[test]
    fn reorder_detaches() {
        let mut parent = PrimIndexGraph::default();
        parent.init_root(
            LayerStackId::from_raw(1),
            LayerId::from_raw(0),
            Path::new("/Model").unwrap(),
        );
        let mut root = desc("/Model", ArcType::Root);
        root.namespace_depth = Some(0);
        let local = parent.add_child(NodeId::INVALID, root);
        let class = parent.add_child(local, desc("/Class", ArcType::Inherit));
        let other = parent.add_child(local, desc("/Other", ArcType::Inherit));
        // An implied class introduced deeper than its parent sits: it starts
        // level with `class`, and falls a level behind once the graph deepens.
        let mut implied = desc("/Other", ArcType::Inherit);
        implied.origin = Some(other);
        implied.namespace_depth = Some(5);
        let implied = parent.add_child(class, implied);
        let specialize = |origin| {
            let mut special = desc("/Base", ArcType::Specialize);
            special.origin = Some(origin);
            special.flags = NodeFlags::HAS_SPECIALIZES;
            special
        };
        let far = parent.add_child(local, specialize(implied));
        let near = parent.add_child(local, specialize(other));
        parent.finalize_strength_order();
        let before = structure(&parent);
        let rank = |g: &PrimIndexGraph, id| g.strength_order().iter().position(|&n| n == id);
        assert!(rank(&parent, far) < rank(&parent, near));

        let mut child = parent.seed_child(&Path::new("/Model/Rig").unwrap());
        assert!(child.shares_data_with(&parent) && !child.finalized);
        child.finalize_strength_order();

        assert!(
            rank(&child, near) < rank(&child, far),
            "the deeper graph ranks them the other way"
        );
        assert!(!child.shares_data_with(&parent));
        assert_eq!(structure(&parent), before);
        assert_eq!(parent.len(), child.len());
    }

    /// Rewriting maps gives a graph its own data and leaves the maps of the
    /// graph it was taken from alone, as a prototype needs of its canonical
    /// instance. The copy keeps the sibling order and the strength order.
    #[test]
    fn rebase_detaches() {
        let stack = LayerStackId::from_raw(1);
        let layer = LayerId::from_raw(0);
        let path = |s: &str| Path::new(s).unwrap();
        let mut canonical = PrimIndexGraph::default();
        canonical.init_root(stack, layer, path("/Inst"));
        let local = canonical.add_child(
            NodeId::INVALID,
            NodeDesc::new(stack, layer, path("/Inst"), ArcType::Root, MapFunction::identity()),
        );
        let map = MapFunction::from_pair_identity(path("/Ref"), path("/Inst"));
        let reference = canonical.add_child(
            local,
            NodeDesc::new(stack, layer, path("/Ref"), ArcType::Reference, map.clone()),
        );
        // An inherit sorts in front of the reference inserted before it.
        let class = canonical.add_child(local, desc("/Class", ArcType::Inherit));
        canonical.finalize_strength_order();
        let before = structure(&canonical);
        assert_eq!(canonical.children(local).collect::<Vec<_>>(), [class, reference]);

        let mut prototype = canonical.clone();
        prototype.rebase_maps(|map| map.rebase_target(&path("/Inst"), &path("/__Prototype_1")));

        assert!(!prototype.shares_data_with(&canonical));
        assert_eq!(structure(&prototype), before);
        assert_eq!(structure(&canonical), before);
        assert!(prototype.order_is_current());
        assert_eq!(canonical.node(reference).map_to_root(), &map);
        assert_ne!(prototype.node(reference).map_to_root(), &map);
        assert!(prototype.finalized, "the maps do not enter the strength order");
    }

    #[test]
    fn introduction_depth_and_path() {
        // An arc introduced at the prim's own level: depth 0, path unchanged.
        let (g, id) = arc_graph("/Model", ArcType::Inherit, "/_class_Model", &[]);
        assert_eq!(g.depth_below_introduction(id), 0);
        assert!(!g.is_due_to_ancestor(id));
        assert_eq!(g.path_at_introduction(id), Path::new("/_class_Model").unwrap());

        // The same arc deepened two levels into a descendant: depth 2, and the
        // introduction path strips the two trailing elements.
        let (g, id) = arc_graph("/Model", ArcType::Inherit, "/_class_Model", &["Rig", "Anim"]);
        assert_eq!(g.depth_below_introduction(id), 2);
        assert!(g.is_due_to_ancestor(id));
        assert_eq!(g.path_at_introduction(id), Path::new("/_class_Model").unwrap());
    }

    /// The depth is measured on the introducing parent's site, so an arc whose
    /// target sits at a different namespace depth than the prim that authored it
    /// still reports the number of levels the graph has been deepened.
    #[test]
    fn introduction_depth_uneven_target() {
        // A reference from a depth-2 prim onto a depth-1 target.
        let (g, id) = arc_graph("/World/G", ArcType::Reference, "/Ref", &[]);
        assert_eq!(g.depth_below_introduction(id), 0);
        assert_eq!(g.path_at_introduction(id), Path::new("/Ref").unwrap());

        let (g, id) = arc_graph("/World/G", ArcType::Reference, "/Ref", &["A"]);
        assert_eq!(g.depth_below_introduction(id), 1);
        assert_eq!(g.path_at_introduction(id), Path::new("/Ref").unwrap());

        // And the reverse: a depth-1 prim referencing a depth-2 target.
        let (g, id) = arc_graph("/World", ArcType::Reference, "/Ref/Inner", &["A"]);
        assert_eq!(g.depth_below_introduction(id), 1);
        assert_eq!(g.path_at_introduction(id), Path::new("/Ref/Inner").unwrap());
    }
}
