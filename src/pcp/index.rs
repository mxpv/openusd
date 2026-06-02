//! Per-prim composition index (`PcpPrimIndex` equivalent).
//!
//! A [`PrimIndex`] records the strength-ordered list of layer specs that
//! contribute opinions to a single composed prim. See the
//! [module-level docs](super) for the full composition overview.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use anyhow::Result;
use bitflags::bitflags;

use crate::ar::Resolver;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{self, AbstractData, LayerOffset, ListOp, Path, Payload, PayloadListOp, Reference, Specifier, Value};

use super::clip;
use super::mapping::MapFunction;
use super::{Error, LayerStack, VariantFallbackMap};

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

/// Stable handle to a [`Node`] within a [`PrimIndex`]'s composition graph
/// (C++ `PcpNodeRef`).
///
/// A handle stays valid for the life of the index: the node arena is only
/// ever appended to, never reordered, so a `NodeId` is safe to store in
/// another node's `parent`/`children`/`origin`. The sentinel value
/// [`INVALID`](Self::INVALID) represents the absence of a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(u32);

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
/// place in the composition tree; access them through [`PrimIndex`].
#[derive(Debug, Clone)]
pub struct Node {
    /// The layer stack contributing opinions at this site (C++
    /// `PcpNode::GetLayerStack`): each member is a `(layer index, sublayer
    /// offset)` pair, strongest sublayer first. A member's sublayer offset is
    /// composed atop `map_to_root`'s arc offset during value resolution (see
    /// [`layers`](Self::layers)).
    layer_stack: Vec<(usize, LayerOffset)>,
    /// The path within that layer (may differ from composed path due to remapping).
    pub path: Path,
    /// The composition arc that introduced this node.
    pub arc: ArcType,
    /// Maps paths from this node's namespace to its parent's namespace.
    pub map_to_parent: MapFunction,
    /// Maps paths from this node's namespace directly to the root namespace.
    /// Computed as `parent.map_to_root.compose(self.map_to_parent)`.
    pub map_to_root: MapFunction,
    /// Structural parent in the composition tree, or `None` for a root node.
    parent: Option<NodeId>,
    /// Structural children, in the order they were introduced (strength order
    /// among siblings).
    children: Vec<NodeId>,
    /// Node that introduced this arc (C++ `GetOriginNode`): the parent for a
    /// direct arc (set at [`add_child`](PrimIndexGraph::add_child) time), or
    /// the propagated-from node for an implied class or graft. `None` only for
    /// the synthetic root, which has no parent.
    origin: Option<NodeId>,
    /// Namespace depth at which the introducing arc was authored. Used by
    /// implied inherits/specializes that propagate toward the root.
    namespace_depth: u16,
    /// Position of this node's prim in its specializes chain: 0 for a directly
    /// specialized class, 1 for the class it specializes, and so on. A specialize
    /// source is weaker than its target (spec 10.4.1), so a lower depth is
    /// stronger. Set during [`finalize_strength_order`](PrimIndexGraph::finalize_strength_order);
    /// meaningful only for specialize-introduced nodes.
    specialize_chain_depth: u16,
    /// Composition state bits (see [`NodeFlags`]).
    flags: NodeFlags,
}

impl Node {
    /// Builds a standalone node with no structural links.
    ///
    /// Callers that append through [`PrimIndexGraph::add_child`] have their
    /// `parent`/`children` populated by the builder; the relocate inserts and
    /// grafts set the links explicitly afterward.
    pub(crate) fn new(
        layer_index: usize,
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
            // A node lists one layer until the per-site model folds a whole
            // sublayer stack into it; that lone layer's sublayer offset is
            // already baked into `map_to_root`, so its entry offset is identity.
            layer_stack: vec![(layer_index, LayerOffset::IDENTITY)],
            path,
            arc,
            map_to_parent,
            map_to_root,
            parent: None,
            children: Vec::new(),
            origin: None,
            namespace_depth: 0,
            specialize_chain_depth: 0,
            flags,
        }
    }

    /// Builds a standalone node spanning a whole sublayer stack: `layer_stack`
    /// lists every contributing `(layer index, sublayer offset)` member,
    /// strongest first. Like [`new`](Self::new) but for a per-site node not
    /// appended through [`PrimIndexGraph::add_site_child`] (the relocate
    /// inserts). Panics on an empty `layer_stack`.
    pub(crate) fn new_site(
        layer_stack: Vec<(usize, LayerOffset)>,
        path: Path,
        arc: ArcType,
        map_to_parent: MapFunction,
        map_to_root: MapFunction,
        introduced_by_specialize: bool,
    ) -> Self {
        let mut node = Self::new(
            layer_stack[0].0,
            path,
            arc,
            map_to_parent,
            map_to_root,
            introduced_by_specialize,
        );
        node.layer_stack = layer_stack;
        node
    }

    /// Index of the strongest layer contributing at this site. A representative
    /// for callers that key on a single layer (dependencies, dumps); value
    /// resolution iterates [`layers`](Self::layers) instead.
    pub fn layer_index(&self) -> usize {
        self.layer_stack[0].0
    }

    /// The site's contributing layers as stored: `(layer index, sublayer
    /// offset)` members, strongest first. Used when grafting a node into
    /// another index, which copies the stack verbatim. Value resolution should
    /// use [`layers`](Self::layers) instead, which folds in the arc offset.
    pub(crate) fn layer_stack(&self) -> &[(usize, LayerOffset)] {
        &self.layer_stack
    }

    /// Iterates the site's contributing layers strongest first, each paired
    /// with its effective time offset to the root namespace: `map_to_root`'s
    /// arc offset with the member's sublayer offset composed on top. Value
    /// resolution reads opinions through this iterator so one per-site node can
    /// fold every sublayer.
    pub fn layers(&self) -> impl Iterator<Item = (usize, LayerOffset)> + '_ {
        let arc_offset = self.map_to_root.time_offset();
        self.layer_stack
            .iter()
            .map(move |&(li, sub)| (li, arc_offset.concatenate(&sub)))
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

    /// Composition state bits.
    pub fn flags(&self) -> NodeFlags {
        self.flags
    }

    /// True when this node contributes no opinions and exists only to give the
    /// composition graph structure (the synthetic tree root).
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
/// the arena slice for the builder's structural lookups.
///
/// `root` is the synthetic, inert tree root created by
/// [`init_root`](Self::init_root): every otherwise-parentless node attaches
/// under it, so the graph is a single rooted tree rather than a forest. It is
/// [`NodeId::INVALID`] for the hand-built test graphs that never call
/// `init_root`.
#[derive(Debug, Clone, Default)]
pub(crate) struct PrimIndexGraph {
    nodes: Vec<Node>,
    strength_order: Vec<NodeId>,
    root: NodeId,
}

impl PrimIndexGraph {
    fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the prim's local root node — the `Root`-arc child of the
    /// synthetic inert root, carrying the prim's own (sublayer) opinions. An
    /// implied class anchors here so it ranks among the prim's direct arcs (C++
    /// `_AddClassBasedArc` adds it under the node owning the prim), regardless
    /// of how deep the arc that implied it sits or whether an ancestral arc was
    /// grafted as a separate root-level sibling. [`NodeId::INVALID`] when the
    /// prim has no local opinion (composed purely through arcs).
    fn local_root(&self) -> NodeId {
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
    fn init_root(&mut self, path: Path) -> NodeId {
        debug_assert!(self.nodes.is_empty(), "synthetic root must be the first node");
        let id = NodeId(self.nodes.len() as u32);
        let depth = path.prim_element_count() as u16;
        let mut node = Node::new(
            0,
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
    fn add_child(
        &mut self,
        parent: NodeId,
        layer_index: usize,
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
            layer_index,
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

    /// Like [`add_child`](Self::add_child) but for a site spanning several
    /// sublayers: `layer_stack` lists every contributing `(layer index,
    /// sublayer offset)`, strongest sublayer first. The first member is the
    /// site representative; the remaining members are folded into the node's
    /// layer stack so value resolution reads each sublayer in turn. Panics on
    /// an empty `layer_stack`.
    fn add_site_child(
        &mut self,
        parent: NodeId,
        layer_stack: Vec<(usize, LayerOffset)>,
        path: Path,
        arc: ArcType,
        map_to_parent: MapFunction,
        introduced_by_specialize: bool,
    ) -> NodeId {
        let id = self.add_child(
            parent,
            layer_stack[0].0,
            path,
            arc,
            map_to_parent,
            introduced_by_specialize,
        );
        self.nodes[id.idx()].layer_stack = layer_stack;
        id
    }

    /// Tags a node as introduced by implied-class propagation, recording the
    /// originating arc node. Pure metadata: it does not affect resolution.
    fn mark_implied(&mut self, id: NodeId, origin: NodeId) {
        let node = &mut self.nodes[id.idx()];
        node.flags |= NodeFlags::IMPLIED_CLASS;
        if origin.is_valid() {
            node.origin = Some(origin);
        }
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
    /// stronger); for two specializes, specializes-chain depth (a source is
    /// weaker than its target); namespace depth (deeper stronger, skipped for
    /// specializes); origin strength (the node whose origin is reached first in
    /// a strong-to-weak walk); finally sibling number — the earlier-created
    /// node (lower [`NodeId`]) is stronger.
    fn compare_sibling_node_strength(&self, a: NodeId, b: NodeId) -> Ordering {
        let na = &self.nodes[a.idx()];
        let nb = &self.nodes[b.idx()];

        // 1. Arc type: lower discriminant (e.g. Inherit) is stronger.
        if na.arc != nb.arc {
            return na.arc.cmp(&nb.arc);
        }

        let both_specialize = na.introduced_by_specialize() && nb.introduced_by_specialize();

        // 2a. Specializes-chain depth: a class is stronger than the class it
        // specializes (C++ `_OriginsAreNestedArcs`: the source of a specializes
        // arc is weaker than its target regardless of namespace depth, spec
        // 10.4.1). Lower depth is stronger.
        if both_specialize && na.specialize_chain_depth != nb.specialize_chain_depth {
            return na.specialize_chain_depth.cmp(&nb.specialize_chain_depth);
        }

        // 2b. Namespace depth: a deeper arc-introduction site is stronger. C++
        // skips this for specializes whose origins are nested arcs (handled by
        // the chain-depth key above), so it is skipped for two specializes.
        if !both_specialize && na.namespace_depth != nb.namespace_depth {
            return nb.namespace_depth.cmp(&na.namespace_depth);
        }

        // 3. Origin strength, only when the two origins differ. `origin` is
        // total (C++ `GetOriginNode`): the node an implied arc was propagated
        // from, or the parent for a directly-authored arc, so two direct
        // siblings share an origin and fall through to the tiebreak below. The
        // synthetic root is the sole node without an origin; it stands in for
        // itself. Comparing origins recurses only over strictly-older nodes (an
        // origin is always created before the node carrying it), so the
        // recursion is well-founded — except when both nodes default to
        // themselves (no origin authored): recursing on the same `(a, b)` would
        // not progress, so skip straight to the sibling-number tiebreak.
        let oa = na.origin.unwrap_or(a);
        let ob = nb.origin.unwrap_or(b);
        if oa != ob && (oa != a || ob != b) {
            let ord = self.compare_node_strength(oa, ob);
            if ord != Ordering::Equal {
                return ord;
            }
        }

        // 4. Sibling number: the earlier-created node (lower arena index) was
        // introduced first and is stronger.
        a.0.cmp(&b.0)
    }

    /// Compares two arbitrary nodes in the same tree by strength, porting C++
    /// `PcpCompareNodeStrength`. Returns [`Ordering::Less`] when `a` is stronger.
    ///
    /// Walks each node's chain to the shared root to find their lowest common
    /// ancestor. When one node is an ancestor of the other, the ancestor is
    /// stronger; otherwise the two diverging children are siblings, compared by
    /// [`compare_sibling_node_strength`](Self::compare_sibling_node_strength).
    fn compare_node_strength(&self, a: NodeId, b: NodeId) -> Ordering {
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

    /// Rebuilds the strength-order projection: a pre-order DFS of the tree for
    /// non-specialize nodes, followed by the globally-weak specialize band
    /// (spec 10.4.1). The result runs strongest to weakest; reversing it gives
    /// weak-to-strong.
    ///
    /// Each node's `children` are first sorted by
    /// [`compare_sibling_node_strength`](Self::compare_sibling_node_strength),
    /// so the DFS yields strength order among siblings. The specialize band is
    /// then ordered by the same comparator over the whole band: in C++ the
    /// specializes nodes are copied to the root and ordered there as siblings
    /// (`_EvalImpliedSpecializes`); ordering them directly with the sibling
    /// comparator reproduces that without mutating the tree, so the nested
    /// structure the grafts depend on is preserved.
    ///
    /// The comparator reads only arc type, specializes-chain depth, namespace
    /// depth, origin chains, and arena order — never the projection being
    /// computed — so it is well-defined here.
    fn finalize_strength_order(&mut self) {
        if !self.root.is_valid() {
            return;
        }

        self.compute_specialize_chain_depths();

        // Order every node's children by sibling strength. `children` is taken
        // out so the comparator can borrow the arena immutably during the sort.
        for i in 0..self.nodes.len() {
            let mut children = std::mem::take(&mut self.nodes[i].children);
            children.sort_by(|&a, &b| self.compare_sibling_node_strength(a, b));
            self.nodes[i].children = children;
        }

        // Pre-order DFS from the root: visit a node, then its children in
        // strength order. Pushing children reversed makes the strongest pop
        // first.
        let mut dfs = Vec::with_capacity(self.nodes.len());
        let mut stack = vec![self.root];
        while let Some(id) = stack.pop() {
            dfs.push(id);
            for &child in self.nodes[id.idx()].children.iter().rev() {
                stack.push(child);
            }
        }

        // Specializes are globally weaker than every other opinion (spec
        // 10.4.1). Keep the non-specialize nodes in DFS order, then append the
        // specialize band ordered among itself by the sibling comparator (which
        // treats the band as siblings at the root, mirroring copy-to-root).
        let (mut order, mut specials): (Vec<NodeId>, Vec<NodeId>) = dfs
            .into_iter()
            .partition(|id| !self.nodes[id.idx()].introduced_by_specialize());
        specials.sort_by(|&a, &b| self.compare_sibling_node_strength(a, b));
        order.append(&mut specials);
        self.strength_order = order;
    }

    /// Records, on every specialize-introduced node, the depth of its prim in
    /// the specializes chain: the number of specialize ancestors of the deepest
    /// node at that prim's path. A directly specialized class is depth 0, the
    /// class it specializes is depth 1, and so on, so a lower depth sorts
    /// stronger (a specializes source is weaker than its target, spec 10.4.1).
    ///
    /// The per-path maximum recovers the chain position even for the implied
    /// copies a class brings in across references, which hang flat rather than
    /// nested under the class they specialize.
    fn compute_specialize_chain_depths(&mut self) {
        let mut depth_by_path: HashMap<Path, u16> = HashMap::new();
        for node in &self.nodes {
            if !node.introduced_by_specialize() {
                continue;
            }
            let mut depth = 0u16;
            let mut parent = node.parent;
            while let Some(pid) = parent {
                let pnode = &self.nodes[pid.idx()];
                if pnode.introduced_by_specialize() {
                    depth += 1;
                }
                parent = pnode.parent;
            }
            depth_by_path
                .entry(node.path.clone())
                .and_modify(|d| *d = (*d).max(depth))
                .or_insert(depth);
        }
        for node in &mut self.nodes {
            if node.introduced_by_specialize() {
                node.specialize_chain_depth = depth_by_path.get(&node.path).copied().unwrap_or(0);
            }
        }
    }
}

impl std::ops::Deref for PrimIndexGraph {
    /// Dereferences to the node arena in insertion (structural) order. The
    /// builder relies on this for positional lookups while composing; strength
    /// order is reached through [`PrimIndex::nodes`].
    type Target = [Node];
    fn deref(&self) -> &[Node] {
        &self.nodes
    }
}

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
}

/// A single authored opinion surfaced by [`PrimIndex::opinions`].
///
/// One opinion is yielded per contributing layer of a node's layer stack, so a
/// per-site node fans out into one opinion per sublayer that authored the
/// field.
struct Opinion<'a> {
    /// The contributing node, strongest-to-weakest in the walk.
    node: &'a Node,
    /// Index of the contributing layer within the node's layer stack.
    layer: usize,
    /// The path queried in the contributing layer (the node path with the
    /// property suffix applied).
    query_path: Cow<'a, Path>,
    /// The authored value at `query_path`.
    value: Cow<'a, Value>,
    /// Effective time offset of the contributing layer to the root namespace
    /// (the node's arc offset with the layer's sublayer offset composed on
    /// top). Used to retime time samples and clip schedules.
    offset: LayerOffset,
}

impl PrimIndex {
    /// Returns `true` if no layers contribute opinions for this prim.
    ///
    /// A prim with no opinions still owns the synthetic, inert tree root, and
    /// may own culled arc nodes kept only for structure, so emptiness is the
    /// absence of any node that contributes to value resolution.
    pub fn is_empty(&self) -> bool {
        !self.graph.iter().any(|node| !node.is_inert() && !node.is_culled())
    }

    /// Returns `true` if any node that contributes opinions was introduced by a
    /// composition arc. Culled arc nodes (empty targets) do not count: they add
    /// no shared content, so a prim that only references an empty target is not
    /// treated as composed for instancing.
    pub(crate) fn has_composition_arc(&self) -> bool {
        self.arena()
            .iter()
            .any(|node| node.arc != ArcType::Root && !node.is_culled())
    }

    /// Iterates the nodes in strength order (strongest first).
    ///
    /// This is the order value resolution uses: it walks the strength-order
    /// projection, so specializes appear last (spec 10.4.1) regardless of where
    /// they sit in the arena. Inert and culled nodes are skipped — they
    /// contribute no opinions. The iterator is cheap and re-creatable; call it
    /// again for another pass rather than collecting.
    pub fn nodes(&self) -> impl Iterator<Item = &Node> + Clone + '_ {
        self.all_nodes().filter(|node| !node.is_culled())
    }

    /// Iterates every retained node in strength order, including culled arc
    /// nodes (an arc whose target authors no spec). Skips only the inert
    /// synthetic root. Used for composition introspection and change tracking,
    /// where the full arc structure matters even where it contributes no
    /// opinions; value resolution uses [`nodes`](Self::nodes) instead.
    pub fn all_nodes(&self) -> impl Iterator<Item = &Node> + Clone + '_ {
        let nodes = &self.graph.nodes;
        self.graph
            .strength_order
            .iter()
            .map(move |id| &nodes[id.idx()])
            .filter(|node| !node.is_inert())
    }

    /// Iterates `(handle, node)` pairs in strength order. Used by the subtree
    /// graft, which needs each node's [`NodeId`] to rebuild parent links. The
    /// inert synthetic root is skipped, so a grafted target's real roots become
    /// orphans that re-parent under the destination's own root.
    pub(crate) fn nodes_with_ids(&self) -> impl Iterator<Item = (NodeId, &Node)> + '_ {
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
                "{:indent$}{:?} [{}] {} #{}",
                "",
                node.arc,
                node.layer_index(),
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
        self.graph.nodes.push(node);
        self.graph.strength_order.push(id);
    }

    /// Inserts a standalone relocate node at the correct LIVERPS strength
    /// position.
    ///
    /// The node is tagged [`RELOCATE_SOURCE`](NodeFlags::RELOCATE_SOURCE),
    /// appended to the arena (keeping every handle stable), and its handle is
    /// spliced into the strength projection before the first node weaker than
    /// `Relocate` (i.e. `Reference`, `Payload`, or `Specialize`).
    pub(crate) fn insert_relocate_node(&mut self, mut node: Node) {
        node.flags |= NodeFlags::RELOCATE_SOURCE;
        node.namespace_depth = node.path.prim_element_count() as u16;
        let id = NodeId(self.graph.nodes.len() as u32);
        // Attach under the synthetic root so the graph stays a single tree.
        // Composing through the identity-mapped root leaves `map_to_root` equal
        // to the node's own `map_to_parent`.
        if self.graph.root.is_valid() {
            let root = self.graph.root;
            node.map_to_root = self.graph.nodes[root.idx()].map_to_root.compose(&node.map_to_parent);
            node.parent = Some(root);
            node.origin = Some(root);
            self.graph.nodes[root.idx()].children.push(id);
        }
        self.graph.nodes.push(node);
        self.splice_relocate(id);
    }

    /// Grafts a relocate node under `parent` (or as a root when `None`),
    /// preserving the source subtree's structure.
    ///
    /// `map_to_parent` translates the node's namespace to its grafted parent
    /// (or straight to the composed path for a root); `map_to_root` composes
    /// down the grafted chain. The handle is spliced into the relocate strength
    /// band exactly like [`insert_relocate_node`](Self::insert_relocate_node).
    pub(crate) fn graft_relocate_node(
        &mut self,
        parent: Option<NodeId>,
        layer_stack: Vec<(usize, LayerOffset)>,
        path: Path,
        map_to_parent: MapFunction,
    ) -> NodeId {
        // A `None` parent is a root site: re-parent under the synthetic root
        // for structure while taking the namespace depth from the node's own
        // path (the conceptual parent site).
        let struct_parent = parent.or_else(|| self.graph.root.is_valid().then_some(self.graph.root));
        let map_to_root = match struct_parent {
            Some(p) => self.graph.nodes[p.idx()].map_to_root.compose(&map_to_parent),
            None => map_to_parent.clone(),
        };
        let namespace_depth = match parent {
            Some(p) => self.graph.nodes[p.idx()].path.prim_element_count(),
            None => path.prim_element_count(),
        } as u16;
        let id = NodeId(self.graph.nodes.len() as u32);
        let mut node = Node::new_site(layer_stack, path, ArcType::Relocate, map_to_parent, map_to_root, false);
        node.flags |= NodeFlags::RELOCATE_SOURCE;
        node.namespace_depth = namespace_depth;
        if let Some(p) = struct_parent {
            node.parent = Some(p);
            node.origin = Some(p);
            self.graph.nodes[p.idx()].children.push(id);
        }
        self.graph.nodes.push(node);
        self.splice_relocate(id);
        id
    }

    /// Splices a just-appended relocate node's handle into the strength
    /// projection, keeping the relocate band ordered by node strength.
    ///
    /// Relocate nodes sit ahead of the first node weaker than `Relocate`
    /// (`Reference` / `Payload` / `Specialize`). Within that band the handle is
    /// placed by [`compare_node_strength`](PrimIndexGraph::compare_node_strength)
    /// so multiple relocates resolve in strength order rather than the order
    /// they were grafted (a parent relocate before its children, a stronger
    /// relocate before a weaker sibling).
    fn splice_relocate(&mut self, id: NodeId) {
        let band_end = self
            .graph
            .strength_order
            .iter()
            .position(|sid| self.graph.nodes[sid.idx()].arc > ArcType::Relocate)
            .unwrap_or(self.graph.strength_order.len());
        let mut pos = band_end;
        for i in 0..band_end {
            let sid = self.graph.strength_order[i];
            if self.graph.nodes[sid.idx()].arc == ArcType::Relocate
                && self.graph.compare_node_strength(id, sid) == Ordering::Less
            {
                pos = i;
                break;
            }
        }
        self.graph.strength_order.insert(pos, id);
    }

    /// Builds a prim index using composition context from the parent prim.
    ///
    /// The context carries variant selections and arc mappings from ancestors,
    /// enabling single-pass composition without post-processing.
    pub(crate) fn build_with_context(path: &Path, stack: &LayerStack, ctx: &CompositionContext) -> Result<Self, Error> {
        Self::build_with_cache(path, stack, ctx, &HashMap::new())
    }

    /// Like [`build_with_context`](Self::build_with_context) but with access to
    /// previously-composed prim indices. Cached indices are checked before
    /// building from scratch, ensuring inherit/specialize targets use the
    /// fully-composed result (including ancestor-propagated specs).
    pub(crate) fn build_with_cache(
        path: &Path,
        stack: &LayerStack,
        ctx: &CompositionContext,
        cached_indices: &HashMap<Path, PrimIndex>,
    ) -> Result<Self, Error> {
        Self::build_with_cache_in(path, stack, ctx, cached_indices, &stack.root_layer_stack(), true)
    }

    /// Builds a prim index whose root `L` site scans the given `ambient` layer
    /// stack rather than the stage's root layer stack.
    ///
    /// `ambient` is the layer stack the prim is composed in: the root layer
    /// stack for a stage prim, or a referenced asset's sublayer stack for an
    /// arc target reached within that reference. `ambient_is_root` records
    /// whether `ambient` is the stage's root layer stack, which is the only
    /// case where the shared `cached_indices` (keyed by stage path) apply.
    pub(crate) fn build_with_cache_in(
        path: &Path,
        stack: &LayerStack,
        ctx: &CompositionContext,
        cached_indices: &HashMap<Path, PrimIndex>,
        ambient: &[(usize, LayerOffset)],
        ambient_is_root: bool,
    ) -> Result<Self, Error> {
        if ambient_is_root {
            if let Some(cached) = cached_indices.get(path) {
                return Ok(cached.clone());
            }
        }
        let mut builder = IndexBuilder::new(stack, ctx, cached_indices, ambient.to_vec(), ambient_is_root);
        builder.build(path)?;
        Ok(PrimIndex { graph: builder.output })
    }

    /// Returns the composition context derived from this prim's index.
    ///
    /// Child prims use this context to inherit ancestor arc mappings and
    /// variant selections without recomputing them.
    pub(crate) fn context_for_children(
        &self,
        stack: &LayerStack,
        parent_ctx: &CompositionContext,
    ) -> CompositionContext {
        // Gather variant selections from this prim's nodes; ancestor selections
        // outrank this prim's local fallbacks.
        let selections = resolve_variant_selections_in(
            self.nodes(),
            &stack.layers,
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
        // Record each non-Root node and which arc it nested under (its tree
        // parent in this prim's graph). Strength order places a parent before
        // its child, so a node's parent is already in `node_to_idx` when the
        // node is reached. A parent that is this prim's Root node (not recorded)
        // leaves `parent` None — the arc sits directly on the prim. Cross-prim
        // nesting is not threaded here: an arc inherited from a grandparent
        // stays flat (its own level already recorded its nesting).
        let base = ancestor_arcs.len();
        let mut node_to_idx: HashMap<NodeId, usize> = HashMap::new();
        for (id, node) in self.nodes_with_ids() {
            if node.arc == ArcType::Root {
                continue;
            }
            let parent = node.parent().and_then(|p| node_to_idx.get(&p).copied());
            node_to_idx.insert(id, base + node_to_idx.len());
            ancestor_arcs.push(AncestorArc {
                map: node.map_to_root.clone(),
                map_to_parent: node.map_to_parent.clone(),
                layer_stack: node.layer_stack().to_vec(),
                arc: node.arc,
                parent,
            });
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
            within_instance: parent_ctx.within_instance,
            // Carried forward; the cache appends this prim's own denied targets.
            denied_prefixes: parent_ctx.denied_prefixes.clone(),
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

    /// Resolves a field across the composition graph.
    ///
    /// Most fields use strongest-opinion-wins (spec 12.2). Four field classes
    /// have special rules:
    ///
    /// - `specifier`: precedence by `def`/`class`/`over` with direct-inherit handling
    /// - `variability`: weakest authored opinion wins
    /// - `custom`: any-true (logical OR across all authored opinions)
    /// - dictionaries: recursive merge of stronger and weaker dictionary opinions
    ///
    /// When `prop_suffix` is `None`, queries use the node's path directly (zero-copy).
    /// When `Some`, appends the suffix to form a property path for each node.
    /// A [`Value::ValueBlock`] blocks opinions from weaker layers.
    pub(crate) fn resolve_field(
        &self,
        field: &str,
        stack: &LayerStack,
        prop_suffix: Option<&str>,
    ) -> Result<Option<Value>> {
        if field == FieldKey::Specifier.as_str() {
            return self.resolve_specifier(stack, prop_suffix);
        }
        if field == FieldKey::Variability.as_str() {
            return self.resolve_variability(stack, prop_suffix);
        }
        if field == FieldKey::Custom.as_str() {
            return self.resolve_custom(stack, prop_suffix);
        }
        if field == FieldKey::TimeSamples.as_str() {
            return Ok(self.resolve_time_samples(stack, prop_suffix)?.map(Value::TimeSamples));
        }
        self.resolve_strongest(field, stack, prop_suffix)
    }

    /// Resolves a token-list-op field by composing list edits from strongest
    /// to weakest across all contributing nodes.
    ///
    /// This is used for metadata like `apiSchemas`, where the field value is a
    /// list operation rather than a strongest-opinion scalar. A value block
    /// stops weaker opinions while preserving any stronger composed edits.
    pub(crate) fn resolve_token_list_op(
        &self,
        field: FieldKey,
        stack: &LayerStack,
        prop_suffix: Option<&str>,
    ) -> Result<Vec<String>> {
        let field = field.as_str();
        let mut ops = Vec::new();

        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            // TODO: a non-conformant backend may store `apiSchemas` as a plain
            // `Value::TokenVec` even though the field is declared as a
            // list-op. We currently skip those opinions (falling through to
            // `_ => continue`). Tightening this further requires a
            // schema-aware decode step in the USDC reader (and any other
            // backend) so list-op fields are always produced as
            // `Value::TokenListOp`; until that lands, ill-typed opinions for
            // list-op fields are simply ignored rather than coerced.
            let list_op = match value.into_owned() {
                Value::ValueBlock => break,
                Value::TokenListOp(op) => op,
                _ => continue,
            };
            ops.push(list_op);
        }

        Ok(compose_list_ops(&ops))
    }

    /// Resolves a path-list-op field by composing list edits from strongest
    /// to weakest across all contributing nodes. Used for property-level
    /// fields like `connectionPaths` and `targetPaths`. A value block stops
    /// weaker opinions while preserving any stronger composed edits.
    pub(crate) fn resolve_path_list_op(
        &self,
        field: FieldKey,
        stack: &LayerStack,
        prop_suffix: Option<&str>,
    ) -> Result<Vec<Path>> {
        let field = field.as_str();
        let mut ops = Vec::new();

        for opinion in self.opinions(field, stack, prop_suffix) {
            let Opinion {
                node,
                query_path,
                value,
                ..
            } = opinion?;
            // A bare `PathVec` (no list-op envelope) is treated as an explicit
            // replacement of weaker opinions — the natural interpretation for
            // a non-list-op-typed value when the field is declared list-op.
            let list_op = match value.into_owned() {
                Value::ValueBlock => break,
                Value::PathListOp(op) => op,
                Value::PathVec(paths) => sdf::PathListOp::explicit(paths),
                _ => continue,
            };
            ops.push(Self::map_path_list_op_to_root(list_op, &query_path, &node.map_to_root));
        }

        Ok(compose_list_ops(&ops))
    }

    /// Translate a path-list-op opinion from one contributing node into the
    /// composed stage namespace before list-op composition.
    ///
    /// Every bucket must be translated, not just contributed values: delete
    /// and reorder opinions only work when they compare against weaker items
    /// in the same namespace. Unmappable paths are dropped, matching a
    /// namespace map whose source domain does not include the authored target.
    fn map_path_list_op_to_root(op: sdf::PathListOp, anchor: &Path, map: &MapFunction) -> sdf::PathListOp {
        fn map_paths(paths: Vec<Path>, anchor: &Path, map: &MapFunction) -> Vec<Path> {
            paths
                .into_iter()
                .filter_map(|path| {
                    // List-op targets are authored in the contributing node's
                    // namespace; compose them only after translating to the
                    // stage root namespace so deletes and reorders compare
                    // like-for-like across layers and arcs.
                    let absolute = anchor.make_absolute(&path);
                    map.map_source_to_target(&absolute)
                })
                .collect()
        }

        sdf::PathListOp {
            explicit: op.explicit,
            explicit_items: map_paths(op.explicit_items, anchor, map),
            added_items: map_paths(op.added_items, anchor, map),
            prepended_items: map_paths(op.prepended_items, anchor, map),
            appended_items: map_paths(op.appended_items, anchor, map),
            deleted_items: map_paths(op.deleted_items, anchor, map),
            ordered_items: map_paths(op.ordered_items, anchor, map),
        }
    }

    /// Builds the query path for a node, applying `prop_suffix` if given.
    /// Borrows the node's path when no suffix is needed (zero-copy).
    fn query_path<'a>(node: &'a Node, prop_suffix: Option<&str>) -> Result<Cow<'a, Path>> {
        match prop_suffix {
            Some(suffix) => Ok(Cow::Owned(Path::new(&format!("{}{suffix}", node.path))?)),
            None => Ok(Cow::Borrowed(&node.path)),
        }
    }

    /// Iterates the authored opinions for `field` across the composition graph,
    /// strongest to weakest, skipping nodes with no opinion. Centralizes the
    /// query-path / layer / `try_get` walk shared by every `resolve_*` field
    /// resolver.
    fn opinions<'a>(
        &'a self,
        field: &'a str,
        stack: &'a LayerStack,
        prop_suffix: Option<&'a str>,
    ) -> impl Iterator<Item = Result<Opinion<'a>>> + 'a {
        // Each node fans out into one opinion per contributing layer in its
        // layer stack, strongest sublayer first, so a per-site node surfaces
        // every sublayer that authored the field. Permission-denied nodes (a
        // direct arc to a private site, spec 10.3.3) stay in `nodes` for
        // structural queries but contribute no opinions here.
        //
        // TODO(perf): collecting per node allocates a small Vec; a custom
        // iterator over (node, layer) pairs would avoid it on the hot path.
        self.nodes()
            .filter(|node| !node.is_permission_denied())
            .flat_map(move |node| {
                let query_path = match Self::query_path(node, prop_suffix) {
                    Ok(path) => path,
                    Err(err) => return vec![Err(err)],
                };
                let mut out: Vec<Result<Opinion<'a>>> = Vec::new();
                for (layer, offset) in node.layers() {
                    match stack.layer(layer).try_get(&query_path, field) {
                        Ok(Some(value)) => out.push(Ok(Opinion {
                            node,
                            layer,
                            query_path: query_path.clone(),
                            value,
                            offset,
                        })),
                        Ok(None) => {}
                        Err(err) => out.push(Err(err)),
                    }
                }
                out
            })
    }

    /// Walks nodes from strongest to weakest, returning the first opinion.
    /// A [`Value::ValueBlock`] returns `None`, blocking weaker layers. When
    /// the strongest opinion is a dictionary, weaker dictionary opinions are
    /// recursively merged into it (spec 12.2.5); a `ValueBlock` then blocks
    /// only the remaining weaker opinions, and weaker non-dictionary opinions
    /// are ignored.
    fn resolve_strongest(&self, field: &str, stack: &LayerStack, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let mut merged: Option<HashMap<String, Value>> = None;
        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            match (merged.as_mut(), value.into_owned()) {
                (None, Value::ValueBlock) => return Ok(None),
                (None, Value::Dictionary(dict)) => merged = Some(dict),
                (None, other) => return Ok(Some(other)),
                (Some(_), Value::ValueBlock) => break,
                (Some(strong), Value::Dictionary(weaker)) => dictionary_over(strong, weaker),
                (Some(_), _) => {}
            }
        }
        Ok(merged.map(Value::Dictionary))
    }

    /// Resolves `timeSamples` across the composition graph, applying each
    /// node's effective layer offset (spec 12.3.2.1) so authored layer time is
    /// mapped to stage time.
    ///
    /// Walks nodes strongest-to-weakest and returns the first node that authors
    /// time samples, retimed by that node's `map_to_root` offset. A
    /// [`Value::ValueBlock`] blocks weaker layers, matching [`Self::resolve_strongest`].
    ///
    /// Unlike generic fields, time samples never merge across nodes: the
    /// strongest authored opinion wins as a whole.
    pub(crate) fn resolve_time_samples(
        &self,
        stack: &LayerStack,
        prop_suffix: Option<&str>,
    ) -> Result<Option<sdf::TimeSampleMap>> {
        self.time_samples_in(stack, prop_suffix, None)
    }

    /// Resolves `timeSamples` considering only opinions from the root layer
    /// stack (`local_layers`). Used by value-clip resolution, where clip data
    /// is weaker than the anchoring layer's local opinions but stronger than
    /// data introduced across reference/payload arcs (spec 12.3.4.5).
    ///
    /// Membership is by layer index, not arc type: a referenced layer stack
    /// also contributes `Root`-arc nodes, so only the stage's own root layer
    /// stack counts as local.
    pub(crate) fn resolve_local_time_samples(
        &self,
        stack: &LayerStack,
        prop_suffix: Option<&str>,
        local_layers: &HashSet<usize>,
    ) -> Result<Option<sdf::TimeSampleMap>> {
        self.time_samples_in(stack, prop_suffix, Some(local_layers))
    }

    /// Shared `timeSamples` walk. When `local_layers` is `Some`, opinions
    /// whose contributing layer is outside that set are skipped so only
    /// root-layer-stack opinions contribute.
    fn time_samples_in(
        &self,
        stack: &LayerStack,
        prop_suffix: Option<&str>,
        local_layers: Option<&HashSet<usize>>,
    ) -> Result<Option<sdf::TimeSampleMap>> {
        let field = FieldKey::TimeSamples.as_str();
        for opinion in self.opinions(field, stack, prop_suffix) {
            let Opinion {
                layer, value, offset, ..
            } = opinion?;
            if local_layers.is_some_and(|local| !local.contains(&layer)) {
                continue;
            }
            match value.into_owned() {
                Value::ValueBlock => return Ok(None),
                Value::TimeSamples(samples) => {
                    return Ok(Some(retime_samples(samples, offset)));
                }
                _ => continue,
            }
        }
        Ok(None)
    }

    /// Resolves the `clipSets` strength order, if authored. Returns the ordered
    /// clip set names (strongest first), folding the list-op edits across every
    /// contributing layer per generic list-op resolution (spec 12.2.6).
    ///
    /// The list op is composed over an empty base, matching C++
    /// `Usd_ClipSetDefinition`: an authored `clipSets` is the authoritative
    /// ordered list, so a set absent from it is excluded. This makes the
    /// return value three-way:
    ///
    /// - `None` — no opinion authored anywhere; clip sets fall back to name
    ///   order (spec 12.3.4.1).
    /// - `Some([])` — authored but composing to empty (explicit `[]` or a
    ///   delete that cancels every name); no clip sets are active.
    /// - `Some(names)` — the composed strength order.
    ///
    /// `clipSets` is a string list op; both the `String` and `Token` list-op
    /// encodings (and bare vecs, treated as explicit) are accepted, since USDC
    /// backends may decode it either way. A `ValueBlock` with no stronger
    /// opinion leaves the field unauthored (`None`), falling back to name order.
    pub(crate) fn clip_sets_order(&self, stack: &LayerStack) -> Result<Option<Vec<String>>> {
        let mut ops = Vec::new();
        for opinion in self.opinions(FieldKey::ClipSets.as_str(), stack, None) {
            match opinion?.value.into_owned() {
                // Stop weaker opinions while keeping any stronger composed edits.
                Value::ValueBlock => break,
                Value::StringListOp(op) | Value::TokenListOp(op) => ops.push(op),
                Value::StringVec(names) | Value::TokenVec(names) => ops.push(sdf::StringListOp::explicit(names)),
                _ => continue,
            }
        }
        if ops.is_empty() {
            return Ok(None);
        }
        Ok(Some(compose_list_ops(&ops)))
    }

    /// Resolves explicit value clip sets while preserving the layer that
    /// authored path-bearing fields. The top-level `clips` dictionary composes
    /// recursively, but relative clip assets must still be anchored to the
    /// layer that supplied `assetPaths`/`manifestAssetPath`.
    pub(crate) fn resolve_clip_sets(&self, stack: &LayerStack) -> Result<Vec<clip::ResolvedClipSet>> {
        let mut sets: HashMap<String, HashMap<String, Value>> = HashMap::new();
        let mut blocked_sets: HashSet<String> = HashSet::new();
        let mut asset_layers: HashMap<String, usize> = HashMap::new();
        let mut manifest_layers: HashMap<String, usize> = HashMap::new();
        // Sets with explicit `assetPaths` (whose `active`/`times` are retimed
        // as they compose) versus the offset of a template set's authoring
        // node (whose schedule is derived later and retimed afterwards).
        let mut explicit_sets: HashSet<String> = HashSet::new();
        let mut template_offsets: HashMap<String, LayerOffset> = HashMap::new();

        // Opinions fan out per contributing sublayer, strongest first; a value
        // block on any layer stops every weaker opinion (spec 12.3.4).
        for opinion in self.opinions(FieldKey::Clips.as_str(), stack, None) {
            let Opinion {
                layer, value, offset, ..
            } = opinion?;
            match value.into_owned() {
                Value::ValueBlock => break,
                Value::Dictionary(dict) => {
                    for (set_name, set_value) in dict {
                        if blocked_sets.contains(&set_name) {
                            continue;
                        }
                        let Value::Dictionary(fields) = set_value else {
                            if !sets.contains_key(&set_name) {
                                blocked_sets.insert(set_name);
                            }
                            continue;
                        };
                        let composed = sets.entry(set_name.clone()).or_default();
                        for (field, value) in fields {
                            if composed.contains_key(&field) {
                                continue;
                            }
                            let value = if field == clip::keys::ACTIVE || field == clip::keys::TIMES {
                                retime_clip_stage_times(value, offset)
                            } else {
                                value
                            };
                            // Relative clip asset paths anchor on the layer that
                            // authored them. Explicit `assetPaths` win over a
                            // template in parse_one, so they always set the
                            // anchor, while `templateAssetPath` only sets it when
                            // no explicit `assetPaths` has been composed — else a
                            // weaker template layer would mis-anchor the explicit
                            // paths the stronger layer authored.
                            if field == clip::keys::ASSET_PATHS {
                                asset_layers.insert(set_name.clone(), layer);
                                explicit_sets.insert(set_name.clone());
                            } else if field == clip::keys::TEMPLATE_ASSET_PATH {
                                if !explicit_sets.contains(&set_name) {
                                    asset_layers.insert(set_name.clone(), layer);
                                }
                                template_offsets.insert(set_name.clone(), offset);
                            } else if field == clip::keys::MANIFEST_ASSET_PATH {
                                manifest_layers.insert(set_name.clone(), layer);
                            }
                            composed.insert(field, value);
                        }
                    }
                }
                _ => continue,
            }
        }

        let clips = Value::Dictionary(
            sets.into_iter()
                .map(|(name, fields)| (name, Value::Dictionary(fields)))
                .collect(),
        );
        let order = self.clip_sets_order(stack)?;

        Ok(clip::ClipSet::parse_all(&clips, order.as_deref())
            .into_iter()
            .filter_map(|mut set| {
                let asset_layer = asset_layers.get(&set.name).copied()?;
                let manifest_layer = manifest_layers.get(&set.name).copied();
                // Explicit `active`/`times` were retimed as they composed. A
                // template schedule is derived in clip time, so retime its
                // stage times here by the authoring node's offset.
                if !explicit_sets.contains(&set.name) {
                    if let Some(&offset) = template_offsets.get(&set.name) {
                        set.retime_stage_times(offset);
                    }
                }
                Some(clip::ResolvedClipSet {
                    set,
                    asset_layer,
                    manifest_layer,
                })
            })
            .collect())
    }

    /// Variability resolution per spec 12.2.3: weakest authored opinion wins.
    /// Iterates strongest-to-weakest tracking the latest match, so a
    /// [`Value::ValueBlock`] still blocks weaker opinions.
    fn resolve_variability(&self, stack: &LayerStack, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let field = FieldKey::Variability.as_str();
        let mut weakest = None;
        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            if matches!(value.as_ref(), Value::ValueBlock) {
                break;
            }
            if matches!(value.as_ref(), Value::Variability(_)) {
                weakest = Some(value.into_owned());
            }
        }
        Ok(weakest)
    }

    /// `custom` resolution per spec 12.2.4: any-true across authored opinions.
    /// Returns `Bool(true)` as soon as any opinion is true, `Bool(false)` if
    /// at least one opinion was authored but none were true, and `None`
    /// otherwise.
    fn resolve_custom(&self, stack: &LayerStack, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let field = FieldKey::Custom.as_str();
        let mut saw_opinion = false;
        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            if matches!(value.as_ref(), Value::ValueBlock) {
                break;
            }
            saw_opinion = true;
            if matches!(value.as_ref(), Value::Bool(true)) {
                return Ok(Some(Value::Bool(true)));
            }
        }
        Ok(saw_opinion.then_some(Value::Bool(false)))
    }

    /// Specifier resolution per spec 12.2.1.
    ///
    /// `over` is undefining; `def` and `class` are defining. The composed
    /// specifier is `def` if the strongest defining opinion is `def`, or if
    /// the strongest defining opinion not from a direct inherit is `def`.
    /// It is `class` if the strongest defining opinion not from a direct
    /// inherit is `class`, or if every defining opinion is `class`. It is
    /// `over` only when every authored opinion is `over`.
    fn resolve_specifier(&self, stack: &LayerStack, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let field = FieldKey::Specifier.as_str();
        let mut specs: Vec<(Specifier, ArcType)> = Vec::new();
        for opinion in self.opinions(field, stack, prop_suffix) {
            let Opinion { node, value, .. } = opinion?;
            if matches!(value.as_ref(), Value::ValueBlock) {
                break;
            }
            if let Value::Specifier(s) = value.into_owned() {
                specs.push((s, node.arc));
            }
        }
        if specs.is_empty() {
            return Ok(None);
        }

        let strongest_defining = specs.iter().find(|(s, _)| *s != Specifier::Over).map(|(s, _)| *s);
        let Some(strongest) = strongest_defining else {
            // All authored opinions are `over`.
            return Ok(Some(Value::Specifier(Specifier::Over)));
        };

        let strongest_non_inherit_defining = specs
            .iter()
            .find(|(s, arc)| *s != Specifier::Over && *arc != ArcType::Inherit)
            .map(|(s, _)| *s);

        if strongest == Specifier::Def || strongest_non_inherit_defining == Some(Specifier::Def) {
            return Ok(Some(Value::Specifier(Specifier::Def)));
        }

        let all_defining_class = specs
            .iter()
            .filter(|(s, _)| *s != Specifier::Over)
            .all(|(s, _)| *s == Specifier::Class);
        if strongest_non_inherit_defining == Some(Specifier::Class) || all_defining_class {
            return Ok(Some(Value::Specifier(Specifier::Class)));
        }

        Ok(Some(Value::Specifier(strongest)))
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
#[derive(Debug, Clone, Default)]
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
    /// `true` when this prim is a descendant of an instance prim (spec
    /// 11.3.3). Set by the cache once an ancestor resolves as an instance and
    /// inherited by every deeper prim, so local opinions on the instance
    /// subtree can be discarded during composition.
    pub within_instance: bool,
    /// Target-namespace paths an ancestor's direct arc to a `permission =
    /// private` site denied (spec 10.3.3). A node whose path lies under one of
    /// these prefixes was reached through that denied arc, so the cache marks
    /// it `PERMISSION_DENIED` even in descendant prims composed separately
    /// (where the arc is extended, not authored here).
    pub denied_prefixes: Vec<Path>,
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
    /// The node's mapping to its parent node (relative, not to the root). When
    /// the arc nests under [`parent`](Self::parent), composing this atop the
    /// parent's `map_to_root` reproduces `map` exactly, including time offsets
    /// — whereas inverting `map` would drop them.
    pub map_to_parent: MapFunction,
    /// Layer stack of the arc target site: each `(layer index, sublayer
    /// offset)` member that a descendant must rescan to find its own site.
    pub layer_stack: Vec<(usize, LayerOffset)>,
    /// Arc type that introduced this mapping.
    pub arc: ArcType,
    /// Index in the ancestor-arc list of the arc this one nested under in the
    /// parent prim's graph (e.g. a variant set a reference brought in nests
    /// under that reference). `None` for an arc directly on the parent prim.
    /// Lets a child rebuild the parent's node tree instead of flattening it (C++
    /// `AppendChildNameToAllSites` preserves this nesting).
    pub parent: Option<usize>,
}

// ---------------------------------------------------------------------------
// IndexBuilder: single-pass LIVRPS composition
// ---------------------------------------------------------------------------

/// Maximum recursion depth for nested composition arcs.
const MAX_COMPOSITION_DEPTH: usize = 100;

/// Builds a prim index by evaluating LIVRPS for each composition site.
///
/// All inputs are immutable shared references, making each build an
/// independent pure function (suitable for future parallel execution).
struct IndexBuilder<'a> {
    stack: &'a LayerStack,
    ctx: &'a CompositionContext,
    /// Cached prim indices from the composition cache. Used by
    /// `merge_full_index` and `add_implied_nodes` to resolve targets
    /// with full context (including ancestor-propagated specs).
    cached_indices: &'a HashMap<Path, PrimIndex>,
    /// Strength-ordered composition graph.
    output: PrimIndexGraph,
    /// Deduplication: (layer_index, path, arc) triples already emitted.
    seen: HashSet<(usize, Path, ArcType)>,
    /// Sites currently being evaluated (on the call stack).
    eval_stack: HashSet<(usize, Path)>,
    /// Builder-local cache of target indices for inherit/specialize/internal-ref
    /// targets. Avoids rebuilding the same target within a single prim's composition.
    target_indices: HashMap<Path, PrimIndex>,
    /// True when evaluation is within a specializes arc context.
    /// All nodes created while true are flagged `HAS_SPECIALIZES`, which the
    /// strength comparator uses to place them in the globally-weak band per
    /// spec section 10.4.1.
    in_specialize: bool,
    /// Layer stack the root `L` site scans (the root layer stack for a stage
    /// prim, or a referenced asset's sublayer stack for an arc target reached
    /// within that reference).
    ambient: Vec<(usize, LayerOffset)>,
    /// Whether [`ambient`](Self::ambient) is the stage's root layer stack. Lets
    /// `merge_full_index` decide if an arc target is composed at root ambient
    /// (where the stage-keyed `cached_indices` apply) without rebuilding the
    /// root layer stack to compare against.
    ambient_is_root: bool,
}

impl<'a> IndexBuilder<'a> {
    fn new(
        stack: &'a LayerStack,
        ctx: &'a CompositionContext,
        cached_indices: &'a HashMap<Path, PrimIndex>,
        ambient: Vec<(usize, LayerOffset)>,
        ambient_is_root: bool,
    ) -> Self {
        Self {
            stack,
            ctx,
            cached_indices,
            output: PrimIndexGraph::default(),
            seen: HashSet::new(),
            eval_stack: HashSet::new(),
            target_indices: HashMap::new(),
            in_specialize: false,
            ambient,
            ambient_is_root,
        }
    }

    /// Build the prim index for the given composed path.
    ///
    /// Evaluates all composition sites (root + ancestor-derived). Arc targets
    /// are composed recursively in the referencing prim's context (including
    /// its variant selections), so a variant set a reference or payload brings
    /// in is resolved during that recursive build rather than by a separate
    /// re-resolution pass.
    fn build(&mut self, path: &Path) -> Result<(), Error> {
        // The synthetic, inert tree root owns every otherwise-parentless node,
        // making the composition graph a single rooted tree. It must exist
        // before any site is evaluated so the root `L` site, ancestor arcs, and
        // implied classes attach under it. A prim with no opinions keeps only
        // this inert root, so `is_empty()` still reports it as empty.
        self.output.init_root(path.clone());

        // A prim inside an instance discards every local opinion (spec 11.3.3):
        // its subtree is composed purely from the arcs the instance brings in,
        // which arrive through ancestor-arc propagation below. Skipping the
        // local root site here means local arcs are never followed in the first
        // place — a post-build node prune would drop the local `Root` node but
        // leave the Reference/Inherit/Variant nodes that local opinion spawned.
        if !self.ctx.within_instance {
            // The root L stage scans this build's ambient layer stack (the stage
            // root layer stack for a stage prim, or a referenced asset's
            // sublayer stack for an arc target). Opinions from other layer
            // stacks are not scanned here — they enter only by following their
            // arcs, which compose as real child subtrees with implied-class
            // propagation.
            let ambient = self.ambient.clone();

            // Evaluate root composition site (no parent — this is the graph root).
            self.eval_site(
                path,
                &ambient,
                ArcType::Root,
                0,
                NodeId::INVALID,
                MapFunction::identity(),
                &[],
            )?;
        }

        // Propagate ancestor arcs: only match arcs whose target (composed)
        // prefix equals the parent path, then remap by appending the child name.
        // This mirrors C++ behavior where each level only uses its direct
        // parent's arc mappings for descendant propagation.
        //
        // TODO: this reconstructs the parent prim's node tree from a flat arc
        // list by re-composing each arc with `eval_site`. C++
        // `AppendChildNameToAllSites` instead copies the parent's already-built
        // graph and only deepens the site paths (maps untouched). Migrating to
        // that graph-copy model would retire `AncestorArc`'s `parent` /
        // `map_to_parent` bookkeeping and the re-composition, and would carry
        // nesting across all ancestor levels (this step nests only one level).
        let child_name = path.name().unwrap_or("");
        if !child_name.is_empty() {
            let parent_path = path.parent();
            // A class an ancestral arc brings in (e.g. a referenced prim's
            // inherit) propagates its implied class into this build's ambient
            // stack, so pass it as the outer stack. This reaches a global class
            // the inherited prim references whose implied node sits at the same
            // path but in the ambient (referencing) layer stack.
            let ambient = self.ambient.clone();
            // `ctx` aliases the external composition context, so iterating its
            // arcs does not borrow `self` and leaves `self.eval_site` free.
            let ctx = self.ctx;
            // The node each ancestral arc composed to, so a nested arc can
            // attach under its parent (C++ `AppendChildNameToAllSites` keeps the
            // parent prim's tree). The arc list is parent-before-child.
            let mut composed: Vec<NodeId> = vec![NodeId::INVALID; ctx.ancestor_arcs.len()];
            for (i, a) in ctx.ancestor_arcs.iter().enumerate() {
                // Map the parent path through this arc. Only arcs whose target
                // prefix matches the parent succeed.
                let Some(parent_in_source) = parent_path.as_ref().and_then(|p| a.map.map_target_to_source(p)) else {
                    continue;
                };
                let Ok(rpath) = parent_in_source.append_path(child_name) else {
                    continue;
                };
                // Nest under the parent arc's composed node and map relative to
                // it (`map_to_parent`), so composing atop the parent's
                // `map_to_root` reproduces this node's `map` — paths and time
                // offsets alike. A top-level arc (no composed parent) maps to the
                // root directly, where `map_to_parent` already equals `map`.
                let parent_node = a.parent.map(|p| composed[p]).unwrap_or(NodeId::INVALID);
                let map = if parent_node.is_valid() {
                    a.map_to_parent.clone()
                } else {
                    a.map.clone()
                };
                // `map` carries the ancestor node's arc offset to the root; the
                // L-loop composes each member's sublayer offset on top, so the
                // site's whole layer stack must be rescanned at the child path.
                //
                // `eval_site` appends the site's own node first (the L node when
                // the site has a local opinion), so the node at `before` is the
                // representative a nested child attaches under. A site with no
                // local opinion at the child path contributes no node here, so a
                // child arc would fall back to a flat attach — acceptable, since
                // an arc that authors nothing at the child adds no nesting.
                let before = self.output.len();
                self.eval_site(&rpath, &a.layer_stack, a.arc, 0, parent_node, map, &ambient)?;
                if self.output.len() > before {
                    composed[i] = NodeId(before as u32);
                }
            }
        }

        // Build the strength-order projection: a DFS of the tree for
        // non-specialize nodes, then the globally-weak specialize band (spec
        // 10.4.1), all ordered by the node strength comparator.
        self.output.finalize_strength_order();

        Ok(())
    }

    /// Evaluate a single composition site: run LIVRPS for `path` within
    /// `layer_stack`. Called recursively for each arc target.
    ///
    /// `map_to_parent` is the namespace mapping for L nodes created at this
    /// site (translates from `path`'s namespace to the parent node's namespace).
    /// The incoming time offset in `map_to_parent` represents the retiming
    /// applied by the arc that introduced this site; each per-layer entry's
    /// sublayer offset is composed on top for the L-node produced by that
    /// layer.
    #[allow(clippy::too_many_arguments)]
    fn eval_site(
        &mut self,
        path: &Path,
        layer_stack: &[(usize, LayerOffset)],
        arc: ArcType,
        depth: usize,
        parent: NodeId,
        map_to_parent: MapFunction,
        outer_stack: &[(usize, LayerOffset)],
    ) -> Result<(), Error> {
        if depth > MAX_COMPOSITION_DEPTH {
            return Err(Error::ArcCycle {
                path: path.clone(),
                depth,
            });
        }

        // Cycle detection: if this (root_layer, path) site is already being
        // evaluated somewhere up the call stack, we have a composition cycle.
        let Some(&(root_layer, _)) = layer_stack.first() else {
            return Ok(());
        };
        let site_key = (root_layer, path.clone());
        if !self.eval_stack.insert(site_key.clone()) {
            return Err(Error::ArcCycle {
                path: path.clone(),
                depth,
            });
        }

        // Track specialize context for global weakness (spec 10.4.1).
        let prev_in_specialize = self.in_specialize;
        if arc == ArcType::Specialize {
            self.in_specialize = true;
        }

        let result = self.eval_site_body(path, layer_stack, arc, depth, parent, map_to_parent, outer_stack);
        self.in_specialize = prev_in_specialize;
        self.eval_stack.remove(&site_key);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_site_body(
        &mut self,
        path: &Path,
        layer_stack: &[(usize, LayerOffset)],
        arc: ArcType,
        depth: usize,
        parent: NodeId,
        map_to_parent: MapFunction,
        outer_stack: &[(usize, LayerOffset)],
    ) -> Result<(), Error> {
        let site_start = self.output.len();

        // L — Local opinions: one node for the whole site (C++ `PcpNode` =
        // (layerStack, path)). Collect every sublayer that authors a spec,
        // strongest first, pairing each with its sublayer offset; value
        // resolution folds that offset atop the arc offset per member. The site
        // node is the representative — parent for subsequent arcs at this site.
        let members: Vec<(usize, LayerOffset)> = layer_stack
            .iter()
            .filter(|&&(i, _)| self.stack.layer(i).has_spec(path) && self.seen.insert((i, path.clone(), arc)))
            .copied()
            .collect();
        let mut site_node = NodeId::INVALID;
        if !members.is_empty() {
            site_node = self.output.add_site_child(
                parent,
                members,
                path.clone(),
                arc,
                map_to_parent.clone(),
                self.in_specialize,
            );
        }

        // I — Inherits: compose InheritPaths. A class arc targets a prim in the
        // same layer stack as the inheriting site, so compose it within that
        // ambient `layer_stack` rather than re-rooting at the root layer stack.
        // Implied arcs are propagated inline through ancestor arc mappings.
        let inherit_start = self.output.len();
        let inherits =
            compose_arc_list_in::<Path>(&self.output[site_start..], FieldKey::InheritPaths, &self.stack.layers)?;
        for inherit_path in &inherits {
            let resolved = path.make_absolute(inherit_path);
            let before = self.output.len();
            self.merge_full_index(
                &resolved,
                ArcType::Inherit,
                site_node,
                LayerOffset::IDENTITY,
                layer_stack,
            )?;
            self.add_implied_nodes(before, depth, site_node)?;
            for vt in variant_expanded_targets(path, &resolved) {
                let before = self.output.len();
                self.merge_full_index(&vt, ArcType::Inherit, site_node, LayerOffset::IDENTITY, layer_stack)?;
                self.add_implied_nodes(before, depth, site_node)?;
            }
        }

        // Implied classes through a reference/payload transfer. A class the
        // referenced prim inherits lives in the referenced layer stack, but the
        // same relationship must hold in the referencing namespace so outer
        // opinions on the class contribute (spec 10.3.2.3.2). Conjugate each
        // inherit just composed through this arc's transfer and compose the
        // implied class against the OUTER layer stack — before variants, so a
        // variant selection authored on the implied class outranks the
        // referenced prim's own selection.
        if matches!(arc, ArcType::Reference | ArcType::Payload) && !outer_stack.is_empty() {
            let transfer = map_to_parent.with_root_identity();
            self.propagate_implied_through_transfer(inherit_start, &transfer, outer_stack, depth, parent)?;
        }

        // V — Variants: resolve selections iteratively (nested variant sets).
        self.eval_variants(site_start, site_node, layer_stack);

        // Collect range of all opinion nodes (L + I + V) for R/P/S lookups.
        let opinion_end = self.output.len();

        // R — References.
        let references = compose_references_in(&self.output[site_start..opinion_end], &self.stack.layers)?;
        for reference in &references {
            self.eval_arc_target(
                &reference.asset_path,
                &reference.prim_path,
                ArcType::Reference,
                path,
                depth,
                site_node,
                reference.layer_offset.sanitized(),
                layer_stack,
            )?;
        }

        // P — Payloads.
        if self.stack.load_payloads {
            let payloads = collect_payloads_in(&self.output[site_start..opinion_end], &self.stack.layers)?;
            for payload in &payloads {
                self.eval_arc_target(
                    &payload.asset_path,
                    &payload.prim_path,
                    ArcType::Payload,
                    path,
                    depth,
                    site_node,
                    payload.layer_offset.unwrap_or_default().sanitized(),
                    layer_stack,
                )?;
            }
        }

        // S — Specializes.
        let specializes = compose_arc_list_in::<Path>(
            &self.output[site_start..opinion_end],
            FieldKey::Specializes,
            &self.stack.layers,
        )?;
        for specialize_path in &specializes {
            let resolved = path.make_absolute(specialize_path);
            let before = self.output.len();
            self.merge_full_index(
                &resolved,
                ArcType::Specialize,
                site_node,
                LayerOffset::IDENTITY,
                layer_stack,
            )?;
            self.add_implied_nodes(before, depth, site_node)?;
        }

        // Cascade implied classes for every class arc in this site's subtree up
        // through the arc that introduced the site, into `outer_stack` (the
        // referencing layer stack). Running at the end — after all of L/I/V/R/P/S
        // composed — over the whole subtree is what carries a class up the full
        // reference chain to the root: each nesting level re-propagates what the
        // level below produced, so a class inherited several references deep
        // still reaches the root namespace (spec 10.3.2.3.2, and 10.4.1 for the
        // specializes case). The post-inherit propagation above is the narrower
        // pass that runs before variants resolve, for variant-selection timing.
        if !outer_stack.is_empty() {
            let transfer = map_to_parent.with_root_identity();
            self.propagate_implied_through_transfer(site_start, &transfer, outer_stack, depth, parent)?;
        }

        Ok(())
    }

    /// Propagate implied classes for inherit/specialize nodes added since
    /// `start` through this prim's ancestor composition arcs.
    ///
    /// Each ancestor arc is a transfer the class is conjugated across — the same
    /// `_EvalImpliedClassTree` mechanism [`propagate_implied_through_transfer`]
    /// uses for a directly-followed reference, here driven by the arcs
    /// accumulated from ancestor prims. A class inherited inside an ancestor's
    /// referenced layer stack must also hold in this build's namespace so its
    /// opinions there contribute; the implied class is composed against the
    /// build's ambient layer stack (no flat scan of every loaded layer) and
    /// tagged [`IMPLIED_CLASS`](NodeFlags::IMPLIED_CLASS) with `origin`.
    fn add_implied_nodes(&mut self, start: usize, depth: usize, origin: NodeId) -> Result<(), Error> {
        if self.ctx.ancestor_arcs.is_empty() {
            return Ok(());
        }
        // Clone the transfers up front so the `&mut self` propagation calls do
        // not alias the borrow of `self.ctx.ancestor_arcs`.
        let transfers: Vec<MapFunction> = self
            .ctx
            .ancestor_arcs
            .iter()
            .map(|a| a.map.with_root_identity())
            .collect();
        let ambient = self.ambient.clone();
        for transfer in &transfers {
            self.propagate_implied_through_transfer(start, transfer, &ambient, depth, origin)?;
        }
        Ok(())
    }

    fn get_sublayer_stack(&self, root_layer: usize) -> Vec<(usize, LayerOffset)> {
        self.stack
            .sublayer_stacks
            .get(&root_layer)
            .cloned()
            .unwrap_or_else(|| LayerStack::build_sublayer_stack(root_layer, &self.stack.layers, &*self.stack.resolver))
    }

    /// Seed context for building an arc target whose own namespace parent
    /// contributes no context (a top-level class/base prim). The target
    /// inherits the referencing prim's variant selections — resolved from the
    /// opinions composed so far, including the prim's own authored selection —
    /// plus the incoming ancestor selections and fallbacks, so a variant set
    /// the target brings in resolves during this recursive build rather than
    /// needing a global re-resolution pass.
    fn arc_target_seed_context(&self) -> CompositionContext {
        // Skip the inert synthetic root: it carries no opinions and a
        // placeholder layer index, so reading a selection off it would inject a
        // spurious opinion from an unrelated layer.
        let selections = resolve_variant_selections_in(
            self.output.iter().filter(|n| !n.is_inert()),
            &self.stack.layers,
            &self.ctx.variant_fallbacks,
            &self.ctx.selections,
        );
        CompositionContext {
            selections,
            variant_fallbacks: self.ctx.variant_fallbacks.clone(),
            ..Default::default()
        }
    }

    /// Compose the ancestral [`CompositionContext`] for an arc target built
    /// within `ambient`.
    ///
    /// Recurses up the target's namespace: each ancestor is composed in the same
    /// `ambient` from its own parent's context, so the chain carries each
    /// ancestor's arcs and variant selections without the referencing prim's
    /// ancestor arcs leaking in. The recursion bottoms out at a root-level
    /// ancestor with the seed context (the referencing prim's variant selections
    /// and fallbacks), and `context_for_children` threads those selections down.
    /// Intermediate indices are memoised in `target_indices`.
    fn target_ctx(
        &mut self,
        path: &Path,
        ambient: &[(usize, LayerOffset)],
        ambient_is_root: bool,
    ) -> Result<CompositionContext, Error> {
        let parent = match path.parent() {
            Some(p) if p != Path::abs_root() => p,
            _ => return Ok(self.arc_target_seed_context()),
        };
        let parent_ctx = self.target_ctx(&parent, ambient, ambient_is_root)?;
        if !self.target_indices.contains_key(&parent) {
            let parent_idx = PrimIndex::build_with_cache_in(
                &parent,
                self.stack,
                &parent_ctx,
                self.cached_indices,
                ambient,
                ambient_is_root,
            )?;
            self.target_indices.insert(parent.clone(), parent_idx);
        }
        Ok(self.target_indices[&parent].context_for_children(self.stack, &parent_ctx))
    }

    /// Build a full PrimIndex for an arc target and merge its nodes into this
    /// builder's output. Used for inherit, specialize, and internal-reference
    /// targets, which need their own ancestral composition (their namespace
    /// parent's arcs and variant selections).
    ///
    /// The target is composed within `ambient` — the layer stack the arc lives
    /// in (the same stack as the referencing site for class arcs and internal
    /// references), not the stage root layer stack. Its ancestral context comes
    /// from composing the target's namespace parent in the same `ambient`. The
    /// stage-keyed `cached_indices` are consulted only when `ambient` is the
    /// stage root layer stack (handled inside `build_with_cache_in`).
    ///
    /// `arc_offset` is the layer offset of the arc introducing this merge
    /// (identity for inherit/specialize, non-identity only for internal
    /// references/payloads). Each merged node's internal time composition is
    /// preserved by concatenating `arc_offset` with the target node's own
    /// `map_to_root.time_offset()`.
    /// Grafts `source`'s composed subtree into `output`, preserving its
    /// internal parent/child structure. Each node contributes only the
    /// layer-stack members not already recorded in `seen` at `(layer, path,
    /// arc)`; a fully-deduped node is skipped, orphaning its children onto the
    /// root attachment. A grafted child hangs under its grafted parent with its
    /// own `map_to_parent`; a target root or orphan attaches under `root_parent`
    /// with `root_map(node)`. `finish` runs on each newly created node (set
    /// `origin`, mark it implied, …).
    ///
    /// The graph and `seen` are taken as split borrows so the caller can keep
    /// `source` borrowed from a sibling field (`target_indices` / the cached
    /// index map) while this mutates `output`.
    #[allow(clippy::too_many_arguments)]
    fn graft_subtree(
        output: &mut PrimIndexGraph,
        seen: &mut HashSet<(usize, Path, ArcType)>,
        source: &PrimIndex,
        arc: ArcType,
        in_specialize: bool,
        root_parent: NodeId,
        mut root_map: impl FnMut(&Node) -> MapFunction,
        mut finish: impl FnMut(&mut PrimIndexGraph, NodeId),
    ) {
        let mut remap: Vec<Option<NodeId>> = vec![None; source.arena().len()];
        for (sid, node) in source.nodes_with_ids() {
            let members: Vec<(usize, LayerOffset)> = node
                .layer_stack()
                .iter()
                .copied()
                .filter(|&(li, _)| seen.insert((li, node.path.clone(), arc)))
                .collect();
            if members.is_empty() {
                continue;
            }
            let grafted_parent = node.parent().and_then(|p| remap[p.idx()]);
            let (struct_parent, node_map) = match grafted_parent {
                Some(grafted) => (grafted, node.map_to_parent.clone()),
                None => (root_parent, root_map(node)),
            };
            let new_id = output.add_site_child(struct_parent, members, node.path.clone(), arc, node_map, in_specialize);
            finish(output, new_id);
            remap[sid.idx()] = Some(new_id);
        }
    }

    fn merge_full_index(
        &mut self,
        target: &Path,
        arc: ArcType,
        parent: NodeId,
        arc_offset: LayerOffset,
        ambient: &[(usize, LayerOffset)],
    ) -> Result<(), Error> {
        // Track specialize context for global weakness (spec 10.4.1).
        let prev_in_specialize = self.in_specialize;
        if arc == ArcType::Specialize {
            self.in_specialize = true;
        }

        // An arc target is composed at root ambient only when this builder is
        // itself at root ambient and the merge runs against that same stack
        // (class arcs and internal references compose within the site's stack).
        // Comparing against the stored `ambient` avoids rebuilding the root
        // layer stack on every merge.
        let ambient_is_root = self.ambient_is_root && ambient == self.ambient.as_slice();

        if !self.target_indices.contains_key(target) {
            // Compose the target within `ambient` using the ancestral context of
            // its own namespace parent (composed recursively in the same
            // `ambient`), not the referencing prim's. Carrying the referencing
            // prim's ancestor arcs would re-introduce them as opinions on the
            // target's namespace, where they do not belong (and self-cycles when
            // such an arc maps back onto the target's own path).
            let ctx = self.target_ctx(target, ambient, ambient_is_root)?;
            let idx = PrimIndex::build_with_cache_in(
                target,
                self.stack,
                &ctx,
                self.cached_indices,
                ambient,
                ambient_is_root,
            )?;
            self.target_indices.insert(target.clone(), idx);
        }
        let target_index = &self.target_indices[target];
        // The mapping for merged nodes translates from the target's namespace
        // to the parent node's namespace (the inheriting/specializing prim).
        let parent_path = if parent.is_valid() {
            self.output[parent.idx()].path.clone()
        } else {
            target.clone()
        };

        // Graft the target's composed subtree, preserving its internal
        // parent/child links. A target root re-parents under `parent`, mapping
        // the target namespace onto the inheriting prim with the arc's offset;
        // each internal node keeps its own `map_to_parent` and hangs under its
        // grafted parent. A node orphaned by a deduped ancestor falls back to
        // attaching directly under `parent` with the flattened mapping; its
        // origin is `parent` (a directly-introduced arc).
        Self::graft_subtree(
            &mut self.output,
            &mut self.seen,
            target_index,
            arc,
            self.in_specialize,
            parent,
            |node| {
                let composed_offset = arc_offset.concatenate(&node.map_to_root.time_offset());
                MapFunction::from_pair_identity(node.path.clone(), parent_path.clone())
                    .with_time_offset(composed_offset)
            },
            |output, new_id| {
                if parent.is_valid() {
                    output.nodes[new_id.idx()].origin = Some(parent);
                }
            },
        );

        self.in_specialize = prev_in_specialize;
        Ok(())
    }

    /// Adds variant nodes for `variant_path` from the site's ambient
    /// `layer_stack`. Returns the index range of newly added nodes.
    ///
    /// A variant set is authored in the layer stack the prim is composed in, so
    /// only those layers are scanned — not every loaded layer. Scanning all
    /// layers would pull a same-named variant from an unrelated referenced layer
    /// stack into this composition.
    fn add_variant_nodes(
        &mut self,
        variant_path: &Path,
        base: &Path,
        parent: NodeId,
        layer_stack: &[(usize, LayerOffset)],
    ) -> (usize, usize) {
        let start = self.output.len();
        let variant_map = MapFunction::from_pair_identity(variant_path.clone(), base.clone());
        // One variant node for the whole site, folding every sublayer that
        // authors the selected variant (strongest first) with its offset.
        let members: Vec<(usize, LayerOffset)> = layer_stack
            .iter()
            .filter(|&&(i, _)| {
                self.stack.layer(i).has_spec(variant_path)
                    && self.seen.insert((i, variant_path.clone(), ArcType::Variant))
            })
            .copied()
            .collect();
        if !members.is_empty() {
            self.output.add_site_child(
                parent,
                members,
                variant_path.clone(),
                ArcType::Variant,
                variant_map,
                self.in_specialize,
            );
        }
        (start, self.output.len())
    }

    /// Resolve variant selections iteratively, handling nested variant sets
    /// and variant sets on inherited classes.
    fn eval_variants(&mut self, site_start: usize, parent: NodeId, layer_stack: &[(usize, LayerOffset)]) {
        let mut processed = HashSet::new();
        loop {
            let current_end = self.output.len();
            // Gather selections from ALL output nodes (not just this site) so
            // cross-site selections are visible during the first pass. The
            // inert synthetic root carries no opinions and a placeholder layer
            // index, so it is skipped to avoid reading a spurious selection.
            let selections = resolve_variant_selections_in(
                self.output[..current_end].iter().filter(|n| !n.is_inert()),
                &self.stack.layers,
                &self.ctx.variant_fallbacks,
                &self.ctx.selections,
            );
            if selections.is_empty() {
                break;
            }
            // Graft variant nodes in a deterministic order. `selections` is a
            // HashMap, whose iteration order is randomized per run and would
            // otherwise leak into the order of equal-strength variant sibling
            // nodes (and thus the composed prim stack).
            //
            // TODO: order by the prim's authored `variantSetNames` rather than
            // by set name — C++ ranks variant arcs by a set's position in that
            // list (e.g. `["v2", "v1"]` makes `v2` stronger). Sorting by name
            // matches it only when the declared order is alphabetical.
            let mut selections: Vec<(&String, &String)> = selections.iter().collect();
            selections.sort_by(|a, b| a.0.cmp(b.0));
            let before = self.output.len();
            for (set_name, selection) in selections {
                // Try appending variant to every node in this site (not all output —
                // variant sets belong to this site's paths).
                let bases: Vec<Path> = self.output[site_start..before].iter().map(|n| n.path.clone()).collect();
                for base in &bases {
                    let variant_path = base.append_variant_selection(set_name, selection);
                    if !processed.insert(variant_path.clone()) {
                        continue;
                    }
                    self.add_variant_nodes(&variant_path, base, parent, layer_stack);
                }
            }

            if self.output.len() == before {
                break;
            }
        }
    }

    /// Evaluate a reference or payload target.
    ///
    /// `arc_offset` is the layer offset authored on the reference/payload
    /// itself (spec 10.3.2.1.2 / 10.3.2.2.2). It composes with the per-layer
    /// sublayer offsets inside `eval_site`'s L loop to produce the effective
    /// retiming carried by `map_to_root`.
    #[allow(clippy::too_many_arguments)]
    fn eval_arc_target(
        &mut self,
        asset_path: &str,
        prim_path: &Path,
        arc: ArcType,
        context_path: &Path,
        depth: usize,
        parent: NodeId,
        arc_offset: LayerOffset,
        outer_stack: &[(usize, LayerOffset)],
    ) -> Result<(), Error> {
        if asset_path.is_empty() {
            // Internal reference — the target lives in the same layer stack as
            // the referencing site, so compose it within that ambient stack
            // (`outer_stack`, which the caller set to the site's layer stack)
            // with its own ancestral context, rather than re-rooting at the
            // stage's root layer stack.
            if prim_path.is_empty() {
                return Ok(());
            }
            self.merge_full_index(prim_path, arc, parent, arc_offset, outer_stack)?;
            for vt in variant_expanded_targets(context_path, prim_path) {
                self.merge_full_index(&vt, arc, parent, arc_offset, outer_stack)?;
            }
        } else {
            // External reference — evaluate in a fresh sub-builder so the
            // target's layer stack doesn't share our `seen` set. The sub-builder
            // uses its own ancestor context derived from the target path.
            let Some(layer_index) = find_layer(asset_path, &self.stack.layers, &*self.stack.resolver) else {
                return Err(Error::UnresolvedLayer {
                    asset_path: asset_path.to_string(),
                    arc,
                    site_path: context_path.clone(),
                });
            };
            let layer_id = self.stack.identifier(layer_index).to_owned();
            let source = if prim_path.is_empty() {
                let root = Path::abs_root();
                let Some(value) = self
                    .stack
                    .layer(layer_index)
                    .try_get(&root, FieldKey::DefaultPrim.as_str())?
                else {
                    return Err(Error::MissingDefaultPrim {
                        layer_id,
                        arc,
                        site_path: context_path.clone(),
                    });
                };
                match value.into_owned() {
                    Value::Token(name) | Value::String(name) => match Path::new(&format!("/{name}")) {
                        Ok(p) => p,
                        Err(_) => {
                            return Err(Error::InvalidDefaultPrim {
                                layer_id,
                                arc,
                                site_path: context_path.clone(),
                            });
                        }
                    },
                    _ => {
                        return Err(Error::InvalidDefaultPrim {
                            layer_id,
                            arc,
                            site_path: context_path.clone(),
                        });
                    }
                }
            } else {
                prim_path.clone()
            };
            let target_stack = self.get_sublayer_stack(layer_index);
            let arc_map = MapFunction::from_pair(source.clone(), context_path.clone()).with_time_offset(arc_offset);
            // Evaluate directly — arc-type-aware dedup allows the same
            // (layer, path) to appear under different arc types. Pass the
            // referencing site's `outer_stack` so the target's own inherits can
            // propagate implied classes back into the referencing namespace.
            let before = self.output.len();
            self.eval_site(&source, &target_stack, arc, depth + 1, parent, arc_map, outer_stack)?;
            // Composition added nothing. Keep a culled node for the members not
            // already contributed at this site (filtering empties out a target
            // whose layers were consumed elsewhere, leaving only the genuinely
            // empty target), so an editor and change tracking still see the arc;
            // it contributes no opinions to value resolution (C++ culling).
            if self.output.len() == before {
                let members: Vec<(usize, LayerOffset)> = target_stack
                    .iter()
                    .copied()
                    .filter(|&(li, _)| self.seen.insert((li, source.clone(), arc)))
                    .collect();
                if !members.is_empty() {
                    let culled_map =
                        MapFunction::from_pair(source.clone(), context_path.clone()).with_time_offset(arc_offset);
                    let id = self.output.add_site_child(
                        parent,
                        members,
                        source.clone(),
                        arc,
                        culled_map,
                        self.in_specialize,
                    );
                    self.output.nodes[id.idx()].flags |= NodeFlags::CULLED;
                }
            }
            // Also propagate ancestor arcs within the target layer: the
            // reference target may sit under a prim that itself carries arcs
            // (an ancestral reference), so its descendants must reach those.
            // Compose the target's namespace parent within the target's own
            // sublayer stack (not the stage root), from a clean seed context.
            if let Some(source_parent) = source.parent() {
                if source_parent != Path::abs_root() {
                    let child_name = source.name().unwrap_or("");
                    let seed = self.arc_target_seed_context();
                    let parent_index = PrimIndex::build_with_cache_in(
                        &source_parent,
                        self.stack,
                        &seed,
                        self.cached_indices,
                        &target_stack,
                        false,
                    )?;
                    let ancestor_sites: Vec<_> = parent_index
                        .nodes()
                        .filter(|n| n.arc != ArcType::Root)
                        .filter_map(|n| {
                            n.path
                                .append_path(child_name)
                                .ok()
                                .map(|p| (p, n.layer_stack().to_vec(), n.arc, n.path.clone()))
                        })
                        .collect();
                    for (rpath, layer_stack, a, node_path) in &ancestor_sites {
                        let ancestor_map = MapFunction::from_pair(node_path.clone(), context_path.clone())
                            .with_time_offset(arc_offset);
                        self.eval_site(rpath, layer_stack, *a, depth + 1, parent, ancestor_map, outer_stack)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Propagate implied classes for class arcs found in a freshly composed
    /// arc-target subtree (C++ `_EvalImpliedClassTree`).
    ///
    /// `start` bounds the subtree's nodes. For each inherit/specialize node in
    /// it, the class path is conjugated through `transfer` (the arc's
    /// map-to-parent carrying the `(/, /)` root identity so a class rooted
    /// outside the arc's domain still maps) into the referencing namespace, and
    /// the implied class is composed against `outer_stack` — the referencing
    /// layer stack — so outer opinions on the class contribute. Each implied
    /// node is tagged [`IMPLIED_CLASS`](NodeFlags::IMPLIED_CLASS) with `origin`,
    /// the node in the referencing namespace the class is propagated under
    /// (the reference/payload site's parent). Because that origin is stronger
    /// for an outer reference than for an inner one, the strength comparator
    /// orders an implied class's opinions by reference nesting (spec 10.4.1)
    /// without consulting layer indices.
    ///
    /// When `outer_stack` is the stage root layer stack, the fully-composed
    /// index for the implied class is grafted from `cached_indices` if present,
    /// so an implied class keeps the deep structure its own ancestral arcs gave
    /// it (a local-class chain's inherited grandchildren). Otherwise it is
    /// composed inline against `outer_stack`.
    fn propagate_implied_through_transfer(
        &mut self,
        start: usize,
        transfer: &MapFunction,
        outer_stack: &[(usize, LayerOffset)],
        depth: usize,
        origin: NodeId,
    ) -> Result<(), Error> {
        let outer_is_root = self.ambient_is_root && outer_stack == self.ambient.as_slice();

        // Snapshot the class arcs before composing any implied node, since
        // composing appends to `self.output`.
        let class_nodes: Vec<(Path, Path, ArcType)> = self.output[start..]
            .iter()
            .filter(|n| n.arc == ArcType::Inherit || n.arc == ArcType::Specialize)
            .map(|n| {
                let prim = n
                    .map_to_root
                    .map_source_to_target(&n.path)
                    .unwrap_or_else(|| n.path.clone());
                (n.path.clone(), prim, n.arc)
            })
            .collect();

        for (class_path, inheriting_prim, arc) in &class_nodes {
            let Some(implied_path) = transfer.map_source_to_target(class_path) else {
                continue;
            };

            // Skip a node-to-itself arc: if the implied class's site is already
            // being composed up the call stack, adding it would self-reference.
            // C++ PCP guards against this in `_AddClassBasedArc`; it surfaces
            // when an implied inherit propagates through a relocated prim back
            // onto its own site (bug 69932).
            if let Some(&(root_layer, _)) = outer_stack.first() {
                if self.eval_stack.contains(&(root_layer, implied_path.clone())) {
                    continue;
                }
            }

            // Prefer the fully-composed cached index: a stage-prim implied class
            // at root ambient is composed by the cache (following its own arcs),
            // and the cache precaches inherit targets so it is available here
            // regardless of traversal order. Graft its subtree onto the
            // inheriting prim — a root node maps the class namespace onto
            // `inheriting_prim`, internal nodes keep their own `map_to_parent`.
            // `cached_indices` outlives `self`, so its borrow does not block the
            // `self.output` mutations below.
            //
            // An implied inherit attaches under the inheriting prim's local root
            // node, sibling to the reference/payload it was implied through. The
            // strength comparator then ranks it ahead of that arc by arc type
            // (inherit beats reference, spec 10.4.1 / C++ `_AddClassBasedArc`).
            // An implied specialize stays an orphan so `finalize_strength_order`
            // can move it to the globally-weak band.
            //
            // The class's site path maps to `inheriting_prim`. The local root
            // carries the prim's own opinions with an identity `map_to_root`, so
            // anchoring there leaves the composed mapping (and value resolution)
            // unchanged — only the node's tree position, and thus strength,
            // moves. An orphan (no local opinion) keeps the same identity-rooted
            // mapping.
            let implied_parent = if *arc == ArcType::Inherit {
                self.output.local_root()
            } else {
                NodeId::INVALID
            };
            let anchored = |path: &Path| MapFunction::from_pair_identity(path.clone(), inheriting_prim.clone());

            if outer_is_root {
                if let Some(cached) = self.cached_indices.get(&implied_path) {
                    // Graft the cached class subtree onto the inheriting prim: a
                    // root/orphan node maps the class namespace onto
                    // `inheriting_prim`; every node is tagged implied.
                    Self::graft_subtree(
                        &mut self.output,
                        &mut self.seen,
                        cached,
                        *arc,
                        *arc == ArcType::Specialize,
                        implied_parent,
                        |node| anchored(&node.path),
                        |output, new_id| output.mark_implied(new_id, origin),
                    );
                    continue;
                }
            }

            // Not a cached stage prim (composing within a referenced layer
            // stack): the class is local to that stack, so compose it inline
            // against `outer_stack`.
            let before = self.output.len();
            let map = anchored(&implied_path);
            self.eval_site(&implied_path, outer_stack, *arc, depth + 1, implied_parent, map, &[])?;
            for id in before..self.output.len() {
                self.output.mark_implied(NodeId(id as u32), origin);
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Shared helpers (used by IndexBuilder and Stage)
// ---------------------------------------------------------------------------

/// Folds list-op opinions, collected strongest-to-weakest, into a single
/// resolved list (spec 12.2.6): each weaker op is composed under the stronger
/// ones. `compose_over` short-circuits on an explicit op, so a stronger
/// explicit opinion replaces all weaker contributions.
fn compose_list_ops<T: Default + Clone + PartialEq>(ops: &[sdf::ListOp<T>]) -> Vec<T> {
    let mut result = Vec::new();
    for op in ops.iter().rev() {
        result = op.compose_over(&result);
    }
    result
}

/// Expands an internal reference target by inserting variant segments from
/// the context path.
///
/// If the context is `/Model{vset=with_children}Foo` and the target is
/// `/Model/_prototype`, returns `[/Model{vset=with_children}_prototype]`.
fn variant_expanded_targets(context: &Path, target: &Path) -> Vec<Path> {
    let ctx = context.as_str();
    if !ctx.contains('{') {
        return Vec::new();
    }
    let tgt = target.as_str();
    let mut results = Vec::new();

    let mut pos = 0;
    while let Some(open) = ctx[pos..].find('{') {
        let open = pos + open;
        let Some(close) = ctx[open..].find('}') else {
            break;
        };
        let close = open + close;
        let prim_prefix = &ctx[..open];
        let variant_segment = &ctx[open..=close];

        if let Some(after_prefix) = tgt.strip_prefix(prim_prefix) {
            if !after_prefix.starts_with('{') {
                // The inserted variant segment supplies the namespace boundary,
                // so the child attaches directly after it (canonical form
                // `/Prim{v=s}Child`); drop the target's `/` separator.
                let child = after_prefix.strip_prefix('/').unwrap_or(after_prefix);
                let expanded = format!("{prim_prefix}{variant_segment}{child}");
                if let Ok(p) = Path::new(&expanded) {
                    results.push(p);
                }
            }
        }

        pos = close + 1;
    }

    results
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
    layers: &[sdf::Layer],
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
        for &(layer, _) in node.layer_stack() {
            if let Ok(value) = layers[layer].get(&node.path, FieldKey::VariantSelection.as_str()) {
                if let Value::VariantSelectionMap(map) = value.into_owned() {
                    for (set_name, selection) in map {
                        selections.entry(set_name).or_insert(selection);
                    }
                }
            }
        }
    }

    // For variant sets without an explicit selection, try the fallback map
    // first, then fall back to the first variant name in the set.
    for node in &ordered {
        for &(layer, _) in node.layer_stack() {
            let data = &layers[layer];
            let Ok(value) = data.get(&node.path, ChildrenKey::VariantSetChildren.as_str()) else {
                continue;
            };
            let Value::TokenVec(set_names) = value.into_owned() else {
                continue;
            };
            for set_name in set_names {
                let Entry::Vacant(entry) = selections.entry(set_name) else {
                    continue;
                };
                let set_path = node.path.append_variant_selection(entry.key(), "");
                let Ok(val) = data.get(&set_path, ChildrenKey::VariantChildren.as_str()) else {
                    continue;
                };
                let Value::TokenVec(variants) = val.into_owned() else {
                    continue;
                };
                // Try fallback selections in order — use the first one that
                // exists in this variant set.
                let fallbacks = variant_fallbacks.get(entry.key());
                if let Some(fb) = fallbacks.iter().find(|fb| variants.contains(fb)) {
                    entry.insert(fb.clone());
                    continue;
                }
                // No fallback matched — default to the first variant.
                if let Some(first) = variants.into_iter().next() {
                    entry.insert(first);
                }
            }
        }
    }

    selections
}

/// Maps time sample keys from layer time to stage time through `offset`
/// (spec 12.3.2.1): `stage_t = offset + scale * layer_t`. Returns the samples
/// untouched when `offset` is the identity.
fn retime_samples(samples: sdf::TimeSampleMap, offset: LayerOffset) -> sdf::TimeSampleMap {
    if offset.is_identity() {
        return samples;
    }
    samples.into_iter().map(|(t, value)| (offset.apply(t), value)).collect()
}

/// Maps the stage-time component of clip `active`/`times` pairs through the
/// layer offset of the node that authored the field.
fn retime_clip_stage_times(value: Value, offset: LayerOffset) -> Value {
    if offset.is_identity() {
        return value;
    }
    match value {
        Value::Vec2dVec(pairs) => Value::Vec2dVec(
            pairs
                .into_iter()
                .map(|[stage, data]| [offset.apply(stage), data])
                .collect(),
        ),
        other => other,
    }
}

/// Applies `strong over weak` dictionary composition in place.
///
/// Keys authored in the stronger dictionary win. If both dictionaries hold a
/// dictionary at the same key, those nested dictionaries are composed
/// recursively; otherwise the stronger value is kept.
fn dictionary_over(stronger: &mut HashMap<String, Value>, weaker: HashMap<String, Value>) {
    for (key, weaker_value) in weaker {
        match stronger.entry(key) {
            Entry::Occupied(mut entry) => {
                if let (Value::Dictionary(strong_dict), Value::Dictionary(weak_dict)) = (entry.get_mut(), weaker_value)
                {
                    dictionary_over(strong_dict, weak_dict);
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(weaker_value);
            }
        }
    }
}

/// Composes a list-op field across nodes' layer stacks, returning the
/// flattened list.
///
/// Each node fans out into its contributing sublayers, strongest first.
/// `decode` turns a raw field value into a `ListOp<T>` (returning `None` for a
/// wrong-typed value, treated as no opinion); `retime` rewrites each item by
/// the contributing sublayer's offset (a no-op for offset-free arcs). Backend
/// decode errors surface to the caller.
fn compose_list_op_in<T, D, R>(
    nodes: &[Node],
    field: &str,
    layers: &[sdf::Layer],
    decode: D,
    mut retime: R,
) -> Result<Vec<T>>
where
    T: Default + Clone + PartialEq,
    D: Fn(Value) -> Option<ListOp<T>>,
    R: FnMut(&mut T, LayerOffset),
{
    let mut combined: Option<ListOp<T>> = None;

    for node in nodes {
        for &(layer, sub) in node.layer_stack() {
            let Some(value) = layers[layer].try_get(&node.path, field)? else {
                continue;
            };
            let Some(mut list_op) = decode(value.into_owned()) else {
                continue;
            };
            if !sub.is_identity() {
                list_op.iter_mut().for_each(|item| retime(item, sub));
            }
            combined = Some(match combined {
                Some(stronger) => stronger.combined_with(&list_op),
                None => list_op,
            });
        }
    }

    Ok(combined.map(|op| op.reduced().flatten()).unwrap_or_default())
}

/// Composes an offset-free list-op field (inherits, specializes) by decoding
/// each opinion through `TryInto` and combining across the layer stack.
fn compose_arc_list_in<T: Default + Clone + PartialEq>(
    nodes: &[Node],
    field: FieldKey,
    layers: &[sdf::Layer],
) -> Result<Vec<T>>
where
    Value: TryInto<ListOp<T>>,
{
    compose_list_op_in(nodes, field.as_str(), layers, |v| v.try_into().ok(), |_, _| {})
}

/// Composes the `references` list-op, folding each authoring sublayer's offset
/// into its references' layer offsets (C++ `PcpComposeSiteReferences`). A
/// reference brought in by a sublayer with a non-identity offset retimes its
/// target by that offset, which the per-site node otherwise carries only per
/// member.
fn compose_references_in(nodes: &[Node], layers: &[sdf::Layer]) -> Result<Vec<Reference>> {
    compose_list_op_in(
        nodes,
        FieldKey::References.as_str(),
        layers,
        |v| v.try_into().ok(),
        |r: &mut Reference, sub| r.layer_offset = sub.concatenate(&r.layer_offset),
    )
}

/// Collects payloads from nodes, handling both single `Payload` and
/// `PayloadListOp`. Each authoring sublayer's offset is folded into its
/// payloads' layer offsets, mirroring [`compose_references_in`].
fn collect_payloads_in(nodes: &[Node], layers: &[sdf::Layer]) -> Result<Vec<Payload>> {
    compose_list_op_in(
        nodes,
        FieldKey::Payload.as_str(),
        layers,
        |v| match v {
            Value::Payload(p) => Some(PayloadListOp {
                explicit: true,
                explicit_items: vec![p],
                ..Default::default()
            }),
            Value::PayloadListOp(op) => Some(op),
            _ => None,
        },
        |p: &mut Payload, sub| p.layer_offset = Some(sub.concatenate(&p.layer_offset.unwrap_or_default())),
    )
}

/// Finds a layer index whose identifier matches `asset_path`.
///
/// Tries an exact match first, then suffix-matches at a path-separator
/// boundary. For relative paths that traverse parent directories (`../foo`,
/// `..\foo`), these strategies fail against canonical absolute identifiers.
/// The resolver anchors the path against each candidate identifier so that
/// custom asset resolution backends work correctly without any filesystem
/// access in this function.
pub(super) fn find_layer(asset_path: &str, layers: &[sdf::Layer], resolver: &dyn Resolver) -> Option<usize> {
    use crate::ar::ResolvedPath;

    let asset_path_ref = std::path::Path::new(asset_path);
    let needle = asset_path_ref.strip_prefix(".").unwrap_or(asset_path_ref);

    // Fast path: exact or suffix match against canonical identifiers.
    for (i, layer) in layers.iter().enumerate() {
        let identifier = std::path::Path::new(layer.identifier.as_str());
        if identifier == needle || identifier.ends_with(needle) {
            return Some(i);
        }
    }

    // Relative paths traversing parent directories need anchoring. Delegate to
    // the resolver so custom AR backends override path handling without any
    // filesystem access here.
    if needle.starts_with("..") {
        for anchor_layer in layers {
            let anchor = ResolvedPath::new(PathBuf::from(&anchor_layer.identifier));
            let resolved = resolver.create_identifier(asset_path, Some(&anchor));
            if let Some(pos) = layers.iter().position(|layer| layer.identifier == resolved) {
                return Some(pos);
            }
        }
    }

    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;
    use crate::layer::Collector;

    use anyhow::Result;

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

    /// Loads layers into a `Vec<sdf::Layer>` for PrimIndex::build.
    fn load_layers(path: &str) -> Result<Vec<sdf::Layer>> {
        let resolver = DefaultResolver::new();
        Collector::new(&resolver).collect(path)
    }

    /// Builds a prim index for a given path string.
    fn build(stack: &LayerStack, prim: &str) -> PrimIndex {
        build_with_fallbacks(stack, prim, VariantFallbackMap::new())
    }

    /// Builds a prim index with variant fallbacks applied.
    fn build_with_fallbacks(stack: &LayerStack, prim: &str, fallbacks: VariantFallbackMap) -> PrimIndex {
        let path = Path::from(prim);
        let mut ctx = if let Some(parent) = path.parent() {
            if parent != Path::abs_root() {
                let parent_index = PrimIndex::build_with_context(&parent, stack, &CompositionContext::default())
                    .expect("parent index build failed");
                parent_index.context_for_children(stack, &CompositionContext::default())
            } else {
                CompositionContext::default()
            }
        } else {
            CompositionContext::default()
        };
        ctx.variant_fallbacks = fallbacks;
        PrimIndex::build_with_context(&path, stack, &ctx).expect("index build failed")
    }

    /// Helper: loads layers and creates a [`LayerStack`].
    fn load_stack(path: &str) -> anyhow::Result<LayerStack> {
        let layers = load_layers(path)?;
        Ok(LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true))
    }

    /// Builds a single-layer stack from in-memory `root.usd` data.
    fn one_layer_stack(root: Box<dyn sdf::AbstractData>) -> LayerStack {
        let layers = vec![sdf::Layer::new("root.usd", root)];
        LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true)
    }

    /// Builds a two-layer stack from in-memory `root.usd` + `ref.usd` data.
    fn two_layer_stack(root: Box<dyn sdf::AbstractData>, refl: Box<dyn sdf::AbstractData>) -> LayerStack {
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("ref.usd", refl)];
        LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true)
    }

    #[test]
    fn single_layer_root_node() -> Result<()> {
        let stack = load_stack(&composition_path("active.usda"))?;
        let index = build(&stack, "/World");

        assert_eq!(index.nodes().count(), 1);
        assert_eq!(index.nodes().next().unwrap().layer_index(), 0);
        assert_eq!(index.nodes().next().unwrap().arc, ArcType::Root);
        Ok(())
    }

    #[test]
    fn sublayer_site_layer_order() -> Result<()> {
        let stack = load_stack(&fixture_path("sublayer_override.usda"))?;
        let index = build(&stack, "/World");

        let ns: Vec<_> = index.nodes().collect();
        assert_eq!(ns.len(), 1, "one per-site node spans both sublayers");
        assert_eq!(ns[0].arc, ArcType::Root);
        let layers: Vec<usize> = ns[0].layers().map(|(li, _)| li).collect();
        assert_eq!(layers, vec![0, 1], "stronger sublayer first");
        Ok(())
    }

    #[test]
    fn prim_only_in_stronger_layer() -> Result<()> {
        let stack = load_stack(&fixture_path("sublayer_override.usda"))?;
        let index = build(&stack, "/World/Sphere");

        assert_eq!(index.nodes().count(), 1);
        assert_eq!(index.nodes().next().unwrap().layer_index(), 0);
        Ok(())
    }

    #[test]
    fn nonexistent_prim_empty_index() -> Result<()> {
        let stack = load_stack(&composition_path("active.usda"))?;
        let index = build(&stack, "/DoesNotExist");

        assert!(index.is_empty());
        Ok(())
    }

    #[test]
    fn reference_arc_present() -> Result<()> {
        let stack = load_stack(&fixture_path("ref_external.usda"))?;
        let index = build(&stack, "/World/MyPrim");

        assert!(index.nodes().any(|n| n.arc == ArcType::Reference));
        Ok(())
    }

    #[test]
    fn empty_reference_target_culled() -> Result<()> {
        // /A references a prim the target layer never defines.
        let root = parse_usda("#usda 1.0\ndef \"A\" ( references = @base.usd@</Empty> ) {\n  custom double x = 1\n}\n");
        let base = parse_usda("#usda 1.0\ndef \"Other\" {}\n");
        let layers = vec![sdf::Layer::new("root.usd", root), sdf::Layer::new("base.usd", base)];
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/A");

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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let index = build(&stack, "/Model/Sub");
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
        let stack = two_layer_stack(root, refl);
        let index = build(&stack, "/Model");
        assert!(
            index
                .nodes()
                .any(|n| n.arc == ArcType::Variant && n.path.as_str().contains("{v=b}")),
            "selected variant from the referenced layer must be composed"
        );
        Ok(())
    }

    /// Like the above but the variant set arrives through an internal reference
    /// (same layer stack), which the builder grafts via `merge_full_index`.
    #[test]
    fn variant_from_internal_reference() -> Result<()> {
        let root = parse_usda(
            "#usda 1.0\ndef \"Base\" (\n  add variantSets = \"v\"\n) {\n  variantSet \"v\" = {\n    \"a\" { custom string x = \"a\" }\n    \"b\" { custom string x = \"b\" }\n  }\n}\ndef \"Model\" (\n  references = </Base>\n  variants = { string v = \"b\" }\n) {}\n",
        );
        let stack = one_layer_stack(root);
        let index = build(&stack, "/Model");
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
        let stack = two_layer_stack(root, refl);
        let index = build(&stack, "/Model");
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

    /// The builder records structural parent/child links: a reference node hangs
    /// under a root node, and every stored parent agrees with its child list.
    #[test]
    fn structural_links_consistent() -> Result<()> {
        let stack = load_stack(&fixture_path("ref_external.usda"))?;
        let index = build(&stack, "/World/MyPrim");

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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let index = build(&stack, "/Model");
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/Model");

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
        let stack = load_stack(&composition_path("class_inherit.usda"))?;
        let index = build(&stack, "/World/cubeWithoutSetColor");

        assert!(index.nodes().any(|n| n.arc == ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn inherit_root_is_strongest() -> Result<()> {
        let stack = load_stack(&composition_path("class_inherit.usda"))?;
        let index = build(&stack, "/World/cubeWithSetColor");
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
        let stack = load_stack(&path)?;
        let index = build(&stack, "/World/Sphere");

        assert!(index.nodes().any(|n| n.arc == ArcType::Variant));

        let variant_node = index.nodes().find(|n| n.arc == ArcType::Variant).unwrap();
        assert_eq!(variant_node.path.as_str(), "/World/Sphere{size=small}");
        Ok(())
    }

    #[test]
    fn specialize_arc_present() -> Result<()> {
        let stack = load_stack(&composition_path("inherit_and_specialize.usda"))?;
        let index = build(&stack, "/World/cubeScene/specializes");

        assert!(index.nodes().any(|n| n.arc == ArcType::Specialize));
        Ok(())
    }

    #[test]
    fn find_layer_exact_match() -> Result<()> {
        let resolver = DefaultResolver::new();
        let layers = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer(&layers[0].identifier, &layers, &resolver).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_suffix_match() -> Result<()> {
        let resolver = DefaultResolver::new();
        let layers = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("ref_target.usda", &layers, &resolver).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_relative_child() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let asset_dir = tmp.path().join("asset");
        std::fs::create_dir_all(&asset_dir)?;
        let model = asset_dir.join("model.usda");
        std::fs::write(&model, b"placeholder")?;

        let resolver = DefaultResolver::new();
        let layers = vec![sdf::Layer::new(
            model.canonicalize()?.to_string_lossy(),
            Box::new(sdf::Data::new()),
        )];
        assert_eq!(find_layer("./asset/model.usda", &layers, &resolver), Some(0));
        Ok(())
    }

    #[test]
    fn find_layer_no_partial_name_match() -> Result<()> {
        let resolver = DefaultResolver::new();
        let layers = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("target.usda", &layers, &resolver).is_none());
        Ok(())
    }

    #[test]
    fn find_layer_not_found() -> Result<()> {
        let resolver = DefaultResolver::new();
        let layers = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("nonexistent.usda", &layers, &resolver).is_none());
        Ok(())
    }

    /// Relative `../` paths must be anchored against each candidate
    /// identifier's location via the resolver. Without this, a reference
    /// like `../Materials/Materials.usd` authored inside a prop USD silently
    /// fails every composition lookup with `UnresolvedLayer`.
    #[test]
    fn find_layer_relative_parent_anchored() -> Result<()> {
        let tmp = tempfile::tempdir()?;
        let a_dir = tmp.path().join("Props");
        let b_dir = tmp.path().join("Materials");
        std::fs::create_dir_all(&a_dir)?;
        std::fs::create_dir_all(&b_dir)?;
        let a = a_dir.join("link.usd");
        let b = b_dir.join("Materials.usd");
        std::fs::write(&a, b"placeholder")?;
        std::fs::write(&b, b"placeholder")?;
        let layers = vec![
            sdf::Layer::new(a.canonicalize()?.to_string_lossy(), Box::new(sdf::Data::new())),
            sdf::Layer::new(b.canonicalize()?.to_string_lossy(), Box::new(sdf::Data::new())),
        ];
        let resolver = DefaultResolver::new();
        // `../Materials/Materials.usd` written inside `Props/link.usd`
        // should resolve to identifier index 1 (the Materials.usd).
        assert_eq!(find_layer("../Materials/Materials.usd", &layers, &resolver), Some(1));
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
        let stack = load_stack(&path)?;
        let index = build(&stack, "/Root");

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

        let a_idx = find_layer("A.usd", &stack.layers, &*stack.resolver).unwrap();
        let a_attr_path = Path::new("/A.A_attr").unwrap();
        assert!(
            stack.layer(a_idx).has_spec(&a_attr_path),
            "A.usd should have spec at /A.A_attr"
        );
        Ok(())
    }

    /// Variant that introduces a specializes arc should propagate the
    /// specialized prim's variant opinions to the composing prim.
    #[test]
    fn specializes_from_variant() -> Result<()> {
        let path = format!(
            "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/SpecializesAndVariants_root/usda/root.usd",
            manifest_dir()
        );
        let stack = load_stack(&path)?;
        let index = build(&stack, "/B");

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
        let stack = load_stack(&path)?;

        assert!(
            find_layer("camera_perspective.usd", &stack.layers, &*stack.resolver).is_some(),
            "camera_perspective.usd should be collected from variant reference"
        );

        let index = build(&stack, "/main_cam/Lens");
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
        let stack = load_stack(&path)?;
        let index = build(&stack, "/bob");

        assert!(
            index.nodes().any(|n| n.path.as_str().contains("{geotype=cube}")),
            "should have geotype=cube variant node from inherited selection"
        );
        Ok(())
    }

    // --- Error reporting ---

    fn parse_usda(text: &str) -> Box<dyn sdf::AbstractData> {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        Box::new(crate::usda::TextReader::from_data(data))
    }

    /// Composition depth exceeding the limit returns `Error::ArcCycle`
    /// instead of panicking.
    #[test]
    fn arc_cycle_returns_error() -> Result<()> {
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let result = PrimIndex::build_with_context(&Path::from("/Root"), &stack, &CompositionContext::default());
        assert!(
            matches!(result, Err(Error::ArcCycle { .. })),
            "expected ArcCycle error, got {result:?}"
        );
        Ok(())
    }

    /// Referencing a layer not in the collected set returns `Error::UnresolvedLayer`.
    #[test]
    fn unresolved_layer_returns_error() -> Result<()> {
        let layer = parse_usda(
            r#"#usda 1.0
def "Prim" (
    references = @nonexistent.usd@
)
{
}
"#,
        );
        let layers = vec![sdf::Layer::new("test.usda", layer)];
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let result = PrimIndex::build_with_context(&Path::from("/Prim"), &stack, &CompositionContext::default());
        assert!(
            matches!(result, Err(Error::UnresolvedLayer { .. })),
            "expected UnresolvedLayer error, got {result:?}"
        );
        Ok(())
    }

    /// Referencing a layer without defaultPrim (and no explicit prim path)
    /// returns `Error::MissingDefaultPrim`.
    #[test]
    fn missing_default_prim_returns_error() -> Result<()> {
        let root = parse_usda(
            r#"#usda 1.0
def "Prim" (
    references = @target.usda@
)
{
}
"#,
        );
        let target = parse_usda("#usda 1.0\ndef \"Foo\" {}\n");
        let layers = vec![
            sdf::Layer::new("root.usda", root),
            sdf::Layer::new("target.usda", target),
        ];
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let result = PrimIndex::build_with_context(&Path::from("/Prim"), &stack, &CompositionContext::default());
        assert!(
            matches!(result, Err(Error::MissingDefaultPrim { .. })),
            "expected MissingDefaultPrim error, got {result:?}"
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

    /// When no fallback is provided and no authored selection exists, the first
    /// variant in the set should be selected by default.
    #[test]
    fn variant_default_without_fallback() -> Result<()> {
        let stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let index = build(&stack, "/NoSelection");
        let paths = variant_paths(&index);
        assert!(
            paths.iter().any(|p| p.contains("{shadingComplexity=full}")),
            "default should be 'full' (first variant): got {paths:?}"
        );
        Ok(())
    }

    /// When a fallback map specifies "simple" as the preferred fallback, and no
    /// authored selection exists, the composition should select "simple".
    #[test]
    fn variant_fallback_overrides_default() -> Result<()> {
        let stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["simple"]);
        let index = build_with_fallbacks(&stack, "/NoSelection", fb);
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
        let stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["none"]);
        let index = build_with_fallbacks(&stack, "/Root", fb);
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
        let stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["ultra", "simple"]);
        let index = build_with_fallbacks(&stack, "/NoSelection", fb);
        let paths = variant_paths(&index);
        assert!(
            paths.iter().any(|p| p.contains("{shadingComplexity=simple}")),
            "should skip 'ultra' and use 'simple': got {paths:?}"
        );
        Ok(())
    }

    /// When all fallback names are invalid, the first variant in the set is used.
    #[test]
    fn variant_fallback_all_invalid_uses_first() -> Result<()> {
        let stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["ultra", "mega"]);
        let index = build_with_fallbacks(&stack, "/NoSelection", fb);
        let paths = variant_paths(&index);
        assert!(
            paths.iter().any(|p| p.contains("{shadingComplexity=full}")),
            "all fallbacks invalid — should use first variant 'full': got {paths:?}"
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
        let mut g = PrimIndexGraph::default();
        let root = g.add_child(NodeId::INVALID, 0, p("/A"), ArcType::Root, id.clone(), false);
        let inh = g.add_child(root, 0, p("/Class"), ArcType::Inherit, id.clone(), false);
        let r1 = g.add_child(root, 0, p("/R1"), ArcType::Reference, id.clone(), false);
        let r2 = g.add_child(root, 0, p("/R2"), ArcType::Reference, id.clone(), false);

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
        let deep = g.add_child(root, 0, p("/D"), ArcType::Reference, id.clone(), false);
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

    #[test]
    fn insert_relocate_node_before_references() {
        let p = |s: &str| Path::from(s.to_string());
        let node = |arc: ArcType| Node::new(0, p("/X"), arc, MapFunction::identity(), MapFunction::identity(), false);

        let mut index = PrimIndex::default();
        index.push_node(node(ArcType::Root));
        index.push_node(node(ArcType::Inherit));
        index.push_node(node(ArcType::Variant));
        index.push_node(node(ArcType::Reference));
        index.push_node(node(ArcType::Payload));
        index.push_node(node(ArcType::Specialize));

        // Insert two relocate nodes — both should land between Variant and Reference.
        index.insert_relocate_node(node(ArcType::Relocate));
        index.insert_relocate_node(node(ArcType::Relocate));

        let arcs: Vec<ArcType> = index.nodes().map(|n| n.arc).collect();
        assert_eq!(
            arcs,
            vec![
                ArcType::Root,
                ArcType::Inherit,
                ArcType::Variant,
                ArcType::Relocate,
                ArcType::Relocate,
                ArcType::Reference,
                ArcType::Payload,
                ArcType::Specialize,
            ]
        );

        // Relocate nodes are tagged RELOCATE_SOURCE; nothing else is.
        for node in index.nodes() {
            assert_eq!(
                node.flags().contains(NodeFlags::RELOCATE_SOURCE),
                node.arc == ArcType::Relocate,
                "only relocate nodes carry RELOCATE_SOURCE"
            );
        }
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
    fn prim_stack(index: &PrimIndex, stack: &LayerStack) -> Vec<(String, String)> {
        index
            .nodes()
            .map(|n| {
                (
                    layer_name(stack.identifier(n.layer_index())).to_owned(),
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
        let stack = load_stack(&spec_composition_path("BasicSpecializes_root/usda/root.usd"))?;
        let index = build(&stack, "/Root");

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
        let stack = load_stack(&spec_composition_path("BasicSpecializes_root/usda/root.usd"))?;
        let index = build(&stack, "/MultipleSpecializes");

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
        let stack = load_stack(&spec_composition_path("BasicSpecializes_root/usda/root.usd"))?;
        let index = build(&stack, "/Basic");

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

    #[test]
    fn insert_relocate_node_appends_when_no_rps() {
        let p = |s: &str| Path::from(s.to_string());
        let node = |arc: ArcType| Node::new(0, p("/X"), arc, MapFunction::identity(), MapFunction::identity(), false);

        let mut index = PrimIndex::default();
        index.push_node(node(ArcType::Root));
        index.push_node(node(ArcType::Variant));

        index.insert_relocate_node(node(ArcType::Relocate));

        let arcs: Vec<ArcType> = index.nodes().map(|n| n.arc).collect();
        assert_eq!(arcs, vec![ArcType::Root, ArcType::Variant, ArcType::Relocate]);
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

    /// Returns `(layer_name, node_path, arc_type, offset, scale)` tuples for
    /// every node in the prim stack. The offset/scale values are the effective
    /// [`sdf::LayerOffset`] carried by the node — i.e., the composition of
    /// every arc offset and sublayer offset from the stage root down to this
    /// node's layer.
    fn offset_stack(index: &PrimIndex, stack: &LayerStack) -> Vec<(String, String, ArcType, f64, f64)> {
        index
            .nodes()
            .flat_map(|n| {
                let path = n.path.to_string();
                let arc = n.arc;
                // Expand each per-site node into one row per contributing
                // sublayer, carrying that layer's effective offset (the arc
                // offset with the sublayer offset composed on top).
                n.layers().map(move |(li, off)| {
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

    fn basic_time_offset_stack() -> anyhow::Result<LayerStack> {
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
        let stack = basic_time_offset_stack()?;
        let index = build(&stack, "/Root");
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
        let stack = basic_time_offset_stack()?;
        let index = build(&stack, "/PayloadRefPayload");
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
        let stack = basic_time_offset_stack()?;
        let index = build(&stack, "/PayloadMultiRef");
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
        let stack = basic_time_offset_stack()?;
        let index = build(&stack, "/Root/Anim");
        let got = offset_stack(&index, &stack);

        assert!(
            got.contains(&("B.usd".into(), "/Model/Anim".into(), ArcType::Reference, 30.0, 1.0)),
            "missing /Model/Anim at effective (30, 1): got {got:?}"
        );
        Ok(())
    }

    #[test]
    fn retime_samples_offset_scale() {
        let samples: sdf::TimeSampleMap = vec![(1.0, Value::Double(0.0)), (5.0, Value::Double(1.0))];
        let retimed = retime_samples(samples, LayerOffset::new(10.0, 2.0));
        let times: Vec<f64> = retimed.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![12.0, 20.0]);
    }

    #[test]
    fn retime_samples_identity_passthrough() {
        let samples: sdf::TimeSampleMap = vec![(1.0, Value::Double(0.0))];
        let retimed = retime_samples(samples.clone(), LayerOffset::IDENTITY);
        assert_eq!(retimed, samples);
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = PrimIndex::build_with_context(&Path::from("/Root"), &stack, &CompositionContext::default())?;

        let samples = index
            .resolve_time_samples(&stack, Some(".radius"))?
            .expect("retimed samples");
        let times: Vec<f64> = samples.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![12.0, 20.0]);
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/Root");
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/Root");
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/Root");
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/P");

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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/P");

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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);
        let index = build(&stack, "/P");

        assert_eq!(index.clip_sets_order(&stack)?, Some(Vec::new()));
        Ok(())
    }
}
