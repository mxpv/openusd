//! Task-queue prim indexer (C++ `Pcp_PrimIndexer` port).
//!
//! [`Indexer`] grows a [`PrimIndexGraph`] node-by-node by draining a
//! priority-ordered task queue, mirroring C++ `Pcp_BuildPrimIndex`. It is the
//! replacement for the recursive `IndexBuilder`: rather than the builder's
//! global `(layer, path, arc)` dedup set, the queue follows each composition arc
//! structurally, so reference/payload diamonds — a shared target reached by two
//! arc paths — contribute a node on each path.
//!
//! Ancestral opinions enter through the graph-clone seed (C++
//! `_BuildInitialPrimIndexFromAncestor`): the parent prim's composed graph is
//! cloned and every site path deepened by the child name
//! ([`PrimIndexGraph::append_child_name_to_all_sites`]), so the references and
//! payloads an ancestor introduced are re-evaluated at the deepened path by the
//! same queue. Each node carries its full site layer stack, so deepening only
//! needs to recompute which layers author a spec (`has_specs`).
//!
//! Inherits compose as class-based arcs (C++ `_EvalNodeInherits` →
//! `_AddClassBasedArc`), and a class brought in through a reference is mirrored
//! into the referencing namespace by implied-class propagation (C++
//! `_EvalImpliedClasses` → `_EvalImpliedClassTree`) driven by the queue: an
//! `EvalImpliedClasses` task carries a node's class-based children one level up,
//! repeating until the class reaches the root namespace.
//!
//! An arc whose target is not a root prim is composed as its own sub-index,
//! including the opinions above the target, then grafted under the arc (C++
//! `_AddArc`'s `includeAncestralOpinions` branch → `InsertChildSubgraph`). A
//! borrowed [`Frame`] chain threads the parent graphs back through the nested
//! builds so duplicate-node skipping (C++ `_AddArc`'s `skipDuplicateNodes`)
//! drops a class reached both directly and through an ancestral reference,
//! keeping it grafted once. Ancestral inherits ride the graph-clone seed
//! alongside references and payloads, so a class an ancestor introduces
//! re-evaluates at the child path.
//!
//! The indexer is being ported arc-by-arc. `build_with_cache_in` composes a
//! prim with the indexer when [`Indexer::build`] reports support and otherwise
//! falls back to the recursive builder. Ported so far: the root local site;
//! reference, payload, and inherit arcs to either a root-level or a sub-root
//! target (with the ancestral sub-index and duplicate-node skipping); internal
//! references and `defaultPrim` targets; ancestral reference/payload/inherit
//! propagation through the graph-clone seed; and implied classes. Features that
//! still abandon the prim ([`Indexer::build`] returns `None`): specializes,
//! variants, relocates (any prim composing an inherit while `layerRelocates` is
//! present, or whose ancestor graph carries a variant/specialize/relocate node
//! the seed cannot deepen), and instances. Each deferral point carries its
//! reason inline.

use std::collections::BinaryHeap;
use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf::schema::FieldKey;
use crate::sdf::{AbstractData, LayerOffset, Path, Value};

use super::graph::{ArcType, NodeFlags, NodeId, PrimIndexGraph};
use super::index::{
    collect_payloads_in, compose_arc_list_in, compose_references_in, find_layer, CompositionContext, PrimIndex,
};
use super::mapping::MapFunction;
use super::{Error, LayerStack};

/// Maximum composition-arc nesting before the prim is abandoned to the
/// recursive builder (which reports it as a cycle). Matches the builder's
/// `MAX_COMPOSITION_DEPTH`.
const MAX_DEPTH: usize = 100;

/// Whether an arc introduces a class hierarchy node — an inherit or a
/// specializes (C++ `PcpIsClassBasedArc`). Implied-class propagation acts on
/// these.
fn is_class_based(arc: ArcType) -> bool {
    matches!(arc, ArcType::Inherit | ArcType::Specialize)
}

/// Whether `path` is a root prim (`/Foo`), whose composition needs no ancestral
/// opinions because its only namespace ancestor is the pseudo-root.
fn is_root_prim(path: &Path) -> bool {
    path.parent().is_some_and(|p| p == Path::abs_root())
}

/// A borrowed parent-frame in the recursive sub-index build chain (C++
/// `PcpPrimIndex_StackFrame`).
///
/// When an arc target needs ancestral opinions (`includeAncestralOpinions`),
/// the target is composed as its own sub-index by a nested [`Indexer`], then
/// grafted under the arc's parent. The nested indexer carries a `Frame` back to
/// the graph that introduced the arc, so cross-frame duplicate-node skipping
/// (C++ `_AddArc`'s `skipDuplicateNodes` search) can reach the parent graph's
/// already-composed nodes — the mechanism that keeps a class reached both
/// directly and through an ancestral reference from grafting twice.
struct Frame<'f> {
    /// The path the sub-index this frame introduces was requested at (C++
    /// `PcpPrimIndex_StackFrame::requestedSite.path`), used to deepen a
    /// cross-frame site lookup by the suffix the request adds.
    requested_path: Path,
    /// The path the parent graph is rooted at (its local-root site path), the
    /// prefix replaced out of a cross-frame lookup.
    root_path: Path,
    /// The parent graph, searched for an existing node at the (prefix-replaced)
    /// site during duplicate-node skipping.
    graph: &'f PrimIndexGraph,
    /// The next parent frame, or `None` at the top-level build.
    previous: Option<&'f Frame<'f>>,
}

/// Fields whose presence at a composed site means the prim pulls in an arc or
/// variant a later phase ports. While any is authored the indexer abandons the
/// prim to the recursive builder rather than composing a half-resolved result.
const UNSUPPORTED_FIELDS: [FieldKey; 3] = [
    FieldKey::Specializes,
    FieldKey::VariantSetNames,
    FieldKey::VariantSelection,
];

/// A queued unit of composition work on one node (C++ `Pcp_PrimIndexer::Task`).
///
/// `BinaryHeap` pops the greatest `Task`, and the derived order compares
/// [`kind`](Self::kind) first (highest priority drains first, C++ `Task::Type`),
/// then the node index. For `EvalImpliedClasses` the higher node index — a more
/// recently added, deeper node — drains first, so a class is propagated up from
/// its descendants before its ancestors (C++ `Task::PriorityOrder`). For the
/// order-independent reference/payload/inherit tasks the node order is just a
/// deterministic tiebreak.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Task {
    kind: TaskKind,
    node: NodeId,
}

/// The ported task kinds, ordered weakest-priority first so the derived `Ord`
/// makes the heap pop the highest-priority kind first (C++ `Task::Type`, whose
/// numeric order runs strongest-to-weakest: references, payloads, inherits, then
/// implied classes).
// The `Eval` prefix mirrors the C++ `Task::Type` names.
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum TaskKind {
    /// Propagate a node's class-based children one level up toward the root.
    EvalImpliedClasses,
    /// Evaluate the inherits authored at the node's site.
    EvalNodeInherits,
    /// Evaluate the payloads authored at the node's site.
    EvalNodePayloads,
    /// Evaluate the references authored at the node's site.
    EvalNodeReferences,
}

/// Composes a single prim by draining a task queue over a composition graph
/// grown node-by-node (C++ `Pcp_PrimIndexer`).
///
/// All borrowed inputs are shared references, so each build is an independent
/// pure function over the layer stack and incoming context (Rayon-friendly —
/// see the `TODO(rayon)` on the cross-prim driver in `cache.rs`).
pub(crate) struct Indexer<'a, 'f> {
    stack: &'a LayerStack,
    ctx: &'a CompositionContext,
    /// Cached prim indices from the composition cache. The parent prim's index
    /// is read from here to seed this child's graph (C++
    /// `_BuildInitialPrimIndexFromAncestor`).
    cached_indices: &'a HashMap<Path, PrimIndex>,
    /// Layer stack the root `L` site scans (the stage root layer stack for a
    /// stage prim, or a referenced asset's sublayer stack for an arc target).
    ambient: &'a [(usize, LayerOffset)],
    /// Whether [`ambient`](Self::ambient) is the stage's root layer stack, the
    /// only case where the stage-keyed `cached_indices` apply.
    ambient_is_root: bool,
    /// The path this build composes — the graph's local-root site path. Set at
    /// the start of [`build`](Self::build) and used as the current-graph root in
    /// cross-frame duplicate-node lookups.
    build_path: Path,
    /// The parent frame for a recursive sub-index build, or `None` at the
    /// top-level build (C++ `Pcp_PrimIndexer::previousFrame`).
    frame: Option<&'f Frame<'f>>,
    /// Whether duplicate-node skipping is in force for this build, inherited
    /// from the arc that spawned the sub-index (C++ `previousFrame->skipDuplicateNodes`).
    frame_skip: bool,
    /// Sub-index nesting depth; a build exceeding [`MAX_DEPTH`] is abandoned,
    /// bounding true composition cycles.
    frame_depth: usize,
    /// The graph grown so far.
    output: PrimIndexGraph,
    /// Open composition tasks, highest priority first.
    tasks: BinaryHeap<Task>,
    /// Nodes already enqueued for `EvalImpliedClasses`, mirroring C++
    /// `taskUniq`: implied-class propagation re-reaches the same node from
    /// several arcs, so the task is deduplicated to avoid redundant work.
    implied_seen: HashSet<NodeId>,
    /// Whether any layer authors `layerRelocates`. Class arcs interact with
    /// relocates (C++ `_EvalImpliedClassTree` routes implied classes across
    /// relocate nodes); that interaction is a later phase, so while relocates
    /// are present the indexer defers any prim that composes an inherit.
    has_relocates: bool,
    /// Cleared the moment composition meets a feature a later phase ports; the
    /// build is then abandoned and the recursive builder composes the prim.
    supported: bool,
}

impl<'a, 'f> Indexer<'a, 'f> {
    pub(crate) fn new(
        stack: &'a LayerStack,
        ctx: &'a CompositionContext,
        cached_indices: &'a HashMap<Path, PrimIndex>,
        ambient: &'a [(usize, LayerOffset)],
        ambient_is_root: bool,
    ) -> Self {
        Self {
            stack,
            ctx,
            cached_indices,
            ambient,
            ambient_is_root,
            build_path: Path::abs_root(),
            frame: None,
            frame_skip: false,
            frame_depth: 0,
            output: PrimIndexGraph::default(),
            tasks: BinaryHeap::new(),
            implied_seen: HashSet::new(),
            has_relocates: stack.has_relocates,
            supported: true,
        }
    }

    /// Composes `path`, returning the graph when the prim's composition is fully
    /// within the ported feature set, or `None` when it relies on a feature a
    /// later phase ports (the caller then uses the recursive builder).
    pub(crate) fn build(mut self, path: &Path) -> Result<Option<PrimIndexGraph>, Error> {
        // Instance composition is a later phase.
        if self.ctx.within_instance {
            return Ok(None);
        }

        // A sub-index nested past the depth bound is a true composition cycle;
        // abandon the whole prim so the recursive builder reports it.
        if self.frame_depth > MAX_DEPTH {
            return Ok(None);
        }
        self.build_path = path.clone();

        // Seed the graph: a root prim starts empty (just its local site); a
        // child prim clones its parent's graph for ancestral opinions.
        if !self.seed(path)? {
            return Ok(None);
        }

        // Recompute `has_specs` at the seeded paths, abandon the prim if any
        // site authors an unported field, and enqueue the spec-bearing nodes'
        // reference/payload tasks (the root node and every cloned ancestral one).
        if !self.scan_and_enqueue()? {
            return Ok(None);
        }

        // Drain the queue. Each handler may append nodes and enqueue further
        // work; an unported feature clears `supported` and abandons the prim.
        while let Some(task) = self.tasks.pop() {
            match task.kind {
                TaskKind::EvalNodeReferences | TaskKind::EvalNodePayloads => self.eval_arcs(task.node, task.kind)?,
                TaskKind::EvalNodeInherits => self.eval_node_inherits(task.node)?,
                TaskKind::EvalImpliedClasses => {
                    self.implied_seen.remove(&task.node);
                    self.eval_implied_classes(task.node)?;
                }
            }
            if !self.supported {
                return Ok(None);
            }
        }

        self.output.finalize_strength_order();
        Ok(Some(self.output))
    }

    /// Builds the initial graph for `path` (C++ `_BuildInitialPrimIndexFromAncestor`
    /// plus the root-node setup). Returns `false` to abandon the prim.
    ///
    /// A root prim (parent is the pseudo-root) seeds an empty graph with just its
    /// local site. A child prim clones its already-composed parent's graph and
    /// deepens every site path by the child name, so the references and payloads
    /// an ancestor introduced re-evaluate at this prim's depth.
    fn seed(&mut self, path: &Path) -> Result<bool, Error> {
        let parent = path.parent();
        let needs_ancestor = matches!(&parent, Some(p) if p != &Path::abs_root());

        if !needs_ancestor {
            // Root prim: synthetic inert root plus a local site scanning ambient.
            self.output.init_root(path.clone());
            self.add_local_root(path);
            return Ok(true);
        }

        let parent = parent.expect("checked by needs_ancestor");
        // The parent's composed graph seeds this child. At the top-level build
        // in the stage root layer stack it is read from the stage cache; in a
        // recursive sub-index build it is composed afresh in the same ambient,
        // reusing the frame chain so duplicate-node skipping (C++
        // `_BuildInitialPrimIndexFromAncestor`'s else-branch
        // `Pcp_BuildPrimIndex(parentSite, …, previousFrame)`) applies.
        let graph = if self.frame.is_none() && self.ambient_is_root {
            let Some(parent_index) = self.cached_indices.get(&parent) else {
                return Ok(false);
            };
            parent_index.graph().clone()
        } else {
            let Some(graph) = self.compose_ancestral_subindex(&parent)? else {
                return Ok(false);
            };
            graph
        };

        // Only a graph composed entirely of ported arcs can be deepened
        // structurally. A culled or variant/specialize/relocate node means the
        // parent relied on an unported feature. Inherit (and the implied-class
        // placeholders, which are inert) deepen and re-evaluate at the child
        // path through the queue, carrying ancestral classes to the child.
        if graph.nodes.iter().any(|n| {
            !n.is_inert()
                && (n.is_culled()
                    || !matches!(
                        n.arc,
                        ArcType::Root | ArcType::Reference | ArcType::Payload | ArcType::Inherit
                    ))
        }) {
            return Ok(false);
        }
        self.output = graph;
        // Deepening keeps each cloned node's full site layer stack; the set of
        // layers that author a spec changes at the deeper path, so `has_specs`
        // is recomputed for every node by `scan_and_enqueue`.
        self.output.append_child_name_to_all_sites(path);

        // The parent may have had no local opinion, leaving no Root site to
        // become this child's local root. Ensure one exists so a local opinion
        // authored only at this child still composes.
        if !self.output.local_root().is_valid() {
            self.add_local_root(path);
        }
        Ok(true)
    }

    /// Adds the prim's local site: a `Root` node over the full ambient layer
    /// stack. Its `has_specs` is computed with every other node's in
    /// `scan_and_enqueue`.
    fn add_local_root(&mut self, path: &Path) {
        self.output.add_site_child(
            NodeId::INVALID,
            self.ambient.to_vec(),
            path.clone(),
            ArcType::Root,
            MapFunction::identity(),
            false,
        );
    }

    /// Builds a nested sub-indexer one frame deeper, sharing this build's layer
    /// stack, context, and cache. The caller supplies the ambient stack, the
    /// parent-frame chain, and whether duplicate-node skipping is in force.
    fn new_sub<'b, 'g>(
        &self,
        ambient: &'b [(usize, LayerOffset)],
        ambient_is_root: bool,
        frame: Option<&'g Frame<'g>>,
        frame_skip: bool,
    ) -> Indexer<'b, 'g>
    where
        'a: 'b,
    {
        let mut sub = Indexer::new(self.stack, self.ctx, self.cached_indices, ambient, ambient_is_root);
        sub.frame = frame;
        sub.frame_skip = frame_skip;
        sub.frame_depth = self.frame_depth + 1;
        sub
    }

    /// Composes the ancestral parent of a sub-index in the same ambient,
    /// reusing the current frame chain (C++ `_BuildInitialPrimIndexFromAncestor`'s
    /// else-branch `Pcp_BuildPrimIndex(parentSite, …, previousFrame)`). Returns
    /// `None` when the parent relies on an unported feature.
    fn compose_ancestral_subindex(&self, parent: &Path) -> Result<Option<PrimIndexGraph>, Error> {
        self.new_sub(self.ambient, self.ambient_is_root, self.frame, self.frame_skip)
            .build(parent)
    }

    /// Composes an arc target as its own sub-index, including the ancestral
    /// opinions above the target (C++ `_AddArc`'s `includeAncestralOpinions`
    /// branch). A fresh [`Frame`] threads this graph back to the nested build so
    /// duplicate-node skipping can reach the nodes already composed here. Returns
    /// `None` when the target relies on an unported feature.
    fn compose_subindex(
        &self,
        target: &Path,
        ambient: &[(usize, LayerOffset)],
        ambient_is_root: bool,
        skip: bool,
    ) -> Result<Option<PrimIndexGraph>, Error> {
        let frame = Frame {
            requested_path: target.clone(),
            root_path: self.build_path.clone(),
            graph: &self.output,
            previous: self.frame,
        };
        self.new_sub(ambient, ambient_is_root, Some(&frame), skip).build(target)
    }

    /// Composes an arc target as its own ancestral sub-index and grafts it under
    /// `parent` (C++ `_AddArc`'s `includeAncestralOpinions` branch +
    /// `InsertChildSubgraph`), returning the grafted arc node. The grafted node's
    /// implied classes still need to cascade up the new arc, so its
    /// implied-class task is enqueued. Clears `supported` and returns `None` when
    /// the target or its graft relies on an unported feature.
    #[allow(clippy::too_many_arguments)]
    fn compose_and_graft(
        &mut self,
        target: &Path,
        ambient: &[(usize, LayerOffset)],
        ambient_is_root: bool,
        skip: bool,
        parent: NodeId,
        arc: ArcType,
        map: MapFunction,
        origin: NodeId,
        sibling: u16,
    ) -> Result<Option<NodeId>, Error> {
        let Some(sub) = self.compose_subindex(target, ambient, ambient_is_root, skip)? else {
            self.supported = false;
            return Ok(None);
        };
        let Some(grafted) = self.graft_subindex(&sub, parent, arc, map, origin, sibling) else {
            self.supported = false;
            return Ok(None);
        };
        self.add_implied_tasks_for_node(grafted);
        Ok(Some(grafted))
    }

    /// Whether a node at the arc target site `(rep_layer, site_path)` already
    /// exists in this graph or a parent frame's graph (C++ `_AddArc`'s
    /// `skipDuplicateNodes` search). Adding a duplicate would introduce the same
    /// site twice; class arcs and arcs composed inside a skip sub-build skip it.
    ///
    /// The current graph is searched at the target path; each parent frame is
    /// searched at the path the site takes once deepened by the suffix that
    /// frame's request adds (C++'s `ReplacePrefix` across the stack frame).
    fn find_duplicate(&self, rep_layer: usize, site_path: &Path) -> bool {
        if self.output.node_using_site(rep_layer, site_path).is_some() {
            return true;
        }
        let mut search = site_path.clone();
        let mut current_root = self.build_path.clone();
        let mut frame = self.frame;
        while let Some(f) = frame {
            search = if current_root == search {
                f.requested_path.clone()
            } else {
                f.requested_path
                    .replace_prefix(&current_root, &search)
                    .unwrap_or_else(|| f.requested_path.clone())
            };
            if f.graph.node_using_site(rep_layer, &search).is_some() {
                return true;
            }
            current_root = f.root_path.clone();
            frame = f.previous;
        }
        false
    }

    /// Grafts a composed sub-index under `parent` (C++ `InsertChildSubgraph`).
    ///
    /// The source's local root becomes the arc node, carrying `root_map`,
    /// `origin`, `sibling`, and the parent site's namespace depth; every
    /// internal node keeps its own arc, map-to-parent, and strength metadata,
    /// with node handles remapped into this graph. Returns the grafted arc node,
    /// or `None` when the source has no single local root to graft (an extra
    /// root-level arc a later phase grafts individually).
    fn graft_subindex(
        &mut self,
        source: &PrimIndexGraph,
        parent: NodeId,
        arc: ArcType,
        root_map: MapFunction,
        origin: NodeId,
        sibling: u16,
    ) -> Option<NodeId> {
        let local_root = source.local_root();
        if !local_root.is_valid() {
            return None;
        }
        // The source local root is the lone contributing child of the source's
        // synthetic root; a second one means extra root-level arcs to graft.
        let synthetic = source.root;
        let extra_roots = source[synthetic.idx()]
            .children()
            .iter()
            .any(|&c| c != local_root && !source[c.idx()].is_inert());
        if extra_roots {
            return None;
        }

        let parent_depth = self.node(parent).path.prim_element_count() as u16;
        let mut remap: Vec<Option<NodeId>> = vec![None; source.nodes.len()];
        let mut grafted_root = NodeId::INVALID;
        // The arena is append-only, so a node's parent always precedes it and is
        // already remapped when its turn comes.
        for sid in 0..source.nodes.len() {
            if sid == synthetic.idx() {
                continue;
            }
            let node = &source.nodes[sid];
            // The local root becomes the arc node, taking the arc's identity and
            // the parent site's strength metadata; every other node keeps its own
            // arc and metadata, with its parent and origin remapped into this
            // graph.
            let (struct_parent, node_map, node_arc, node_sibling, node_depth, node_origin) = if sid == local_root.idx()
            {
                (parent, root_map.clone(), arc, sibling, parent_depth, Some(origin))
            } else {
                let grafted_parent = node.parent().and_then(|p| remap[p.idx()]).unwrap_or(parent);
                let grafted_origin = node.origin().and_then(|o| remap[o.idx()]).or(Some(grafted_parent));
                (
                    grafted_parent,
                    node.map_to_parent.clone(),
                    node.arc,
                    node.sibling_num_at_origin,
                    node.namespace_depth,
                    grafted_origin,
                )
            };
            let new_id = self.output.add_site_child(
                struct_parent,
                node.layer_stack().to_vec(),
                node.path.clone(),
                node_arc,
                node_map,
                false,
            );
            let n = &mut self.output.nodes[new_id.idx()];
            n.has_specs = node.has_specs;
            n.flags = node.flags;
            n.sibling_num_at_origin = node_sibling;
            n.namespace_depth = node_depth;
            n.origin = node_origin;
            remap[sid] = Some(new_id);
            if sid == local_root.idx() {
                grafted_root = new_id;
            }
        }
        Some(grafted_root)
    }

    /// Computes `has_specs` at each non-inert node's path, abandons the prim
    /// (returns `false`) if any node authors an unported field, and enqueues
    /// reference/payload tasks for the spec-bearing nodes (C++
    /// `AddTasksForRootNode`, restricted to the ported tasks). A node with no
    /// spec at its path authors no arc, so it gets no task.
    fn scan_and_enqueue(&mut self) -> Result<bool, Error> {
        for i in 0..self.output.nodes.len() {
            if self.output.nodes[i].is_inert() {
                continue;
            }
            let node = NodeId(i as u32);
            let has_specs = self.stack_has_spec(self.output.nodes[i].layer_stack(), &self.output.nodes[i].path);
            self.output.nodes[i].has_specs = has_specs;
            if self.node_authors_unsupported(node)? {
                return Ok(false);
            }
            if has_specs {
                self.add_tasks_for_node(node);
            }
        }
        Ok(true)
    }

    /// Enqueues a node's expressed-arc tasks and any implied-class propagation
    /// it triggers (C++ `AddTasksForNode`, restricted to the ported tasks).
    ///
    /// A class-based node propagates the whole class hierarchy it starts from
    /// (`_FindStartingNodeForImpliedClasses`); a non-class node that picked up
    /// class-based children (from a referenced subtree) propagates them from
    /// itself.
    fn add_tasks_for_node(&mut self, node: NodeId) {
        self.tasks.push(Task {
            kind: TaskKind::EvalNodeReferences,
            node,
        });
        if self.stack.load_payloads {
            self.tasks.push(Task {
                kind: TaskKind::EvalNodePayloads,
                node,
            });
        }
        self.tasks.push(Task {
            kind: TaskKind::EvalNodeInherits,
            node,
        });

        self.add_implied_tasks_for_node(node);
    }

    /// Enqueues only the implied-class propagation a node triggers, without its
    /// expressed-arc tasks (C++ `AddTasksForNode(node, tasks & ~ExpressedArcTasks)`).
    ///
    /// Used after grafting an ancestral sub-index: the nested build already
    /// evaluated the grafted nodes' references, payloads, and inherits, so only
    /// the implied-class cascade up the new arc remains.
    fn add_implied_tasks_for_node(&mut self, node: NodeId) {
        if is_class_based(self.node(node).arc) {
            let start = self.find_starting_node_for_implied_classes(node);
            self.enqueue_implied(start);
        } else if self.has_class_based_child(node) {
            self.enqueue_implied(node);
        }
    }

    /// Enqueues an `EvalImpliedClasses` task, deduplicated per node (C++
    /// `taskUniq`).
    fn enqueue_implied(&mut self, node: NodeId) {
        if self.implied_seen.insert(node) {
            self.tasks.push(Task {
                kind: TaskKind::EvalImpliedClasses,
                node,
            });
        }
    }

    /// Composes the references or payloads authored at `node`'s site and adds an
    /// arc for each (C++ `_EvalNodeReferences` / `_EvalNodePayloads`). Both
    /// resolve to a uniform `(asset, prim, offset)` list and share the arc-add
    /// loop; an unported target clears `supported` and unwinds.
    fn eval_arcs(&mut self, node: NodeId, kind: TaskKind) -> Result<(), Error> {
        let (arc, arcs) = match kind {
            TaskKind::EvalNodeReferences => {
                let refs = compose_references_in(self.node_slice(node), &self.stack.layers, &*self.stack.resolver)?;
                let arcs = refs
                    .into_iter()
                    .map(|r| (r.asset_path, r.prim_path, r.layer_offset.sanitized()))
                    .collect::<Vec<_>>();
                (ArcType::Reference, arcs)
            }
            TaskKind::EvalNodePayloads => {
                let payloads = collect_payloads_in(self.node_slice(node), &self.stack.layers, &*self.stack.resolver)?;
                let arcs = payloads
                    .into_iter()
                    .map(|p| {
                        (
                            p.asset_path,
                            p.prim_path,
                            p.layer_offset.unwrap_or_default().sanitized(),
                        )
                    })
                    .collect::<Vec<_>>();
                (ArcType::Payload, arcs)
            }
            // `eval_arcs` is dispatched only for reference and payload tasks.
            TaskKind::EvalNodeInherits | TaskKind::EvalImpliedClasses => {
                unreachable!("eval_arcs handles only reference and payload tasks")
            }
        };
        for (asset_path, prim_path, offset) in &arcs {
            self.add_ref_or_payload_arc(node, asset_path, prim_path, arc, *offset)?;
            if !self.supported {
                return Ok(());
            }
        }
        Ok(())
    }

    /// Composes the inherits authored at `node`'s site and adds a class-based arc
    /// for each (C++ `_EvalNodeInherits` → `_AddClassBasedArcs`).
    fn eval_node_inherits(&mut self, node: NodeId) -> Result<(), Error> {
        // An inert node (a non-contributing implied placeholder) authors nothing.
        if self.node(node).is_inert() {
            return Ok(());
        }
        let inherits = compose_arc_list_in::<Path>(self.node_slice(node), FieldKey::InheritPaths, &self.stack.layers)?;
        // A class arc interacting with relocates is a later phase.
        if !inherits.is_empty() && self.has_relocates {
            self.supported = false;
            return Ok(());
        }
        let node_path = self.node(node).path.clone();
        for (arc_num, class_path) in inherits.iter().enumerate() {
            let resolved = node_path.make_absolute(class_path);
            // A class arc must target a prim, not a variant selection (P2).
            if resolved.is_prim_variant_selection_path() {
                self.supported = false;
                return Ok(());
            }
            // The class-arc map sends the class to the instance; every other
            // path (notably root classes) maps through the added root identity.
            let inherit_map = MapFunction::from_pair(resolved, node_path.clone()).with_root_identity();
            self.add_class_based_arc(node, node, inherit_map, arc_num as u16, None, ArcType::Inherit)?;
            if !self.supported {
                return Ok(());
            }
        }
        Ok(())
    }

    /// Adds a single class-based arc under `parent` (C++ `_AddClassBasedArc`),
    /// returning the new or existing node. The arc may be a directly-authored
    /// inherit or an implied class propagated from `origin` in another subtree.
    ///
    /// A sub-root class target is composed as its own ancestral sub-index
    /// (`includeAncestralOpinions`) and grafted under `parent`; a class reached
    /// both directly and through an ancestral reference grafts once thanks to
    /// duplicate-node skipping (C++ `skipDuplicateNodes`).
    fn add_class_based_arc(
        &mut self,
        parent: NodeId,
        origin: NodeId,
        inherit_map: MapFunction,
        arc_num: u16,
        ignore_if_same_as_site: Option<(usize, Path)>,
        arc: ArcType,
    ) -> Result<Option<NodeId>, Error> {
        let parent_path = self.node(parent).path.clone();
        // Class arcs added to a variant-selection site need the strip/re-add
        // handling a later phase ports.
        if parent_path.is_prim_variant_selection_path() {
            self.supported = false;
            return Ok(None);
        }
        // Map the parent site back across the arc to find the site to inherit.
        // An empty result means there is no appropriate site (the parent is
        // outside the arc's co-domain); that is not an error, just no node.
        let Some(inherit_path) = inherit_map.map_target_to_source(&parent_path) else {
            return Ok(None);
        };

        let parent_layers = self.node(parent).layer_stack().to_vec();
        let rep = parent_layers[0].0;

        // Dedup: a matching child already inherits this site.
        if let Some(existing) = self.find_matching_child(parent, rep, &inherit_path) {
            return Ok(Some(existing));
        }

        let same_as_ignore = ignore_if_same_as_site
            .as_ref()
            .is_some_and(|(li, p)| *li == rep && *p == inherit_path);
        let direct_should = inherit_path != parent_path && !same_as_ignore;
        // A contributing class arc skips a duplicate site; an inert placeholder
        // (mapping unchanged) is kept to keep propagating. The skip also carries
        // in from a parent frame (C++ `_AddArc`'s `|= previousFrame->skip`).
        let skip = direct_should || self.frame_skip;
        if skip && self.find_duplicate(rep, &inherit_path) {
            return Ok(None);
        }

        // A sub-root class needs the opinions above it: compose the target as its
        // own ancestral sub-index and graft it under the parent.
        if direct_should && !is_root_prim(&inherit_path) {
            let target_is_root = self.ambient_is_root_for(&parent_layers);
            return self.compose_and_graft(
                &inherit_path,
                &parent_layers,
                target_is_root,
                skip,
                parent,
                arc,
                inherit_map,
                origin,
                arc_num,
            );
        }

        let has_specs = self.stack_has_spec(&parent_layers, &inherit_path);
        let new_node = self.output.add_site_child(
            parent,
            parent_layers,
            inherit_path,
            arc,
            inherit_map,
            arc == ArcType::Specialize,
        );
        let n = &mut self.output.nodes[new_node.idx()];
        n.origin = Some(origin);
        n.sibling_num_at_origin = arc_num;
        n.has_specs = has_specs;
        // A redundant arc (mapping the site unchanged, or onto the ignored site)
        // is kept to propagate but contributes no opinions.
        if !direct_should {
            n.flags |= NodeFlags::INERT;
        }

        if self.node_authors_unsupported(new_node)? {
            self.supported = false;
            return Ok(None);
        }

        self.add_tasks_for_node(new_node);
        Ok(Some(new_node))
    }

    /// Propagates `node`'s class-based children one level up to its parent (C++
    /// `_EvalImpliedClasses`): the queue repeats this, carrying a class brought
    /// in through a reference up the arc chain into the referencing namespace.
    fn eval_implied_classes(&mut self, node: NodeId) -> Result<(), Error> {
        let Some(parent) = self.node(node).parent() else {
            return Ok(());
        };
        if !self.has_class_based_child(node) {
            return Ok(());
        }
        // The map to the parent gets the root identity so a root class still
        // maps across a restricted (reference) arc domain.
        let transfer = self.node(node).map_to_parent.with_root_identity();
        self.eval_implied_class_tree(parent, node, &transfer, true)
    }

    /// Propagates the class hierarchy under `src` to `dest`, conjugating each
    /// class arc through `transfer` (C++ `_EvalImpliedClassTree`).
    fn eval_implied_class_tree(
        &mut self,
        dest: NodeId,
        src: NodeId,
        transfer: &MapFunction,
        start_of_tree: bool,
    ) -> Result<(), Error> {
        // Implied classes across relocate nodes need special routing (P4).
        if self.node(dest).arc == ArcType::Relocate {
            self.supported = false;
            return Ok(());
        }

        let src = self.node(src);
        let src_is_class = is_class_based(src.arc);
        let src_depth = src.depth_below_introduction();
        let src_children = src.children().to_vec();

        for child in src_children {
            let c = self.node(child);
            if !is_class_based(c.arc) {
                continue;
            }
            // Skip the arc that continues an ancestral class chain rather than a
            // true namespace child: it must not be implied directly to dest.
            if start_of_tree && src_is_class && src_depth == c.depth_below_introduction() {
                continue;
            }

            let child_arc = c.arc;
            let child_map = c.map_to_parent.clone();
            let child_site = (c.layer_index(), c.path.clone());
            let sibling = c.sibling_num_at_origin;
            let dest_class_func = transfer.implied_class(&child_map);

            // Reuse the implied node already propagated for this child, else add
            // it; either may be absent (no appropriate site to inherit).
            let dest_child = match self.find_implied_child(dest, child) {
                Some(existing) => Some(existing),
                None => self.add_class_based_arc(
                    dest,
                    child,
                    dest_class_func.clone(),
                    sibling,
                    Some(child_site),
                    child_arc,
                )?,
            };
            if !self.supported {
                return Ok(());
            }

            // Recurse into nested classes under the child.
            if let Some(dest_child) = dest_child {
                if self.has_class_based_child(child) {
                    let child_transfer = dest_class_func.inverse().compose(&transfer.compose(&child_map));
                    self.eval_implied_class_tree(dest_child, child, &child_transfer, false)?;
                    if !self.supported {
                        return Ok(());
                    }
                }
            }
        }
        Ok(())
    }

    /// Finds the node where implied-class propagation for class-based node `n`
    /// should start, so the whole class hierarchy propagates as a unit (C++
    /// `_FindStartingNodeForImpliedClasses`).
    fn find_starting_node_for_implied_classes(&self, n: NodeId) -> NodeId {
        let mut start = n;
        while is_class_based(self.node(start).arc) {
            let (instance, class) = self.find_starting_node_of_class_hierarchy(start);
            start = instance;
            if is_class_based(self.node(instance).arc) {
                let ancestral = self.node(instance).path_at_introduction();
                if self.node(class).path.has_prefix(&ancestral) {
                    break;
                }
            }
        }
        start
    }

    /// Walks up the chain of class arcs at the same depth-below-introduction from
    /// `n`, returning `(instance node, topmost class node)` (C++
    /// `Pcp_FindStartingNodeOfClassHierarchy`).
    fn find_starting_node_of_class_hierarchy(&self, n: NodeId) -> (NodeId, NodeId) {
        let mut instance = n;
        let mut class = n;
        let depth = self.node(instance).depth_below_introduction();
        while is_class_based(self.node(instance).arc) && self.node(instance).depth_below_introduction() == depth {
            class = instance;
            match self.node(instance).parent() {
                Some(p) => instance = p,
                None => break,
            }
        }
        (instance, class)
    }

    /// Returns the child of `parent` whose site matches `(rep_layer, path)` (C++
    /// `_FindMatchingChild`, the non-relocate case).
    fn find_matching_child(&self, parent: NodeId, rep_layer: usize, path: &Path) -> Option<NodeId> {
        self.node(parent)
            .children()
            .iter()
            .copied()
            .find(|&c| self.node(c).layer_index() == rep_layer && &self.node(c).path == path)
    }

    /// Returns the child of `dest` already propagated for the implied class
    /// `src_child`, identified by its origin (C++ `_EvalImpliedClassTree`'s
    /// origin dedup).
    fn find_implied_child(&self, dest: NodeId, src_child: NodeId) -> Option<NodeId> {
        self.node(dest)
            .children()
            .iter()
            .copied()
            .find(|&c| self.node(c).origin() == Some(src_child))
    }

    /// Whether `node` has any class-based (inherit/specialize) child (C++
    /// `_HasClassBasedChild`).
    fn has_class_based_child(&self, node: NodeId) -> bool {
        self.node(node)
            .children()
            .iter()
            .any(|&c| is_class_based(self.node(c).arc))
    }

    /// Resolves a reference or payload to its target layer stack, adds the target
    /// node under `parent`, and enqueues that node's own reference/payload tasks
    /// (C++ `_AddArc` for an arc without ancestral opinions).
    ///
    /// Targets outside the ported set — internal references, `defaultPrim`
    /// resolution, sub-root targets, unresolved layers, empty targets — abandon
    /// the prim to the recursive builder.
    fn add_ref_or_payload_arc(
        &mut self,
        parent: NodeId,
        asset_path: &str,
        prim_path: &Path,
        arc: ArcType,
        arc_offset: LayerOffset,
    ) -> Result<(), Error> {
        let is_internal = asset_path.is_empty();
        let parent_path = self.node(parent).path.clone();

        // Resolve the target layer stack. An internal reference targets the
        // referencing node's own layer stack (C++ `node.GetLayerStack()`); an
        // external one resolves the asset's sublayer stack.
        let (target_stack, target_is_root) = if is_internal {
            let stack = self.node(parent).layer_stack().to_vec();
            let is_root = self.ambient_is_root_for(&stack);
            (stack, is_root)
        } else {
            let Some(layer_index) = find_layer(asset_path, &self.stack.layers, &*self.stack.resolver) else {
                // The recursive builder raises `UnresolvedLayer`; let it.
                self.supported = false;
                return Ok(());
            };
            (self.stack.sublayer_stack(layer_index), false)
        };

        // Resolve the source prim path, falling back to the target layer's
        // `defaultPrim` when the arc names no prim (C++ `_GetDefaultPrimPath`).
        let source = if prim_path.is_empty() {
            let Some(p) = self.resolve_default_prim(&target_stack)? else {
                self.supported = false;
                return Ok(());
            };
            p
        } else {
            prim_path.clone()
        };

        let rep = target_stack[0].0;
        // A duplicate site reached inside a skip sub-build is skipped, keeping a
        // class reached both directly and through this arc from grafting twice.
        if self.frame_skip && self.find_duplicate(rep, &source) {
            return Ok(());
        }
        if !self.arc_target_in_bounds(parent, rep, &source) {
            // Deep nesting or a cycle the recursive builder reports.
            self.supported = false;
            return Ok(());
        }

        let mut map = MapFunction::from_pair(source.clone(), parent_path).with_time_offset(arc_offset);
        if is_internal {
            // Internal references keep full namespace visibility outside the
            // source and target (C++ `mapExpr.AddRootIdentity()`).
            map = map.with_root_identity();
        }

        // A sub-root target needs the opinions above it: compose it as its own
        // ancestral sub-index and graft it under the parent.
        if !is_root_prim(&source) {
            self.compose_and_graft(
                &source,
                &target_stack,
                target_is_root,
                self.frame_skip,
                parent,
                arc,
                map,
                parent,
                0,
            )?;
            return Ok(());
        }

        if !self.stack_has_spec(&target_stack, &source) {
            // The recursive builder keeps an empty arc target as a culled node;
            // the indexer does not reproduce that yet, so defer the whole prim.
            self.supported = false;
            return Ok(());
        }

        let new_node = self
            .output
            .add_site_child(parent, target_stack, source, arc, map, false);
        if self.node_authors_unsupported(new_node)? {
            self.supported = false;
            return Ok(());
        }

        // The new node may itself author references, payloads, and inherits.
        self.add_tasks_for_node(new_node);
        Ok(())
    }

    /// Resolves the `defaultPrim` of a layer stack's root layer to a root-prim
    /// path (C++ `_GetDefaultPrimPath`), or `None` when it is absent or invalid.
    fn resolve_default_prim(&self, target_stack: &[(usize, LayerOffset)]) -> Result<Option<Path>, Error> {
        let root_layer = target_stack[0].0;
        let Some(value) = self
            .stack
            .layer(root_layer)
            .try_get(&Path::abs_root(), FieldKey::DefaultPrim.as_str())?
        else {
            return Ok(None);
        };
        match value.into_owned() {
            Value::Token(name) | Value::String(name) => Ok(Path::new(&format!("/{name}")).ok()),
            _ => Ok(None),
        }
    }

    /// Returns `true` when an arc to `(root_layer, path)` under `parent` is
    /// within the depth bound and is not a cycle. A single walk of the parent
    /// chain both rejects an ancestor that is the same site (C++ `_CheckForCycle`)
    /// and counts hops against `MAX_DEPTH`.
    fn arc_target_in_bounds(&self, parent: NodeId, root_layer: usize, path: &Path) -> bool {
        // Count the arc target node itself, then each ancestor up to the root.
        let mut depth = 1;
        let mut cur = parent;
        while cur.is_valid() {
            let n = self.node(cur);
            if n.layer_index() == root_layer && &n.path == path {
                return false;
            }
            depth += 1;
            cur = n.parent().unwrap_or(NodeId::INVALID);
        }
        depth <= MAX_DEPTH
    }

    /// Whether `layers` is the stage root layer stack — the only ambient where
    /// an arc target is composed at root and the stage-keyed `cached_indices`
    /// apply. A sub-index composed in this ambient is keyed in the stage cache.
    fn ambient_is_root_for(&self, layers: &[(usize, LayerOffset)]) -> bool {
        self.ambient_is_root && layers == self.ambient
    }

    /// Whether any layer in `stack` authors a spec at `path`.
    fn stack_has_spec(&self, stack: &[(usize, LayerOffset)], path: &Path) -> bool {
        stack.iter().any(|&(li, _)| self.stack.layer(li).has_spec(path))
    }

    /// Returns `true` when any layer of `node`'s site authors an
    /// inherit/specialize/variant field at its path (see [`UNSUPPORTED_FIELDS`]).
    fn node_authors_unsupported(&self, node: NodeId) -> Result<bool, Error> {
        let n = self.node(node);
        for &(li, _) in n.layer_stack() {
            let layer = self.stack.layer(li);
            for field in UNSUPPORTED_FIELDS {
                if layer.try_get(&n.path, field.as_str())?.is_some() {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// Borrows the node behind a handle in the graph being grown.
    fn node(&self, id: NodeId) -> &super::graph::Node {
        &self.output[id.idx()]
    }

    /// A one-element slice over `node`, for the `compose_*_in` helpers that read
    /// a field across a node's member layers.
    fn node_slice(&self, node: NodeId) -> &[super::graph::Node] {
        &self.output[node.idx()..=node.idx()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;

    fn stack(text: &str) -> LayerStack {
        let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
        let layer = crate::sdf::Layer::new("root.usd", Box::new(crate::usda::TextReader::from_data(data)));
        LayerStack::new(vec![layer], 0, Box::new(DefaultResolver::new()), true)
    }

    fn multi_stack(layers: &[(&str, &str)]) -> LayerStack {
        let layers = layers
            .iter()
            .map(|(id, text)| {
                let data = crate::usda::parser::Parser::new(text).parse().expect("parse usda");
                crate::sdf::Layer::new(*id, Box::new(crate::usda::TextReader::from_data(data)))
            })
            .collect();
        LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true)
    }

    fn build(stack: &LayerStack, prim: &str) -> Option<PrimIndexGraph> {
        let ctx = CompositionContext::default();
        let ambient = stack.root_layer_stack();
        Indexer::new(stack, &ctx, &HashMap::new(), &ambient, true)
            .build(&Path::from(prim))
            .expect("indexer build")
    }

    #[test]
    fn local_prim_supported() {
        let s = stack("#usda 1.0\ndef \"World\" {\n  def \"Sphere\" {}\n}\n");
        let graph = build(&s, "/World").expect("a purely local prim is supported");
        // The synthetic inert root plus one Root-arc site node.
        let arcs: Vec<ArcType> = graph.iter().filter(|n| !n.is_inert()).map(|n| n.arc).collect();
        assert_eq!(arcs, vec![ArcType::Root]);
    }

    #[test]
    fn local_inherit_composed() {
        let s = stack("#usda 1.0\nclass \"C\" { custom double x = 1 }\ndef \"World\" (\n    inherits = </C>\n) {\n}\n");
        let graph = build(&s, "/World").expect("a local inherit to a root class is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Inherit && n.path.as_str() == "/C" && n.has_specs()),
            "the inherit arc to /C contributes the class opinion"
        );
    }

    #[test]
    fn subroot_inherit_composed() {
        // A class nested under another prim composes through the ancestral
        // sub-index build (C++ `includeAncestralOpinions`).
        let s = stack(
            "#usda 1.0\ndef \"Scope\" {\n  class \"C\" { custom double x = 1 }\n}\ndef \"World\" (\n    inherits = </Scope/C>\n) {\n}\n",
        );
        let graph = build(&s, "/World").expect("a sub-root class inherit is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Inherit && n.path.as_str() == "/Scope/C" && n.has_specs()),
            "the sub-root inherit arc to /Scope/C contributes the class opinion"
        );
    }

    /// A class brought in through a reference is mirrored into the referencing
    /// namespace as an implied class node, so an outer opinion on the class
    /// contributes (C++ `_EvalImpliedClassTree`).
    #[test]
    fn implied_class_from_reference() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"Model\" (\n    references = @ref.usd@</Model>\n) {}\nclass \"Class\" { custom double x = 1 }\n",
            ),
            (
                "ref.usd",
                "#usda 1.0\ndef \"Model\" (\n    inherits = </Class>\n) {}\nclass \"Class\" {}\n",
            ),
        ]);
        let graph = build(&s, "/Model").expect("reference + class is composed by the indexer");
        // The referenced class node, plus the implied class node in root.usd.
        let class_layers: Vec<usize> = graph
            .iter()
            .filter(|n| n.arc == ArcType::Inherit && n.path.as_str() == "/Class")
            .map(|n| n.layer_index())
            .collect();
        assert!(
            class_layers.contains(&0) && class_layers.contains(&1),
            "the class is composed in both the referenced (1) and referencing (0) layers, got {class_layers:?}"
        );
    }

    #[test]
    fn internal_reference_composed() {
        let s = stack(
            "#usda 1.0\ndef \"Base\" { custom double x = 1 }\ndef \"World\" (\n    references = </Base>\n) {\n}\n",
        );
        let graph = build(&s, "/World").expect("an internal reference to a root prim is composed");
        assert!(
            graph
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/Base" && n.has_specs()),
            "the internal reference arc to /Base contributes its opinion"
        );
    }

    /// The task queue composes a reference diamond: `/Root` references `A` and
    /// `B`, both of which reference `C`. The shared target `C` is reached by two
    /// arc paths, so it contributes a node on each — the no-dedup behavior that
    /// distinguishes the queue from the recursive builder's global set.
    #[test]
    fn reference_diamond_two_targets() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"Root\" (\n    references = [@A.usd@</A>, @B.usd@</B>]\n) {}\n",
            ),
            ("A.usd", "#usda 1.0\ndef \"A\" (\n    references = @C.usd@</C>\n) {}\n"),
            ("B.usd", "#usda 1.0\ndef \"B\" (\n    references = @C.usd@</C>\n) {}\n"),
            ("C.usd", "#usda 1.0\ndef \"C\" { custom double x = 1 }\n"),
        ]);
        let graph = build(&s, "/Root").expect("a pure reference diamond is composed by the indexer");
        let c_nodes = graph.iter().filter(|n| n.path.as_str() == "/C").count();
        assert_eq!(c_nodes, 2, "the shared reference target appears once per arc path");
    }

    /// Ancestral references propagate to a child through the graph-clone seed:
    /// `/Root` references `A`, and `A/Child` is reachable at the deepened site
    /// `/A/Child` in the referenced layer.
    #[test]
    fn ancestral_reference_propagates_to_child() {
        let s = multi_stack(&[
            (
                "root.usd",
                "#usda 1.0\ndef \"Root\" (\n    references = @A.usd@</A>\n) {}\n",
            ),
            (
                "A.usd",
                "#usda 1.0\ndef \"A\" {\n    def \"Child\" { custom double x = 1 }\n}\n",
            ),
        ]);
        let ctx = CompositionContext::default();
        let ambient = s.root_layer_stack();
        // Seed the child build with the parent's composed index, as the cache does.
        let root_index = PrimIndex::build_with_context(&Path::from("/Root"), &s, &ctx).expect("root index build");
        let mut cached = HashMap::new();
        cached.insert(Path::from("/Root"), root_index);
        let child = Indexer::new(&s, &ctx, &cached, &ambient, true)
            .build(&Path::from("/Root/Child"))
            .expect("indexer build")
            .expect("child composed by indexer");
        assert!(
            child
                .iter()
                .any(|n| n.path.as_str() == "/A/Child" && n.arc == ArcType::Reference && n.has_specs()),
            "the ancestral reference contributes the child's opinion at the deepened site"
        );
    }
}
