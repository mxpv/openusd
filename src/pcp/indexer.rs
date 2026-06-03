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
//! The indexer is being ported arc-by-arc. `build_with_cache_in` composes a
//! prim with the indexer when [`Indexer::build`] reports support and otherwise
//! falls back to the recursive builder. Ported so far: the root local site,
//! external reference/payload arcs to a root-level target, and ancestral
//! reference/payload propagation through the graph-clone seed. Any other feature
//! (inherits, specializes, variants, relocates, internal references,
//! `defaultPrim` targets, sub-root targets, instances) abandons the prim
//! ([`Indexer::build`] returns `None`); each deferral point carries its reason
//! inline.

use std::collections::BinaryHeap;
use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::schema::FieldKey;
use crate::sdf::{AbstractData, LayerOffset, Path};

use super::graph::{ArcType, NodeId, PrimIndexGraph};
use super::index::{collect_payloads_in, compose_references_in, find_layer, CompositionContext, PrimIndex};
use super::mapping::MapFunction;
use super::{Error, LayerStack};

/// Maximum composition-arc nesting before the prim is abandoned to the
/// recursive builder (which reports it as a cycle). Matches the builder's
/// `MAX_COMPOSITION_DEPTH`.
const MAX_DEPTH: usize = 100;

/// Fields whose presence at a composed site means the prim pulls in an arc or
/// variant a later phase ports. While any is authored the indexer abandons the
/// prim to the recursive builder rather than composing a half-resolved result.
const UNSUPPORTED_FIELDS: [FieldKey; 4] = [
    FieldKey::InheritPaths,
    FieldKey::Specializes,
    FieldKey::VariantSetNames,
    FieldKey::VariantSelection,
];

/// A queued unit of composition work on one node (C++ `Pcp_PrimIndexer::Task`).
///
/// `BinaryHeap` pops the greatest `Task`, and the derived order compares
/// [`kind`](Self::kind) first, so references drain before payloads (C++
/// `Task::Type` priority). Within a kind the node index gives a consistent,
/// arbitrary tiebreak — references and payloads compose order-independently, so
/// only determinism matters.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Task {
    kind: TaskKind,
    node: NodeId,
}

/// The ported task kinds, ordered weakest-priority first so the derived `Ord`
/// makes the heap pop the highest-priority kind: payloads are evaluated after
/// references (C++ `Task::Type`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum TaskKind {
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
pub(crate) struct Indexer<'a> {
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
    /// The graph grown so far.
    output: PrimIndexGraph,
    /// Open composition tasks, highest priority first.
    tasks: BinaryHeap<Task>,
    /// Cleared the moment composition meets a feature a later phase ports; the
    /// build is then abandoned and the recursive builder composes the prim.
    supported: bool,
}

impl<'a> Indexer<'a> {
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
            output: PrimIndexGraph::default(),
            tasks: BinaryHeap::new(),
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
            self.eval_arcs(task.node, task.kind)?;
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
        // The stage-keyed cache only applies when this prim is composed in the
        // stage root layer stack. Ancestral seeding for an arc target (composed
        // in a referenced sublayer stack) is a later phase.
        if !self.ambient_is_root {
            return Ok(false);
        }
        let Some(parent_index) = self.cached_indices.get(&parent) else {
            return Ok(false);
        };

        // Clone the parent's graph; only a graph composed entirely of ported
        // arcs can be deepened structurally. A culled or class/variant/relocate
        // node means the parent relied on an unported feature.
        let graph = parent_index.graph().clone();
        if graph.nodes.iter().any(|n| {
            !n.is_inert() && (n.is_culled() || !matches!(n.arc, ArcType::Root | ArcType::Reference | ArcType::Payload))
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
                self.enqueue_arc_tasks(node);
            }
        }
        Ok(true)
    }

    /// Enqueues a node's reference and payload evaluation (C++ `_AddArc`'s
    /// `AddTasksForNode`, restricted to the ported tasks).
    fn enqueue_arc_tasks(&mut self, node: NodeId) {
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
        };
        for (asset_path, prim_path, offset) in &arcs {
            self.add_ref_or_payload_arc(node, asset_path, prim_path, arc, *offset)?;
            if !self.supported {
                return Ok(());
            }
        }
        Ok(())
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
        // Internal references (empty asset path) and `defaultPrim` targets
        // (empty prim path) are later phases.
        if asset_path.is_empty() || prim_path.is_empty() {
            self.supported = false;
            return Ok(());
        }
        // A sub-root target sits under a prim that may carry ancestral arcs; the
        // recursive-subindex composition it needs is a later phase.
        if prim_path.parent().is_some_and(|p| p != Path::abs_root()) {
            self.supported = false;
            return Ok(());
        }
        let Some(layer_index) = find_layer(asset_path, &self.stack.layers, &*self.stack.resolver) else {
            // The recursive builder raises `UnresolvedLayer`; let it.
            self.supported = false;
            return Ok(());
        };

        if !self.arc_target_in_bounds(parent, layer_index, prim_path) {
            // Deep nesting or a cycle the recursive builder reports.
            self.supported = false;
            return Ok(());
        }

        let target_stack = self.stack.sublayer_stack(layer_index);
        if !self.stack_has_spec(&target_stack, prim_path) {
            // The recursive builder keeps an empty arc target as a culled node;
            // the indexer does not reproduce that yet, so defer the whole prim.
            self.supported = false;
            return Ok(());
        }

        let parent_path = self.output.nodes[parent.idx()].path.clone();
        let map = MapFunction::from_pair(prim_path.clone(), parent_path).with_time_offset(arc_offset);
        let new_node = self
            .output
            .add_site_child(parent, target_stack, prim_path.clone(), arc, map, false);

        if self.node_authors_unsupported(new_node)? {
            self.supported = false;
            return Ok(());
        }

        // The new node may itself author references and payloads.
        self.enqueue_arc_tasks(new_node);
        Ok(())
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
            let n = &self.output.nodes[cur.idx()];
            if n.layer_index() == root_layer && &n.path == path {
                return false;
            }
            depth += 1;
            cur = n.parent().unwrap_or(NodeId::INVALID);
        }
        depth <= MAX_DEPTH
    }

    /// Whether any layer in `stack` authors a spec at `path`.
    fn stack_has_spec(&self, stack: &[(usize, LayerOffset)], path: &Path) -> bool {
        stack.iter().any(|&(li, _)| self.stack.layer(li).has_spec(path))
    }

    /// Returns `true` when any layer of `node`'s site authors an
    /// inherit/specialize/variant field at its path (see [`UNSUPPORTED_FIELDS`]).
    fn node_authors_unsupported(&self, node: NodeId) -> Result<bool, Error> {
        let n = &self.output.nodes[node.idx()];
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
    fn inherit_prim_deferred() {
        let s = stack("#usda 1.0\nclass \"C\" {}\ndef \"World\" (\n    inherits = </C>\n) {\n}\n");
        assert!(
            build(&s, "/World").is_none(),
            "a prim authoring an inherit defers to the recursive builder"
        );
    }

    #[test]
    fn internal_reference_deferred() {
        let s = stack("#usda 1.0\ndef \"Base\" {}\ndef \"World\" (\n    references = </Base>\n) {\n}\n");
        assert!(
            build(&s, "/World").is_none(),
            "an internal reference defers to the recursive builder"
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
