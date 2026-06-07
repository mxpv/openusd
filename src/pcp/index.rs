//! Per-prim composition index (`PcpPrimIndex` equivalent).
//!
//! A [`PrimIndex`] records the strength-ordered list of layer specs that
//! contribute opinions to a single composed prim. See the
//! [module-level docs](super) for the full composition overview.

use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use anyhow::Result;

use crate::ar::Resolver;
use crate::sdf::expr;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{self, AbstractData, LayerOffset, ListOp, Path, Payload, PayloadListOp, Reference, Value};

use super::builder::BuildResult;
use super::graph::{ArcType, Node, NodeFlags, NodeId, PrimIndexGraph};
use super::mapping::MapFunction;
use super::{Error, LayerStack, VariantFallbackMap};

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
    /// composition arc. Culled arc nodes (empty targets) and spec-less full-stack
    /// nodes do not count: they add no shared content, so a prim that only
    /// references an empty target is not treated as composed for instancing.
    pub(crate) fn has_composition_arc(&self) -> bool {
        self.arena()
            .iter()
            .any(|node| node.arc != ArcType::Root && !node.is_culled() && node.has_specs())
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

    /// Returns the underlying composition graph. The task-queue builder clones a
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
    /// (The local root is also inerted earlier by the builder via
    /// [`CompositionContext::within_instance`](super::index::CompositionContext::within_instance).)
    pub(crate) fn mark_instance_local_inert(&mut self, instance_depth: u16) {
        let local = self.instance_local_nodes(instance_depth);
        for (node, &is_local) in self.graph.nodes.iter_mut().zip(local.iter()) {
            if is_local {
                node.flags |= NodeFlags::INERT;
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

    /// Builds a prim index for a root prim with no cached ancestors (a test
    /// convenience over [`build_with_cache`](Self::build_with_cache)). A child
    /// prim must instead be built through a cache holding its ancestors, since
    /// the builder seeds a child from its cached parent.
    #[cfg(test)]
    pub(crate) fn build_with_context(path: &Path, stack: &LayerStack, ctx: &CompositionContext) -> BuildResult<Self> {
        Self::build_with_cache(path, stack, ctx, &HashMap::new()).map(|(index, _errors)| index)
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
    ) -> BuildResult<(Self, Vec<Error>)> {
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
    ) -> BuildResult<(Self, Vec<Error>)> {
        if ambient_is_root {
            if let Some(cached) = cached_indices.get(path) {
                return Ok((cached.clone(), Vec::new()));
            }
        }
        // The task-queue builder is the sole composition path. A genuine cycle
        // surfaces as `Error::ArcCycle`; an unresolvable arc is recorded in the
        // returned errors and skipped. A `None` graph means an unestablished seed
        // or the runaway nesting backstop, which composes to an empty prim index.
        let builder = super::builder::Builder::new(stack, ctx, cached_indices, ambient, ambient_is_root);
        let super::builder::BuildOutput { graph, errors } = builder.build(path)?;
        Ok((
            PrimIndex {
                graph: graph.unwrap_or_default(),
            },
            errors,
        ))
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
// Shared helpers (used by the `Builder` and Stage)
// ---------------------------------------------------------------------------

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

    // For variant sets without an explicit selection, apply a configured
    // fallback if one names an existing variant. With no applicable fallback the
    // set stays unselected (C++ `_EvalNodeFallbackVariant`); there is no implicit
    // first-variant default, matching the builder.
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
                // Use the first configured fallback that exists in this set.
                let fallbacks = variant_fallbacks.get(entry.key());
                if let Some(fb) = fallbacks.iter().find(|fb| variants.contains(fb)) {
                    entry.insert(fb.clone());
                }
            }
        }
    }

    selections
}

/// Composes a list-op field across nodes' layer stacks, returning the
/// flattened list.
///
/// Each node fans out into its contributing sublayers, strongest first.
/// `decode` turns a raw field value into a `ListOp<T>` (returning `None` for a
/// wrong-typed value, treated as no opinion); `retime` rewrites each item by
/// the contributing sublayer's offset (a no-op for offset-free arcs). Backend
/// decode errors surface to the caller.
fn compose_list_op_in<T, D, R, A>(
    nodes: &[Node],
    field: &str,
    layers: &[sdf::Layer],
    decode: D,
    mut retime: R,
    mut anchor: A,
) -> Result<Vec<T>>
where
    T: Default + Clone + PartialEq,
    D: Fn(Value) -> Option<ListOp<T>>,
    R: FnMut(&mut T, LayerOffset, f64),
    A: FnMut(&mut T, usize) -> f64,
{
    let mut combined: Option<ListOp<T>> = None;
    // The sublayer offset and time-codes scale to fold into each item, keyed by
    // the item as authored (after anchoring). Recorded strongest-first and applied
    // only after the list-op is composed: an offset-bearing item (reference/
    // payload) is deduped by its AUTHORED value, so two items that resolve to the
    // same composed offset but are authored differently — e.g. `(offset=45,
    // scale=0.5)` under a layer offset `(10, 2)` versus a literal `(offset=100)` —
    // stay distinct (C++ composes `SdfReference`s by authored value, then applies
    // the layer offset and time-codes retiming).
    // TODO(perf): linear scans of `folds`; fine for the short per-prim arc lists.
    let mut folds: Vec<(T, LayerOffset, f64)> = Vec::new();

    for node in nodes {
        // A layer that is sublayered from more than one place (a sublayer
        // diamond) appears multiple times in the node's layer stack, strongest
        // occurrence first. Its authored opinion at this path is identical at
        // every occurrence — only the composed offset differs — so it is read
        // once, at its strongest occurrence (C++ `GetLayerOffsetForLayer` is
        // single-valued per layer).
        let mut seen_layers: HashSet<usize> = HashSet::new();
        for &(layer, sub) in node.layer_stack() {
            if !seen_layers.insert(layer) {
                continue;
            }
            let Some(value) = layers[layer].try_get(&node.path, field)? else {
                continue;
            };
            let Some(mut list_op) = decode(value.into_owned()) else {
                continue;
            };
            // Anchor each item to the layer that authored it before composing, so
            // a relative asset path in different sublayers resolves to distinct
            // targets and is not wrongly deduped (e.g. `@./ref.usd@` authored in
            // `sub1/` and `sub2/` are two references, not one). The anchor resolves
            // the path and returns the time-codes scale to fold later — it does not
            // change the offset, so dedup still compares authored values.
            for item in list_op.iter_mut() {
                let scale = anchor(item, layer);
                if (!sub.is_identity() || scale != 1.0) && !folds.iter().any(|(i, _, _)| i == item) {
                    folds.push((item.clone(), sub, scale));
                }
            }
            combined = Some(match combined {
                Some(stronger) => stronger.combined_with(&list_op),
                None => list_op,
            });
        }
    }

    let mut result = combined.map(|op| op.reduced().flatten()).unwrap_or_default();
    for item in &mut result {
        if let Some((_, sub, scale)) = folds.iter().find(|(i, _, _)| i == item) {
            retime(item, *sub, *scale);
        }
    }
    Ok(result)
}

/// Composes an offset-free list-op field (inherits, specializes) by decoding
/// each opinion through `TryInto` and combining across the layer stack.
pub(super) fn compose_arc_list_in<T: Default + Clone + PartialEq>(
    nodes: &[Node],
    field: FieldKey,
    layers: &[sdf::Layer],
) -> Result<Vec<T>>
where
    Value: TryInto<ListOp<T>>,
{
    compose_list_op_in(
        nodes,
        field.as_str(),
        layers,
        |v| v.try_into().ok(),
        |_, _, _| {},
        |_, _| 1.0,
    )
}

/// Resolves `asset_path` against `layer`'s identifier, yielding the canonical
/// identifier of the targeted layer. Shared by [`anchor_asset_path`] (binding a
/// reference to its authoring layer) and [`find_layer`] (locating a parent-
/// relative sublayer).
///
/// TODO(perf): `create_identifier` canonicalizes via the filesystem, so this
/// runs a `canonicalize` per reference/payload per authoring layer per prim.
/// Cache resolved identifiers per (layer, asset_path) once the resolver exposes
/// a pure-string anchoring path.
fn resolve_against_layer(asset_path: &str, layer: &sdf::Layer, resolver: &dyn Resolver) -> String {
    let anchor = crate::ar::ResolvedPath::new(PathBuf::from(&layer.identifier));
    resolver.create_identifier(asset_path, Some(&anchor))
}

/// The retiming scale a reference or payload arc folds into its layer offset
/// when the introducing (authoring) layer and the referenced layer have
/// different time-codes-per-second rates (spec 12.3.2): `introducing / target`.
/// An internal arc (empty asset path) or an unresolved target retimes by 1.0.
/// `asset_path` must already be anchored to its authoring layer.
//
// TODO(perf): this `find_layer` re-resolves the target that
// `builder::add_ref_or_payload_arc` resolves again moments later for the same
// anchored path. The duplicate can't be hoisted trivially — the ratio's
// numerator is the per-member authoring rate, knowable only here inside the
// in-place list-op fold, while the target stack is needed there — so it waits on
// the asset-path resolution cache the `resolve_against_layer` TODO(perf) calls for.
fn arc_tcps_scale(introducing: &sdf::Layer, asset_path: &str, layers: &[sdf::Layer], resolver: &dyn Resolver) -> f64 {
    if asset_path.is_empty() {
        return 1.0;
    }
    find_layer(asset_path, layers, resolver).map_or(1.0, |target| {
        super::effective_time_codes_per_second(introducing) / super::effective_time_codes_per_second(&layers[target])
    })
}

/// Anchors a non-empty, non-absolute asset path to the layer that authored it,
/// so the same relative path in different layers resolves to distinct targets
/// (C++ resolves a reference's asset path against its authoring layer when the
/// layer stack is composed). An empty path (internal reference) is left as-is.
fn anchor_asset_path(asset_path: &mut String, authoring_layer: &sdf::Layer, resolver: &dyn Resolver) {
    if asset_path.is_empty() {
        return;
    }
    *asset_path = resolve_against_layer(asset_path, authoring_layer, resolver);
}

/// Resolves a reference/payload arc's asset path in place: evaluates a backtick
/// variable expression against `expr_vars`, anchors the result to its authoring
/// layer, and returns the time-codes-per-second retiming scale to fold into the
/// arc offset (spec 12.3.2). Shared by [`compose_references_in`] and
/// [`collect_payloads_in`], which differ only in their offset field's shape.
///
/// A malformed or non-string expression is recoverable (C++
/// `PcpErrorVariableExpression`): the failure is recorded in `errors`, the path
/// is left as the raw unevaluated expression for the caller to drop, and `None`
/// is returned so no scale is folded.
#[allow(clippy::too_many_arguments)]
fn resolve_arc_asset_path(
    asset_path: &mut String,
    authoring_layer: usize,
    layers: &[sdf::Layer],
    resolver: &dyn Resolver,
    expr_vars: &HashMap<String, Value>,
    arc: ArcType,
    site: &Path,
    errors: &mut Vec<Error>,
) -> Option<f64> {
    match expr::evaluate_asset_path(asset_path, expr_vars) {
        Ok(resolved) => *asset_path = resolved,
        Err(source) => {
            errors.push(Error::InvalidExpression {
                expression: asset_path.clone(),
                arc,
                site_path: site.clone(),
                message: source.to_string(),
            });
            return None;
        }
    }
    anchor_asset_path(asset_path, &layers[authoring_layer], resolver);
    Some(arc_tcps_scale(&layers[authoring_layer], asset_path, layers, resolver))
}

/// Composes the `references` list-op, folding each authoring sublayer's offset
/// into its references' layer offsets (C++ `PcpComposeSiteReferences`). A
/// reference brought in by a sublayer with a non-identity offset retimes its
/// target by that offset, which the per-site node otherwise carries only per
/// member. Each reference's asset path is anchored to its authoring layer so
/// relative paths in distinct sublayers stay distinct.
pub(super) fn compose_references_in(
    nodes: &[Node],
    layers: &[sdf::Layer],
    resolver: &dyn Resolver,
    expr_vars: &HashMap<String, Value>,
    site: &Path,
    errors: &mut Vec<Error>,
) -> Result<Vec<Reference>> {
    let mut refs = compose_list_op_in(
        nodes,
        FieldKey::References.as_str(),
        layers,
        |v| v.try_into().ok(),
        |r: &mut Reference, sub, scale| {
            if scale != 1.0 {
                r.layer_offset = r.layer_offset.concatenate(&sdf::LayerOffset::scale_only(scale));
            }
            if !sub.is_identity() {
                r.layer_offset = sub.concatenate(&r.layer_offset);
            }
        },
        |r: &mut Reference, layer| {
            resolve_arc_asset_path(
                &mut r.asset_path,
                layer,
                layers,
                resolver,
                expr_vars,
                ArcType::Reference,
                site,
                errors,
            )
            .unwrap_or(1.0)
        },
    )?;
    // A reference whose expression failed to evaluate keeps its raw backtick
    // path (the failure is already recorded in `errors`); drop it so it is not
    // mistaken for a literal asset path and grafted as a broken arc.
    refs.retain(|r| !expr::is_expression(&r.asset_path));
    Ok(refs)
}

/// Collects payloads from nodes, handling both single `Payload` and
/// `PayloadListOp`. Each authoring sublayer's offset is folded into its
/// payloads' layer offsets, mirroring [`compose_references_in`]; each payload's
/// asset path is anchored to its authoring layer.
pub(super) fn collect_payloads_in(
    nodes: &[Node],
    layers: &[sdf::Layer],
    resolver: &dyn Resolver,
    expr_vars: &HashMap<String, Value>,
    site: &Path,
    errors: &mut Vec<Error>,
) -> Result<Vec<Payload>> {
    let mut payloads = compose_list_op_in(
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
        // Fold the retiming only when it is not identity, so a payload with no
        // authored offset and no rate change keeps its `layer_offset` as `None`
        // (identity `Some` would change the serialized form without affecting
        // composition). Applied after the list-op composes so payloads are deduped
        // by authored value (see [`compose_list_op_in`]).
        |p: &mut Payload, sub, scale| {
            if scale != 1.0 {
                let offset = p.layer_offset.unwrap_or_default();
                p.layer_offset = Some(offset.concatenate(&sdf::LayerOffset::scale_only(scale)));
            }
            if !sub.is_identity() {
                p.layer_offset = Some(sub.concatenate(&p.layer_offset.unwrap_or_default()));
            }
        },
        |p: &mut Payload, layer| {
            resolve_arc_asset_path(
                &mut p.asset_path,
                layer,
                layers,
                resolver,
                expr_vars,
                ArcType::Payload,
                site,
                errors,
            )
            .unwrap_or(1.0)
        },
    )?;
    // A payload whose expression failed to evaluate keeps its raw backtick path
    // (the failure is already recorded in `errors`); drop it, as in
    // [`compose_references_in`].
    payloads.retain(|p| !expr::is_expression(&p.asset_path));
    Ok(payloads)
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
            let resolved = resolve_against_layer(asset_path, anchor_layer, resolver);
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
    use std::cmp::Ordering;

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
    ///
    /// The task-queue builder seeds a child prim from its cached parent, so the
    /// ancestors are composed top-down into a cache first (mirroring the cache's
    /// `ensure_index`), threading each prim's child context to the next.
    fn build_with_fallbacks(stack: &LayerStack, prim: &str, fallbacks: VariantFallbackMap) -> PrimIndex {
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

        let mut cache: HashMap<Path, PrimIndex> = HashMap::new();
        let mut parent_ctx = CompositionContext {
            variant_fallbacks: fallbacks,
            ..CompositionContext::default()
        };
        let mut last = None;
        for ancestor in &chain {
            let (index, _errors) =
                PrimIndex::build_with_cache(ancestor, stack, &parent_ctx, &cache).expect("index build failed");
            parent_ctx = index.context_for_children(stack, &parent_ctx);
            cache.insert(ancestor.clone(), index.clone());
            last = Some(index);
        }
        last.expect("a non-empty namespace chain")
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
    /// specialized prim's variant opinions to the composing prim (C++
    /// `_DetermineInheritPath` strips the parent's variant selections before
    /// mapping the class arc and re-adds the nearest containing one).
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let (_index, errors) = PrimIndex::build_with_cache(
            &Path::from("/Root"),
            &stack,
            &CompositionContext::default(),
            &HashMap::new(),
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let (_index, errors) = PrimIndex::build_with_cache(
            &Path::from("/Root"),
            &stack,
            &CompositionContext::default(),
            &HashMap::new(),
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let (index, errors) = PrimIndex::build_with_cache(
            &Path::from("/Prim"),
            &stack,
            &CompositionContext::default(),
            &HashMap::new(),
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
        let stack = LayerStack::new(layers, 0, Box::new(DefaultResolver::new()), true);

        let (index, errors) = PrimIndex::build_with_cache(
            &Path::from("/Prim"),
            &stack,
            &CompositionContext::default(),
            &HashMap::new(),
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
        let stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let index = build(&stack, "/NoSelection");
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

    /// When every configured fallback names a variant that does not exist in the
    /// set, the set stays unselected — no variant arc is added.
    #[test]
    fn variant_fallback_all_invalid_unselected() -> Result<()> {
        let stack = load_stack(&fixture_path("variant_fallback.usda"))?;
        let fb = VariantFallbackMap::new().add("shadingComplexity", ["ultra", "mega"]);
        let index = build_with_fallbacks(&stack, "/NoSelection", fb);
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
