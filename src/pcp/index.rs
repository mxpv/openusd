//! Per-prim composition index (`PcpPrimIndex` equivalent).
//!
//! A [`PrimIndex`] records the strength-ordered list of layer specs that
//! contribute opinions to a single composed prim. See the
//! [module-level docs](super) for the full composition overview.

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{LayerData, ListOp, Path, Payload, PayloadListOp, Reference, Value};

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

/// Compact index into the graph's node arena.
///
/// A lightweight handle identifying a single [`Node`] within a
/// [`PrimIndex`]'s composition graph. The sentinel value [`INVALID`](Self::INVALID)
/// represents "no node" (analogous to C++ `_invalidNodeIndex`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeIndex(u32);

impl NodeIndex {
    /// Sentinel: no node.
    pub const INVALID: Self = Self(u32::MAX);

    /// Returns `true` if this index points to an actual node.
    pub fn is_valid(self) -> bool {
        self.0 != u32::MAX
    }

    /// Converts to a `usize` for indexing into a `Vec`.
    pub(crate) fn idx(self) -> usize {
        self.0 as usize
    }
}

/// A single node in the composition graph.
///
/// Each node represents a site (layer + path) contributing opinions to a
/// composed prim. The identity fields (`layer_index`, `path`, `arc`)
/// define *what* this node contributes. The namespace mappings
/// (`map_to_parent`, `map_to_root`) translate paths across composition arcs.
#[derive(Debug, Clone)]
pub struct Node {
    /// Index into the stage's layer list.
    pub layer_index: usize,
    /// The path within that layer (may differ from composed path due to remapping).
    pub path: Path,
    /// The composition arc that introduced this node.
    pub arc: ArcType,
    /// Maps paths from this node's namespace to its parent's namespace.
    pub map_to_parent: MapFunction,
    /// Maps paths from this node's namespace directly to the root namespace.
    /// Computed as `parent.map_to_root.compose(self.map_to_parent)`.
    pub map_to_root: MapFunction,
    /// True when this node was introduced through a specializes composition
    /// arc (directly or transitively). Nodes with this flag are globally
    /// weaker than all other opinions per spec section 10.4.1.
    pub(crate) introduced_by_specialize: bool,
}

/// Arena-based composition graph.
///
/// Stores [`Node`]s in a flat `Vec` where links between nodes are encoded
/// as [`NodeIndex`] values. Nodes are ordered strongest-to-weakest by
/// insertion order (matching the LIVRPS evaluation sequence).
#[derive(Debug, Clone, Default)]
pub(crate) struct PrimIndexGraph {
    nodes: Vec<Node>,
}

impl PrimIndexGraph {
    fn len(&self) -> usize {
        self.nodes.len()
    }

    fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Appends a node to the graph and computes its `map_to_root`.
    ///
    /// `parent` identifies the structural parent in the composition graph.
    /// When valid, `map_to_root` is composed from the parent's `map_to_root`
    /// and the new node's `map_to_parent`. Nodes are ordered by insertion
    /// (strongest to weakest).
    fn add_child(
        &mut self,
        parent: NodeIndex,
        layer_index: usize,
        path: Path,
        arc: ArcType,
        map_to_parent: MapFunction,
        introduced_by_specialize: bool,
    ) -> NodeIndex {
        let map_to_root = if parent.is_valid() {
            self.nodes[parent.idx()].map_to_root.compose(&map_to_parent)
        } else {
            map_to_parent.clone()
        };
        let idx = NodeIndex(self.nodes.len() as u32);
        self.nodes.push(Node {
            layer_index,
            path,
            arc,
            map_to_parent,
            map_to_root,
            introduced_by_specialize,
        });
        idx
    }
}

impl std::ops::Deref for PrimIndexGraph {
    type Target = [Node];
    fn deref(&self) -> &[Node] {
        &self.nodes
    }
}

/// Composition index for a single prim.
///
/// Contains a graph of [`Node`]s ordered from strongest to weakest.
/// Value resolution walks nodes in strength order and takes the first
/// opinion found.
#[derive(Debug, Clone, Default)]
pub struct PrimIndex {
    /// Composition graph with nodes in strength order.
    graph: PrimIndexGraph,
}

impl PrimIndex {
    /// Returns `true` if no layers contribute opinions for this prim.
    pub fn is_empty(&self) -> bool {
        self.graph.is_empty()
    }

    /// Returns the nodes in strength order (index 0 = strongest).
    pub fn nodes(&self) -> &[Node] {
        &self.graph
    }

    /// Appends a node to the end of the composition graph.
    pub(crate) fn push_node(&mut self, node: Node) {
        self.graph.nodes.push(node);
    }

    /// Inserts a relocate node at the correct LIVERPS strength position.
    ///
    /// Finds the first node whose arc type is weaker than `Relocate`
    /// (i.e. `Reference`, `Payload`, or `Specialize`) and inserts before it.
    pub(crate) fn insert_relocate_node(&mut self, node: Node) {
        let pos = self
            .graph
            .nodes
            .iter()
            .position(|n| n.arc > ArcType::Relocate)
            .unwrap_or(self.graph.nodes.len());
        self.graph.nodes.insert(pos, node);
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
        if let Some(cached) = cached_indices.get(path) {
            return Ok(cached.clone());
        }
        let mut builder = IndexBuilder::new(stack, ctx, cached_indices);
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
        // Gather variant selections from this prim's nodes.
        let selections = resolve_variant_selections_in(self.nodes(), &stack.layers, &parent_ctx.variant_fallbacks);

        // Build ancestor arcs: for each non-Root node whose map_to_root is
        // not a no-op, record it so children can remap through it.
        // We use map_to_root (not map_to_parent) because ancestor propagation
        // needs to translate all the way to the composed namespace.
        let mut ancestor_arcs = parent_ctx.ancestor_arcs.clone();
        for node in self.nodes() {
            if node.arc == ArcType::Root || node.map_to_root.is_noop() {
                continue;
            }
            ancestor_arcs.push(AncestorArc {
                map: node.map_to_root.clone(),
                layer_index: node.layer_index,
                arc: node.arc,
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
        }
    }

    /// Resolves a field by walking nodes from strongest to weakest, returning the first opinion.
    ///
    /// When `prop_suffix` is `None`, queries use the node's path directly (zero-copy).
    /// When `Some`, appends the suffix to form a property path for each node.
    /// A [`Value::ValueBlock`] explicitly blocks opinions from weaker layers.
    pub(crate) fn resolve_field(
        &self,
        field: &str,
        stack: &LayerStack,
        prop_suffix: Option<&str>,
    ) -> Result<Option<Value>> {
        for node in self.nodes() {
            let query_path = match prop_suffix {
                Some(suffix) => Cow::Owned(Path::new(&format!("{}{suffix}", node.path))?),
                None => Cow::Borrowed(&node.path),
            };

            let data = stack.layer(node.layer_index);
            if !data.has_field(&query_path, field) {
                continue;
            }

            let value = data.get(&query_path, field)?;
            if matches!(value.as_ref(), Value::ValueBlock) {
                return Ok(None);
            }
            return Ok(Some(value.into_owned()));
        }

        Ok(None)
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
    /// Layer index where the arc target lives.
    pub layer_index: usize,
    /// Arc type that introduced this mapping.
    pub arc: ArcType,
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
    /// All nodes created while true are marked for global weakness
    /// reordering per spec section 10.4.1.
    in_specialize: bool,
}

impl<'a> IndexBuilder<'a> {
    fn new(stack: &'a LayerStack, ctx: &'a CompositionContext, cached_indices: &'a HashMap<Path, PrimIndex>) -> Self {
        Self {
            stack,
            ctx,
            cached_indices,
            output: PrimIndexGraph::default(),
            seen: HashSet::new(),
            eval_stack: HashSet::new(),
            target_indices: HashMap::new(),
            in_specialize: false,
        }
    }

    /// Build the prim index for the given composed path.
    ///
    /// Evaluates all composition sites (root + ancestor-derived), then loops
    /// until stable: if variant resolution produces new nodes (because R/P
    /// arcs introduced variant sets that V hadn't seen), their arcs are
    /// followed and variants re-resolved.
    fn build(&mut self, path: &Path) -> Result<(), Error> {
        let root_stack: Vec<usize> = (0..self.stack.len()).collect();

        // Evaluate root composition site (no parent — this is the graph root).
        self.eval_site(
            path,
            &root_stack,
            ArcType::Root,
            0,
            NodeIndex::INVALID,
            MapFunction::identity(),
        )?;

        // Propagate ancestor arcs: only match arcs whose target (composed)
        // prefix equals the parent path, then remap by appending the child name.
        // This mirrors C++ behavior where each level only uses its direct
        // parent's arc mappings for descendant propagation.
        let child_name = path.as_str().rsplit('/').next().unwrap_or("");
        if !child_name.is_empty() {
            let parent = path.parent();
            let ancestor_sites: Vec<_> = self
                .ctx
                .ancestor_arcs
                .iter()
                .filter_map(|a| {
                    // Map the parent path through this arc. Only arcs whose target
                    // prefix matches the parent will succeed.
                    let parent_in_source = a.map.map_target_to_source(parent.as_ref()?)?;
                    let remapped = Path::new(&format!("{parent_in_source}/{child_name}")).ok()?;
                    Some((remapped, a.layer_index, a.arc, a.map.clone()))
                })
                .collect();
            for (rpath, li, arc, map) in &ancestor_sites {
                self.eval_site(rpath, &[*li], *arc, 0, NodeIndex::INVALID, map.clone())?;
            }
        }

        // Loop until stable: R/P arcs may introduce variant sets that V
        // hadn't seen. Re-resolve variants and follow any new arcs.
        self.stabilize()?;

        // Global weakness: specializes opinions are globally weaker than all
        // other opinions (spec 10.4.1). Stable-partition so non-specialize
        // nodes come first, preserving relative order within each group.
        self.apply_specialize_weakness();

        Ok(())
    }

    /// Reorders nodes so that all opinions introduced through specializes arcs
    /// appear after all other opinions, implementing the global weakness
    /// requirement from spec section 10.4.1.
    fn apply_specialize_weakness(&mut self) {
        // Stable sort with a bool key (false < true) acts as an in-place
        // stable partition: non-specialize nodes stay first, specialize nodes
        // move to the end, and relative order within each group is preserved.
        self.output.nodes.sort_by_key(|n| n.introduced_by_specialize);
    }

    /// Re-resolve variants across all accumulated nodes until no new nodes
    /// are produced. Handles the LIVRPS ordering gap where V runs before R/P
    /// but variant sets may come from referenced/payloaded layers.
    fn stabilize(&mut self) -> Result<(), Error> {
        // Track already-processed variant paths across loop iterations.
        let mut processed: HashSet<Path> = self
            .output
            .iter()
            .filter(|n| n.arc == ArcType::Variant)
            .map(|n| n.path.clone())
            .collect();

        loop {
            let before = self.output.len();

            let mut selections =
                resolve_variant_selections_in(&self.output, &self.stack.layers, &self.ctx.variant_fallbacks);
            for (set, sel) in &self.ctx.selections {
                selections.entry(set.clone()).or_insert_with(|| sel.clone());
            }

            let orig_len = self.output.len();
            for (set_name, selection) in &selections {
                for idx in 0..orig_len {
                    let variant_path = self.output[idx].path.append_variant_selection(set_name, selection);
                    if !processed.insert(variant_path.clone()) {
                        continue;
                    }
                    let base_node = NodeIndex(idx as u32);
                    let base_prim_path = self.output[idx].path.clone();

                    // Propagate specialize context from base node for global weakness.
                    let prev_in_specialize = self.in_specialize;
                    if self.output[idx].introduced_by_specialize {
                        self.in_specialize = true;
                    }

                    let (start, end) = self.add_variant_nodes(&variant_path, &base_prim_path, base_node);
                    // Follow arcs from newly discovered variant nodes.
                    if start < end {
                        let new_nodes: Vec<Node> = self.output[start..end].to_vec();
                        let refs =
                            compose_arc_list_in::<Reference>(&new_nodes, FieldKey::References, &self.stack.layers);
                        let payloads = collect_payloads_in(&new_nodes, &self.stack.layers);
                        for reference in &refs {
                            self.eval_arc_target(
                                &reference.asset_path,
                                &reference.prim_path,
                                ArcType::Reference,
                                &Path::abs_root(),
                                0,
                                base_node,
                            )?;
                        }
                        for payload in &payloads {
                            self.eval_arc_target(
                                &payload.asset_path,
                                &payload.prim_path,
                                ArcType::Payload,
                                &Path::abs_root(),
                                0,
                                base_node,
                            )?;
                        }
                    }

                    self.in_specialize = prev_in_specialize;
                }
            }

            // Stable — no new nodes produced.
            if self.output.len() == before {
                break;
            }
        }
        Ok(())
    }

    /// Evaluate a single composition site: run LIVRPS for `path` within
    /// `layer_stack`. Called recursively for each arc target.
    ///
    /// `map_to_parent` is the namespace mapping for L nodes created at this
    /// site (translates from `path`'s namespace to the parent node's namespace).
    fn eval_site(
        &mut self,
        path: &Path,
        layer_stack: &[usize],
        arc: ArcType,
        depth: usize,
        parent: NodeIndex,
        map_to_parent: MapFunction,
    ) -> Result<(), Error> {
        if depth > MAX_COMPOSITION_DEPTH {
            return Err(Error::ArcCycle {
                path: path.clone(),
                depth,
            });
        }

        // Cycle detection: if this (root_layer, path) site is already being
        // evaluated somewhere up the call stack, we have a composition cycle.
        let Some(&root_layer) = layer_stack.first() else {
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

        let result = self.eval_site_body(path, layer_stack, arc, depth, parent, map_to_parent);
        self.in_specialize = prev_in_specialize;
        self.eval_stack.remove(&site_key);
        result
    }

    fn eval_site_body(
        &mut self,
        path: &Path,
        layer_stack: &[usize],
        arc: ArcType,
        depth: usize,
        parent: NodeIndex,
        map_to_parent: MapFunction,
    ) -> Result<(), Error> {
        let site_start = self.output.len();

        // L — Local opinions: check each layer in the stack for a spec.
        // The first L node becomes the "site representative" — parent for
        // subsequent arcs discovered at this site.
        let mut site_node = NodeIndex::INVALID;
        for &i in layer_stack {
            if self.stack.layer(i).has_spec(path) && self.seen.insert((i, path.clone(), arc)) {
                let idx =
                    self.output
                        .add_child(parent, i, path.clone(), arc, map_to_parent.clone(), self.in_specialize);
                if !site_node.is_valid() {
                    site_node = idx;
                }
            }
        }

        // I — Inherits: compose InheritPaths. Build a full index for each
        // target (which includes ancestor context) and merge its nodes.
        // Implied arcs are propagated inline through ancestor arc mappings.
        let inherits =
            compose_arc_list_in::<Path>(&self.output[site_start..], FieldKey::InheritPaths, &self.stack.layers);
        for inherit_path in &inherits {
            let resolved = path.make_absolute(inherit_path);
            let before = self.output.len();
            self.merge_full_index(&resolved, ArcType::Inherit, site_node)?;
            self.add_implied_nodes(before, ArcType::Inherit, site_node);
            for vt in variant_expanded_targets(path, &resolved) {
                let before = self.output.len();
                self.merge_full_index(&vt, ArcType::Inherit, site_node)?;
                self.add_implied_nodes(before, ArcType::Inherit, site_node);
            }
        }

        // V — Variants: resolve selections iteratively (nested variant sets).
        self.eval_variants(site_start, site_node);

        // Collect range of all opinion nodes (L + I + V) for R/P/S lookups.
        let opinion_end = self.output.len();

        // R — References.
        let references = compose_arc_list_in::<Reference>(
            &self.output[site_start..opinion_end],
            FieldKey::References,
            &self.stack.layers,
        );
        for reference in &references {
            self.eval_arc_target(
                &reference.asset_path,
                &reference.prim_path,
                ArcType::Reference,
                path,
                depth,
                site_node,
            )?;
        }

        // P — Payloads.
        let payloads = collect_payloads_in(&self.output[site_start..opinion_end], &self.stack.layers);
        for payload in &payloads {
            self.eval_arc_target(
                &payload.asset_path,
                &payload.prim_path,
                ArcType::Payload,
                path,
                depth,
                site_node,
            )?;
        }

        // S — Specializes.
        let specializes = compose_arc_list_in::<Path>(
            &self.output[site_start..opinion_end],
            FieldKey::Specializes,
            &self.stack.layers,
        );
        for specialize_path in &specializes {
            let resolved = path.make_absolute(specialize_path);
            let before = self.output.len();
            self.merge_full_index(&resolved, ArcType::Specialize, site_node)?;
            self.add_implied_nodes(before, ArcType::Specialize, site_node);
        }

        Ok(())
    }

    /// Propagate implied arcs for inherit/specialize nodes added since `start`.
    ///
    /// Remaps through ancestor arc namespace mappings. For each remapped path,
    /// uses the cached index if available (giving full LIVRPS evaluation
    /// matching C++ PCP's `EvalImpliedClasses`), otherwise falls back to
    /// direct layer spec lookups.
    fn add_implied_nodes(&mut self, start: usize, arc: ArcType, origin: NodeIndex) {
        if self.ctx.ancestor_arcs.is_empty() {
            return;
        }

        // Track specialize context for global weakness (spec 10.4.1).
        let prev_in_specialize = self.in_specialize;
        if arc == ArcType::Specialize {
            self.in_specialize = true;
        }

        let paths_to_check: Vec<Path> = self.output[start..]
            .iter()
            .filter(|n| n.arc == ArcType::Inherit || n.arc == ArcType::Specialize)
            .map(|n| n.path.clone())
            .collect();

        for node_path in &paths_to_check {
            for (idx, mapping) in self.ctx.ancestor_arcs.iter().enumerate() {
                let Some(remapped) = mapping.map.map_source_to_target(node_path) else {
                    continue;
                };
                if remapped == *node_path {
                    continue;
                }

                // Use cached index for full LIVRPS evaluation when available.
                if let Some(cached) = self.cached_indices.get(&remapped) {
                    for node in cached.nodes() {
                        if self.seen.insert((node.layer_index, node.path.clone(), arc)) {
                            let implied_map = MapFunction::from_pair_identity(node.path.clone(), remapped.clone());
                            self.output.add_child(
                                NodeIndex::INVALID,
                                node.layer_index,
                                node.path.clone(),
                                arc,
                                implied_map,
                                self.in_specialize,
                            );
                        }
                    }
                } else {
                    // Fallback: check individual layers for direct specs.
                    let implied_map = MapFunction::from_pair_identity(node_path.clone(), remapped.clone());
                    for li in 0..self.stack.len() {
                        if self.stack.layer(li).has_spec(&remapped) && self.seen.insert((li, remapped.clone(), arc)) {
                            self.output.add_child(
                                NodeIndex::INVALID,
                                li,
                                remapped.clone(),
                                arc,
                                implied_map.clone(),
                                self.in_specialize,
                            );
                        }
                    }
                }

                // Cross-remap through other ancestor arcs: composed → other source namespace.
                for (other_idx, other) in self.ctx.ancestor_arcs.iter().enumerate() {
                    if other_idx == idx {
                        continue;
                    }
                    let Some(other_remapped) = other.map.map_target_to_source(&remapped) else {
                        continue;
                    };
                    let li = other.layer_index;
                    if self.stack.layer(li).has_spec(&other_remapped)
                        && self.seen.insert((li, other_remapped.clone(), arc))
                    {
                        let other_map = MapFunction::from_pair_identity(node_path.clone(), other_remapped.clone());
                        self.output
                            .add_child(origin, li, other_remapped, arc, other_map, self.in_specialize);
                    }
                }
            }
        }

        self.in_specialize = prev_in_specialize;
    }

    fn get_sublayer_stack(&self, root_layer: usize) -> Vec<usize> {
        self.stack.sublayer_stacks.get(&root_layer).cloned().unwrap_or_else(|| {
            LayerStack::build_sublayer_stack(root_layer, &self.stack.layers, &self.stack.identifiers)
        })
    }

    /// Build a full PrimIndex for a target path and merge its nodes into this
    /// builder's output. Used for inherit/specialize targets that need their
    /// own ancestor propagation.
    ///
    /// Checks the composition cache first (for fully-composed indices including
    /// ancestor-propagated specs), then the builder-local cache, and finally
    /// builds from scratch with the current prim's context.
    fn merge_full_index(&mut self, target: &Path, arc: ArcType, parent: NodeIndex) -> Result<(), Error> {
        // Track specialize context for global weakness (spec 10.4.1).
        let prev_in_specialize = self.in_specialize;
        if arc == ArcType::Specialize {
            self.in_specialize = true;
        }

        if !self.target_indices.contains_key(target) {
            // Prefer the composition cache — it has the fully-composed result
            // including propagate_parent_specs.
            if let Some(cached) = self.cached_indices.get(target) {
                self.target_indices.insert(target.clone(), cached.clone());
            } else {
                // Build the target's ancestor context using the current prim's
                // context so ancestor arcs are available.
                let ctx = if let Some(parent) = target.parent() {
                    if parent != Path::abs_root() {
                        if !self.target_indices.contains_key(&parent) {
                            let parent_idx = if let Some(cp) = self.cached_indices.get(&parent) {
                                cp.clone()
                            } else {
                                PrimIndex::build_with_context(&parent, self.stack, self.ctx)?
                            };
                            self.target_indices.insert(parent.clone(), parent_idx);
                        }
                        let parent_idx = &self.target_indices[&parent];
                        parent_idx.context_for_children(self.stack, self.ctx)
                    } else {
                        CompositionContext::default()
                    }
                } else {
                    CompositionContext::default()
                };
                let idx = PrimIndex::build_with_context(target, self.stack, &ctx)?;
                self.target_indices.insert(target.clone(), idx);
            }
        }
        let target_index = &self.target_indices[target];
        // The mapping for merged nodes translates from the target's namespace
        // to the parent node's namespace (the inheriting/specializing prim).
        let parent_path = if parent.is_valid() {
            self.output[parent.idx()].path.clone()
        } else {
            target.clone()
        };
        for node in target_index.nodes() {
            if self.seen.insert((node.layer_index, node.path.clone(), arc)) {
                // Each node maps from its own path to the parent's composed path.
                let node_map = MapFunction::from_pair_identity(node.path.clone(), parent_path.clone());
                self.output.add_child(
                    parent,
                    node.layer_index,
                    node.path.clone(),
                    arc,
                    node_map,
                    self.in_specialize,
                );
            }
        }

        self.in_specialize = prev_in_specialize;
        Ok(())
    }

    /// Adds variant nodes for `variant_path` across all layers. Returns
    /// the index range of newly added nodes.
    fn add_variant_nodes(&mut self, variant_path: &Path, base: &Path, parent: NodeIndex) -> (usize, usize) {
        let start = self.output.len();
        let variant_map = MapFunction::from_pair_identity(variant_path.clone(), base.clone());
        for (i, layer) in self.stack.layers.iter().enumerate() {
            if layer.has_spec(variant_path) && self.seen.insert((i, variant_path.clone(), ArcType::Variant)) {
                self.output.add_child(
                    parent,
                    i,
                    variant_path.clone(),
                    ArcType::Variant,
                    variant_map.clone(),
                    self.in_specialize,
                );
            }
        }
        (start, self.output.len())
    }

    /// Resolve variant selections iteratively, handling nested variant sets
    /// and variant sets on inherited classes.
    fn eval_variants(&mut self, site_start: usize, parent: NodeIndex) {
        let mut processed = HashSet::new();
        loop {
            let current_end = self.output.len();
            // Gather selections from ALL output nodes (not just this site) so
            // cross-site selections are visible during the first pass.
            let mut selections = resolve_variant_selections_in(
                &self.output[..current_end],
                &self.stack.layers,
                &self.ctx.variant_fallbacks,
            );
            // Merge accumulated selections (includes ancestor context).
            for (set, sel) in &self.ctx.selections {
                selections.entry(set.clone()).or_insert_with(|| sel.clone());
            }
            if selections.is_empty() {
                break;
            }
            let before = self.output.len();
            for (set_name, selection) in &selections {
                // Try appending variant to every node in this site (not all output —
                // variant sets belong to this site's paths).
                let bases: Vec<Path> = self.output[site_start..before].iter().map(|n| n.path.clone()).collect();
                for base in &bases {
                    let variant_path = base.append_variant_selection(set_name, selection);
                    if !processed.insert(variant_path.clone()) {
                        continue;
                    }
                    self.add_variant_nodes(&variant_path, base, parent);
                }
            }

            if self.output.len() == before {
                break;
            }
        }
    }

    /// Evaluate a reference or payload target.
    fn eval_arc_target(
        &mut self,
        asset_path: &str,
        prim_path: &Path,
        arc: ArcType,
        context_path: &Path,
        depth: usize,
        parent: NodeIndex,
    ) -> Result<(), Error> {
        if asset_path.is_empty() {
            // Internal reference — build full index for target (with ancestor
            // context) so variant selections and arc mappings propagate.
            if prim_path.is_empty() {
                return Ok(());
            }
            self.merge_full_index(prim_path, arc, parent)?;
            for vt in variant_expanded_targets(context_path, prim_path) {
                self.merge_full_index(&vt, arc, parent)?;
            }
        } else {
            // External reference — evaluate in a fresh sub-builder so the
            // target's layer stack doesn't share our `seen` set. The sub-builder
            // uses its own ancestor context derived from the target path.
            let Some(layer_index) = find_layer(asset_path, &self.stack.identifiers) else {
                return Err(Error::UnresolvedLayer {
                    asset_path: asset_path.to_string(),
                    arc,
                    site_path: context_path.clone(),
                });
            };
            let layer_id = self.stack.identifier(layer_index).to_owned();
            let source = if prim_path.is_empty() {
                let root = Path::abs_root();
                let Ok(value) = self.stack.layer(layer_index).get(&root, FieldKey::DefaultPrim.as_str()) else {
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
            let arc_map = MapFunction::from_pair(source.clone(), context_path.clone());
            // Evaluate directly — arc-type-aware dedup allows the same
            // (layer, path) to appear under different arc types.
            self.eval_site(&source, &target_stack, arc, depth + 1, parent, arc_map)?;
            // Also propagate ancestor arcs within the target layer.
            if let Some(source_parent) = source.parent() {
                if source_parent != Path::abs_root() {
                    let child_name = source.as_str().rsplit('/').next().unwrap_or("");
                    let parent_index = PrimIndex::build_with_context(&source_parent, self.stack, self.ctx)?;
                    let ancestor_sites: Vec<_> = parent_index
                        .nodes()
                        .iter()
                        .filter(|n| n.arc != ArcType::Root)
                        .filter_map(|n| {
                            Path::new(&format!("{}/{child_name}", n.path))
                                .ok()
                                .map(|p| (p, n.layer_index, n.arc, n.path.clone()))
                        })
                        .collect();
                    for (rpath, li, a, node_path) in &ancestor_sites {
                        let ancestor_map = MapFunction::from_pair(node_path.clone(), context_path.clone());
                        self.eval_site(rpath, &[*li], *a, depth + 1, parent, ancestor_map)?;
                    }
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Shared helpers (used by IndexBuilder and Stage)
// ---------------------------------------------------------------------------

/// Expands an internal reference target by inserting variant segments from
/// the context path.
///
/// If the context is `/Model{vset=with_children}/Foo` and the target is
/// `/Model/_prototype`, returns `[/Model{vset=with_children}/_prototype]`.
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
                let expanded = format!("{prim_prefix}{variant_segment}{after_prefix}");
                if let Ok(p) = Path::new(&expanded) {
                    results.push(p);
                }
            }
        }

        pos = close + 1;
    }

    results
}

/// Resolves variant selections by walking nodes strongest-to-weakest.
///
/// Gathers explicit selections (first opinion wins), then falls back to
/// the first variant name in each variant set as the default.
fn resolve_variant_selections_in(
    nodes: &[Node],
    layers: &[LayerData],
    variant_fallbacks: &VariantFallbackMap,
) -> HashMap<String, String> {
    let mut selections: HashMap<String, String> = HashMap::new();

    // Gather explicit selections (first opinion wins).
    for node in nodes {
        let data = &layers[node.layer_index];
        if let Ok(value) = data.get(&node.path, FieldKey::VariantSelection.as_str()) {
            if let Value::VariantSelectionMap(map) = value.into_owned() {
                for (set_name, selection) in map {
                    selections.entry(set_name).or_insert(selection);
                }
            }
        }
    }

    // For variant sets without an explicit selection, try the fallback map
    // first, then fall back to the first variant name in the set.
    for node in nodes {
        let data = &layers[node.layer_index];
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

    selections
}

/// Composes a list-op field across nodes, returning the flattened list.
fn compose_arc_list_in<T: Default + Clone + PartialEq>(nodes: &[Node], field: FieldKey, layers: &[LayerData]) -> Vec<T>
where
    Value: TryInto<ListOp<T>>,
{
    let field = field.as_str();
    let mut combined: Option<ListOp<T>> = None;

    for node in nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, field) else {
            continue;
        };
        let Ok(list_op) = value.into_owned().try_into() else {
            continue;
        };
        combined = Some(match combined {
            Some(stronger) => stronger.combined_with(&list_op),
            None => list_op,
        });
    }

    combined.map(|op| op.reduced().flatten()).unwrap_or_default()
}

/// Collects payloads from nodes, handling both single `Payload` and `PayloadListOp`.
fn collect_payloads_in(nodes: &[Node], layers: &[LayerData]) -> Vec<Payload> {
    let mut combined: Option<PayloadListOp> = None;

    for node in nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, FieldKey::Payload.as_str()) else {
            continue;
        };

        let list_op = match value.into_owned() {
            Value::Payload(p) => PayloadListOp {
                explicit: true,
                explicit_items: vec![p],
                ..Default::default()
            },
            Value::PayloadListOp(op) => op,
            _ => continue,
        };

        combined = Some(match combined {
            Some(stronger) => stronger.combined_with(&list_op),
            None => list_op,
        });
    }

    combined.map(|op| op.reduced().flatten()).unwrap_or_default()
}

/// Finds a layer index whose identifier matches `asset_path`.
///
/// Tries an exact match first, then falls back to suffix matching at a
/// path separator boundary. Strips leading `./` before matching.
pub(super) fn find_layer(asset_path: &str, identifiers: &[String]) -> Option<usize> {
    let sep = std::path::MAIN_SEPARATOR as u8;
    let needle = asset_path.strip_prefix("./").unwrap_or(asset_path);

    for (i, id) in identifiers.iter().enumerate() {
        if *id == needle {
            return Some(i);
        }

        if id.ends_with(needle) {
            let prefix_len = id.len() - needle.len();
            if prefix_len > 0 && id.as_bytes()[prefix_len - 1] == sep {
                return Some(i);
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
    use crate::layer::collect_layers;
    use crate::sdf::LayerData;

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

    /// Loads layers and splits into parallel vecs for PrimIndex::build.
    fn load_layers(path: &str) -> Result<(Vec<LayerData>, Vec<String>)> {
        let resolver = DefaultResolver::new();
        let collected = collect_layers(&resolver, path)?;
        let mut layers = Vec::new();
        let mut identifiers = Vec::new();
        for layer in collected {
            identifiers.push(layer.identifier);
            layers.push(layer.data);
        }
        Ok((layers, identifiers))
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
        let (layers, identifiers) = load_layers(path)?;
        Ok(LayerStack::new(layers, identifiers, 0))
    }

    #[test]
    fn single_layer_root_node() -> Result<()> {
        let stack = load_stack(&composition_path("active.usda"))?;
        let index = build(&stack, "/World");

        assert_eq!(index.nodes().len(), 1);
        assert_eq!(index.nodes()[0].layer_index, 0);
        assert_eq!(index.nodes()[0].arc, ArcType::Root);
        Ok(())
    }

    #[test]
    fn sublayer_two_root_nodes() -> Result<()> {
        let stack = load_stack(&fixture_path("sublayer_override.usda"))?;
        let index = build(&stack, "/World");

        assert_eq!(index.nodes().len(), 2, "both layers should have /World");
        assert_eq!(index.nodes()[0].layer_index, 0, "stronger layer first");
        assert_eq!(index.nodes()[1].layer_index, 1, "weaker layer second");
        Ok(())
    }

    #[test]
    fn prim_only_in_stronger_layer() -> Result<()> {
        let stack = load_stack(&fixture_path("sublayer_override.usda"))?;
        let index = build(&stack, "/World/Sphere");

        assert_eq!(index.nodes().len(), 1);
        assert_eq!(index.nodes()[0].layer_index, 0);
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

        assert!(index.nodes().iter().any(|n| n.arc == ArcType::Reference));
        Ok(())
    }

    #[test]
    fn inherit_arc_present() -> Result<()> {
        let stack = load_stack(&composition_path("class_inherit.usda"))?;
        let index = build(&stack, "/World/cubeWithoutSetColor");

        assert!(index.nodes().iter().any(|n| n.arc == ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn inherit_root_is_strongest() -> Result<()> {
        let stack = load_stack(&composition_path("class_inherit.usda"))?;
        let index = build(&stack, "/World/cubeWithSetColor");
        let arcs: Vec<_> = index.nodes().iter().map(|n| n.arc).collect();

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

        assert!(index.nodes().iter().any(|n| n.arc == ArcType::Variant));

        let variant_node = index.nodes().iter().find(|n| n.arc == ArcType::Variant).unwrap();
        assert_eq!(variant_node.path.as_str(), "/World/Sphere{size=small}");
        Ok(())
    }

    #[test]
    fn specialize_arc_present() -> Result<()> {
        let stack = load_stack(&composition_path("inherit_and_specialize.usda"))?;
        let index = build(&stack, "/World/cubeScene/specializes");

        assert!(index.nodes().iter().any(|n| n.arc == ArcType::Specialize));
        Ok(())
    }

    #[test]
    fn find_layer_exact_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer(&ids[0], &ids).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_suffix_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("ref_target.usda", &ids).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_no_partial_name_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("target.usda", &ids).is_none());
        Ok(())
    }

    #[test]
    fn find_layer_not_found() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("nonexistent.usda", &ids).is_none());
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
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/A"),
            "should have node from A.usd"
        );
        assert!(
            index
                .nodes()
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/B"),
            "should have node from B.usd"
        );
        assert!(
            index
                .nodes()
                .iter()
                .any(|n| n.arc == ArcType::Reference && n.path.as_str() == "/C"),
            "should have node from C.usd via nested reference"
        );

        let a_idx = find_layer("A.usd", &stack.identifiers).unwrap();
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
            index.nodes().iter().any(|n| n.arc == ArcType::Specialize),
            "should have specialize node from variant"
        );
        assert!(
            index
                .nodes()
                .iter()
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
            find_layer("camera_perspective.usd", &stack.identifiers).is_some(),
            "camera_perspective.usd should be collected from variant reference"
        );

        let index = build(&stack, "/main_cam/Lens");
        assert!(
            index
                .nodes()
                .iter()
                .any(|n| n.path.as_str() == "/camera/_localclass_Lens"),
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
            index.nodes().iter().any(|n| n.path.as_str().contains("{geotype=cube}")),
            "should have geotype=cube variant node from inherited selection"
        );
        Ok(())
    }

    // --- Error reporting ---

    fn parse_usda(text: &str) -> LayerData {
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
        let layers = vec![a, b];
        let ids = vec!["a.usd".to_string(), "b.usd".to_string()];
        let stack = LayerStack::new(layers, ids, 0);

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
        let layers = vec![layer];
        let ids = vec!["test.usda".to_string()];
        let stack = LayerStack::new(layers, ids, 0);

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
        let layers = vec![root, target];
        let ids = vec!["root.usda".to_string(), "target.usda".to_string()];
        let stack = LayerStack::new(layers, ids, 0);

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
            .iter()
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
        let node = |arc: ArcType| Node {
            layer_index: 0,
            path: p("/X"),
            arc,
            map_to_parent: MapFunction::identity(),
            map_to_root: MapFunction::identity(),
            introduced_by_specialize: false,
        };

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

        let arcs: Vec<ArcType> = index.nodes().iter().map(|n| n.arc).collect();
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
        identifier.rsplit('/').next().unwrap_or(identifier)
    }

    /// Formats a prim stack as a vec of (layer_name, path) pairs for assertion.
    fn prim_stack(index: &PrimIndex, stack: &LayerStack) -> Vec<(String, String)> {
        index
            .nodes()
            .iter()
            .map(|n| {
                (
                    layer_name(stack.identifier(n.layer_index)).to_owned(),
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

        // Verify the introduced_by_specialize flag: first 3 nodes are non-specialize,
        // remaining 6 are specialize.
        for node in &index.nodes()[..3] {
            assert!(
                !node.introduced_by_specialize,
                "node {:?} should not be specialize",
                node.path
            );
        }
        for node in &index.nodes()[3..] {
            assert!(
                node.introduced_by_specialize,
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
            .iter()
            .position(|n| n.introduced_by_specialize)
            .expect("should have specialize nodes");
        assert!(first_spec >= 2, "at least Root + Reference before specializes");

        // All nodes after the first specialize must also be specialize.
        for node in &index.nodes()[first_spec..] {
            assert!(
                node.introduced_by_specialize,
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
        let node = |arc: ArcType| Node {
            layer_index: 0,
            path: p("/X"),
            arc,
            map_to_parent: MapFunction::identity(),
            map_to_root: MapFunction::identity(),
            introduced_by_specialize: false,
        };

        let mut index = PrimIndex::default();
        index.push_node(node(ArcType::Root));
        index.push_node(node(ArcType::Variant));

        index.insert_relocate_node(node(ArcType::Relocate));

        let arcs: Vec<ArcType> = index.nodes().iter().map(|n| n.arc).collect();
        assert_eq!(arcs, vec![ArcType::Root, ArcType::Variant, ArcType::Relocate]);
    }
}
