//! Relocates: non-destructive namespace remapping.
//!
//! The [`Relocates`] struct encapsulates all relocate logic — extracting
//! `layerRelocates` from layer metadata, computing effective relocates in
//! composed namespace, finding pre-relocation source paths, and merging
//! relocate-arc nodes into prim indices. It is an isolated object that
//! does not reference [`Cache`](super::cache::Cache) directly; all
//! external data (layer stack, cached indices, cached contexts) is passed
//! in through method parameters.

use std::collections::{HashMap, HashSet};

use crate::sdf::schema::FieldKey;
use crate::sdf::{self, AbstractData, LayerOffset, Path, Value};

use super::index::{ArcType, CompositionContext, Node, NodeId, PrimIndex};
use super::mapping::MapFunction;
use super::{Error, LayerStack};

/// Per-layer relocates and operations for namespace remapping.
///
/// Owns the `layerRelocates` data extracted at construction time. All
/// query and mutation methods receive the composition cache's state
/// (layer stack, indices, contexts) as explicit parameters.
pub(super) struct Relocates {
    /// Per-layer relocates: `layerRelocates` extracted from each layer's pseudoroot.
    layer_relocates: HashMap<usize, Vec<(Path, Path)>>,
}

/// Hard limit on relocate chaining depth to avoid stack overflow on malformed inputs.
const MAX_RELOCATE_CHAIN: usize = 128;

impl Relocates {
    /// Creates a new `Relocates` by extracting `layerRelocates` from every
    /// layer's pseudoroot.
    pub fn new(layers: &[sdf::Layer]) -> Self {
        let root = Path::abs_root();
        let mut layer_relocates = HashMap::new();
        for (i, layer) in layers.iter().enumerate() {
            if let Ok(val) = layer.get(&root, FieldKey::LayerRelocates.as_str()) {
                if let Value::Relocates(pairs) = val.into_owned() {
                    if !pairs.is_empty() {
                        layer_relocates.insert(i, pairs);
                    }
                }
            }
        }
        Self { layer_relocates }
    }

    /// Returns `true` if no layer has any relocates.
    pub fn is_empty(&self) -> bool {
        self.layer_relocates.is_empty()
    }

    // ------------------------------------------------------------------
    // Source path resolution
    // ------------------------------------------------------------------

    /// Finds the pre-relocation source path for a composed path by checking
    /// effective relocates from the parent. Tries raw (unchained) relocates
    /// first for simple cases, then falls back to chained relocates for
    /// multi-level relocate chains. Chains recursively when the source itself
    /// is a relocate target.
    pub fn find_source_path(
        &self,
        composed_path: &Path,
        stack: &LayerStack,
        indices: &HashMap<Path, PrimIndex>,
    ) -> Result<Option<Path>, Error> {
        let mut visited = HashSet::new();
        self.find_source_path_inner(composed_path, stack, indices, &mut visited, 0)
    }

    fn find_source_path_inner(
        &self,
        composed_path: &Path,
        stack: &LayerStack,
        indices: &HashMap<Path, PrimIndex>,
        visited: &mut HashSet<Path>,
        depth: usize,
    ) -> Result<Option<Path>, Error> {
        if depth >= MAX_RELOCATE_CHAIN {
            return Err(Error::ArcCycle {
                path: composed_path.clone(),
                depth,
            });
        }
        if !visited.insert(composed_path.clone()) {
            return Err(Error::ArcCycle {
                path: composed_path.clone(),
                depth,
            });
        }

        let Some(parent) = composed_path.parent() else {
            visited.remove(composed_path);
            return Ok(None);
        };

        // Try raw (unchained) relocates first, then fall back to chained
        // relocates only when raw didn't match. Chaining handles a composed
        // path in a namespace created by multiple relocates (e.g. A→B in
        // layer1, B→C in layer2).
        let result = Self::first_source(&self.raw_effective_relocates(&parent, indices), composed_path)
            .or_else(|| Self::first_source(&self.effective_relocates(&parent, indices), composed_path));

        // Chain: if the source is itself a relocate target, resolve further.
        // Only chain if the deeper source actually has specs in some layer,
        // to avoid incorrectly reversing relocates for prims authored in
        // the post-relocation namespace.
        if let Some(ref source) = result {
            if let Some(deeper) = self.find_source_path_inner(source, stack, indices, visited, depth + 1)? {
                let has_spec = stack.layers.iter().any(|l| l.has_spec(&deeper));
                if has_spec {
                    visited.remove(composed_path);
                    return Ok(Some(deeper));
                }
            }
        }
        visited.remove(composed_path);
        Ok(result)
    }

    /// Returns the first relocate whose target prefixes `composed`, remapped
    /// back onto the relocate source. Relocates with an empty target are
    /// skipped (a deletion, not a rename).
    fn first_source(relocates: &[(Path, Path)], composed: &Path) -> Option<Path> {
        relocates.iter().find_map(|(src, tgt)| {
            if tgt.is_empty() {
                None
            } else {
                composed.replace_prefix(tgt, src)
            }
        })
    }

    // ------------------------------------------------------------------
    // Relocate node merging
    // ------------------------------------------------------------------

    /// Adds relocate nodes to a prim index for a relocated prim.
    ///
    /// Builds a full composition index for the source path and merges its
    /// nodes. The recursive build captures all of the source's opinions
    /// (through references, variants, inherits). For each inherit/specialize
    /// node in the source parent, this also checks the class child path for
    /// additional specs.
    pub fn add_relocate_nodes(
        &self,
        composed_path: &Path,
        index: &mut PrimIndex,
        stack: &LayerStack,
        indices: &HashMap<Path, PrimIndex>,
        contexts: &HashMap<Path, CompositionContext>,
    ) -> Result<(), Error> {
        let Some(source_path) = self.find_source_path(composed_path, stack, indices)? else {
            return Ok(());
        };
        let source_ctx = Self::build_source_context(&source_path, stack, contexts);
        let Ok(source_index) = PrimIndex::build_with_cache(&source_path, stack, &source_ctx, indices) else {
            return Ok(());
        };

        // Merge source nodes, grafting the source subtree so relocate nodes
        // keep the source's internal parent/child structure instead of
        // flattening to a list. A source root maps straight to the composed
        // path; internal nodes keep their own map-to-parent and compose down.
        let mut remap: Vec<Option<NodeId>> = vec![None; source_index.arena().len()];
        for (sid, node) in source_index.nodes_with_ids() {
            let grafted_parent = node.parent().and_then(|sp| remap[sp.idx()]);
            let map_to_parent = match grafted_parent {
                Some(_) => node.map_to_parent.clone(),
                None => MapFunction::from_pair_identity(node.path.clone(), composed_path.clone()),
            };
            let new_id = index.graft_relocate_node(
                grafted_parent,
                node.layer_stack().to_vec(),
                node.path.clone(),
                map_to_parent,
            );
            remap[sid.idx()] = Some(new_id);
        }

        // Check the source parent's composition arcs for additional child
        // specs and implied inherit/specialize opinions. This descends the
        // source parent's class arcs directly, covering cases where the
        // source_index has cached nodes with wrong variant selections or
        // overrides from class prims in unreachable layers.
        if let Some(source_parent) = source_path.parent() {
            if let Some(source_name) = source_path.name() {
                let parent_nodes: Vec<Node> = if let Some(parent_index) = indices.get(&source_parent) {
                    parent_index.nodes().cloned().collect()
                } else {
                    let ctx = Self::build_source_context(&source_parent, stack, contexts);
                    PrimIndex::build_with_cache(&source_parent, stack, &ctx, indices)
                        .map(|idx| idx.nodes().cloned().collect())
                        .unwrap_or_default()
                };

                for pn in &parent_nodes {
                    if pn.arc == ArcType::Root {
                        continue;
                    }
                    let Ok(child_path) = pn.path.append_path(source_name) else {
                        continue;
                    };

                    // Non-Root arcs: check all layers for child specs, folding
                    // every authoring sublayer into one per-site relocate node.
                    let members = Self::site_layer_stack(&child_path, stack);
                    if !members.is_empty() {
                        Self::push_relocate_node(index, members, &child_path, composed_path);
                    }

                    // Inherit/Specialize arcs: also build the class child's
                    // full index to capture opinions from deeper composition.
                    if pn.arc == ArcType::Inherit || pn.arc == ArcType::Specialize {
                        let class_ctx = Self::build_source_context(&child_path, stack, contexts);
                        let Ok(class_index) = PrimIndex::build_with_cache(&child_path, stack, &class_ctx, indices)
                        else {
                            continue;
                        };
                        for node in class_index.nodes() {
                            Self::push_relocate_node(index, node.layer_stack().to_vec(), &node.path, composed_path);
                        }
                    }
                }
            }
        }

        // Merge additional opinions from cached prims at the relocate node
        // paths. Source nodes may come from a referenced layer (e.g. LegsRig.usd)
        // but the root layer may have overrides at the composed-namespace path
        // (e.g. root.usd at /CharRig/Rig/LegsRig/SymLegRig/.../Seg2). Those
        // overrides are in the cached prim for that composed path but not in
        // the source index built from the relocate chain.
        let first = index.nodes().next().map(|n| (n.layer_index(), n.path.clone()));
        if let Some((first_li, first_path)) = first {
            // Track every contributing (layer, path), not just each node's
            // representative layer: a per-site node spans several sublayers, so
            // deduping on the strongest member alone would let an overlapping
            // node re-add a shared layer and double-apply its list-op edits.
            let mut existing: HashSet<(usize, Path)> = index
                .nodes()
                .flat_map(|n| n.layers().map(move |(layer, _)| (layer, n.path.clone())))
                .collect();
            // Find ALL cached prims whose index contains a node at the same
            // (layer, path) as the first relocate node, and merge any
            // additional opinions from all of them.
            for cached_index in indices.values() {
                let matched = cached_index
                    .nodes()
                    .any(|cn| cn.layer_index() == first_li && cn.path == first_path);
                if !matched {
                    continue;
                }
                for extra in cached_index.nodes() {
                    // Keep only the members not already contributing at this
                    // path; an empty remainder means the node is fully covered.
                    let members: Vec<(usize, LayerOffset)> = extra
                        .layer_stack()
                        .iter()
                        .copied()
                        .filter(|&(layer, _)| existing.insert((layer, extra.path.clone())))
                        .collect();
                    if !members.is_empty() {
                        Self::push_relocate_node(index, members, &extra.path, composed_path);
                    }
                }
            }
        }

        // If the index is still empty, the source path itself may be at an
        // intermediate relocate level. Iteratively resolve deeper sources
        // through the relocate chain until we find one with actual specs.
        // This handles multi-level relocate chains where find_source_path's
        // has_spec guard stopped too early (specs exist through class
        // inheritance, not direct layer authoring).
        if index.is_empty() {
            let mut current = source_path;
            let mut visited = vec![composed_path.clone(), current.clone()];
            while index.is_empty() {
                let Some(deeper) = self.find_source_path(&current, stack, indices)? else {
                    break;
                };
                if visited.contains(&deeper) {
                    break;
                }
                visited.push(deeper.clone());
                self.add_relocate_nodes_at(&deeper, composed_path, index, stack, indices, contexts);
                current = deeper;
            }
        }

        Ok(())
    }

    /// Builds a source index at the given source path and merges relocate
    /// nodes into the composed path's index. Shared implementation for
    /// retry-with-deeper-source in [`add_relocate_nodes`].
    fn add_relocate_nodes_at(
        &self,
        source_path: &Path,
        composed_path: &Path,
        index: &mut PrimIndex,
        stack: &LayerStack,
        indices: &HashMap<Path, PrimIndex>,
        contexts: &HashMap<Path, CompositionContext>,
    ) {
        let source_ctx = Self::build_source_context(source_path, stack, contexts);
        let Ok(source_index) = PrimIndex::build_with_cache(source_path, stack, &source_ctx, indices) else {
            return;
        };
        for node in source_index.nodes() {
            Self::push_relocate_node(index, node.layer_stack().to_vec(), &node.path, composed_path);
        }
        if source_index.is_empty() {
            if let Some(sp) = source_path.parent() {
                if let Some(sn) = source_path.name() {
                    let parent_nodes = Self::get_or_build_nodes(&sp, stack, indices, contexts);
                    for pn in &parent_nodes {
                        if pn.arc == ArcType::Root {
                            continue;
                        }
                        let Ok(child_path) = pn.path.append_path(sn) else {
                            continue;
                        };
                        let members = Self::site_layer_stack(&child_path, stack);
                        if !members.is_empty() {
                            Self::push_relocate_node(index, members, &child_path, composed_path);
                        }
                    }
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // Child name adjustment
    // ------------------------------------------------------------------

    /// Applies per-node layer relocates to a list of child names.
    ///
    /// Each node's layer may have relocates that create children under the
    /// node's path. This handles children that exist only through relocates
    /// within a referenced layer (e.g. Knot03 under Tentacle in TentacleRig).
    pub fn apply_node_relocates(&self, path: &Path, children: &mut Vec<String>, indices: &HashMap<Path, PrimIndex>) {
        let Some(cached_index) = indices.get(path) else {
            return;
        };
        for node in cached_index.nodes() {
            // Check every contributing sublayer of the per-site node, not just
            // the strongest representative: a weaker sublayer may author the
            // `layerRelocates` that creates or hides a child here.
            for (layer, _) in node.layers() {
                let Some(relocates) = self.layer_relocates.get(&layer) else {
                    continue;
                };
                for (src, tgt) in relocates {
                    // Target child: add if target's parent matches this node's path.
                    if !tgt.is_empty() {
                        if let Some(tgt_name) = tgt.name() {
                            if tgt.parent().as_ref() == Some(&node.path) {
                                let name = tgt_name.to_string();
                                if !children.contains(&name) {
                                    children.push(name);
                                }
                            }
                        }
                    }
                    // Source child: remove if source's parent matches this node's path.
                    if let Some(src_name) = src.name() {
                        if src.parent().as_ref() == Some(&node.path) {
                            children.retain(|n| n != src_name);
                        }
                    }
                }
            }
        }
    }

    /// Computes effective relocates for a parent prim in composed namespace.
    ///
    /// Collects relocates from all layers reachable through any cached prim
    /// in the same root subtree, maps them to composed namespace using the
    /// layer's namespace mapping, then chains transitive relocates.
    pub fn effective_relocates(&self, path: &Path, indices: &HashMap<Path, PrimIndex>) -> Vec<(Path, Path)> {
        let mut result = self.raw_effective_relocates(path, indices);

        // Chain: if a target falls under another source, compose to final target.
        let snapshot = result.clone();
        for entry in &mut result {
            if entry.1.is_empty() {
                continue;
            }
            for (other_src, other_tgt) in &snapshot {
                if other_tgt.is_empty() {
                    continue;
                }
                if let Some(remapped) = entry.1.replace_prefix(other_src, other_tgt) {
                    if remapped != entry.1 {
                        entry.1 = remapped;
                        break;
                    }
                }
            }
        }

        result
    }

    /// Applies relocate namespace remapping to a list of child names.
    ///
    /// - Source children are removed (or remapped if the target is a child of
    ///   the same parent).
    /// - Target children whose parent matches but source comes from a different
    ///   parent are added (cross-hierarchy relocation).
    pub fn apply_children_remapping(parent: &Path, children: &mut Vec<String>, relocates: &[(Path, Path)]) {
        let mut to_remove = Vec::new();
        let mut to_add: Vec<String> = Vec::new();

        for (i, name) in children.iter().enumerate() {
            let Ok(child_path) = parent.append_path(name.as_str()) else {
                continue;
            };
            if let Some(target) = relocates.iter().find(|(s, _)| *s == child_path).map(|(_, t)| t) {
                to_remove.push(i);
                if !target.is_empty() {
                    if let Some(tname) = target.name() {
                        let tname = tname.to_string();
                        if target.parent().as_ref() == Some(parent) && !children.contains(&tname) {
                            to_add.push(tname);
                        }
                    }
                }
            }
        }

        for &i in to_remove.iter().rev() {
            children.remove(i);
        }
        for name in to_add {
            if !children.contains(&name) {
                children.push(name);
            }
        }

        // Cross-hierarchy: add targets whose parent is this prim but source is
        // from a different parent.
        for (source, target) in relocates {
            if target.is_empty() {
                continue;
            }
            if target.parent().as_ref() == Some(parent) {
                if let Some(tname) = target.name() {
                    let name = tname.to_string();
                    if !children.contains(&name) && source.parent().as_ref() != Some(parent) {
                        children.push(name);
                    }
                }
            }
        }
    }

    // ------------------------------------------------------------------
    // Private helpers
    // ------------------------------------------------------------------

    /// Raw (unchained) effective relocates. Each layer's relocates are mapped
    /// through namespace mappings found in cached prims.
    fn raw_effective_relocates(&self, path: &Path, indices: &HashMap<Path, PrimIndex>) -> Vec<(Path, Path)> {
        let layer_maps = self.collect_layer_maps(path, indices);
        let mut result: Vec<(Path, Path)> = Vec::new();

        for (li, map) in &layer_maps {
            let Some(relocates) = self.layer_relocates.get(li) else {
                continue;
            };
            for (src, tgt) in relocates {
                let Some(composed_src) = map.map_source_to_target(src) else {
                    continue;
                };
                let composed_tgt = if tgt.is_empty() {
                    tgt.clone()
                } else {
                    let Some(t) = map.map_source_to_target(tgt) else {
                        continue;
                    };
                    t
                };
                if !result.iter().any(|(s, t)| *s == composed_src && *t == composed_tgt) {
                    result.push((composed_src, composed_tgt));
                }
            }
        }

        // Sort by target length descending for longest-prefix-first matching.
        result.sort_by(|a, b| b.1.as_str().len().cmp(&a.1.as_str().len()));
        result
    }

    /// Collects (layer_index, map_to_root) pairs from ancestor prims and from
    /// other cached prims in the same root subtree that have layers with
    /// relocates.
    fn collect_layer_maps(&self, path: &Path, indices: &HashMap<Path, PrimIndex>) -> Vec<(usize, MapFunction)> {
        let mut maps: Vec<(usize, MapFunction)> = Vec::new();

        // Walk up ancestors. A per-site node fans out into every contributing
        // sublayer so a weaker sublayer that authors `layerRelocates` is mapped
        // through this node's namespace mapping, not just the representative.
        let mut current = Some(path.clone());
        while let Some(p) = current {
            if let Some(cached_index) = indices.get(&p) {
                for node in cached_index.nodes() {
                    if node.arc == ArcType::Relocate {
                        continue;
                    }
                    for (layer, _) in node.layers() {
                        if !maps.iter().any(|(li, m)| *li == layer && *m == node.map_to_root) {
                            maps.push((layer, node.map_to_root.clone()));
                        }
                    }
                }
            }
            current = p.parent().filter(|pp| *pp != Path::abs_root());
        }

        // Also search cached prims in the same root subtree for layers with
        // relocates that weren't found in the ancestor walk (e.g. referenced
        // layers only reachable from a sibling branch).
        let relocate_layers: Vec<usize> = self.layer_relocates.keys().copied().collect();
        let root_name = path.as_str().split('/').nth(1).unwrap_or("");

        for (cached_path, cached_index) in indices {
            let cached_root = cached_path.as_str().split('/').nth(1).unwrap_or("");
            if cached_root != root_name {
                continue;
            }
            for node in cached_index.nodes() {
                if node.arc == ArcType::Relocate {
                    continue;
                }
                for (layer, _) in node.layers() {
                    if relocate_layers.contains(&layer)
                        && !maps.iter().any(|(li, m)| *li == layer && *m == node.map_to_root)
                    {
                        maps.push((layer, node.map_to_root.clone()));
                    }
                }
            }
        }

        maps
    }

    /// Builds the composition context for a source path's parent.
    /// Checks cached contexts first; builds on the fly if not cached.
    fn build_source_context(
        source_path: &Path,
        stack: &LayerStack,
        contexts: &HashMap<Path, CompositionContext>,
    ) -> CompositionContext {
        let Some(parent) = source_path.parent() else {
            return CompositionContext::default();
        };
        if parent == Path::abs_root() {
            return CompositionContext::default();
        }
        if let Some(ctx) = contexts.get(&parent) {
            return ctx.clone();
        }
        // Build on the fly without the composition cache so inherit targets
        // get the correct variant selections for this specific path rather
        // than reusing cached indices with potentially different selections.
        let grandparent_ctx = Self::build_source_context(&parent, stack, contexts);
        let Ok(parent_index) = PrimIndex::build_with_context(&parent, stack, &grandparent_ctx) else {
            return CompositionContext::default();
        };
        parent_index.context_for_children(stack, &grandparent_ctx)
    }

    /// Returns the nodes for a path, from cache if available, otherwise built
    /// on the fly.
    fn get_or_build_nodes(
        path: &Path,
        stack: &LayerStack,
        indices: &HashMap<Path, PrimIndex>,
        contexts: &HashMap<Path, CompositionContext>,
    ) -> Vec<Node> {
        if let Some(index) = indices.get(path) {
            return index.nodes().cloned().collect();
        }
        let ctx = Self::build_source_context(path, stack, contexts);
        PrimIndex::build_with_context(path, stack, &ctx)
            .map(|idx| idx.nodes().cloned().collect())
            .unwrap_or_default()
    }

    /// Pushes a Relocate-arc node into the index, mapping `source_path` to
    /// `composed_path`. `layer_stack` lists every `(layer index, sublayer
    /// offset)` member contributing at the source site, strongest first, so a
    /// relocate source spanning several sublayers keeps all of them.
    fn push_relocate_node(
        index: &mut PrimIndex,
        layer_stack: Vec<(usize, LayerOffset)>,
        source_path: &Path,
        composed_path: &Path,
    ) {
        let m = MapFunction::from_pair_identity(source_path.clone(), composed_path.clone());
        index.insert_relocate_node(Node::new_site(
            layer_stack,
            source_path.clone(),
            ArcType::Relocate,
            m.clone(),
            m,
            false,
        ));
    }

    /// Collects the layers that author a spec at `path` as a per-site layer
    /// stack (strongest first, identity sublayer offsets). Only the root layer
    /// stack is scanned — relocates compose there — so a same-path spec in an
    /// unrelated referenced layer stack is not pulled in. Each member's sublayer
    /// offset is already folded into the node's map-to-root, hence identity.
    fn site_layer_stack(path: &Path, stack: &LayerStack) -> Vec<(usize, LayerOffset)> {
        stack
            .root_layer_stack()
            .into_iter()
            .filter(|&(li, _)| stack.layer(li).has_spec(path))
            .map(|(li, _)| (li, LayerOffset::IDENTITY))
            .collect()
    }
}
