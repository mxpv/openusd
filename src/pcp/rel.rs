//! Relocate-related methods of [`Cache`].
//!
//! This file contains the relocate logic split out from `cache.rs` for
//! readability. It provides an `impl Cache` block with methods that
//! compute effective relocates, find pre-relocation source paths, and
//! merge relocate-arc nodes into prim indices. Two free functions
//! (`collect_layer_relocates` and `apply_relocates`) support the cache
//! constructor and child-name adjustment respectively.

use std::collections::HashMap;

use crate::sdf::schema::FieldKey;
use crate::sdf::{LayerData, Path, Value};

use super::cache::Cache;
use super::index::{ArcType, CompositionContext, Node, PrimIndex};
use super::mapping::MapFunction;

impl Cache {
    /// Returns a snapshot of all cached prim indices for passing to
    /// `PrimIndex::build_with_cache`.
    pub(super) fn index_snapshot(&self) -> HashMap<Path, PrimIndex> {
        self.cache.iter().map(|(k, v)| (k.clone(), v.index.clone())).collect()
    }

    /// Pushes a Relocate-arc node into the index, mapping `source_path` to
    /// `composed_path`.
    fn push_relocate_node(index: &mut PrimIndex, layer_index: usize, source_path: &Path, composed_path: &Path) {
        let m = MapFunction::from_pair(source_path.clone(), composed_path.clone());
        index.push_node(Node {
            layer_index,
            path: source_path.clone(),
            arc: ArcType::Relocate,
            map_to_parent: m.clone(),
            map_to_root: m,
        });
    }

    /// Returns the nodes for a path, from cache if available, otherwise built
    /// on the fly.
    fn get_or_build_nodes(&self, path: &Path) -> Vec<Node> {
        if let Some(entry) = self.cache.get(path) {
            return entry.index.nodes().to_vec();
        }
        let ctx = self.build_source_context(path);
        PrimIndex::build_with_context(path, &self.stack, &ctx)
            .map(|idx| idx.nodes().to_vec())
            .unwrap_or_default()
    }

    /// Computes effective relocates for a parent prim in composed namespace.
    ///
    /// Collects relocates from all layers reachable through any cached prim
    /// in the same root subtree, maps them to composed namespace using the
    /// layer's namespace mapping, then chains transitive relocates.
    fn effective_relocates(&self, path: &Path) -> Vec<(Path, Path)> {
        let mut result = self.raw_effective_relocates(path);

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

    /// Raw (unchained) effective relocates. Each layer's relocates are mapped
    /// through namespace mappings found in cached prims.
    fn raw_effective_relocates(&self, path: &Path) -> Vec<(Path, Path)> {
        let layer_maps = self.collect_layer_maps(path);
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
    fn collect_layer_maps(&self, path: &Path) -> Vec<(usize, MapFunction)> {
        let mut maps: Vec<(usize, MapFunction)> = Vec::new();

        // Walk up ancestors.
        let mut current = Some(path.clone());
        while let Some(p) = current {
            if let Some(entry) = self.cache.get(&p) {
                for node in entry.index.nodes() {
                    if node.arc == ArcType::Relocate {
                        continue;
                    }
                    if !maps
                        .iter()
                        .any(|(li, m)| *li == node.layer_index && *m == node.map_to_root)
                    {
                        maps.push((node.layer_index, node.map_to_root.clone()));
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

        for (cached_path, entry) in &self.cache {
            let cached_root = cached_path.as_str().split('/').nth(1).unwrap_or("");
            if cached_root != root_name {
                continue;
            }
            for node in entry.index.nodes() {
                if node.arc == ArcType::Relocate {
                    continue;
                }
                if relocate_layers.contains(&node.layer_index)
                    && !maps
                        .iter()
                        .any(|(li, m)| *li == node.layer_index && *m == node.map_to_root)
                {
                    maps.push((node.layer_index, node.map_to_root.clone()));
                }
            }
        }

        maps
    }

    /// Finds the pre-relocation source path for a composed path by checking
    /// effective relocates from the parent. Tries raw (unchained) relocates
    /// first for simple cases, then falls back to chained relocates for
    /// multi-level relocate chains. Chains recursively when the source itself
    /// is a relocate target.
    pub(super) fn find_source_path(&self, composed_path: &Path) -> Option<Path> {
        let parent = composed_path.parent()?;

        // Try raw (unchained) relocates first.
        let raw_relocates = self.raw_effective_relocates(&parent);
        let mut result = None;
        for (src, tgt) in &raw_relocates {
            if tgt.is_empty() {
                continue;
            }
            if let Some(sp) = composed_path.replace_prefix(tgt, src) {
                result = Some(sp);
                break;
            }
        }

        // Fall back to chained relocates when raw didn't match. This handles
        // cases where the composed path is in a namespace created by chaining
        // multiple relocates (e.g. A→B in layer1, B→C in layer2).
        if result.is_none() {
            let chained_relocates = self.effective_relocates(&parent);
            for (src, tgt) in &chained_relocates {
                if tgt.is_empty() {
                    continue;
                }
                if let Some(sp) = composed_path.replace_prefix(tgt, src) {
                    result = Some(sp);
                    break;
                }
            }
        }

        // Chain: if the source is itself a relocate target, resolve further.
        // Only chain if the deeper source actually has specs in some layer,
        // to avoid incorrectly reversing relocates for prims authored in
        // the post-relocation namespace.
        if let Some(ref source) = result {
            if let Some(deeper) = self.find_source_path(source) {
                let has_spec = self.stack.layers.iter().any(|l| l.has_spec(&deeper));
                if has_spec {
                    return Some(deeper);
                }
            }
        }
        result
    }

    /// Ensures a path and all its ancestors are cached (built on the fly if needed).
    pub(super) fn precache_path(&mut self, path: &Path) {
        let mut to_build = Vec::new();
        let mut p = Some(path.clone());
        while let Some(pp) = p {
            if pp == Path::abs_root() || self.cache.contains_key(&pp) {
                break;
            }
            to_build.push(pp.clone());
            p = pp.parent();
        }
        for pp in to_build.into_iter().rev() {
            let _ = self.ensure_index(&pp);
        }
    }

    /// Builds the composition context for a source path's parent.
    /// Checks cache first; builds on the fly if not cached. Uses
    /// `build_with_context` (without cache) so that inherit/specialize
    /// targets are built fresh with the correct variant selections rather
    /// than using cached indices that may have different selections.
    fn build_source_context(&self, source_path: &Path) -> CompositionContext {
        let Some(parent) = source_path.parent() else {
            return CompositionContext::default();
        };
        if parent == Path::abs_root() {
            return CompositionContext::default();
        }
        if let Some(entry) = self.cache.get(&parent) {
            return entry.child_context.clone();
        }
        // Build on the fly without the composition cache so inherit targets
        // get the correct variant selections for this specific path rather
        // than reusing cached indices with potentially different selections.
        let grandparent_ctx = self.build_source_context(&parent);
        let Ok(parent_index) = PrimIndex::build_with_context(&parent, &self.stack, &grandparent_ctx) else {
            return CompositionContext::default();
        };
        parent_index.context_for_children(&self.stack, &grandparent_ctx)
    }

    /// Adds relocate nodes to a prim index for a relocated prim.
    ///
    /// Builds a full composition index for the source path and merges its
    /// nodes. The source index captures all opinions (through references,
    /// variants, inherits) including those propagated via
    /// [`propagate_parent_specs`](Self::propagate_parent_specs). For each
    /// inherit/specialize node in the source parent, also checks the class
    /// child path for additional specs.
    pub(super) fn add_relocate_nodes(&self, composed_path: &Path, index: &mut PrimIndex) {
        let Some(source_path) = self.find_source_path(composed_path) else {
            return;
        };
        let source_ctx = self.build_source_context(&source_path);
        let source_cache: HashMap<Path, PrimIndex> = self.index_snapshot();
        let Ok(source_index) = PrimIndex::build_with_cache(&source_path, &self.stack, &source_ctx, &source_cache)
        else {
            return;
        };

        // Merge source nodes.
        for node in source_index.nodes() {
            Self::push_relocate_node(index, node.layer_index, &node.path, composed_path);
        }

        // Check the source parent's composition arcs for additional child
        // specs. This mirrors Cache::propagate_parent_specs (which is not
        // called by PrimIndex::build_with_cache) and also handles cases where
        // the source_index has cached nodes with wrong variant selections.
        if let Some(source_parent) = source_path.parent() {
            if let Some(source_name) = source_path.name() {
                let index_cache: HashMap<Path, PrimIndex> = self.index_snapshot();
                let parent_nodes: Vec<Node> = if let Some(entry) = self.cache.get(&source_parent) {
                    entry.index.nodes().to_vec()
                } else {
                    let ctx = self.build_source_context(&source_parent);
                    PrimIndex::build_with_cache(&source_parent, &self.stack, &ctx, &index_cache)
                        .map(|idx| idx.nodes().to_vec())
                        .unwrap_or_default()
                };

                for pn in &parent_nodes {
                    if pn.arc == ArcType::Root {
                        continue;
                    }
                    let Ok(child_path) = pn.path.append_path(source_name) else {
                        continue;
                    };
                    for li in 0..self.stack.len() {
                        if self.stack.layer(li).has_spec(&child_path) {
                            Self::push_relocate_node(index, li, &child_path, composed_path);
                        }
                    }
                }
            }
        }

        // Also add implied nodes from the source parent's inherit/specialize
        // chain. The source index may miss opinions from class prims whose
        // overrides live in layers not reachable through the source's own
        // LIVRPS (e.g. local overrides on a class in the root layer).
        if let Some(source_parent) = source_path.parent() {
            if let Some(source_name) = source_path.name() {
                let parent_nodes: Vec<Node> = if let Some(entry) = self.cache.get(&source_parent) {
                    entry.index.nodes().to_vec()
                } else {
                    let ctx = self.build_source_context(&source_parent);
                    PrimIndex::build_with_context(&source_parent, &self.stack, &ctx)
                        .map(|idx| idx.nodes().to_vec())
                        .unwrap_or_default()
                };

                for pn in &parent_nodes {
                    if pn.arc != ArcType::Inherit && pn.arc != ArcType::Specialize {
                        continue;
                    }
                    let Ok(class_child) = pn.path.append_path(source_name) else {
                        continue;
                    };
                    let class_ctx = self.build_source_context(&class_child);
                    let class_cache: HashMap<Path, PrimIndex> = self.index_snapshot();
                    let Ok(class_index) =
                        PrimIndex::build_with_cache(&class_child, &self.stack, &class_ctx, &class_cache)
                    else {
                        continue;
                    };
                    for node in class_index.nodes() {
                        Self::push_relocate_node(index, node.layer_index, &node.path, composed_path);
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
        if let Some(first_node) = index.nodes().first() {
            let first_li = first_node.layer_index;
            let first_path = first_node.path.clone();
            let mut existing: Vec<(usize, Path)> =
                index.nodes().iter().map(|n| (n.layer_index, n.path.clone())).collect();
            // Find ALL cached prims whose index contains a node at the same
            // (layer, path) as the first relocate node, and merge any
            // additional opinions from all of them.
            for entry in self.cache.values() {
                let matched = entry
                    .index
                    .nodes()
                    .iter()
                    .any(|cn| cn.layer_index == first_li && cn.path == first_path);
                if !matched {
                    continue;
                }
                for extra in entry.index.nodes() {
                    if !existing
                        .iter()
                        .any(|(li, p)| *li == extra.layer_index && *p == extra.path)
                    {
                        existing.push((extra.layer_index, extra.path.clone()));
                        Self::push_relocate_node(index, extra.layer_index, &extra.path, composed_path);
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
                let Some(deeper) = self.find_source_path(&current) else {
                    break;
                };
                if visited.contains(&deeper) {
                    break;
                }
                visited.push(deeper.clone());
                self.add_relocate_nodes_at(&deeper, composed_path, index);
                current = deeper;
            }
        }
    }

    /// Builds a source index at the given source path and merges relocate
    /// nodes into the composed path's index. Shared implementation for
    /// retry-with-deeper-source in [`add_relocate_nodes`].
    fn add_relocate_nodes_at(&self, source_path: &Path, composed_path: &Path, index: &mut PrimIndex) {
        let source_ctx = self.build_source_context(source_path);
        let source_cache: HashMap<Path, PrimIndex> = self.index_snapshot();
        let Ok(source_index) = PrimIndex::build_with_cache(source_path, &self.stack, &source_ctx, &source_cache) else {
            return;
        };
        for node in source_index.nodes() {
            Self::push_relocate_node(index, node.layer_index, &node.path, composed_path);
        }
        // Also check parent nodes for child specs.
        if source_index.is_empty() {
            if let Some(sp) = source_path.parent() {
                if let Some(sn) = source_path.name() {
                    let parent_nodes = self.get_or_build_nodes(&sp);
                    for pn in &parent_nodes {
                        if pn.arc == ArcType::Root {
                            continue;
                        }
                        let Ok(child_path) = pn.path.append_path(sn) else {
                            continue;
                        };
                        for li in 0..self.stack.len() {
                            if self.stack.layer(li).has_spec(&child_path) {
                                Self::push_relocate_node(index, li, &child_path, composed_path);
                            }
                        }
                    }
                }
            }
        }
    }

    /// Applies relocate namespace remapping to a list of child names.
    ///
    /// Per-node layer relocates are applied first: each node's layer may have
    /// relocates that create children under the node's path. This handles
    /// children that exist only through relocates within a referenced layer
    /// (e.g. Knot03 under Tentacle in TentacleRig). Then effective relocates
    /// are applied to remap source children to targets and add cross-hierarchy
    /// targets.
    pub(super) fn apply_relocates_to_children(&mut self, path: &Path, children: &mut Vec<String>) {
        // Apply per-node layer relocates: each node's layer may have
        // relocates that create children under the node's path. This
        // handles children that exist only through relocates within a
        // referenced layer (e.g. Knot03 under Tentacle in TentacleRig).
        if let Some(entry) = self.cache.get(path) {
            let nodes: Vec<Node> = entry.index.nodes().to_vec();
            for node in &nodes {
                if let Some(relocates) = self.layer_relocates.get(&node.layer_index) {
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

        let relocates = self.effective_relocates(path);
        if !relocates.is_empty() {
            // Pre-cache source ancestor chains so their prim indices are
            // available when building relocated target indices later.
            for (src, _) in &relocates {
                self.precache_path(src);
            }
            apply_relocates(path, children, &relocates);
        }
    }
}

/// Extracts `layerRelocates` from every layer's pseudoroot.
pub(super) fn collect_layer_relocates(layers: &[LayerData]) -> HashMap<usize, Vec<(Path, Path)>> {
    let root = Path::abs_root();
    let mut result = HashMap::new();
    for (i, layer) in layers.iter().enumerate() {
        if let Ok(val) = layer.get(&root, FieldKey::LayerRelocates.as_str()) {
            if let Value::Relocates(pairs) = val.into_owned() {
                if !pairs.is_empty() {
                    result.insert(i, pairs);
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
fn apply_relocates(parent: &Path, children: &mut Vec<String>, relocates: &[(Path, Path)]) {
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
