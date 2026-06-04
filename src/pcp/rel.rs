//! Relocates: non-destructive namespace remapping.
//!
//! The [`Relocates`] struct encapsulates all relocate logic — extracting
//! `layerRelocates` from layer metadata, computing effective relocates in
//! composed namespace, finding pre-relocation source paths, and merging
//! relocate-arc nodes into prim indices. It is an isolated object that
//! does not reference [`Cache`](super::cache::Cache) directly; all
//! external data (layer stack, cached indices, cached contexts) is passed
//! in through method parameters.

use std::collections::HashMap;

use crate::sdf::schema::FieldKey;
use crate::sdf::{self, AbstractData, Path, Value};

use super::graph::ArcType;
use super::index::PrimIndex;
use super::mapping::MapFunction;

/// Per-layer relocates and operations for namespace remapping.
///
/// Owns the `layerRelocates` data extracted at construction time. All
/// query and mutation methods receive the composition cache's state
/// (layer stack, indices, contexts) as explicit parameters.
pub(super) struct Relocates {
    /// Per-layer relocates: `layerRelocates` extracted from each layer's pseudoroot.
    layer_relocates: HashMap<usize, Vec<(Path, Path)>>,
}

/// Extracts each layer's authored `layerRelocates` pairs `(source, target)`,
/// keyed by layer index; layers without relocates are omitted. Shared by
/// [`Relocates::new`] and [`LayerStack`](super::LayerStack).
pub(crate) fn extract_layer_relocates(layers: &[sdf::Layer]) -> HashMap<usize, Vec<(Path, Path)>> {
    let root = Path::abs_root();
    let mut out = HashMap::new();
    for (i, layer) in layers.iter().enumerate() {
        if let Ok(val) = layer.get(&root, FieldKey::LayerRelocates.as_str()) {
            if let Value::Relocates(pairs) = val.into_owned() {
                if !pairs.is_empty() {
                    out.insert(i, pairs);
                }
            }
        }
    }
    out
}

impl Relocates {
    /// Creates a new `Relocates` by extracting `layerRelocates` from every
    /// layer's pseudoroot.
    pub fn new(layers: &[sdf::Layer]) -> Self {
        Self {
            layer_relocates: extract_layer_relocates(layers),
        }
    }

    /// Returns `true` if no layer has any relocates.
    pub fn is_empty(&self) -> bool {
        self.layer_relocates.is_empty()
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

        // Sorted iteration: a `HashMap` walk would make the collected layer-map
        // order (and so downstream relocate composition) hash-order-dependent.
        let mut cached_paths: Vec<&Path> = indices.keys().collect();
        cached_paths.sort();
        for cached_path in cached_paths {
            let cached_index = &indices[cached_path];
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
}
