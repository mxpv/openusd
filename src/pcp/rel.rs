//! Relocates: non-destructive namespace remapping.
//!
//! The [`Relocates`] struct encapsulates all relocate logic — extracting
//! `layerRelocates` from layer metadata, computing effective relocates in
//! composed namespace, finding pre-relocation source paths, and merging
//! relocate-arc nodes into prim indices. It is an isolated object that
//! does not reference [`Cache`](super::cache::Cache) directly; all
//! external data (layer stack, cached indices, cached contexts) is passed
//! in through method parameters.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::sdf::schema::FieldKey;
use crate::sdf::{self, AbstractData, Path, PathComponent, Value};

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

/// Follows `path` to its final location through a set of relocates, applying the
/// longest matching source prefix at each step until it reaches a fixed point.
///
/// This is the chaining a relocate undergoes when an ancestor (or the relocated
/// prim itself) is in turn relocated — e.g. `/A` maps onward to `/C` given both
/// `/A -> /B` and `/B -> /C`, and `…/SubRig/Anim` becomes `…/SubRig2/Anim` once
/// `/…/SubRig -> /…/SubRig2`. The pair whose source equals `skip_source` is
/// ignored so a relocate's own endpoints chain only through *other* renames, not
/// themselves. Choosing the longest source prefix at each step makes the result
/// independent of the relocate list's order; the step count is bounded by the
/// number of relocates, so a cyclic (invalid) set cannot loop forever.
pub(crate) fn chain_through_relocates(path: &Path, relocates: &[(Path, Path)], skip_source: Option<&Path>) -> Path {
    let mut current = path.clone();
    for _ in 0..relocates.len() {
        let next = relocates
            .iter()
            .filter(|(s, t)| !t.is_empty() && Some(s) != skip_source)
            .filter_map(|(s, t)| current.replace_prefix(s, t).map(|p| (s.as_str().len(), p)))
            .filter(|(_, p)| *p != current)
            .max_by_key(|(len, _)| *len);
        match next {
            Some((_, p)) => current = p,
            None => break,
        }
    }
    current
}

/// The name of a path's topmost prim (its root prim), or `None` for the
/// absolute root. Groups cached prims by the root subtree they live under.
fn root_prim_name(path: &Path) -> Option<&str> {
    match path.components().next() {
        Some(PathComponent::Prim(name)) => Some(name),
        _ => None,
    }
}

/// Shifts an endpoint through the single nearest ancestor rename in `renames`.
///
/// When an ancestor prim is relocated, a relocate authored below it sits under
/// the renamed parent in composed namespace (e.g. `…/Rig/SubRig/Anim` becomes
/// `…/Rig2/SubRig/Anim` once `Rig -> Rig2`). Only the nearest applicable
/// ancestor — the longest matching source prefix other than `endpoint` itself —
/// is applied, and it is applied once against the original `endpoint`: faithful
/// to C++ USD relocates, a relocate's authored source keeps its as-authored
/// depth and is never transitively re-chained (`_ConformLegacyRelocates` is a
/// no-op in USD mode). Returns `endpoint` unchanged when no ancestor matches.
fn shift_through_nearest_ancestor(endpoint: &Path, renames: &[(Path, Path)]) -> Path {
    renames
        .iter()
        .filter(|(src, tgt)| !tgt.is_empty() && src != endpoint)
        .filter_map(|(src, tgt)| endpoint.replace_prefix(src, tgt).map(|p| (src.as_str().len(), p)))
        .max_by_key(|(len, _)| *len)
        .map(|(_, p)| p)
        .unwrap_or_else(|| endpoint.clone())
}

/// Applies one node's layer-stack relocates to a running child-name order, in
/// place (C++ `_ComposePrimChildNamesAtNode`'s relocate classification). The
/// `pairs` are the node layer stack's as-authored relocates; `parent` is the
/// node's path. Renames keep the source name's position, removes drop it, and
/// cross-hierarchy targets are appended in lexicographic order. Every relocation
/// source under `parent` is recorded in `prohibited`.
pub(crate) fn apply_child_relocates(
    parent: &Path,
    pairs: &[(Path, Path)],
    name_order: &mut Vec<String>,
    name_set: &mut HashSet<String>,
    prohibited: &mut HashSet<String>,
) {
    let mut renames: HashMap<String, String> = HashMap::new();
    let mut removes: HashSet<String> = HashSet::new();
    let mut adds: BTreeSet<String> = BTreeSet::new();

    for (src, tgt) in pairs {
        let src_is_child = src.parent().as_ref() == Some(parent);
        let tgt_is_child = !tgt.is_empty() && tgt.parent().as_ref() == Some(parent);
        if src_is_child {
            if let Some(name) = src.name() {
                prohibited.insert(name.to_string());
                match (tgt_is_child, tgt.name()) {
                    // Target shares the parent: a rename keeps the old position.
                    (true, Some(tgt_name)) => {
                        renames.insert(name.to_string(), tgt_name.to_string());
                    }
                    // Target moves elsewhere (or is a deletion): a removal.
                    _ => {
                        removes.insert(name.to_string());
                    }
                }
            }
        }
        // A child relocated in from a different parent is an addition.
        if tgt_is_child && !src_is_child {
            if let Some(tgt_name) = tgt.name() {
                adds.insert(tgt_name.to_string());
            }
        }
    }

    if !renames.is_empty() || !removes.is_empty() {
        let mut retained: Vec<String> = Vec::with_capacity(name_order.len());
        for name in name_order.drain(..) {
            if let Some(new_name) = renames.get(&name) {
                name_set.remove(&name);
                // A weaker node may already contribute the new name (a "shadow"
                // child across a reference); the relocation silently drops it
                // (C++ `_ComposePrimChildNamesAtNode`).
                if name_set.insert(new_name.clone()) {
                    retained.push(new_name.clone());
                }
            } else if removes.contains(&name) {
                name_set.remove(&name);
            } else {
                retained.push(name);
            }
        }
        *name_order = retained;
    }

    for name in adds {
        if name_set.insert(name.clone()) {
            name_order.push(name);
        }
    }
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

    /// Computes effective relocates for a parent prim in composed namespace.
    ///
    /// Collects relocates from all layers reachable through any cached prim
    /// in the same root subtree, maps them to composed namespace using the
    /// layer's namespace mapping, then chains transitive relocates.
    pub fn effective_relocates(&self, path: &Path, indices: &HashMap<Path, PrimIndex>) -> Vec<(Path, Path)> {
        let mut result = self.raw_effective_relocates(path, indices);

        // Shift each endpoint through a single ancestor rename: when an ancestor
        // prim is relocated, a relocate authored below it sits under the renamed
        // parent in composed namespace (e.g. `…/Rig/SubRig/Anim` becomes
        // `…/Rig2/SubRig/Anim` once `Rig` is relocated to `Rig2`). Faithful to
        // C++ USD relocates, sources are not transitively re-chained: a
        // relocate's authored source keeps its as-authored depth (C++
        // `_ConformLegacyRelocates` is a no-op in USD mode), so only the nearest
        // applicable ancestor rename is folded in. The snapshot is sorted by
        // target length, making the fold order deterministic.
        let snapshot = result.clone();
        for entry in &mut result {
            entry.0 = shift_through_nearest_ancestor(&entry.0, &snapshot);
            if !entry.1.is_empty() {
                entry.1 = shift_through_nearest_ancestor(&entry.1, &snapshot);
            }
        }

        result
    }

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
        let root_name = root_prim_name(path);

        // Sorted iteration: a `HashMap` walk would make the collected layer-map
        // order (and so downstream relocate composition) hash-order-dependent.
        let mut cached_paths: Vec<&Path> = indices.keys().collect();
        cached_paths.sort();
        for cached_path in cached_paths {
            let cached_index = &indices[cached_path];
            if root_prim_name(cached_path) != root_name {
                continue;
            }
            for node in cached_index.all_nodes() {
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Only the nearest ancestor rename shifts an endpoint; a relocate's source
    /// is not transitively re-chained through a rename applied to an already-
    /// shifted path (C++ `_ConformLegacyRelocates` is a no-op in USD mode).
    #[test]
    fn nearest_ancestor_only() {
        let renames = vec![
            (Path::from("/Rig"), Path::from("/Rig2")),
            (Path::from("/Rig2/Sub"), Path::from("/Rig2/SubX")),
        ];
        // `/Rig` is the only ancestor rename that prefixes the as-authored
        // endpoint, so the shift applies it once and stops: `/Rig/Sub/Anim`
        // becomes `/Rig2/Sub/Anim`, and the deeper `/Rig2/Sub` rename — which
        // matches only the shifted path — is not re-applied.
        let shifted = shift_through_nearest_ancestor(&Path::from("/Rig/Sub/Anim"), &renames);
        assert_eq!(shifted, Path::from("/Rig2/Sub/Anim"));
    }

    /// An endpoint with no ancestor rename is returned unchanged, and a rename
    /// whose source equals the endpoint itself never applies.
    #[test]
    fn no_ancestor_match_unchanged() {
        let renames = vec![(Path::from("/A"), Path::from("/B"))];
        assert_eq!(
            shift_through_nearest_ancestor(&Path::from("/A"), &renames),
            Path::from("/A")
        );
        assert_eq!(
            shift_through_nearest_ancestor(&Path::from("/X/Y"), &renames),
            Path::from("/X/Y")
        );
    }
}
