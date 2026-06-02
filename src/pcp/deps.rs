//! Reverse dependency index from layer sites to composed prim indices.
//!
//! For each composed [`PrimIndex`], records the `(layer_index, site_path)`
//! pairs read by its graph. When an authoring change reports "layer L
//! changed at path P", [`Dependencies::lookup_with_ancestors`] (plus
//! [`subtree_lookup`](Self::subtree_lookup) for fanout downward) returns
//! the prim indices that need invalidating.
//!
//! Single-layer-stack equivalent of C++ `Pcp_Dependencies`. Because
//! [`Cache`](super::Cache) owns exactly one layer stack, the outer key is
//! `layer_index` rather than a layer-stack reference.

use std::collections::{HashMap, HashSet};

use crate::sdf::Path;

use super::graph::ArcType;
use super::index::PrimIndex;

#[derive(Debug, Default)]
pub(super) struct Dependencies {
    /// `per_layer[layer_index][site_path]` = prim index paths that read this site.
    per_layer: Vec<HashMap<Path, Vec<Path>>>,
    /// Reverse map for cheap removal: prim_index_path → list of (layer, site)
    /// it registered. Avoids re-walking the index when invalidating.
    by_prim: HashMap<Path, Vec<(usize, Path)>>,
}

impl Dependencies {
    /// Ensure `per_layer` has at least `layer_count` slots.
    fn ensure_layer_capacity(&mut self, layer_count: usize) {
        if self.per_layer.len() < layer_count {
            self.per_layer.resize_with(layer_count, HashMap::new);
        }
    }

    /// Register every `(layer_index, node.path)` site referenced by `index` as
    /// a dependency of `prim_index_path`. Replaces any prior registration for
    /// the same prim. A site whose node spans several sublayers registers each
    /// member layer, so a change to any of them fans out to this prim.
    ///
    /// The implicit "self" edge — a Root node whose path equals the prim's
    /// own path — is skipped to keep the map compact. C++
    /// `PcpDependencyTypeRoot` follows the same rule.
    pub(super) fn add(&mut self, prim_index_path: &Path, index: &PrimIndex, layer_count: usize) {
        self.ensure_layer_capacity(layer_count);

        // Clear any previous registration before adding the new one.
        self.remove(prim_index_path);

        // `seen` provides O(1) dedup as we walk graph nodes; the parallel
        // `registered` Vec preserves insertion order for the reverse-map
        // entry (the order is irrelevant to lookups but helps debug).
        let mut seen: HashSet<(usize, Path)> = HashSet::new();
        let mut registered: Vec<(usize, Path)> = Vec::new();
        // Include culled arc nodes (empty targets): authoring a spec at such a
        // site must invalidate this prim so the node un-culls on recomposition.
        for node in index.all_nodes() {
            if node.arc == ArcType::Root && node.path == *prim_index_path {
                continue;
            }
            for (layer, _) in node.layers() {
                let key = (layer, node.path.clone());
                if !seen.insert(key.clone()) {
                    continue;
                }
                registered.push(key);
                self.per_layer[layer]
                    .entry(node.path.clone())
                    .or_default()
                    .push(prim_index_path.clone());
            }
        }

        // Ensure the prim's own path is findable on every layer. Without
        // this, cached misses (empty `PrimIndex`) and self-Root-only
        // indices have no reverse-map entry, so an authoring change that
        // names exactly this path on a layer the graph doesn't already
        // touch cannot reach them via `lookup_with_ancestors`. Synthetic
        // self-registrations are cheap (O(layer_count)) and let the
        // dependency map serve as the single source of truth for "which
        // prims observe site X on layer L".
        for li in 0..layer_count {
            let key = (li, prim_index_path.clone());
            if !seen.insert(key.clone()) {
                continue;
            }
            registered.push(key);
            self.per_layer[li]
                .entry(prim_index_path.clone())
                .or_default()
                .push(prim_index_path.clone());
        }
        self.by_prim.insert(prim_index_path.clone(), registered);
    }

    /// Drop all registered `(layer, site)` entries for `prim_index_path`.
    pub(super) fn remove(&mut self, prim_index_path: &Path) {
        let Some(sites) = self.by_prim.remove(prim_index_path) else {
            return;
        };
        for (li, site) in sites {
            if let Some(map) = self.per_layer.get_mut(li) {
                if let Some(deps) = map.get_mut(&site) {
                    deps.retain(|p| p != prim_index_path);
                    if deps.is_empty() {
                        map.remove(&site);
                    }
                }
            }
        }
    }

    /// Drop all entries.
    pub(super) fn clear(&mut self) {
        for m in &mut self.per_layer {
            m.clear();
        }
        self.by_prim.clear();
    }

    /// Find prim indices that depend on `(layer_index, site_path)` or on any
    /// ancestor of `site_path`.
    ///
    /// The ancestor walk matches C++ `Pcp_DidChangeDependents` (changes.cpp):
    /// an arc introduced at `/Foo` makes `/Foo/Bar`'s composed index depend
    /// transitively on opinions at `/Foo`, so a change at `/Foo` invalidates
    /// `/Foo/Bar` too.
    pub(super) fn lookup_with_ancestors(&self, layer_index: usize, site_path: &Path) -> Vec<Path> {
        let Some(map) = self.per_layer.get(layer_index) else {
            return Vec::new();
        };
        let mut out: Vec<Path> = Vec::new();
        let mut seen: HashSet<Path> = HashSet::new();
        let mut cursor = Some(site_path.clone());
        while let Some(p) = cursor {
            if let Some(deps) = map.get(&p) {
                for d in deps {
                    if seen.insert(d.clone()) {
                        out.push(d.clone());
                    }
                }
            }
            if p.is_abs_root() {
                break;
            }
            cursor = p.parent();
        }
        out
    }

    /// Find prim indices whose dependency site is at or below `prefix` in
    /// `layer_index`.
    ///
    /// Used to fan out an invalidation downward (a significant change at
    /// `/Foo` must drop every cached index whose graph touches `/Foo/*`).
    /// Linear scan over the layer's dependency map — matches the cost
    /// profile of the previous full-cache invalidation in the worst case
    /// and is strictly cheaper on the single-prim authoring path.
    //
    // TODO: back the per-layer map with an `SdfPathTable`-like trie so
    // this becomes an `O(log n + k)` subtree range query. Same primitive
    // needed by `Cache::drop_index_subtree`.
    //
    // TODO: snapshot a `culled_dependencies` set per prim index when
    // `IndexBuilder` starts culling weaker nodes. Without it, an inert
    // spec added at a culled site fails to un-cull the node on next
    // composition.
    pub(super) fn subtree_lookup(&self, layer_index: usize, prefix: &Path) -> Vec<Path> {
        let Some(map) = self.per_layer.get(layer_index) else {
            return Vec::new();
        };
        let mut out: Vec<Path> = Vec::new();
        let mut seen: HashSet<Path> = HashSet::new();
        for (site, deps) in map {
            if site.has_prefix(prefix) {
                for d in deps {
                    if seen.insert(d.clone()) {
                        out.push(d.clone());
                    }
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcp::graph::Node;
    use crate::pcp::mapping::MapFunction;

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid path")
    }

    fn make_index(prim_path: &Path, nodes: Vec<(ArcType, usize, Path)>) -> PrimIndex {
        let mut idx = PrimIndex::default();
        for (arc, layer_index, node_path) in nodes {
            let map = MapFunction::from_pair_identity(node_path.clone(), prim_path.clone());
            idx.push_node(Node::new(layer_index, node_path, arc, map.clone(), map, false));
        }
        idx
    }

    #[test]
    fn synthetic_self_registration_covers_empty_index() {
        // An index with only a self-Root edge contributes no graph-derived
        // dependencies (the Root-at-own-path is intentionally skipped to
        // keep the map compact). The synthetic self-registration ensures
        // the prim path is still findable on every layer.
        let mut deps = Dependencies::default();
        let foo = p("/Foo");
        let index = make_index(&foo, vec![(ArcType::Root, 0, foo.clone())]);
        deps.add(&foo, &index, 2);
        assert_eq!(deps.lookup_with_ancestors(0, &foo), vec![foo.clone()]);
        assert_eq!(deps.lookup_with_ancestors(1, &foo), vec![foo.clone()]);
    }

    #[test]
    fn reference_arc_registers_dependency() {
        let mut deps = Dependencies::default();
        let here = p("/World/Inst");
        let there = p("/Model");
        let index = make_index(
            &here,
            vec![(ArcType::Root, 0, here.clone()), (ArcType::Reference, 1, there.clone())],
        );
        deps.add(&here, &index, 2);
        assert_eq!(deps.lookup_with_ancestors(1, &there), vec![here.clone()]);
    }

    #[test]
    fn ancestor_walk_finds_dep() {
        let mut deps = Dependencies::default();
        let here = p("/A/B");
        let arc_site = p("/X/Y");
        let index = make_index(
            &here,
            vec![
                (ArcType::Root, 0, here.clone()),
                (ArcType::Inherit, 0, arc_site.clone()),
            ],
        );
        deps.add(&here, &index, 1);
        // A change at /X/Y/Child should still invalidate /A/B (it depends
        // transitively on /X/Y).
        assert_eq!(deps.lookup_with_ancestors(0, &p("/X/Y/Child")), vec![here.clone()]);
    }

    #[test]
    fn subtree_lookup_finds_descendants() {
        let mut deps = Dependencies::default();
        let a = p("/A");
        let b = p("/B");
        let xy = p("/X/Y");
        let xy_child = p("/X/Y/Child");
        deps.add(&a, &make_index(&a, vec![(ArcType::Reference, 0, xy.clone())]), 1);
        deps.add(&b, &make_index(&b, vec![(ArcType::Reference, 0, xy_child.clone())]), 1);
        // Subtree at /X/Y catches both sites.
        let mut found = deps.subtree_lookup(0, &p("/X"));
        found.sort();
        assert_eq!(found, vec![a.clone(), b.clone()]);
    }

    #[test]
    fn remove_drops_all_entries() {
        let mut deps = Dependencies::default();
        let here = p("/A");
        let there = p("/X");
        deps.add(
            &here,
            &make_index(&here, vec![(ArcType::Reference, 0, there.clone())]),
            1,
        );
        assert!(!deps.lookup_with_ancestors(0, &there).is_empty());
        deps.remove(&here);
        assert!(deps.lookup_with_ancestors(0, &there).is_empty());
    }
}
