//! Reverse dependency index from layer sites to composed prim indices.
//!
//! For each composed [`PrimIndex`], records the `(layer_index, site_path)`
//! pairs read by its graph. When an authoring change reports "layer L
//! changed at path P", [`Dependencies::lookup_with_ancestors`] (plus
//! [`subtree_lookup`](Self::subtree_lookup) for fanout downward) returns
//! the prim indices that need invalidating.
//!
//! Single-layer-stack equivalent of C++ `Pcp_Dependencies`. Because
//! [`IndexCache`](super::IndexCache) owns exactly one layer stack, the outer key is
//! `layer_index` rather than a layer-stack reference.

use std::collections::{HashMap, HashSet};

use crate::sdf::{self, Path};

use super::prim_graph::ArcType;
use super::prim_index::PrimIndex;
use super::{LayerGraph, LayerId};

#[derive(Debug, Default)]
pub(super) struct Dependencies {
    /// `per_layer[layer_id][site_path]` = prim index paths that read this site.
    ///
    /// The inner map is an [`sdf::PathTable`] so
    /// [`subtree_lookup`](Self::subtree_lookup) is a subtree walk rather than a
    /// full scan.
    per_layer: HashMap<LayerId, sdf::PathTable<Vec<Path>>>,
    /// Reverse map for cheap removal: prim_index_path → list of (layer, site)
    /// it registered. Avoids re-walking the index when invalidating.
    by_prim: HashMap<Path, Vec<(LayerId, Path)>>,
    /// Layer-agnostic set of prim-index paths, each observing exactly its own
    /// path. A prim self-registers here so an empty or cache-miss index stays
    /// findable when a spec is first authored at its path on a layer its graph
    /// does not yet touch; one entry per prim covers that prim on every layer.
    by_path: HashSet<Path>,
}

impl Dependencies {
    /// Register every `(layer_id, node.path)` site referenced by `index` as a
    /// dependency of `prim_index_path`. Replaces any prior registration for the
    /// same prim. A site whose node spans several sublayers registers each member
    /// layer, so a change to any of them fans out to this prim.
    ///
    /// The implicit "self" edge — a Root node whose path equals the prim's
    /// own path — is skipped to keep the map compact. C++
    /// `PcpDependencyTypeRoot` follows the same rule.
    pub(super) fn add(&mut self, prim_index_path: &Path, index: &PrimIndex, graph: &LayerGraph) {
        // Clear any previous registration before adding the new one.
        self.remove(prim_index_path);

        // `seen` provides O(1) dedup as we walk graph nodes; the parallel
        // `registered` Vec preserves insertion order for the reverse-map
        // entry (the order is irrelevant to lookups but helps debug).
        let mut seen: HashSet<(LayerId, Path)> = HashSet::new();
        let mut registered: Vec<(LayerId, Path)> = Vec::new();
        // Include culled arc nodes (empty targets) and inert relocation-source
        // nodes: authoring a spec at such a site must invalidate this prim so the
        // node un-culls / re-relocates on recomposition.
        for node in index.dependency_nodes() {
            if node.arc == ArcType::Root && node.path == *prim_index_path {
                continue;
            }
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter() {
                let key = (layer, node.path.clone());
                if !seen.insert(key.clone()) {
                    continue;
                }
                registered.push(key);
                self.per_layer
                    .entry(layer)
                    .or_default()
                    .get_or_insert_default(&node.path)
                    .push(prim_index_path.clone());
            }
        }

        self.by_prim.insert(prim_index_path.clone(), registered);

        // Register the prim's own path once, independent of layer. Without
        // this, cached misses (empty `PrimIndex`) and self-Root-only indices
        // have no reverse-map entry, so an authoring change that names exactly
        // this path on a layer the graph doesn't already touch cannot reach
        // them. The per-layer lookups fold `by_path` in (see
        // [`path_dependents`](Self::path_dependents)), so one layer-agnostic
        // entry per prim keeps every layer covered.
        self.by_path.insert(prim_index_path.clone());
    }

    /// Drop all registered `(layer, site)` entries for `prim_index_path`.
    pub(super) fn remove(&mut self, prim_index_path: &Path) {
        // Drop the prim's layer-agnostic self-registration so an eviction or
        // rebuild leaves no stale `by_path` entry.
        self.by_path.remove(prim_index_path);
        let Some(sites) = self.by_prim.remove(prim_index_path) else {
            return;
        };
        for (li, site) in sites {
            if let Some(map) = self.per_layer.get_mut(&li) {
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
        self.per_layer.clear();
        self.by_prim.clear();
        self.by_path.clear();
    }

    /// Find prim indices that depend on `(layer_id, site_path)` or on any
    /// ancestor of `site_path`.
    ///
    /// The ancestor walk matches C++ `Pcp_DidChangeDependents` (changes.cpp):
    /// an arc introduced at `/Foo` makes `/Foo/Bar`'s composed index depend
    /// transitively on opinions at `/Foo`, so a change at `/Foo` invalidates
    /// `/Foo/Bar` too.
    pub(super) fn lookup_with_ancestors(&self, layer_id: LayerId, site_path: &Path) -> Vec<Path> {
        let per_layer = self
            .per_layer
            .get(&layer_id)
            .into_iter()
            .flat_map(|map| map.ancestors(site_path).map(|(_, deps)| deps.as_slice()));
        // The layer-agnostic self-registrations are findable on every layer, so
        // an ancestor that observes its own path invalidates `site_path` even on
        // a layer its graph does not touch.
        let by_path = site_path.ancestors().map(|anc| self.path_dependents(&anc));
        Self::dedup_paths(per_layer.chain(by_path))
    }

    /// Find prim indices whose graph reads exactly `(layer_id, site_path)`,
    /// with no ancestor or subtree walk. The spec-tier rescan uses this to
    /// reach the nodes sitting at that precise site whose `has_specs` flag an
    /// inert spec add or remove can flip.
    pub(super) fn exact_lookup(&self, layer_id: LayerId, site_path: &Path) -> Vec<Path> {
        let per_layer = self
            .per_layer
            .get(&layer_id)
            .and_then(|map| map.get(site_path))
            .map(Vec::as_slice);
        Self::dedup_paths(
            per_layer
                .into_iter()
                .chain(std::iter::once(self.path_dependents(site_path))),
        )
    }

    /// Find prim indices whose graph-derived dependency site is at or below
    /// `prefix` in `layer_index`.
    ///
    /// Used to fan out an invalidation downward to the cross-namespace
    /// dependents a [`drop_index_subtree`](super::IndexCache::drop_index_subtree)
    /// of `prefix` misses: a prim like `/World/Inst` whose own path lies outside
    /// `prefix` but whose graph references `/Foo/Model` under it. Walks the
    /// `prefix` subtree of the layer's dependency [`sdf::PathTable`].
    ///
    /// The layer-agnostic [`by_path`](Self::by_path) self-registrations are not
    /// folded in here: a prim whose only registration is its own path under
    /// `prefix` is a namespace descendant of `prefix`, so the caller's
    /// literal-path subtree drop already reaches it.
    pub(super) fn subtree_lookup(&self, layer_id: LayerId, prefix: &Path) -> Vec<Path> {
        let Some(map) = self.per_layer.get(&layer_id) else {
            return Vec::new();
        };
        Self::dedup_paths(map.subtree(prefix).map(|(_, deps)| deps.as_slice()))
    }

    /// Prim indices that observe exactly `path`, independent of layer.
    ///
    /// [`exact_lookup`](Self::exact_lookup) and
    /// [`lookup_with_ancestors`](Self::lookup_with_ancestors) fold this in so a
    /// first opinion authored at `path` reaches the prims registered there
    /// regardless of which layer carried it.
    fn path_dependents(&self, path: &Path) -> &[Path] {
        self.by_path.get(path).map_or(&[], std::slice::from_ref)
    }

    /// Collects the deduplicated union of several dependent-path lists,
    /// preserving first-seen order.
    fn dedup_paths<'a>(lists: impl Iterator<Item = &'a [Path]>) -> Vec<Path> {
        let mut out: Vec<Path> = Vec::new();
        let mut seen: HashSet<&Path> = HashSet::new();
        for deps in lists {
            for d in deps {
                if seen.insert(d) {
                    out.push(d.clone());
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcp::layer_graph::LayerStackId;
    use crate::pcp::mapping::MapFunction;
    use crate::pcp::prim_graph::Node;

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid path")
    }

    /// A layer graph of `n` sublayer-free in-memory layers, so the sublayer
    /// stack rooted at the n-th layer is just that layer — the single-layer
    /// stacks a node's site registers against.
    fn graph(n: usize) -> LayerGraph {
        let layers = (0..n)
            .map(|i| sdf::Layer::new_in_memory(format!("l{i}.usda")))
            .collect();
        LayerGraph::from_layers(layers, 0, sdf::LayerRegistry::default())
    }

    fn make_index(prim_path: &Path, nodes: Vec<(ArcType, LayerId, Path)>) -> PrimIndex {
        let mut idx = PrimIndex::default();
        for (arc, layer_id, node_path) in nodes {
            let map = MapFunction::from_pair_identity(node_path.clone(), prim_path.clone());
            idx.push_node(Node::new(
                LayerStackId::Sublayer(layer_id),
                layer_id,
                node_path,
                arc,
                map.clone(),
                map,
                false,
            ));
        }
        idx
    }

    #[test]
    fn by_path_covers_empty_index() {
        // An index with only a self-Root edge contributes no graph-derived
        // dependencies (the Root-at-own-path is intentionally skipped to keep
        // the map compact). The layer-agnostic `by_path` entry ensures the
        // prim path is still findable on every layer, so a first opinion
        // authored at `/Foo` invalidates it regardless of which layer carries
        // the change.
        let g = graph(2);
        let (l0, l1) = (g.all_ids()[0], g.all_ids()[1]);
        let mut deps = Dependencies::default();
        let foo = p("/Foo");
        let index = make_index(&foo, vec![(ArcType::Root, l0, foo.clone())]);
        deps.add(&foo, &index, &g);
        assert_eq!(deps.lookup_with_ancestors(l0, &foo), vec![foo.clone()]);
        assert_eq!(deps.lookup_with_ancestors(l1, &foo), vec![foo.clone()]);
        assert_eq!(deps.exact_lookup(l1, &foo), vec![foo.clone()]);
    }

    #[test]
    fn reference_arc_registers_dependency() {
        let g = graph(2);
        let (l0, l1) = (g.all_ids()[0], g.all_ids()[1]);
        let mut deps = Dependencies::default();
        let here = p("/World/Inst");
        let there = p("/Model");
        let index = make_index(
            &here,
            vec![
                (ArcType::Root, l0, here.clone()),
                (ArcType::Reference, l1, there.clone()),
            ],
        );
        deps.add(&here, &index, &g);
        assert_eq!(deps.lookup_with_ancestors(l1, &there), vec![here.clone()]);
    }

    #[test]
    fn ancestor_walk_finds_dep() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let mut deps = Dependencies::default();
        let here = p("/A/B");
        let arc_site = p("/X/Y");
        let index = make_index(
            &here,
            vec![
                (ArcType::Root, l0, here.clone()),
                (ArcType::Inherit, l0, arc_site.clone()),
            ],
        );
        deps.add(&here, &index, &g);
        // A change at /X/Y/Child should still invalidate /A/B (it depends
        // transitively on /X/Y).
        assert_eq!(deps.lookup_with_ancestors(l0, &p("/X/Y/Child")), vec![here.clone()]);
    }

    #[test]
    fn subtree_lookup_finds_descendants() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let mut deps = Dependencies::default();
        let a = p("/A");
        let b = p("/B");
        let xy = p("/X/Y");
        let xy_child = p("/X/Y/Child");
        deps.add(&a, &make_index(&a, vec![(ArcType::Reference, l0, xy.clone())]), &g);
        deps.add(
            &b,
            &make_index(&b, vec![(ArcType::Reference, l0, xy_child.clone())]),
            &g,
        );
        // Subtree at /X/Y catches both sites.
        let mut found = deps.subtree_lookup(l0, &p("/X"));
        found.sort();
        assert_eq!(found, vec![a.clone(), b.clone()]);
    }

    #[test]
    fn remove_drops_all_entries() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let mut deps = Dependencies::default();
        let here = p("/A");
        let there = p("/X");
        deps.add(
            &here,
            &make_index(&here, vec![(ArcType::Reference, l0, there.clone())]),
            &g,
        );
        assert!(!deps.lookup_with_ancestors(l0, &there).is_empty());
        deps.remove(&here);
        assert!(deps.lookup_with_ancestors(l0, &there).is_empty());
    }
}
