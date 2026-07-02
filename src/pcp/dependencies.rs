//! Reverse dependency index from layer sites to composed prim indices.
//!
//! For each composed [`PrimIndex`], records the `(layer_index, site_path)`
//! pairs read by its graph. When an authoring change reports "layer L
//! changed at path P", [`Dependencies::lookup_with_ancestors`] (plus
//! [`subtree_lookup`](Self::subtree_lookup) for fanout downward) returns
//! the prim indices that need invalidating. A coarser `layer → indices` map
//! ([`indices_for_layers`](Dependencies::indices_for_layers)) answers the
//! whole-layer question a mute/unmute or layer-stack edit asks, without
//! scanning every cached index.
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
    /// Reverse `layer → prim-index-paths` map over the layers each index's
    /// composition actually reaches — any dependency node's own layer or a member
    /// of that node's resolved layer stack (including the self-Root edge, which
    /// `per_layer` skips, since the local prim reads its own root layer stack). A
    /// `subLayers`/offset/relocate/`timeCodesPerSecond`/`expressionVariables` edit
    /// or a mute/unmute collects its victims as a union of lookups over the changed
    /// layers ([`indices_for_layers`](Self::indices_for_layers)). A muted
    /// reference/payload target — reached by nothing — is kept out and tracked by
    /// canonical identifier in [`by_muted_canonical`](Self::by_muted_canonical).
    by_layer: HashMap<LayerId, HashSet<Path>>,
    /// The layers `prim_index_path` registered under in `by_layer`, for O(1)
    /// retraction on removal.
    by_prim_layers: HashMap<Path, HashSet<LayerId>>,
    /// Reverse `canonical muted identifier → prim-index-paths` map: which indices
    /// depend on a reference/payload target's *mute state* without reaching it
    /// through a live site. Two cases resolve to one key here — a target muted
    /// before it ever loaded (never interned, so keyed by the canonical identifier
    /// the mute matched), and one muted after loading (its stack emptied, grafting
    /// no node, so keyed by the interned target root's identifier, which equals that
    /// same canonical). Unmuting a target fans back to these indices
    /// ([`indices_for_mute_toggle`](Self::indices_for_mute_toggle)); muting a
    /// still-loaded target reaches its referrer through `by_layer` (the pre-mute
    /// reach) instead.
    by_muted_canonical: HashMap<String, HashSet<Path>>,
    /// The canonical identifiers `prim_index_path` registered under in
    /// `by_muted_canonical`, for O(1) retraction on removal.
    by_prim_muted: HashMap<Path, HashSet<String>>,
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
        // The layers this index touched, for the `by_layer` map. Includes the
        // self-Root edge the site map skips.
        let mut layers: HashSet<LayerId> = HashSet::new();
        // Include culled arc nodes (empty targets) and inert relocation-source
        // nodes: authoring a spec at such a site must invalidate this prim so the
        // node un-culls / re-relocates on recomposition.
        for node in index.dependency_nodes() {
            let is_self_root = node.arc == ArcType::Root && node.path == *prim_index_path;
            layers.insert(node.layer_id());
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter() {
                layers.insert(layer);
                // The site map skips the self-Root edge to stay compact; the
                // layer map keeps it (the prim reads its own root stack).
                if is_self_root {
                    continue;
                }
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
        for &layer in &layers {
            self.by_layer.entry(layer).or_default().insert(prim_index_path.clone());
        }

        // A reference/payload target this index depends on the mute state of but has
        // no live site for: one muted before loading (never interned — its canonical
        // identifier is in `muted_unloaded_targets`), or one muted after loading (its
        // stack emptied, so it grafted no node — the interned target root, whose
        // identifier is that same canonical). Register both by canonical identifier
        // so unmuting the target fans back here, without counting it as reached.
        let muted: HashSet<String> = index
            .muted_unloaded_targets()
            .iter()
            .cloned()
            .chain(
                index
                    .muted_external_targets()
                    .iter()
                    .map(|&t| graph.identifier(t).to_string()),
            )
            .collect();
        for canonical in &muted {
            self.by_muted_canonical
                .entry(canonical.clone())
                .or_default()
                .insert(prim_index_path.clone());
        }

        self.by_prim.insert(prim_index_path.clone(), registered);
        self.by_prim_layers.insert(prim_index_path.clone(), layers);
        // The common unmuted index depends on no muted target, so skip an empty entry.
        if !muted.is_empty() {
            self.by_prim_muted.insert(prim_index_path.clone(), muted);
        }

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
        // Retract the `layer → index` registrations.
        if let Some(layers) = self.by_prim_layers.remove(prim_index_path) {
            for li in layers {
                if let Some(set) = self.by_layer.get_mut(&li) {
                    set.remove(prim_index_path);
                    if set.is_empty() {
                        self.by_layer.remove(&li);
                    }
                }
            }
        }
        // Retract the `muted canonical identifier → index` registrations.
        if let Some(canonicals) = self.by_prim_muted.remove(prim_index_path) {
            for canonical in canonicals {
                if let Some(set) = self.by_muted_canonical.get_mut(&canonical) {
                    set.remove(prim_index_path);
                    if set.is_empty() {
                        self.by_muted_canonical.remove(&canonical);
                    }
                }
            }
        }
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
        Self::dedup_paths(per_layer.chain(by_path).flatten())
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
                .chain(std::iter::once(self.path_dependents(site_path)))
                .flatten(),
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
        Self::dedup_paths(map.subtree(prefix).flat_map(|(_, deps)| deps.as_slice()))
    }

    /// Prim indices to invalidate for a change to any layer in `affected` — the
    /// deduplicated union of the `by_layer` registrations. The victim set for a
    /// mute/unmute or a `subLayers`/offset/relocate/`timeCodesPerSecond`/`expressionVariables`
    /// edit (C++ `PcpChanges` layer-stack fanout). Each registered index reads a
    /// layer stack containing one of `affected`, so it is exactly one the change can
    /// restructure. A referrer that only *skipped* a muted target reaches it through
    /// [`indices_for_mute_toggle`](Self::indices_for_mute_toggle) instead.
    pub(super) fn indices_for_layers(&self, affected: &HashSet<LayerId>) -> Vec<Path> {
        Self::dedup_paths(affected.iter().filter_map(|layer| self.by_layer.get(layer)).flatten())
    }

    /// Prim indices to invalidate when the layer with canonical identifier
    /// `canonical` toggles muted state and its stack members shift by `affected`
    /// (from [`mute_fanout`](super::LayerGraph::mute_fanout)): the indices that read
    /// one of `affected` through `by_layer` (a still-loaded target reached before
    /// the toggle), plus those that only *skipped* the target and recorded it in
    /// `by_muted_canonical` (muted before loading, or after its stack emptied).
    /// Deduplicated in one pass over both streams.
    pub(super) fn indices_for_mute_toggle(&self, affected: &HashSet<LayerId>, canonical: &str) -> Vec<Path> {
        let by_layer = affected.iter().filter_map(|layer| self.by_layer.get(layer)).flatten();
        let by_canonical = self.by_muted_canonical.get(canonical).into_iter().flatten();
        Self::dedup_paths(by_layer.chain(by_canonical))
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

    /// Collects the deduplicated union of dependent paths, preserving first-seen
    /// order. Callers flatten their per-site lists into one path stream.
    fn dedup_paths<'a>(deps: impl Iterator<Item = &'a Path>) -> Vec<Path> {
        let mut out: Vec<Path> = Vec::new();
        let mut seen: HashSet<&Path> = HashSet::new();
        for d in deps {
            if seen.insert(d) {
                out.push(d.clone());
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcp::layer_graph::ExternalStack;
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

    fn make_index(g: &LayerGraph, prim_path: &Path, nodes: Vec<(ArcType, LayerId, Path)>) -> PrimIndex {
        let mut idx = PrimIndex::default();
        for (arc, layer_id, node_path) in nodes {
            // The stack rooted at `layer_id` — `external_stack_id` resolves it to the
            // root or a plain instance the graph minted for each sublayer-free layer.
            let stack = match g.external_stack_id(layer_id, &HashMap::new()) {
                ExternalStack::Ready(id) => id,
                ExternalStack::Demand => panic!("no minted stack for test layer {layer_id:?}"),
            };
            let map = MapFunction::from_pair_identity(node_path.clone(), prim_path.clone());
            idx.push_node(Node::new(stack, layer_id, node_path, arc, map.clone(), map, false));
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
        let index = make_index(&g, &foo, vec![(ArcType::Root, l0, foo.clone())]);
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
            &g,
            &here,
            vec![
                (ArcType::Root, l0, here.clone()),
                (ArcType::Reference, l1, there.clone()),
            ],
        );
        deps.add(&here, &index, &g);
        assert_eq!(deps.lookup_with_ancestors(l1, &there), vec![here.clone()]);
    }

    /// `indices_for_layers` scopes a layer-set invalidation to the indices that
    /// touched a changed layer. Unlike the `(layer, site)` map, it registers the
    /// self-Root edge, so a local prim touching only its root layer is found; a
    /// sibling reading a different layer is not, and removal retracts both maps.
    #[test]
    fn by_layer_scopes_invalidation() {
        let g = graph(2);
        let (l0, l1) = (g.all_ids()[0], g.all_ids()[1]);
        let mut deps = Dependencies::default();

        let local = p("/Local");
        deps.add(
            &local,
            &make_index(&g, &local, vec![(ArcType::Root, l0, local.clone())]),
            &g,
        );
        let refp = p("/Ref");
        deps.add(
            &refp,
            &make_index(
                &g,
                &refp,
                vec![
                    (ArcType::Root, l0, refp.clone()),
                    (ArcType::Reference, l1, p("/Target")),
                ],
            ),
            &g,
        );

        // Both prims' Root edges live on l0; only /Ref reaches l1.
        let mut on_l0 = deps.indices_for_layers(&HashSet::from([l0]));
        on_l0.sort();
        assert_eq!(on_l0, vec![local.clone(), refp.clone()]);
        assert_eq!(deps.indices_for_layers(&HashSet::from([l1])), vec![refp.clone()]);

        // Removal retracts the `by_layer` registrations.
        deps.remove(&refp);
        assert!(deps.indices_for_layers(&HashSet::from([l1])).is_empty());
        assert_eq!(deps.indices_for_layers(&HashSet::from([l0])), vec![local]);
    }

    #[test]
    fn ancestor_walk_finds_dep() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let mut deps = Dependencies::default();
        let here = p("/A/B");
        let arc_site = p("/X/Y");
        let index = make_index(
            &g,
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
        deps.add(&a, &make_index(&g, &a, vec![(ArcType::Reference, l0, xy.clone())]), &g);
        deps.add(
            &b,
            &make_index(&g, &b, vec![(ArcType::Reference, l0, xy_child.clone())]),
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
            &make_index(&g, &here, vec![(ArcType::Reference, l0, there.clone())]),
            &g,
        );
        assert!(!deps.lookup_with_ancestors(l0, &there).is_empty());
        deps.remove(&here);
        assert!(deps.lookup_with_ancestors(l0, &there).is_empty());
    }
}
