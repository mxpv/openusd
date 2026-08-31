//! Reverse dependency index from layer sites to composed prim indices.
//!
//! For each composed [`PrimIndex`], records the `(layer_index, site_path)`
//! pairs read by its graph. When an authoring change reports "layer L
//! changed at path P", [`ancestor_sites`](Dependencies::ancestor_sites) (plus
//! [`subtree_lookup`](Self::subtree_lookup) for fanout downward) returns
//! the registrations that change reaches. The pairs are untranslated: naming
//! the composed path a dependent is affected at needs that dependent's own
//! composition graph, which this table does not hold, so
//! [`IndexStore`](super::index_store::IndexStore) joins and translates them.
//! A coarser `layer → indices` map
//! ([`indices_for_layers`](Dependencies::indices_for_layers)) answers the
//! whole-layer question a mute/unmute or layer-stack edit asks, without
//! scanning every cached index.
//!
//! Single-layer-stack equivalent of C++ `Pcp_Dependencies`. Because
//! [`IndexCache`](super::IndexCache) owns exactly one layer stack, the outer key is
//! `layer_index` rather than a layer-stack reference.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::mem;

use crate::sdf::{self, Path};

use super::prim_index::{PrimIndex, registers_site};
use super::prim_indexer::ExprVarDeps;
use super::{LayerGraph, LayerId, LayerStackId};

#[derive(Debug, Default)]
pub(super) struct Dependencies {
    /// `per_layer[layer_id][site_path]` = prim index paths that read this site.
    ///
    /// The inner map is an [`sdf::PathTable`] so
    /// [`subtree_lookup`](Self::subtree_lookup) is a subtree walk rather than a
    /// full scan.
    per_layer: HashMap<LayerId, sdf::PathTable<Vec<Path>>>,
    /// Reverse map for cheap removal: `prim_index_path` → list of (layer, site)
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
    /// Reverse `layer → prim-index-paths` map for `defaultPrim` consultation:
    /// which indices resolved a reference or payload target through this layer's
    /// default because the arc named no prim. Registered whether or not the layer
    /// named one — an unresolved default grafts no node, so no site records it —
    /// and read by [`prims_using_default_prim`](Self::prims_using_default_prim)
    /// to evict exactly those indices when the field is edited.
    by_default_prim: HashMap<LayerId, HashSet<Path>>,
    /// The layers `prim_index_path` registered under in `by_default_prim`, for
    /// O(1) retraction on removal.
    by_prim_default_prim: HashMap<Path, HashSet<LayerId>>,
    /// Reverse `layer stack → prim-index-paths` map over the stacks each index's
    /// dependency nodes compose against. An `expressionVariables` edit whose
    /// stack delta demands a full resync — the variable source changed, or a
    /// changed name is one of the stack's own sublayer dependencies — collects
    /// its victims here (C++ resyncs every prim using the layer stack). The root
    /// stack is never recorded: every prim composes in it, so its entry would
    /// mirror every cached path; [`prims_for_stack`](Self::prims_for_stack)
    /// answers for it with the pseudo-root instead.
    by_stack: HashMap<LayerStackId, HashSet<Path>>,
    /// The stacks `prim_index_path` registered under — in
    /// [`by_stack`](Self::by_stack), [`by_stack_vars`](Self::by_stack_vars), or
    /// both — for O(1) retraction on removal. Absent for a prim with neither
    /// registration, the common arc-free, expression-free case.
    by_prim_stacks: HashMap<Path, HashSet<LayerStackId>>,
    /// Per-stack expression-variable dependencies: `by_stack_vars[stack][prim]` =
    /// the variable names `prim`'s build read from `stack`'s composed set (C++
    /// `PcpExpressionVariablesDependencyData`). A variable edit that changes
    /// neither the stack's source nor its sublayer selection resyncs only the
    /// prims whose recorded names intersect the changed set
    /// ([`prims_using_vars`](Self::prims_using_vars)). Unlike
    /// [`by_stack`](Self::by_stack), the root stack appears here — its per-prim
    /// names are exactly what the targeted lookup needs.
    by_stack_vars: HashMap<LayerStackId, HashMap<Path, HashSet<String>>>,
}

impl Dependencies {
    /// Register every `(layer_id, node.path)` site referenced by `index` as a
    /// dependency of `prim_index_path`, together with the per-stack
    /// expression-variable names its build read (`expr_var_deps`, from
    /// [`BuildOutput::expr_var_deps`](super::prim_indexer::BuildOutput::expr_var_deps)).
    /// Replaces any prior registration for the same prim. A site whose node spans
    /// several sublayers registers each member layer, so a change to any of them
    /// fans out to this prim.
    ///
    /// The implicit "self" edge — a Root node whose path equals the prim's
    /// own path — is skipped to keep the map compact. C++
    /// `PcpDependencyTypeRoot` follows the same rule.
    pub(super) fn add(
        &mut self,
        prim_index_path: &Path,
        index: &PrimIndex,
        graph: &LayerGraph,
        expr_var_deps: ExprVarDeps,
    ) {
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
        // The layer stacks this index composes against, for the two stack-keyed
        // maps and their shared retraction. The root stack is left implicit:
        // every prim composes in it, so recording it in `by_stack` would mirror
        // the whole cache per prim; `prims_for_stack` answers for it with the
        // pseudo-root instead.
        let mut stacks: HashSet<LayerStackId> = HashSet::new();
        // Include culled arc nodes (empty targets) and inert relocation-source
        // nodes: authoring a spec at such a site must invalidate this prim so the
        // node un-culls / re-relocates on recomposition.
        for node in index.dependency_nodes() {
            let registers = registers_site(node, prim_index_path);
            layers.insert(node.layer_id());
            if node.layer_stack_id() != LayerStackId::ROOT {
                stacks.insert(node.layer_stack_id());
            }
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter() {
                layers.insert(layer);
                // The site map skips the self-Root edge to stay compact; the
                // layer map keeps it (the prim reads its own root stack).
                if !registers {
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
        // Fold the variable-reading stacks into the same retraction set — the
        // root stack included here, since its per-prim names are the step-4
        // lookup even though `by_stack` leaves it implicit.
        for (stack, names) in expr_var_deps {
            stacks.insert(stack);
            self.by_stack_vars
                .entry(stack)
                .or_default()
                .insert(prim_index_path.clone(), names);
        }
        for &stack in &stacks {
            if stack != LayerStackId::ROOT {
                self.by_stack.entry(stack).or_default().insert(prim_index_path.clone());
            }
        }

        // A reference/payload target this index depends on the mute state of but has
        // no live site for: one muted before loading (never interned — its canonical
        // identifier is in `NonSiteDeps::muted_unloaded`), or one muted after
        // loading (its stack emptied, so it grafted no node — the interned target
        // root, whose identifier is that same canonical). Register both by
        // canonical identifier so unmuting the target fans back here, without
        // counting it as reached.
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

        // Layers whose `defaultPrim` this index's composition consulted. Collected
        // through a set because one target reached by both a `references` and a
        // `payload` arc records twice.
        let defaults: HashSet<LayerId> = index.default_prim_layers().iter().copied().collect();
        for &layer in &defaults {
            self.by_default_prim
                .entry(layer)
                .or_default()
                .insert(prim_index_path.clone());
        }

        self.by_prim.insert(prim_index_path.clone(), registered);
        self.by_prim_layers.insert(prim_index_path.clone(), layers);
        // The common arc-free, expression-free index registers under no stack
        // (its only stack is the implicit root), so skip an empty entry.
        if !stacks.is_empty() {
            self.by_prim_stacks.insert(prim_index_path.clone(), stacks);
        }
        // The common unmuted index depends on no muted target, so skip an empty entry.
        if !muted.is_empty() {
            self.by_prim_muted.insert(prim_index_path.clone(), muted);
        }
        // Likewise the common index resolves no `defaultPrim`.
        if !defaults.is_empty() {
            self.by_prim_default_prim.insert(prim_index_path.clone(), defaults);
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
        // Retract the three reverse-keyed registrations: the layers this index
        // reached, the muted targets it depends on the state of, and the layers
        // whose `defaultPrim` it consulted.
        retract(&mut self.by_layer, &mut self.by_prim_layers, prim_index_path);
        retract(&mut self.by_muted_canonical, &mut self.by_prim_muted, prim_index_path);
        retract(
            &mut self.by_default_prim,
            &mut self.by_prim_default_prim,
            prim_index_path,
        );
        // Retract both stack-keyed registrations — the `by_stack` users and the
        // per-stack variable names — through the one per-prim stack set.
        if let Some(stacks) = self.by_prim_stacks.remove(prim_index_path) {
            for stack in stacks {
                if let Some(set) = self.by_stack.get_mut(&stack) {
                    set.remove(prim_index_path);
                    if set.is_empty() {
                        self.by_stack.remove(&stack);
                    }
                }
                if let Some(map) = self.by_stack_vars.get_mut(&stack) {
                    map.remove(prim_index_path);
                    if map.is_empty() {
                        self.by_stack_vars.remove(&stack);
                    }
                }
            }
        }
        let Some(sites) = self.by_prim.remove(prim_index_path) else {
            return;
        };
        for (li, site) in sites {
            if let Some(map) = self.per_layer.get_mut(&li)
                && let Some(deps) = map.get_mut(&site)
            {
                deps.retain(|p| p != prim_index_path);
                if deps.is_empty() {
                    map.remove(&site);
                }
            }
        }
    }

    /// The registered `(site, dependent)` pairs a change at `(layer_id,
    /// site_path)` reaches — the site itself and every ancestor of it, each
    /// paired with a prim index that reads it. Untranslated: this table holds no
    /// composition graphs, so it cannot say what composed path a dependent is
    /// affected at. [`IndexStore`](super::index_store::IndexStore) joins each
    /// pair to the dependent's live index and translates there.
    ///
    /// The ancestor walk matches C++ `Pcp_DidChangeDependents` (changes.cpp):
    /// an arc introduced at `/Foo` makes `/Foo/Bar`'s composed index depend
    /// transitively on opinions at `/Foo`, so a change at `/Foo` reaches
    /// `/Foo/Bar` too.
    pub(super) fn ancestor_sites<'a>(
        &'a self,
        layer_id: LayerId,
        site_path: &'a Path,
    ) -> impl Iterator<Item = (&'a Path, &'a Path)> {
        self.per_layer
            .get(&layer_id)
            .into_iter()
            .flat_map(move |map| ancestors_to_variant_boundary(site_path).filter_map(|p| map.get_key_value(&p)))
            .flat_map(|(site, deps)| deps.iter().map(move |dep| (site, dep)))
    }

    /// Whether `path` or an ancestor of it carries a layer-agnostic
    /// [`by_path`](Self::by_path) self-registration, stopping at a
    /// variant-selection boundary like [`ancestor_sites`](Self::ancestor_sites).
    ///
    /// A self-registration observes exactly its own path, so an ancestor holding
    /// one says only that the changed path itself is affected — which is what
    /// the caller contributes, at any depth.
    pub(super) fn has_path_ancestor(&self, path: &Path) -> bool {
        ancestors_to_variant_boundary(path).any(|p| self.by_path.contains(&p))
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

    /// Prim indices whose composition uses the layer stack `stack`, as an
    /// invalidation victim list. The victim set for an `expressionVariables`
    /// delta that demands a full per-stack resync: the stack's variable source
    /// changed, or a changed name is one of its own sublayer dependencies (C++
    /// resyncs every prim using the layer stack in both cases). The root
    /// stack's users are every cached prim — [`by_stack`](Self::by_stack)
    /// leaves it unrecorded — named as the single pseudo-root entry, whose
    /// subtree drop is the whole cache.
    pub(super) fn prims_for_stack(&self, stack: LayerStackId) -> Vec<Path> {
        if stack == LayerStackId::ROOT {
            return vec![Path::abs_root()];
        }
        keyed_prims(&self.by_stack, &stack)
    }

    /// Prim indices whose composition resolved a reference or payload target
    /// through `layer`'s `defaultPrim`, because the arc named no prim — the
    /// victim set for an edit to that field.
    ///
    /// Layer-keyed with no ancestor or subtree walk: what was read is layer
    /// metadata, not a site, and a namespace descendant of a consumer inherits
    /// the record through its ancestral seed, so it registers here in its own
    /// right.
    pub(super) fn prims_using_default_prim(&self, layer: LayerId) -> Vec<Path> {
        keyed_prims(&self.by_default_prim, &layer)
    }

    /// Prim indices that recorded reading one of `changed` from `stack`'s
    /// composed expression variables — the targeted victim set for a variable
    /// edit that changed neither the stack's source nor its sublayer selection
    /// (C++ `PcpExpressionVariablesDependencyData` intersection).
    pub(super) fn prims_using_vars(&self, stack: LayerStackId, changed: &HashSet<String>) -> Vec<Path> {
        self.by_stack_vars
            .get(&stack)
            .into_iter()
            .flatten()
            .filter(|(_, names)| !names.is_disjoint(changed))
            .map(|(prim, _)| prim.clone())
            .collect()
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
    /// [`exact_lookup`](Self::exact_lookup) folds this in, as does the store's
    /// `lookup_with_ancestors` through
    /// [`has_path_ancestor`](Self::has_path_ancestor), so a first opinion
    /// authored at `path` reaches the prims registered there regardless of
    /// which layer carried it.
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

/// `path` and its ancestors, stopping where a variant selection ends the
/// namespace chain (C++ `Pcp_Dependencies::ForEachDependencyOnSite`, USD mode).
///
/// A variant-selection path is not a namespace child of the prim it sits under,
/// so `/Model{lod=high}/Child` depends on opinions at `/Model{lod=high}` but not
/// on those at `/Model`. The selection path is visited and then ends the walk;
/// a `site_path` that is itself one yields only itself.
fn ancestors_to_variant_boundary(path: &Path) -> impl Iterator<Item = Path> {
    let mut past_boundary = false;
    path.ancestors()
        .take_while(move |p| !mem::replace(&mut past_boundary, p.is_prim_variant_selection_path()))
}

/// The prim indices registered under `key`, as an invalidation victim list.
fn keyed_prims<K: Eq + Hash>(map: &HashMap<K, HashSet<Path>>, key: &K) -> Vec<Path> {
    map.get(key).into_iter().flatten().cloned().collect()
}

/// Drops `prim`'s registrations from a `key → prims` map and its `prim → keys`
/// reverse, leaving no empty entry behind in either.
fn retract<K: Eq + Hash>(
    forward: &mut HashMap<K, HashSet<Path>>,
    reverse: &mut HashMap<Path, HashSet<K>>,
    prim: &Path,
) {
    for key in reverse.remove(prim).into_iter().flatten() {
        if let Some(set) = forward.get_mut(&key) {
            set.remove(prim);
            if set.is_empty() {
                forward.remove(&key);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcp::LayerStackId;
    use crate::pcp::layer_graph::ExternalStack;
    use crate::pcp::mapping::MapFunction;
    use crate::pcp::prim_graph::ArcType;
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

    /// The dependent paths `ancestor_sites` reports for a site, deduplicated
    /// in first-seen order — what the table knows before any translation.
    fn dependents(deps: &Dependencies, layer: LayerId, site: &Path) -> Vec<Path> {
        let mut out: Vec<Path> = Vec::new();
        for (_, dep) in deps.ancestor_sites(layer, site) {
            if !out.contains(dep) {
                out.push(dep.clone());
            }
        }
        out
    }

    fn make_index(g: &LayerGraph, prim_path: &Path, nodes: Vec<(ArcType, LayerId, Path)>) -> PrimIndex {
        let mut idx = PrimIndex::default();
        for (arc, layer_id, node_path) in nodes {
            // The stack rooted at `layer_id` — `external_stack_id` resolves it to the
            // root or a plain instance the graph minted for each sublayer-free layer.
            // The fixture layers author no variables, so the root stack is the
            // empty context every arc carries.
            let stack = match g.external_stack_id(layer_id, LayerStackId::ROOT) {
                ExternalStack::Ready(id) => id,
                ExternalStack::Demand => panic!("no minted stack for test layer {layer_id:?}"),
            };
            let map = MapFunction::from_pair_identity(node_path.clone(), prim_path.clone());
            idx.push_node(Node::new(stack, layer_id, node_path, arc, map.clone(), map, false));
        }
        idx
    }

    /// A recorded `defaultPrim` consultation registers under the layer it named
    /// and retracts cleanly, and a layer recorded twice — one target reached by
    /// both a `references` and a `payload` arc — answers once.
    #[test]
    fn default_prim_register_remove() {
        let g = graph(2);
        let (l0, l1) = (g.all_ids()[0], g.all_ids()[1]);
        let mut deps = Dependencies::default();
        let foo = p("/Foo");
        let mut index = make_index(&g, &foo, vec![(ArcType::Root, l0, foo.clone())]);
        index.record_default_prim(l1);
        index.record_default_prim(l1);
        deps.add(&foo, &index, &g, ExprVarDeps::default());

        assert_eq!(deps.prims_using_default_prim(l1), vec![foo.clone()]);
        assert!(deps.prims_using_default_prim(l0).is_empty(), "only the layer consulted");

        deps.remove(&foo);
        assert!(deps.prims_using_default_prim(l1).is_empty());
        assert!(deps.by_default_prim.is_empty(), "the forward map keeps no empty entry");
        assert!(deps.by_prim_default_prim.is_empty(), "nor the reverse one");
    }

    /// The report a `defaultPrim` edit publishes must not fold in the
    /// layer-agnostic self-registrations: a prim cached at `/Source` that never
    /// reads the edited layer is not a dependent of that layer's `/Source`.
    #[test]
    fn ancestor_self_registration() {
        let g = graph(2);
        let (l0, l1) = (g.all_ids()[0], g.all_ids()[1]);
        let mut deps = Dependencies::default();
        let source = p("/Source");
        // A prim whose only registration is its own path, on no particular layer.
        let bystander = make_index(&g, &source, vec![(ArcType::Root, l0, source.clone())]);
        deps.add(&source, &bystander, &g, ExprVarDeps::default());
        // A prim whose graph genuinely reads `/Source` on `l1`.
        let user = p("/User");
        let reader = make_index(&g, &user, vec![(ArcType::Reference, l1, source.clone())]);
        deps.add(&user, &reader, &g, ExprVarDeps::default());

        assert_eq!(
            dependents(&deps, l1, &source),
            vec![user.clone()],
            "only the graph reader registers a site here"
        );
        assert!(
            deps.has_path_ancestor(&source),
            "the bystander's self-registration is what the invalidation lookup folds in"
        );
    }

    #[test]
    fn empty_index_self_path() {
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
        deps.add(&foo, &index, &g, ExprVarDeps::default());
        assert!(
            dependents(&deps, l0, &foo).is_empty(),
            "the self-Root edge registers no site"
        );
        assert!(
            deps.has_path_ancestor(&foo),
            "the layer-agnostic entry covers it instead"
        );
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
        deps.add(&here, &index, &g, ExprVarDeps::default());
        assert_eq!(dependents(&deps, l1, &there), vec![here.clone()]);
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
            ExprVarDeps::default(),
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
            ExprVarDeps::default(),
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

    /// A change below an arc's site reaches the dependent through the ancestor
    /// walk: `/A/B` inheriting `/X/Y` is reported for a change at
    /// `/X/Y/Child`. Which composed path it is affected at is the join's
    /// question, not the table's.
    #[test]
    fn ancestor_walk_pairs() {
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
        deps.add(&here, &index, &g, ExprVarDeps::default());
        assert_eq!(dependents(&deps, l0, &p("/X/Y/Child")), vec![here.clone()]);
        // The site itself reaches the dependent too.
        assert_eq!(dependents(&deps, l0, &arc_site), vec![here]);
    }

    /// A variant selection ends the namespace chain: it is not a child of the
    /// prim it sits under, so a change beneath `/Model{lod=high}` must not reach
    /// a dependent registered on `/Model` (C++ `ForEachDependencyOnSite`, USD
    /// mode). The selection path itself is still visited.
    #[test]
    fn variant_stops_ancestors() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let mut deps = Dependencies::default();
        let plain = p("/Plain");
        let sel = p("/Sel");
        let model = p("/Model");
        let variant = p("/Model{lod=high}");
        deps.add(
            &plain,
            &make_index(&g, &plain, vec![(ArcType::Reference, l0, model.clone())]),
            &g,
            ExprVarDeps::default(),
        );
        deps.add(
            &sel,
            &make_index(&g, &sel, vec![(ArcType::Reference, l0, variant.clone())]),
            &g,
            ExprVarDeps::default(),
        );

        let under = p("/Model{lod=high}Child");
        assert_eq!(
            dependents(&deps, l0, &under),
            vec![sel.clone()],
            "the walk stops at the selection, so /Model's dependent is not reached"
        );
        assert_eq!(
            dependents(&deps, l0, &variant),
            vec![sel],
            "a site that is itself a selection reaches only its own dependents"
        );
        assert_eq!(
            dependents(&deps, l0, &p("/Model/Child")),
            vec![plain],
            "an ordinary child still walks up to /Model"
        );
    }

    /// The same boundary through the layer-agnostic channel: a self-registered
    /// `/Model` must not be folded in for a change beneath a variant selection.
    #[test]
    fn variant_stops_by_path() {
        let g = graph(1);
        let l0 = g.all_ids()[0];
        let mut deps = Dependencies::default();
        let model = p("/Model");
        deps.add(
            &model,
            &make_index(&g, &model, vec![(ArcType::Root, l0, model.clone())]),
            &g,
            ExprVarDeps::default(),
        );
        assert!(deps.has_path_ancestor(&p("/Model/Child")));
        assert!(
            !deps.has_path_ancestor(&p("/Model{lod=high}Child")),
            "the selection ends the chain before /Model's self-registration"
        );
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
        deps.add(
            &a,
            &make_index(&g, &a, vec![(ArcType::Reference, l0, xy.clone())]),
            &g,
            ExprVarDeps::default(),
        );
        deps.add(
            &b,
            &make_index(&g, &b, vec![(ArcType::Reference, l0, xy_child.clone())]),
            &g,
            ExprVarDeps::default(),
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
            ExprVarDeps::default(),
        );
        assert!(!dependents(&deps, l0, &there).is_empty());
        deps.remove(&here);
        assert!(dependents(&deps, l0, &there).is_empty());
        assert!(!deps.has_path_ancestor(&here), "the self-registration goes too");
    }
}
