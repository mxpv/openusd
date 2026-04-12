//! Composition graph: lazily-built cache of per-prim composition indices.
//!
//! The [`Cache`] is the primary interface between [`Stage`](crate::Stage)
//! and the composition engine. It caches [`PrimIndex`] results alongside the
//! [`CompositionContext`] that flows from parent prims to children, so ancestor
//! composition is never recomputed.
//!
//! Relocates (`layerRelocates`) are handled at the cache level: source paths
//! are resolved, full composition indices are built for them, and the results
//! are merged as `ArcType::Relocate` nodes. The child name lists are
//! adjusted to hide relocated sources and expose targets.

use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{LayerData, Path, SpecType, Value};

use super::index::{AncestorArc, ArcType, CompositionContext, Node, PrimIndex, SublayerStacks};
use super::mapping::MapFunction;

/// Cached entry for a composed prim: its index and the context its children need.
pub(super) struct CachedPrim {
    pub(super) index: PrimIndex,
    pub(super) child_context: CompositionContext,
}

/// Lazily-built composition graph.
///
/// Caches per-prim composition indices and contexts. When a prim is queried
/// for the first time, its index is built using the parent's cached context
/// (if available). During depth-first traversal, parents are always composed
/// before children, so the context chain is always populated.
///
/// All public methods return `Result` — a [`pcp::Error`](super::Error) is
/// returned when composition fails. The caller ([`Stage`](crate::Stage))
/// decides whether to skip or abort via its error handler.
pub struct Cache {
    pub(super) layers: Vec<LayerData>,
    pub(super) identifiers: Vec<String>,
    pub(super) cache: HashMap<Path, CachedPrim>,
    /// Precomputed sublayer stacks shared by all per-prim builds.
    pub(super) sublayer_stacks: SublayerStacks,
    /// Per-layer relocates: `layerRelocates` extracted from each layer's pseudoroot.
    pub(super) layer_relocates: HashMap<usize, Vec<(Path, Path)>>,
}

impl Cache {
    /// Creates a new composition graph for the given layer stack.
    pub fn new(layers: Vec<LayerData>, identifiers: Vec<String>) -> Self {
        let sublayer_stacks = super::index::precompute_sublayer_stacks(&layers, &identifiers);
        let layer_relocates = super::rel::collect_layer_relocates(&layers);
        Self {
            layers,
            identifiers,
            cache: HashMap::new(),
            sublayer_stacks,
            layer_relocates,
        }
    }

    /// Returns the number of layers in the stage.
    pub fn layer_count(&self) -> usize {
        self.layers.len()
    }

    /// Returns the layer identifiers in strength order (root first).
    pub fn layer_identifiers(&self) -> &[String] {
        &self.identifiers
    }

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    pub fn has_spec(&mut self, path: &Path) -> Result<bool> {
        if path.is_property_path() {
            let prim_path = path.prim_path();
            let prop_suffix = &path.as_str()[prim_path.as_str().len()..];
            self.ensure_index(&prim_path)?;
            let Some(entry) = self.cache.get(&prim_path) else {
                return Ok(false);
            };
            for node in entry.index.nodes() {
                let prop_path = format!("{}{prop_suffix}", node.path);
                if let Ok(p) = Path::new(&prop_path) {
                    if self.layers[node.layer_index].has_spec(&p) {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        } else {
            self.ensure_index(path)?;
            Ok(self.cache.get(path).is_some_and(|e| !e.index.is_empty()))
        }
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub fn spec_type(&mut self, path: &Path) -> Result<Option<SpecType>> {
        self.ensure_index(path)?;
        let Some(entry) = self.cache.get(path) else {
            return Ok(None);
        };
        for node in entry.index.nodes() {
            if let Some(ty) = self.layers[node.layer_index].spec_type(&node.path) {
                return Ok(Some(ty));
            }
        }
        Ok(None)
    }

    /// Resolves a field value from the strongest opinion across all composition nodes.
    pub fn resolve_field(&mut self, path: &Path, field: &str) -> Result<Option<Value>> {
        if path.is_property_path() {
            let prim_path = path.prim_path();
            let prop_suffix = &path.as_str()[prim_path.as_str().len()..];
            self.ensure_index(&prim_path)?;
            let entry = &self.cache[&prim_path];
            entry.index.resolve_field(field, &self.layers, Some(prop_suffix))
        } else {
            self.ensure_index(path)?;
            let entry = &self.cache[path];
            entry.index.resolve_field(field, &self.layers, None)
        }
    }

    /// Returns the composed list of child names for a prim path.
    ///
    /// Merges the children field across all composition nodes, returning the
    /// union with strongest-first ordering. When relocates are present,
    /// source children are hidden and target children are added.
    pub fn prim_children(&mut self, path: &Path) -> Result<Vec<String>> {
        let mut children = self.composed_children(path, ChildrenKey::PrimChildren)?;

        if !self.layer_relocates.is_empty() {
            self.apply_relocates_to_children(path, &mut children);
        }

        Ok(children)
    }

    /// Returns the composed list of property names for a prim path.
    pub fn prim_properties(&mut self, path: &Path) -> Result<Vec<String>> {
        self.composed_children(path, ChildrenKey::PropertyChildren)
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    pub fn default_prim(&self) -> Option<String> {
        let root = Path::abs_root();
        let value = self.layers.first()?.get(&root, FieldKey::DefaultPrim.as_str()).ok()?;
        match value.into_owned() {
            Value::Token(s) | Value::String(s) => Some(s),
            _ => None,
        }
    }

    /// Collects ancestor arcs from all cached ancestors of `path`.
    fn collect_ancestor_arcs(&self, path: &Path) -> Vec<AncestorArc> {
        let mut arcs = Vec::new();
        let mut p = Some(path.clone());
        while let Some(pp) = p {
            if let Some(e) = self.cache.get(&pp) {
                for a in &e.child_context.ancestor_arcs {
                    arcs.push(a.clone());
                }
            }
            p = pp.parent();
        }
        arcs
    }

    /// Pre-caches inherit/specialize targets declared in the prim's layer
    /// data. Reads inherit paths from each layer, resolves them to composed
    /// namespace using ancestor arcs, and ensures those targets are cached.
    fn precache_inherit_targets(&mut self, path: &Path) {
        let Some(parent) = path.parent() else {
            return;
        };
        let Some(parent_entry) = self.cache.get(&parent) else {
            return;
        };

        let ancestor_arcs = self.collect_ancestor_arcs(&parent);

        // Scan both the parent's nodes and the prim's own specs (if any) for
        // inherit/specialize targets.
        let mut nodes_to_scan: Vec<(Path, usize)> = Vec::new();
        for node in parent_entry.index.nodes() {
            nodes_to_scan.push((node.path.clone(), node.layer_index));
            // Also check the node's child path (the prim itself in this node's namespace).
            if let Some(name) = path.name() {
                if let Ok(child_in_node) = node.path.append_path(name) {
                    nodes_to_scan.push((child_in_node, node.layer_index));
                }
            }
        }
        // Also check the prim's own path in all layers.
        for li in 0..self.layers.len() {
            if self.layers[li].has_spec(path) {
                nodes_to_scan.push((path.clone(), li));
            }
        }

        let mut targets_to_cache = Vec::new();
        for (scan_path, scan_layer) in &nodes_to_scan {
            for field in [FieldKey::InheritPaths, FieldKey::Specializes] {
                let Ok(val) = self.layers[*scan_layer].get(scan_path, field.as_str()) else {
                    continue;
                };
                let Value::PathListOp(list_op) = val.into_owned() else {
                    continue;
                };
                for target in &list_op.flatten() {
                    let raw = parent.make_absolute(target);
                    // Try composed-namespace versions via ancestor arcs.
                    for a in &ancestor_arcs {
                        if let Some(composed) = a.map.map_source_to_target(&raw) {
                            if composed != raw && !targets_to_cache.contains(&composed) {
                                targets_to_cache.push(composed);
                            }
                        }
                    }
                    if !targets_to_cache.contains(&raw) {
                        targets_to_cache.push(raw);
                    }
                }
            }
        }

        for target in targets_to_cache {
            self.precache_path(&target);
            // Recursively precache the target's own inherit targets.
            if self.cache.contains_key(&target) {
                self.precache_inherit_targets(&target);
            }
        }
    }

    // ------------------------------------------------------------------
    // Core composition
    // ------------------------------------------------------------------

    /// Ensures the prim index for `path` is built and cached.
    ///
    /// When LIVRPS composition produces an empty index (no layer has a direct
    /// spec at the composed path), parent composition nodes are checked for
    /// child specs at their respective paths. This handles prims that only
    /// exist through ancestor inherit, specialize, or reference arcs.
    pub(super) fn ensure_index(&mut self, path: &Path) -> Result<()> {
        if self.cache.contains_key(path) {
            return Ok(());
        }

        // Pre-cache inherit/specialize targets so the index builder can
        // find them. This handles the timing issue where a target prim is
        // in a sibling subtree that hasn't been traversed yet.
        self.precache_inherit_targets(path);

        let parent_ctx = path
            .parent()
            .and_then(|p| self.cache.get(&p))
            .map(|e| e.child_context.clone())
            .unwrap_or_default();

        // Provide the composition cache to the index builder so that
        // merge_full_index can use fully-composed indices for inherit/
        // specialize targets instead of building them from scratch.
        let index_cache: HashMap<Path, PrimIndex> = self.index_snapshot();

        match PrimIndex::build_with_cache(
            path,
            &self.layers,
            &self.identifiers,
            &parent_ctx,
            &self.sublayer_stacks,
            &index_cache,
        ) {
            Ok(mut index) => {
                // Propagate specs from parent nodes for inherit-only children.
                if index.is_empty() {
                    if let Some(name) = path.name() {
                        self.propagate_parent_specs(path, name, &mut index);
                    }
                }

                // For relocated prims, merge source path opinions.
                if !self.layer_relocates.is_empty() {
                    if let Some(source) = self.find_source_path(path) {
                        self.precache_path(&source);
                    }
                    self.add_relocate_nodes(path, &mut index);
                }

                let child_context = index.context_for_children(&self.layers, &parent_ctx);
                self.cache.insert(path.clone(), CachedPrim { index, child_context });
                Ok(())
            }
            Err(e) => Err(e.into()),
        }
    }

    /// Propagates child specs from the parent's composition nodes.
    ///
    /// When a child prim has no direct spec in any layer, it may exist through
    /// ancestor composition arcs (e.g. a child of an inherited class that has
    /// no local override). For each non-Root node in the parent's index, check
    /// if the node's layer has a spec at `node.path / child_name`. If so, add
    /// it as an implied node.
    ///
    /// Also scans the parent's layer data for inherit/specialize targets whose
    /// child may have specs in other layers. This covers cases where the index
    /// builder's `merge_full_index` produced empty indices for inherit targets
    /// (due to using default composition context).
    fn propagate_parent_specs(&self, child_path: &Path, child_name: &str, index: &mut PrimIndex) {
        let Some(parent_path) = child_path.parent() else {
            return;
        };
        let Some(parent_entry) = self.cache.get(&parent_path) else {
            return;
        };

        // Phase 1: Check non-Root nodes from the parent's index.
        for parent_node in parent_entry.index.nodes() {
            if parent_node.arc == ArcType::Root {
                continue;
            }

            let Ok(node_child_path) = parent_node.path.append_path(child_name) else {
                continue;
            };

            for li in 0..self.layers.len() {
                if self.layers[li].has_spec(&node_child_path) {
                    let map = MapFunction::from_pair(node_child_path.clone(), child_path.clone());
                    index.push_node(Node {
                        layer_index: li,
                        path: node_child_path.clone(),
                        arc: parent_node.arc,
                        map_to_parent: map.clone(),
                        map_to_root: map,
                    });
                }
            }
        }

        // Phase 2: Use ancestor arcs from all cached ancestors to find
        // specs at alternative namespace paths. This covers cases where
        // merge_full_index produced empty indices for inherit targets
        // (due to building with default context that misses ancestor arcs).
        if index.is_empty() {
            let mut all_ancestor_arcs = parent_entry.child_context.ancestor_arcs.clone();
            let mut ap = parent_path.clone();
            while let Some(pp) = ap.parent() {
                if let Some(e) = self.cache.get(&pp) {
                    for a in &e.child_context.ancestor_arcs {
                        if !all_ancestor_arcs.iter().any(|x| x.map == a.map) {
                            all_ancestor_arcs.push(a.clone());
                        }
                    }
                }
                ap = pp;
            }
            for ancestor in &all_ancestor_arcs {
                let Some(alt_path) = ancestor.map.map_target_to_source(child_path) else {
                    continue;
                };
                if alt_path == *child_path {
                    continue;
                }
                for li in 0..self.layers.len() {
                    if self.layers[li].has_spec(&alt_path) {
                        let map = MapFunction::from_pair(alt_path.clone(), child_path.clone());
                        index.push_node(Node {
                            layer_index: li,
                            path: alt_path.clone(),
                            arc: ancestor.arc,
                            map_to_parent: map.clone(),
                            map_to_root: map,
                        });
                    }
                }
            }
        }

        // Phase 3: Read inherit/specialize targets from the parent's layer
        // data and check their child paths in all namespace variants. This
        // handles the case where the inherit target's index was empty
        // (merge_full_index with default context) and ancestor_arcs don't
        // have the mapping.
        if index.is_empty() {
            let mut grandparent_arcs = Vec::new();
            let mut p = parent_path.parent();
            while let Some(pp) = p {
                if let Some(entry) = self.cache.get(&pp) {
                    for a in &entry.child_context.ancestor_arcs {
                        grandparent_arcs.push(a.clone());
                    }
                }
                p = pp.parent();
            }

            for parent_node in parent_entry.index.nodes() {
                for field in [FieldKey::InheritPaths, FieldKey::Specializes] {
                    let arc = if field.as_str() == FieldKey::InheritPaths.as_str() {
                        ArcType::Inherit
                    } else {
                        ArcType::Specialize
                    };
                    let Ok(val) = self.layers[parent_node.layer_index].get(&parent_node.path, field.as_str()) else {
                        continue;
                    };
                    let Value::PathListOp(list_op) = val.into_owned() else {
                        continue;
                    };
                    for target in &list_op.flatten() {
                        let resolved = parent_path.make_absolute(target);
                        let Ok(target_child) = resolved.append_path(child_name) else {
                            continue;
                        };
                        // Check composed path + all grandparent ancestor remappings.
                        let mut paths_to_check = vec![target_child.clone()];
                        for ga in &grandparent_arcs {
                            if let Some(alt) = ga.map.map_target_to_source(&target_child) {
                                if alt != target_child && !paths_to_check.contains(&alt) {
                                    paths_to_check.push(alt);
                                }
                            }
                        }
                        for check in &paths_to_check {
                            for li in 0..self.layers.len() {
                                if self.layers[li].has_spec(check) {
                                    let map = MapFunction::from_pair(check.clone(), child_path.clone());
                                    index.push_node(Node {
                                        layer_index: li,
                                        path: check.clone(),
                                        arc,
                                        map_to_parent: map.clone(),
                                        map_to_root: map,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Merges a children field across all nodes in the prim index.
    ///
    /// Also discovers children from inherit/specialize targets declared in
    /// the layer data when those targets weren't successfully merged during
    /// index building. This bridges the gap between the index builder's
    /// `merge_full_index` (which uses default context) and the full
    /// composition needed to discover class children.
    fn composed_children(&mut self, path: &Path, children_field: ChildrenKey) -> Result<Vec<String>> {
        self.ensure_index(path)?;
        let entry = &self.cache[path];
        let mut result: Vec<String> = Vec::new();

        for node in entry.index.nodes() {
            if let Ok(value) = self.layers[node.layer_index].get(&node.path, children_field.as_str()) {
                if let Value::TokenVec(names) = value.into_owned() {
                    for name in names {
                        if !result.contains(&name) {
                            result.push(name);
                        }
                    }
                }
            }
        }

        // For prim children, also check inherit/specialize targets from each
        // node's layer data. The inherit might not have been merged into the
        // index (empty target), but the target's children should still appear.
        if matches!(children_field, ChildrenKey::PrimChildren) {
            self.add_inherited_children(path, &mut result);
        }

        Ok(result)
    }

    /// Adds children from inherit/specialize targets that weren't merged
    /// during index building. Follows inherit chains recursively.
    fn add_inherited_children(&self, path: &Path, result: &mut Vec<String>) {
        let mut visited = Vec::new();
        self.add_inherited_children_inner(path, result, &mut visited);
    }

    fn add_inherited_children_inner(&self, path: &Path, result: &mut Vec<String>, visited: &mut Vec<Path>) {
        if visited.contains(path) {
            return;
        }
        visited.push(path.clone());

        let Some(entry) = self.cache.get(path) else {
            return;
        };

        let ancestor_arcs = self.collect_ancestor_arcs(path);

        let nodes: Vec<Node> = entry.index.nodes().to_vec();
        for node in &nodes {
            for field in [FieldKey::InheritPaths, FieldKey::Specializes] {
                let Ok(val) = self.layers[node.layer_index].get(&node.path, field.as_str()) else {
                    continue;
                };
                let Value::PathListOp(list_op) = val.into_owned() else {
                    continue;
                };
                for target in &list_op.flatten() {
                    let raw = path.make_absolute(target);

                    // Build namespace-remapped variants of the target path.
                    let mut targets = vec![raw.clone()];
                    for a in &ancestor_arcs {
                        if let Some(composed) = a.map.map_source_to_target(&raw) {
                            if composed != raw && !targets.contains(&composed) {
                                targets.push(composed);
                            }
                        }
                        if let Some(alt) = a.map.map_target_to_source(&raw) {
                            if alt != raw && !targets.contains(&alt) {
                                targets.push(alt);
                            }
                        }
                    }

                    // Add children from inherit targets — check both cached
                    // entries and raw layer data (for uncached targets).
                    for tgt in &targets {
                        if let Some(tgt_entry) = self.cache.get(tgt) {
                            for tgt_node in tgt_entry.index.nodes() {
                                if let Ok(val) = self.layers[tgt_node.layer_index]
                                    .get(&tgt_node.path, ChildrenKey::PrimChildren.as_str())
                                {
                                    if let Value::TokenVec(names) = val.into_owned() {
                                        for name in names {
                                            if !result.contains(&name) {
                                                result.push(name);
                                            }
                                        }
                                    }
                                }
                            }
                            self.add_inherited_children_inner(tgt, result, visited);
                        }
                        self.find_children_in_layers(tgt, result, &ancestor_arcs, visited);
                    }

                    for tgt in &targets {
                        for li in 0..self.layers.len() {
                            if let Ok(val) = self.layers[li].get(tgt, ChildrenKey::PrimChildren.as_str()) {
                                if let Value::TokenVec(names) = val.into_owned() {
                                    for name in names {
                                        if !result.contains(&name) {
                                            result.push(name);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Finds children at a path by checking layer data, recursively following
    /// inherit/specialize chains. Used when the target isn't cached and its
    /// children come from an inherit chain in the layer data.
    fn find_children_in_layers(
        &self,
        path: &Path,
        result: &mut Vec<String>,
        ancestor_arcs: &[AncestorArc],
        visited: &mut Vec<Path>,
    ) {
        if visited.contains(path) {
            return;
        }
        visited.push(path.clone());

        // Direct children at this path in any layer.
        for li in 0..self.layers.len() {
            if let Ok(val) = self.layers[li].get(path, ChildrenKey::PrimChildren.as_str()) {
                if let Value::TokenVec(names) = val.into_owned() {
                    for name in names {
                        if !result.contains(&name) {
                            result.push(name);
                        }
                    }
                }
            }
        }

        // If no direct children found, follow the path's own inherit targets.
        if result.is_empty() {
            for li in 0..self.layers.len() {
                for field in [FieldKey::InheritPaths, FieldKey::Specializes] {
                    let Ok(val) = self.layers[li].get(path, field.as_str()) else {
                        continue;
                    };
                    let Value::PathListOp(list_op) = val.into_owned() else {
                        continue;
                    };
                    for inh_target in &list_op.flatten() {
                        let resolved = path.make_absolute(inh_target);
                        let mut paths = vec![resolved.clone()];
                        for a in ancestor_arcs {
                            if let Some(alt) = a.map.map_source_to_target(&resolved) {
                                if alt != resolved && !paths.contains(&alt) {
                                    paths.push(alt);
                                }
                            }
                            if let Some(alt) = a.map.map_target_to_source(&resolved) {
                                if alt != resolved && !paths.contains(&alt) {
                                    paths.push(alt);
                                }
                            }
                        }
                        for p in &paths {
                            self.find_children_in_layers(p, result, ancestor_arcs, visited);
                        }
                    }
                }
            }
        }
    }
}
