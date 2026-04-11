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
use super::map_function::MapFunction;

/// Cached entry for a composed prim: its index and the context its children need.
struct CachedPrim {
    index: PrimIndex,
    child_context: CompositionContext,
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
    layers: Vec<LayerData>,
    identifiers: Vec<String>,
    cache: HashMap<Path, CachedPrim>,
    /// Precomputed sublayer stacks shared by all per-prim builds.
    sublayer_stacks: SublayerStacks,
    /// Per-layer relocates: `layerRelocates` extracted from each layer's pseudoroot.
    layer_relocates: HashMap<usize, Vec<(Path, Path)>>,
}

impl Cache {
    /// Creates a new composition graph for the given layer stack.
    pub fn new(layers: Vec<LayerData>, identifiers: Vec<String>) -> Self {
        let sublayer_stacks = super::index::precompute_sublayer_stacks(&layers, &identifiers);
        let layer_relocates = collect_layer_relocates(&layers);
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
                apply_relocates(path, &mut children, &relocates);
            }
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

    /// Returns a snapshot of all cached prim indices for passing to
    /// `PrimIndex::build_with_cache`.
    fn index_snapshot(&self) -> HashMap<Path, PrimIndex> {
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
        PrimIndex::build_with_context(path, &self.layers, &self.identifiers, &ctx, &self.sublayer_stacks)
            .map(|idx| idx.nodes().to_vec())
            .unwrap_or_default()
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

    // ------------------------------------------------------------------
    // Relocates
    // ------------------------------------------------------------------

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
    fn find_source_path(&self, composed_path: &Path) -> Option<Path> {
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
                let has_spec = self.layers.iter().any(|l| l.has_spec(&deeper));
                if has_spec {
                    return Some(deeper);
                }
            }
        }
        result
    }

    /// Ensures a path and all its ancestors are cached (built on the fly if needed).
    fn precache_path(&mut self, path: &Path) {
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
        let Ok(parent_index) = PrimIndex::build_with_context(
            &parent,
            &self.layers,
            &self.identifiers,
            &grandparent_ctx,
            &self.sublayer_stacks,
        ) else {
            return CompositionContext::default();
        };
        parent_index.context_for_children(&self.layers, &grandparent_ctx)
    }

    /// Adds relocate nodes to a prim index for a relocated prim.
    ///
    /// Builds a full composition index for the source path and merges its
    /// nodes. The source index captures all opinions (through references,
    /// variants, inherits) including those propagated via
    /// [`propagate_parent_specs`](Self::propagate_parent_specs). For each
    /// inherit/specialize node in the source parent, also checks the class
    /// child path for additional specs.
    fn add_relocate_nodes(&self, composed_path: &Path, index: &mut PrimIndex) {
        let Some(source_path) = self.find_source_path(composed_path) else {
            return;
        };
        let source_ctx = self.build_source_context(&source_path);
        let source_cache: HashMap<Path, PrimIndex> = self.index_snapshot();
        let Ok(source_index) = PrimIndex::build_with_cache(
            &source_path,
            &self.layers,
            &self.identifiers,
            &source_ctx,
            &self.sublayer_stacks,
            &source_cache,
        ) else {
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
                    PrimIndex::build_with_cache(
                        &source_parent,
                        &self.layers,
                        &self.identifiers,
                        &ctx,
                        &self.sublayer_stacks,
                        &index_cache,
                    )
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
                    for li in 0..self.layers.len() {
                        if self.layers[li].has_spec(&child_path) {
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
                    PrimIndex::build_with_context(
                        &source_parent,
                        &self.layers,
                        &self.identifiers,
                        &ctx,
                        &self.sublayer_stacks,
                    )
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
                    let Ok(class_index) = PrimIndex::build_with_cache(
                        &class_child,
                        &self.layers,
                        &self.identifiers,
                        &class_ctx,
                        &self.sublayer_stacks,
                        &class_cache,
                    ) else {
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
        let Ok(source_index) = PrimIndex::build_with_cache(
            source_path,
            &self.layers,
            &self.identifiers,
            &source_ctx,
            &self.sublayer_stacks,
            &source_cache,
        ) else {
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
                        for li in 0..self.layers.len() {
                            if self.layers[li].has_spec(&child_path) {
                                Self::push_relocate_node(index, li, &child_path, composed_path);
                            }
                        }
                    }
                }
            }
        }
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
    fn ensure_index(&mut self, path: &Path) -> Result<()> {
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

// ---------------------------------------------------------------------------
// Free functions
// ---------------------------------------------------------------------------

/// Extracts `layerRelocates` from every layer's pseudoroot.
fn collect_layer_relocates(layers: &[LayerData]) -> HashMap<usize, Vec<(Path, Path)>> {
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
