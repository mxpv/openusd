//! Composition graph: lazily-built cache of per-prim composition indices.
//!
//! The [`Cache`] is the primary interface between [`Stage`](crate::Stage)
//! and the composition engine. It caches [`PrimIndex`] results alongside the
//! [`CompositionContext`] that flows from parent prims to children, so ancestor
//! composition is never recomputed.

use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{LayerData, Path, SpecType, Value};

use super::index::{ArcType, CompositionContext, Node, PrimIndex, SublayerStacks};
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
}

impl Cache {
    /// Creates a new composition graph for the given layer stack.
    pub fn new(layers: Vec<LayerData>, identifiers: Vec<String>) -> Self {
        let sublayer_stacks = super::index::precompute_sublayer_stacks(&layers, &identifiers);
        Self {
            layers,
            identifiers,
            cache: HashMap::new(),
            sublayer_stacks,
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
    /// union with strongest-first ordering.
    pub fn prim_children(&mut self, path: &Path) -> Result<Vec<String>> {
        self.composed_children(path, ChildrenKey::PrimChildren)
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

        // Look up parent's context (available if parent was composed first).
        let parent_ctx = path
            .parent()
            .and_then(|p| self.cache.get(&p))
            .map(|e| e.child_context.clone())
            .unwrap_or_default();

        match PrimIndex::build_with_context(
            path,
            &self.layers,
            &self.identifiers,
            &parent_ctx,
            &self.sublayer_stacks,
        ) {
            Ok(mut index) => {
                // When no layer has a direct spec at the composed path, the
                // prim may still exist through ancestor composition arcs
                // (inherit, specialize, reference, etc.). Propagate specs from
                // the parent's nodes: for each parent node, check if a child
                // spec exists at `parent_node.path / child_name` in that layer.
                if index.is_empty() {
                    if let Some(name) = path.name() {
                        self.propagate_parent_specs(path, name, &mut index);
                    }
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
    /// it as an implied node, carrying the parent node's arc type and namespace
    /// mapping adjusted for the child.
    fn propagate_parent_specs(&self, child_path: &Path, child_name: &str, index: &mut PrimIndex) {
        let Some(parent_path) = child_path.parent() else {
            return;
        };
        let Some(parent_entry) = self.cache.get(&parent_path) else {
            return;
        };

        for parent_node in parent_entry.index.nodes() {
            // Skip Root nodes — they're already checked by the L phase.
            if parent_node.arc == ArcType::Root {
                continue;
            }

            let Ok(node_child_path) = parent_node.path.append_path(child_name) else {
                continue;
            };

            // Check all layers for a spec at this node-relative child path.
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
    }

    /// Merges a children field across all nodes in the prim index.
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

        Ok(result)
    }
}
