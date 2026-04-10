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

use super::index::{CompositionContext, PrimIndex, SublayerStacks};

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
    /// exists in any layer contributing to the owning prim's composition.
    pub fn has_spec(&mut self, path: &Path) -> bool {
        if path.is_property_path() {
            let prim_path = path.prim_path();
            let prop_suffix = &path.as_str()[prim_path.as_str().len()..];
            self.ensure_index(&prim_path);
            let Some(entry) = self.cache.get(&prim_path) else {
                return false;
            };
            for node in entry.index.nodes() {
                let prop_path = format!("{}{prop_suffix}", node.path);
                if let Ok(p) = Path::new(&prop_path) {
                    if self.layers[node.layer_index].has_spec(&p) {
                        return true;
                    }
                }
            }
            false
        } else {
            self.ensure_index(path);
            self.cache.get(path).is_some_and(|e| !e.index.is_empty())
        }
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub fn spec_type(&mut self, path: &Path) -> Option<SpecType> {
        self.ensure_index(path);
        let entry = self.cache.get(path)?;
        for node in entry.index.nodes() {
            if let Some(ty) = self.layers[node.layer_index].spec_type(&node.path) {
                return Some(ty);
            }
        }
        None
    }

    /// Resolves a field value from the strongest opinion across all composition nodes.
    pub fn resolve_field(&mut self, path: &Path, field: &str) -> Result<Option<Value>> {
        if path.is_property_path() {
            let prim_path = path.prim_path();
            let prop_suffix = &path.as_str()[prim_path.as_str().len()..];
            self.ensure_index(&prim_path);
            let entry = &self.cache[&prim_path];
            entry.index.resolve_field(field, &self.layers, Some(prop_suffix))
        } else {
            self.ensure_index(path);
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
    fn ensure_index(&mut self, path: &Path) {
        if self.cache.contains_key(path) {
            return;
        }

        // Look up parent's context (available if parent was composed first).
        let parent_ctx = path
            .parent()
            .and_then(|p| self.cache.get(&p))
            .map(|e| e.child_context.clone())
            .unwrap_or_default();

        let index = PrimIndex::build_with_context(
            path,
            &self.layers,
            &self.identifiers,
            &parent_ctx,
            &self.sublayer_stacks,
        );
        let child_context = index.context_for_children(path, &self.layers, &parent_ctx);

        self.cache.insert(path.clone(), CachedPrim { index, child_context });
    }

    /// Merges a children field across all nodes in the prim index.
    fn composed_children(&mut self, path: &Path, children_field: ChildrenKey) -> Result<Vec<String>> {
        self.ensure_index(path);
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
