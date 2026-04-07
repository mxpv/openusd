//! Prim composition index.
//!
//! A [`PrimIndex`] records, for a single composed prim, the ordered list of
//! layer specs that contribute opinions — from strongest to weakest. The
//! ordering follows USD's LIVERPS strength rules:
//!
//! 1. **L**ocal opinions (root layer stack / sublayers)
//! 2. **I**nherits
//! 3. **V**ariant sets
//! 4. **R**eferences
//! 5. **P**ayloads
//! 6. **S**pecializes
//!
//! See <https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html>

use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::schema::FieldKey;
use crate::sdf::{AbstractData, LayerData, ListOp, Path, Payload, Reference, Value};

/// The type of composition arc that introduced a [`Node`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArcType {
    /// Direct opinions from the root layer stack (sublayers).
    Root,
    /// Inherited from a class prim.
    Inherit,
    /// Contributed by a selected variant.
    Variant,
    /// Brought in via a reference arc.
    Reference,
    /// Brought in via a payload arc.
    Payload,
    /// Contributed by a specializes arc (weakest).
    Specialize,
}

/// A single contributing spec in the composition index.
///
/// Each node points to a specific layer (by index) and the path within that
/// layer where the prim's opinions live. The path may differ from the
/// composed prim path when namespace remapping is involved (e.g. references).
#[derive(Debug, Clone)]
pub struct Node {
    /// Index into the stage's layer list.
    pub layer_index: usize,
    /// The path within that layer (may differ from composed path due to remapping).
    pub path: Path,
    /// The composition arc that introduced this node.
    #[allow(dead_code)] // Part of the public data model; read by tests and downstream users.
    pub arc: ArcType,
}

/// Composition index for a single prim.
///
/// Contains an ordered list of [`Node`]s from strongest to weakest.
/// Value resolution walks this list and takes the first opinion found.
#[derive(Debug, Clone)]
pub struct PrimIndex {
    /// Nodes ordered from strongest to weakest.
    pub nodes: Vec<Node>,
}

impl PrimIndex {
    /// Returns `true` if no layers contribute opinions for this prim.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Builds a prim index for the given path across the layer stack.
    ///
    /// Follows LIVERPS ordering:
    /// Local (sublayers) > Inherits > Variants > References > Payloads > Specializes.
    pub(crate) fn build(path: &Path, layers: &[LayerData], identifiers: &[String]) -> Self {
        let mut nodes = Vec::new();

        // L — Root / sublayer opinions: check each layer in strength order.
        for (i, layer) in layers.iter().enumerate() {
            if layer.has_spec(path) {
                nodes.push(Node {
                    layer_index: i,
                    path: path.clone(),
                    arc: ArcType::Root,
                });
            }
        }

        // I — Inherits: compose PathListOp across root nodes, then add nodes
        // from the inherited prims within the same layer stack.
        let inherits = compose_arc_list::<Path>(&nodes, FieldKey::InheritPaths, layers);
        for inherit_path in &inherits {
            for (i, layer) in layers.iter().enumerate() {
                add_remapped_nodes(layer.as_ref(), i, path, inherit_path, ArcType::Inherit, &mut nodes);
            }
        }

        // V — Variants: resolve variant selection (first opinion wins), then
        // add specs from the selected variant path in each layer.
        let selections = resolve_variant_selections(&nodes, layers);
        for (set_name, selection) in &selections {
            let variant_path = path.append_variant_selection(set_name, selection);
            for (i, layer) in layers.iter().enumerate() {
                if layer.has_spec(&variant_path) {
                    nodes.push(Node {
                        layer_index: i,
                        path: variant_path.clone(),
                        arc: ArcType::Variant,
                    });
                }
            }
        }

        // R — References: compose ReferenceListOp across root nodes, then add
        // nodes from referenced layers with namespace remapping.
        let references = compose_arc_list::<Reference>(&nodes, FieldKey::References, layers);
        for reference in &references {
            add_reference_nodes(path, reference, ArcType::Reference, &mut nodes, layers, identifiers);
        }

        // P — Payloads: same as references but weaker.
        let payloads = collect_payloads(&nodes, layers);
        for payload in &payloads {
            let reference = Reference {
                asset_path: payload.asset_path.clone(),
                prim_path: payload.prim_path.clone(),
                ..Default::default()
            };
            add_reference_nodes(path, &reference, ArcType::Payload, &mut nodes, layers, identifiers);
        }

        // S — Specializes: same as inherits but weakest in LIVERPS.
        let specializes = compose_arc_list::<Path>(&nodes, FieldKey::Specializes, layers);
        for specialize_path in &specializes {
            for (i, layer) in layers.iter().enumerate() {
                add_remapped_nodes(
                    layer.as_ref(),
                    i,
                    path,
                    specialize_path,
                    ArcType::Specialize,
                    &mut nodes,
                );
            }
        }

        PrimIndex { nodes }
    }

    /// Resolves a field by walking nodes from strongest to weakest, returning the first opinion.
    ///
    /// `make_path` maps each node to the path to query in that layer.
    /// A [`Value::ValueBlock`] explicitly blocks opinions from weaker layers.
    pub(crate) fn resolve_field(
        &self,
        field: &str,
        layers: &[LayerData],
        make_path: impl Fn(&Node) -> Result<Path>,
    ) -> Result<Option<Value>> {
        for node in &self.nodes {
            let query_path = make_path(node)?;
            let data = &layers[node.layer_index];
            if !data.has_field(&query_path, field) {
                continue;
            }

            let value = data.get(&query_path, field)?;
            if matches!(value.as_ref(), Value::ValueBlock) {
                return Ok(None);
            }
            return Ok(Some(value.into_owned()));
        }

        Ok(None)
    }
}

/// Resolves variant selections by walking root nodes strongest-to-weakest.
///
/// For each variant set, the first opinion wins.
fn resolve_variant_selections(root_nodes: &[Node], layers: &[LayerData]) -> Vec<(String, String)> {
    let mut selections: HashMap<String, String> = HashMap::new();

    for node in root_nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, FieldKey::VariantSelection.as_str()) else {
            continue;
        };

        if let Value::VariantSelectionMap(map) = value.into_owned() {
            for (set_name, selection) in map {
                // First opinion wins.
                selections.entry(set_name).or_insert(selection);
            }
        }
    }

    selections.into_iter().collect()
}

/// Composes a list-op field across root nodes, returning the flattened list.
fn compose_arc_list<T: Default + Clone + PartialEq>(
    root_nodes: &[Node],
    field: FieldKey,
    layers: &[LayerData],
) -> Vec<T>
where
    Value: TryInto<ListOp<T>>,
{
    let field = field.as_str();
    let mut result: Vec<T> = Vec::new();

    // Walk from weakest to strongest, composing each ListOp on top.
    for node in root_nodes.iter().rev() {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, field) else {
            continue;
        };

        let Ok(list_op) = value.into_owned().try_into() else {
            continue;
        };

        result = list_op.compose_over(&result);
    }

    result
}

/// Collects payloads from root nodes, handling both single `Payload` and `PayloadListOp`.
fn collect_payloads(root_nodes: &[Node], layers: &[LayerData]) -> Vec<Payload> {
    let mut result: Vec<Payload> = Vec::new();

    for node in root_nodes.iter().rev() {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, FieldKey::Payload.as_str()) else {
            continue;
        };

        match value.into_owned() {
            Value::Payload(p) => {
                if !result.contains(&p) {
                    result.push(p);
                }
            }
            Value::PayloadListOp(list_op) => {
                result = list_op.compose_over(&result);
            }
            _ => {}
        }
    }

    result
}

/// Adds nodes from a referenced layer for a given prim path.
///
/// If the reference has an `asset_path`, looks up the target layer by
/// identifier. If empty, the reference is internal (same layer stack).
/// The source `prim_path` is used for namespace remapping; if empty,
/// the target layer's `defaultPrim` is used.
fn add_reference_nodes(
    composed_path: &Path,
    reference: &Reference,
    arc: ArcType,
    nodes: &mut Vec<Node>,
    layers: &[LayerData],
    identifiers: &[String],
) {
    if reference.asset_path.is_empty() {
        // Internal reference — target is within the same layer stack.
        let source = &reference.prim_path;
        if source.is_empty() {
            return;
        }
        for (i, layer) in layers.iter().enumerate() {
            add_remapped_nodes(layer.as_ref(), i, composed_path, source, arc, nodes);
        }
    } else {
        // External reference — find the target layer by identifier.
        let Some(layer_index) = find_layer(&reference.asset_path, identifiers) else {
            return;
        };
        let layer = layers[layer_index].as_ref();

        let source = if reference.prim_path.is_empty() {
            // Use the target layer's defaultPrim.
            let root = Path::abs_root();
            let Ok(value) = layer.get(&root, FieldKey::DefaultPrim.as_str()) else {
                return;
            };
            match value.into_owned() {
                Value::Token(name) | Value::String(name) => Path::new(&format!("/{name}")).unwrap_or_default(),
                _ => return,
            }
        } else {
            reference.prim_path.clone()
        };

        add_remapped_nodes(layer, layer_index, composed_path, &source, arc, nodes);
    }
}

/// Adds nodes from a single layer with namespace remapping.
///
/// Maps `composed_path` and its children from `source_path` in the layer.
fn add_remapped_nodes(
    layer: &dyn AbstractData,
    layer_index: usize,
    composed_path: &Path,
    source_path: &Path,
    arc: ArcType,
    nodes: &mut Vec<Node>,
) {
    // Remap: the composed_path corresponds to source_path in the target layer.
    // For the prim itself, just check if source_path exists.
    let query_path = composed_path.replace_prefix(composed_path, source_path);
    let Some(query_path) = query_path else {
        return;
    };

    if layer.has_spec(&query_path) {
        nodes.push(Node {
            layer_index,
            path: query_path,
            arc,
        });
    }
}

/// Finds a layer index whose identifier matches `asset_path`.
///
/// Tries an exact match first, then falls back to suffix matching at a
/// path separator boundary (so `_stage.usda` matches `/abs/path/_stage.usda`
/// but not `/abs/path/not_stage.usda`).
fn find_layer(asset_path: &str, identifiers: &[String]) -> Option<usize> {
    let sep = std::path::MAIN_SEPARATOR as u8;

    for (i, id) in identifiers.iter().enumerate() {
        if *id == asset_path {
            return Some(i);
        }

        if id.ends_with(asset_path) {
            let prefix_len = id.len() - asset_path.len();
            if id.as_bytes()[prefix_len - 1] == sep {
                return Some(i);
            }
        }
    }

    None
}
