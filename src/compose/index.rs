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

use std::borrow::Cow;
use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::schema::FieldKey;
use crate::sdf::{AbstractData, LayerData, ListOp, Path, Payload, PayloadListOp, Reference, Value};

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
                add_remapped_nodes(layer.as_ref(), i, inherit_path, ArcType::Inherit, &mut nodes);
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
            add_arc_nodes(
                &reference.asset_path,
                &reference.prim_path,
                ArcType::Reference,
                &mut nodes,
                layers,
                identifiers,
            );
        }

        // P — Payloads: same as references but weaker.
        let payloads = collect_payloads(&nodes, layers);
        for payload in &payloads {
            add_arc_nodes(
                &payload.asset_path,
                &payload.prim_path,
                ArcType::Payload,
                &mut nodes,
                layers,
                identifiers,
            );
        }

        // S — Specializes: same as inherits but weakest in LIVERPS.
        let specializes = compose_arc_list::<Path>(&nodes, FieldKey::Specializes, layers);
        for specialize_path in &specializes {
            for (i, layer) in layers.iter().enumerate() {
                add_remapped_nodes(layer.as_ref(), i, specialize_path, ArcType::Specialize, &mut nodes);
            }
        }

        PrimIndex { nodes }
    }

    /// Resolves a field by walking nodes from strongest to weakest, returning the first opinion.
    ///
    /// When `prop_suffix` is `None`, queries use the node's path directly (zero-copy).
    /// When `Some`, appends the suffix to form a property path for each node.
    /// A [`Value::ValueBlock`] explicitly blocks opinions from weaker layers.
    pub(crate) fn resolve_field(
        &self,
        field: &str,
        layers: &[LayerData],
        prop_suffix: Option<&str>,
    ) -> Result<Option<Value>> {
        for node in &self.nodes {
            let query_path = match prop_suffix {
                Some(suffix) => Cow::Owned(Path::new(&format!("{}{suffix}", node.path))?),
                None => Cow::Borrowed(&node.path),
            };

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
fn resolve_variant_selections(root_nodes: &[Node], layers: &[LayerData]) -> HashMap<String, String> {
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

    selections
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
    let mut combined: Option<ListOp<T>> = None;

    // Walk from strongest to weakest, combining ListOps into a single reduced op.
    for node in root_nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, field) else {
            continue;
        };
        let Ok(list_op) = value.into_owned().try_into() else {
            continue;
        };
        combined = Some(match combined {
            Some(stronger) => stronger.combined_with(&list_op),
            None => list_op,
        });
    }

    combined.map(|op| op.reduced().flatten()).unwrap_or_default()
}

/// Collects payloads from root nodes, handling both single `Payload` and `PayloadListOp`.
fn collect_payloads(root_nodes: &[Node], layers: &[LayerData]) -> Vec<Payload> {
    let mut combined: Option<PayloadListOp> = None;

    // Walk from strongest to weakest, combining payload ListOps.
    for node in root_nodes {
        let data = &layers[node.layer_index];
        let Ok(value) = data.get(&node.path, FieldKey::Payload.as_str()) else {
            continue;
        };

        let list_op = match value.into_owned() {
            Value::Payload(p) => PayloadListOp {
                explicit: true,
                explicit_items: vec![p],
                ..Default::default()
            },
            Value::PayloadListOp(op) => op,
            _ => continue,
        };

        combined = Some(match combined {
            Some(stronger) => stronger.combined_with(&list_op),
            None => list_op,
        });
    }

    combined.map(|op| op.reduced().flatten()).unwrap_or_default()
}

/// Adds nodes from a referenced or payloaded layer for a given prim path.
///
/// If `asset_path` is empty, the target is internal (same layer stack).
/// `prim_path` is used for namespace remapping; if empty, the target
/// layer's `defaultPrim` is used.
fn add_arc_nodes(
    asset_path: &str,
    prim_path: &Path,
    arc: ArcType,
    nodes: &mut Vec<Node>,
    layers: &[LayerData],
    identifiers: &[String],
) {
    if asset_path.is_empty() {
        // Internal reference — target is within the same layer stack.
        if prim_path.is_empty() {
            return;
        }
        for (i, layer) in layers.iter().enumerate() {
            add_remapped_nodes(layer.as_ref(), i, prim_path, arc, nodes);
        }
    } else {
        // External reference — find the target layer by identifier.
        let Some(layer_index) = find_layer(asset_path, identifiers) else {
            return;
        };
        let layer = layers[layer_index].as_ref();

        let source = if prim_path.is_empty() {
            // Use the target layer's defaultPrim.
            let root = Path::abs_root();
            let Ok(value) = layer.get(&root, FieldKey::DefaultPrim.as_str()) else {
                return;
            };
            match value.into_owned() {
                Value::Token(name) | Value::String(name) => {
                    Cow::Owned(Path::new(&format!("/{name}")).unwrap_or_default())
                }
                _ => return,
            }
        } else {
            Cow::Borrowed(prim_path)
        };

        add_remapped_nodes(layer, layer_index, &source, arc, nodes);
    }
}

/// Adds nodes from a single layer with namespace remapping.
///
/// Maps `composed_path` and its children from `source_path` in the layer.
fn add_remapped_nodes(
    layer: &dyn AbstractData,
    layer_index: usize,
    source_path: &Path,
    arc: ArcType,
    nodes: &mut Vec<Node>,
) {
    if layer.has_spec(source_path) {
        nodes.push(Node {
            layer_index,
            path: source_path.clone(),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;
    use crate::compose::collect_layers;
    use crate::sdf::LayerData;

    use anyhow::Result;

    const VENDOR_COMPOSITION: &str = "vendor/usd-wg-assets/test_assets/foundation/stage_composition";

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    fn composition_path(relative: &str) -> String {
        format!("{}/{VENDOR_COMPOSITION}/{relative}", manifest_dir())
    }

    fn fixture_path(relative: &str) -> String {
        format!("{}/fixtures/{relative}", manifest_dir())
    }

    /// Loads layers and splits into parallel vecs for PrimIndex::build.
    fn load_layers(path: &str) -> Result<(Vec<LayerData>, Vec<String>)> {
        let resolver = DefaultResolver::new();
        let collected = collect_layers(&resolver, path)?;
        let mut layers = Vec::new();
        let mut identifiers = Vec::new();
        for layer in collected {
            identifiers.push(layer.identifier);
            layers.push(layer.data);
        }
        Ok((layers, identifiers))
    }

    /// Builds a prim index for a given path string.
    fn build(layers: &[LayerData], identifiers: &[String], prim: &str) -> PrimIndex {
        PrimIndex::build(&Path::from(prim), layers, identifiers)
    }

    #[test]
    fn single_layer_root_node() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("active.usda"))?;
        let index = build(&layers, &ids, "/World");

        assert_eq!(index.nodes.len(), 1);
        assert_eq!(index.nodes[0].layer_index, 0);
        assert_eq!(index.nodes[0].arc, ArcType::Root);
        Ok(())
    }

    #[test]
    fn sublayer_two_root_nodes() -> Result<()> {
        let (layers, ids) = load_layers(&fixture_path("sublayer_override.usda"))?;
        let index = build(&layers, &ids, "/World");

        assert_eq!(index.nodes.len(), 2, "both layers should have /World");
        assert_eq!(index.nodes[0].layer_index, 0, "stronger layer first");
        assert_eq!(index.nodes[1].layer_index, 1, "weaker layer second");
        Ok(())
    }

    #[test]
    fn prim_only_in_stronger_layer() -> Result<()> {
        let (layers, ids) = load_layers(&fixture_path("sublayer_override.usda"))?;
        let index = build(&layers, &ids, "/World/Sphere");

        assert_eq!(index.nodes.len(), 1);
        assert_eq!(index.nodes[0].layer_index, 0);
        Ok(())
    }

    #[test]
    fn nonexistent_prim_empty_index() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("active.usda"))?;
        let index = build(&layers, &ids, "/DoesNotExist");

        assert!(index.is_empty());
        Ok(())
    }

    #[test]
    fn reference_arc_present() -> Result<()> {
        let (layers, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        let index = build(&layers, &ids, "/World/MyPrim");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Reference));
        Ok(())
    }

    #[test]
    fn inherit_arc_present() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("class_inherit.usda"))?;
        let index = build(&layers, &ids, "/World/cubeWithoutSetColor");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn inherit_root_is_strongest() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("class_inherit.usda"))?;
        let index = build(&layers, &ids, "/World/cubeWithSetColor");
        let arcs: Vec<_> = index.nodes.iter().map(|n| n.arc).collect();

        assert_eq!(arcs[0], ArcType::Root);
        assert!(arcs.contains(&ArcType::Inherit));
        Ok(())
    }

    #[test]
    fn variant_arc_with_selection() -> Result<()> {
        let path = format!(
            "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
            manifest_dir()
        );
        let (layers, ids) = load_layers(&path)?;
        let index = build(&layers, &ids, "/World/Sphere");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Variant));

        let variant_node = index.nodes.iter().find(|n| n.arc == ArcType::Variant).unwrap();
        assert_eq!(variant_node.path.as_str(), "/World/Sphere{size=small}");
        Ok(())
    }

    #[test]
    fn specialize_arc_present() -> Result<()> {
        let (layers, ids) = load_layers(&composition_path("inherit_and_specialize.usda"))?;
        let index = build(&layers, &ids, "/World/cubeScene/specializes");

        assert!(index.nodes.iter().any(|n| n.arc == ArcType::Specialize));
        Ok(())
    }

    #[test]
    fn find_layer_exact_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer(&ids[0], &ids).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_suffix_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("ref_target.usda", &ids).is_some());
        Ok(())
    }

    #[test]
    fn find_layer_no_partial_name_match() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("target.usda", &ids).is_none());
        Ok(())
    }

    #[test]
    fn find_layer_not_found() -> Result<()> {
        let (_, ids) = load_layers(&fixture_path("ref_external.usda"))?;
        assert!(find_layer("nonexistent.usda", &ids).is_none());
        Ok(())
    }
}
