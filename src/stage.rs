//! Composed USD stage.
//!
//! A [`Stage`] loads a root layer file and all its dependencies, then provides
//! composed access to the scene graph by merging opinions across layers
//! according to USD's [LIVERPS] strength ordering:
//!
//! 1. **L**ocal opinions (root layer stack / sublayers) — strongest
//! 2. **I**nherit arcs
//! 3. **V**ariant set arcs
//! 4. **R**eference arcs
//! 5. **P**ayload arcs
//! 6. **S**pecialize arcs — weakest
//!
//! The strength ordering applies recursively within each composition context.
//! When building prim and property stacks:
//!
//! - Local opinions are evaluated first
//! - Inherit arcs follow
//! - Variant sets are applied next
//! - References are processed
//! - Payloads are composed
//! - Specialize arcs provide fallback values
//!
//! [LIVERPS]: https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html

use std::cell::RefCell;
use std::collections::HashMap;

use anyhow::Result;

use crate::ar::Resolver;
use crate::compose;
use crate::compose::prim_index::{ArcType, Node, PrimIndex};
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{AbstractData, ListOp, Path, Payload, Reference, SpecType, Value};

/// The scene's up-axis, as stored in the root layer's `upAxis` metadata.
///
/// USD defines two valid values: `"Y"` (Y-up, the default for many DCC tools)
/// and `"Z"` (Z-up, used by e.g. OpenUSD's own reference scenes).
///
/// See <https://openusd.org/dev/api/group___usd_geom_up_axis__group.html>
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UpAxis {
    /// Y axis points up.
    Y,
    /// Z axis points up.
    Z,
}

/// A composed USD stage.
///
/// Owns the loaded layer stack and provides composed access to prims,
/// properties, and metadata.
pub struct Stage {
    /// All layers, root (strongest) first.
    layers: Vec<Box<dyn AbstractData>>,
    /// Layer identifiers, parallel to `layers`.
    identifiers: Vec<String>,
    /// Cached prim indices, built lazily per prim.
    prim_indices: RefCell<HashMap<Path, PrimIndex>>,
}

impl Stage {
    /// Opens a stage from a root layer file.
    ///
    /// Recursively resolves and loads all referenced layers, then builds a
    /// composed stage ready for queries.
    pub fn open(resolver: &impl Resolver, root_path: &str) -> Result<Self> {
        let collected = compose::collect_layers(resolver, root_path)?;

        let mut identifiers = Vec::with_capacity(collected.len());
        let mut layers = Vec::with_capacity(collected.len());

        for layer in collected {
            identifiers.push(layer.identifier);
            layers.push(layer.data);
        }

        Ok(Self {
            layers,
            identifiers,
            prim_indices: RefCell::new(HashMap::new()),
        })
    }

    /// Returns the number of layers in the stage.
    pub fn layer_count(&self) -> usize {
        self.layers.len()
    }

    /// Returns the layer identifiers in strength order (root first).
    pub fn layer_identifiers(&self) -> &[String] {
        &self.identifiers
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    pub fn default_prim(&self) -> Option<String> {
        self.field::<String>(&Path::abs_root(), FieldKey::DefaultPrim).ok()?
    }

    /// Returns the `upAxis` metadata from the root layer, if set.
    ///
    /// USD defines two valid values: `"Y"` and `"Z"`.  Any other authored
    /// value (malformed data) is treated as `None` rather than an error so
    /// that callers can continue inspecting the rest of the stage.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::{ar::DefaultResolver, Stage};
    /// use openusd::stage::UpAxis;
    ///
    /// let resolver = DefaultResolver::new();
    /// let stage = Stage::open(&resolver, "scene.usda").unwrap();
    /// match stage.up_axis() {
    ///     Some(UpAxis::Y) => println!("Y-up"),
    ///     Some(UpAxis::Z) => println!("Z-up"),
    ///     None => println!("upAxis not set"),
    /// }
    /// ```
    pub fn up_axis(&self) -> Option<UpAxis> {
        let raw = self.field::<String>(&Path::abs_root(), FieldKey::UpAxis).ok()??;
        match raw.as_str() {
            "Y" => Some(UpAxis::Y),
            "Z" => Some(UpAxis::Z),
            _ => None,
        }
    }

    /// Returns the composed list of root prim names (children of the pseudo-root).
    pub fn root_prims(&self) -> Result<Vec<String>> {
        self.prim_children(Path::abs_root())
    }

    /// Returns the composed list of child prim names for a given prim path.
    ///
    /// Merges `primChildren` across all layers that have a spec at the given
    /// path, collecting the union of child names while preserving the order
    /// from the strongest layer.
    pub fn prim_children(&self, path: impl Into<Path>) -> Result<Vec<String>> {
        self.composed_children(&path.into(), ChildrenKey::PrimChildren)
    }

    /// Returns the composed list of property names for a given prim path.
    pub fn prim_properties(&self, path: impl Into<Path>) -> Result<Vec<String>> {
        self.composed_children(&path.into(), ChildrenKey::PropertyChildren)
    }

    /// Returns `true` if any layer has a spec at the given composed path.
    pub fn has_spec(&self, path: impl Into<Path>) -> bool {
        !self.prim_index(&path.into()).is_empty()
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub fn spec_type(&self, path: impl Into<Path>) -> Option<SpecType> {
        let index = self.prim_index(&path.into());
        for node in &index.nodes {
            if let Some(ty) = self.layers[node.layer_index].spec_type(&node.path) {
                return Some(ty);
            }
        }
        None
    }

    /// Resolves a field value by walking the prim index from strongest to weakest.
    ///
    /// For prim paths, walks the prim index nodes. For property paths (containing
    /// a `.`), uses the owning prim's index to determine layer order, then queries
    /// the property spec directly in each layer.
    ///
    /// Returns the first (strongest) opinion found, or `None` if no layer
    /// provides a value. A [`Value::ValueBlock`] explicitly blocks opinions
    /// from weaker layers and causes `None` to be returned.
    ///
    /// The return type is generic: use `Value` to get the raw enum, or a
    /// concrete type (e.g. `bool`, `f64`, `String`) to convert automatically
    /// via [`TryFrom<Value>`].
    ///
    /// Accepts both [`FieldKey`] and `&str` as the field name.
    ///
    /// # Example
    ///
    /// ```ignore
    /// let active: Option<bool> = stage.field(&prim, FieldKey::Active)?;
    /// let raw: Option<Value> = stage.field(&prim, FieldKey::Active)?;
    /// ```
    pub fn field<T>(&self, path: impl Into<Path>, field: impl AsRef<str>) -> Result<Option<T>>
    where
        T: TryFrom<Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        let path: Path = path.into();
        let field: &str = field.as_ref();
        let raw = if path.is_property_path() {
            self.property_field(&path, field)?
        } else {
            self.resolve_field(&path, field)?
        };

        match raw {
            Some(value) => Ok(Some(T::try_from(value)?)),
            None => Ok(None),
        }
    }

    /// Walks the prim index for a prim path, returning the first opinion for `field`.
    fn resolve_field(&self, path: &Path, field: &str) -> Result<Option<Value>> {
        let index = self.prim_index(path);
        self.resolve_field_in(&index, field, |node| Ok(node.path.clone()))
    }

    /// Resolves a field on a property spec (attribute or relationship).
    ///
    /// Uses the owning prim's index to determine layer ordering, then builds
    /// the property path within each layer and queries for the field.
    fn property_field(&self, prop_path: &Path, field: &str) -> Result<Option<Value>> {
        let prim_path = prop_path.prim_path();
        let prop_suffix = &prop_path.as_str()[prim_path.as_str().len()..];
        let index = self.prim_index(&prim_path);
        self.resolve_field_in(&index, field, |node| Path::new(&format!("{}{prop_suffix}", node.path)))
    }

    /// Walks a prim index from strongest to weakest, returning the first opinion.
    ///
    /// `make_path` maps each node to the path to query in that layer.
    fn resolve_field_in(
        &self,
        index: &PrimIndex,
        field: &str,
        make_path: impl Fn(&Node) -> Result<Path>,
    ) -> Result<Option<Value>> {
        for node in &index.nodes {
            let query_path = make_path(node)?;
            let data = &self.layers[node.layer_index];
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

    /// Traverses all composed prims depth-first, calling `visitor` for each.
    ///
    /// The visitor receives the prim's composed path.
    pub fn traverse(&self, mut visitor: impl FnMut(&Path)) -> Result<()> {
        let mut stack = vec![Path::abs_root()];

        while let Some(path) = stack.pop() {
            if path != Path::abs_root() {
                visitor(&path);
            }

            let children = self.prim_children(&path)?;
            // Push in reverse so first child is visited first.
            for name in children.iter().rev() {
                if let Ok(child) = path.append_path(name.as_str()) {
                    stack.push(child);
                }
            }
        }

        Ok(())
    }

    /// Returns the prim index for a path, building and caching it if needed.
    fn prim_index(&self, path: &Path) -> PrimIndex {
        // Check cache first.
        if let Some(cached) = self.prim_indices.borrow().get(path) {
            return cached.clone();
        }

        let index = self.build_prim_index(path);
        self.prim_indices.borrow_mut().insert(path.clone(), index.clone());
        index
    }

    /// Merges a children field (e.g. `primChildren`, `properties`) across all
    /// nodes in the prim index, returning the union with strongest-first ordering.
    fn composed_children(&self, path: &Path, children_field: impl AsRef<str>) -> Result<Vec<String>> {
        let children_field: &str = children_field.as_ref();
        let index = self.prim_index(path);
        let mut result: Vec<String> = Vec::new();

        for node in &index.nodes {
            if let Ok(value) = self.layers[node.layer_index].get(&node.path, children_field) {
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

    /// Builds a prim index for the given path.
    ///
    /// Follows LIVERPS ordering:
    /// Local (sublayers) > Inherits > Variants > References > Payloads > Specializes.
    fn build_prim_index(&self, path: &Path) -> PrimIndex {
        let mut nodes = Vec::new();

        // L — Root / sublayer opinions: check each layer in strength order.
        for (i, layer) in self.layers.iter().enumerate() {
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
        let inherits = self.compose_arc_list::<Path>(&nodes, FieldKey::InheritPaths);
        for inherit_path in &inherits {
            for (i, layer) in self.layers.iter().enumerate() {
                self.add_remapped_nodes(layer.as_ref(), i, path, inherit_path, ArcType::Inherit, &mut nodes);
            }
        }

        // V — Variants: resolve variant selection (first opinion wins), then
        // add specs from the selected variant path in each layer.
        let selections = self.resolve_variant_selections(&nodes);
        for (set_name, selection) in &selections {
            let variant_path = path.append_variant_selection(set_name, selection);
            for (i, layer) in self.layers.iter().enumerate() {
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
        let references = self.compose_arc_list::<Reference>(&nodes, FieldKey::References);
        for reference in &references {
            self.add_reference_nodes(path, reference, ArcType::Reference, &mut nodes);
        }

        // P — Payloads: same as references but weaker.
        let payloads = self.collect_payloads(&nodes);
        for payload in &payloads {
            let reference = Reference {
                asset_path: payload.asset_path.clone(),
                prim_path: payload.prim_path.clone(),
                ..Default::default()
            };
            self.add_reference_nodes(path, &reference, ArcType::Payload, &mut nodes);
        }

        // S — Specializes: same as inherits but weakest in LIVERPS.
        let specializes = self.compose_arc_list::<Path>(&nodes, FieldKey::Specializes);
        for specialize_path in &specializes {
            for (i, layer) in self.layers.iter().enumerate() {
                self.add_remapped_nodes(
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

    /// Resolves variant selections by walking root nodes strongest-to-weakest.
    ///
    /// For each variant set, the first opinion wins. Returns a list of
    /// `(set_name, selection)` pairs.
    fn resolve_variant_selections(&self, root_nodes: &[Node]) -> Vec<(String, String)> {
        let mut selections: HashMap<String, String> = HashMap::new();

        for node in root_nodes {
            let data = &self.layers[node.layer_index];
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
    fn compose_arc_list<T: Default + Clone + PartialEq>(&self, root_nodes: &[Node], field: FieldKey) -> Vec<T>
    where
        Value: TryInto<ListOp<T>>,
    {
        let field = field.as_str();
        let mut result: Vec<T> = Vec::new();

        // Walk from weakest to strongest, composing each ListOp on top.
        for node in root_nodes.iter().rev() {
            let data = &self.layers[node.layer_index];
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
    fn collect_payloads(&self, root_nodes: &[Node]) -> Vec<Payload> {
        let mut result: Vec<Payload> = Vec::new();

        for node in root_nodes.iter().rev() {
            let data = &self.layers[node.layer_index];
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
    fn add_reference_nodes(&self, composed_path: &Path, reference: &Reference, arc: ArcType, nodes: &mut Vec<Node>) {
        if reference.asset_path.is_empty() {
            // Internal reference — target is within the same layer stack.
            let source = &reference.prim_path;
            if source.is_empty() {
                return;
            }
            for (i, layer) in self.layers.iter().enumerate() {
                self.add_remapped_nodes(layer.as_ref(), i, composed_path, source, arc, nodes);
            }
        } else {
            // External reference — find the target layer by identifier.
            let Some((layer_index, layer)) = self.find_layer(&reference.asset_path) else {
                return;
            };

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

            self.add_remapped_nodes(layer, layer_index, composed_path, &source, arc, nodes);
        }
    }

    /// Adds nodes from a single layer with namespace remapping.
    ///
    /// Maps `composed_path` and its children from `source_path` in the layer.
    fn add_remapped_nodes(
        &self,
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

    /// Finds a layer whose identifier matches `asset_path`.
    ///
    /// Tries an exact match first, then falls back to suffix matching at a
    /// path separator boundary (so `_stage.usda` matches `/abs/path/_stage.usda`
    /// but not `/abs/path/not_stage.usda`).
    fn find_layer(&self, asset_path: &str) -> Option<(usize, &dyn AbstractData)> {
        let sep = std::path::MAIN_SEPARATOR as u8;

        for (i, id) in self.identifiers.iter().enumerate() {
            if *id == asset_path {
                return Some((i, self.layers[i].as_ref()));
            }

            if id.ends_with(asset_path) {
                let prefix_len = id.len() - asset_path.len();
                if id.as_bytes()[prefix_len - 1] == sep {
                    return Some((i, self.layers[i].as_ref()));
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ar::DefaultResolver;
    use crate::compose::prim_index::ArcType;

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

    // --- find_layer ---

    /// Exact identifier match should return the layer.
    #[test]
    fn find_layer_exact_match() -> Result<()> {
        let path = fixture_path("ref_external.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // The full identifier of the root layer should match exactly.
        assert!(
            stage.find_layer(&stage.identifiers[0]).is_some(),
            "exact match should succeed"
        );

        Ok(())
    }

    /// Suffix match at a path separator boundary should work
    /// (e.g. "ref_target.usda" matches "/full/path/ref_target.usda").
    #[test]
    fn find_layer_suffix_match() -> Result<()> {
        let path = fixture_path("ref_external.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // ref_external.usda references ref_target.usda, which should be loaded.
        let result = stage.find_layer("ref_target.usda");
        assert!(result.is_some(), "suffix match at separator boundary should succeed");

        Ok(())
    }

    /// A partial filename overlap without a separator boundary must not match
    /// (e.g. "target.usda" should not match "ref_target.usda").
    #[test]
    fn find_layer_no_partial_name_match() -> Result<()> {
        let path = fixture_path("ref_external.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert!(
            stage.find_layer("target.usda").is_none(),
            "partial name should not match"
        );

        Ok(())
    }

    /// A completely unknown path should return None.
    #[test]
    fn find_layer_not_found() -> Result<()> {
        let path = fixture_path("ref_external.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert!(stage.find_layer("nonexistent.usda").is_none());

        Ok(())
    }

    // --- PrimIndex internals ---

    /// A prim in a single-layer stage should produce a PrimIndex with exactly
    /// one Root node pointing at layer 0.
    #[test]
    fn prim_index_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let index = stage.prim_index(&Path::new("/World")?);
        assert_eq!(index.nodes.len(), 1);
        assert_eq!(index.nodes[0].layer_index, 0);
        assert_eq!(index.nodes[0].arc, ArcType::Root);

        Ok(())
    }

    /// When a prim exists in both layers of a sublayer composition, the index
    /// should contain two Root nodes with the stronger layer (index 0) first.
    #[test]
    fn prim_index_sublayer_two_layers() -> Result<()> {
        // sublayer_override.usda sublayers sublayer_base.usda; both have /World.
        let path = fixture_path("sublayer_override.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let index = stage.prim_index(&Path::new("/World")?);
        assert_eq!(index.nodes.len(), 2, "both layers should have /World");
        assert_eq!(index.nodes[0].layer_index, 0, "stronger layer first");
        assert_eq!(index.nodes[1].layer_index, 1, "weaker layer second");

        Ok(())
    }

    /// A prim that only exists in the stronger layer should have a single node.
    #[test]
    fn prim_index_prim_only_in_stronger_layer() -> Result<()> {
        let path = fixture_path("sublayer_override.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // /World/Sphere is only defined in the override layer.
        let index = stage.prim_index(&Path::new("/World/Sphere")?);
        assert_eq!(index.nodes.len(), 1);
        assert_eq!(index.nodes[0].layer_index, 0);

        Ok(())
    }

    /// A path that doesn't exist in any layer should produce an empty PrimIndex.
    #[test]
    fn prim_index_nonexistent() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let index = stage.prim_index(&Path::new("/DoesNotExist")?);
        assert!(index.is_empty());

        Ok(())
    }

    // --- Basic stage opening (vendor/usd-wg-assets) ---

    /// A single-layer .usda file should load with correct defaultPrim and
    /// root prim list.
    #[test]
    fn open_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert_eq!(stage.layer_count(), 1);
        assert_eq!(stage.default_prim(), Some("World".to_string()));
        assert_eq!(stage.root_prims()?, vec!["World"]);

        Ok(())
    }

    /// Traverse should visit all prims depth-first.
    #[test]
    fn traverse_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let mut prims = Vec::new();
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;

        assert_eq!(prims, vec!["/World", "/World/CubeInactive", "/World/CubeActive"]);

        Ok(())
    }

    /// Reading a field from a single-layer stage should return the authored value.
    #[test]
    fn field_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // The "active" metadata on CubeInactive should be false.
        let active = stage.field::<bool>(&Path::new("/World/CubeInactive")?, FieldKey::Active)?;
        assert_eq!(active, Some(false));

        // CubeActive has active = true.
        let active = stage.field::<bool>(&Path::new("/World/CubeActive")?, FieldKey::Active)?;
        assert_eq!(active, Some(true));

        Ok(())
    }

    /// Querying a field that isn't authored should return None.
    #[test]
    fn field_not_authored() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let active = stage.field::<Value>(&Path::new("/World")?, FieldKey::Active)?;
        assert_eq!(active, None);

        Ok(())
    }

    // --- Sublayer composition ---

    /// sublayer_override.usda sublayers sublayer_base.usda. Both layers define
    /// /World/Cube but with different displayColor values. The stronger (override)
    /// layer's opinion should win (first-opinion-wins rule).
    #[test]
    fn sublayer_stronger_opinion_wins() -> Result<()> {
        let path = fixture_path("sublayer_override.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert_eq!(stage.layer_count(), 2);

        // /World/Cube.primvars:displayColor is overridden to blue [(0,0,1)] in
        // the stronger layer, base has red [(1,0,0)].
        let prop_path = Path::new("/World/Cube")?.append_property("primvars:displayColor")?;
        let value: Option<Value> = stage.field(&prop_path, FieldKey::Default)?;
        assert!(value.is_some(), "displayColor should have a composed value");

        // The composed value must come from the stronger layer (blue),
        // not the weaker layer (red). Verify by checking it's not the base red.
        let value = value.unwrap();
        let base_red = Value::Vec3f(vec![1.0, 0.0, 0.0]);
        assert_ne!(value, base_red, "stronger layer opinion should win over weaker");

        Ok(())
    }

    /// A prim defined only in the stronger sublayer should appear in composed
    /// children alongside prims from the weaker layer.
    #[test]
    fn sublayer_children_union() -> Result<()> {
        let path = fixture_path("sublayer_override.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let children = stage.prim_children(&Path::new("/World")?)?;
        // Override layer adds Sphere; base layer defines Cube.
        assert!(children.contains(&"Cube".to_string()), "Cube from base layer");
        assert!(children.contains(&"Sphere".to_string()), "Sphere from override layer");

        Ok(())
    }

    /// The sublayer_same_folder vendor test asset should open correctly with
    /// 2 layers and expose the sublayer's prims through composition.
    #[test]
    fn sublayer_prims_from_weaker_layer() -> Result<()> {
        let path = composition_path("subLayer/sublayer_same_folder.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert_eq!(stage.layer_count(), 2);
        assert_eq!(stage.default_prim(), Some("World".to_string()));

        // The weaker sublayer (_stage.usda) defines /World/Cube.
        let mut prims = Vec::new();
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;
        assert!(prims.contains(&"/World/Cube".to_string()));

        Ok(())
    }

    /// The active.usda vendor test has prims with active=true/false metadata.
    /// Verify field resolution returns the correct authored values.
    #[test]
    fn field_active_metadata() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let inactive: Option<bool> = stage.field(&Path::new("/World/CubeInactive")?, FieldKey::Active)?;
        assert_eq!(inactive, Some(false));

        let active = stage.field::<bool>(&Path::new("/World/CubeActive")?, FieldKey::Active)?;
        assert_eq!(active, Some(true));

        Ok(())
    }

    // --- Reference composition ---

    /// An external reference with defaultPrim should pull the referenced prim's
    /// children into the referencing prim's namespace.
    /// ref_external.usda: /World/MyPrim references ref_target.usda (defaultPrim="Source").
    /// ref_target.usda defines /Source/Child with displayColor.
    #[test]
    fn reference_external_default_prim() -> Result<()> {
        let path = fixture_path("ref_external.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // /World/MyPrim should exist via the reference.
        assert!(stage.has_spec(&Path::new("/World/MyPrim")?));

        // The prim index should have a Reference arc node.
        let index = stage.prim_index(&Path::new("/World/MyPrim")?);
        assert!(
            index.nodes.iter().any(|n| n.arc == ArcType::Reference),
            "prim index should contain a Reference node"
        );

        // /World/MyPrim/Child should be reachable via namespace remapping
        // (maps /Source/Child from the target layer to /World/MyPrim/Child).
        let children = stage.prim_children(&Path::new("/World/MyPrim")?)?;
        assert!(
            children.contains(&"Child".to_string()),
            "referenced children should be visible"
        );

        Ok(())
    }

    /// Vendor test: reference_same_folder.usda references _stage.usda with
    /// defaultPrim. The referenced layer's /World/Cube should appear under the
    /// referencing prim.
    #[test]
    fn reference_default_prim_from_external_layer() -> Result<()> {
        let path = composition_path("references/reference_same_folder.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // /World references _stage.usda's defaultPrim ("World"),
        // so /World/Cube should come from the referenced layer.
        let children = stage.prim_children(&Path::new("/World")?)?;
        assert!(
            children.contains(&"Cube".to_string()),
            "Cube from referenced layer should appear under /World"
        );

        Ok(())
    }

    /// An external reference with an explicit prim path should remap the
    /// target prim into the referencing prim's namespace.
    /// ref_prim.usda: /World/RefPrim references @ref_target.usda@</Source>.
    #[test]
    fn reference_explicit_prim_path() -> Result<()> {
        let path = fixture_path("ref_prim.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // /World/RefPrim should exist with a Reference arc.
        let index = stage.prim_index(&Path::new("/World/RefPrim")?);
        assert!(
            index.nodes.iter().any(|n| n.arc == ArcType::Reference),
            "should have a Reference arc"
        );

        // /Source/Child in ref_target.usda should appear as /World/RefPrim/Child.
        let children = stage.prim_children(&Path::new("/World/RefPrim")?)?;
        assert!(
            children.contains(&"Child".to_string()),
            "referenced children should be namespace-remapped"
        );

        Ok(())
    }

    // --- Inherit composition ---

    /// class_inherit.usda: cubeWithoutSetColor inherits from /_myClass which
    /// defines displayColor = green. The prim should pick up the class property.
    #[test]
    fn inherit_from_class() -> Result<()> {
        let path = composition_path("class_inherit.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // The prim index for cubeWithoutSetColor should include an Inherit node
        // pointing at /_myClass.
        let index = stage.prim_index(&Path::new("/World/cubeWithoutSetColor")?);
        assert!(
            index.nodes.iter().any(|n| n.arc == ArcType::Inherit),
            "should have an Inherit arc"
        );

        // The inherited property should be visible.
        let props = stage.prim_properties(&Path::new("/World/cubeWithoutSetColor")?)?;
        assert!(
            props.contains(&"primvars:displayColor".to_string()),
            "inherited property should be visible"
        );

        Ok(())
    }

    /// class_inherit.usda: cubeWithSetColor inherits from /_myClass but
    /// overrides displayColor locally. Local opinion (red) should win
    /// over the inherited opinion (green).
    #[test]
    fn inherit_local_opinion_wins() -> Result<()> {
        let path = composition_path("class_inherit.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // cubeWithSetColor has both a local and inherited displayColor.
        // The prim index should have Root first, then Inherit.
        let index = stage.prim_index(&Path::new("/World/cubeWithSetColor")?);
        let arcs: Vec<_> = index.nodes.iter().map(|n| n.arc).collect();
        assert_eq!(arcs[0], ArcType::Root, "Root should be strongest");
        assert!(arcs.contains(&ArcType::Inherit), "should also have Inherit");

        // The local displayColor (red) should win over inherited (green).
        let prop = Path::new("/World/cubeWithSetColor")?.append_property("primvars:displayColor")?;
        let value: Option<Value> = stage.field(&prop, FieldKey::Default)?;
        assert!(value.is_some());

        // Verify it's the local red, not the inherited green.
        let green = Value::Vec3f(vec![0.0, 0.8, 0.0]);
        assert_ne!(value.unwrap(), green, "local opinion should win over inherited");

        Ok(())
    }

    // --- Variant selection ---

    /// puzzle_1.usda: /World/Sphere has variantSet "size" with selection "small".
    /// The selected variant sets radius=2, while the local opinion sets radius=1.
    /// Local should win (L > V in LIVERPS), but the variant node should exist.
    #[test]
    fn variant_selection_resolves() -> Result<()> {
        let path = format!(
            "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
            manifest_dir()
        );
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // The prim index should contain a Variant arc node.
        let index = stage.prim_index(&Path::new("/World/Sphere")?);
        assert!(
            index.nodes.iter().any(|n| n.arc == ArcType::Variant),
            "should have a Variant arc for the selected variant"
        );

        // The variant node's path should be /World/Sphere{size=small}.
        let variant_node = index.nodes.iter().find(|n| n.arc == ArcType::Variant).unwrap();
        assert_eq!(variant_node.path.as_str(), "/World/Sphere{size=small}");

        Ok(())
    }

    /// The local opinion on radius (1) should be stronger than the variant's (2).
    #[test]
    fn variant_local_opinion_wins() -> Result<()> {
        let path = format!(
            "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
            manifest_dir()
        );
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // The local radius=1 should win over variant radius=2.
        let prop = Path::new("/World/Sphere")?.append_property("radius")?;
        let value = stage.field::<f64>(&prop, FieldKey::Default)?;
        assert_eq!(value, Some(1.0), "local opinion (1) should win over variant (2)");

        Ok(())
    }

    // --- Payload composition ---

    /// Vendor test: payload_same_folder.usda has a payload to _stage.usda.
    /// The payload's prim hierarchy should be composed into the stage.
    #[test]
    fn payload_pulls_children() -> Result<()> {
        let path = composition_path("payload/payload_same_folder.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        // The payload target layer has /World/Cube. Since /World is the payload
        // target, /World/Cube should appear.
        let children = stage.prim_children(&Path::new("/World")?)?;
        assert!(
            children.contains(&"Cube".to_string()),
            "Cube from payload layer should appear under /World"
        );

        Ok(())
    }

    // --- Specialize composition ---

    /// inherit_and_specialize.usda: /World/cubeScene/specializes specializes
    /// </World/cubeScene/source>. The specialize arc should appear in the
    /// prim index as the weakest arc.
    #[test]
    fn specialize_arc_present() -> Result<()> {
        let path = composition_path("inherit_and_specialize.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let index = stage.prim_index(&Path::new("/World/cubeScene/specializes")?);
        assert!(
            index.nodes.iter().any(|n| n.arc == ArcType::Specialize),
            "should have a Specialize arc"
        );

        Ok(())
    }

    /// The local opinion on displayColor (yellow) should win over the
    /// specialized source's displayColor (red).
    #[test]
    fn specialize_local_opinion_wins() -> Result<()> {
        let path = composition_path("inherit_and_specialize.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let prop = Path::new("/World/cubeScene/specializes")?.append_property("primvars:displayColor")?;
        let value: Option<Value> = stage.field(&prop, FieldKey::Default)?;
        assert!(value.is_some());

        // Local is yellow (0.8, 0.8, 0), source is red (0.8, 0, 0).
        let red = Value::Vec3f(vec![0.8, 0.0, 0.0]);
        assert_ne!(value.unwrap(), red, "local opinion should win over specialized");

        Ok(())
    }

    // --- Stage::up_axis() ---

    /// A stage with `upAxis = "Y"` should return `UpAxis::Y`.
    #[test]
    fn up_axis_y() -> Result<()> {
        let path = fixture_path("up_axis_y.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert_eq!(stage.up_axis(), Some(UpAxis::Y));

        Ok(())
    }

    /// A stage with `upAxis = "Z"` should return `UpAxis::Z`.
    #[test]
    fn up_axis_z() -> Result<()> {
        let path = fixture_path("up_axis_z.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert_eq!(stage.up_axis(), Some(UpAxis::Z));

        Ok(())
    }

    /// A stage without an `upAxis` metadata entry should return `None`.
    #[test]
    fn up_axis_absent_returns_none() -> Result<()> {
        let path = fixture_path("up_axis_absent.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        assert_eq!(stage.up_axis(), None);

        Ok(())
    }
}
