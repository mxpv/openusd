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
use crate::sdf::{AbstractData, Path, SpecType, Value};

/// A composed USD stage.
///
/// Owns the loaded layer stack and provides composed access to prims,
/// properties, and metadata. Layers are wrapped in [`RefCell`] to work
/// around `AbstractData::get` requiring `&mut self` (USDC lazily
/// decompresses values).
pub struct Stage {
    /// All layers, root (strongest) first.
    layers: Vec<RefCell<Box<dyn AbstractData>>>,
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
            layers.push(RefCell::new(layer.data));
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

    /// Returns the composed list of root prim names (children of the pseudo-root).
    pub fn root_prims(&self) -> Result<Vec<String>> {
        self.prim_children(&Path::abs_root())
    }

    /// Returns the composed list of child prim names for a given prim path.
    ///
    /// Merges `primChildren` across all layers that have a spec at the given
    /// path, collecting the union of child names while preserving the order
    /// from the strongest layer.
    pub fn prim_children(&self, path: &Path) -> Result<Vec<String>> {
        self.composed_children(path, ChildrenKey::PrimChildren)
    }

    /// Returns the composed list of property names for a given prim path.
    pub fn prim_properties(&self, path: &Path) -> Result<Vec<String>> {
        self.composed_children(path, ChildrenKey::PropertyChildren)
    }

    /// Returns `true` if any layer has a spec at the given composed path.
    pub fn has_spec(&self, path: &Path) -> bool {
        !self.prim_index(path).is_empty()
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub fn spec_type(&self, path: &Path) -> Option<SpecType> {
        let index = self.prim_index(path);
        for node in &index.nodes {
            let data = self.layers[node.layer_index].borrow();
            if let Some(ty) = data.spec_type(&node.path) {
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
    pub fn field<T>(&self, path: &Path, field: impl Into<&'static str>) -> Result<Option<T>>
    where
        T: TryFrom<Value>,
        T::Error: std::error::Error + Send + Sync + 'static,
    {
        let field: &str = field.into();
        let raw = if path.is_property_path() {
            self.property_field(path, field)?
        } else {
            self.resolve_field(path, field)?
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
            let mut data = self.layers[node.layer_index].borrow_mut();
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
    fn composed_children(&self, path: &Path, children_field: impl Into<&'static str>) -> Result<Vec<String>> {
        let children_field: &str = children_field.into();
        let index = self.prim_index(path);
        let mut result: Vec<String> = Vec::new();

        for node in &index.nodes {
            let mut data = self.layers[node.layer_index].borrow_mut();
            if let Ok(value) = data.get(&node.path, children_field) {
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
    /// Currently handles root/sublayer composition only. Reference, payload,
    /// inherit, variant, and specialize arcs are added incrementally.
    fn build_prim_index(&self, path: &Path) -> PrimIndex {
        let mut nodes = Vec::new();

        // Root / sublayer opinions: check each layer in strength order.
        for (i, layer) in self.layers.iter().enumerate() {
            let data = layer.borrow();
            if data.has_spec(path) {
                nodes.push(Node {
                    layer_index: i,
                    path: path.clone(),
                    arc: ArcType::Root,
                });
            }
        }

        PrimIndex { nodes }
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
    fn vendor_sublayer_same_folder() -> Result<()> {
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
    fn vendor_active_metadata() -> Result<()> {
        let path = composition_path("active.usda");
        let resolver = DefaultResolver::new();
        let stage = Stage::open(&resolver, &path)?;

        let inactive: Option<bool> = stage.field(&Path::new("/World/CubeInactive")?, FieldKey::Active)?;
        assert_eq!(inactive, Some(false));

        let active = stage.field::<bool>(&Path::new("/World/CubeActive")?, FieldKey::Active)?;
        assert_eq!(active, Some(true));

        Ok(())
    }
}
