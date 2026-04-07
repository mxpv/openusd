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

use crate::ar::{DefaultResolver, Resolver};
use crate::compose;
use crate::compose::prim_index::PrimIndex;
use crate::compose::CompositionError;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{LayerData, Path, SpecType, Value};

/// A composed USD stage.
///
/// Owns the loaded layer stack and provides composed access to prims,
/// properties, and metadata.
pub struct Stage {
    /// All layers, root (strongest) first.
    layers: Vec<LayerData>,
    /// Layer identifiers, parallel to `layers`.
    identifiers: Vec<String>,
    /// Cached prim indices, built lazily per prim.
    prim_indices: RefCell<HashMap<Path, PrimIndex>>,
}

impl Stage {
    /// Opens a stage from a root layer file using the [`DefaultResolver`].
    ///
    /// Any unresolvable transitive dependency causes an immediate error.
    /// For custom resolver or error handling, use [`Stage::builder`].
    pub fn open(root_path: &str) -> Result<Self> {
        Self::builder().open(root_path)
    }

    /// Creates a [`StageBuilder`] for configuring how the stage is opened.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::Stage;
    ///
    /// let stage = Stage::builder()
    ///     .on_error(|err| {
    ///         eprintln!("warning: {err}");
    ///         Ok(())
    ///     })
    ///     .open("scene.usda")
    ///     .unwrap();
    /// ```
    pub fn builder() -> StageBuilder<DefaultResolver> {
        StageBuilder::new()
    }

    /// Constructs a stage from pre-collected layers.
    fn from_layers(collected: Vec<compose::Layer>) -> Self {
        let mut identifiers = Vec::with_capacity(collected.len());
        let mut layers = Vec::with_capacity(collected.len());

        for layer in collected {
            identifiers.push(layer.identifier);
            layers.push(layer.data);
        }

        Self {
            layers,
            identifiers,
            prim_indices: RefCell::new(HashMap::new()),
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

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    pub fn default_prim(&self) -> Option<String> {
        self.field::<String>(&Path::abs_root(), FieldKey::DefaultPrim).ok()?
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
        let path = path.into();
        self.update_index(&path);
        let cache = self.prim_indices.borrow();
        !cache[&path].is_empty()
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub fn spec_type(&self, path: impl Into<Path>) -> Option<SpecType> {
        let path = path.into();
        self.update_index(&path);
        let cache = self.prim_indices.borrow();
        for node in &cache[&path].nodes {
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
        self.update_index(path);
        let cache = self.prim_indices.borrow();
        cache[path].resolve_field(field, &self.layers, |node| Ok(node.path.clone()))
    }

    /// Resolves a field on a property spec (attribute or relationship).
    ///
    /// Uses the owning prim's index to determine layer ordering, then builds
    /// the property path within each layer and queries for the field.
    fn property_field(&self, prop_path: &Path, field: &str) -> Result<Option<Value>> {
        let prim_path = prop_path.prim_path();
        let prop_suffix = &prop_path.as_str()[prim_path.as_str().len()..];
        self.update_index(&prim_path);
        let cache = self.prim_indices.borrow();
        cache[&prim_path].resolve_field(field, &self.layers, |node| {
            Path::new(&format!("{}{prop_suffix}", node.path))
        })
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

    /// Ensures the prim index for `path` is built and cached.
    fn update_index(&self, path: &Path) {
        if self.prim_indices.borrow().contains_key(path) {
            return;
        }
        let index = PrimIndex::build(path, &self.layers, &self.identifiers);
        self.prim_indices.borrow_mut().insert(path.clone(), index);
    }

    /// Merges a children field (e.g. `primChildren`, `properties`) across all
    /// nodes in the prim index, returning the union with strongest-first ordering.
    fn composed_children(&self, path: &Path, children_field: impl AsRef<str>) -> Result<Vec<String>> {
        let children_field: &str = children_field.as_ref();
        self.update_index(path);
        let cache = self.prim_indices.borrow();
        let mut result: Vec<String> = Vec::new();

        for node in &cache[path].nodes {
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
}

/// Default composition error handler that treats all errors as fatal.
type StrictErrorHandler = fn(CompositionError) -> Result<()>;

/// Converts a composition error into a hard failure.
fn strict_composition_error(e: CompositionError) -> Result<()> {
    Err(anyhow::anyhow!("{e}"))
}

/// Builder for configuring and opening a [`Stage`].
///
/// Created via [`Stage::builder`]. Allows setting a custom asset resolver
/// and an error handler for recoverable composition failures.
pub struct StageBuilder<R: Resolver = DefaultResolver, E: Fn(CompositionError) -> Result<()> = StrictErrorHandler> {
    resolver: R,
    on_error: E,
}

impl StageBuilder {
    fn new() -> Self {
        Self {
            resolver: DefaultResolver::new(),
            on_error: strict_composition_error,
        }
    }
}

impl<R: Resolver, E: Fn(CompositionError) -> Result<()>> StageBuilder<R, E> {
    /// Sets a custom asset resolver.
    pub fn resolver<R2: Resolver>(self, resolver: R2) -> StageBuilder<R2, E> {
        StageBuilder {
            resolver,
            on_error: self.on_error,
        }
    }

    /// Sets a callback invoked when a recoverable composition error occurs.
    ///
    /// Return `Ok(())` to skip the problematic dependency and continue,
    /// or `Err(...)` to abort composition.
    ///
    /// By default, all composition errors are fatal.
    pub fn on_error<E2: Fn(CompositionError) -> Result<()>>(self, handler: E2) -> StageBuilder<R, E2> {
        StageBuilder {
            resolver: self.resolver,
            on_error: handler,
        }
    }

    /// Opens a stage from a root layer file.
    pub fn open(self, root_path: &str) -> Result<Stage> {
        let collected = compose::collect_layers_with_handler(&self.resolver, root_path, self.on_error)?;
        Ok(Stage::from_layers(collected))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    // --- Basic stage opening (vendor/usd-wg-assets) ---

    /// A single-layer .usda file should load with correct defaultPrim and
    /// root prim list.
    #[test]
    fn open_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        assert_eq!(stage.layer_count(), 1);
        assert_eq!(stage.default_prim(), Some("World".to_string()));
        assert_eq!(stage.root_prims()?, vec!["World"]);

        Ok(())
    }

    /// Traverse should visit all prims depth-first.
    #[test]
    fn traverse_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let mut prims = Vec::new();
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;

        assert_eq!(prims, vec!["/World", "/World/CubeInactive", "/World/CubeActive"]);

        Ok(())
    }

    /// Reading a field from a single-layer stage should return the authored value.
    #[test]
    fn field_single_layer() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        // The "active" metadata on CubeInactive should be false.
        let active = stage.field::<bool>("/World/CubeInactive", FieldKey::Active)?;
        assert_eq!(active, Some(false));

        // CubeActive has active = true.
        let active = stage.field::<bool>("/World/CubeActive", FieldKey::Active)?;
        assert_eq!(active, Some(true));

        Ok(())
    }

    /// Querying a field that isn't authored should return None.
    #[test]
    fn field_not_authored() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let active = stage.field::<Value>("/World", FieldKey::Active)?;
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
        let stage = Stage::open(&path)?;

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
        let stage = Stage::open(&path)?;

        let children = stage.prim_children("/World")?;
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
        let stage = Stage::open(&path)?;

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
        let stage = Stage::open(&path)?;

        let inactive: Option<bool> = stage.field("/World/CubeInactive", FieldKey::Active)?;
        assert_eq!(inactive, Some(false));

        let active = stage.field::<bool>("/World/CubeActive", FieldKey::Active)?;
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
        let stage = Stage::open(&path)?;

        // /World/MyPrim should exist via the reference.
        assert!(stage.has_spec("/World/MyPrim"));

        // /World/MyPrim/Child should be reachable via namespace remapping.
        let children = stage.prim_children("/World/MyPrim")?;
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
        let stage = Stage::open(&path)?;

        // /World references _stage.usda's defaultPrim ("World"),
        // so /World/Cube should come from the referenced layer.
        let children = stage.prim_children("/World")?;
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
        let stage = Stage::open(&path)?;

        // /Source/Child in ref_target.usda should appear as /World/RefPrim/Child.
        let children = stage.prim_children("/World/RefPrim")?;
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
        let stage = Stage::open(&path)?;

        // The inherited property should be visible.
        let props = stage.prim_properties("/World/cubeWithoutSetColor")?;
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
        let stage = Stage::open(&path)?;

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

    /// The local opinion on radius (1) should be stronger than the variant's (2).
    #[test]
    fn variant_local_opinion_wins() -> Result<()> {
        let path = format!(
            "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
            manifest_dir()
        );
        let stage = Stage::open(&path)?;

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
        let stage = Stage::open(&path)?;

        // The payload target layer has /World/Cube. Since /World is the payload
        // target, /World/Cube should appear.
        let children = stage.prim_children("/World")?;
        assert!(
            children.contains(&"Cube".to_string()),
            "Cube from payload layer should appear under /World"
        );

        Ok(())
    }

    // --- Specialize composition ---

    /// The local opinion on displayColor (yellow) should win over the
    /// specialized source's displayColor (red).
    #[test]
    fn specialize_local_opinion_wins() -> Result<()> {
        let path = composition_path("inherit_and_specialize.usda");
        let stage = Stage::open(&path)?;

        let prop = Path::new("/World/cubeScene/specializes")?.append_property("primvars:displayColor")?;
        let value: Option<Value> = stage.field(&prop, FieldKey::Default)?;
        assert!(value.is_some());

        // Local is yellow (0.8, 0.8, 0), source is red (0.8, 0, 0).
        let red = Value::Vec3f(vec![0.8, 0.0, 0.0]);
        assert_ne!(value.unwrap(), red, "local opinion should win over specialized");

        Ok(())
    }

    /// A prim with `instanceable = true` should parse without error, and the
    /// `instanceable` field should be readable via `stage.field()`.
    #[test]
    fn instanceable_true_parses_and_is_readable() -> Result<()> {
        let path = fixture_path("instanceable_metadata.usda");
        let stage = Stage::open(&path)?;

        let value = stage.field::<bool>("/Root/InstancePrototype", FieldKey::Instanceable)?;
        assert_eq!(value, Some(true), "instanceable = true should be stored");

        Ok(())
    }

    /// A prim with `instanceable = false` should also parse correctly.
    #[test]
    fn instanceable_false_parses_and_is_readable() -> Result<()> {
        let path = fixture_path("instanceable_metadata.usda");
        let stage = Stage::open(&path)?;

        let value = stage.field::<bool>("/Root/NotInstanceable", FieldKey::Instanceable)?;
        assert_eq!(value, Some(false), "instanceable = false should be stored");

        Ok(())
    }

    /// A prim without `instanceable` metadata should return None.
    #[test]
    fn instanceable_absent_returns_none() -> Result<()> {
        let path = fixture_path("instanceable_metadata.usda");
        let stage = Stage::open(&path)?;

        let value = stage.field::<bool>("/Root", FieldKey::Instanceable)?;
        assert_eq!(value, None, "instanceable should be None when not authored");

        Ok(())
    }
}
