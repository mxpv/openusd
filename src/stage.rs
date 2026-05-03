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
//! # Configuration
//!
//! Use [`StageBuilder`] to customize stage behavior before opening:
//!
//! - [`StageBuilder::resolver`] sets a custom
//!   [`Resolver`](crate::ar::Resolver) for mapping asset paths to files.
//! - [`StageBuilder::on_error`] sets a callback for recoverable composition
//!   errors (missing layers, arc cycles, etc.).
//! - [`StageBuilder::variant_fallbacks`] provides a
//!   [`VariantFallbackMap`](crate::pcp::VariantFallbackMap) with preferred
//!   selections for variant sets that have no authored opinion.
//!
//! [LIVERPS]: https://docs.nvidia.com/learn-openusd/latest/creating-composition-arcs/strength-ordering/what-is-liverps.html

use std::cell::RefCell;

use anyhow::Result;

use crate::ar::{DefaultResolver, Resolver};
use crate::sdf::{Path, SpecType, Value};
use crate::{layer, pcp, CompositionError};

/// A composed USD stage.
///
/// Owns the loaded layer stack and provides composed access to prims,
/// properties, and metadata. Composition indices are built lazily and
/// cached in the [`Cache`].
pub struct Stage {
    /// Lazily-built composition graph caching per-prim indices and contexts.
    graph: RefCell<pcp::Cache>,
    /// PCP error handler wrapping the user's unified callback.
    on_composition_error: Box<dyn Fn(pcp::Error) -> Result<()>>,
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

    /// Constructs a stage from pre-collected layers and a PCP error handler.
    ///
    /// `session_layers` are prepended at the front of the layer stack so they
    /// hold the strongest opinions (stronger than the root layer).
    fn from_layers<R: Resolver + 'static>(
        resolver: R,
        session_layers: Vec<layer::Layer>,
        root_layers: Vec<layer::Layer>,
        on_composition_error: Box<dyn Fn(pcp::Error) -> Result<()>>,
        variant_fallbacks: pcp::VariantFallbackMap,
    ) -> Self {
        let session_layer_count = session_layers.len();
        let total = session_layer_count + root_layers.len();
        let mut identifiers = Vec::with_capacity(total);
        let mut layers = Vec::with_capacity(total);

        for layer in session_layers.into_iter().chain(root_layers) {
            identifiers.push(layer.identifier);
            layers.push(layer.data);
        }

        let stack = pcp::LayerStack::new(layers, identifiers, session_layer_count, Box::new(resolver));
        Self {
            graph: RefCell::new(pcp::Cache::new(stack, variant_fallbacks)),
            on_composition_error,
        }
    }

    /// Returns the number of layers in the stage (including session layers).
    pub fn layer_count(&self) -> usize {
        self.graph.borrow().layer_count()
    }

    /// Returns the layer identifiers in strength order (session layers first,
    /// then root layer and its sublayers).
    pub fn layer_identifiers(&self) -> Vec<String> {
        self.graph.borrow().layer_identifiers().to_vec()
    }

    /// Returns `true` if the stage has a session layer.
    pub fn has_session_layer(&self) -> bool {
        self.graph.borrow().session_layer_count() > 0
    }

    /// Returns the session layer identifier, if one was provided.
    pub fn session_layer(&self) -> Option<String> {
        let cache = self.graph.borrow();
        if cache.session_layer_count() > 0 {
            Some(cache.layer_identifiers()[0].clone())
        } else {
            None
        }
    }

    /// Returns the `defaultPrim` metadata from the root layer, if set.
    ///
    /// When a session layer is present, `defaultPrim` is still read from
    /// the root layer (not the session layer), matching C++ behavior.
    pub fn default_prim(&self) -> Option<String> {
        self.graph.borrow().default_prim()
    }

    /// Returns the composed list of root prim names (children of the pseudo-root).
    pub fn root_prims(&self) -> Result<Vec<String>> {
        self.try_or_handle(|cache| cache.prim_children(&Path::abs_root()))
    }

    /// Returns the composed list of child prim names for a given prim path.
    ///
    /// Merges `primChildren` across all layers that have a spec at the given
    /// path, collecting the union of child names while preserving the order
    /// from the strongest layer.
    pub fn prim_children(&self, path: impl Into<Path>) -> Result<Vec<String>> {
        self.try_or_handle(|cache| cache.prim_children(&path.into()))
    }

    /// Returns the composed list of property names for a given prim path.
    pub fn prim_properties(&self, path: impl Into<Path>) -> Result<Vec<String>> {
        self.try_or_handle(|cache| cache.prim_properties(&path.into()))
    }

    /// Returns `true` if any layer has a spec at the given composed path.
    ///
    /// For property paths (e.g. `/Prim.attr`), checks whether the property
    /// exists in any layer contributing to the owning prim's composition index.
    pub fn has_spec(&self, path: impl Into<Path>) -> Result<bool> {
        self.try_or_handle(|cache| cache.has_spec(&path.into()))
    }

    /// Returns the spec type at a composed path from the strongest contributing layer.
    pub fn spec_type(&self, path: impl Into<Path>) -> Result<Option<SpecType>> {
        self.try_or_handle(|cache| cache.spec_type(&path.into()))
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
        let raw = self.try_or_handle(|cache| cache.resolve_field(&path.into(), field.as_ref()))?;
        match raw {
            Some(value) => Ok(Some(T::try_from(value)?)),
            None => Ok(None),
        }
    }

    /// Calls `f` with a mutable reference to the composition cache. If `f`
    /// returns a [`pcp::Error`], the error handler decides whether to skip
    /// (returning a default value) or abort (propagating the error).
    fn try_or_handle<T: Default>(&self, f: impl FnOnce(&mut pcp::Cache) -> Result<T>) -> Result<T> {
        match f(&mut self.graph.borrow_mut()) {
            Ok(val) => Ok(val),
            Err(e) => match e.downcast::<pcp::Error>() {
                Ok(pcp_err) => {
                    (self.on_composition_error)(pcp_err)?;
                    Ok(T::default())
                }
                Err(other) => Err(other),
            },
        }
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

            let children = self.try_or_handle(|cache| cache.prim_children(&path))?;
            // Push in reverse so first child is visited first.
            for name in children.iter().rev() {
                if let Ok(child) = path.append_path(name.as_str()) {
                    stack.push(child);
                }
            }
        }

        Ok(())
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
    variant_fallbacks: pcp::VariantFallbackMap,
    session_layer: Option<String>,
}

impl StageBuilder {
    fn new() -> Self {
        Self {
            resolver: DefaultResolver::new(),
            on_error: strict_composition_error,
            variant_fallbacks: pcp::VariantFallbackMap::new(),
            session_layer: None,
        }
    }
}

impl<R: Resolver, E: Fn(CompositionError) -> Result<()>> StageBuilder<R, E> {
    /// Sets a custom asset resolver.
    pub fn resolver<R2: Resolver>(self, resolver: R2) -> StageBuilder<R2, E> {
        StageBuilder {
            resolver,
            on_error: self.on_error,
            variant_fallbacks: self.variant_fallbacks,
            session_layer: self.session_layer,
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
            variant_fallbacks: self.variant_fallbacks,
            session_layer: self.session_layer,
        }
    }

    /// Sets the session layer for the stage.
    ///
    /// The session layer provides the strongest opinions in the composition,
    /// stronger than even the root layer. It is typically used for temporary,
    /// non-persistent overrides such as variant selections, visibility toggles,
    /// or LOD settings.
    ///
    /// The session layer and its sublayers are collected and prepended to the
    /// layer stack before the root layer.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::Stage;
    ///
    /// let stage = Stage::builder()
    ///     .session_layer("session.usda")
    ///     .open("scene.usda")
    ///     .unwrap();
    ///
    /// assert!(stage.has_session_layer());
    /// ```
    pub fn session_layer(mut self, path: impl Into<String>) -> Self {
        self.session_layer = Some(path.into());
        self
    }

    /// Sets the variant fallback map for the stage.
    ///
    /// When a prim has a variant set but no authored selection, the
    /// composition engine tries each fallback in order. The first fallback
    /// matching an existing variant in the set is used; if none match, the
    /// first variant in the set is used as default.
    ///
    /// # Example
    ///
    /// ```no_run
    /// use openusd::Stage;
    /// use openusd::pcp::VariantFallbackMap;
    ///
    /// let fallbacks = VariantFallbackMap::new()
    ///     .add("shadingComplexity", ["full", "simple"]);
    ///
    /// let stage = Stage::builder()
    ///     .variant_fallbacks(fallbacks)
    ///     .open("scene.usda")
    ///     .unwrap();
    /// ```
    pub fn variant_fallbacks(mut self, fallbacks: pcp::VariantFallbackMap) -> Self {
        self.variant_fallbacks = fallbacks;
        self
    }

    /// Opens a stage from a root layer file.
    pub fn open(self, root_path: &str) -> Result<Stage>
    where
        R: 'static,
        E: 'static,
    {
        let on_error = self.on_error;
        let variant_fallbacks = self.variant_fallbacks;

        // Collect session layers first (if any), then root layers.
        let session_layers = if let Some(ref session_path) = self.session_layer {
            layer::collect_layers_with_handler(&self.resolver, session_path, |e| on_error(CompositionError::Layer(e)))?
        } else {
            Vec::new()
        };

        let root_layers =
            layer::collect_layers_with_handler(&self.resolver, root_path, |e| on_error(CompositionError::Layer(e)))?;

        let pcp_handler = Box::new(move |e: pcp::Error| on_error(CompositionError::Pcp(e)));
        Ok(Stage::from_layers(
            self.resolver,
            session_layers,
            root_layers,
            pcp_handler,
            variant_fallbacks,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::schema::FieldKey;

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
        let base_red = Value::Vec3fVec(vec![[1.0, 0.0, 0.0]]);
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
        assert!(stage.has_spec("/World/MyPrim")?);

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
        let green = Value::Vec3fVec(vec![[0.0, 0.8, 0.0]]);
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
        let red = Value::Vec3fVec(vec![[0.8, 0.0, 0.0]]);
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

    // --- Variant fallback selection ---

    /// A variant fallback should select the specified variant when no authored
    /// selection exists. The prim should expose opinions from the fallback variant.
    #[test]
    fn variant_fallback_selects_preferred() -> Result<()> {
        let path = fixture_path("variant_fallback.usda");
        let fallbacks = crate::pcp::VariantFallbackMap::new().add("shadingComplexity", ["simple"]);
        let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

        // /NoSelection has no authored selection. With fallback "simple",
        // the complexity field should be 0.5 (not 1.0 from "full").
        let prop = Path::new("/NoSelection")?.append_property("complexity")?;
        let value = stage.field::<f64>(&prop, FieldKey::Default)?;
        assert_eq!(value, Some(0.5), "fallback 'simple' should give complexity=0.5");

        Ok(())
    }

    /// An authored selection should take priority over a variant fallback at the
    /// stage level.
    #[test]
    fn variant_fallback_does_not_override_authored() -> Result<()> {
        let path = fixture_path("variant_fallback.usda");
        let fallbacks = crate::pcp::VariantFallbackMap::new().add("shadingComplexity", ["none"]);
        let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

        // /Root has authored selection "full". Even with fallback "none",
        // the authored selection should win.
        let prop = Path::new("/Root")?.append_property("complexity")?;
        let value = stage.field::<f64>(&prop, FieldKey::Default)?;
        assert_eq!(value, Some(1.0), "authored 'full' should win over fallback 'none'");

        Ok(())
    }

    // --- Inherit child propagation ---

    /// A prim that inherits a class should expose the class's children even
    /// when the inheriting prim has no local override for them.
    #[test]
    fn inherit_child_exists_without_local_override() -> Result<()> {
        let path = fixture_path("inherit_child_propagation.usda");
        let stage = Stage::open(&path)?;

        // /Instance inherits /BaseClass which has child /BaseClass/Child.
        // /Instance/Child should exist even though Instance has no local "Child".
        let children = stage.prim_children("/Instance")?;
        assert!(
            children.contains(&"Child".to_string()),
            "inherited child should appear: got {children:?}"
        );

        // The inherited property should be accessible.
        assert!(
            stage.has_spec(Path::new("/Instance/Child.name")?)?,
            "property from inherited child should be visible"
        );

        Ok(())
    }

    /// Nested children from an inherited class should propagate through
    /// multiple levels even without local overrides at any level.
    #[test]
    fn inherit_nested_child_propagation() -> Result<()> {
        let path = fixture_path("inherit_nested_child.usda");
        let stage = Stage::open(&path)?;

        // /Prim inherits /Base. /Base/A/B exists with val=1.0.
        // /Prim/A should exist, /Prim/A/B should exist.
        let a_children = stage.prim_children("/Prim")?;
        assert!(
            a_children.contains(&"A".to_string()),
            "first-level child: got {a_children:?}"
        );

        let b_children = stage.prim_children("/Prim/A")?;
        assert!(
            b_children.contains(&"B".to_string()),
            "second-level child: got {b_children:?}"
        );

        assert!(
            stage.has_spec(Path::new("/Prim/A/B.val")?)?,
            "deeply nested inherited property should be visible"
        );

        Ok(())
    }

    /// Children should propagate through an inherit chain (Leaf → Middle → GrandBase).
    #[test]
    fn inherit_chain_child_propagation() -> Result<()> {
        let path = fixture_path("inherit_chain_child.usda");
        let stage = Stage::open(&path)?;

        // /Leaf inherits /Middle which inherits /GrandBase.
        // /GrandBase/Deep exists with x=42. /Leaf/Deep should exist.
        let children = stage.prim_children("/Leaf")?;
        assert!(
            children.contains(&"Deep".to_string()),
            "chain-inherited child: got {children:?}"
        );

        assert!(
            stage.has_spec(Path::new("/Leaf/Deep.x")?)?,
            "property from chain-inherited child should be visible"
        );

        Ok(())
    }

    // --- Session layer ---

    /// Opens a stage with session_layer.usda over session_root.usda.
    fn open_with_session() -> Result<Stage> {
        let root = fixture_path("session_root.usda");
        let session = fixture_path("session_layer.usda");
        Stage::builder().session_layer(&session).open(&root)
    }

    /// A stage opened without a session layer should report no session layer.
    #[test]
    fn no_session_layer_by_default() -> Result<()> {
        let stage = Stage::open(&fixture_path("session_root.usda"))?;

        assert!(!stage.has_session_layer());
        assert_eq!(stage.session_layer(), None);
        assert_eq!(stage.layer_count(), 1);

        Ok(())
    }

    /// A session layer's opinions should be stronger than the root layer's.
    #[test]
    fn session_layer_opinion_wins() -> Result<()> {
        let stage = open_with_session()?;

        assert!(stage.has_session_layer());
        assert_eq!(stage.layer_count(), 2);

        let prop = Path::new("/World")?.append_property("radius")?;
        let value = stage.field::<f64>(&prop, FieldKey::Default)?;
        assert_eq!(value, Some(99.0), "session layer opinion should win");

        Ok(())
    }

    /// The session layer can add properties not present in the root layer.
    #[test]
    fn session_layer_adds_properties() -> Result<()> {
        let stage = open_with_session()?;

        let prop = Path::new("/World")?.append_property("visibility")?;
        let value = stage.field::<String>(&prop, FieldKey::Default)?;
        assert_eq!(value, Some("hidden".to_string()));

        Ok(())
    }

    /// The root layer's properties not overridden by the session layer
    /// should still be accessible.
    #[test]
    fn session_layer_preserves_root_opinions() -> Result<()> {
        let stage = open_with_session()?;

        let prop = Path::new("/World")?.append_property("name")?;
        let value = stage.field::<String>(&prop, FieldKey::Default)?;
        assert_eq!(value, Some("root".to_string()));

        Ok(())
    }

    /// `defaultPrim` should come from the root layer, not the session layer.
    #[test]
    fn session_layer_does_not_affect_default_prim() -> Result<()> {
        let stage = open_with_session()?;
        assert_eq!(stage.default_prim(), Some("World".to_string()));
        Ok(())
    }

    /// Children defined only in the root layer should still be visible
    /// when a session layer is present.
    #[test]
    fn session_layer_preserves_children() -> Result<()> {
        let stage = open_with_session()?;

        let children = stage.prim_children("/World")?;
        assert!(
            children.contains(&"Child".to_string()),
            "root layer's children should be visible: got {children:?}"
        );

        Ok(())
    }
}
