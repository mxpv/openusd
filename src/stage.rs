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
use bitflags::bitflags;

use crate::ar::{DefaultResolver, Resolver};
use crate::sdf::{FieldKey, Path, SpecType, Specifier, Value};
use crate::{layer, pcp, CompositionError};

bitflags! {
    /// Resolved stage-level status bits for a prim.
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
    pub struct PrimStatus: u32 {
        /// The prim and all ancestors are active.
        const ACTIVE = 1 << 0;
        /// The prim is loaded according to the stage's current load behavior.
        const LOADED = 1 << 1;
        /// The prim and all ancestors have defining specifiers.
        const DEFINED = 1 << 2;
        /// The prim or an ancestor has a `class` specifier.
        const ABSTRACT = 1 << 3;
        /// The prim is instanceable and has at least one composition arc.
        const INSTANCE = 1 << 4;
        /// The prim is part of the contiguous model hierarchy.
        const MODEL = 1 << 5;
    }
}

/// Predicate used to filter prim traversal by resolved status bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrimPredicate {
    required: PrimStatus,
    rejected: PrimStatus,
}

impl PrimPredicate {
    /// Status bits inherited from a prim's ancestors. Missing any of these on a
    /// parent guarantees that no descendant can have them either, enabling
    /// subtree pruning during traversal.
    const INHERITED_REQUIRED: PrimStatus = PrimStatus::ACTIVE.union(PrimStatus::LOADED).union(PrimStatus::DEFINED);

    /// Status bits that, once set on an ancestor, are inherited by every descendant.
    const INHERITED_REJECTED: PrimStatus = PrimStatus::ABSTRACT;

    /// Match every composed prim.
    pub const ALL: Self = Self::new(PrimStatus::empty(), PrimStatus::empty());

    /// OpenUSD-style default traversal predicate.
    ///
    /// Matches prims that are active, loaded, defined, and not abstract.
    pub const DEFAULT: Self = Self::new(Self::INHERITED_REQUIRED, Self::INHERITED_REJECTED);

    /// Creates a predicate with required and rejected status bits.
    pub const fn new(required: PrimStatus, rejected: PrimStatus) -> Self {
        Self { required, rejected }
    }

    /// Returns `true` if `status` satisfies the predicate.
    pub const fn matches(self, status: PrimStatus) -> bool {
        status.contains(self.required) && !status.intersects(self.rejected)
    }

    /// Returns the set of status bits this predicate actually consults.
    fn consulted_bits(self) -> PrimStatus {
        self.required.union(self.rejected)
    }

    /// Returns `true` if no descendant can satisfy this predicate.
    fn prunes_descendants(self, status: PrimStatus) -> bool {
        let required = self.required.intersection(Self::INHERITED_REQUIRED);
        if !status.contains(required) {
            return true;
        }
        status.intersects(self.rejected.intersection(Self::INHERITED_REJECTED))
    }
}

impl Default for PrimPredicate {
    fn default() -> Self {
        Self::DEFAULT
    }
}

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

    /// Returns the composed `apiSchemas` list for a prim, flattened across all
    /// contributing layer opinions.
    ///
    /// Multi-apply schema instances (e.g. `PhysicsLimitAPI:rotZ`) are included
    /// as-is; callers that need to match only the base name should strip the
    /// instance suffix themselves.
    pub fn api_schemas(&self, prim: &Path) -> Result<Vec<String>> {
        let raw = self.field::<Value>(prim, "apiSchemas")?;
        Ok(match raw {
            Some(Value::TokenListOp(op)) => op.flatten(),
            Some(Value::TokenVec(v)) => v,
            _ => Vec::new(),
        })
    }

    /// Returns `true` when `name` appears in the prim's composed `apiSchemas` list.
    ///
    /// For multi-apply schemas pass the full instance name (e.g.
    /// `"PhysicsLimitAPI:rotZ"`), not just the base name.
    pub fn has_api_schema(&self, prim: &Path, name: &str) -> Result<bool> {
        Ok(self.api_schemas(prim)?.iter().any(|s| s == name))
    }

    /// Returns the composed `typeName` for a prim, if set.
    pub fn type_name(&self, prim: &Path) -> Result<Option<String>> {
        self.field::<String>(prim, "typeName")
    }

    /// Returns the composed specifier for a prim, if one resolves.
    pub fn specifier(&self, prim: impl Into<Path>) -> Result<Option<Specifier>> {
        self.field::<Specifier>(prim.into().prim_path(), FieldKey::Specifier)
    }

    /// Returns the composed `kind` metadata for a prim, if authored.
    pub fn kind(&self, prim: impl Into<Path>) -> Result<Option<String>> {
        self.field::<String>(prim.into().prim_path(), FieldKey::Kind)
    }

    /// Returns `true` if the prim and all ancestors are active.
    ///
    /// Missing `active` opinions default to `true`; a non-existent prim returns
    /// `false`.
    pub fn is_active(&self, prim: impl Into<Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == Path::abs_root() {
            return Ok(true);
        }
        if !self.has_spec(&prim)? {
            return Ok(false);
        }
        for path in Self::prim_ancestors_inclusive(prim) {
            if self
                .field::<bool>(&path, FieldKey::Active)?
                .is_some_and(|active| !active)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns `true` if the prim is loaded.
    ///
    /// The current stage implementation has no unload rules yet, so all active
    /// prims are considered loaded. This will become load-rule aware when
    /// payload loading control is added.
    pub fn is_loaded(&self, prim: impl Into<Path>) -> Result<bool> {
        self.is_active(prim)
    }

    /// Returns `true` if the prim and all ancestors have defining specifiers.
    ///
    /// `def` and `class` are defining. `over`, missing specs, and missing
    /// specifier opinions are not defining.
    pub fn is_defined(&self, prim: impl Into<Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == Path::abs_root() {
            return Ok(true);
        }
        if !self.has_spec(&prim)? {
            return Ok(false);
        }
        for path in Self::prim_ancestors_inclusive(prim) {
            if !matches!(self.specifier(path)?, Some(Specifier::Def | Specifier::Class)) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Returns `true` if the prim or any ancestor resolves to `class`.
    pub fn is_abstract(&self, prim: impl Into<Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == Path::abs_root() || !self.has_spec(&prim)? {
            return Ok(false);
        }
        for path in Self::prim_ancestors_inclusive(prim) {
            if self.specifier(path)? == Some(Specifier::Class) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Returns `true` if the prim index contains at least one composition arc.
    pub fn has_composition_arc(&self, prim: impl Into<Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        self.try_or_handle(|cache| cache.has_composition_arc(&prim))
    }

    /// Returns `true` if `instanceable` resolves to true and the prim has a composition arc.
    pub fn is_instance(&self, prim: impl Into<Path>) -> Result<bool> {
        let prim = prim.into().prim_path();
        if prim == Path::abs_root() || !self.has_spec(&prim)? {
            return Ok(false);
        }
        if !self.field::<bool>(&prim, FieldKey::Instanceable)?.unwrap_or(false) {
            return Ok(false);
        }
        self.has_composition_arc(&prim)
    }

    /// Returns `true` if the prim is in the contiguous model hierarchy.
    ///
    /// A model prim has `kind` equal to `group`, `assembly`, or `component`.
    /// Any ancestor below the pseudo-root must have `kind` equal to `group` or
    /// `assembly`; `subcomponent` is intentionally not part of the hierarchy.
    pub fn is_model(&self, prim: impl Into<Path>) -> Result<bool> {
        Ok(self.model_kind(prim.into())?.is_some())
    }

    /// Returns `true` if the prim is a group-like model (`group` or `assembly`).
    pub fn is_group(&self, prim: impl Into<Path>) -> Result<bool> {
        Ok(matches!(self.model_kind(prim.into())?, Some("group" | "assembly")))
    }

    /// Returns `true` if the prim is a component model in a valid model hierarchy.
    pub fn is_component(&self, prim: impl Into<Path>) -> Result<bool> {
        Ok(self.model_kind(prim.into())? == Some("component"))
    }

    /// Returns `true` if the prim has `kind = "subcomponent"`.
    pub fn is_subcomponent(&self, prim: impl Into<Path>) -> Result<bool> {
        Ok(self.kind(prim)?.as_deref() == Some("subcomponent"))
    }

    /// Returns the resolved stage status bits for a prim.
    pub fn prim_status(&self, prim: impl Into<Path>) -> Result<PrimStatus> {
        self.prim_status_masked(&prim.into().prim_path(), PrimStatus::all())
    }

    /// Computes only the status bits set in `mask`. Bits outside `mask` are
    /// left unset. Used by traversal so unused checks (e.g. INSTANCE, MODEL
    /// for default traversal) are skipped.
    fn prim_status_masked(&self, prim: &Path, mask: PrimStatus) -> Result<PrimStatus> {
        let mut status = PrimStatus::empty();
        if mask.intersects(PrimStatus::ACTIVE | PrimStatus::LOADED) {
            let active = self.is_active(prim)?;
            status.set(PrimStatus::ACTIVE, active);
            status.set(PrimStatus::LOADED, active);
        }
        if mask.contains(PrimStatus::DEFINED) {
            status.set(PrimStatus::DEFINED, self.is_defined(prim)?);
        }
        if mask.contains(PrimStatus::ABSTRACT) {
            status.set(PrimStatus::ABSTRACT, self.is_abstract(prim)?);
        }
        if mask.contains(PrimStatus::INSTANCE) {
            status.set(PrimStatus::INSTANCE, self.is_instance(prim)?);
        }
        if mask.contains(PrimStatus::MODEL) {
            status.set(PrimStatus::MODEL, self.is_model(prim)?);
        }
        Ok(status)
    }

    /// Returns the model-hierarchy `kind` for the prim — `Some("group" | "assembly" | "component")`
    /// when the prim and all ancestors form a contiguous model hierarchy, else `None`.
    fn model_kind(&self, prim: Path) -> Result<Option<&'static str>> {
        let prim = prim.prim_path();
        if prim == Path::abs_root() || !self.has_spec(&prim)? {
            return Ok(None);
        }
        let leaf = match self.kind(&prim)?.as_deref() {
            Some("group") => "group",
            Some("assembly") => "assembly",
            Some("component") => "component",
            _ => return Ok(None),
        };
        let Some(parent) = prim.parent() else {
            return Ok(Some(leaf));
        };
        for ancestor in Self::prim_ancestors_inclusive(parent) {
            if !matches!(self.kind(ancestor)?.as_deref(), Some("group" | "assembly")) {
                return Ok(None);
            }
        }
        Ok(Some(leaf))
    }

    /// Iterates the prim path and its ancestors from leaf to root, stopping
    /// before the pseudo-root. Assumes `start` is already a prim path.
    fn prim_ancestors_inclusive(start: Path) -> impl Iterator<Item = Path> {
        std::iter::successors(Some(start), Path::parent).take_while(|p| *p != Path::abs_root())
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

    /// Traverses composed prims matching the default predicate.
    ///
    /// The default predicate matches OpenUSD's usual traversal region:
    /// active, loaded, defined, and not abstract.
    pub fn traverse(&self, visitor: impl FnMut(&Path)) -> Result<()> {
        self.traverse_with_predicate(PrimPredicate::DEFAULT, visitor)
    }

    /// Traverses all composed prims depth-first, calling `visitor` for each.
    pub fn traverse_all(&self, visitor: impl FnMut(&Path)) -> Result<()> {
        self.traverse_with_predicate(PrimPredicate::ALL, visitor)
    }

    /// Traverses composed prims depth-first, visiting prims that match `predicate`.
    ///
    /// Descendants are pruned when inherited status bits make it impossible for
    /// them to match, such as below inactive, unloaded, undefined, or abstract
    /// prims when the predicate excludes those regions.
    pub fn traverse_with_predicate(&self, predicate: PrimPredicate, mut visitor: impl FnMut(&Path)) -> Result<()> {
        let needed = predicate.consulted_bits();
        let mut stack = vec![Path::abs_root()];

        while let Some(path) = stack.pop() {
            if path != Path::abs_root() {
                let status = self.prim_status_masked(&path, needed)?;
                if predicate.matches(status) {
                    visitor(&path);
                }
                if predicate.prunes_descendants(status) {
                    continue;
                }
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

    /// Default traversal should visit active, loaded, defined, non-abstract prims.
    #[test]
    fn traverse_uses_default_predicate() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let mut prims = Vec::new();
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;

        assert_eq!(prims, vec!["/World", "/World/CubeActive"]);

        Ok(())
    }

    /// Exhaustive traversal should preserve raw composed hierarchy traversal.
    #[test]
    fn traverse_all_visits_every_composed_prim() -> Result<()> {
        let path = composition_path("active.usda");
        let stage = Stage::open(&path)?;

        let mut prims = Vec::new();
        stage.traverse_all(|p| prims.push(p.as_str().to_string()))?;

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

    #[test]
    fn api_schemas_returns_applied_schemas() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let geo = Path::new("/World/Geo")?;
        let schemas = stage.api_schemas(&geo)?;
        assert!(schemas.contains(&"MaterialBindingAPI".to_string()));
        assert!(schemas.contains(&"SkelBindingAPI".to_string()));
        Ok(())
    }

    #[test]
    fn api_schemas_empty_for_prim_without_schemas() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let props = Path::new("/World/Props")?;
        assert!(stage.api_schemas(&props)?.is_empty());
        Ok(())
    }

    #[test]
    fn has_api_schema_matches_applied() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        let geo = Path::new("/World/Geo")?;
        assert!(stage.has_api_schema(&geo, "MaterialBindingAPI")?);
        assert!(!stage.has_api_schema(&geo, "SkelRootAPI")?);
        Ok(())
    }

    #[test]
    fn type_name_returns_prim_type() -> Result<()> {
        let stage = Stage::open("fixtures/api_schemas.usda")?;
        assert_eq!(stage.type_name(&Path::new("/World/Geo")?)?, Some("Mesh".to_string()));
        assert_eq!(stage.type_name(&Path::new("/World")?)?, Some("Xform".to_string()));
        Ok(())
    }

    fn open_stage_queries_fixture() -> Result<Stage> {
        Stage::open("fixtures/stage_queries.usda")
    }

    #[test]
    fn active_loaded() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert!(stage.is_active("/World/ActiveParent/Child")?);
        assert!(stage.is_loaded("/World/ActiveParent/Child")?);

        assert!(!stage.is_active("/World/InactiveParent")?);
        assert!(!stage.is_active("/World/InactiveParent/Child")?);
        assert!(!stage.is_loaded("/World/InactiveParent/Child")?);

        assert!(!stage.is_active("/World/Missing")?);
        Ok(())
    }

    #[test]
    fn defined_abstract() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(stage.specifier("/World/OverOnly")?, Some(Specifier::Over));
        assert!(stage.is_defined("/World/ActiveParent/Child")?);
        assert!(!stage.is_defined("/World/OverOnly")?);
        assert!(!stage.is_defined("/World/OverParent/Child")?);

        assert!(stage.is_defined("/World/ClassParent/Child")?);
        assert!(stage.is_abstract("/World/ClassParent")?);
        assert!(stage.is_abstract("/World/ClassParent/Child")?);
        assert!(!stage.is_abstract("/World/ActiveParent/Child")?);
        Ok(())
    }

    #[test]
    fn instance_flag() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert!(stage.has_composition_arc("/World/Instance")?);
        assert!(stage.is_instance("/World/Instance")?);

        assert!(!stage.has_composition_arc("/World/InstanceableNoArc")?);
        assert!(!stage.is_instance("/World/InstanceableNoArc")?);
        Ok(())
    }

    #[test]
    fn model_hierarchy() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(stage.kind("/World")?, Some("assembly".to_string()));
        assert!(stage.is_model("/World")?);
        assert!(stage.is_group("/World")?);

        assert!(stage.is_model("/World/Group")?);
        assert!(stage.is_group("/World/Group")?);
        assert!(stage.is_model("/World/Group/Component")?);
        assert!(stage.is_component("/World/Group/Component")?);

        assert!(!stage.is_model("/World/Group/Subcomponent")?);
        assert!(stage.is_subcomponent("/World/Group/Subcomponent")?);

        assert_eq!(
            stage.kind("/World/InvalidComponentParent/Component")?,
            Some("component".to_string())
        );
        assert!(!stage.is_model("/World/InvalidComponentParent/Component")?);
        assert!(!stage.is_component("/World/InvalidComponentParent/Component")?);
        Ok(())
    }

    #[test]
    fn prim_status_bits() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        assert_eq!(
            stage.prim_status("/World/ClassParent/Child")?,
            PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::ABSTRACT
        );

        assert_eq!(
            stage.prim_status("/World/Instance")?,
            PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::INSTANCE
        );
        Ok(())
    }

    #[test]
    fn traverse_default() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        let mut prims = Vec::new();
        stage.traverse(|p| prims.push(p.as_str().to_string()))?;

        assert!(prims.contains(&"/World".to_string()));
        assert!(prims.contains(&"/World/ActiveParent".to_string()));
        assert!(prims.contains(&"/World/ActiveParent/Child".to_string()));
        assert!(prims.contains(&"/World/Instance".to_string()));

        assert!(!prims.contains(&"/World/InactiveParent".to_string()));
        assert!(!prims.contains(&"/World/InactiveParent/Child".to_string()));
        assert!(!prims.contains(&"/World/OverOnly".to_string()));
        assert!(!prims.contains(&"/World/OverParent".to_string()));
        assert!(!prims.contains(&"/World/OverParent/Child".to_string()));
        assert!(!prims.contains(&"/World/ClassParent".to_string()));
        assert!(!prims.contains(&"/World/ClassParent/Child".to_string()));
        Ok(())
    }

    #[test]
    fn traverse_all_predicate() -> Result<()> {
        let stage = open_stage_queries_fixture()?;

        let mut prims = Vec::new();
        stage.traverse_with_predicate(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

        assert!(prims.contains(&"/World/InactiveParent".to_string()));
        assert!(prims.contains(&"/World/InactiveParent/Child".to_string()));
        assert!(prims.contains(&"/World/OverOnly".to_string()));
        assert!(prims.contains(&"/World/OverParent/Child".to_string()));
        assert!(prims.contains(&"/World/ClassParent".to_string()));
        assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
        Ok(())
    }

    #[test]
    fn custom_predicate() -> Result<()> {
        let stage = open_stage_queries_fixture()?;
        let predicate = PrimPredicate::new(PrimStatus::ACTIVE | PrimStatus::DEFINED, PrimStatus::empty());

        let mut prims = Vec::new();
        stage.traverse_with_predicate(predicate, |p| prims.push(p.as_str().to_string()))?;

        assert!(prims.contains(&"/World/ClassParent".to_string()));
        assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
        assert!(!prims.contains(&"/World/InactiveParent".to_string()));
        assert!(!prims.contains(&"/World/OverOnly".to_string()));
        Ok(())
    }
}
