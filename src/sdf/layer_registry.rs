//! Layer loading and the format registry.
//!
//! [`LayerRegistry`] owns the [`ar::Resolver`] and load policy a stage opens
//! layers with, and dispatches through the built-in format set
//! ([`find_by_extension`](LayerRegistry::find_by_extension) /
//! [`find_by_id`](LayerRegistry::find_by_id)) to the
//! [`FileFormat`](super::FileFormat) claiming each layer's extension. It is the
//! Rust seam for C++ `Sdf_LayerRegistry` and `SdfFileFormat::FindByExtension`:
//! a future `find_or_open` cache (the registry will own loaded layers and dedup
//! them) and custom format registration grow here.
//!
//! References and payloads are not followed here. Composition opens each
//! reference/payload target layer on demand when it reaches the arc (see
//! [`crate::pcp`]), so an un-visited subtree never loads its layers. Only the
//! sublayer stack is opened eagerly, since a layer's sublayers contribute
//! opinions to its own namespace and so must be present whenever the layer is
//! (spec 10.3.1.1).

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use anyhow::{bail, Context, Result};

use crate::ar;
use crate::sdf::{self, expr};
use crate::usda::UsdaFileFormat;
use crate::usdc::UsdcFileFormat;
use crate::usdz::UsdzFileFormat;

static USDA: UsdaFileFormat = UsdaFileFormat;
static USDC: UsdcFileFormat = UsdcFileFormat;
static USDZ: UsdzFileFormat = UsdzFileFormat;

/// The built-in formats, in lookup order — the Rust analog of C++
/// `SdfFileFormat`'s static plugin set. Custom formats will register alongside
/// these on a [`LayerRegistry`] in the future; today the set is fixed.
static DEFAULT_FORMATS: &[&dyn sdf::FileFormat] = &[&USDA, &USDC, &USDZ];

/// An error encountered while opening a layer's sublayer stack that may be
/// recoverable.
///
/// A missing sublayer can be tolerated so loading continues; the `on_error`
/// callback passed to [`LayerRegistry::open_stack`] configures that policy.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum Error {
    /// A sublayer asset path could not be resolved to a physical location.
    #[error("failed to resolve sublayer asset: {asset_path} (referenced by {referencing_layer})")]
    UnresolvedAsset {
        /// The sublayer asset path that could not be resolved.
        asset_path: String,
        /// The layer that declared the sublayer.
        referencing_layer: String,
    },

    /// A sublayer resolved to a physical location but could not be read or
    /// parsed. Only the bad sublayer is dropped; the layer that declared it (and
    /// the rest of the stack) still loads, matching C++ `SdfLayer`, which opens
    /// the parent and reports the unreadable sublayer.
    #[error("failed to read sublayer asset: {asset_path} (referenced by {referencing_layer}): {reason}")]
    UnreadableAsset {
        /// The sublayer asset path that resolved but could not be read.
        asset_path: String,
        /// The layer that declared the sublayer.
        referencing_layer: String,
        /// The underlying read or parse error.
        reason: String,
    },
}

/// Owns layer loading for a stage: the [`ar::Resolver`] that finds and opens
/// layers, the built-in [format set](DEFAULT_FORMATS), and whether payload arcs
/// are expanded.
///
/// The [`LayerGraph`](crate::pcp::LayerGraph) holds one and opens reference and
/// payload targets on demand through it. The resolver is private — every path
/// that resolves and reads a layer is a method here, so no caller juggles the
/// resolver itself. This is the Rust analog of C++ `Sdf_LayerRegistry`; it will
/// grow a ref-counted loaded-layer cache (`find_or_open` dedup) and custom
/// format registration.
pub struct LayerRegistry {
    resolver: Box<dyn ar::Resolver>,
}

impl Default for LayerRegistry {
    /// A registry over the filesystem [`DefaultResolver`](ar::DefaultResolver)
    /// and the built-in formats — what [`Stage::builder`](crate::usd::Stage)
    /// uses unless a registry is configured.
    fn default() -> Self {
        Self::new(Box::new(ar::DefaultResolver::new()))
    }
}

impl LayerRegistry {
    /// A registry resolving asset paths through `resolver`.
    pub fn new(resolver: Box<dyn ar::Resolver>) -> Self {
        Self { resolver }
    }

    /// Canonicalizes `asset_path` into a stable identifier, anchoring a relative
    /// path against `anchor`. The registry's resolution surface — the underlying
    /// [`ar::Resolver`] stays private so callers reach it only through here.
    pub(crate) fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
        self.resolver.create_identifier(asset_path, anchor)
    }

    /// Resolves `asset_path` against `anchor_identifier` — the identifier of the
    /// layer it is authored in — yielding the canonical identifier of the
    /// targeted layer. The convenience over [`create_identifier`](Self::create_identifier)
    /// for the common case of anchoring against another layer's identifier
    /// string rather than a pre-resolved [`ar::ResolvedPath`].
    ///
    /// TODO(perf): the resolver canonicalizes via the filesystem, so each call
    /// runs a `canonicalize`. Cache resolved identifiers per
    /// `(anchor_identifier, asset_path)`.
    pub(crate) fn create_identifier_anchored(&self, asset_path: &str, anchor_identifier: &str) -> String {
        self.create_identifier(
            asset_path,
            Some(&ar::ResolvedPath::new(PathBuf::from(anchor_identifier))),
        )
    }

    /// Resolves an asset identifier to a physical location, or `None` if it does
    /// not exist.
    pub(crate) fn resolve(&self, identifier: &str) -> Option<ar::ResolvedPath> {
        self.resolver.resolve(identifier)
    }

    /// The resolver's [`identity`](ar::Resolver::identity) token — the
    /// configuration the stack's asset paths resolve under.
    pub(crate) fn identity(&self) -> String {
        self.resolver.identity()
    }

    /// Find the format claiming `ext` (without the leading dot, case-insensitive),
    /// e.g. `"usda"` or `"usd"`. C++ `SdfFileFormat::FindByExtension`.
    pub fn find_by_extension(ext: &str) -> Option<&'static dyn sdf::FileFormat> {
        DEFAULT_FORMATS
            .iter()
            .copied()
            .find(|f| f.extensions().iter().any(|e| e.eq_ignore_ascii_case(ext)))
    }

    /// Find the format with the given [`format_id`](sdf::FileFormat::format_id),
    /// e.g. `"usdc"`. C++ `SdfFileFormat::FindById`.
    pub fn find_by_id(id: &str) -> Option<&'static dyn sdf::FileFormat> {
        DEFAULT_FORMATS.iter().copied().find(|f| f.format_id() == id)
    }

    /// Resolves `identifier` and opens the layer there in its file format, or
    /// `None` when it does not resolve. Used for value-clip and manifest layers,
    /// which compose outside the layer graph (spec 12.3.4).
    pub(crate) fn open(&self, identifier: &str) -> Result<Option<sdf::LayerData>> {
        match self.resolver.resolve(identifier) {
            Some(resolved) => self.read(&resolved).map(Some),
            None => Ok(None),
        }
    }

    /// Opens `asset_path` (anchored against `anchor`) together with its sublayer
    /// stack, root (strongest) layer first.
    ///
    /// Following stops at references and payloads: composition opens those target
    /// layers on demand when it reaches the arc, so an un-visited subtree never
    /// loads them. Only `subLayers` edges are walked, since a layer's sublayer
    /// stack contributes opinions to its own namespace and so must be present
    /// whenever the layer is (spec 10.3.1.1). `already_present` reports whether a
    /// layer (by canonical identifier) is already loaded, so a sublayer shared
    /// with the graph is neither re-read nor re-emitted.
    ///
    /// The root must resolve and read — its failure propagates as `Err`. A
    /// sublayer that fails to resolve, or that resolves but cannot be read, is
    /// routed to `on_error` and skipped, so one bad sublayer never fails the
    /// whole stack (C++ `SdfLayer` opens the root and reports the bad sublayer).
    ///
    /// `ancestor_expr_vars` are the expression variables composed by the stack
    /// that brought `asset_path` in (empty for the stage root stack, the
    /// referencing stack's composed set for a reference/payload target). They
    /// overlay the root's own `expressionVariables` — the ancestor, closer to the
    /// composed root, wins — and thread down the sublayer stack to evaluate its
    /// expression-valued `subLayers` paths.
    pub(crate) fn open_stack(
        &self,
        asset_path: &str,
        anchor: Option<&ar::ResolvedPath>,
        ancestor_expr_vars: &HashMap<String, sdf::Value>,
        on_error: &dyn Fn(Error) -> Result<()>,
        already_present: &dyn Fn(&str) -> bool,
    ) -> Result<Vec<sdf::Layer>> {
        let mut layers = Vec::new();
        let mut visited = HashSet::new();

        let identifier = self.resolver.create_identifier(asset_path, anchor);
        if identifier.is_empty() || already_present(&identifier) {
            return Ok(layers);
        }
        // The root must resolve and read; both failures propagate.
        let resolved = self
            .resolver
            .resolve(&identifier)
            .with_context(|| format!("failed to resolve asset path: {asset_path}"))?;
        let data = self.read(&resolved)?;
        visited.insert(identifier.clone());

        self.open_sublayers(
            identifier,
            resolved,
            data,
            ancestor_expr_vars,
            on_error,
            already_present,
            &mut visited,
            &mut layers,
        )?;
        Ok(layers)
    }

    /// Opens the layer at `resolved`, dispatching to the registered format for
    /// its extension. The `.usd` extension is the one ambiguous case — binary
    /// crate or text — so it peeks the leading bytes and chooses by
    /// [`matches_content`](sdf::FileFormat::matches_content) (the crate magic),
    /// falling back to text. C++ `SdfFileFormat::FindByExtension` + `CanRead`.
    fn read(&self, resolved: &ar::ResolvedPath) -> Result<sdf::LayerData> {
        let ext = resolved.extension();
        let format = if ext.eq_ignore_ascii_case("usd") {
            // TODO(perf): the chosen format re-opens the asset in `read`; only
            // `.usd` peeks, so fold the peek into one read once `FileFormat::read`
            // can take already-read bytes.
            let prefix = self.read_prefix(resolved)?;
            DEFAULT_FORMATS
                .iter()
                .copied()
                .find(|f| f.matches_content(&prefix))
                .or_else(|| Self::find_by_id("usda"))
        } else {
            Self::find_by_extension(&ext)
        };
        format
            .ok_or_else(|| anyhow::anyhow!("no file format registered for {resolved}"))?
            .read(self.resolver.as_ref(), resolved)
    }

    /// Reads the leading bytes of `resolved` for content-based format detection.
    fn read_prefix(&self, resolved: &ar::ResolvedPath) -> Result<Vec<u8>> {
        use std::io::Read;
        let mut asset = self.resolver.open_asset(resolved)?;
        let mut prefix = Vec::new();
        asset.by_ref().take(8).read_to_end(&mut prefix)?;
        Ok(prefix)
    }

    /// Emits an already-read layer and recursively opens its sublayers.
    ///
    /// `identifier`, `resolved`, and `data` are this layer's canonical
    /// identifier, resolved location, and parsed contents — read by the caller
    /// (the root in [`open_stack`](Self::open_stack), each sublayer in the loop
    /// below) so a sublayer's read failure is routed to `on_error` while the
    /// root's propagates.
    ///
    /// `ancestor_expr_vars` are the expression variables composed from the layers
    /// that sublayer this one (empty at the root). They are applied over this
    /// layer's own `expressionVariables` so a closer-to-root layer's override
    /// wins (C++ `PcpExpressionVariables`); the combined set drives expression
    /// evaluation in this layer's sublayer paths and is threaded into each one.
    #[allow(clippy::too_many_arguments)]
    fn open_sublayers(
        &self,
        identifier: String,
        resolved: ar::ResolvedPath,
        data: sdf::LayerData,
        ancestor_expr_vars: &HashMap<String, sdf::Value>,
        on_error: &dyn Fn(Error) -> Result<()>,
        already_present: &dyn Fn(&str) -> bool,
        visited: &mut HashSet<String>,
        layers: &mut Vec<sdf::Layer>,
    ) -> Result<()> {
        // Compose this layer's authored expression variables with those inherited
        // from the layers that sublayer it; the inherited (closer-to-root) set is
        // applied last so it overrides this layer's own (C++ `PcpExpressionVariables`).
        let mut expr_vars = expr::read_expression_variables(data.as_ref())?.into_owned();
        expr::compose_over(&mut expr_vars, ancestor_expr_vars);

        let is_usdz = resolved.extension() == "usdz";
        let sub_paths = Self::sublayer_paths(data.as_ref());

        // Emit this layer ahead of its sublayers so the collected stack is
        // strongest-first: a layer overrides the layers it sublayers, and earlier
        // entries in a `subLayers` list override later ones (spec 10.3.1.1).
        layers.push(sdf::Layer::new(identifier.clone(), data));

        // A layer inside a `.usdz` package cannot reach a sibling layer within the
        // archive (not yet supported), so a usdz layer declaring any sublayers
        // fails the open.
        if is_usdz && !sub_paths.is_empty() {
            bail!(
                "cross-file references within USDZ archives are not yet supported: {}",
                resolved
            );
        }

        for sub_path in sub_paths {
            // Evaluate the (possibly expression-valued) sublayer path. An
            // unevaluable expression drops only this sublayer — like an unresolved
            // or unreadable one — rather than failing the whole stack open.
            let sub_asset = match expr::evaluate_asset_path(&sub_path, &expr_vars) {
                Ok(evaluated) => evaluated,
                Err(reason) => {
                    on_error(Error::UnreadableAsset {
                        asset_path: sub_path,
                        referencing_layer: identifier.clone(),
                        reason: format!("{reason:#}"),
                    })?;
                    continue;
                }
            };

            let sub_id = self.resolver.create_identifier(&sub_asset, Some(&resolved));
            // A sublayer already opened (this pass or in the graph) is skipped; an
            // empty/degenerate identifier falls through to the resolve below and is
            // reported `UnresolvedAsset`.
            if visited.contains(&sub_id) || already_present(&sub_id) {
                continue;
            }
            // Resolve the sublayer; a missing one is routed to `on_error`.
            let Some(sub_resolved) = self.resolver.resolve(&sub_id) else {
                on_error(Error::UnresolvedAsset {
                    asset_path: sub_asset,
                    referencing_layer: identifier.clone(),
                })?;
                visited.insert(sub_id);
                continue;
            };
            visited.insert(sub_id.clone());
            // Read the sublayer; a resolved-but-unreadable one is routed to
            // `on_error` and skipped, dropping only it (the root's read failure
            // propagated from `open_stack`).
            let sub_data = match self.read(&sub_resolved) {
                Ok(data) => data,
                Err(reason) => {
                    on_error(Error::UnreadableAsset {
                        asset_path: sub_asset,
                        referencing_layer: identifier.clone(),
                        reason: format!("{reason:#}"),
                    })?;
                    continue;
                }
            };

            self.open_sublayers(
                sub_id,
                sub_resolved,
                sub_data,
                &expr_vars,
                on_error,
                already_present,
                visited,
                layers,
            )?;
        }

        Ok(())
    }

    /// A layer's `subLayers` asset paths (empty when it declares none).
    fn sublayer_paths(data: &dyn sdf::AbstractData) -> Vec<String> {
        sdf::PseudoRootSpecRef::get(data)
            .and_then(|root| root.sublayers())
            .unwrap_or_default()
    }
}

/// Test-only full-closure loading, used by the `pcp` composition tests to build
/// a fully-resolved layer graph without the stage's on-demand load loop. Eager
/// arc following lives only here, off the production path.
#[cfg(test)]
impl LayerRegistry {
    /// Opens a root layer and the full transitive closure of its sublayers,
    /// references, and payloads — the layer set a fully-composed (and fully-
    /// traversed) stage would have loaded on demand.
    pub(crate) fn collect_with_arcs(&self, root_path: &str) -> Result<Vec<sdf::Layer>> {
        let mut layers = Vec::new();
        let mut visited = HashSet::new();
        self.collect_with_arcs_in(root_path, None, &HashMap::new(), &mut layers, &mut visited)?;
        layers.reverse();
        Ok(layers)
    }

    fn collect_with_arcs_in(
        &self,
        asset_path: &str,
        anchor: Option<&ar::ResolvedPath>,
        ancestor_expr_vars: &HashMap<String, sdf::Value>,
        layers: &mut Vec<sdf::Layer>,
        visited: &mut HashSet<String>,
    ) -> Result<()> {
        let identifier = self.resolver.create_identifier(asset_path, anchor);
        if identifier.is_empty() || visited.contains(&identifier) {
            return Ok(());
        }
        let Some(resolved) = self.resolver.resolve(&identifier) else {
            return Ok(());
        };
        visited.insert(identifier.clone());
        let data = self.read(&resolved)?;
        let mut expr_vars = expr::read_expression_variables(data.as_ref())?.into_owned();
        expr::compose_over(&mut expr_vars, ancestor_expr_vars);
        for dep in Self::arc_dependencies(data.as_ref())? {
            let dep_asset = expr::evaluate_asset_path(&dep, &expr_vars)?;
            self.collect_with_arcs_in(&dep_asset, Some(&resolved), &expr_vars, layers, visited)?;
        }
        layers.push(sdf::Layer::new(identifier, data));
        Ok(())
    }

    /// Every sublayer, reference, and payload asset path authored in a layer.
    fn arc_dependencies(data: &dyn sdf::AbstractData) -> Result<Vec<String>> {
        let mut deps = Self::sublayer_paths(data);
        let mut queue = vec![sdf::Path::abs_root()];
        while let Some(path) = queue.pop() {
            if !data.has_spec(&path) {
                continue;
            }
            if let Some(value) = data.try_field(&path, sdf::FieldKey::References.as_str())? {
                if let sdf::Value::ReferenceListOp(list_op) = value.as_ref() {
                    deps.extend(
                        list_op
                            .iter()
                            .filter(|r| !r.asset_path.is_empty())
                            .map(|r| r.asset_path.clone()),
                    );
                }
            }
            if let Some(value) = data.try_field(&path, sdf::FieldKey::Payload.as_str())? {
                match value.as_ref() {
                    sdf::Value::Payload(p) if !p.asset_path.is_empty() => deps.push(p.asset_path.clone()),
                    sdf::Value::PayloadListOp(list_op) => {
                        deps.extend(
                            list_op
                                .iter()
                                .filter(|p| !p.asset_path.is_empty())
                                .map(|p| p.asset_path.clone()),
                        );
                    }
                    _ => {}
                }
            }
            if let Some(value) = data.try_field(&path, sdf::ChildrenKey::PrimChildren.as_str())? {
                if let sdf::Value::TokenVec(children) = value.into_owned() {
                    for name in children.iter().rev() {
                        if let Ok(child) = path.append_path(name.as_str()) {
                            queue.push(child);
                        }
                    }
                }
            }
            if let Some(value) = data.try_field(&path, sdf::ChildrenKey::VariantSetChildren.as_str())? {
                if let sdf::Value::TokenVec(set_names) = value.into_owned() {
                    for set_name in &set_names {
                        let set_path = path.append_variant_selection(set_name, "");
                        if let Some(value) = data.try_field(&set_path, sdf::ChildrenKey::VariantChildren.as_str())? {
                            if let sdf::Value::TokenVec(variant_names) = value.into_owned() {
                                for variant_name in &variant_names {
                                    queue.push(path.append_variant_selection(set_name, variant_name));
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(deps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::FileFormatCaps;

    const VENDOR_COMPOSITION: &str = "vendor/usd-wg-assets/test_assets/foundation/stage_composition";

    fn manifest_dir() -> String {
        std::env::var("CARGO_MANIFEST_DIR").unwrap()
    }

    fn composition_path(relative: &str) -> String {
        format!("{}/{}/{}", manifest_dir(), VENDOR_COMPOSITION, relative)
    }

    fn fixture_path(relative: &str) -> String {
        format!("{}/fixtures/{}", manifest_dir(), relative)
    }

    /// A registry over the default filesystem resolver.
    fn registry() -> LayerRegistry {
        LayerRegistry::default()
    }

    /// Opens a root layer and its sublayer stack, erroring on a missing sublayer.
    fn open_stack(path: &str) -> Result<Vec<sdf::Layer>> {
        registry().open_stack(path, None, &HashMap::new(), &|e| Err(e.into()), &|_| false)
    }

    #[test]
    fn lookup_by_extension() {
        assert_eq!(LayerRegistry::find_by_extension("usda").unwrap().format_id(), "usda");
        assert_eq!(LayerRegistry::find_by_extension("usdc").unwrap().format_id(), "usdc");
        assert_eq!(LayerRegistry::find_by_extension("usd").unwrap().format_id(), "usdc");
        assert_eq!(LayerRegistry::find_by_extension("USDA").unwrap().format_id(), "usda");
        assert_eq!(LayerRegistry::find_by_extension("usdz").unwrap().format_id(), "usdz");
        assert!(LayerRegistry::find_by_extension("xyz").is_none());
        assert!(LayerRegistry::find_by_extension("").is_none());
    }

    #[test]
    fn lookup_by_id() {
        assert_eq!(
            LayerRegistry::find_by_id("usdc").unwrap().extensions(),
            &["usdc", "usd"]
        );
        assert!(LayerRegistry::find_by_id("usd").is_none());
    }

    #[test]
    fn builtin_capabilities() {
        for id in ["usda", "usdc"] {
            let caps = LayerRegistry::find_by_id(id).unwrap().caps();
            assert_eq!(caps, FileFormatCaps::all(), "{id} should read, write, and edit");
        }
        // usdz is a package format: writable as a new archive, but not editable
        // (savable) in place.
        let usdz = LayerRegistry::find_by_id("usdz").unwrap().caps();
        assert!(usdz.can_read() && usdz.can_write());
        assert!(!usdz.can_edit(), "usdz should not be editable in place");
    }

    // References and payloads are not followed here — composition opens those
    // targets on demand — so loading walks only the root and its sublayer stack.
    // The binary-`.usd` content-sniff round-trip is covered by
    // `sdf::layer::tests::export_usd_writes_binary`.

    #[test]
    fn expression_sublayer() -> Result<()> {
        let layers = open_stack(&fixture_path("expr_sublayer.usda"))?;
        assert_eq!(layers.len(), 2, "root + 1 expression-resolved sublayer");
        assert!(layers[0].identifier.contains("expr_sublayer.usda"));
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_same_folder() -> Result<()> {
        let layers = open_stack(&composition_path("subLayer/sublayer_same_folder.usda"))?;
        assert_eq!(layers.len(), 2, "root + 1 sublayer");
        assert!(layers[0].identifier.contains("sublayer_same_folder.usda"));
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_child_folder() -> Result<()> {
        let layers = open_stack(&composition_path("subLayer/sublayer_child_folder.usda"))?;
        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_parent_folder() -> Result<()> {
        let layers = open_stack(&composition_path("subLayer/sublayer_parent_folder.usda"))?;
        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    /// A reference target is not opened by the loader; only the root and its
    /// sublayers load. (Composition opens the reference on demand.)
    #[test]
    fn reference_not_followed() -> Result<()> {
        let layers = open_stack(&composition_path("references/reference_same_folder.usda"))?;
        assert_eq!(layers.len(), 1, "only the root; the reference is composed lazily");
        assert!(layers[0].identifier.contains("reference_same_folder.usda"));
        Ok(())
    }

    /// Sibling sublayers load in authored order, strongest first (spec 10.3.1.1):
    /// a layer overrides the layers it sublayers, and an earlier `subLayers` entry
    /// overrides a later one. Guards against reversing sibling subtrees.
    #[test]
    fn sublayer_sibling_order() -> Result<()> {
        let root = format!(
            "{}/vendor/usd-wg-assets/test_assets/RelationshipEncapsulationTests/SublayeredInternalReferenceTest.usda",
            manifest_dir()
        );
        let names: Vec<String> = open_stack(&root)?.iter().map(|l| l.identifier.clone()).collect();
        assert_eq!(names.len(), 4, "root + 3 sublayers");
        assert!(names[0].contains("SublayeredInternalReferenceTest.usda"));
        assert!(names[1].contains("Environment.usda"));
        assert!(names[2].contains("hardware.shading.usda"));
        assert!(names[3].contains("hardware.modeling.usda"));
        Ok(())
    }

    /// The default handler errors on an unresolvable sublayer.
    #[test]
    fn strict_errors_on_missing_sublayer() {
        assert!(open_stack(&composition_path("subLayer/sublayer_invalid.usda")).is_err());
    }

    /// A custom handler receives the missing sublayer's asset path.
    #[test]
    fn handler_receives_sublayer_error() -> Result<()> {
        let errors = std::cell::RefCell::new(Vec::new());
        let layers = registry().open_stack(
            &composition_path("subLayer/sublayer_invalid.usda"),
            None,
            &HashMap::new(),
            &|e| {
                errors.borrow_mut().push(e);
                Ok(())
            },
            &|_| false,
        )?;

        // The root still loads despite the missing sublayer.
        assert_eq!(layers.len(), 1);
        assert!(layers[0].identifier.contains("sublayer_invalid.usda"));

        let errors = errors.into_inner();
        assert_eq!(errors.len(), 1);
        let Error::UnresolvedAsset { referencing_layer, .. } = &errors[0] else {
            panic!("expected UnresolvedAsset, got {:?}", errors[0]);
        };
        assert!(referencing_layer.contains("sublayer_invalid.usda"));
        Ok(())
    }
}
