//! Layer stack collection.
//!
//! Given a root USD file, [`collect_layers`] uses an [`ar::Resolver`] to recursively
//! resolve and load every layer the stage depends on — following sublayers, references,
//! and payloads across files and formats (`.usda`, `.usdc`, `.usd`, `.usdz`). The result
//! is a [`Vec`] of [`Layer`]s, each wrapping a parsed [`AbstractData`] with its resolved
//! identity. Cycles are detected and skipped automatically.

use std::collections::{HashMap, HashSet};
use std::io::Cursor;

use anyhow::{bail, Context, Result};

use crate::ar::{self, Resolver};
use crate::expr;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{AbstractData, LayerData, Path, Value};
use crate::{usda, usdc};

/// The kind of layer dependency that triggered a composition error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DependencyKind {
    /// A sublayer declared on the layer's pseudo-root.
    SubLayer,
    /// A reference arc on a prim.
    Reference,
    /// A payload arc on a prim.
    Payload,
}

impl std::fmt::Display for DependencyKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SubLayer => write!(f, "sublayer"),
            Self::Reference => write!(f, "reference"),
            Self::Payload => write!(f, "payload"),
        }
    }
}

/// An error encountered during stage composition that may be recoverable.
///
/// When opening a stage, some errors (such as missing referenced files) can be
/// tolerated so that the stage is partially constructed. A callback provided via
/// [`StageBuilder::on_error`](crate::stage::StageBuilder::on_error) receives
/// these errors and decides whether to continue or abort.
#[derive(Debug)]
#[non_exhaustive]
pub enum CompositionError {
    /// An asset path could not be resolved to a physical location.
    UnresolvedAsset {
        /// The asset path that could not be resolved.
        asset_path: String,
        /// The layer that declared this dependency.
        referencing_layer: String,
        /// What kind of composition arc declared this dependency.
        kind: DependencyKind,
        /// The prim that declared this arc (`None` for sublayers).
        prim_path: Option<Path>,
    },
}

impl std::fmt::Display for CompositionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnresolvedAsset {
                asset_path,
                referencing_layer,
                kind,
                prim_path,
            } => {
                write!(
                    f,
                    "failed to resolve {kind} asset: {asset_path} (referenced by {referencing_layer}"
                )?;
                if let Some(prim) = prim_path {
                    write!(f, " at {prim}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::error::Error for CompositionError {}

/// A single loaded layer in the composition.
pub struct Layer {
    /// Resolved, canonical identifier for this layer.
    pub identifier: String,
    /// The parsed scene description data.
    pub data: LayerData,
}

impl Layer {
    fn new(identifier: impl Into<String>, data: LayerData) -> Self {
        Self {
            identifier: identifier.into(),
            data,
        }
    }
}

impl std::fmt::Debug for Layer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Layer")
            .field("identifier", &self.identifier)
            .finish_non_exhaustive()
    }
}

/// A dependency discovered while walking a layer's scene graph.
struct Dependency {
    /// The asset path to resolve.
    asset_path: String,
    /// What kind of composition arc declared this dependency.
    kind: DependencyKind,
    /// The prim that declared this arc (`None` for sublayers).
    prim_path: Option<Path>,
}

/// Opens a root layer and recursively collects all referenced layers.
///
/// Any unresolvable transitive dependency causes an immediate error.
/// For more control over error handling, use [`collect_layers_with_handler`].
///
/// Returns a [`Vec<Layer>`] with the root (strongest) layer first.
pub fn collect_layers(resolver: &impl Resolver, root_path: &str) -> Result<Vec<Layer>> {
    collect_layers_with_handler(resolver, root_path, |e| bail!("{e}"))
}

/// Like [`collect_layers`] but with a custom error handler for recoverable
/// composition failures.
///
/// The `on_error` callback decides whether to continue (`Ok(())`) or abort
/// (`Err(...)`) for each composition error encountered.
pub fn collect_layers_with_handler(
    resolver: &impl Resolver,
    root_path: &str,
    on_error: impl Fn(CompositionError) -> Result<()>,
) -> Result<Vec<Layer>> {
    let mut layers = Vec::new();
    let mut visited = HashSet::new();

    collect_recursive(resolver, root_path, None, &mut layers, &mut visited, &on_error)?;

    // Layers are collected in post-order (leaves first), reverse so root is first.
    layers.reverse();

    Ok(layers)
}

/// Recursive layer collector.
fn collect_recursive(
    resolver: &impl Resolver,
    asset_path: &str,
    anchor: Option<&ar::ResolvedPath>,
    layers: &mut Vec<Layer>,
    visited: &mut HashSet<String>,
    on_error: &dyn Fn(CompositionError) -> Result<()>,
) -> Result<()> {
    // Create an anchored identifier so relative paths resolve correctly.
    let identifier = resolver.create_identifier(asset_path, anchor);

    // Skip already-visited layers to avoid cycles.
    if visited.contains(&identifier) {
        return Ok(());
    }

    // Resolve using the anchored identifier (which is absolute).
    // Root layer (no anchor) must always resolve — missing root is a hard error.
    let resolved = resolver
        .resolve(&identifier)
        .with_context(|| format!("failed to resolve asset path: {asset_path}"))?;

    visited.insert(identifier.clone());

    // Load and parse the layer.
    let data = open_layer(resolver, &resolved)?;

    // Read expression variables from this layer's pseudo-root.
    let expr_vars = read_expression_variables(data.as_ref());

    // Collect typed dependencies from this layer.
    let deps = collect_dependencies(data.as_ref());

    let is_usdz = resolved.extension().and_then(|e| e.to_str()) == Some("usdz");

    for dep in deps {
        // Evaluate expression-valued asset paths.
        let dep_asset = resolve_expression(&dep.asset_path, &expr_vars)?;

        if is_usdz {
            bail!(
                "cross-file references within USDZ archives are not yet supported: {}",
                resolved
            );
        }

        // Check if this dependency resolves before recursing.
        let dep_id = resolver.create_identifier(&dep_asset, Some(&resolved));
        if !visited.contains(&dep_id) && resolver.resolve(&dep_id).is_none() {
            on_error(CompositionError::UnresolvedAsset {
                asset_path: dep_asset,
                referencing_layer: identifier.clone(),
                kind: dep.kind,
                prim_path: dep.prim_path,
            })?;
            visited.insert(dep_id);
            continue;
        }

        collect_recursive(resolver, &dep_asset, Some(&resolved), layers, visited, on_error)?;
    }

    layers.push(Layer::new(identifier, data));

    Ok(())
}

/// Collects typed dependencies from sublayers, references, and payloads in a layer.
fn collect_dependencies(data: &dyn AbstractData) -> Vec<Dependency> {
    let mut deps = Vec::new();

    let root = Path::abs_root();

    // Sublayers (layer-level).
    if let Ok(value) = data.get(&root, FieldKey::SubLayers.as_str()) {
        if let Value::StringVec(sub_paths) = value.into_owned() {
            for asset_path in sub_paths {
                deps.push(Dependency {
                    asset_path,
                    kind: DependencyKind::SubLayer,
                    prim_path: None,
                });
            }
        }
    }

    // Walk the prim hierarchy to find references and payloads.
    let prim_paths = collect_prim_paths(data);
    for prim_path in &prim_paths {
        // References.
        if let Ok(value) = data.get(prim_path, FieldKey::References.as_str()) {
            if let Value::ReferenceListOp(list_op) = value.as_ref() {
                for r in list_op.iter().filter(|r| !r.asset_path.is_empty()) {
                    deps.push(Dependency {
                        asset_path: r.asset_path.clone(),
                        kind: DependencyKind::Reference,
                        prim_path: Some(prim_path.clone()),
                    });
                }
            }
        }

        // Payloads.
        if let Ok(value) = data.get(prim_path, FieldKey::Payload.as_str()) {
            match value.as_ref() {
                Value::Payload(p) if !p.asset_path.is_empty() => {
                    deps.push(Dependency {
                        asset_path: p.asset_path.clone(),
                        kind: DependencyKind::Payload,
                        prim_path: Some(prim_path.clone()),
                    });
                }
                Value::PayloadListOp(list_op) => {
                    for p in list_op.iter().filter(|p| !p.asset_path.is_empty()) {
                        deps.push(Dependency {
                            asset_path: p.asset_path.clone(),
                            kind: DependencyKind::Payload,
                            prim_path: Some(prim_path.clone()),
                        });
                    }
                }
                _ => {}
            }
        }
    }

    deps
}

/// Collects all prim and variant spec paths by walking `primChildren`,
/// `variantSetChildren`, and `variantChildren` hierarchies.
fn collect_prim_paths(data: &dyn AbstractData) -> Vec<Path> {
    let mut result = Vec::new();
    let mut queue = vec![Path::abs_root()];

    while let Some(path) = queue.pop() {
        if !data.has_spec(&path) {
            continue;
        }

        // Skip the pseudo-root itself but process its children.
        if path != Path::abs_root() {
            result.push(path.clone());
        }

        // Regular prim children.
        if let Ok(value) = data.get(&path, ChildrenKey::PrimChildren.as_str()) {
            if let Value::TokenVec(children) = value.into_owned() {
                for name in children.iter().rev() {
                    if let Ok(child) = path.append_path(name.as_str()) {
                        queue.push(child);
                    }
                }
            }
        }

        // Variant set children (e.g. /Prim -> /Prim{setName=}).
        if let Ok(value) = data.get(&path, ChildrenKey::VariantSetChildren.as_str()) {
            if let Value::TokenVec(set_names) = value.into_owned() {
                for set_name in &set_names {
                    // Variant children within each set (e.g. /Prim{setName=selA}).
                    let set_path = path.append_variant_selection(set_name, "");
                    if let Ok(value) = data.get(&set_path, ChildrenKey::VariantChildren.as_str()) {
                        if let Value::TokenVec(variant_names) = value.into_owned() {
                            for variant_name in &variant_names {
                                let variant_path = path.append_variant_selection(set_name, variant_name);
                                queue.push(variant_path);
                            }
                        }
                    }
                }
            }
        }
    }

    result
}

/// Opens a single layer from a resolved path, auto-detecting the format.
///
/// Supports `.usda` (text), `.usdc` (binary), `.usd` (auto-detected via magic
/// bytes), and `.usdz` (archive — reads the first layer). Returns the parsed
/// data as a boxed [`AbstractData`].
pub fn open_layer(resolver: &impl Resolver, resolved: &ar::ResolvedPath) -> Result<LayerData> {
    let ext = resolved.extension().and_then(|e| e.to_str()).unwrap_or_default();

    if ext == "usdz" {
        let mut archive = crate::usdz::Archive::open(resolved)?;
        return archive
            .read_first_layer()
            .context("failed to read first layer from USDZ archive");
    }

    let mut asset = resolver.open_asset(resolved)?;
    let bytes = asset.read_all()?;

    // For .usd files, sniff magic bytes to detect binary vs text format.
    let is_binary = ext == "usdc" || (ext == "usd" && bytes.starts_with(usdc::MAGIC));

    if is_binary {
        let data = usdc::CrateData::open(Cursor::new(bytes), true).context("failed to parse USDC layer")?;
        Ok(Box::new(data))
    } else {
        let content = String::from_utf8(bytes).context("layer is not valid UTF-8")?;
        let mut parser = usda::parser::Parser::new(&content);
        let data = parser.parse().context("failed to parse USDA layer")?;
        Ok(Box::new(usda::TextReader::from_data(data)))
    }
}

/// Reads `expressionVariables` from the layer's pseudo-root, if present.
fn read_expression_variables(data: &dyn AbstractData) -> HashMap<String, Value> {
    let root = Path::abs_root();
    if let Ok(value) = data.get(&root, FieldKey::ExpressionVariables.as_str()) {
        if let Value::Dictionary(dict) = value.into_owned() {
            return dict;
        }
    }
    HashMap::new()
}

/// Evaluates an expression-valued asset path, or passes it through unchanged.
fn resolve_expression(path: &str, vars: &HashMap<String, Value>) -> Result<String> {
    if expr::is_expression(path) {
        let expression = expr::Expr::parse(path).with_context(|| format!("failed to parse expression: {path}"))?;
        let result = expression
            .eval(vars)
            .with_context(|| format!("failed to evaluate expression: {path}"))?;
        match result {
            Value::String(s) => Ok(s),
            other => bail!("expression must evaluate to a string, got: {other:?}"),
        }
    } else {
        Ok(path.to_string())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::ar::DefaultResolver;

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

    // -----------------------------------------------------------------------
    // Expression evaluation
    // -----------------------------------------------------------------------

    #[test]
    fn expression_sublayer() -> Result<()> {
        let path = fixture_path("expr_sublayer.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved sublayer");
        assert!(layers[0].identifier.contains("expr_sublayer.usda"));
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn expression_reference() -> Result<()> {
        let path = fixture_path("expr_reference.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved reference");
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn expression_asset_path() -> Result<()> {
        let path = fixture_path("expr_asset_path.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved reference");
        assert!(layers[0].identifier.contains("expr_asset_path.usda"));
        assert!(layers[1]
            .identifier
            .replace('\\', "/")
            .contains("expr_assets/extraAssets.usda"));
        Ok(())
    }

    #[test]
    fn expression_payload() -> Result<()> {
        let path = fixture_path("expr_payload.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved payload");
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Sublayers
    // -----------------------------------------------------------------------

    #[test]
    fn sublayer_same_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_same_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2, "root + 1 sublayer");
        assert!(layers[0].identifier.contains("sublayer_same_folder.usda"));
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_child_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_parent_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // References
    // -----------------------------------------------------------------------

    #[test]
    fn reference_same_folder() -> Result<()> {
        let path = composition_path("references/reference_same_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2, "root + 1 referenced layer");
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_child_folder() -> Result<()> {
        let path = composition_path("references/reference_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_parent_folder() -> Result<()> {
        let path = composition_path("references/reference_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Payloads
    // -----------------------------------------------------------------------

    #[test]
    fn payload_same_folder() -> Result<()> {
        let path = composition_path("payload/payload_same_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2, "root + 1 payload layer");
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn payload_child_folder() -> Result<()> {
        let path = composition_path("payload/payload_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn payload_parent_folder() -> Result<()> {
        let path = composition_path("payload/payload_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Multi-level composition
    // -----------------------------------------------------------------------

    #[test]
    fn teapot_multi_level() -> Result<()> {
        let path = format!("{}/vendor/usd-wg-assets/full_assets/Teapot/Teapot.usd", manifest_dir());
        let resolver = DefaultResolver::new();
        let layers = collect_layers(&resolver, &path)?;

        // Teapot.usd -> payload Teapot_Payload.usd -> sublayer Teapot_Materials.usd
        assert!(layers.len() >= 3, "expected at least 3 layers, got {}", layers.len());

        assert!(layers[0].identifier.contains("Teapot.usd"));

        let ids = layers.iter().map(|l| l.identifier.as_str()).collect::<Vec<_>>();
        assert!(ids.iter().any(|id| id.contains("Teapot_Payload")));
        assert!(ids.iter().any(|id| id.contains("Teapot_Materials")));

        Ok(())
    }

    // -----------------------------------------------------------------------
    // Error handling
    // -----------------------------------------------------------------------

    /// Default handler errors on unresolvable dependencies (backward compat).
    #[test]
    fn collect_layers_errors_on_missing_reference() {
        let path = composition_path("references/reference_invalid.usda");
        let resolver = DefaultResolver::new();
        assert!(collect_layers(&resolver, &path).is_err());
    }

    /// Custom handler receives correct error details for each dependency kind.
    #[test]
    fn handler_receives_error() -> Result<()> {
        let resolver = DefaultResolver::new();
        let errors = RefCell::new(Vec::new());

        let path = composition_path("references/reference_invalid.usda");
        collect_layers_with_handler(&resolver, &path, |e| {
            errors.borrow_mut().push(e);
            Ok(())
        })?;

        let path = composition_path("payload/payload_invalid.usda");
        collect_layers_with_handler(&resolver, &path, |e| {
            errors.borrow_mut().push(e);
            Ok(())
        })?;

        let path = composition_path("subLayer/sublayer_invalid.usda");
        collect_layers_with_handler(&resolver, &path, |e| {
            errors.borrow_mut().push(e);
            Ok(())
        })?;

        let errors = errors.into_inner();
        assert_eq!(errors.len(), 3);

        let CompositionError::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[0];
        assert_eq!(kind, DependencyKind::Reference);
        assert_eq!(prim_path.as_ref().unwrap().as_str(), "/World/invalid_reference");

        let CompositionError::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[1];
        assert_eq!(kind, DependencyKind::Payload);
        assert_eq!(prim_path.as_ref().unwrap().as_str(), "/World/invalid_payload");

        let CompositionError::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[2];
        assert_eq!(kind, DependencyKind::SubLayer);
        assert!(prim_path.is_none());

        Ok(())
    }

    /// Handler that ignores all errors allows partial layer collection.
    #[test]
    fn handler_can_ignore_errors() -> Result<()> {
        let path = composition_path("references/reference_invalid.usda");
        let resolver = DefaultResolver::new();
        let layers = collect_layers_with_handler(&resolver, &path, |_| Ok(()))?;

        // Root layer loads despite the missing reference.
        assert_eq!(layers.len(), 1);
        assert!(layers[0].identifier.contains("reference_invalid.usda"));
        Ok(())
    }
}
