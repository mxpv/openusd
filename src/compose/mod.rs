//! Layer collection and composition.
//!
//! Given a root USD file, [`collect_layers`] uses an [`ar::Resolver`] to recursively
//! resolve and load every layer the stage depends on — following sublayers, references,
//! and payloads across files and formats (`.usda`, `.usdc`, `.usd`, `.usdz`). The result
//! is a [`Vec`] of [`Layer`]s, each wrapping a parsed [`AbstractData`] with its resolved
//! identity. Cycles are detected and skipped automatically.

#[allow(dead_code)] // TODO: Remove once all arc types are implemented.
pub(crate) mod prim_index;

use std::collections::{HashMap, HashSet};
use std::io::Cursor;

use anyhow::{bail, Context, Result};

use crate::ar::{self, Resolver};
use crate::expr;
use crate::sdf::schema::{ChildrenKey, FieldKey};
use crate::sdf::{AbstractData, Path, Value};
use crate::{usda, usdc};

/// A single loaded layer in the composition.
pub struct Layer {
    /// Resolved, canonical identifier for this layer.
    pub identifier: String,
    /// The parsed scene description data.
    pub data: Box<dyn AbstractData>,
}

impl Layer {
    fn new(identifier: impl Into<String>, data: Box<dyn AbstractData>) -> Self {
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

/// Opens a root layer and recursively collects all referenced layers.
///
/// Walks sublayers (layer-level), then traverses every prim to collect
/// references and payloads. Each discovered asset path is resolved via the
/// provided [`Resolver`], loaded, and itself walked for further references.
///
/// Returns a [`Vec<Layer>`] with the root (strongest) layer first.
pub fn collect_layers(resolver: &impl Resolver, root_path: &str) -> Result<Vec<Layer>> {
    let (layers, _unresolved) = collect_layers_recording(resolver, root_path)?;
    Ok(layers)
}

/// Like [`collect_layers`] but also returns the asset paths that could not
/// be resolved during composition.
///
/// The second element of the returned tuple contains the unresolved asset
/// paths in the order they were first encountered.  These paths correspond
/// to layers that are referenced or payloaded in the scene but whose files
/// could not be found by the [`Resolver`].
///
/// Note the asymmetric handling:
///
/// * If the **root** asset cannot be resolved, this function returns `Err`
///   (there is no stage to return).
/// * If a **transitively referenced** asset cannot be resolved, it is
///   recorded in the unresolved list and composition continues with the
///   assets that *could* be loaded.
pub fn collect_layers_recording(resolver: &impl Resolver, root_path: &str) -> Result<(Vec<Layer>, Vec<String>)> {
    let mut layers = Vec::new();
    let mut visited = HashSet::new();
    let mut unresolved = Vec::new();

    collect_recursive(resolver, root_path, None, &mut layers, &mut visited, &mut unresolved)?;

    // Layers are collected in post-order (leaves first), reverse so root is first.
    layers.reverse();

    Ok((layers, unresolved))
}

/// Recursive layer collector.
fn collect_recursive(
    resolver: &impl Resolver,
    asset_path: &str,
    anchor: Option<&ar::ResolvedPath>,
    layers: &mut Vec<Layer>,
    visited: &mut HashSet<String>,
    unresolved: &mut Vec<String>,
) -> Result<()> {
    // Create an anchored identifier so relative paths resolve correctly.
    let identifier = resolver.create_identifier(asset_path, anchor);

    // Skip already-visited layers to avoid cycles.
    if visited.contains(&identifier) {
        return Ok(());
    }

    // Resolve using the anchored identifier (which is absolute).
    // For the root asset (anchor == None) a missing file is always fatal.
    // For transitively referenced assets (anchor == Some), record the path
    // and continue so that callers can inspect `unresolved` afterwards.
    let resolved = match resolver.resolve(&identifier) {
        Some(r) => r,
        None => {
            if anchor.is_none() {
                // Root layer must exist.
                anyhow::bail!("failed to resolve asset path: {asset_path}");
            }
            if !unresolved.contains(&identifier) {
                unresolved.push(identifier.clone());
            }
            // Mark as visited so we don't attempt to re-resolve in recursive calls.
            visited.insert(identifier);
            return Ok(());
        }
    };

    visited.insert(identifier.clone());

    // Load and parse the layer.
    let data = open_layer(resolver, &resolved)?;

    // Read expression variables from this layer's pseudo-root.
    let expr_vars = read_expression_variables(data.as_ref());

    // Collect all asset paths that need recursive loading.
    let raw_paths = collect_asset_paths(data.as_ref());

    // Evaluate any expression-valued asset paths.
    let referenced = resolve_expressions(&raw_paths, &expr_vars)?;

    // Recurse into discovered layers, anchored to the current layer.
    let is_usdz = resolved.extension().and_then(|e| e.to_str()) == Some("usdz");
    if is_usdz && !referenced.is_empty() {
        bail!(
            "cross-file references within USDZ archives are not yet supported: {}",
            resolved
        );
    }

    for ref_path in &referenced {
        collect_recursive(resolver, ref_path, Some(&resolved), layers, visited, unresolved)?;
    }

    layers.push(Layer::new(identifier, data));

    Ok(())
}

/// Collects all asset paths from sublayers, references, and payloads in a layer.
fn collect_asset_paths(data: &dyn AbstractData) -> Vec<String> {
    let mut paths = Vec::new();

    let root = Path::abs_root();

    // Sublayers (layer-level).
    if let Ok(value) = data.get(&root, FieldKey::SubLayers.as_str()) {
        if let Value::StringVec(sub_paths) = value.into_owned() {
            paths.extend(sub_paths);
        }
    }

    // Walk the prim hierarchy to find references and payloads.
    let prim_paths = collect_prim_paths(data);
    for prim_path in &prim_paths {
        // References.
        if let Ok(value) = data.get(prim_path, FieldKey::References.as_str()) {
            extract_reference_paths(&value, &mut paths);
        }

        // Payloads.
        if let Ok(value) = data.get(prim_path, FieldKey::Payload.as_str()) {
            extract_payload_paths(&value, &mut paths);
        }
    }

    paths
}

/// Collects all prim paths by walking the `primChildren` hierarchy.
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

        if let Ok(value) = data.get(&path, ChildrenKey::PrimChildren.as_str()) {
            if let Value::TokenVec(children) = value.into_owned() {
                for name in children.iter().rev() {
                    if let Ok(child) = path.append_path(name.as_str()) {
                        queue.push(child);
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
pub fn open_layer(resolver: &impl Resolver, resolved: &ar::ResolvedPath) -> Result<Box<dyn AbstractData>> {
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

/// Appends external asset paths from a references value.
fn extract_reference_paths(value: &Value, out: &mut Vec<String>) {
    if let Value::ReferenceListOp(list_op) = value {
        out.extend(list_op.iter().map(|r| &r.asset_path).filter(|p| !p.is_empty()).cloned());
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

/// Evaluates expression-valued asset paths, passing through plain paths unchanged.
fn resolve_expressions(paths: &[String], vars: &HashMap<String, Value>) -> Result<Vec<String>> {
    paths
        .iter()
        .map(|path| {
            if expr::is_expression(path) {
                let expression =
                    expr::Expr::parse(path).with_context(|| format!("failed to parse expression: {path}"))?;
                let result = expression
                    .eval(vars)
                    .with_context(|| format!("failed to evaluate expression: {path}"))?;
                match result {
                    Value::String(s) => Ok(s),
                    other => bail!("expression must evaluate to a string, got: {other:?}"),
                }
            } else {
                Ok(path.clone())
            }
        })
        .collect()
}

/// Appends external asset paths from a payload value.
fn extract_payload_paths(value: &Value, out: &mut Vec<String>) {
    match value {
        Value::Payload(p) if !p.asset_path.is_empty() => {
            out.push(p.asset_path.clone());
        }
        Value::PayloadListOp(list_op) => {
            out.extend(list_op.iter().map(|p| &p.asset_path).filter(|p| !p.is_empty()).cloned());
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
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
}
