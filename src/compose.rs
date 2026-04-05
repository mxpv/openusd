//! Layer collection and composition.
//!
//! Given a root USD file, [`collect_layers`] uses an [`ar::Resolver`] to recursively
//! resolve and load every layer the stage depends on — following sublayers, references,
//! and payloads across files and formats (`.usda`, `.usdc`, `.usd`, `.usdz`). The result
//! is a [`LayerStack`] of [`Layer`]s, each wrapping a parsed
//! [`AbstractData`] with its resolved identity. Cycles are
//! detected and skipped automatically.

use std::collections::HashSet;
use std::io::Cursor;

use anyhow::{bail, Context, Result};

use crate::ar::{self, Resolver};
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

/// Result of composing a USD stage from a root layer.
///
/// Contains the ordered stack of layers discovered by walking sublayers,
/// references, and payloads.
#[derive(Debug)]
pub struct LayerStack {
    /// All layers in the stack, root layer first.
    pub layers: Vec<Layer>,
}

impl LayerStack {
    /// Returns the root (strongest) layer.
    pub fn root(&self) -> &Layer {
        &self.layers[0]
    }

    /// Returns the number of layers in the stack.
    pub fn len(&self) -> usize {
        self.layers.len()
    }

    /// Returns `true` if the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.layers.is_empty()
    }

    /// Returns an iterator over all layers.
    pub fn iter(&self) -> impl Iterator<Item = &Layer> {
        self.layers.iter()
    }

    /// Returns the layer identifiers in order.
    pub fn identifiers(&self) -> Vec<&str> {
        self.layers.iter().map(|l| l.identifier.as_str()).collect()
    }
}

/// Opens a root layer and recursively collects all referenced layers.
///
/// Walks sublayers (layer-level), then traverses every prim to collect
/// references and payloads. Each discovered asset path is resolved via the
/// provided [`Resolver`], loaded, and itself walked for further references.
///
/// Returns a [`LayerStack`] with the root layer first.
pub fn collect_layers(resolver: &impl Resolver, root_path: &str) -> Result<LayerStack> {
    let mut layers = Vec::new();
    let mut visited = HashSet::new();

    collect_recursive(resolver, root_path, None, &mut layers, &mut visited)?;

    // Layers are collected in post-order (leaves first), reverse so root is first.
    layers.reverse();

    Ok(LayerStack { layers })
}

/// Recursive layer collector.
fn collect_recursive(
    resolver: &impl Resolver,
    asset_path: &str,
    anchor: Option<&ar::ResolvedPath>,
    layers: &mut Vec<Layer>,
    visited: &mut HashSet<String>,
) -> Result<()> {
    // Create an anchored identifier so relative paths resolve correctly.
    let identifier = resolver.create_identifier(asset_path, anchor);

    // Skip already-visited layers to avoid cycles.
    if visited.contains(&identifier) {
        return Ok(());
    }

    // Resolve using the anchored identifier (which is absolute).
    let resolved = resolver
        .resolve(&identifier)
        .with_context(|| format!("failed to resolve asset path: {asset_path}"))?;

    visited.insert(identifier.clone());

    // Load and parse the layer.
    let mut data = open_layer(resolver, &resolved)?;

    // Collect all asset paths that need recursive loading.
    let referenced = collect_asset_paths(data.as_mut());

    // Recurse into discovered layers, anchored to the current layer.
    let is_usdz = resolved.extension().and_then(|e| e.to_str()) == Some("usdz");
    if is_usdz && !referenced.is_empty() {
        bail!(
            "cross-file references within USDZ archives are not yet supported: {}",
            resolved
        );
    }

    for ref_path in &referenced {
        collect_recursive(resolver, ref_path, Some(&resolved), layers, visited)?;
    }

    layers.push(Layer::new(identifier, data));

    Ok(())
}

/// Collects all asset paths from sublayers, references, and payloads in a layer.
fn collect_asset_paths(data: &mut dyn AbstractData) -> Vec<String> {
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
fn collect_prim_paths(data: &mut dyn AbstractData) -> Vec<Path> {
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

/// Opens a layer from a resolved path, auto-detecting the format.
fn open_layer(resolver: &impl Resolver, resolved: &ar::ResolvedPath) -> Result<Box<dyn AbstractData>> {
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

    // -----------------------------------------------------------------------
    // Sublayers
    // -----------------------------------------------------------------------

    #[test]
    fn sublayer_same_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_same_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2, "root + 1 sublayer");
        assert!(stack.root().identifier.contains("sublayer_same_folder.usda"));
        assert!(stack.layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_child_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_child_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2);
        assert!(stack.layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_parent_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2);
        assert!(stack.layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // References
    // -----------------------------------------------------------------------

    #[test]
    fn reference_same_folder() -> Result<()> {
        let path = composition_path("references/reference_same_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2, "root + 1 referenced layer");
        assert!(stack.layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_child_folder() -> Result<()> {
        let path = composition_path("references/reference_child_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2);
        assert!(stack.layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_parent_folder() -> Result<()> {
        let path = composition_path("references/reference_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2);
        assert!(stack.layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Payloads
    // -----------------------------------------------------------------------

    #[test]
    fn payload_same_folder() -> Result<()> {
        let path = composition_path("payload/payload_same_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2, "root + 1 payload layer");
        assert!(stack.layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn payload_child_folder() -> Result<()> {
        let path = composition_path("payload/payload_child_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2);
        assert!(stack.layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn payload_parent_folder() -> Result<()> {
        let path = composition_path("payload/payload_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        assert_eq!(stack.len(), 2);
        assert!(stack.layers[1].identifier.contains("_parent_stage.usda"));
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Multi-level composition
    // -----------------------------------------------------------------------

    #[test]
    fn teapot_multi_level() -> Result<()> {
        let path = format!("{}/vendor/usd-wg-assets/full_assets/Teapot/Teapot.usd", manifest_dir());
        let resolver = DefaultResolver::new();
        let stack = collect_layers(&resolver, &path)?;

        // Teapot.usd -> payload Teapot_Payload.usd -> sublayer Teapot_Materials.usd
        assert!(stack.len() >= 3, "expected at least 3 layers, got {}", stack.len());

        assert!(stack.root().identifier.contains("Teapot.usd"));

        let ids = stack.identifiers();
        assert!(ids.iter().any(|id| id.contains("Teapot_Payload")));
        assert!(ids.iter().any(|id| id.contains("Teapot_Materials")));

        Ok(())
    }
}
