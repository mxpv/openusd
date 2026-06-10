//! Layer stack collection.
//!
//! Given a root USD file, [`Collector`] uses an [`ar::Resolver`] to recursively
//! resolve and load every layer the stage depends on — following sublayers,
//! references, and payloads across files and formats (`.usda`, `.usdc`, `.usd`,
//! `.usdz`). The result is a [`Vec`] of [`sdf::Layer`]s, each wrapping a
//! parsed [`sdf::AbstractData`] with its resolved identity. Cycles are
//! detected and skipped automatically.
//!
//! The [`sdf::Layer`] type itself, along with its authoring surface and
//! persistence (`save`/`save_as`), lives in [`crate::sdf`] — the Rust
//! equivalent of C++ `SdfLayer`.

use std::collections::{HashMap, HashSet};
use std::io::Cursor;

use anyhow::{bail, Context, Result};

use crate::sdf::expr;
use crate::{ar, sdf, usda, usdc, usdz};

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

/// An error encountered during layer collection that may be recoverable.
///
/// Some errors, such as missing referenced files, can be tolerated so collection
/// can continue. [`Collector::on_error`] configures that policy.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum Error {
    /// An asset path could not be resolved to a physical location.
    #[error(
        "failed to resolve {kind} asset: {asset_path} (referenced by {referencing_layer}{})",
        "prim_path.as_ref().map(|p| format!(\" at {p}\")).unwrap_or_default()"
    )]
    UnresolvedAsset {
        /// The asset path that could not be resolved.
        asset_path: String,
        /// The layer that declared this dependency.
        referencing_layer: String,
        /// What kind of composition arc declared this dependency.
        kind: DependencyKind,
        /// The prim that declared this arc (`None` for sublayers).
        prim_path: Option<sdf::Path>,
    },
}

/// A dependency discovered while walking a layer's scene graph.
struct Dependency {
    /// The asset path to resolve.
    asset_path: String,
    /// What kind of composition arc declared this dependency.
    kind: DependencyKind,
    /// The prim that declared this arc (`None` for sublayers).
    prim_path: Option<sdf::Path>,
}

struct CollectionContext<'a> {
    load_payloads: bool,
    include_prim_dependency: Option<&'a dyn Fn(&sdf::Path) -> bool>,
    on_error: &'a dyn Fn(Error) -> Result<()>,
}

impl<'a> CollectionContext<'a> {
    fn with_filter(&self, include_prim_dependency: Option<&'a dyn Fn(&sdf::Path) -> bool>) -> Self {
        Self {
            load_payloads: self.load_payloads,
            include_prim_dependency,
            on_error: self.on_error,
        }
    }
}

type StrictErrorHandler = fn(Error) -> Result<()>;

fn strict_error(e: Error) -> Result<()> {
    bail!("{e}")
}

/// Builder for collecting a root layer and all layers it depends on.
pub struct Collector<'a, R: ar::Resolver, E: Fn(Error) -> Result<()> = StrictErrorHandler> {
    resolver: &'a R,
    load_payloads: bool,
    include_prim_dependency: Option<&'a dyn Fn(&sdf::Path) -> bool>,
    on_error: E,
}

impl<'a, R: ar::Resolver> Collector<'a, R, StrictErrorHandler> {
    /// Creates a collector that errors on any unresolvable dependency and
    /// follows payload arcs. Use [`Collector::on_error`] or
    /// [`Collector::load_payloads`] to override.
    pub fn new(resolver: &'a R) -> Self {
        Self {
            resolver,
            load_payloads: true,
            include_prim_dependency: None,
            on_error: strict_error,
        }
    }
}

impl<'a, R: ar::Resolver, E: Fn(Error) -> Result<()>> Collector<'a, R, E> {
    /// Controls whether payload dependencies are followed.
    ///
    /// When `load_payloads` is `false`, payload arcs are left as authored
    /// metadata but their target layers are not loaded during collection.
    pub fn load_payloads(mut self, load_payloads: bool) -> Self {
        self.load_payloads = load_payloads;
        self
    }

    /// Sets a callback for recoverable layer collection errors.
    ///
    /// The callback decides whether to continue (`Ok(())`) or abort (`Err(...)`)
    /// for each recoverable error encountered.
    pub fn on_error<E2: Fn(Error) -> Result<()>>(self, on_error: E2) -> Collector<'a, R, E2> {
        Collector {
            resolver: self.resolver,
            load_payloads: self.load_payloads,
            include_prim_dependency: self.include_prim_dependency,
            on_error,
        }
    }

    /// Skips reference/payload dependencies whose authoring prim path fails
    /// `include`. Used by `StageBuilder` to honor `StagePopulationMask` during
    /// root-layer-stack collection so culled-subtree dependencies aren't
    /// resolved or loaded. Crate-internal pending a public design.
    pub(crate) fn prim_dependency_filter(mut self, include: &'a dyn Fn(&sdf::Path) -> bool) -> Self {
        self.include_prim_dependency = Some(include);
        self
    }

    /// Opens a root layer and recursively collects all referenced layers.
    ///
    /// Returns a [`Vec<sdf::Layer>`] with the root (strongest) layer first.
    pub fn collect(&self, root_path: &str) -> Result<Vec<sdf::Layer>> {
        let mut layers = Vec::new();
        let mut visited = HashSet::new();
        let context = CollectionContext {
            load_payloads: self.load_payloads,
            include_prim_dependency: self.include_prim_dependency,
            on_error: &self.on_error,
        };

        collect_recursive(
            self.resolver,
            root_path,
            None,
            &context,
            &HashMap::new(),
            &mut layers,
            &mut visited,
        )?;

        // Layers are collected in post-order (leaves first), reverse so root is first.
        layers.reverse();

        Ok(layers)
    }
}

/// Recursive layer collector.
///
/// `ancestor_expr_vars` are the expression variables composed from the
/// referencing layer stacks above this one (empty at the root). They are
/// applied over this layer's own `expressionVariables` so a closer-to-root
/// stack's override wins (C++ `PcpExpressionVariables`); the combined set then
/// drives expression evaluation in this layer's asset paths and is threaded
/// into each child arc. Without this, an asset-path expression would evaluate
/// against only the local variables during collection while the `pcp` builder
/// evaluates it against the composed set, so a referencing override could
/// resolve an arc to a layer collection never loaded — leaving the valid arc
/// dropped as `UnresolvedLayer`.
///
/// TODO(expr-vars): two gaps remain versus a faithful `PcpExpressionVariables`:
///
/// 1. Within a layer stack the variables are not pre-composed: a sublayer sees
///    only the variables of layers that sublayer it (applied as ancestors), not
///    those of its weaker sibling sublayers, so a variable a weaker sublayer
///    authors but a stronger layer's arc uses is missed.
/// 2. A layer reached through two arcs with different composed variables is
///    collected once (the `visited` set is keyed by identifier alone), so an
///    expression that resolves to different targets on each path only loads the
///    first. Both targets must be loaded.
///
/// The durable fix is to stop evaluating asset-path expressions in two places.
/// Collection and the `pcp` builder should share one `PcpExpressionVariables`
/// computation — ideally by having composition drive layer loading lazily —
/// rather than two evaluators that must be kept in agreement.
fn collect_recursive(
    resolver: &impl ar::Resolver,
    asset_path: &str,
    anchor: Option<&ar::ResolvedPath>,
    context: &CollectionContext<'_>,
    ancestor_expr_vars: &HashMap<String, sdf::Value>,
    layers: &mut Vec<sdf::Layer>,
    visited: &mut HashSet<String>,
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

    // Compose this layer's authored expression variables with those inherited
    // from the referencing layer stacks; the inherited (closer-to-root) set is
    // applied last so it overrides this layer's own (C++ `PcpExpressionVariables`).
    let mut expr_vars = expr::read_expression_variables(data.as_ref())?;
    expr_vars.extend(ancestor_expr_vars.iter().map(|(k, v)| (k.clone(), v.clone())));

    // Collect typed dependencies from this layer.
    let deps = collect_dependencies(data.as_ref(), context.load_payloads)?;

    let is_usdz = resolved.extension().and_then(|e| e.to_str()) == Some("usdz");

    for dep in deps {
        if let (Some(include), Some(prim_path)) = (context.include_prim_dependency, dep.prim_path.as_ref()) {
            if !include(prim_path) {
                continue;
            }
        }

        // Evaluate expression-valued asset paths.
        let dep_asset = expr::evaluate_asset_path(&dep.asset_path, &expr_vars)?;

        if is_usdz {
            bail!(
                "cross-file references within USDZ archives are not yet supported: {}",
                resolved
            );
        }

        // Check if this dependency resolves before recursing.
        let dep_id = resolver.create_identifier(&dep_asset, Some(&resolved));
        if !visited.contains(&dep_id) && resolver.resolve(&dep_id).is_none() {
            (context.on_error)(Error::UnresolvedAsset {
                asset_path: dep_asset,
                referencing_layer: identifier.clone(),
                kind: dep.kind,
                prim_path: dep.prim_path,
            })?;
            visited.insert(dep_id);
            continue;
        }

        // References and payloads enter a new layer's namespace, so the
        // caller's prim-path filter (rooted in the originating namespace) no
        // longer applies. Sublayers share the parent's namespace and keep it.
        let child_filter = match dep.kind {
            DependencyKind::SubLayer => context.include_prim_dependency,
            DependencyKind::Reference | DependencyKind::Payload => None,
        };
        collect_recursive(
            resolver,
            &dep_asset,
            Some(&resolved),
            &context.with_filter(child_filter),
            &expr_vars,
            layers,
            visited,
        )?;
    }

    layers.push(sdf::Layer::new(identifier, data));

    Ok(())
}

/// Collects typed dependencies from sublayers, references, and optionally
/// payloads in a layer.
fn collect_dependencies(data: &dyn sdf::AbstractData, load_payloads: bool) -> Result<Vec<Dependency>> {
    let mut deps = Vec::new();

    let root = sdf::Path::abs_root();

    // Sublayers (layer-level).
    if let Some(value) = data.try_get(&root, sdf::FieldKey::SubLayers.as_str())? {
        if let sdf::Value::StringVec(sub_paths) = value.into_owned() {
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
    let prim_paths = collect_prim_paths(data)?;
    for prim_path in &prim_paths {
        // References.
        if let Some(value) = data.try_get(prim_path, sdf::FieldKey::References.as_str())? {
            if let sdf::Value::ReferenceListOp(list_op) = value.as_ref() {
                for r in list_op.iter().filter(|r| !r.asset_path.is_empty()) {
                    deps.push(Dependency {
                        asset_path: r.asset_path.clone(),
                        kind: DependencyKind::Reference,
                        prim_path: Some(prim_path.clone()),
                    });
                }
            }
        }

        if load_payloads {
            // Payloads.
            if let Some(value) = data.try_get(prim_path, sdf::FieldKey::Payload.as_str())? {
                match value.as_ref() {
                    sdf::Value::Payload(p) if !p.asset_path.is_empty() => {
                        deps.push(Dependency {
                            asset_path: p.asset_path.clone(),
                            kind: DependencyKind::Payload,
                            prim_path: Some(prim_path.clone()),
                        });
                    }
                    sdf::Value::PayloadListOp(list_op) => {
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
    }

    Ok(deps)
}

/// Collects all prim and variant spec paths by walking `primChildren`,
/// `variantSetChildren`, and `variantChildren` hierarchies.
fn collect_prim_paths(data: &dyn sdf::AbstractData) -> Result<Vec<sdf::Path>> {
    let mut result = Vec::new();
    let mut queue = vec![sdf::Path::abs_root()];

    while let Some(path) = queue.pop() {
        if !data.has_spec(&path) {
            continue;
        }

        // Skip the pseudo-root itself but process its children.
        if path != sdf::Path::abs_root() {
            result.push(path.clone());
        }

        // Regular prim children.
        if let Some(value) = data.try_get(&path, sdf::ChildrenKey::PrimChildren.as_str())? {
            if let sdf::Value::TokenVec(children) = value.into_owned() {
                for name in children.iter().rev() {
                    if let Ok(child) = path.append_path(name.as_str()) {
                        queue.push(child);
                    }
                }
            }
        }

        // Variant set children (e.g. /Prim -> /Prim{setName=}).
        if let Some(value) = data.try_get(&path, sdf::ChildrenKey::VariantSetChildren.as_str())? {
            if let sdf::Value::TokenVec(set_names) = value.into_owned() {
                for set_name in &set_names {
                    // Variant children within each set (e.g. /Prim{setName=selA}).
                    let set_path = path.append_variant_selection(set_name, "");
                    if let Some(value) = data.try_get(&set_path, sdf::ChildrenKey::VariantChildren.as_str())? {
                        if let sdf::Value::TokenVec(variant_names) = value.into_owned() {
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

    Ok(result)
}

/// Opens a single layer from a resolved path, auto-detecting the format.
///
/// Supports `.usda` (text), `.usdc` (binary), `.usd` (auto-detected via magic
/// bytes), and `.usdz` (archive — reads the first layer). Returns the parsed
/// data as a boxed [`sdf::AbstractData`].
pub fn open_layer(resolver: &dyn ar::Resolver, resolved: &ar::ResolvedPath) -> Result<sdf::LayerData> {
    let ext = resolved.extension().and_then(|e| e.to_str()).unwrap_or_default();

    let mut asset = resolver.open_asset(resolved)?;
    let bytes = asset.read_all()?;

    if ext == "usdz" {
        let mut archive = usdz::Archive::from_reader(Cursor::new(bytes)).context("failed to open USDZ archive")?;
        return archive
            .read_first_layer()
            .context("failed to read first layer from USDZ archive");
    }

    // For .usd files, sniff magic bytes to detect binary vs text format.
    let is_binary = ext == "usdc" || (ext == "usd" && bytes.starts_with(usdc::MAGIC));

    if is_binary {
        let data = usdc::CrateData::open(Cursor::new(bytes), true).context("failed to parse USDC layer")?;
        Ok(Box::new(data))
    } else {
        let content = String::from_utf8(bytes).context("layer is not valid UTF-8")?;
        let data = usda::parse(&content).context("failed to parse USDA layer")?;
        Ok(Box::new(data))
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::ar::{DefaultResolver, Resolver};
    use crate::sdf::AbstractData;

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
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved sublayer");
        assert!(layers[0].identifier.contains("expr_sublayer.usda"));
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn expression_reference() -> Result<()> {
        let path = fixture_path("expr_reference.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 expression-resolved reference");
        assert!(layers[1].identifier.contains("expr_sublayer_target.usda"));
        Ok(())
    }

    #[test]
    fn expression_asset_path() -> Result<()> {
        let path = fixture_path("expr_asset_path.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

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
        let layers = Collector::new(&resolver).collect(&path)?;

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
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 sublayer");
        assert!(layers[0].identifier.contains("sublayer_same_folder.usda"));
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_child_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn sublayer_parent_folder() -> Result<()> {
        let path = composition_path("subLayer/sublayer_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

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
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 referenced layer");
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_child_folder() -> Result<()> {
        let path = composition_path("references/reference_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn reference_parent_folder() -> Result<()> {
        let path = composition_path("references/reference_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

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
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2, "root + 1 payload layer");
        assert!(layers[1].identifier.contains("_stage.usda"));
        Ok(())
    }

    #[test]
    fn skip_payloads() -> Result<()> {
        let resolver = DefaultResolver::new();

        let path = composition_path("payload/payload_same_folder.usda");
        let layers = Collector::new(&resolver)
            .load_payloads(false)
            .on_error(|_| Ok(()))
            .collect(&path)?;
        assert_eq!(layers.len(), 1);
        assert!(layers[0].identifier.contains("payload_same_folder.usda"));

        let errors = RefCell::new(0);
        let path = composition_path("payload/payload_invalid.usda");
        let layers = Collector::new(&resolver)
            .load_payloads(false)
            .on_error(|_| {
                *errors.borrow_mut() += 1;
                Ok(())
            })
            .collect(&path)?;
        assert_eq!(layers.len(), 1);
        assert_eq!(*errors.borrow(), 0);
        Ok(())
    }

    #[test]
    fn payload_child_folder() -> Result<()> {
        let path = composition_path("payload/payload_child_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

        assert_eq!(layers.len(), 2);
        assert!(layers[1].identifier.contains("_child_stage.usda"));
        Ok(())
    }

    #[test]
    fn payload_parent_folder() -> Result<()> {
        let path = composition_path("payload/payload_parent_folder.usda");
        let resolver = DefaultResolver::new();
        let layers = Collector::new(&resolver).collect(&path)?;

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
        let layers = Collector::new(&resolver).collect(&path)?;

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
    fn strict_errors_on_missing_reference() {
        let path = composition_path("references/reference_invalid.usda");
        let resolver = DefaultResolver::new();
        assert!(Collector::new(&resolver).collect(&path).is_err());
    }

    /// Custom handler receives correct error details for each dependency kind.
    #[test]
    fn handler_receives_error() -> Result<()> {
        let resolver = DefaultResolver::new();
        let errors = RefCell::new(Vec::new());

        let path = composition_path("references/reference_invalid.usda");
        Collector::new(&resolver)
            .on_error(|e| {
                errors.borrow_mut().push(e);
                Ok(())
            })
            .collect(&path)?;

        let path = composition_path("payload/payload_invalid.usda");
        Collector::new(&resolver)
            .on_error(|e| {
                errors.borrow_mut().push(e);
                Ok(())
            })
            .collect(&path)?;

        let path = composition_path("subLayer/sublayer_invalid.usda");
        Collector::new(&resolver)
            .on_error(|e| {
                errors.borrow_mut().push(e);
                Ok(())
            })
            .collect(&path)?;

        let errors = errors.into_inner();
        assert_eq!(errors.len(), 3);

        let Error::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[0];
        assert_eq!(kind, DependencyKind::Reference);
        assert_eq!(prim_path.as_ref().unwrap().as_str(), "/World/invalid_reference");

        let Error::UnresolvedAsset {
            kind, ref prim_path, ..
        } = errors[1];
        assert_eq!(kind, DependencyKind::Payload);
        assert_eq!(prim_path.as_ref().unwrap().as_str(), "/World/invalid_payload");

        let Error::UnresolvedAsset {
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
        let layers = Collector::new(&resolver).on_error(|_| Ok(())).collect(&path)?;

        // Root layer loads despite the missing reference.
        assert_eq!(layers.len(), 1);
        assert!(layers[0].identifier.contains("reference_invalid.usda"));
        Ok(())
    }

    #[test]
    fn filter_skips_dependency() -> Result<()> {
        let path = composition_path("references/reference_invalid.usda");
        let resolver = DefaultResolver::new();
        let errors = RefCell::new(0);
        let include = |path: &sdf::Path| path.as_str() == "/World/cube";
        let layers = Collector::new(&resolver)
            .prim_dependency_filter(&include)
            .on_error(|_| {
                *errors.borrow_mut() += 1;
                Ok(())
            })
            .collect(&path)?;

        assert_eq!(layers.len(), 1);
        assert_eq!(*errors.borrow(), 0);
        assert!(layers[0].identifier.contains("reference_invalid.usda"));
        Ok(())
    }

    #[test]
    fn save_dispatches_on_extension() -> Result<()> {
        use crate::sdf::{self, SpecType};

        let mut data = sdf::Data::new();
        let root = sdf::Path::abs_root();
        let ps = data.create_spec(root, SpecType::PseudoRoot);
        ps.add("primChildren", sdf::Value::TokenVec(vec!["Foo".into()]));
        let foo = sdf::path("/Foo")?;
        let sp = data.create_spec(foo, SpecType::Prim);
        sp.add("specifier", sdf::Value::Specifier(sdf::Specifier::Def));
        sp.add("typeName", sdf::Value::Token("Xform".into()));

        let layer = sdf::Layer::new("test://layer", Box::new(data));
        let dir = tempfile::tempdir()?;

        let usda_path = dir.path().join("layer-save.usda");
        let usdc_path = dir.path().join("layer-save.usdc");
        let usdz_path = dir.path().join("layer-save.usdz");

        layer.save(&usda_path)?;
        layer.save(&usdc_path)?;
        layer.save(&usdz_path)?;

        assert!(std::fs::metadata(&usda_path)?.len() > 0);
        assert!(std::fs::metadata(&usdc_path)?.len() > 0);
        assert!(std::fs::metadata(&usdz_path)?.len() > 0);

        // The usdz should contain an entry we can read back.
        let archive = crate::usdz::Archive::open(&usdz_path)?;
        let name = archive.first_layer_name().expect("usdz has a layer");
        assert!(name.ends_with(".usdc"));
        Ok(())
    }

    #[test]
    fn save_as_usd_writes_binary_and_roundtrips() -> Result<()> {
        use crate::sdf::{self, SpecType};

        let mut data = sdf::Data::new();
        let root = sdf::Path::abs_root();
        let ps = data.create_spec(root, SpecType::PseudoRoot);
        ps.add("primChildren", sdf::Value::TokenVec(vec!["Bar".into()]));
        let bar = sdf::path("/Bar")?;
        let sp = data.create_spec(bar.clone(), SpecType::Prim);
        sp.add("specifier", sdf::Value::Specifier(sdf::Specifier::Def));
        sp.add("typeName", sdf::Value::Token("Cube".into()));

        let layer = sdf::Layer::new("test://layer-usd", Box::new(data));
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("layer-save.usd");
        layer.save(&path)?;

        // Writer chose binary for `.usd` — first bytes must be the USDC magic.
        let bytes = std::fs::read(&path)?;
        assert!(
            bytes.starts_with(crate::usdc::MAGIC),
            "writer should emit binary for .usd, got magic {:?}",
            &bytes[..crate::usdc::MAGIC.len().min(bytes.len())],
        );

        // Reader's magic-byte auto-detection must accept it.
        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve(path.to_str().unwrap()).unwrap();
        let round = open_layer(&resolver, &resolved)?;
        assert_eq!(round.spec_type(&bar), Some(SpecType::Prim));
        assert_eq!(
            round.get(&bar, "typeName").unwrap().into_owned(),
            sdf::Value::Token("Cube".into())
        );
        Ok(())
    }

    #[test]
    fn save_rejects_unknown_extension() {
        use crate::sdf::{self, SpecType};
        let mut data = sdf::Data::new();
        data.create_spec(sdf::Path::abs_root(), SpecType::PseudoRoot);
        let layer = sdf::Layer::new("test://layer", Box::new(data));
        let err = layer.save("/tmp/openusd-bad.xyz").unwrap_err();
        assert!(err.to_string().contains("unsupported"));
    }

    /// Per spec §16.2, `.usd` is a valid extension for text layers. Verify we
    /// can force-write text to a `.usd` file and the reader correctly
    /// auto-detects it as text via the absence of the USDC magic.
    #[test]
    fn save_as_forces_text_to_usd_extension() -> Result<()> {
        use crate::sdf::{self, SpecType};

        let mut data = sdf::Data::new();
        let root = sdf::Path::abs_root();
        let ps = data.create_spec(root, SpecType::PseudoRoot);
        ps.add("primChildren", sdf::Value::TokenVec(vec!["Text".into()]));
        let prim = sdf::path("/Text")?;
        let sp = data.create_spec(prim.clone(), SpecType::Prim);
        sp.add("specifier", sdf::Value::Specifier(sdf::Specifier::Def));
        sp.add("typeName", sdf::Value::Token("Xform".into()));

        let layer = sdf::Layer::new("test://text-as-usd", Box::new(data));
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("text-as-usd.usd");
        layer.save_as(&path, sdf::LayerFormat::Usda)?;

        // Emitted bytes must NOT start with the binary magic — they're text.
        let bytes = std::fs::read(&path)?;
        assert!(
            !bytes.starts_with(crate::usdc::MAGIC),
            "save_as(Usda) should produce text, but output begins with USDC magic",
        );
        assert!(bytes.starts_with(b"#usda"), "text output must start with #usda header");

        // Reader auto-detect (magic-byte sniff) accepts it as text.
        let resolver = DefaultResolver::new();
        let resolved = resolver.resolve(path.to_str().unwrap()).unwrap();
        let round = open_layer(&resolver, &resolved)?;
        assert_eq!(round.spec_type(&prim), Some(SpecType::Prim));
        assert_eq!(
            round.get(&prim, "typeName").unwrap().into_owned(),
            sdf::Value::Token("Xform".into())
        );
        Ok(())
    }

    #[test]
    fn layer_format_from_extension_matches_spec() {
        assert_eq!(sdf::LayerFormat::from_extension("usda"), Some(sdf::LayerFormat::Usda));
        assert_eq!(sdf::LayerFormat::from_extension("usdc"), Some(sdf::LayerFormat::Usdc));
        assert_eq!(sdf::LayerFormat::from_extension("usd"), Some(sdf::LayerFormat::Usdc));
        assert_eq!(sdf::LayerFormat::from_extension("USDA"), Some(sdf::LayerFormat::Usda));
        assert_eq!(sdf::LayerFormat::from_extension("usdz"), Some(sdf::LayerFormat::Usdz));
        assert_eq!(sdf::LayerFormat::from_extension("xyz"), None);
        assert_eq!(sdf::LayerFormat::from_extension(""), None);
    }

    // -----------------------------------------------------------------------
    // Authoring API
    // -----------------------------------------------------------------------

    #[test]
    fn create_prim_basic() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        let mut prim = layer.create_prim("/World", sdf::Specifier::Def, "Xform")?;
        prim.set_kind("group");

        let world = layer.prim("/World").expect("prim authored");
        assert_eq!(world.type_name().as_deref(), Some("Xform"));
        assert_eq!(world.specifier(), Some(sdf::Specifier::Def));
        assert_eq!(world.kind().as_deref(), Some("group"));
        Ok(())
    }

    #[test]
    fn auto_ancestor_chain() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.create_prim("/A/B/C", sdf::Specifier::Def, "Mesh")?;

        // Leaf is Def; ancestors are Over.
        assert_eq!(
            layer.prim("/A/B/C").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Def)
        );
        assert_eq!(
            layer.prim("/A/B").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Over)
        );
        assert_eq!(layer.prim("/A").and_then(|p| p.specifier()), Some(sdf::Specifier::Over));
        Ok(())
    }

    #[test]
    fn prim_children() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.create_prim("/World", sdf::Specifier::Def, "Xform")?;
        layer.create_prim("/World/Mesh", sdf::Specifier::Def, "Mesh")?;
        layer.create_prim("/World/Cube", sdf::Specifier::Def, "Cube")?;

        let root = layer.pseudo_root().expect("pseudo-root present");
        let root_children = root.prim_children().unwrap();
        let root_children: Vec<&str> = root_children.iter().map(|t| t.as_str()).collect();
        assert_eq!(root_children, ["World"]);

        let world = layer.prim("/World").expect("prim");
        let world_children = world.prim_children().unwrap();
        let world_children: Vec<&str> = world_children.iter().map(|t| t.as_str()).collect();
        assert_eq!(world_children, ["Mesh", "Cube"]);
        Ok(())
    }

    #[test]
    fn property_children() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.create_prim("/Mesh", sdf::Specifier::Def, "Mesh")?;
        layer.create_attribute("/Mesh.points", "point3f[]", sdf::Variability::Varying, false)?;
        layer.create_attribute("/Mesh.normals", "normal3f[]", sdf::Variability::Varying, false)?;
        layer.create_relationship("/Mesh.material:binding", sdf::Variability::Varying, false)?;

        let mesh = layer.prim("/Mesh").expect("prim");
        let props = mesh.property_children().unwrap();
        let props: Vec<&str> = props.iter().map(|t| t.as_str()).collect();
        assert_eq!(props, ["points", "normals", "material:binding"]);
        Ok(())
    }

    #[test]
    fn relationship_variability() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.create_relationship("/Mesh.material:binding", sdf::Variability::Uniform, false)?;

        let rel = layer.relationship("/Mesh.material:binding").expect("relationship");
        assert_eq!(rel.variability(), sdf::Variability::Uniform);

        layer.create_relationship("/Mesh.material:binding", sdf::Variability::Varying, false)?;
        let rel = layer.relationship("/Mesh.material:binding").expect("relationship");
        assert_eq!(rel.variability(), sdf::Variability::Varying);
        assert!(rel.field(sdf::FieldKey::Variability.as_str()).ok().flatten().is_none());
        Ok(())
    }

    #[test]
    fn bad_prim_children_errors() {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.data_mut().set_field(
            &sdf::Path::abs_root(),
            sdf::ChildrenKey::PrimChildren.as_str(),
            sdf::Value::String("bad".into()),
        );

        let err = layer.create_prim("/A", sdf::Specifier::Def, "Xform").unwrap_err();
        assert!(matches!(err, sdf::AuthoringError::InvalidPath { .. }));

        let value = layer
            .data()
            .get(&sdf::Path::abs_root(), sdf::ChildrenKey::PrimChildren.as_str())
            .unwrap()
            .into_owned();
        assert!(matches!(value, sdf::Value::String(value) if value == "bad"));
    }

    #[test]
    fn bad_property_children_errors() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.create_prim("/Mesh", sdf::Specifier::Def, "Mesh")?;
        layer.data_mut().set_field(
            &sdf::path("/Mesh").unwrap(),
            sdf::ChildrenKey::PropertyChildren.as_str(),
            sdf::Value::String("bad".into()),
        );

        let err = layer
            .create_relationship("/Mesh.material:binding", sdf::Variability::Varying, false)
            .unwrap_err();
        assert!(matches!(err, sdf::AuthoringError::InvalidPath { .. }));

        assert!(!layer.data().has_spec(&sdf::path("/Mesh.material:binding").unwrap()));
        let value = layer
            .data()
            .get(
                &sdf::path("/Mesh").unwrap(),
                sdf::ChildrenKey::PropertyChildren.as_str(),
            )
            .unwrap()
            .into_owned();
        assert!(matches!(value, sdf::Value::String(value) if value == "bad"));
        Ok(())
    }

    #[test]
    fn attr_samples() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.create_prim("/Sphere", sdf::Specifier::Def, "Sphere")?;

        let mut radius = layer.create_attribute("/Sphere.radius", "double", sdf::Variability::Varying, false)?;
        radius.set_default(sdf::Value::Double(2.5));
        radius.set_time_sample(0.0, sdf::Value::Double(1.0));
        radius.set_time_sample(10.0, sdf::Value::Double(3.0));
        // Out-of-order insert lands in sorted position.
        radius.set_time_sample(5.0, sdf::Value::Double(2.0));

        let read = layer.attribute("/Sphere.radius").expect("attr");
        assert_eq!(read.type_name().as_deref(), Some("double"));
        assert_eq!(read.default(), Some(sdf::Value::Double(2.5)));
        let samples = read.time_samples().expect("samples authored");
        let times: Vec<f64> = samples.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![0.0, 5.0, 10.0]);
        Ok(())
    }

    #[test]
    fn wrong_ancestor_type() {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        // Plant a non-Prim spec at a prim-shaped path through the public data API.
        layer
            .data_mut()
            .create_spec(sdf::path("/A").unwrap(), sdf::SpecType::Attribute);

        let err = layer.create_prim("/A/B", sdf::Specifier::Def, "Xform").unwrap_err();
        assert!(matches!(err, sdf::AuthoringError::InvalidPath { .. }));
        let err = layer
            .create_attribute("/A.x", "double", sdf::Variability::Varying, false)
            .unwrap_err();
        assert!(matches!(err, sdf::AuthoringError::InvalidPath { .. }));
    }

    #[test]
    fn failed_prim_chain_creation_is_atomic() {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        let bad_child = sdf::path("/A/B").unwrap();
        layer.data_mut().create_spec(bad_child, sdf::SpecType::Attribute);

        let err = layer.create_prim("/A/B", sdf::Specifier::Def, "Xform").unwrap_err();
        assert!(matches!(err, sdf::AuthoringError::InvalidPath { .. }));

        assert!(!layer.data().has_spec(&sdf::path("/A").unwrap()));
        assert!(layer
            .data()
            .try_get(&sdf::Path::abs_root(), sdf::ChildrenKey::PrimChildren.as_str())
            .unwrap()
            .is_none());
    }

    #[test]
    fn nan_time_sample() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.create_prim("/Sphere", sdf::Specifier::Def, "Sphere")?;
        let mut r = layer.create_attribute("/Sphere.radius", "double", sdf::Variability::Varying, false)?;

        r.set_time_sample(1.0, sdf::Value::Double(1.0));
        r.set_time_sample(f64::NAN, sdf::Value::Double(99.0));
        r.set_time_sample(2.0, sdf::Value::Double(2.0));
        // NaN does not collide with finite samples — both finite values survive.
        let samples = layer
            .attribute("/Sphere.radius")
            .unwrap()
            .time_samples()
            .unwrap()
            .to_vec();
        let finite: Vec<f64> = samples.iter().map(|(t, _)| *t).filter(|t| t.is_finite()).collect();
        assert_eq!(finite, vec![1.0, 2.0]);

        // erase_time_sample(NaN) can find the NaN entry via total_cmp.
        assert!(layer
            .attribute_mut("/Sphere.radius")
            .unwrap()
            .erase_time_sample(f64::NAN));
        let times: Vec<f64> = layer
            .attribute("/Sphere.radius")
            .unwrap()
            .time_samples()
            .unwrap()
            .iter()
            .map(|(t, _)| *t)
            .collect();
        assert_eq!(times, vec![1.0, 2.0]);
        Ok(())
    }

    #[test]
    fn override_prim() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        layer.override_prim("/A/B")?;

        assert_eq!(layer.prim("/A").and_then(|p| p.specifier()), Some(sdf::Specifier::Over));
        assert_eq!(
            layer.prim("/A/B").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Over)
        );

        // override_prim on an existing def leaves the specifier untouched.
        layer.create_prim("/Defined", sdf::Specifier::Def, "Xform")?;
        layer.override_prim("/Defined")?;
        assert_eq!(
            layer.prim("/Defined").and_then(|p| p.specifier()),
            Some(sdf::Specifier::Def)
        );
        Ok(())
    }

    #[test]
    fn pseudo_root_metadata() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        {
            let mut root = layer.pseudo_root_mut().expect("writable");
            root.set_default_prim("World");
            root.set_documentation("auto-generated");
            root.set_start_time_code(1.0);
            root.set_end_time_code(24.0);
            root.add_sublayer("./over.usda");
            root.add_sublayer("./over.usda");
        }
        let root = layer.pseudo_root().expect("present");
        assert_eq!(root.default_prim().as_deref(), Some("World"));
        assert_eq!(root.documentation().as_deref(), Some("auto-generated"));
        assert_eq!(root.start_time_code(), Some(1.0));
        assert_eq!(root.end_time_code(), Some(24.0));
        assert_eq!(
            root.sublayers(),
            Some(vec!["./over.usda".to_string(), "./over.usda".to_string()])
        );
        Ok(())
    }

    #[test]
    fn invalid_paths() {
        let mut layer = sdf::Layer::new_anonymous("anon.usda");
        assert!(matches!(
            layer.create_prim("/", sdf::Specifier::Def, "Xform").unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        assert!(matches!(
            layer.create_prim("/A.foo", sdf::Specifier::Def, "Xform").unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        assert!(matches!(
            layer
                .create_attribute("/A", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        // Relative property paths must error, not panic in ensure_prim_chain.
        assert!(matches!(
            layer
                .create_attribute("A.foo", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        assert!(matches!(
            layer
                .create_relationship("A.foo", sdf::Variability::Varying, false)
                .unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        // Root-level property paths (`/.foo`) must also error, not panic.
        assert!(matches!(
            layer
                .create_attribute("/.foo", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        // Target-bracket property paths slip past `is_property_path` because the
        // tail after the last `.` is alphanumeric — split_property_path must reject them.
        assert!(matches!(
            layer
                .create_attribute("/A.rel[/Target].attr", "double", sdf::Variability::Varying, false)
                .unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        // Well-formed variant selections are authorable (they build the variant
        // set / variant scaffolding), but malformed ones — here an empty
        // selection — must still be rejected.
        assert!(matches!(
            layer
                .create_prim("/A{x=}child", sdf::Specifier::Def, "Xform")
                .unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
    }

    /// Authoring a prim inside a variant builds the full variant set / variant
    /// scaffolding with correct spec types and child registration.
    #[test]
    fn variant_authoring() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("variants.usda");
        layer.create_prim("/Prim", sdf::Specifier::Def, "Xform")?;
        layer.create_prim("/Prim{set=sel}child", sdf::Specifier::Def, "Scope")?;

        assert_eq!(layer.data().spec_type(&sdf::path("/Prim")?), Some(sdf::SpecType::Prim));
        assert_eq!(
            layer.data().spec_type(&sdf::path("/Prim{set=}")?),
            Some(sdf::SpecType::VariantSet)
        );
        assert_eq!(
            layer.data().spec_type(&sdf::path("/Prim{set=sel}")?),
            Some(sdf::SpecType::Variant)
        );
        assert_eq!(
            layer.data().spec_type(&sdf::path("/Prim{set=sel}child")?),
            Some(sdf::SpecType::Prim)
        );

        let token_vec = |path: &str, key: sdf::ChildrenKey| -> Result<Vec<String>> {
            match layer.data().get(&sdf::path(path)?, key.as_str())?.into_owned() {
                sdf::Value::TokenVec(v) => Ok(v.into_iter().map(Into::into).collect()),
                other => panic!("expected TokenVec at {path}, got {other:?}"),
            }
        };
        assert_eq!(token_vec("/Prim", sdf::ChildrenKey::VariantSetChildren)?, vec!["set"]);
        assert_eq!(
            token_vec("/Prim{set=}", sdf::ChildrenKey::VariantChildren)?,
            vec!["sel"]
        );
        assert_eq!(
            token_vec("/Prim{set=sel}", sdf::ChildrenKey::PrimChildren)?,
            vec!["child"]
        );
        Ok(())
    }

    /// A bare variant-selection leaf isn't a prim, so prim authoring rejects it
    /// (rather than panicking on the `PrimSpecMut` downcast or writing prim
    /// fields onto the variant spec).
    #[test]
    fn prim_authoring_rejects_variant_leaf() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("variants.usda");
        layer.create_prim("/Prim", sdf::Specifier::Def, "Xform")?;
        assert!(matches!(
            layer
                .create_prim("/Prim{set=sel}", sdf::Specifier::Def, "Xform")
                .unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        assert!(matches!(
            layer.override_prim("/Prim{set=sel}").unwrap_err(),
            sdf::AuthoringError::InvalidPath { .. }
        ));
        // The rejected calls must not have authored a variant spec.
        assert_eq!(layer.data().spec_type(&sdf::path("/Prim{set=sel}")?), None);
        Ok(())
    }

    #[test]
    fn usda_roundtrip() -> Result<()> {
        let mut layer = sdf::Layer::new_anonymous("scene.usda");
        layer.pseudo_root_mut().unwrap().set_default_prim("World");
        layer.create_prim("/World", sdf::Specifier::Def, "Xform")?;
        let mut sphere = layer.create_prim("/World/Sphere", sdf::Specifier::Def, "Sphere")?;
        sphere.set_kind("component");
        let mut radius = layer.create_attribute("/World/Sphere.radius", "double", sdf::Variability::Varying, false)?;
        radius.set_default(sdf::Value::Double(1.5));
        let material = sdf::path("/World/Material")?;
        layer.create_prim(&material, sdf::Specifier::Def, "Material")?;
        let mut binding =
            layer.create_relationship("/World/Sphere.material:binding", sdf::Variability::Varying, false)?;
        binding.add_target(material.clone());
        let mut surface = layer.create_attribute(
            "/World/Sphere.inputs:surface",
            "token",
            sdf::Variability::Varying,
            false,
        )?;
        surface.set_connection_paths([sdf::path("/World/Material.outputs:surface")?]);

        let tmp = std::env::temp_dir().join("openusd_authoring_roundtrip.usda");
        layer.save_as(&tmp, sdf::LayerFormat::Usda)?;

        let parsed = usda::read_file(&tmp)?;
        assert_eq!(parsed.spec_type(&sdf::path("/World")?), Some(sdf::SpecType::Prim));
        assert_eq!(
            parsed.spec_type(&sdf::path("/World/Sphere")?),
            Some(sdf::SpecType::Prim)
        );
        assert_eq!(
            parsed.spec_type(&sdf::path("/World/Sphere.radius")?),
            Some(sdf::SpecType::Attribute)
        );
        assert_eq!(
            parsed
                .get(&sdf::Path::abs_root(), sdf::FieldKey::DefaultPrim.as_str())?
                .into_owned(),
            sdf::Value::Token("World".into())
        );
        match parsed
            .get(
                &sdf::path("/World/Sphere.material:binding")?,
                sdf::FieldKey::TargetPaths.as_str(),
            )?
            .into_owned()
        {
            sdf::Value::PathListOp(op) => {
                assert!(op.explicit);
                assert_eq!(op.explicit_items, vec![material]);
            }
            other => panic!("expected relationship targets as PathListOp, got {other:?}"),
        }
        match parsed
            .get(
                &sdf::path("/World/Sphere.inputs:surface")?,
                sdf::FieldKey::ConnectionPaths.as_str(),
            )?
            .into_owned()
        {
            sdf::Value::PathListOp(op) => {
                assert!(op.explicit);
                assert_eq!(op.explicit_items, vec![sdf::path("/World/Material.outputs:surface")?]);
            }
            other => panic!("expected connection paths as PathListOp, got {other:?}"),
        }
        let _ = std::fs::remove_file(&tmp);
        Ok(())
    }
}
