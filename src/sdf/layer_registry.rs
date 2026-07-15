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

use anyhow::{Context, Result};

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
    /// path against `anchor`. Every canonical-identifier computation — interning a
    /// layer as it loads, anchoring an authored sublayer/arc path for lookup,
    /// keying the muted set — flows through here, so the underlying
    /// [`ar::Resolver`] stays private and the rules below apply uniformly.
    ///
    /// An anonymous layer identifier is its own canonical id: it names no
    /// asset-resolvable location, so it passes through unchanged (C++
    /// `SdfLayer::_GetCanonicalLayerId` / `ArResolver::CreateIdentifier`).
    /// Anchoring it against a layer would corrupt it into a bogus path that no
    /// interned layer matches.
    pub(crate) fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
        if sdf::Layer::is_anonymous_identifier(asset_path) {
            return asset_path.to_string();
        }
        self.resolver.create_identifier(asset_path, anchor)
    }

    /// Resolves `asset_path` against `anchor_location` — the resolved real path
    /// of the layer it is authored in (its
    /// [`real_path`](sdf::Layer::real_path), which for a package is the
    /// package-relative default layer, not the bare package identifier) —
    /// yielding the canonical identifier of the targeted layer. The convenience
    /// over [`create_identifier`](Self::create_identifier) for the common case
    /// of anchoring against another layer's location string rather than a
    /// pre-resolved [`ar::ResolvedPath`].
    ///
    /// TODO(perf): the resolver canonicalizes via the filesystem, so each call
    /// runs a `canonicalize`. Cache resolved identifiers per
    /// `(anchor_location, asset_path)`.
    pub(crate) fn create_identifier_anchored(&self, asset_path: &str, anchor_location: &str) -> String {
        self.create_identifier(asset_path, Some(&ar::ResolvedPath::new(PathBuf::from(anchor_location))))
    }

    /// Resolves an asset identifier to a physical location, or `None` if it does
    /// not exist.
    pub(crate) fn resolve(&self, identifier: &str) -> Option<ar::ResolvedPath> {
        self.resolver.resolve(identifier)
    }

    /// Resolves the layer the composition graph should open at `identifier`.
    ///
    /// This is [`resolve`](Self::resolve) deferred to the selected format's
    /// [`resolve_layer`](sdf::FileFormat::resolve_layer): a package
    /// (`pkg.usdz`) resolves to its default — first — packaged layer
    /// (`pkg.usdz[root.usd]`), so it composes as an ordinary layer stack and
    /// the sublayers and references authored inside it anchor in-package, while
    /// an ordinary format keeps the resolved location. Generic
    /// [`resolve`](Self::resolve) stays package-agnostic for asset-value
    /// resolution and the resolvability probe, which want the package path
    /// itself rather than a layer inside it. A resolved location no registered
    /// format claims passes through unchanged, so [`read`](Self::read) reports
    /// the missing format.
    ///
    /// The format is chosen by extension alone — unlike [`read`](Self::read),
    /// which content-sniffs the ambiguous `.usd`. That is sound because every
    /// `.usd` claimant keeps the identity default, so which one is picked does
    /// not change the real path; a future `.usd` format with a non-identity
    /// `resolve_layer` would need the content sniff here too.
    pub(crate) fn resolve_layer(&self, identifier: &str) -> Option<ar::ResolvedPath> {
        let resolved = self.resolver.resolve(identifier)?;
        match Self::find_by_extension(&resolved.extension()) {
            Some(format) => format.resolve_layer(self.resolver.as_ref(), &resolved),
            None => Some(resolved),
        }
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
        match self.resolve_layer(identifier) {
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
    /// `ancestor_expr_vars` are the overrides the stack that brought `asset_path`
    /// in supplies (the session root's own variables for the stage root stack, a
    /// reference/payload arc's composed set for a target). They overlay the root
    /// layer's own `expressionVariables` — the overrides win — to form the one
    /// context the whole stack resolves its expression-valued `subLayers` paths
    /// against (C++ `PcpExpressionVariables`). Sublayers of the root contribute no
    /// variables, so the context is fixed for the whole walk.
    ///
    /// This is a pure loader: it reports every load failure raw (a missing or
    /// unreadable sublayer, at whatever site reaches it) and knows nothing of
    /// muting. Whether such a failure is a stage diagnostic depends on composition
    /// reachability — a failure under a muted branch contributes nothing — which the
    /// composition layer decides once the muted-aware graph exists (see
    /// [`StageBuilder::make_stage`](crate::usd::Stage)). Keeping the muted policy out
    /// of the load walk avoids attributing a diagnostic to whichever branch happened
    /// to reach a shared layer first.
    /// The `expressionVariables` authored on the single layer at `asset_path`
    /// (anchored against `anchor`), read without opening its sublayers — the shallow
    /// read the stage root stack needs to compose its root and session layers' own
    /// variables into one context before either region's sublayer subtree is
    /// collected. An empty identifier yields an empty map; a resolve or read failure
    /// propagates.
    ///
    /// TODO(perf): the layer read here is read again when its stack is collected;
    /// the registry does not cache reads, so a root or session layer is parsed twice
    /// at open.
    pub(crate) fn own_expression_variables(
        &self,
        asset_path: &str,
        anchor: Option<&ar::ResolvedPath>,
    ) -> Result<HashMap<String, sdf::Value>> {
        let identifier = self.create_identifier(asset_path, anchor);
        if identifier.is_empty() {
            return Ok(HashMap::new());
        }
        let resolved = self
            .resolve_layer(&identifier)
            .with_context(|| format!("failed to resolve asset path: {asset_path}"))?;
        let data = self.read(&resolved)?;
        Ok(expr::read_expression_variables(data.as_ref())?.into_owned())
    }

    pub(crate) fn open_stack(
        &self,
        asset_path: &str,
        anchor: Option<&ar::ResolvedPath>,
        ancestor_expr_vars: &HashMap<String, sdf::Value>,
        reload: bool,
        on_error: &dyn Fn(Error) -> Result<()>,
        already_present: &dyn Fn(&str) -> bool,
    ) -> Result<Vec<sdf::Layer>> {
        let mut layers = Vec::new();
        let mut visited = HashSet::new();

        let identifier = self.create_identifier(asset_path, anchor);
        if identifier.is_empty() {
            return Ok(layers);
        }
        // With `reload`, an already-interned root and its already-present sublayers
        // are re-read and re-walked (but not re-emitted) so a re-open under a new
        // expression-variable context loads the `${VAR}` sublayers the context now
        // resolves — including ones nested below a literal sublayer — that a first,
        // variable-free open left unresolved. The caller only reloads for that case.
        //
        // The root must resolve and read; both failures propagate.
        let resolved = self
            .resolve_layer(&identifier)
            .with_context(|| format!("failed to resolve asset path: {asset_path}"))?;
        let data = self.read(&resolved)?;
        visited.insert(identifier.clone());

        // The whole stack resolves its `${VAR}` sublayers against one context (C++
        // `PcpExpressionVariables`): the root layer's own `expressionVariables`
        // overlaid by the inherited overrides. Sublayers contribute nothing, so it
        // is fixed for the walk.
        let stack_vars = expr::stack_expression_variables(data.as_ref(), ancestor_expr_vars)?;

        self.open_sublayers(
            identifier,
            resolved,
            data,
            &stack_vars,
            reload,
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
    /// `stack_vars` is the one context the whole stack resolves against (the root
    /// layer's own `expressionVariables` overlaid by the inherited overrides,
    /// computed once in [`open_stack`](Self::open_stack)). This layer's own
    /// `expressionVariables` do not contribute — only the stack root's do (C++
    /// `PcpExpressionVariables`) — so it is passed down unchanged.
    #[allow(clippy::too_many_arguments)]
    fn open_sublayers(
        &self,
        identifier: String,
        resolved: ar::ResolvedPath,
        data: sdf::LayerData,
        stack_vars: &HashMap<String, sdf::Value>,
        reload: bool,
        on_error: &dyn Fn(Error) -> Result<()>,
        already_present: &dyn Fn(&str) -> bool,
        visited: &mut HashSet<String>,
        layers: &mut Vec<sdf::Layer>,
    ) -> Result<()> {
        let sub_paths = Self::sublayer_paths(data.as_ref());

        // Emit this layer ahead of its sublayers so the collected stack is
        // strongest-first: a layer overrides the layers it sublayers, and earlier
        // entries in a `subLayers` list override later ones (spec 10.3.1.1). In a
        // reload pass an already-interned layer is re-walked (to reach a `${VAR}`
        // sublayer the new context now resolves) but not re-emitted.
        if !already_present(&identifier) {
            layers.push(sdf::Layer::new_resolved(identifier.clone(), &resolved, data));
        }

        // Failed sublayer identifiers already reported for *this* layer, so a layer
        // that authors the same missing/unreadable sublayer twice reports it once.
        // Kept per referrer (not shared with the pass-wide `visited`) so a failure
        // suppressed here never hides the same sublayer's diagnostic at another,
        // active referrer.
        let mut failed: HashSet<String> = HashSet::new();

        // Sublayers (and references) reached from inside a `.usdz` resolve
        // in-package: a package root is anchored to its first layer, so this
        // layer's `resolved` is already package-relative and its sublayer paths
        // anchor against it the same way any other layer's do.
        for sub_path in sub_paths {
            // Evaluate the (possibly expression-valued) sublayer path. An
            // unevaluable expression drops only this sublayer — like an unresolved
            // or unreadable one — rather than failing the whole stack open. It has no
            // resolved identifier to key on, so it deduplicates per referrer by its
            // authored path, keeping the three load-failure branches consistent.
            let sub_asset = match expr::evaluate_asset_path(&sub_path, stack_vars) {
                Ok(evaluated) => evaluated,
                Err(reason) => {
                    if failed.insert(sub_path.clone()) {
                        on_error(Error::UnreadableAsset {
                            asset_path: sub_path,
                            referencing_layer: identifier.clone(),
                            reason: format!("{reason:#}"),
                        })?;
                    }
                    continue;
                }
            };

            let sub_id = self.create_identifier(&sub_asset, Some(&resolved));
            // A sublayer already opened this pass is skipped. One already in the
            // graph is skipped too — except in a reload pass, where it is re-walked
            // to reach the `${VAR}` sublayers the new context now resolves below it
            // (it is not re-emitted; see the push above). A failure this layer
            // already reported is skipped too. An empty/degenerate identifier falls
            // through to the resolve below as `UnresolvedAsset`.
            if visited.contains(&sub_id) || failed.contains(&sub_id) || (already_present(&sub_id) && !reload) {
                continue;
            }
            // Resolve the sublayer; a missing one is a raw load failure reported at
            // this referencing site. It is a leaf (no subtree to walk), so it is not
            // added to the pass-wide `visited`: each referencing layer records its own
            // edge, so a shared missing layer reached from several layers is reported
            // once per referrer and the composition layer can suppress by referrer.
            let Some(sub_resolved) = self.resolve_layer(&sub_id) else {
                on_error(Error::UnresolvedAsset {
                    asset_path: sub_asset,
                    referencing_layer: identifier.clone(),
                })?;
                failed.insert(sub_id);
                continue;
            };
            // Read the sublayer; a resolved-but-unreadable one is a raw load failure
            // like a missing one — reported at this referencing site and, being a
            // leaf, left out of `visited` (dropping only this layer; the root's read
            // failure propagated from `open_stack`).
            let sub_data = match self.read(&sub_resolved) {
                Ok(data) => data,
                Err(reason) => {
                    on_error(Error::UnreadableAsset {
                        asset_path: sub_asset,
                        referencing_layer: identifier.clone(),
                        reason: format!("{reason:#}"),
                    })?;
                    failed.insert(sub_id);
                    continue;
                }
            };
            // A readable layer is interned and its subtree walked once; claim it in
            // `visited` before recursing so a diamond or cycle does not re-emit it.
            visited.insert(sub_id.clone());

            self.open_sublayers(
                sub_id,
                sub_resolved,
                sub_data,
                stack_vars,
                reload,
                on_error,
                already_present,
                visited,
                layers,
            )?;
        }

        Ok(())
    }

    /// A layer's `subLayers` asset paths (empty when it declares none).
    pub(crate) fn sublayer_paths(data: &dyn sdf::AbstractData) -> Vec<String> {
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
        let identifier = self.create_identifier(asset_path, anchor);
        if identifier.is_empty() || visited.contains(&identifier) {
            return Ok(());
        }
        let Some(resolved) = self.resolve_layer(&identifier) else {
            return Ok(());
        };
        visited.insert(identifier.clone());
        let data = self.read(&resolved)?;
        // Resolve this layer's arc/sublayer paths against its stack context (root
        // own overlaid by the inherited overrides). This eager test closure loads a
        // superset of what any one stack references; the `LayerGraph` re-derives the
        // actual per-stack membership with the same stack-level context, so a layer
        // reached here that no stack includes is simply an unused node.
        let stack_vars = expr::stack_expression_variables(data.as_ref(), ancestor_expr_vars)?;
        for dep in Self::arc_dependencies(data.as_ref())? {
            let dep_asset = expr::evaluate_asset_path(&dep, &stack_vars)?;
            self.collect_with_arcs_in(&dep_asset, Some(&resolved), &stack_vars, layers, visited)?;
        }
        layers.push(sdf::Layer::new_resolved(identifier, &resolved, data));
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
        registry().open_stack(path, None, &HashMap::new(), false, &|e| Err(e.into()), &|_| false)
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
            false,
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
