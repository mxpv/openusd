//! Value-time `asset` resolution: anchoring an authored path, evaluating a
//! `` `${VAR}` `` expression in it, and filling the derived paths
//! (C++ `UsdStage::_MakeResolvedAssetPaths` and `Usd_AssetPathContext`).
//!
//! The composed value sources resolve through here — a `default` or
//! `timeSamples` opinion from the composition graph, and a sample or manifest
//! default read out of a value clip — so all of them anchor, evaluate, and
//! report alike. What differs between them is only the [`AssetSite`] they
//! supply. (A schema fallback does not: it is read straight off the prim
//! definition and never reaches value resolution — see the `pcp` remaining-work
//! list.)

use crate::ar;
use crate::sdf::{self, Path, Value};

use super::compose_site::{self, EvaluatedExpression};
use super::layer_graph::LayerGraph;
use super::{Error, ExpressionContext, LayerId, LayerStackId};

/// Where an `asset` value was authored: what to anchor a relative path against,
/// whose `expressionVariables` are in scope, and the site to name in a
/// diagnostic (C++ `Usd_AssetPathContext`).
///
/// Holds the source layer's resolved location and identifier rather than a
/// [`LayerId`], because not every source layer is in the composition graph: a
/// value clip's layer is owned by the clip cache and never interned, so it has
/// no id. The stack is carried separately rather than derived from the layer
/// for the same reason — see [`in_clip`](Self::in_clip).
///
/// [`query_path`](Self::query_path) is the path *in the source layer*, which
/// under a reference or variant arc differs from the composed stage path the
/// caller started from.
#[derive(Debug)]
pub(crate) struct AssetSite {
    /// Resolved location of the source layer, the anchor for a relative path.
    /// `None` only for an anonymous layer, which has no location to anchor
    /// against; a named layer that failed to resolve still anchors on its
    /// identifier, since that is what [`sdf::Layer::real_path`] falls back to.
    anchor: Option<ar::ResolvedPath>,
    /// Identifier of the source layer, for [`Error::InvalidExpression`].
    source_layer: String,
    /// The layer stack whose composed variables an expression evaluates against.
    stack: LayerStackId,
    /// The path queried in the source layer.
    query_path: Path,
}

impl AssetSite {
    /// The site of an opinion authored in `layer` at `query_path`, contributed
    /// by a node composing in `stack` — the graph-backed case, which resolves
    /// the anchor and identifier through `graph`.
    ///
    /// Copies the layer's resolved location and identifier, so build it only for
    /// a value that actually holds asset paths.
    pub(super) fn in_graph(graph: &LayerGraph, stack: LayerStackId, layer: LayerId, query_path: &Path) -> Self {
        Self {
            anchor: graph.anchor_location(Some(layer)),
            source_layer: graph.identifier(layer).to_string(),
            stack,
            query_path: query_path.clone(),
        }
    }

    /// The site of a value read out of the clip or manifest `layer`, which the
    /// clip cache owns.
    ///
    /// Such a layer stands outside the composition graph, so it anchors on its
    /// own resolved location and names itself. `stack` is the layer stack of the
    /// node that *introduced the clips*, not anything about the clip itself:
    /// that is where a clip-sourced expression's variables come from (C++
    /// `UsdStage::_GetAssetPathContext` takes the layer from the active clip and
    /// the node from where the clips were introduced). The manifest reads
    /// against the same stack, one set having one introducing node.
    pub(super) fn in_clip(layer: &sdf::Layer, stack: LayerStackId, query_path: &Path) -> Self {
        Self {
            anchor: layer.anchor_location(),
            source_layer: layer.identifier().to_string(),
            stack,
            query_path: query_path.clone(),
        }
    }
}

/// Fills the evaluated and resolved paths on an `asset` / `asset[]` value
/// authored at `site`, recording any expression failure in `errors`. A value
/// holding no asset paths passes through untouched.
///
/// `site` is `None` when the caller found no authoring site, which leaves both
/// derived paths unset and drops an expression without a diagnostic — there is
/// no layer or path to name in one.
///
/// TODO(perf): each asset read re-runs `Resolver::resolve` (a filesystem hit);
/// a per-(layer, path) resolution cache would avoid repeating it.
pub(super) fn resolve_values(
    graph: &LayerGraph,
    value: Value,
    site: Option<&AssetSite>,
    errors: &mut Vec<Error>,
) -> Value {
    match value {
        Value::AssetPath(asset) => Value::AssetPath(resolve_path(graph, asset, site, errors)),
        Value::AssetPathVec(assets) => Value::AssetPathVec(
            assets
                .into_iter()
                .map(|asset| resolve_path(graph, asset, site, errors))
                .collect(),
        ),
        other => other,
    }
}

/// Resolves `asset` against `anchor` (its source layer's resolved location) and
/// returns it with the evaluated and resolved paths recorded.
///
/// A variable expression is evaluated against the composed variables in scope at
/// `site` to the path used as input to resolution (C++
/// `SdfAssetPath::GetAssetPath`). A malformed or non-string expression records
/// [`Error::InvalidExpression`] and leaves both derived paths unset, as a
/// reference or payload arc's asset path does; one evaluating to the
/// expression-language `None` is left unset silently, and so is any expression
/// with no `site` to supply variables. Resolution owns the derived paths: the
/// result is rebuilt from the authored path so any prior evaluated/resolved path
/// is discarded.
fn resolve_path(
    graph: &LayerGraph,
    asset: sdf::AssetPath,
    site: Option<&AssetSite>,
    errors: &mut Vec<Error>,
) -> sdf::AssetPath {
    let mut asset = sdf::AssetPath::new(asset.into_string());
    if asset.is_empty() {
        return asset;
    }
    let anchor = site.and_then(|site| site.anchor.as_ref());
    // The per-element `is_expression` is load-bearing for `asset[]`: a plain
    // element in a mixed array must still skip evaluation.
    let identifier = if sdf::expr::is_expression(asset.as_str()) {
        let Some(site) = site else { return asset };
        // No variable dependency is recorded: nothing caches the result, so
        // there would be nothing to invalidate. `Changes::apply` covers these
        // reads wholesale through its asset-path channel instead.
        let EvaluatedExpression::Value(evaluated) = compose_site::evaluate_expression(
            asset.as_str(),
            graph.stack_expression_variables(site.stack),
            ExpressionContext::AssetValue,
            &site.source_layer,
            &site.query_path,
            Some(errors),
            None,
        ) else {
            return asset;
        };
        let identifier = graph.layer_registry().create_identifier(&evaluated, anchor);
        asset.set_evaluated_path(evaluated);
        identifier
    } else {
        graph.layer_registry().create_identifier(asset.as_str(), anchor)
    };
    if let Some(resolved) = graph.layer_registry().resolve(&identifier) {
        asset.set_resolved_path(resolved.to_string_lossy().into_owned());
    }
    asset
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An expression-valued asset with no site to supply variables (no composed
    /// index or no authoring site for the field) stays unevaluated, and reports
    /// nothing: without a site there is no layer or path to name.
    #[test]
    fn expr_asset_without_site() {
        let graph = LayerGraph::from_layers(Vec::new(), 0, sdf::LayerRegistry::default());
        let mut errors = Vec::new();
        let resolved = resolve_path(&graph, sdf::AssetPath::new("`${A}`"), None, &mut errors);
        assert_eq!(resolved.as_str(), "`${A}`", "the authored expression is kept");
        assert!(resolved.evaluated_path().is_none(), "no evaluated path is derived");
        assert!(errors.is_empty(), "no site means no diagnostic");
    }
}
