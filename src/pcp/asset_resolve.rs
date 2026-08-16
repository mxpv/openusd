//! Where an `asset` value was authored, and the diagnostics that naming the
//! site makes possible (C++ `Usd_AssetPathContext`).
//!
//! The composed value sources resolve through here — a `default` or
//! `timeSamples` opinion from the composition graph, and a sample or manifest
//! default read out of a value clip — so all of them anchor, evaluate, and
//! report alike. What differs between them is only the [`AssetSite`] they
//! supply. The anchoring and evaluation themselves are
//! [`sdf::resolve_asset_paths`], which knows nothing of composition; a site is
//! how this tier expresses the anchor and variable scope that function takes.
//! The schema tier resolves through the same `sdf` seam from its own side
//! (`Stage::resolve_schema_asset`), supplying the schematics that authored a
//! fallback in place of a site.

use std::collections::HashMap;

use crate::ar;
use crate::sdf::{self, Path, Value};

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

    /// What a relative path authored here anchors against.
    fn anchor(&self) -> Option<&ar::ResolvedPath> {
        self.anchor.as_ref()
    }

    /// The composed variables an expression authored here evaluates against.
    fn variables<'graph>(&self, graph: &'graph LayerGraph) -> &'graph HashMap<String, Value> {
        graph.stack_expression_variables(self.stack)
    }
}

/// Fills the evaluated and resolved paths on an `asset` / `asset[]` value
/// authored at `site`, recording any expression failure in `errors`. A value
/// holding no asset paths passes through untouched.
///
/// `site` is `None` when the caller found no authoring site, which leaves both
/// derived paths unset and drops an expression without a diagnostic — there is
/// no layer or path to name in one.
pub(super) fn resolve_values(
    graph: &LayerGraph,
    value: Value,
    site: Option<&AssetSite>,
    errors: &mut Vec<Error>,
) -> Value {
    let mut failures = Vec::new();
    let anchor = site.and_then(AssetSite::anchor);
    let value = sdf::resolve_asset_paths(
        graph.layer_registry(),
        anchor,
        site.map(|site| site.variables(graph)),
        value,
        &mut failures,
    );
    record_failures(site, failures, errors);
    value
}

/// Fills the evaluated path on an `asset` / `asset[]` value authored at `site`,
/// recording any expression failure in `errors`, without resolving it — and
/// says how it came out.
///
/// For a caller that anchors the result itself, or one whose value is not a
/// file name at all: a `templateAssetPath` is a `#`-pattern expanded into a
/// sequence of clip paths, so resolving the pattern would name nothing.
pub(super) fn evaluate_values(
    graph: &LayerGraph,
    value: Value,
    site: Option<&AssetSite>,
    errors: &mut Vec<Error>,
) -> (Value, sdf::AssetOutcome) {
    let mut failures = Vec::new();
    let variables = site.map(|site| site.variables(graph));
    let (value, outcome) = sdf::evaluate_asset_paths(variables, value, &mut failures);
    record_failures(site, failures, errors);
    (value, outcome)
}

/// Names the site every expression failure was authored at and records it as
/// [`Error::InvalidExpression`], as a reference or payload arc's asset path
/// does.
///
/// No variable dependency is recorded: the read carries no prim index to
/// register one against, so no per-variable invalidation could name it.
/// `Changes::apply` covers these reads wholesale through its asset-path channel
/// instead.
fn record_failures(site: Option<&AssetSite>, failures: Vec<sdf::AssetExpressionFailure>, errors: &mut Vec<Error>) {
    // Only a site supplies variables, and only an evaluation against variables
    // can fail, so a caller with no site has nothing to report.
    let Some(site) = site else {
        return;
    };
    for failure in failures {
        Error::InvalidExpression {
            expression: failure.expression,
            context: ExpressionContext::AssetValue,
            source_layer: site.source_layer.clone(),
            site_path: site.query_path.clone(),
            message: failure.message,
        }
        .record(errors);
    }
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
        let value = Value::AssetPath(sdf::AssetPath::new("`${A}`"));
        let resolved = resolve_values(&graph, value, None, &mut errors)
            .try_as_asset_path()
            .expect("an asset value stays one");
        assert_eq!(resolved.as_str(), "`${A}`", "the authored expression is kept");
        assert!(resolved.evaluated_path().is_none(), "no evaluated path is derived");
        assert!(errors.is_empty(), "no site means no diagnostic");
    }
}
