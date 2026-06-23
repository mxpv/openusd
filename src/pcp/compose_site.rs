//! Site field composition (C++ `composeSite.cpp`).
//!
//! The list-op composition primitives the indexer drives to read a node's arc
//! fields — `references`, `payload`, `inheritPaths`, `specializes` — across its
//! layer stack and flatten them, together with the asset-path anchoring and
//! time-codes-per-second retiming the reference/payload arcs fold in. Every
//! function is a pure read over a `[Node]` slice and the
//! [`LayerGraph`](super::layer_graph::LayerGraph), so the indexer composes a
//! site without touching composition state.

use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf::expr;
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, LayerOffset, ListOp, Path, Payload, PayloadListOp, Reference, Value};

use super::prim_graph::{ArcType, Node};
use super::{Error, LayerGraph, LayerId};

/// Composes the `references` list-op, folding each authoring sublayer's offset
/// into its references' layer offsets (C++ `PcpComposeSiteReferences`). A
/// reference brought in by a sublayer with a non-identity offset retimes its
/// target by that offset, which the per-site node otherwise carries only per
/// member. Each reference's asset path is anchored to its authoring layer so
/// relative paths in distinct sublayers stay distinct.
pub(super) fn compose_references_in(
    nodes: &[Node],
    graph: &LayerGraph,
    expr_vars: &HashMap<String, Value>,
    site: &Path,
    errors: &mut Vec<Error>,
) -> Result<Vec<Reference>> {
    let mut refs = compose_list_op_in(
        nodes,
        FieldKey::References.as_str(),
        graph,
        |v| v.try_into().ok(),
        |r: &mut Reference, sub, scale| {
            if scale != 1.0 {
                r.layer_offset = r.layer_offset.concatenate(&sdf::LayerOffset::scale_only(scale));
            }
            if !sub.is_identity() {
                r.layer_offset = sub.concatenate(&r.layer_offset);
            }
        },
        |r: &mut Reference, layer| {
            resolve_arc_asset_path(
                &mut r.asset_path,
                layer,
                graph,
                expr_vars,
                ArcType::Reference,
                site,
                errors,
            )
            .unwrap_or(1.0)
        },
    )?;
    // A reference whose expression failed to evaluate keeps its raw backtick
    // path (the failure is already recorded in `errors`); drop it so it is not
    // mistaken for a literal asset path and grafted as a broken arc.
    refs.retain(|r| !expr::is_expression(&r.asset_path));
    Ok(refs)
}

/// Collects payloads from nodes, handling both single `Payload` and
/// `PayloadListOp`. Each authoring sublayer's offset is folded into its
/// payloads' layer offsets, mirroring [`compose_references_in`]; each payload's
/// asset path is anchored to its authoring layer.
pub(super) fn collect_payloads_in(
    nodes: &[Node],
    graph: &LayerGraph,
    expr_vars: &HashMap<String, Value>,
    site: &Path,
    errors: &mut Vec<Error>,
) -> Result<Vec<Payload>> {
    let mut payloads = compose_list_op_in(
        nodes,
        FieldKey::Payload.as_str(),
        graph,
        |v| match v {
            Value::Payload(p) => Some(PayloadListOp {
                explicit: true,
                explicit_items: vec![p],
                ..Default::default()
            }),
            Value::PayloadListOp(op) => Some(op),
            _ => None,
        },
        // Fold the retiming only when it is not identity, so a payload with no
        // authored offset and no rate change keeps its `layer_offset` as `None`
        // (identity `Some` would change the serialized form without affecting
        // composition). Applied after the list-op composes so payloads are deduped
        // by authored value (see [`compose_list_op_in`]).
        |p: &mut Payload, sub, scale| {
            if scale != 1.0 {
                let offset = p.layer_offset.unwrap_or_default();
                p.layer_offset = Some(offset.concatenate(&sdf::LayerOffset::scale_only(scale)));
            }
            if !sub.is_identity() {
                p.layer_offset = Some(sub.concatenate(&p.layer_offset.unwrap_or_default()));
            }
        },
        |p: &mut Payload, layer| {
            resolve_arc_asset_path(
                &mut p.asset_path,
                layer,
                graph,
                expr_vars,
                ArcType::Payload,
                site,
                errors,
            )
            .unwrap_or(1.0)
        },
    )?;
    // A payload whose expression failed to evaluate keeps its raw backtick path
    // (the failure is already recorded in `errors`); drop it, as in
    // [`compose_references_in`].
    payloads.retain(|p| !expr::is_expression(&p.asset_path));
    Ok(payloads)
}

/// Composes an offset-free list-op field (inherits, specializes) by decoding
/// each opinion through `TryInto` and combining across the layer stack.
pub(super) fn compose_arc_list_in<T: Default + Clone + PartialEq>(
    nodes: &[Node],
    field: FieldKey,
    graph: &LayerGraph,
) -> Result<Vec<T>>
where
    Value: TryInto<ListOp<T>>,
{
    compose_list_op_in(
        nodes,
        field.as_str(),
        graph,
        |v| v.try_into().ok(),
        |_, _, _| {},
        |_, _| 1.0,
    )
}

/// Composes a list-op field across nodes' layer stacks, returning the
/// flattened list.
///
/// Each node fans out into its contributing sublayers, strongest first.
/// `decode` turns a raw field value into a `ListOp<T>` (returning `None` for a
/// wrong-typed value, treated as no opinion); `retime` rewrites each item by
/// the contributing sublayer's offset (a no-op for offset-free arcs). Backend
/// decode errors surface to the caller.
fn compose_list_op_in<T, D, R, A>(
    nodes: &[Node],
    field: &str,
    graph: &LayerGraph,
    decode: D,
    mut retime: R,
    mut anchor: A,
) -> Result<Vec<T>>
where
    T: Default + Clone + PartialEq,
    D: Fn(Value) -> Option<ListOp<T>>,
    R: FnMut(&mut T, LayerOffset, f64),
    A: FnMut(&mut T, LayerId) -> f64,
{
    let mut combined: Option<ListOp<T>> = None;
    // The sublayer offset and time-codes scale to fold into each item, keyed by
    // the item as authored (after anchoring). Recorded strongest-first and applied
    // only after the list-op is composed: an offset-bearing item (reference/
    // payload) is deduped by its AUTHORED value, so two items that resolve to the
    // same composed offset but are authored differently — e.g. `(offset=45,
    // scale=0.5)` under a layer offset `(10, 2)` versus a literal `(offset=100)` —
    // stay distinct (C++ composes `SdfReference`s by authored value, then applies
    // the layer offset and time-codes retiming).
    // TODO(perf): linear scans of `folds`; fine for the short per-prim arc lists.
    let mut folds: Vec<(T, LayerOffset, f64)> = Vec::new();

    for node in nodes {
        // A layer that is sublayered from more than one place (a sublayer
        // diamond) appears multiple times in the node's layer stack, strongest
        // occurrence first. Its authored opinion at this path is identical at
        // every occurrence — only the composed offset differs — so it is read
        // once, at its strongest occurrence (C++ `GetLayerOffsetForLayer` is
        // single-valued per layer).
        let mut seen_layers: HashSet<LayerId> = HashSet::new();
        for &(layer, sub) in graph.layer_stack(node.layer_stack_id()) {
            if !seen_layers.insert(layer) {
                continue;
            }
            let Some(value) = graph.layer(layer).data().try_field(&node.path, field)? else {
                continue;
            };
            let Some(mut list_op) = decode(value.into_owned()) else {
                continue;
            };
            // Anchor each item to the layer that authored it before composing, so
            // a relative asset path in different sublayers resolves to distinct
            // targets and is not wrongly deduped (e.g. `@./ref.usd@` authored in
            // `sub1/` and `sub2/` are two references, not one). The anchor resolves
            // the path and returns the time-codes scale to fold later — it does not
            // change the offset, so dedup still compares authored values.
            for item in list_op.iter_mut() {
                let scale = anchor(item, layer);
                if (!sub.is_identity() || scale != 1.0) && !folds.iter().any(|(i, _, _)| i == item) {
                    folds.push((item.clone(), sub, scale));
                }
            }
            combined = Some(match combined {
                Some(stronger) => stronger.combined_with(&list_op),
                None => list_op,
            });
        }
    }

    let mut result = combined.map(|op| op.reduced().flatten()).unwrap_or_default();
    for item in &mut result {
        if let Some((_, sub, scale)) = folds.iter().find(|(i, _, _)| i == item) {
            retime(item, *sub, *scale);
        }
    }
    Ok(result)
}

/// Resolves a reference/payload arc's asset path in place: evaluates a backtick
/// variable expression against `expr_vars`, anchors the result to its authoring
/// layer, and returns the time-codes-per-second retiming scale to fold into the
/// arc offset (spec 12.3.2). Shared by [`compose_references_in`] and
/// [`collect_payloads_in`], which differ only in their offset field's shape.
///
/// A malformed or non-string expression is recoverable (C++
/// `PcpErrorVariableExpression`): the failure is recorded in `errors`, the path
/// is left as the raw unevaluated expression for the caller to drop, and `None`
/// is returned so no scale is folded.
#[allow(clippy::too_many_arguments)]
fn resolve_arc_asset_path(
    asset_path: &mut String,
    authoring_layer: LayerId,
    graph: &LayerGraph,
    expr_vars: &HashMap<String, Value>,
    arc: ArcType,
    site: &Path,
    errors: &mut Vec<Error>,
) -> Option<f64> {
    match expr::evaluate_asset_path(asset_path, expr_vars) {
        Ok(resolved) => *asset_path = resolved,
        Err(source) => {
            errors.push(Error::InvalidExpression {
                expression: asset_path.clone(),
                arc,
                site_path: site.clone(),
                message: source.to_string(),
            });
            return None;
        }
    }
    anchor_asset_path(asset_path, graph.layer(authoring_layer), graph.layer_registry());
    Some(arc_tcps_scale(graph.layer(authoring_layer), asset_path, graph))
}

/// Anchors a non-empty, non-absolute asset path to the layer that authored it,
/// so the same relative path in different layers resolves to distinct targets
/// (C++ resolves a reference's asset path against its authoring layer when the
/// layer stack is composed). An empty path (internal reference) is left as-is.
fn anchor_asset_path(asset_path: &mut String, authoring_layer: &sdf::Layer, registry: &sdf::LayerRegistry) {
    if asset_path.is_empty() {
        return;
    }
    *asset_path = registry.create_identifier_anchored(asset_path, &authoring_layer.identifier);
}

/// The retiming scale a reference or payload arc folds into its layer offset
/// when the introducing (authoring) layer and the referenced layer have
/// different time-codes-per-second rates (spec 12.3.2): `introducing / target`.
/// An internal arc (empty asset path) or an unresolved target retimes by 1.0.
/// `asset_path` must already be anchored to its authoring layer.
//
// TODO(perf): this `graph.find` re-resolves the target that
// `indexer::add_ref_or_payload_arc` resolves again moments later for the same
// anchored path. The duplicate can't be hoisted trivially — the ratio's
// numerator is the per-member authoring rate, knowable only here inside the
// in-place list-op fold, while the target stack is needed there — so it waits on
// an asset-path resolution cache at the resolver level.
fn arc_tcps_scale(introducing: &sdf::Layer, asset_path: &str, graph: &LayerGraph) -> f64 {
    if asset_path.is_empty() {
        return 1.0;
    }
    graph.find(asset_path).map_or(1.0, |target| {
        super::effective_time_codes_per_second(introducing)
            / super::effective_time_codes_per_second(graph.layer(target))
    })
}
