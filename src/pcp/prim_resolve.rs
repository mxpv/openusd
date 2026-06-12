//! Value resolution over a composed [`PrimIndex`].
//!
//! These methods walk the prim's composition graph in strength order and apply
//! the per-field resolution rules (spec section 12). See the
//! [module-level docs](super) for the composition overview and
//! [`graph`](super::graph) for the underlying node arena.

use std::borrow::Cow;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::gf;
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, LayerOffset, Path, Specifier, Value};
use crate::tf::Token;

use super::clip;
use super::mapping::MapFunction;
use super::prim_graph::{ArcType, Node};
use super::prim_index::PrimIndex;
use super::{LayerGraph, LayerId};

/// A single authored opinion surfaced by [`PrimIndex::opinions`].
///
/// One opinion is yielded per contributing layer of a node's layer stack, so a
/// per-site node fans out into one opinion per sublayer that authored the
/// field.
struct Opinion<'a> {
    /// The contributing node, strongest-to-weakest in the walk.
    node: &'a Node,
    /// Id of the contributing layer, as yielded by
    /// [`Node::layers`](super::prim_graph::Node::layers) and used with
    /// [`LayerGraph::layer`](super::LayerGraph::layer) — not a position within
    /// the node's layer stack.
    layer: LayerId,
    /// The path queried in the contributing layer (the node path with the
    /// property suffix applied).
    query_path: Cow<'a, Path>,
    /// The authored value at `query_path`.
    value: Cow<'a, Value>,
    /// Effective time offset of the contributing layer to the root namespace
    /// (the node's arc offset with the layer's sublayer offset composed on
    /// top). Used to retime time samples and clip schedules.
    offset: LayerOffset,
}

/// Why a relationship/connection target was dropped during target composition.
pub(crate) enum InvalidTargetKind {
    /// The target does not translate through its arc's domain (C++
    /// `PcpErrorInvalidExternalTargetPath`): a path outside the arc, or a class
    /// node's own instance image.
    External,
    /// The target translates but, authored in a class, names a *different*
    /// instance of that class (C++ `PcpErrorInvalidInstanceTargetPath`).
    Instance,
}

/// A relationship/connection target dropped during target composition (C++
/// `PcpBuildFilteredTargetIndex`'s invalid-target reporting). Carries the
/// node-namespace paths and arc context the diagnostic names. One node's invalid
/// contribution does not affect another's: the path is dropped from the
/// contributing node's list-op only, so a valid stronger opinion for the same
/// path survives.
pub(crate) struct InvalidTarget {
    /// Whether the drop is an out-of-scope or an instance-target error.
    pub kind: InvalidTargetKind,
    /// The dropped target/connection path, in the contributing node's namespace.
    pub target: Path,
    /// The owning property path, in the contributing node's namespace.
    pub property: Path,
    /// Global index of the layer that authored the target.
    pub layer: LayerId,
    /// The arc the target was authored across (selects the "reference" /
    /// "inherit" / … phrasing in the external message).
    pub arc: ArcType,
    /// The prim, in root namespace, where that arc is introduced (external
    /// message's arc root).
    pub arc_root: Path,
    /// The composed (root-namespace) target, for an `Instance` drop. A `delete`
    /// of this composed path retracts the error (C++
    /// `_RemoveTargetPathErrorsForPath`); `None` for an `External` drop, which a
    /// delete never matches.
    pub composed: Option<Path>,
}

impl PrimIndex {
    /// Resolves a field across the composition graph.
    ///
    /// Most fields use strongest-opinion-wins (spec 12.2). Four field classes
    /// have special rules:
    ///
    /// - `specifier`: precedence by `def`/`class`/`over` with direct-inherit handling
    /// - `variability`: weakest authored opinion wins
    /// - `custom`: any-true (logical OR across all authored opinions)
    /// - dictionaries: recursive merge of stronger and weaker dictionary opinions
    ///
    /// When `prop_suffix` is `None`, queries use the node's path directly (zero-copy).
    /// When `Some`, appends the suffix to form a property path for each node.
    /// A [`Value::ValueBlock`] blocks opinions from weaker layers.
    pub(crate) fn resolve_field(
        &self,
        field: &str,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Result<Option<Value>> {
        if field == FieldKey::Specifier.as_str() {
            return self.resolve_specifier(stack, prop_suffix);
        }
        if field == FieldKey::Variability.as_str() {
            return self.resolve_variability(stack, prop_suffix);
        }
        if field == FieldKey::Custom.as_str() {
            return self.resolve_custom(stack, prop_suffix);
        }
        if field == FieldKey::TimeSamples.as_str() {
            return Ok(self.resolve_time_samples(stack, prop_suffix)?.map(Value::TimeSamples));
        }
        self.resolve_strongest(field, stack, prop_suffix)
    }

    /// Resolves a token-list-op field by composing list edits from strongest
    /// to weakest across all contributing nodes.
    ///
    /// This is used for metadata like `apiSchemas`, where the field value is a
    /// list operation rather than a strongest-opinion scalar. A value block
    /// stops weaker opinions while preserving any stronger composed edits.
    pub(crate) fn resolve_token_list_op(
        &self,
        field: FieldKey,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Result<Vec<Token>> {
        let field = field.as_str();
        let mut ops = Vec::new();

        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            // TODO: a non-conformant backend may store `apiSchemas` as a plain
            // `Value::TokenVec` even though the field is declared as a
            // list-op. We currently skip those opinions (falling through to
            // `_ => continue`). Tightening this further requires a
            // schema-aware decode step in the USDC reader (and any other
            // backend) so list-op fields are always produced as
            // `Value::TokenListOp`; until that lands, ill-typed opinions for
            // list-op fields are simply ignored rather than coerced.
            let list_op = match value.into_owned() {
                Value::ValueBlock => break,
                Value::TokenListOp(op) => op,
                _ => continue,
            };
            ops.push(list_op);
        }

        Ok(compose_list_ops(&ops))
    }

    /// Resolves a path-list-op field (relationship targets / attribute
    /// connections), also returning the targets dropped during composition (C++
    /// `PcpBuildFilteredTargetIndex` / `_PathTranslateCallback`).
    ///
    /// Each authored target is translated to the root namespace through its
    /// contributing node's map (C++ `PcpTranslatePathFromNodeToRoot`). A target
    /// that does not translate is dropped as
    /// [`External`](InvalidTargetKind::External); a target whose
    /// `(target, property)` is in `instance_targets` (a class target naming a
    /// different instance of that class, precomputed cross-prim by the cache) is
    /// dropped as [`Instance`](InvalidTargetKind::Instance). Both drops apply to
    /// the contributing node's list-op only, so a valid stronger opinion for the
    /// same path survives the merge. A `delete` of a composed path retracts a
    /// matching `Instance` error (C++ `_RemoveTargetPathErrorsForPath`).
    pub(crate) fn resolve_path_list_op_validated(
        &self,
        field: FieldKey,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        instance_targets: &HashSet<(Path, Path)>,
    ) -> Result<(Vec<Path>, Vec<InvalidTarget>)> {
        let mut ops = Vec::new();
        let mut invalid = Vec::new();
        let mut deleted_composed: HashSet<Path> = HashSet::new();
        // An explicit opinion replaces everything weaker, so weaker opinions never
        // contribute and are not validated — only their stronger survivors are.
        let mut seen_explicit = false;
        for opinion in self.opinions(field.as_str(), stack, prop_suffix) {
            let Opinion {
                node,
                layer,
                query_path,
                value,
                ..
            } = opinion?;
            let list_op = match value.into_owned() {
                Value::ValueBlock => break,
                Value::PathListOp(op) => op,
                Value::PathVec(paths) => sdf::PathListOp::explicit(paths),
                _ => continue,
            };
            let is_explicit = list_op.explicit;
            let map = self.map_to_root_for_targets(node);
            let arc = node.arc;
            let arc_root = node.parent.map_or_else(Path::abs_root, |p| self.node(p).path.clone());
            let report = !seen_explicit;
            // Translate one authored target, dropping (and recording, when not
            // shadowed) an out-of-scope or instance target.
            let mut authored = |path: Path| {
                let absolute = query_path.make_absolute(&path);
                let mapped = map.translate_to_target(&absolute);
                let (kind, composed) = match &mapped {
                    Some(t) if instance_targets.contains(&(absolute.clone(), query_path.as_ref().clone())) => {
                        (InvalidTargetKind::Instance, Some(t.clone()))
                    }
                    Some(_) => return mapped,
                    None => (InvalidTargetKind::External, None),
                };
                if report {
                    invalid.push(InvalidTarget {
                        kind,
                        target: absolute,
                        property: query_path.as_ref().clone(),
                        layer,
                        arc,
                        arc_root: arc_root.clone(),
                        composed,
                    });
                }
                None
            };
            let op = sdf::PathListOp {
                explicit: list_op.explicit,
                explicit_items: list_op.explicit_items.into_iter().filter_map(&mut authored).collect(),
                added_items: list_op.added_items.into_iter().filter_map(&mut authored).collect(),
                prepended_items: list_op.prepended_items.into_iter().filter_map(&mut authored).collect(),
                appended_items: list_op.appended_items.into_iter().filter_map(&mut authored).collect(),
                // Deletes and reorders translate silently; a deleted composed path
                // also retracts a matching instance error below.
                deleted_items: list_op
                    .deleted_items
                    .into_iter()
                    .filter_map(|p| {
                        let mapped = map.translate_to_target(&query_path.make_absolute(&p));
                        if let Some(d) = &mapped {
                            deleted_composed.insert(d.clone());
                        }
                        mapped
                    })
                    .collect(),
                ordered_items: list_op
                    .ordered_items
                    .into_iter()
                    .filter_map(|p| map.translate_to_target(&query_path.make_absolute(&p)))
                    .collect(),
            };
            seen_explicit |= is_explicit;
            ops.push(op);
        }
        // A delete of a composed target retracts the instance error for it (C++
        // `_RemoveTargetPathErrorsForPath`); an external drop has no composed path
        // and is never matched.
        invalid.retain(|inv| inv.composed.as_ref().is_none_or(|c| !deleted_composed.contains(c)));
        Ok((compose_list_ops(&ops), invalid))
    }

    /// Collects the field's path-list-op opinions across the composition graph,
    /// strongest first, each translated into the stage root namespace. A bare
    /// `PathVec` (no list-op envelope) is treated as an explicit replacement of
    /// weaker opinions; a `ValueBlock` stops the walk. Shared by
    /// [`resolve_path_list_op_validated`](Self::resolve_path_list_op_validated) and
    /// [`resolve_path_list_op_deleted`](Self::resolve_path_list_op_deleted).
    fn collect_path_list_ops(
        &self,
        field: FieldKey,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Result<Vec<sdf::PathListOp>> {
        let field = field.as_str();
        let mut ops = Vec::new();
        for opinion in self.opinions(field, stack, prop_suffix) {
            let Opinion {
                node,
                query_path,
                value,
                ..
            } = opinion?;
            let list_op = match value.into_owned() {
                Value::ValueBlock => break,
                Value::PathListOp(op) => op,
                Value::PathVec(paths) => sdf::PathListOp::explicit(paths),
                _ => continue,
            };
            let map = self.map_to_root_for_targets(node);
            ops.push(Self::map_path_list_op_to_root(list_op, &query_path, &map));
        }
        Ok(ops)
    }

    /// A node's map to the root namespace, used when mapping the authored
    /// target/connection paths of a property (C++ `PcpNodeRef::GetMapToRoot`).
    ///
    /// This is the node's stored `map_to_root` — the composition of each arc's
    /// `map_to_parent` from the node up to the tree root. [`compose`](MapFunction::compose)
    /// already carries every relocate the node crosses and enforces invertibility,
    /// so target translation reads it directly.
    pub(crate) fn map_to_root_for_targets(&self, node: &Node) -> MapFunction {
        // Strip variant selections so the map matches C++ (whose maps never carry
        // selections — a variant arc's map is identity). This collapses a variant
        // node's strip pair to the identity, so a sibling connection target
        // authored in a variant is not shadowed by the strip pair in the
        // invertibility check.
        node.map_to_root.without_variant_selections()
    }

    /// Resolves the deleted target/connection paths of a path-list-op field:
    /// every mappable, non-empty path named in a `delete` operation across the
    /// property stack, in weak-to-strong application order (C++
    /// `PcpBuildFilteredTargetIndex`'s `deletedPaths` out-param). An explicit
    /// opinion overwrites the composed result, so it clears the accumulated
    /// deletions, matching the C++ `IsExplicit()` clear.
    pub(crate) fn resolve_path_list_op_deleted(
        &self,
        field: FieldKey,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Result<Vec<Path>> {
        // `collect_path_list_ops` yields strongest first; deletions accumulate as
        // the C++ applies them, weakest to strongest, and an explicit opinion
        // clears the accumulated deletions.
        let ops = self.collect_path_list_ops(field, stack, prop_suffix)?;
        let mut deleted = Vec::new();
        for op in ops.iter().rev() {
            // An explicit opinion fully replaces the composed result and carries
            // no residual deletions (C++ `IsExplicit()`; see `ListOp::combined_with`),
            // so it discards weaker deletions and contributes none of its own.
            if op.explicit {
                deleted.clear();
                continue;
            }
            deleted.extend(op.deleted_items.iter().cloned());
        }
        Ok(deleted)
    }

    /// Translate a path-list-op opinion from one contributing node into the
    /// composed stage namespace before list-op composition.
    ///
    /// Every bucket must be translated, not just contributed values: delete
    /// and reorder opinions only work when they compare against weaker items
    /// in the same namespace. Unmappable paths are dropped, matching a
    /// namespace map whose source domain does not include the authored target.
    fn map_path_list_op_to_root(op: sdf::PathListOp, anchor: &Path, map: &MapFunction) -> sdf::PathListOp {
        fn map_paths(paths: Vec<Path>, anchor: &Path, map: &MapFunction) -> Vec<Path> {
            paths
                .into_iter()
                .filter_map(|path| {
                    // List-op targets are authored in the contributing node's
                    // namespace; compose them only after translating to the
                    // stage root namespace so deletes and reorders compare
                    // like-for-like across layers and arcs.
                    let absolute = anchor.make_absolute(&path);
                    map.map_source_to_target(&absolute)
                })
                .collect()
        }

        sdf::PathListOp {
            explicit: op.explicit,
            explicit_items: map_paths(op.explicit_items, anchor, map),
            added_items: map_paths(op.added_items, anchor, map),
            prepended_items: map_paths(op.prepended_items, anchor, map),
            appended_items: map_paths(op.appended_items, anchor, map),
            deleted_items: map_paths(op.deleted_items, anchor, map),
            ordered_items: map_paths(op.ordered_items, anchor, map),
        }
    }

    /// Builds the query path for a node, applying `prop_suffix` if given.
    /// Borrows the node's path when no suffix is needed (zero-copy).
    fn query_path<'a>(node: &'a Node, prop_suffix: Option<&str>) -> Result<Cow<'a, Path>> {
        match prop_suffix {
            Some(suffix) => Ok(Cow::Owned(Path::new(&format!("{}{suffix}", node.path))?)),
            None => Ok(Cow::Borrowed(&node.path)),
        }
    }

    /// Iterates the authored opinions for `field` across the composition graph,
    /// strongest to weakest, skipping nodes with no opinion. Centralizes the
    /// query-path / layer / `try_field` walk shared by every `resolve_*` field
    /// resolver.
    fn opinions<'a>(
        &'a self,
        field: &'a str,
        stack: &'a LayerGraph,
        prop_suffix: Option<&'a str>,
    ) -> impl Iterator<Item = Result<Opinion<'a>>> + 'a {
        // Each node fans out into one opinion per contributing layer in its
        // layer stack, strongest sublayer first, so a per-site node surfaces
        // every sublayer that authored the field. Two kinds of node stay in
        // `nodes` for structural queries but contribute no opinions here: a
        // permission-denied node (a direct arc to a private site, spec 10.3.3),
        // and a node authoring no spec at its path (`has_specs == false`, a
        // full-stack ancestral site deepened to a child with no local opinion).
        // Skipping the spec-less node avoids a `try_field` per field on a site
        // that cannot author one, and guards against a backend that would return
        // a field where no spec exists.
        //
        // TODO(perf): collecting per node allocates a small Vec; a custom
        // iterator over (node, layer) pairs would avoid it on the hot path.
        self.nodes()
            .filter(|node| node.has_specs() && !node.is_permission_denied())
            .flat_map(move |node| {
                let query_path = match Self::query_path(node, prop_suffix) {
                    Ok(path) => path,
                    Err(err) => return vec![Err(err)],
                };
                let mut out: Vec<Result<Opinion<'a>>> = Vec::new();
                for (layer, offset) in node.layers() {
                    match stack.layer(layer).data().try_field(&query_path, field) {
                        Ok(Some(value)) => out.push(Ok(Opinion {
                            node,
                            layer,
                            query_path: query_path.clone(),
                            value,
                            offset,
                        })),
                        Ok(None) => {}
                        Err(err) => out.push(Err(err)),
                    }
                }
                out
            })
    }

    /// The strongest authored opinion for `field`: the contributing layer (the
    /// anchor for a relative asset path, mirroring C++
    /// `UsdStage::_MakeResolvedAssetPaths`) and the node it came from (the scope
    /// for composing the `expressionVariables` an asset-path expression is
    /// evaluated against). Returns `None` if nothing authors the field.
    pub(crate) fn strongest_opinion(
        &self,
        field: &str,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Option<(LayerId, &Node)> {
        // A direct walk rather than `opinions()` so the returned node borrows
        // from `self` alone, not from the `field` / `stack` parameters. The
        // node/layer filter must match `opinions()`'s first-yield: keep the
        // `has_specs` / permission / `query_path` / `try_field` checks in sync.
        for node in self.nodes() {
            if !node.has_specs() || node.is_permission_denied() {
                continue;
            }
            let Ok(query_path) = Self::query_path(node, prop_suffix) else {
                continue;
            };
            for (layer, _) in node.layers() {
                if matches!(stack.layer(layer).data().try_field(&query_path, field), Ok(Some(_))) {
                    return Some((layer, node));
                }
            }
        }
        None
    }

    /// Composes the `expressionVariables` visible at `node`, a port of
    /// `Indexer::composed_expr_vars` over the finished index. Walking node→root,
    /// each root/reference/payload arc boundary contributes its layer stack's
    /// authored variables, with the closer-to-root stack overriding the farther
    /// one (C++ `PcpExpressionVariables`).
    ///
    /// Keep this walk in sync with `Indexer::composed_expr_vars`: both must
    /// agree on which arcs are boundaries and how stacks compose. The
    /// indexer's `TODO(expr-arcs)` (sub-root frames) applies here too.
    pub(crate) fn composed_expr_vars(&self, node: &Node, stack: &LayerGraph) -> HashMap<String, Value> {
        let mut composed = HashMap::new();
        let mut cur = Some(node);
        while let Some(n) = cur {
            if matches!(n.arc, ArcType::Root | ArcType::Reference | ArcType::Payload) {
                // Members are strongest-first; apply weakest-first so the strongest wins.
                for &(layer, _) in n.layer_stack().iter().rev() {
                    if let Ok(dict) = crate::sdf::expr::read_expression_variables(stack.layer(layer).data()) {
                        composed.extend(dict);
                    }
                }
            }
            cur = n.parent().map(|id| self.node(id));
        }
        composed
    }

    /// Walks nodes from strongest to weakest, returning the first opinion.
    /// A [`Value::ValueBlock`] returns `None`, blocking weaker layers. When
    /// the strongest opinion is a dictionary, weaker dictionary opinions are
    /// recursively merged into it (spec 12.2.5); a `ValueBlock` then blocks
    /// only the remaining weaker opinions, and weaker non-dictionary opinions
    /// are ignored.
    fn resolve_strongest(&self, field: &str, stack: &LayerGraph, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let mut merged: Option<HashMap<String, Value>> = None;
        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            match (merged.as_mut(), value.into_owned()) {
                (None, Value::ValueBlock) => return Ok(None),
                (None, Value::Dictionary(dict)) => merged = Some(dict),
                (None, other) => return Ok(Some(other)),
                (Some(_), Value::ValueBlock) => break,
                (Some(strong), Value::Dictionary(weaker)) => dictionary_over(strong, weaker),
                (Some(_), _) => {}
            }
        }
        Ok(merged.map(Value::Dictionary))
    }

    /// Resolves `timeSamples` across the composition graph, applying each
    /// node's effective layer offset (spec 12.3.2.1) so authored layer time is
    /// mapped to stage time.
    ///
    /// Walks nodes strongest-to-weakest and returns the first node that authors
    /// time samples, retimed by that node's `map_to_root` offset. A
    /// [`Value::ValueBlock`] blocks weaker layers, matching [`Self::resolve_strongest`].
    ///
    /// Unlike generic fields, time samples never merge across nodes: the
    /// strongest authored opinion wins as a whole.
    pub(crate) fn resolve_time_samples(
        &self,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Result<Option<sdf::TimeSampleMap>> {
        self.first_time_samples(stack, prop_suffix, None, |map, offset| {
            retime_samples(map.clone(), offset)
        })
    }

    /// Interpolates the strongest authored `timeSamples` at stage `time`
    /// without cloning the sample map. The matched map is borrowed and
    /// interpolated in its own layer-time frame: `time` is mapped back through
    /// the node's inverse layer offset, which yields the same result as
    /// retiming every sample to stage time (the lerp fraction is invariant
    /// under the affine offset) but clones only the value `interp` returns,
    /// not the whole map.
    ///
    /// When `local_layers` is `Some`, only opinions from those layers
    /// contribute, giving the root-layer-stack precedence that value-clip
    /// resolution relies on (clip data is weaker than the anchoring layer's
    /// local opinions but stronger than data across reference/payload arcs,
    /// spec 12.3.4.5). Membership is by layer index, not arc type: a referenced
    /// layer stack also contributes `Root`-arc nodes, so only the stage's own
    /// root layer stack counts as local.
    ///
    /// The outer `Option` distinguishes a matched `timeSamples` opinion
    /// (`Some`, so value resolution stops here) from no authored or blocked
    /// opinion (`None`, fall through to weaker sources); the inner `Option` is
    /// the interpolated value, `None` for an empty or blocked-bracket result.
    pub(crate) fn resolve_value_at(
        &self,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        local_layers: Option<&HashSet<LayerId>>,
        time: f64,
        interp: &dyn Fn(&sdf::TimeSampleMap, f64) -> Option<Value>,
    ) -> Result<Option<Option<Value>>> {
        self.first_time_samples(stack, prop_suffix, local_layers, |map, offset| {
            interp(map, offset.inverse().apply(time))
        })
    }

    /// Resolves the strongest authored `timeSamples` map together with its
    /// node's layer offset, cloning the map once. A cached value view
    /// ([`Stage::attribute_query`](crate::usd::Stage::attribute_query))
    /// resolves this once and then interpolates the held map per query via
    /// `offset.inverse().apply(time)`, matching [`Self::resolve_value_at`]
    /// without re-walking opinions. `local_layers` filters as in
    /// [`Self::resolve_value_at`].
    pub(crate) fn resolve_time_samples_with_offset(
        &self,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        local_layers: Option<&HashSet<LayerId>>,
    ) -> Result<Option<(sdf::TimeSampleMap, LayerOffset)>> {
        self.first_time_samples(stack, prop_suffix, local_layers, |map, offset| (map.clone(), offset))
    }

    /// Resolves only the retimed sample times of the strongest authored
    /// `timeSamples` opinion, without cloning the sample values. `local_layers`
    /// filters as in [`Self::resolve_value_at`], letting the clip-aware times
    /// path distinguish local from arc opinions.
    pub(crate) fn resolve_time_sample_times(
        &self,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        local_layers: Option<&HashSet<LayerId>>,
    ) -> Result<Option<Vec<f64>>> {
        self.first_time_samples(stack, prop_suffix, local_layers, |map, offset| {
            map.iter().map(|(t, _)| offset.apply(*t)).collect()
        })
    }

    /// Resolves only the count of the strongest authored `timeSamples`
    /// opinion, without cloning the sample values. The layer offset does not
    /// change the count; `local_layers` filters as in
    /// [`Self::resolve_time_sample_times`].
    pub(crate) fn resolve_time_sample_count(
        &self,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        local_layers: Option<&HashSet<LayerId>>,
    ) -> Result<Option<usize>> {
        self.first_time_samples(stack, prop_suffix, local_layers, |map, _| map.len())
    }

    /// Walks `timeSamples` opinions strongest-to-weakest and applies `extract`
    /// to the first authored map, borrowed rather than cloned, paired with its
    /// layer `offset`. A `ValueBlock` blocks weaker layers and yields
    /// `Ok(None)`, as does the absence of any opinion. When `local_layers` is
    /// `Some`, opinions whose contributing layer is outside that set are
    /// skipped so only root-layer-stack opinions contribute.
    fn first_time_samples<R>(
        &self,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        local_layers: Option<&HashSet<LayerId>>,
        extract: impl FnOnce(&sdf::TimeSampleMap, LayerOffset) -> R,
    ) -> Result<Option<R>> {
        let field = FieldKey::TimeSamples.as_str();
        for opinion in self.opinions(field, stack, prop_suffix) {
            let Opinion {
                layer, value, offset, ..
            } = opinion?;
            if local_layers.is_some_and(|local| !local.contains(&layer)) {
                continue;
            }
            match value.as_ref() {
                Value::ValueBlock => return Ok(None),
                Value::TimeSamples(map) => return Ok(Some(extract(map, offset))),
                _ => continue,
            }
        }
        Ok(None)
    }

    /// Resolves the `clipSets` strength order, if authored. Returns the ordered
    /// clip set names (strongest first), folding the list-op edits across every
    /// contributing layer per generic list-op resolution (spec 12.2.6).
    ///
    /// The list op is composed over an empty base, matching C++
    /// `Usd_ClipSetDefinition`: an authored `clipSets` is the authoritative
    /// ordered list, so a set absent from it is excluded. This makes the
    /// return value three-way:
    ///
    /// - `None` — no opinion authored anywhere; clip sets fall back to name
    ///   order (spec 12.3.4.1).
    /// - `Some([])` — authored but composing to empty (explicit `[]` or a
    ///   delete that cancels every name); no clip sets are active.
    /// - `Some(names)` — the composed strength order.
    ///
    /// `clipSets` is a string list op (C++ `SdfStringListOp`). The `String` and
    /// `Token` list-op encodings, and bare vecs (treated as explicit), are all
    /// accepted, since USDC backends may decode the field either way. A
    /// `ValueBlock` with no stronger opinion leaves the field unauthored
    /// (`None`), falling back to name order.
    pub(crate) fn clip_sets_order(&self, stack: &LayerGraph) -> Result<Option<Vec<String>>> {
        // Fold directly into the applied order. This shares the opinion-gather
        // (`clip_sets_ops`) with `clip_sets_list_op` but composes into a `Vec`
        // in one pass, rather than building an intermediate list-op — value
        // resolution reaches this per clipped-attribute read.
        let ops = self.clip_sets_ops(stack)?;
        if ops.is_empty() {
            return Ok(None);
        }
        Ok(Some(compose_list_ops(&ops)))
    }

    /// Resolves the `clipSets` list-op composed across the stack (C++
    /// `SdfStringListOp` folding), preserving the prepend/append/delete
    /// structure rather than flattening to an applied order like
    /// [`clip_sets_order`](Self::clip_sets_order). `None` when unauthored.
    pub(crate) fn clip_sets_list_op(&self, stack: &LayerGraph) -> Result<Option<sdf::StringListOp>> {
        // `clip_sets_ops` yields strongest first; fold each weaker op under the
        // accumulated stronger one.
        Ok(self
            .clip_sets_ops(stack)?
            .into_iter()
            .reduce(|stronger, weaker| stronger.combined_with(&weaker)))
    }

    /// Gathers the contributing `clipSets` list-op opinions, strongest first,
    /// stopping at a `ValueBlock`. The `String`/`Token` list-op encodings and
    /// bare vecs (treated as explicit) are all accepted, since USDC backends may
    /// decode the field either way (spec 12.2.6).
    fn clip_sets_ops(&self, stack: &LayerGraph) -> Result<Vec<sdf::StringListOp>> {
        let mut ops = Vec::new();
        for opinion in self.opinions(FieldKey::ClipSets.as_str(), stack, None) {
            match opinion?.value.into_owned() {
                // Stop weaker opinions while keeping any stronger composed edits.
                Value::ValueBlock => break,
                Value::StringListOp(op) => ops.push(op),
                Value::TokenListOp(op) => ops.push(op.map(String::from)),
                Value::StringVec(names) => ops.push(sdf::StringListOp::explicit(names)),
                Value::TokenVec(names) => ops.push(sdf::StringListOp::explicit(
                    names.into_iter().map(String::from).collect::<Vec<_>>(),
                )),
                _ => continue,
            }
        }
        Ok(ops)
    }

    /// Resolves explicit value clip sets while preserving the layer that
    /// authored path-bearing fields. The top-level `clips` dictionary composes
    /// recursively, but relative clip assets must still be anchored to the
    /// layer that supplied `assetPaths`/`manifestAssetPath`.
    pub(crate) fn resolve_clip_sets(&self, stack: &LayerGraph) -> Result<Vec<clip::ResolvedClipSet>> {
        let mut sets: HashMap<String, HashMap<String, Value>> = HashMap::new();
        let mut blocked_sets: HashSet<String> = HashSet::new();
        let mut asset_layers: HashMap<String, LayerId> = HashMap::new();
        let mut manifest_layers: HashMap<String, LayerId> = HashMap::new();
        // Sets with explicit `assetPaths` (whose `active`/`times` are retimed
        // as they compose) versus the offset of a template set's authoring
        // node (whose schedule is derived later and retimed afterwards).
        let mut explicit_sets: HashSet<String> = HashSet::new();
        let mut template_offsets: HashMap<String, LayerOffset> = HashMap::new();

        // Opinions fan out per contributing sublayer, strongest first; a value
        // block on any layer stops every weaker opinion (spec 12.3.4).
        for opinion in self.opinions(FieldKey::Clips.as_str(), stack, None) {
            let Opinion {
                layer, value, offset, ..
            } = opinion?;
            match value.into_owned() {
                Value::ValueBlock => break,
                Value::Dictionary(dict) => {
                    for (set_name, set_value) in dict {
                        if blocked_sets.contains(&set_name) {
                            continue;
                        }
                        let Value::Dictionary(fields) = set_value else {
                            if !sets.contains_key(&set_name) {
                                blocked_sets.insert(set_name);
                            }
                            continue;
                        };
                        let composed = sets.entry(set_name.clone()).or_default();
                        for (field, value) in fields {
                            if composed.contains_key(&field) {
                                continue;
                            }
                            let value = if field == clip::keys::ACTIVE || field == clip::keys::TIMES {
                                retime_clip_stage_times(value, offset)
                            } else {
                                value
                            };
                            // Relative clip asset paths anchor on the layer that
                            // authored them. Explicit `assetPaths` win over a
                            // template in parse_set, so they always set the
                            // anchor, while `templateAssetPath` only sets it when
                            // no explicit `assetPaths` has been composed — else a
                            // weaker template layer would mis-anchor the explicit
                            // paths the stronger layer authored.
                            if field == clip::keys::ASSET_PATHS {
                                asset_layers.insert(set_name.clone(), layer);
                                explicit_sets.insert(set_name.clone());
                            } else if field == clip::keys::TEMPLATE_ASSET_PATH {
                                if !explicit_sets.contains(&set_name) {
                                    asset_layers.insert(set_name.clone(), layer);
                                }
                                template_offsets.insert(set_name.clone(), offset);
                            } else if field == clip::keys::MANIFEST_ASSET_PATH {
                                manifest_layers.insert(set_name.clone(), layer);
                            }
                            composed.insert(field, value);
                        }
                    }
                }
                _ => continue,
            }
        }

        let clips = Value::Dictionary(
            sets.into_iter()
                .map(|(name, fields)| (name, Value::Dictionary(fields)))
                .collect(),
        );
        let order = self.clip_sets_order(stack)?;

        Ok(clip::ClipSet::parse(&clips, order.as_deref())
            .into_iter()
            .filter_map(|mut set| {
                let asset_layer = asset_layers.get(&set.name).copied()?;
                let manifest_layer = manifest_layers.get(&set.name).copied();
                // Explicit `active`/`times` were retimed as they composed. A
                // template schedule is derived in clip time, so retime its
                // stage times here by the authoring node's offset.
                if !explicit_sets.contains(&set.name) {
                    if let Some(&offset) = template_offsets.get(&set.name) {
                        set.retime_stage_times(offset);
                    }
                }
                Some(clip::ResolvedClipSet {
                    set,
                    asset_layer,
                    manifest_layer,
                })
            })
            .collect())
    }

    /// Variability resolution per spec 12.2.3: weakest authored opinion wins.
    /// Iterates strongest-to-weakest tracking the latest match, so a
    /// [`Value::ValueBlock`] still blocks weaker opinions.
    fn resolve_variability(&self, stack: &LayerGraph, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let field = FieldKey::Variability.as_str();
        let mut weakest = None;
        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            if matches!(value.as_ref(), Value::ValueBlock) {
                break;
            }
            if matches!(value.as_ref(), Value::Variability(_)) {
                weakest = Some(value.into_owned());
            }
        }
        Ok(weakest)
    }

    /// `custom` resolution per spec 12.2.4: any-true across authored opinions.
    /// Returns `Bool(true)` as soon as any opinion is true, `Bool(false)` if
    /// at least one opinion was authored but none were true, and `None`
    /// otherwise.
    fn resolve_custom(&self, stack: &LayerGraph, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let field = FieldKey::Custom.as_str();
        let mut saw_opinion = false;
        for opinion in self.opinions(field, stack, prop_suffix) {
            let value = opinion?.value;
            if matches!(value.as_ref(), Value::ValueBlock) {
                break;
            }
            saw_opinion = true;
            if matches!(value.as_ref(), Value::Bool(true)) {
                return Ok(Some(Value::Bool(true)));
            }
        }
        Ok(saw_opinion.then_some(Value::Bool(false)))
    }

    /// Specifier resolution per spec 12.2.1.
    ///
    /// `over` is undefining; `def` and `class` are defining. The composed
    /// specifier is `def` if the strongest defining opinion is `def`, or if
    /// the strongest defining opinion not from a direct inherit is `def`.
    /// It is `class` if the strongest defining opinion not from a direct
    /// inherit is `class`, or if every defining opinion is `class`. It is
    /// `over` only when every authored opinion is `over`.
    fn resolve_specifier(&self, stack: &LayerGraph, prop_suffix: Option<&str>) -> Result<Option<Value>> {
        let field = FieldKey::Specifier.as_str();
        let mut specs: Vec<(Specifier, ArcType)> = Vec::new();
        for opinion in self.opinions(field, stack, prop_suffix) {
            let Opinion { node, value, .. } = opinion?;
            if matches!(value.as_ref(), Value::ValueBlock) {
                break;
            }
            if let Value::Specifier(s) = value.into_owned() {
                specs.push((s, node.arc));
            }
        }
        if specs.is_empty() {
            return Ok(None);
        }

        let strongest_defining = specs.iter().find(|(s, _)| *s != Specifier::Over).map(|(s, _)| *s);
        let Some(strongest) = strongest_defining else {
            // All authored opinions are `over`.
            return Ok(Some(Value::Specifier(Specifier::Over)));
        };

        let strongest_non_inherit_defining = specs
            .iter()
            .find(|(s, arc)| *s != Specifier::Over && *arc != ArcType::Inherit)
            .map(|(s, _)| *s);

        if strongest == Specifier::Def || strongest_non_inherit_defining == Some(Specifier::Def) {
            return Ok(Some(Value::Specifier(Specifier::Def)));
        }

        let all_defining_class = specs
            .iter()
            .filter(|(s, _)| *s != Specifier::Over)
            .all(|(s, _)| *s == Specifier::Class);
        if strongest_non_inherit_defining == Some(Specifier::Class) || all_defining_class {
            return Ok(Some(Value::Specifier(Specifier::Class)));
        }

        Ok(Some(Value::Specifier(strongest)))
    }
}

/// Folds list-op opinions, collected strongest-to-weakest, into a single
/// resolved list (spec 12.2.6): each weaker op is composed under the stronger
/// ones. `compose_over` short-circuits on an explicit op, so a stronger
/// explicit opinion replaces all weaker contributions.
fn compose_list_ops<T: Default + Clone + PartialEq>(ops: &[sdf::ListOp<T>]) -> Vec<T> {
    let mut result = Vec::new();
    for op in ops.iter().rev() {
        result = op.compose_over(&result);
    }
    result
}

/// Maps time sample keys from layer time to stage time through `offset`
/// (spec 12.3.2.1): `stage_t = offset + scale * layer_t`. Returns the samples
/// untouched when `offset` is the identity.
fn retime_samples(samples: sdf::TimeSampleMap, offset: LayerOffset) -> sdf::TimeSampleMap {
    if offset.is_identity() {
        return samples;
    }
    samples.into_iter().map(|(t, value)| (offset.apply(t), value)).collect()
}

/// Maps the stage-time component of clip `active`/`times` pairs through the
/// layer offset of the node that authored the field.
fn retime_clip_stage_times(value: Value, offset: LayerOffset) -> Value {
    if offset.is_identity() {
        return value;
    }
    match value {
        Value::Vec2dVec(pairs) => {
            Value::Vec2dVec(pairs.into_iter().map(|p| gf::vec2d(offset.apply(p.x), p.y)).collect())
        }
        other => other,
    }
}

/// Applies `strong over weak` dictionary composition in place.
///
/// Keys authored in the stronger dictionary win. If both dictionaries hold a
/// dictionary at the same key, those nested dictionaries are composed
/// recursively; otherwise the stronger value is kept.
fn dictionary_over(stronger: &mut HashMap<String, Value>, weaker: HashMap<String, Value>) {
    for (key, weaker_value) in weaker {
        match stronger.entry(key) {
            Entry::Occupied(mut entry) => {
                if let (Value::Dictionary(strong_dict), Value::Dictionary(weak_dict)) = (entry.get_mut(), weaker_value)
                {
                    dictionary_over(strong_dict, weak_dict);
                }
            }
            Entry::Vacant(entry) => {
                entry.insert(weaker_value);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retime_samples_offset_scale() {
        let samples: sdf::TimeSampleMap = vec![(1.0, Value::Double(0.0)), (5.0, Value::Double(1.0))];
        let retimed = retime_samples(samples, LayerOffset::new(10.0, 2.0));
        let times: Vec<f64> = retimed.iter().map(|(t, _)| *t).collect();
        assert_eq!(times, vec![12.0, 20.0]);
    }

    #[test]
    fn retime_samples_identity_passthrough() {
        let samples: sdf::TimeSampleMap = vec![(1.0, Value::Double(0.0))];
        let retimed = retime_samples(samples.clone(), LayerOffset::IDENTITY);
        assert_eq!(retimed, samples);
    }
}
