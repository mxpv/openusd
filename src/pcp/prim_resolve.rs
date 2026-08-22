//! Value resolution over a composed [`PrimIndex`].
//!
//! These methods walk the prim's composition graph in strength order and apply
//! the per-field resolution rules (spec section 12). See the
//! [module-level docs](super) for the composition overview and
//! [`graph`](super::graph) for the underlying node arena.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use crate::gf;
use crate::sdf::schema::FieldKey;
use crate::sdf::{self, LayerOffset, Path, Specifier, Value};

use super::asset_resolve::{self, AssetSite};
use super::clip;
use super::mapping::MapFunction;
use super::prim_graph::{ArcType, Node};
use super::prim_index::PrimIndex;
use super::value_resolve::SelectedSite;
use super::{CompositionError, LayerGraph, LayerId, QueryError};

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

impl Opinion<'_> {
    /// Maps this opinion's value into the stage's time frame through the
    /// contributing layer's offset
    /// ([`LayerOffset::apply_to_value`](sdf::LayerOffset::apply_to_value)). The
    /// value stays borrowed unless the offset actually retimes something in it.
    fn retimed(mut self) -> Self {
        if !self.offset.is_identity() && self.value.holds_time_codes() {
            self.offset.apply_to_value(self.value.to_mut());
        }
        self
    }
}

/// A live contributing spec site: a [`SpecSite`](super::prim_graph::SpecSite)
/// whose node still contributes opinions (inert and culled nodes filtered
/// out), paired with the path to query in the contributing layer. The shared
/// output of [`PrimIndex::contributing_sites`], so
/// [`opinions`](PrimIndex::opinions) and
/// [`strongest_opinion`](PrimIndex::strongest_opinion) apply the same node
/// filter and query-path resolution and cannot drift.
struct ContributingSite<'a> {
    /// The contributing node, strongest-to-weakest in the walk.
    node: &'a Node,
    /// Id of the contributing layer (see [`Opinion::layer`]).
    layer: LayerId,
    /// Effective time offset of the contributing layer to the root namespace,
    /// taken precomputed from the spec stack (see [`Opinion::offset`]).
    offset: LayerOffset,
    /// The path queried in the contributing layer (the node path with the
    /// property suffix applied).
    query_path: Cow<'a, Path>,
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
    /// Most fields use strongest-opinion-wins (spec 12.2). Five field classes
    /// have special rules:
    ///
    /// - `specifier`: precedence by `def`/`class`/`over` with direct-inherit handling
    /// - `variability`: weakest authored opinion wins
    /// - `custom`: any-true (logical OR across all authored opinions)
    /// - dictionaries: recursive merge of stronger and weaker dictionary opinions
    /// - list ops: list edits folded across all contributing opinions (12.2.6),
    ///   for the fields [`sdf::folds_list_ops`] accepts — a field composed by
    ///   dedicated machinery (arcs, targets, clips, values) keeps its raw
    ///   strongest opinion here
    /// - path expressions: `%_` weaker references composed across opinions,
    ///   each mapped into the root namespace through its node
    ///
    /// When `prop_suffix` is `None`, queries use the node's path directly (zero-copy).
    /// When `Some`, appends the suffix to form a property path for each node.
    /// A [`Value::ValueBlock`] blocks opinions from weaker layers.
    pub(crate) fn resolve_field(
        &self,
        field: &str,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Result<Option<Value>, QueryError> {
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
        match self.resolve_strongest(field, stack, prop_suffix, None)? {
            Some(strongest) if sdf::folds_list_ops(field) => {
                self.resolve_list_op(field, stack, prop_suffix, strongest).map(Some)
            }
            other => Ok(other),
        }
    }

    /// Folds a list-op-valued field across every contributing opinion into a
    /// baked explicit list op, so any field authored as a list op composes by
    /// list-edit folding (spec 12.2.6) — the dispatch C++
    /// `UsdStage::_GetGeneralMetadataImpl` performs through `_IsListOpValue`
    /// before `_GetListOpMetadataImpl` bakes the result.
    ///
    /// `strongest` is the field's already-resolved strongest opinion: its
    /// variant decides the element type, and a non-list-op value passes
    /// through unchanged. A value block stops weaker opinions while preserving
    /// the stronger composed edits.
    // TODO: a non-conformant backend may store a list-op field as a plain vec
    // (`apiSchemas` as `Value::TokenVec`). Opinions whose variant differs from
    // the strongest opinion's are skipped here; coercing them instead needs a
    // schema-aware decode step in the USDC reader (and any other backend) so a
    // list-op field is always produced as a list-op value.
    //
    // TODO(perf): the strongest opinion is materialized only for its variant
    // here, and the fold walk re-reads the sites the strongest pass already
    // visited. Peeking the borrowed discriminant before owning would resolve
    // a list-op field in one walk.
    fn resolve_list_op(
        &self,
        field: &str,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        strongest: Value,
    ) -> Result<Value, QueryError> {
        macro_rules! fold {
            ($variant:ident) => {{
                let mut ops = Vec::new();
                for opinion in self.opinions(field, stack, prop_suffix) {
                    match opinion?.value.into_owned() {
                        Value::ValueBlock => break,
                        Value::$variant(op) => {
                            // An explicit opinion replaces everything weaker,
                            // so the walk stops with it.
                            let explicit = op.explicit;
                            ops.push(op);
                            if explicit {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                Value::$variant(sdf::ListOp::explicit(compose_list_ops(&ops)))
            }};
        }

        Ok(match strongest {
            Value::TokenListOp(_) => fold!(TokenListOp),
            Value::StringListOp(_) => fold!(StringListOp),
            Value::PathListOp(_) => fold!(PathListOp),
            Value::ReferenceListOp(_) => fold!(ReferenceListOp),
            Value::PayloadListOp(_) => fold!(PayloadListOp),
            Value::IntListOp(_) => fold!(IntListOp),
            Value::Int64ListOp(_) => fold!(Int64ListOp),
            Value::UIntListOp(_) => fold!(UIntListOp),
            Value::UInt64ListOp(_) => fold!(UInt64ListOp),
            Value::UnregisteredValueListOp(_) => fold!(UnregisteredValueListOp),
            // `apiSchemas` is declared token-list-op by the core schema, so it
            // folds even when a non-conformant backend stored the strongest
            // opinion as a plain vec: the ill-typed opinion is skipped and the
            // conformant edits still compose (see the TODO above).
            _ if field == FieldKey::ApiSchemas.as_str() => fold!(TokenListOp),
            other => other,
        })
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
    ) -> Result<(Vec<Path>, Vec<InvalidTarget>), QueryError> {
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
            // The node's map to the root namespace (C++ `PcpNodeRef::GetMapToRoot`).
            let map = &node.map_to_root;
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
    ) -> Result<Vec<sdf::PathListOp>, QueryError> {
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
            ops.push(Self::map_path_list_op_to_root(list_op, &query_path, &node.map_to_root));
        }
        Ok(ops)
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
    ) -> Result<Vec<Path>, QueryError> {
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
                    // like-for-like across layers and arcs. A variant-qualified
                    // anchor makes the absolute form carry a selection, which
                    // map functions never do, so it is stripped before mapping
                    // (as `translate_to_target` does internally).
                    let mut absolute = anchor.make_absolute(&path);
                    if absolute.contains_prim_variant_selection() {
                        absolute = absolute.strip_all_variant_selections();
                    }
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

    /// Maps a path expression authored at a node into the stage's root
    /// namespace (C++ `_PathExprToStage`): relative patterns and reference
    /// paths anchor to the authoring prim first, then every path maps through
    /// the node's map function. An atom whose path does not translate has no
    /// meaning at the root and becomes the empty expression.
    fn map_expression_to_root(expr: sdf::PathExpression, anchor: &Path, map: &MapFunction) -> sdf::PathExpression {
        expr.make_absolute(anchor).map_paths(|path| {
            // A variant-qualified anchor makes the absolute form carry a
            // selection, which map functions never do.
            let mut absolute = path.clone();
            if absolute.contains_prim_variant_selection() {
                absolute = absolute.strip_all_variant_selections();
            }
            map.map_source_to_target(&absolute)
        })
    }

    /// Builds the query path for a node, applying `prop_suffix` if given.
    /// Borrows the node's path when no suffix is needed (zero-copy).
    ///
    /// The suffix comes from an already-validated property path and the node
    /// path from the composed graph, so appending one to the other needs no
    /// re-validation.
    pub(super) fn query_path<'a>(node: &'a Node, prop_suffix: Option<&str>) -> Cow<'a, Path> {
        match prop_suffix {
            Some(suffix) => Cow::Owned(Path::from_str_unchecked(&format!("{}{suffix}", node.path))),
            None => Cow::Borrowed(&node.path),
        }
    }

    /// Iterates the live contributing spec sites in strength order, strongest
    /// first — each [`live_spec_sites`](Self::live_spec_sites) entry paired with
    /// its query path. The shared query-path resolution behind both
    /// [`opinions`](Self::opinions) and [`strongest_opinion`](Self::strongest_opinion),
    /// so the two cannot drift.
    fn contributing_sites<'a>(
        &'a self,
        prop_suffix: Option<&'a str>,
    ) -> impl Iterator<Item = Result<ContributingSite<'a>, QueryError>> + 'a {
        self.live_spec_sites().map(move |(site, node)| {
            Ok(ContributingSite {
                node,
                layer: site.layer,
                offset: site.offset,
                query_path: Self::query_path(node, prop_suffix),
            })
        })
    }

    /// Iterates the opinions for `field` across the composition graph, strongest
    /// to weakest, each value mapped into the stage's time frame by the
    /// contributing layer's offset — C++ transforms a field value the moment it
    /// is read from its layer, before composing it (`_FieldValueToStageXf` in
    /// `ConsumeAuthored`), so a `timecode` merges and compares against weaker
    /// opinions in the one frame every consumer resolves in.
    ///
    /// A consumer that does its own retiming from
    /// [`Opinion::offset`](Opinion::offset) reads
    /// [`opinions_in_layer_time`](Self::opinions_in_layer_time) instead.
    fn opinions<'a>(
        &'a self,
        field: &'a str,
        stack: &'a LayerGraph,
        prop_suffix: Option<&'a str>,
    ) -> impl Iterator<Item = Result<Opinion<'a>, QueryError>> + 'a {
        self.opinions_in_layer_time(field, stack, prop_suffix)
            .map(|opinion| opinion.map(Opinion::retimed))
    }

    /// Iterates the authored opinions for `field` across the composition graph,
    /// strongest to weakest, each value exactly as its layer holds it — in that
    /// layer's own time frame — and skipping sites with no opinion for `field`. Reads the
    /// memoized spec stack through [`contributing_sites`](Self::contributing_sites),
    /// so each site's contributing layer and root-namespace offset are already
    /// resolved; only the `try_field` for this `field` happens per query.
    fn opinions_in_layer_time<'a>(
        &'a self,
        field: &'a str,
        stack: &'a LayerGraph,
        prop_suffix: Option<&'a str>,
    ) -> impl Iterator<Item = Result<Opinion<'a>, QueryError>> + 'a {
        self.contributing_sites(prop_suffix).filter_map(move |site| {
            let site = match site {
                Ok(site) => site,
                Err(err) => return Some(Err(err)),
            };
            match stack.layer(site.layer).data().try_field(&site.query_path, field) {
                Ok(Some(value)) => Some(Ok(Opinion {
                    node: site.node,
                    layer: site.layer,
                    query_path: site.query_path,
                    value,
                    offset: site.offset,
                })),
                Ok(None) => None,
                Err(err) => Some(Err(err.into())),
            }
        })
    }

    /// The site of the strongest authored opinion for `field` — what an
    /// `asset`-valued opinion needs to anchor, evaluate, and be diagnosed
    /// (mirroring C++ `UsdStage::_GetAssetPathContext` for a default-sourced
    /// value). `None` if nothing authors the field.
    ///
    /// The provenance is owned, so the caller is free to take `&mut self` on the
    /// cache while it resolves.
    pub(crate) fn strongest_opinion(
        &self,
        field: &str,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
    ) -> Option<AssetSite> {
        // Shares `contributing_sites` with `opinions`, so the node filter never
        // drifts.
        for site in self.contributing_sites(prop_suffix) {
            let Ok(site) = site else { continue };
            if matches!(
                stack.layer(site.layer).data().try_field(&site.query_path, field),
                Ok(Some(_))
            ) {
                return Some(AssetSite::in_graph(
                    stack,
                    site.node.layer_stack_id(),
                    site.layer,
                    &site.query_path,
                ));
            }
        }
        None
    }

    /// Walks nodes from strongest to weakest, returning the first opinion.
    /// A [`Value::ValueBlock`] returns `None`, blocking weaker layers. Two
    /// value kinds keep composing past the strongest opinion:
    ///
    /// - a dictionary recursively merges weaker dictionary opinions into
    ///   itself (spec 12.2.5); a `ValueBlock` then blocks only the remaining
    ///   weaker opinions, and weaker non-dictionary opinions are ignored
    /// - a path expression substitutes each `%_` with the next-weaker
    ///   opinion's expression (C++ registers `SdfPathExpression`'s
    ///   compose-over with generic value resolution); a surviving `%_`
    ///   resolves to the empty expression, and every opinion is mapped into
    ///   the root namespace through its node first
    pub(crate) fn resolve_strongest(
        &self,
        field: &str,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        start: Option<&SelectedSite>,
    ) -> Result<Option<Value>, QueryError> {
        let mut opinions = self.opinions(field, stack, prop_suffix);
        // With a `start`, composition begins at the site the shared
        // value-resolution walk selected instead of searching for the strongest
        // opinion again — which is what keeps the composed value and the source
        // that walk reports naming one site. A site that fails to read on the
        // way there is still the walk's to report rather than to skip.
        let first = match start {
            Some(start) => {
                let mut found = None;
                for opinion in opinions.by_ref() {
                    let opinion = opinion?;
                    if start.is(opinion.layer, opinion.node, &opinion.query_path) {
                        found = Some(opinion);
                        break;
                    }
                }
                found
            }
            None => opinions.next().transpose()?,
        };
        let Some(first) = first else {
            return Ok(None);
        };
        match first.value.into_owned() {
            Value::ValueBlock => Ok(None),
            Value::Dictionary(mut merged) => {
                for opinion in opinions {
                    match opinion?.value.into_owned() {
                        Value::ValueBlock => break,
                        Value::Dictionary(weaker) => sdf::dictionary_over(&mut merged, weaker),
                        _ => {}
                    }
                }
                Ok(Some(Value::Dictionary(merged)))
            }
            Value::PathExpression(expr) => {
                let mut composed =
                    Self::map_expression_to_root(expr, &first.query_path.prim_path(), &first.node.map_to_root);
                for opinion in opinions {
                    if !composed.contains_weaker_reference() {
                        break;
                    }
                    let opinion = opinion?;
                    // String and token opinions parse leniently, matching the
                    // schema-less reads collection queries accept.
                    let weaker = match opinion.value.into_owned() {
                        Value::ValueBlock => break,
                        Value::PathExpression(weaker) => weaker,
                        Value::String(text) => sdf::PathExpression::parse(&text),
                        Value::Token(text) => sdf::PathExpression::parse(text.as_str()),
                        _ => continue,
                    };
                    let weaker = Self::map_expression_to_root(
                        weaker,
                        &opinion.query_path.prim_path(),
                        &opinion.node.map_to_root,
                    );
                    composed = composed.compose_over(&weaker);
                }
                // A weaker reference that outlived the stack has no opinion
                // left to name: it resolves to the empty expression.
                composed = composed.compose_over(&sdf::PathExpression::nothing());
                Ok(Some(Value::PathExpression(composed)))
            }
            Value::PathExpressionVec(exprs) => {
                // Array elements translate across arcs like the scalar form;
                // with no per-element weaker stack to draw on, a surviving
                // weaker reference resolves to the empty expression.
                let anchor = first.query_path.prim_path();
                let composed = exprs
                    .into_iter()
                    .map(|expr| {
                        Self::map_expression_to_root(expr, &anchor, &first.node.map_to_root)
                            .compose_over(&sdf::PathExpression::nothing())
                    })
                    .collect();
                Ok(Some(Value::PathExpressionVec(composed)))
            }
            other => Ok(Some(other)),
        }
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
    ) -> Result<Option<sdf::TimeSampleMap>, QueryError> {
        self.first_time_samples(stack, prop_suffix, |map, opinion| {
            let mut samples = map.clone();
            opinion.offset.apply_to_samples(&mut samples);
            samples
        })
    }

    /// Walks `timeSamples` opinions strongest-to-weakest and applies `extract`
    /// to the first authored map, borrowed rather than cloned, paired with its
    /// layer `offset` and the [`AssetSite`] it came from. A `ValueBlock` blocks
    /// weaker layers and yields `Ok(None)`, as does the absence of any opinion.
    /// The winning opinion is handed to `extract` whole so it can describe its
    /// own [`AssetSite`] — which is what lets a sampled `asset` value be
    /// anchored and evaluated like a default-sourced one. Building that site
    /// copies two strings, so an extract that resolves no asset simply never
    /// asks for it.
    ///
    /// The map reaches `extract` in the contributing layer's own time frame, so
    /// an extract that reads a time — the map's keys or a `timecode` sample —
    /// retimes it by `Opinion::offset` itself. A per-time extract does that
    /// through [`sdf::LayerOffset::sample_in_stage_time`], which reads the
    /// borrowed map directly.
    fn first_time_samples<R>(
        &self,
        stack: &LayerGraph,
        prop_suffix: Option<&str>,
        extract: impl FnOnce(&sdf::TimeSampleMap, &Opinion<'_>) -> R,
    ) -> Result<Option<R>, QueryError> {
        let field = FieldKey::TimeSamples.as_str();
        for opinion in self.opinions_in_layer_time(field, stack, prop_suffix) {
            let opinion = opinion?;
            match &*opinion.value {
                Value::ValueBlock => return Ok(None),
                Value::TimeSamples(map) => return Ok(Some(extract(map, &opinion))),
                _ => {}
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
    pub(crate) fn clip_sets_order(&self, stack: &LayerGraph) -> Result<Option<Vec<String>>, QueryError> {
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
    pub(crate) fn clip_sets_list_op(&self, stack: &LayerGraph) -> Result<Option<sdf::StringListOp>, QueryError> {
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
    fn clip_sets_ops(&self, stack: &LayerGraph) -> Result<Vec<sdf::StringListOp>, QueryError> {
        let mut ops = Vec::new();
        for opinion in self.opinions_in_layer_time(FieldKey::ClipSets.as_str(), stack, None) {
            match opinion?.value.into_owned() {
                // Stop weaker opinions while keeping any stronger composed edits.
                Value::ValueBlock => break,
                Value::StringListOp(op) => ops.push(op),
                Value::TokenListOp(op) => ops.push(op.map(String::from)),
                Value::StringVec(names) => ops.push(sdf::StringListOp::explicit(names)),
                Value::TokenVec(names) => ops.push(sdf::StringListOp::explicit(
                    names.into_iter().map(String::from).collect::<Vec<_>>(),
                )),
                _ => {}
            }
        }
        Ok(ops)
    }

    /// Resolves explicit value clip sets while preserving the layer that
    /// authored path-bearing fields. The top-level `clips` dictionary composes
    /// recursively, but relative clip assets must still be anchored to the
    /// layer that supplied `assetPaths`/`manifestAssetPath`.
    ///
    /// The three asset-valued fields have any `` `${VAR}` `` evaluated against
    /// the variables in scope at the opinion that supplied them, and a set whose
    /// expression fails is dropped with [`CompositionError::InvalidExpression`] in `errors`.
    /// C++ diverges here: `clipSetDefinition.cpp` reads all three through plain
    /// dictionary lookups, and `UsdStage::_MakeResolvedAssetPaths` never descends
    /// into a `VtDictionary`, so an expression is inert there. The Sdf
    /// variable-expression documentation promises support in "asset-valued
    /// attributes and metadata", which these are, so the promise is kept here.
    pub(crate) fn resolve_clip_sets(
        &self,
        stack: &LayerGraph,
        errors: &mut Vec<CompositionError>,
    ) -> Result<Vec<clip::ResolvedClipSet>, QueryError> {
        let mut sets: HashMap<String, HashMap<String, Value>> = HashMap::new();
        let mut blocked_sets: HashSet<String> = HashSet::new();
        // The site that authored a set's clip asset paths: the layer, the stack
        // of the node it came from, and that node's own prim path. The stack
        // supplies the variables a clip-sourced `asset` expression evaluates
        // against, the clip layer itself belonging to no stack, and the three
        // together are the position value resolution consults the set at (C++
        // `Usd_ClipSetDefinition`'s anchor).
        let mut asset_sources: HashMap<String, clip::ClipAnchor> = HashMap::new();
        let mut manifest_layers: HashMap<String, LayerId> = HashMap::new();
        // Sets with explicit `assetPaths` (whose `active`/`times` are retimed
        // as they compose) versus the offset of a template set's authoring
        // node (whose schedule is derived later and retimed afterwards).
        let mut explicit_sets: HashSet<String> = HashSet::new();
        // Where each set's expression-valued asset fields were authored, for the
        // evaluation pass below. Recorded per field: the three can come from
        // different opinions, each with its own variables in scope and its own
        // site to name in a diagnostic. Empty unless a `${VAR}` is authored.
        let mut asset_sites: HashMap<String, ClipAssetSites> = HashMap::new();
        let mut template_offsets: HashMap<String, LayerOffset> = HashMap::new();
        // Offset of the node that supplied `active`, kept so a manifest's own
        // authored times can be mapped into the retimed schedule's frame.
        let mut active_offsets: HashMap<String, LayerOffset> = HashMap::new();

        // Opinions fan out per contributing sublayer, strongest first; a value
        // block on any layer stops every weaker opinion (spec 12.3.4).
        for opinion in self.opinions_in_layer_time(FieldKey::Clips.as_str(), stack, None) {
            let Opinion {
                node,
                layer,
                query_path,
                value,
                offset,
            } = opinion?;
            let node_stack = node.layer_stack_id();
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
                            } else if field == clip::keys::TEMPLATE_ASSET_PATH
                                || field == clip::keys::MANIFEST_ASSET_PATH
                            {
                                clip::as_asset_field(value)
                            } else {
                                value
                            };
                            // The site an expression in this field evaluates
                            // against, kept for the pass that runs once the set
                            // is whole. Built here because only the opinion walk
                            // knows which layer won the field.
                            let site = || {
                                sdf::holds_asset_expression(&value)
                                    .then(|| AssetSite::in_graph(stack, node_stack, layer, &query_path))
                            };
                            // Relative clip asset paths anchor on the layer that
                            // authored them. Explicit `assetPaths` win over a
                            // template in parse_set, so they always set the
                            // anchor, while `templateAssetPath` only sets it when
                            // no explicit `assetPaths` has been composed — else a
                            // weaker template layer would mis-anchor the explicit
                            // paths the stronger layer authored.
                            if field == clip::keys::ACTIVE {
                                active_offsets.insert(set_name.clone(), offset);
                            }
                            if field == clip::keys::ASSET_PATHS {
                                asset_sources.insert(
                                    set_name.clone(),
                                    clip::ClipAnchor {
                                        layer,
                                        prim_path: query_path.clone().into_owned(),
                                        stack: node_stack,
                                    },
                                );
                                explicit_sets.insert(set_name.clone());
                                if let Some(site) = site() {
                                    asset_sites.entry(set_name.clone()).or_default().asset_paths = Some(site);
                                }
                            } else if field == clip::keys::TEMPLATE_ASSET_PATH {
                                if !explicit_sets.contains(&set_name) {
                                    asset_sources.insert(
                                        set_name.clone(),
                                        clip::ClipAnchor {
                                            layer,
                                            prim_path: query_path.clone().into_owned(),
                                            stack: node_stack,
                                        },
                                    );
                                }
                                template_offsets.insert(set_name.clone(), offset);
                                if let Some(site) = site() {
                                    asset_sites.entry(set_name.clone()).or_default().template = Some(site);
                                }
                            } else if field == clip::keys::MANIFEST_ASSET_PATH {
                                manifest_layers.insert(set_name.clone(), layer);
                                if let Some(site) = site() {
                                    asset_sites.entry(set_name.clone()).or_default().manifest = Some(site);
                                }
                            }
                            composed.insert(field, value);
                        }
                    }
                }
                _ => {}
            }
        }

        let order = self.clip_sets_order(stack)?;
        evaluate_clip_assets(stack, &mut sets, order.as_deref(), &asset_sites, errors);

        let clips = Value::Dictionary(
            sets.into_iter()
                .map(|(name, fields)| (name, Value::Dictionary(fields)))
                .collect(),
        );

        Ok(clip::ClipSet::parse(&clips, order.as_deref())
            .into_iter()
            .filter_map(|mut set| {
                let anchor = asset_sources.get(&set.name)?;
                let manifest_layer = manifest_layers.get(&set.name).copied();
                // Explicit `active`/`times` were retimed as they composed. A
                // template schedule is derived in clip time, so retime its
                // stage times here by the authoring node's offset.
                let template_offset = template_offsets.get(&set.name).copied();
                if !explicit_sets.contains(&set.name)
                    && let Some(offset) = template_offset
                {
                    set.retime_stage_times(offset);
                }
                // The offset the schedule now carries, so a manifest read off
                // its own layer can be compared against it in stage time.
                let active_offset = if explicit_sets.contains(&set.name) {
                    active_offsets.get(&set.name).copied().unwrap_or(LayerOffset::IDENTITY)
                } else {
                    template_offset.unwrap_or(LayerOffset::IDENTITY)
                };
                Some(clip::ResolvedClipSet {
                    set,
                    source: anchor.clone(),
                    manifest_layer,
                    active_offset,
                })
            })
            .collect())
    }

    /// Variability resolution per spec 12.2.3: weakest authored opinion wins.
    /// Iterates strongest-to-weakest tracking the latest match, so a
    /// [`Value::ValueBlock`] still blocks weaker opinions.
    fn resolve_variability(&self, stack: &LayerGraph, prop_suffix: Option<&str>) -> Result<Option<Value>, QueryError> {
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
    fn resolve_custom(&self, stack: &LayerGraph, prop_suffix: Option<&str>) -> Result<Option<Value>, QueryError> {
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
    fn resolve_specifier(&self, stack: &LayerGraph, prop_suffix: Option<&str>) -> Result<Option<Value>, QueryError> {
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

/// Where a clip set's expression-valued asset fields were authored, one site
/// per field: the three compose independently and can come from different
/// opinions. `None` where the field is absent or holds no expression.
#[derive(Default)]
struct ClipAssetSites {
    asset_paths: Option<AssetSite>,
    template: Option<AssetSite>,
    manifest: Option<AssetSite>,
}

/// Evaluates the variable expressions in the asset-valued fields of every clip
/// set that participates, in place, dropping a set whose paths do not come out.
///
/// Only the fields a set actually reads are evaluated: a set the composed
/// `clipSets` ordering excludes contributes nothing, and a `templateAssetPath`
/// goes unread when [`clip::has_explicit_assets`] answers. Reporting either
/// would blame an author for a field the set ignores. Precedence is only settled
/// once the set is whole, which is why this runs as its own pass.
///
/// A set is dropped when an asset path it reads fails to evaluate, as a
/// reference arc with a bad asset path is dropped rather than attempted, and
/// when one evaluates away to the expression-language `None`, which names no
/// clip. A manifest that evaluates to `None` is merely unauthored, so its field
/// is removed and the set falls back to a synthesized manifest.
fn evaluate_clip_assets(
    graph: &LayerGraph,
    sets: &mut HashMap<String, HashMap<String, Value>>,
    order: Option<&[String]>,
    asset_sites: &HashMap<String, ClipAssetSites>,
    errors: &mut Vec<CompositionError>,
) {
    if asset_sites.is_empty() {
        return;
    }
    let effective: Vec<String> = clip::effective_set_names(sets, order).into_iter().cloned().collect();
    for name in effective {
        let Some(sites) = asset_sites.get(&name) else { continue };
        let Some(fields) = sets.get_mut(&name) else { continue };
        // Whichever of the two asset-path forms the set does not read goes
        // unevaluated: a wrongly-typed `assetPaths` is as unread as a template
        // an explicit set overrides.
        // Which fields this set reads, asked of the readers themselves: the two
        // asset-path forms are alternatives, and each scalar one must be a shape
        // `clip::asset_input` can consume — an array there is ignored, the way a
        // wrongly-typed `assetPaths` is.
        let explicit = clip::has_explicit_assets(fields);
        let reads_template = !explicit && clip::asset_input(fields, clip::keys::TEMPLATE_ASSET_PATH).is_some();
        let reads_manifest = clip::asset_input(fields, clip::keys::MANIFEST_ASSET_PATH).is_some();
        let fields_and_sites = [
            (clip::keys::ASSET_PATHS, explicit, sites.asset_paths.as_ref()),
            (clip::keys::TEMPLATE_ASSET_PATH, reads_template, sites.template.as_ref()),
            (clip::keys::MANIFEST_ASSET_PATH, reads_manifest, sites.manifest.as_ref()),
        ];
        let mut keep = true;
        for (key, read, site) in fields_and_sites {
            let (true, Some(site)) = (read, site) else { continue };
            let Some((key, value)) = fields.remove_entry(key) else {
                continue;
            };
            let (value, outcome) = asset_resolve::evaluate_values(graph, value, Some(site), errors);
            match outcome {
                sdf::AssetOutcome::Evaluated => {
                    fields.insert(key, value);
                }
                // An unauthored manifest is synthesized from the clips instead.
                sdf::AssetOutcome::None if key == clip::keys::MANIFEST_ASSET_PATH => {}
                // The set is going; evaluating its remaining fields would only
                // report a second cause for one failure.
                _ => {
                    keep = false;
                    break;
                }
            }
        }
        if !keep {
            sets.remove(&name);
        }
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
