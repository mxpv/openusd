//! Relocates: non-destructive namespace remapping.
//!
//! Stateless free functions covering all relocate logic — extracting
//! `layerRelocates` from layer metadata ([`validate_layer_relocates`]),
//! computing effective relocates in composed namespace
//! ([`effective_relocates`]), chaining transitive relocates
//! ([`chain_through_relocates`]), and folding relocated child names
//! ([`apply_child_relocates`]). Layer authored pairs live on the
//! [`LayerGraph`]; stack-effective queries apply duplicate-source and conflict
//! rules for the layer stack being composed. All external data (layer graph,
//! cached indices) is passed in through parameters, and nothing references
//! [`IndexCache`](super::index_cache::IndexCache) directly.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::sdf::{self, element_cmp, Path, PathComponent, RelocateList};
use crate::tf::Token;

use super::layer_graph::LayerGraph;
use super::layer_graph::LayerStackId;
use super::mapping::MapFunction;
use super::prim_graph::ArcType;
use super::prim_index::PrimIndex;
use super::{Error, InvalidRelocateReason, LayerId, RelocateConflictReason};

/// Per-layer authored relocates, keyed by layer id.
pub(crate) type LayerRelocates = HashMap<LayerId, RelocateList>;

/// Whether an authored relocate occurrence contributes to Pcp's composed
/// relocate map for one layer stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RelocateOccurrence {
    /// The occurrence survives extraction and contributes to composition.
    Active,
    /// The source/target pair is structurally invalid before conflict checks.
    DroppedStructural,
    /// A stronger occurrence with the same source already contributes.
    DroppedDuplicateSource,
    /// The occurrence conflicts with another structurally valid occurrence.
    DroppedConflict,
}

impl RelocateOccurrence {
    /// Whether this occurrence survives extraction.
    pub(crate) fn is_active(self) -> bool {
        self == RelocateOccurrence::Active
    }
}

/// Follows `path` to its final location through a set of relocates, applying the
/// longest matching source prefix at each step until it reaches a fixed point.
///
/// This is the chaining a relocate undergoes when an ancestor (or the relocated
/// prim itself) is in turn relocated — e.g. `/A` maps onward to `/C` given both
/// `/A -> /B` and `/B -> /C`, and `…/SubRig/Anim` becomes `…/SubRig2/Anim` once
/// `/…/SubRig -> /…/SubRig2`. The pair whose source equals `skip_source` is
/// ignored so a relocate's own endpoints chain only through *other* renames, not
/// themselves. Choosing the longest source prefix at each step makes the result
/// independent of the relocate list's order; the step count is bounded by the
/// number of relocates, so a cyclic (invalid) set cannot loop forever.
pub(crate) fn chain_through_relocates(path: &Path, relocates: &[(Path, Path)], skip_source: Option<&Path>) -> Path {
    let mut current = path.clone();
    for _ in 0..relocates.len() {
        let next = relocates
            .iter()
            .filter(|(s, t)| !t.is_empty() && Some(s) != skip_source)
            .filter_map(|(s, t)| current.replace_prefix(s, t).map(|p| (s.as_str().len(), p)))
            .filter(|(_, p)| *p != current)
            .max_by_key(|(len, _)| *len);
        match next {
            Some((_, p)) => current = p,
            None => break,
        }
    }
    current
}

/// The name of a path's topmost prim (its root prim), or `None` for the
/// absolute root. Groups cached prims by the root subtree they live under.
fn root_prim_name(path: &Path) -> Option<&str> {
    match path.components().next() {
        Some(PathComponent::Prim(name)) => Some(name),
        _ => None,
    }
}

/// Shifts an endpoint through the single nearest ancestor rename in `renames`.
///
/// When an ancestor prim is relocated, a relocate authored below it sits under
/// the renamed parent in composed namespace (e.g. `…/Rig/SubRig/Anim` becomes
/// `…/Rig2/SubRig/Anim` once `Rig -> Rig2`). Only the nearest applicable
/// ancestor — the longest matching source prefix other than `endpoint` itself —
/// is applied, and it is applied once against the original `endpoint`: matching
/// C++ USD relocates, a relocate's authored source keeps its as-authored
/// depth and is never transitively re-chained (`_ConformLegacyRelocates` is a
/// no-op in USD mode). Returns `endpoint` unchanged when no ancestor matches.
fn shift_through_nearest_ancestor(endpoint: &Path, renames: &[(Path, Path)]) -> Path {
    renames
        .iter()
        .filter(|(src, tgt)| !tgt.is_empty() && src != endpoint)
        .filter_map(|(src, tgt)| endpoint.replace_prefix(src, tgt).map(|p| (src.as_str().len(), p)))
        .max_by_key(|(len, _)| *len)
        .map(|(_, p)| p)
        .unwrap_or_else(|| endpoint.clone())
}

/// Applies one node's layer-stack relocates to a running child-name order, in
/// place (C++ `_ComposePrimChildNamesAtNode`'s relocate classification). The
/// `pairs` are the node layer stack's as-authored relocates; `parent` is the
/// node's path. Renames keep the source name's position, removes drop it, and
/// cross-hierarchy targets are appended in the normative element order (spec
/// 11.3.1's `path_element_sorted`, [`sdf::element_cmp`](crate::sdf::element_cmp)).
/// Every relocation source under `parent` is recorded in `prohibited`.
pub(crate) fn apply_child_relocates(
    parent: &Path,
    pairs: &[(Path, Path)],
    name_order: &mut Vec<Token>,
    name_set: &mut HashSet<Token>,
    prohibited: &mut HashSet<Token>,
) {
    // A source child maps to `Some(new_name)` (renamed in place) or `None`
    // (removed — moved to a different parent or deleted).
    let mut relocations: HashMap<Token, Option<Token>> = HashMap::new();
    let mut adds: Vec<Token> = Vec::new();

    for (src, tgt) in pairs {
        let src_is_child = src.parent().as_ref() == Some(parent);
        let tgt_is_child = !tgt.is_empty() && tgt.parent().as_ref() == Some(parent);
        if src_is_child {
            if let Some(name) = src.name() {
                prohibited.insert(name.into());
                // A target sharing the parent renames in place; anything else
                // (a move elsewhere or a deletion) removes the child.
                let rename = tgt_is_child.then(|| tgt.name()).flatten();
                relocations.insert(name.into(), rename.map(Token::from));
            }
        }
        // A child relocated in from a different parent is an addition.
        if tgt_is_child && !src_is_child {
            if let Some(tgt_name) = tgt.name() {
                adds.push(tgt_name.into());
            }
        }
    }
    // Relocated-in children are appended in the normative element order (spec
    // 11.3.1's `path_element_sorted`), not authored order; the `name_set` guard
    // in the append loop below drops any duplicate target name.
    adds.sort_by(|a, b| element_cmp(a.as_str(), b.as_str()));

    if !relocations.is_empty() {
        let mut retained: Vec<Token> = Vec::with_capacity(name_order.len());
        for name in name_order.drain(..) {
            match relocations.get(&name) {
                Some(Some(new_name)) => {
                    name_set.remove(&name);
                    // A weaker node may already contribute the new name (a "shadow"
                    // child across a reference); the relocation silently drops it
                    // (C++ `_ComposePrimChildNamesAtNode`).
                    if name_set.insert(new_name.clone()) {
                        retained.push(new_name.clone());
                    }
                }
                Some(None) => {
                    name_set.remove(&name);
                }
                None => retained.push(name),
            }
        }
        *name_order = retained;
    }

    for name in adds {
        if name_set.insert(name.clone()) {
            name_order.push(name);
        }
    }
}

/// Validates each layer's authored `layerRelocates` against the
/// [`LayerGraph`]: structurally valid pairs `(source, target)` are returned
/// keyed by layer id (layers without valid relocates are omitted), and each
/// invalid pair becomes an [`Error::InvalidRelocate`] reported in authored order
/// (C++ `PcpErrorInvalidAuthoredRelocates`). Conflicts are scoped to a single
/// layer stack via [`LayerGraph::relocate_conflict_scopes`].
pub(crate) fn validate_layer_relocates(graph: &LayerGraph) -> (LayerRelocates, Vec<Error>) {
    let mut errors = Vec::new();
    // Collect every structurally valid authored relocate, recording its layer.
    // Conflict diagnostics are computed over the layer-stack scopes below.
    let mut all: Vec<(Path, Path, LayerId, String)> = Vec::new();
    for &id in graph.all_ids() {
        // A muted layer contributes nothing, including its authored relocates and
        // their diagnostics.
        if graph.is_muted(id) {
            continue;
        }
        let layer = graph.layer(id);
        for (source, target) in layer.relocates() {
            match relocate_invalid_reason(&source, &target) {
                None => all.push((source, target, id, layer.identifier().to_string())),
                Some(reason) => errors.push(Error::InvalidRelocate {
                    source_path: source,
                    target_path: target,
                    layer: layer.identifier().to_string(),
                    reason,
                }),
            }
        }
    }

    let mut by_layer: HashMap<LayerId, Vec<usize>> = HashMap::new();
    for (idx, (_, _, layer_id, _)) in all.iter().enumerate() {
        by_layer.entry(*layer_id).or_default().push(idx);
    }
    let scope_indices: Vec<Vec<usize>> = graph
        .relocate_conflict_scopes()
        .into_iter()
        .map(|scope| {
            let mut seen = HashSet::new();
            scope
                .into_iter()
                .flat_map(|layer| by_layer.get(&layer).into_iter().flatten().copied())
                .filter(|idx| seen.insert(*idx))
                .collect()
        })
        .collect();
    detect_relocate_conflicts(&all, &scope_indices, &mut errors);

    let mut out: LayerRelocates = HashMap::new();
    for (source, target, layer_id, _) in all {
        out.entry(layer_id).or_default().push((source, target));
    }
    (out, errors)
}

/// Detects cross-relocate conflicts over the layer stack's structurally valid
/// relocates (C++ `Pcp_ComputeRelocationsForLayerStackWorkspace`'s conflict
/// validation), pushing an error for each conflict. Each scope lists indices in
/// authored strength order. Grouped same-target errors come first
/// (target-sorted), then the pairwise conflicts sorted by `(source, reason,
/// conflict source)`. Conflict and duplicate-source dropping happen when
/// composing a specific layer stack; the layer cache keeps the structurally
/// valid authored pairs.
fn detect_relocate_conflicts(all: &[(Path, Path, LayerId, String)], scopes: &[Vec<usize>], errors: &mut Vec<Error>) {
    // TODO: Diagnostics currently group raw authored occurrences, so weaker
    // duplicate-source relocates can make active stack-effective relocates look
    // conflicting. Filter each scope through the duplicate-source
    // classification used by `analyze_relocate_occurrences` before same-target
    // and pairwise conflict reporting.

    // Multiple sources moving to the same target: all of them are invalid.
    let mut same_target_errors: Vec<(Path, Vec<usize>)> = Vec::new();
    let mut seen_same_target: HashSet<(Path, Vec<usize>)> = HashSet::new();
    for scope in scopes {
        let mut by_target: BTreeMap<Path, Vec<usize>> = BTreeMap::new();
        for &idx in scope {
            let target = &all[idx].1;
            if !target.is_empty() {
                by_target.entry(target.clone()).or_default().push(idx);
            }
        }
        for (target, mut group) in by_target {
            if group.len() <= 1 {
                continue;
            }
            group.sort_unstable();
            if seen_same_target.insert((target.clone(), group.clone())) {
                same_target_errors.push((target, group));
            }
        }
    }
    same_target_errors.sort_by(|a, b| a.0.cmp(&b.0));
    for (target, group) in same_target_errors {
        let mut sources: Vec<(Path, String)> = group.iter().map(|&i| (all[i].0.clone(), all[i].3.clone())).collect();
        sources.sort_by(|a, b| a.0.cmp(&b.0));
        errors.push(Error::SameTargetRelocations { target, sources });
    }

    // Pairwise conflicts, emitted sorted by (source, reason, conflict source) —
    // `RelocateConflictReason`'s declaration order is the tie-break order.
    // TODO(perf): O(n^2) over the layer stack's relocates; runs once at extraction
    // (not a query hot path) and n is small, but a group-by-source/prefix index
    // would make it near-linear if a stack ever authors many relocates.
    let mut pairwise: Vec<(usize, usize, RelocateConflictReason)> = Vec::new();
    for scope in scopes {
        for &i in scope {
            for &j in scope {
                if i == j {
                    continue;
                }
                for reason in relocate_pair_conflicts(&all[i].0, &all[i].1, &all[j].0, &all[j].1) {
                    push_pairwise_conflict(&mut pairwise, i, j, reason);
                }
            }
        }
    }
    pairwise.sort_by(|a, b| {
        all[a.0]
            .0
            .cmp(&all[b.0].0)
            .then(a.2.cmp(&b.2))
            .then(all[a.1].0.cmp(&all[b.1].0))
    });
    for (i, j, reason) in pairwise {
        errors.push(Error::ConflictingRelocation {
            source_path: all[i].0.clone(),
            target_path: all[i].1.clone(),
            layer: all[i].3.clone(),
            other_source_path: all[j].0.clone(),
            other_target_path: all[j].1.clone(),
            other_layer: all[j].3.clone(),
            reason,
        });
    }
}

fn push_pairwise_conflict(
    pairwise: &mut Vec<(usize, usize, RelocateConflictReason)>,
    i: usize,
    j: usize,
    reason: RelocateConflictReason,
) {
    if !pairwise.iter().any(|&(pi, pj, pr)| pi == i && pj == j && pr == reason) {
        pairwise.push((i, j, reason));
    }
}

/// A relocate pair presented to [`first_unrepresentable_relocate`] for
/// validation, carrying the edit-batch provenance that decides whether a pair
/// Pcp would drop may be blamed on the batch.
pub(crate) struct BatchRelocate {
    /// The relocate's `(source, target)`; an empty target is a deletion.
    pub pair: (Path, Path),
    /// Whether the batch created or changed this occurrence. Only a fresh pair
    /// can be the reported offender: a pair the batch left untouched was
    /// authored before it and Pcp already tolerates it as a recoverable error.
    /// Freshness is per occurrence, not per value — a pair the batch changed
    /// into the same value as another layer's pre-existing one is still fresh
    /// and still rejected when it conflicts.
    pub fresh: bool,
    /// Whether Pcp had already dropped this structurally valid pair before the
    /// batch. Its continued drop is not the batch's doing, so it is never the
    /// reported offender; the caller checks separately whether it has become
    /// newly active.
    pub dropped_seed: bool,
}

/// The source path of the first relocate Pcp would reject as authored, treating
/// `relocates` as one layer stack's pairs classified by `status` (index-aligned),
/// or `None` if Pcp would accept them all. A pair is rejected when it is
/// structurally invalid (see [`relocate_invalid_reason`]) or conflicts with
/// another pair: two non-empty targets coincide, a target is another's source,
/// a source is another's target, or a source/target is strictly nested in
/// another pair's source. Lets a writer reject a batch up front rather than
/// author relocates Pcp would silently drop.
///
/// Only a [`fresh`](BatchRelocate::fresh) pair that is not a
/// [`dropped_seed`](BatchRelocate::dropped_seed) is blamed — the batch answers
/// only for the occurrences it created or changed, and a fresh pair is rejected
/// when it conflicts with any surviving pair, including a pre-existing one. The
/// reasons mirror [`detect_relocate_conflicts`], which reports them for
/// diagnostics.
pub(crate) fn first_unrepresentable_relocate(
    relocates: &[BatchRelocate],
    status: &[RelocateOccurrence],
) -> Option<Path> {
    debug_assert_eq!(relocates.len(), status.len());
    relocates
        .iter()
        .zip(status)
        .find_map(|(r, status)| (r.fresh && !r.dropped_seed && !status.is_active()).then(|| r.pair.0.clone()))
}

/// The conflict reasons one structurally valid relocate pair `a = (sa, ta)`
/// raises against another `b = (sb, tb)` in the same layer stack: `a`'s target
/// is `b`'s source, `a`'s source is `b`'s target, or `a`'s target/source is a
/// strict descendant of `b`'s source. The single definition of the pairwise
/// rule, shared by [`analyze_relocate_occurrences`] and
/// [`detect_relocate_conflicts`]. Same-target collisions are handled separately,
/// since several sources sharing one target all drop together.
fn relocate_pair_conflicts(sa: &Path, ta: &Path, sb: &Path, tb: &Path) -> Vec<RelocateConflictReason> {
    let mut reasons = Vec::new();
    if !ta.is_empty() && ta == sb {
        reasons.push(RelocateConflictReason::TargetIsSource);
    }
    if !tb.is_empty() && sa == tb {
        reasons.push(RelocateConflictReason::SourceIsTarget);
    }
    if !ta.is_empty() && ta != sb && ta.has_prefix(sb) {
        reasons.push(RelocateConflictReason::TargetDescendant);
    }
    if sa != sb && sa.has_prefix(sb) {
        reasons.push(RelocateConflictReason::SourceDescendant);
    }
    reasons
}

/// Analyze authored relocate occurrences in one layer stack, in strength order.
///
/// Mirrors Pcp extraction in stages: structurally invalid pairs drop first;
/// duplicate sources keep the strongest structurally valid occurrence and drop
/// weaker ones; several sources sharing one target all drop; then the surviving
/// pairs are checked for pairwise conflicts. Duplicate-source occurrences are
/// removed from conflict checks; conflict-dropped occurrences still participate
/// so a connected conflict set drops as one unit.
// TODO(perf): the pairwise pass is O(n^2) over a stack's relocates; n is small
// and this runs at extraction, but a source/target index would make it linear.
pub(crate) fn analyze_relocate_occurrences(pairs: &[(Path, Path)]) -> Vec<RelocateOccurrence> {
    let mut status: Vec<RelocateOccurrence> = pairs
        .iter()
        .map(|(source, target)| {
            if relocate_invalid_reason(source, target).is_some() {
                RelocateOccurrence::DroppedStructural
            } else {
                RelocateOccurrence::Active
            }
        })
        .collect();

    let mut seen_sources: HashSet<&Path> = HashSet::new();
    for (i, (source, _)) in pairs.iter().enumerate() {
        if !status[i].is_active() {
            continue;
        }
        if !seen_sources.insert(source) {
            status[i] = RelocateOccurrence::DroppedDuplicateSource;
        }
    }

    let can_conflict: Vec<bool> = status.iter().map(|s| s.is_active()).collect();
    let mut by_target: HashMap<&Path, Vec<usize>> = HashMap::new();
    for (i, (_, target)) in pairs.iter().enumerate() {
        if can_conflict[i] && !target.is_empty() {
            by_target.entry(target).or_default().push(i);
        }
    }
    for group in by_target.values() {
        if group.len() > 1 {
            for &i in group {
                status[i] = RelocateOccurrence::DroppedConflict;
            }
        }
    }

    for i in 0..pairs.len() {
        if !can_conflict[i] {
            continue;
        }
        let (si, ti) = (&pairs[i].0, &pairs[i].1);
        for j in 0..pairs.len() {
            if i == j || !can_conflict[j] {
                continue;
            }
            let (sj, tj) = (&pairs[j].0, &pairs[j].1);
            if !relocate_pair_conflicts(si, ti, sj, tj).is_empty() {
                status[i] = RelocateOccurrence::DroppedConflict;
                break;
            }
        }
    }

    status
}

/// The rule an authored relocate `source -> target` violates, or `None` when it
/// is valid (C++ `Pcp_ComputeRelocationsForLayerStack`'s authored-relocate
/// validation, whose messages this mirrors). An invalid relocate is ignored
/// rather than composed; composing one whose source and target are nested
/// recurses without terminating (the bug-92827 hang).
///
/// A deletion relocate (empty target) is always valid. Otherwise: a root prim
/// cannot be a relocate source, and the target must not equal, be an ancestor
/// of, or be a descendant of the source — the moved prim would otherwise contain
/// or be contained by its own destination.
fn relocate_invalid_reason(source: &Path, target: &Path) -> Option<InvalidRelocateReason> {
    if target.is_empty() {
        return None;
    }
    if source.is_root_prim() {
        return Some(InvalidRelocateReason::RootPrimSource);
    }
    if source == target {
        return Some(InvalidRelocateReason::SourceEqualsTarget);
    }
    if source.has_prefix(target) {
        return Some(InvalidRelocateReason::TargetIsAncestor);
    }
    if target.has_prefix(source) {
        return Some(InvalidRelocateReason::TargetIsDescendant);
    }
    None
}

/// Computes effective relocates for a parent prim in composed namespace.
///
/// Collects relocates from all layers reachable through any cached prim in the
/// same root subtree, maps them to composed namespace using the layer's
/// namespace mapping, then folds each endpoint through the nearest ancestor
/// rename. Used to apply relocates to a relationship/connection's *deleted*
/// target paths, which have no per-node origin to translate through (resolved
/// targets translate through their node's own map instead).
pub(crate) fn effective_relocates(
    graph: &LayerGraph,
    path: &Path,
    indices: &sdf::PathTable<PrimIndex>,
) -> RelocateList {
    let stack_maps = collect_stack_maps(graph, path, indices);
    let mut result: RelocateList = Vec::new();

    for (stack, map) in &stack_maps {
        for (src, tgt) in graph.combined_relocates(*stack) {
            let Some(composed_src) = map.map_source_to_target(&src) else {
                continue;
            };
            let composed_tgt = if tgt.is_empty() {
                tgt.clone()
            } else {
                match map.map_source_to_target(&tgt) {
                    Some(t) => t,
                    None => continue,
                }
            };
            let pair = (composed_src, composed_tgt);
            if !result.contains(&pair) {
                result.push(pair);
            }
        }
    }

    // Sort by target length descending for longest-prefix-first matching.
    result.sort_by(|a, b| b.1.as_str().len().cmp(&a.1.as_str().len()));

    // Shift each endpoint through a single ancestor rename: when an ancestor
    // prim is relocated, a relocate authored below it sits under the renamed
    // parent in composed namespace (e.g. `…/Rig/SubRig/Anim` becomes
    // `…/Rig2/SubRig/Anim` once `Rig` is relocated to `Rig2`). Matching C++
    // USD relocates, sources are not transitively re-chained: a relocate's
    // authored source keeps its as-authored depth (C++ `_ConformLegacyRelocates`
    // is a no-op in USD mode), so only the nearest applicable ancestor rename is
    // folded in.
    let snapshot = result.clone();
    for entry in &mut result {
        entry.0 = shift_through_nearest_ancestor(&entry.0, &snapshot);
        if !entry.1.is_empty() {
            entry.1 = shift_through_nearest_ancestor(&entry.1, &snapshot);
        }
    }

    result
}

/// Collects (layer-stack, map_to_root) pairs from ancestor prims and from
/// other cached prims in the same root subtree that have layers with
/// relocates.
fn collect_stack_maps(
    graph: &LayerGraph,
    path: &Path,
    indices: &sdf::PathTable<PrimIndex>,
) -> Vec<(LayerStackId, MapFunction)> {
    let mut maps: Vec<(LayerStackId, MapFunction)> = Vec::new();

    // Walk up ancestors. Each node's layer stack is filtered independently, so a
    // relocate dropped in the root stack can still contribute when that same
    // layer is referenced as its own stack.
    for (p, cached_index) in indices.ancestors(path) {
        if p.is_abs_root() {
            continue;
        }
        for node in cached_index.nodes() {
            if node.arc == ArcType::Relocate {
                continue;
            }
            let stack = node.layer_stack_id();
            if !maps.iter().any(|(s, m)| *s == stack && *m == node.map_to_root) {
                maps.push((stack, node.map_to_root.clone()));
            }
        }
    }

    // Also search cached prims in the same root subtree for layers with
    // relocates that weren't found in the ancestor walk (e.g. referenced
    // layers only reachable from a sibling branch).
    let relocate_layers: Vec<LayerId> = graph
        .all_ids()
        .iter()
        .copied()
        .filter(|&id| graph.get(id).is_some_and(|node| !node.relocates.is_empty()))
        .collect();
    let root_name = root_prim_name(path);

    // Sort for deterministic iteration: the collected layer-map order feeds
    // downstream relocate composition, so it must not depend on hash order.
    let mut entries: Vec<(&Path, &PrimIndex)> = indices.iter().collect();
    entries.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (cached_path, cached_index) in entries {
        if root_prim_name(cached_path) != root_name {
            continue;
        }
        for node in cached_index.all_nodes() {
            if node.arc == ArcType::Relocate {
                continue;
            }
            let stack = node.layer_stack_id();
            let has_relocates = graph
                .layer_stack(stack)
                .iter()
                .any(|&(layer, _)| relocate_layers.contains(&layer));
            if has_relocates && !maps.iter().any(|(s, m)| *s == stack && *m == node.map_to_root) {
                maps.push((stack, node.map_to_root.clone()));
            }
        }
    }

    maps
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Freshness is per occurrence, not per value: an occurrence the batch
    /// changed into the same pair as an untouched pre-existing one is still
    /// blamed for the same-target conflict, while two untouched pre-existing
    /// pairs are Pcp's own recoverable error and are not reported.
    #[test]
    fn fresh_value_conflict() {
        let p = Path::from;
        let pairs = vec![(p("/W/A"), p("/W/B")), (p("/W/A"), p("/W/B"))];
        let status = analyze_relocate_occurrences(&pairs);
        let batch = |fresh: [bool; 2]| -> Vec<BatchRelocate> {
            pairs
                .iter()
                .zip(fresh)
                .map(|(pair, fresh)| BatchRelocate {
                    pair: pair.clone(),
                    fresh,
                    dropped_seed: false,
                })
                .collect()
        };
        // Second occurrence changed by the batch into the first's value.
        assert_eq!(
            first_unrepresentable_relocate(&batch([false, true]), &status),
            Some(p("/W/A"))
        );
        // Neither changed by the batch: a pre-existing conflict, not reported.
        assert_eq!(first_unrepresentable_relocate(&batch([false, false]), &status), None);
    }

    #[test]
    fn invalid_seed_inactive() {
        let p = Path::from;
        let pairs = vec![(p("/A"), p("/B")), (p("/World/A"), p("/World/B"))];
        assert_eq!(
            analyze_relocate_occurrences(&pairs),
            vec![RelocateOccurrence::DroppedStructural, RelocateOccurrence::Active]
        );
    }

    #[test]
    fn conflicting_seeds_inactive() {
        let p = Path::from;
        let pairs = vec![
            (p("/World/A"), p("/World/C")),
            (p("/World/B"), p("/World/D")),
            (p("/World/D"), p("/World/C")),
        ];
        assert_eq!(
            analyze_relocate_occurrences(&pairs),
            vec![
                RelocateOccurrence::DroppedConflict,
                RelocateOccurrence::DroppedConflict,
                RelocateOccurrence::DroppedConflict
            ]
        );
    }

    #[test]
    fn duplicate_source_strength() {
        let p = Path::from;
        let pairs = vec![(p("/World/A"), p("/World/C")), (p("/World/A"), p("/World/D"))];
        assert_eq!(
            analyze_relocate_occurrences(&pairs),
            vec![RelocateOccurrence::Active, RelocateOccurrence::DroppedDuplicateSource]
        );
    }

    #[test]
    fn duplicate_source_skips_conflict() {
        let p = Path::from;
        let pairs = vec![
            (p("/World/A"), p("/World/C")),
            (p("/World/A"), p("/World/D")),
            (p("/World/B"), p("/World/D")),
        ];
        assert_eq!(
            analyze_relocate_occurrences(&pairs),
            vec![
                RelocateOccurrence::Active,
                RelocateOccurrence::DroppedDuplicateSource,
                RelocateOccurrence::Active,
            ]
        );
    }

    /// A relocate is invalid when its source and target are nested within one
    /// another (C++ "the target of a relocate cannot be an ancestor of its
    /// source"). Composing such a relocate recurses forever (bug 92827), so the
    /// pair is dropped at extraction. Deletion (empty target) and disjoint
    /// source/target pairs stay valid.
    #[test]
    fn relocate_validity() {
        let p = Path::from;
        let reason = |s, t| relocate_invalid_reason(&p(s), &p(t));
        // Target is an ancestor of the source (the bug-92827 hang).
        assert_eq!(
            reason("/Rig/Other/A/Instance/A", "/Rig/Other/A"),
            Some(InvalidRelocateReason::TargetIsAncestor)
        );
        // Target is a descendant of the source.
        assert_eq!(
            reason("/Rig/A", "/Rig/A/B"),
            Some(InvalidRelocateReason::TargetIsDescendant)
        );
        // Identical source and target.
        assert_eq!(
            reason("/Rig/B", "/Rig/B"),
            Some(InvalidRelocateReason::SourceEqualsTarget)
        );
        // A root prim cannot be a relocate source.
        assert_eq!(reason("/A", "/B"), Some(InvalidRelocateReason::RootPrimSource));
        // Disjoint move — the ordinary valid case.
        assert_eq!(reason("/Rig/Model", "/Group/Model"), None);
        // Deletion relocate (empty target) keeps its source as a prohibited name.
        assert_eq!(reason("/Rig/Model", ""), None);
    }

    /// Only the nearest ancestor rename shifts an endpoint; a relocate's source
    /// is not transitively re-chained through a rename applied to an already-
    /// shifted path (C++ `_ConformLegacyRelocates` is a no-op in USD mode).
    #[test]
    fn nearest_ancestor_only() {
        let renames = vec![
            (Path::from("/Rig"), Path::from("/Rig2")),
            (Path::from("/Rig2/Sub"), Path::from("/Rig2/SubX")),
        ];
        // `/Rig` is the only ancestor rename that prefixes the as-authored
        // endpoint, so the shift applies it once and stops: `/Rig/Sub/Anim`
        // becomes `/Rig2/Sub/Anim`, and the deeper `/Rig2/Sub` rename — which
        // matches only the shifted path — is not re-applied.
        let shifted = shift_through_nearest_ancestor(&Path::from("/Rig/Sub/Anim"), &renames);
        assert_eq!(shifted, Path::from("/Rig2/Sub/Anim"));
    }

    /// An endpoint with no ancestor rename is returned unchanged, and a rename
    /// whose source equals the endpoint itself never applies.
    #[test]
    fn no_ancestor_match_unchanged() {
        let renames = vec![(Path::from("/A"), Path::from("/B"))];
        assert_eq!(
            shift_through_nearest_ancestor(&Path::from("/A"), &renames),
            Path::from("/A")
        );
        assert_eq!(
            shift_through_nearest_ancestor(&Path::from("/X/Y"), &renames),
            Path::from("/X/Y")
        );
    }

    /// Children relocated in from a different parent are appended in the
    /// normative element order (spec 11.3.1's `path_element_sorted`), not the
    /// authored or byte-lexicographic order: `B9` precedes `B10` because the
    /// digit runs compare numerically, even though `"B10" < "B9"` byte-wise.
    #[test]
    fn relocated_in_children_element_ordered() {
        let pairs = vec![
            (Path::from("/Src/B10"), Path::from("/Dst/B10")),
            (Path::from("/Src/B9"), Path::from("/Dst/B9")),
        ];
        let mut name_order = Vec::new();
        let mut name_set = HashSet::new();
        let mut prohibited = HashSet::new();
        apply_child_relocates(
            &Path::from("/Dst"),
            &pairs,
            &mut name_order,
            &mut name_set,
            &mut prohibited,
        );
        assert_eq!(name_order.iter().map(|t| t.as_str()).collect::<Vec<_>>(), ["B9", "B10"]);
    }
}
