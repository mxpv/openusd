//! Relocates: non-destructive namespace remapping.
//!
//! Stateless free functions covering all relocate logic — extracting
//! `layerRelocates` from layer metadata ([`validate_layer_relocates`]),
//! computing effective relocates in composed namespace
//! ([`effective_relocates`]), chaining transitive relocates
//! ([`chain_through_relocates`]), and folding relocated child names
//! ([`apply_child_relocates`]). Each reads the validated per-layer relocates
//! straight off the [`LayerGraph`], so there is no owned state; all external
//! data (layer graph, cached indices) is passed in through parameters, and
//! nothing references [`IndexCache`](super::index_cache::IndexCache) directly.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::sdf::{self, element_cmp, Path, PathComponent, RelocateList};
use crate::tf::Token;

use super::layer_graph::LayerGraph;
use super::mapping::MapFunction;
use super::prim_graph::ArcType;
use super::prim_index::PrimIndex;
use super::{Error, InvalidRelocateReason, LayerId, RelocateConflictReason};

/// Per-layer authored relocates, keyed by layer id.
pub(crate) type LayerRelocates = HashMap<LayerId, RelocateList>;

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
    // Collect every structurally valid authored relocate across the layer stack,
    // recording its layer; cross-relocate conflicts are checked over the whole set
    // ("in the same layer stack"). Each structurally invalid pair is reported here.
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

    let scopes = graph.relocate_conflict_scopes();
    let same_stack = |i: usize, j: usize| {
        let left = all[i].2;
        let right = all[j].2;
        scopes
            .iter()
            .any(|scope| scope.contains(&left) && scope.contains(&right))
    };
    let conflicting = detect_relocate_conflicts(&all, &same_stack, &mut errors);
    let mut out: LayerRelocates = HashMap::new();
    for (idx, (source, target, layer_id, _)) in all.into_iter().enumerate() {
        if !conflicting.contains(&idx) {
            out.entry(layer_id).or_default().push((source, target));
        }
    }
    (out, errors)
}

/// Detects cross-relocate conflicts over the layer stack's structurally valid
/// relocates (C++ `Pcp_ComputeRelocationsForLayerStackWorkspace`'s conflict
/// validation), returning the indices of every conflicting relocate and pushing
/// an error for each. `same_stack(i, j)` reports whether `all[i]` and `all[j]`
/// were authored in the same layer stack. Grouped same-target errors come first
/// (target-sorted), then the pairwise conflicts sorted by `(source, reason,
/// conflict source)`. A conflicting relocate is dropped from the composed map.
fn detect_relocate_conflicts(
    all: &[(Path, Path, LayerId, String)],
    same_stack: &dyn Fn(usize, usize) -> bool,
    errors: &mut Vec<Error>,
) -> HashSet<usize> {
    let mut conflicting = HashSet::new();

    // Multiple sources moving to the same target: all of them are invalid.
    let mut by_target: BTreeMap<Path, Vec<usize>> = BTreeMap::new();
    for (idx, (_, target, _, _)) in all.iter().enumerate() {
        if !target.is_empty() {
            by_target.entry(target.clone()).or_default().push(idx);
        }
    }
    for (target, idxs) in &by_target {
        let mut remaining = idxs.clone();
        while let Some(seed) = remaining.pop() {
            let mut group = vec![seed];
            let mut changed = true;
            while changed {
                changed = false;
                let mut i = 0;
                while i < remaining.len() {
                    if group.iter().any(|&member| same_stack(member, remaining[i])) {
                        group.push(remaining.swap_remove(i));
                        changed = true;
                    } else {
                        i += 1;
                    }
                }
            }
            if group.len() <= 1 {
                continue;
            }
            let mut sources: Vec<(Path, String)> =
                group.iter().map(|&i| (all[i].0.clone(), all[i].3.clone())).collect();
            sources.sort_by(|a, b| a.0.cmp(&b.0));
            errors.push(Error::SameTargetRelocations {
                target: target.clone(),
                sources,
            });
            conflicting.extend(group);
        }
    }

    // Pairwise conflicts: a relocate's target is another's source, or its source
    // or target is a strict descendant of another's source. Emitted sorted by
    // (source, reason, conflict source) — `RelocateConflictReason`'s declaration
    // order is the tie-break order.
    // TODO(perf): O(n^2) over the layer stack's relocates; runs once at extraction
    // (not a query hot path) and n is small, but a group-by-source/prefix index
    // would make it near-linear if a stack ever authors many relocates.
    let mut pairwise: Vec<(usize, usize, RelocateConflictReason)> = Vec::new();
    for i in 0..all.len() {
        for j in 0..all.len() {
            if i == j || !same_stack(i, j) {
                continue;
            }
            let (si, ti) = (&all[i].0, &all[i].1);
            let (sj, tj) = (&all[j].0, &all[j].1);
            if !ti.is_empty() && ti == sj {
                pairwise.push((i, j, RelocateConflictReason::TargetIsSource));
            }
            if !tj.is_empty() && si == tj {
                pairwise.push((i, j, RelocateConflictReason::SourceIsTarget));
            }
            if !ti.is_empty() && ti != sj && ti.has_prefix(sj) {
                pairwise.push((i, j, RelocateConflictReason::TargetDescendant));
            }
            if si != sj && si.has_prefix(sj) {
                pairwise.push((i, j, RelocateConflictReason::SourceDescendant));
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
        conflicting.insert(i);
    }

    conflicting
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
    let layer_maps = collect_layer_maps(graph, path, indices);
    let mut result: RelocateList = Vec::new();

    for (li, map) in &layer_maps {
        let relocates = match graph.get(*li) {
            Some(node) if !node.relocates.is_empty() => &node.relocates,
            _ => continue,
        };
        for (src, tgt) in relocates {
            let Some(composed_src) = map.map_source_to_target(src) else {
                continue;
            };
            let composed_tgt = if tgt.is_empty() {
                tgt.clone()
            } else {
                match map.map_source_to_target(tgt) {
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

/// Collects (layer_index, map_to_root) pairs from ancestor prims and from
/// other cached prims in the same root subtree that have layers with
/// relocates.
fn collect_layer_maps(
    graph: &LayerGraph,
    path: &Path,
    indices: &sdf::PathTable<PrimIndex>,
) -> Vec<(LayerId, MapFunction)> {
    let mut maps: Vec<(LayerId, MapFunction)> = Vec::new();

    // Walk up ancestors. A per-site node fans out into every contributing
    // sublayer so a weaker sublayer that authors `layerRelocates` is mapped
    // through this node's namespace mapping, not just the representative.
    for (p, cached_index) in indices.ancestors(path) {
        if p.is_abs_root() {
            continue;
        }
        for node in cached_index.nodes() {
            if node.arc == ArcType::Relocate {
                continue;
            }
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                if !maps.iter().any(|(li, m)| *li == layer && *m == node.map_to_root) {
                    maps.push((layer, node.map_to_root.clone()));
                }
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
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()) {
                if relocate_layers.contains(&layer)
                    && !maps.iter().any(|(li, m)| *li == layer && *m == node.map_to_root)
                {
                    maps.push((layer, node.map_to_root.clone()));
                }
            }
        }
    }

    maps
}

#[cfg(test)]
mod tests {
    use super::*;

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
