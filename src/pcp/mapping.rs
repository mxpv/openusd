//! Namespace mapping function (`PcpMapFunction` equivalent).
//!
//! A [`MapFunction`] translates paths from one namespace to another using a set
//! of (source, target) path pairs plus an optional whole-namespace root
//! identity. Mapping finds the longest matching prefix and applies
//! [`Path::replace_prefix`], then enforces the bidirectional-invertibility rule
//! (C++ `PcpMapFunction::_Map`) that drops a result shadowed by a closer inverse
//! match.
//!
//! This is the foundation for all namespace remapping in USD composition: each
//! arc (reference, inherit, variant, etc.) produces a map function that
//! translates between the arc target's namespace and the referencing prim's
//! namespace.

use crate::sdf::{self, Path};

/// Internal storage for the explicit path mapping pairs (the root identity is
/// kept as a separate flag, never as a pair).
///
/// The single-pair variant avoids a heap allocation for the common case
/// (one composition arc = one pair).
#[derive(Debug, Clone, PartialEq)]
enum PathMap {
    /// No explicit pairs.
    Empty,
    /// Exactly one pair, stored inline without heap allocation.
    Single((Path, Path)),
    /// Multiple pairs.
    Multi(Vec<(Path, Path)>),
}

impl PathMap {
    fn as_slice(&self) -> &[(Path, Path)] {
        match self {
            PathMap::Empty => &[],
            PathMap::Single(pair) => std::slice::from_ref(pair),
            PathMap::Multi(pairs) => pairs,
        }
    }

    fn from_vec(mut pairs: Vec<(Path, Path)>) -> Self {
        match pairs.len() {
            0 => PathMap::Empty,
            1 => PathMap::Single(pairs.remove(0)),
            _ => PathMap::Multi(pairs),
        }
    }
}

/// A namespace mapping function (C++
/// [`PcpMapFunction`](https://openusd.org/dev/api/class_pcp_map_function.html)).
///
/// Stores explicit (source, target) path pairs for longest-prefix matching plus
/// a `has_root_identity` flag (the `/ → /` catch-all that lets paths outside the
/// explicit domain map to themselves). Storing the root identity as a flag —
/// rather than a `(/, /)` pair — matches C++ and keeps the invertibility check
/// (`_HasBetterTargetMatch`) correct: a path that maps only via the identity is
/// dropped when a real pair's target shadows it.
#[derive(Debug, Clone, PartialEq)]
pub struct MapFunction {
    path_map: PathMap,
    /// Whether the whole-namespace identity `/ → /` is part of this mapping.
    has_root_identity: bool,
    /// Layer time offset associated with this mapping. Composes multiplicatively
    /// with other offsets when [`compose`](Self::compose) is called.
    time_offset: sdf::LayerOffset,
}

impl MapFunction {
    /// The identity mapping: maps every absolute path to itself.
    pub fn identity() -> Self {
        Self {
            path_map: PathMap::Empty,
            has_root_identity: true,
            time_offset: sdf::LayerOffset::IDENTITY,
        }
    }

    /// A null mapping that maps nothing.
    pub fn null() -> Self {
        Self {
            path_map: PathMap::Empty,
            has_root_identity: false,
            time_offset: sdf::LayerOffset::IDENTITY,
        }
    }

    /// Creates a mapping from the given (source, target) path pairs (C++
    /// `PcpMapFunction::Create`). A `(/, /)` pair is folded into the root-identity
    /// flag, and redundant pairs are canonicalized away.
    pub fn new(pairs: impl Into<Vec<(Path, Path)>>) -> Self {
        Self::from_parts(pairs.into(), false, sdf::LayerOffset::IDENTITY)
    }

    /// Builds a mapping from raw pairs, an initial root-identity flag, and a time
    /// offset: extracts any explicit `(/, /)` pair into the flag, then drops
    /// redundant pairs (C++ `_Canonicalize`).
    fn from_parts(mut pairs: Vec<(Path, Path)>, mut has_root_identity: bool, time_offset: sdf::LayerOffset) -> Self {
        pairs.retain(|(s, t)| {
            if s.is_abs_root() && t.is_abs_root() {
                has_root_identity = true;
                false
            } else {
                true
            }
        });
        // A lone pair needs no canonicalization scan: it is redundant only when
        // the root identity already maps it to itself (`source == target`).
        let pairs = match pairs.as_slice() {
            [] => pairs,
            [(s, t)] if has_root_identity && s == t => Vec::new(),
            [_] => pairs,
            _ => Self::canonicalize(pairs, has_root_identity),
        };
        Self {
            path_map: PathMap::from_vec(pairs),
            has_root_identity,
            time_offset,
        }
    }

    /// Drops redundant pairs — those the remaining (more general) pairs plus the
    /// root identity already imply (C++ `PcpMapFunction::Create` /
    /// `_Canonicalize`). For example `(/A, /A)` is redundant once the root
    /// identity is present, and an entry equal to what a shorter-prefix entry
    /// maps it to carries no information. Removing them keeps
    /// [`map_target_to_source`](Self::map_target_to_source) unambiguous.
    fn canonicalize(mut pairs: Vec<(Path, Path)>, has_root_identity: bool) -> Vec<(Path, Path)> {
        // Process shorter sources first so each pair is tested against the more
        // general pairs already kept.
        // TODO(perf): `map_via` rescans `kept` per candidate, so this is O(n²);
        // fine for the 2-3 pair maps composition produces today.
        pairs.sort_by_key(|(s, _)| s.element_count());
        let mut kept: Vec<(Path, Path)> = Vec::new();
        for (source, target) in pairs {
            if Self::map_via(&kept, has_root_identity, &source).as_ref() != Some(&target) {
                kept.push((source, target));
            }
        }
        kept
    }

    /// Maps `path` through `pairs` (plus the root identity) by longest
    /// source-prefix match, ignoring the invertibility check. Used by
    /// canonicalization to test whether a pair is already implied.
    fn map_via(pairs: &[(Path, Path)], has_root_identity: bool, path: &Path) -> Option<Path> {
        match Self::best_prefix(path, pairs, false, 0) {
            Some(i) => path.replace_prefix(&pairs[i].0, &pairs[i].1),
            None if has_root_identity => Some(path.clone()),
            None => None,
        }
    }

    /// Creates a single-pair mapping without the root identity.
    ///
    /// Paths outside the explicit domain return `None` from
    /// [`Self::map_source_to_target`]. Used for external references and payloads
    /// where the mapping crosses layer stack boundaries and the domain is
    /// restricted to the referenced prim's namespace (spec 10.3.2.1.1).
    pub fn from_pair(source: Path, target: Path) -> Self {
        Self {
            path_map: PathMap::Single((source, target)),
            has_root_identity: false,
            time_offset: sdf::LayerOffset::IDENTITY,
        }
    }

    /// Creates a mapping with one explicit pair plus the root identity, so paths
    /// outside the explicit domain map to themselves.
    ///
    /// The standard mapping for arcs within the same layer stack: inherits,
    /// specializes, internal references, variants, and relocates.
    pub fn from_pair_identity(source: Path, target: Path) -> Self {
        Self::from_parts(vec![(source, target)], true, sdf::LayerOffset::IDENTITY)
    }

    /// Returns this mapping with any pair whose source is exactly `source`
    /// removed.
    pub fn dropping_source(&self, source: &Path) -> MapFunction {
        if !self.path_map.as_slice().iter().any(|(s, _)| s == source) {
            return self.clone();
        }
        let pairs: Vec<(Path, Path)> = self
            .path_map
            .as_slice()
            .iter()
            .filter(|(s, _)| s != source)
            .cloned()
            .collect();
        Self::from_parts(pairs, self.has_root_identity, self.time_offset)
    }

    /// Returns `true` if this is an identity mapping (identity paths *and*
    /// identity time offset).
    pub fn is_identity(&self) -> bool {
        self.path_map.as_slice().is_empty() && self.has_root_identity && self.time_offset.is_identity()
    }

    /// Returns `true` if this mapping maps but changes nothing — every explicit
    /// pair is a no-op `(/X, /X)` and the time offset is identity. Returns
    /// `false` for null (empty, no root identity) mappings.
    pub fn is_noop(&self) -> bool {
        !self.is_null() && self.path_map.as_slice().iter().all(|(s, t)| s == t) && self.time_offset.is_identity()
    }

    /// Returns the layer time offset associated with this mapping.
    #[inline]
    pub fn time_offset(&self) -> sdf::LayerOffset {
        self.time_offset
    }

    /// Returns this mapping with its time offset replaced.
    #[inline]
    pub fn with_time_offset(mut self, offset: sdf::LayerOffset) -> Self {
        self.time_offset = offset;
        self
    }

    /// Returns `true` if this mapping maps nothing.
    pub fn is_null(&self) -> bool {
        self.path_map.as_slice().is_empty() && !self.has_root_identity
    }

    /// Returns the explicit (source, target) path pairs, excluding the root
    /// identity.
    pub fn path_pairs(&self) -> &[(Path, Path)] {
        self.path_map.as_slice()
    }

    /// Maps a path from the source namespace to the target namespace (C++
    /// `PcpMapFunction::MapSourceToTarget`, without the invertibility check).
    ///
    /// This is the bare prefix mapping the indexer and value resolution use. The
    /// stricter, invertibility-checked translation used for relationship and
    /// connection targets is [`translate_to_target`](Self::translate_to_target).
    pub fn map_source_to_target(&self, path: &Path) -> Option<Path> {
        self.map_impl(path, false, false)
    }

    /// Maps a path from the target namespace back to the source namespace (C++
    /// `PcpMapFunction::MapTargetToSource`, without the invertibility check).
    pub fn map_target_to_source(&self, path: &Path) -> Option<Path> {
        self.map_impl(path, true, false)
    }

    /// Translates a relationship/connection target to the root namespace through
    /// this node's map (C++ `PcpTranslatePathFromNodeToRoot` →
    /// `MapSourceToTarget` with the full `_Map` invertibility check). Unlike
    /// [`map_source_to_target`](Self::map_source_to_target), the result is dropped
    /// when some other entry's target shadows it (C++ `_HasBetterTargetMatch`) —
    /// the rule that makes a class target naming the class's own instance image
    /// fail to translate, and keeps a relocated class target at its pre-relocation
    /// path.
    pub fn translate_to_target(&self, path: &Path) -> Option<Path> {
        self.map_impl(path, false, true)
    }

    /// Longest-prefix map in the chosen direction (or the root identity). When
    /// `check_bijection` is set, drops the result if the bidirectional
    /// invertibility requirement is not met (C++ `_HasBetterTargetMatch`).
    fn map_impl(&self, path: &Path, invert: bool, check_bijection: bool) -> Option<Path> {
        let pairs = self.path_map.as_slice();
        let best = Self::best_prefix(path, pairs, invert, 0);
        let result = match best {
            Some(i) => {
                let (source, target) = &pairs[i];
                // A block (empty target) makes its source subtree unmappable
                // (C++ `_Map` returns the empty path). Reached only forward;
                // `best_prefix` never matches a block on the target side.
                if target.is_empty() {
                    return None;
                }
                if invert {
                    path.replace_prefix(target, source)
                } else {
                    path.replace_prefix(source, target)
                }
            }
            None if self.has_root_identity => Some(path.clone()),
            None => None,
        }?;
        if check_bijection && self.has_better_target_match(&result, best, invert) {
            return None;
        }
        Some(result)
    }

    /// Index of the entry whose source (or target, when `invert`) is the longest
    /// prefix of `path` with at least `min_elems` path elements (C++
    /// `_GetBestSourceMatch` / `_GetBestTargetMatch`). A block (empty target) is
    /// never matched on the target side.
    fn best_prefix(path: &Path, pairs: &[(Path, Path)], invert: bool, min_elems: usize) -> Option<usize> {
        let mut best: Option<usize> = None;
        let mut best_elems = 0usize;
        for (i, (source, target)) in pairs.iter().enumerate() {
            let key = if invert { target } else { source };
            // Gate on the cheap prefix test before the O(path-length)
            // `element_count` walk. A block (empty target) is never a match.
            if key.is_empty() || !path.has_prefix(key) {
                continue;
            }
            let elems = key.element_count();
            if elems >= min_elems && (best.is_none() || elems >= best_elems) {
                best = Some(i);
                best_elems = elems;
            }
        }
        best
    }

    /// Whether another entry maps `result` back more closely than `best` did, so
    /// the forward mapping is not one-to-one bidirectional (C++
    /// `_HasBetterTargetMatch`). The root identity is never counted here (it is
    /// not an explicit pair), so a path mapped only via the identity is dropped
    /// when any pair's target shadows it.
    fn has_better_target_match(&self, result: &Path, best: Option<usize>, invert: bool) -> bool {
        let pairs = self.path_map.as_slice();
        let min_elems = match best {
            None => 0,
            Some(i) => {
                let (source, target) = &pairs[i];
                if invert { source } else { target }.element_count()
            }
        };
        match Self::best_prefix(result, pairs, !invert, min_elems) {
            Some(j) => Some(j) != best,
            None => false,
        }
    }

    /// Composes two mappings: applies `inner` first, then `self`, so the result
    /// maps `h(x) = self(inner(x))` (C++ `PcpMapFunction::Compose`).
    ///
    /// The composed pairs are built in two halves: each of `inner`'s pairs
    /// `(s, t)` becomes `(s, self(t))`, and each of `self`'s pairs `(s, t)`
    /// becomes `(inner⁻¹(s), t)`. A source produced by both keeps the first
    /// (half-1) mapping. The composed root identity is present only when *both*
    /// halves have it. Pairs whose mapping falls outside the other function's
    /// domain are dropped.
    ///
    /// Time offsets compose: the outer offset (`self`) is concatenated with the
    /// deeper offset (`inner`).
    pub fn compose(&self, inner: &MapFunction) -> MapFunction {
        let time_offset = if self.time_offset.is_identity() && inner.time_offset.is_identity() {
            sdf::LayerOffset::IDENTITY
        } else {
            self.time_offset.concatenate(&inner.time_offset)
        };

        // Identity path-shortcuts, still carrying the composed time offset.
        if self.path_is_identity() {
            return inner.clone().with_time_offset(time_offset);
        }
        if inner.path_is_identity() {
            return self.clone().with_time_offset(time_offset);
        }

        let mut pairs: Vec<(Path, Path)> = Vec::new();

        // Half 1: inner's output range carried through self (C++ `Compose`'s
        // `scratchPair.second = MapSourceToTarget(pair.second)`). An inner target
        // that does not map through `self` — it escaped `self`'s domain, e.g. a
        // relocate to a prim outside an outer reference — becomes a *block* (empty
        // target) rather than being dropped, so the inner source stays unmappable
        // instead of falling back to a shorter pair. An inner block stays a block.
        for (inner_src, inner_tgt) in inner.path_map.as_slice() {
            let composed_tgt = if inner_tgt.is_empty() {
                inner_tgt.clone()
            } else {
                self.map_source_to_target(inner_tgt)
                    .unwrap_or_else(|| Path::from(String::new()))
            };
            pairs.push((inner_src.clone(), composed_tgt));
        }

        // Half 2: self's input domain pulled back through inner.
        for (outer_src, outer_tgt) in self.path_map.as_slice() {
            if let Some(source) = inner.map_target_to_source(outer_src) {
                if !pairs.iter().any(|(s, _)| *s == source) {
                    pairs.push((source, outer_tgt.clone()));
                }
            }
        }

        let has_root_identity = self.has_root_identity && inner.has_root_identity;
        Self::from_parts(pairs, has_root_identity, time_offset)
    }

    /// True iff the path portion is the identity (root identity only, no explicit
    /// pairs), regardless of time offset.
    fn path_is_identity(&self) -> bool {
        self.path_map.as_slice().is_empty() && self.has_root_identity
    }

    /// Returns the inverse mapping (swaps source and target in each pair).
    ///
    /// The root identity is preserved (C++ `GetInverse`); the time offset is left
    /// as identity because the inverse is unused in time-offset-sensitive
    /// contexts and inverting a `scale = 0` offset is undefined.
    pub fn inverse(&self) -> MapFunction {
        let pairs: Vec<_> = self
            .path_map
            .as_slice()
            .iter()
            .map(|(s, t)| (t.clone(), s.clone()))
            .collect();
        Self::from_parts(pairs, self.has_root_identity, sdf::LayerOffset::IDENTITY)
    }

    /// Returns this mapping with the root identity added (C++
    /// `PcpMapFunction::AddRootIdentity`).
    ///
    /// A reference/payload arc maps only its restricted domain. When propagating
    /// implied classes, a class rooted outside that domain must still map across
    /// the arc, so the transfer function is given the root identity catch-all.
    pub fn with_root_identity(&self) -> MapFunction {
        let mut m = self.clone();
        m.has_root_identity = true;
        m
    }

    /// Returns this class-arc map deepened so its non-identity pairs apply at
    /// `node_path` rather than at the shallower site where the arc was
    /// introduced (used by the ancestor-seed implied-class conjugation).
    pub(crate) fn deepen_to(&self, node_path: &Path) -> MapFunction {
        let node = node_path.strip_all_variant_selections();
        let pairs = self.path_map.as_slice();
        if pairs.iter().any(|(s, _)| *s == node) {
            return self.clone();
        }
        let class = pairs
            .iter()
            .filter(|(s, _)| node.has_prefix(s))
            .max_by_key(|(s, _)| s.element_count());
        let Some((class_src, class_tgt)) = class else {
            return self.clone();
        };
        let Some(deepened_target) = node.replace_prefix(class_src, class_tgt) else {
            return self.clone();
        };
        let deepened: Vec<(Path, Path)> = pairs
            .iter()
            .map(|(s, t)| {
                if s == class_src {
                    (node.clone(), deepened_target.clone())
                } else {
                    (s.clone(), t.clone())
                }
            })
            .collect();
        Self::from_parts(deepened, self.has_root_identity, self.time_offset)
    }

    /// Returns this mapping with variant selections stripped from every pair
    /// endpoint, collapsing a variant arc's strip pair `(/X{set=sel} → /X)` to
    /// the identity (which canonicalization then drops).
    ///
    /// C++ map functions never contain variant selections — a variant arc's map
    /// is the identity and the selection lives only in the node path, stripped by
    /// `StripAllVariantSelections` before translation (C++ `_AddVariantArc`,
    /// `Pcp_TranslatePath`). This engine instead bakes the strip into the variant
    /// node's `map_to_parent`; applying this before target translation recovers
    /// the C++ behavior so a sibling target is not shadowed by the strip pair's
    /// target in the invertibility check.
    pub fn without_variant_selections(&self) -> MapFunction {
        let pairs = self.path_map.as_slice();
        // The common case has no variant selections anywhere (`{` only appears in
        // a selection segment); skip the per-endpoint strip and clone then.
        if !pairs
            .iter()
            .any(|(s, t)| s.as_str().contains('{') || t.as_str().contains('{'))
        {
            return self.clone();
        }
        let stripped: Vec<(Path, Path)> = pairs
            .iter()
            .map(|(s, t)| (s.strip_all_variant_selections(), t.strip_all_variant_selections()))
            .collect();
        Self::from_parts(stripped, self.has_root_identity, self.time_offset)
    }

    /// Builds the implied-class map for propagating a class arc across this
    /// transfer arc (C++ `PcpMapFunction::ImpliedClass`): the conjugation
    /// `T ∘ C ∘ T⁻¹`, with the root identity added so a class rooted outside the
    /// arc's restricted domain still maps.
    pub fn implied_class(&self, class_arc: &MapFunction) -> MapFunction {
        if self.is_identity() {
            return class_arc.clone();
        }
        self.compose(&class_arc.compose(&self.inverse())).with_root_identity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> Path {
        Path::from(s.to_string())
    }

    #[test]
    fn identity() {
        let m = MapFunction::identity();
        assert!(m.is_identity());
        assert!(!m.is_null());
        assert_eq!(m.map_source_to_target(&p("/Foo/Bar")), Some(p("/Foo/Bar")));
        assert_eq!(m.map_target_to_source(&p("/Foo/Bar")), Some(p("/Foo/Bar")));
    }

    #[test]
    fn null() {
        let m = MapFunction::null();
        assert!(m.is_null());
        assert!(!m.is_identity());
        assert_eq!(m.map_source_to_target(&p("/Foo")), None);
        assert_eq!(m.map_target_to_source(&p("/Foo")), None);
    }

    #[test]
    fn single_pair_mapping() {
        let m = MapFunction::new(vec![(p("/RefPrim"), p("/MyPrim"))]);
        assert_eq!(m.map_source_to_target(&p("/RefPrim")), Some(p("/MyPrim")));
        assert_eq!(m.map_source_to_target(&p("/RefPrim/Child")), Some(p("/MyPrim/Child")));
        assert_eq!(m.map_source_to_target(&p("/Other")), None);

        assert_eq!(m.map_target_to_source(&p("/MyPrim")), Some(p("/RefPrim")));
        assert_eq!(m.map_target_to_source(&p("/MyPrim/Child")), Some(p("/RefPrim/Child")));
        assert_eq!(m.map_target_to_source(&p("/Other")), None);
    }

    #[test]
    fn longest_prefix_wins() {
        let m = MapFunction::new(vec![(p("/A"), p("/X")), (p("/A/B"), p("/Y"))]);
        assert_eq!(m.map_source_to_target(&p("/A/B/C")), Some(p("/Y/C")));
        assert_eq!(m.map_source_to_target(&p("/A/C")), Some(p("/X/C")));
    }

    #[test]
    fn compose_simple() {
        let inner = MapFunction::new(vec![(p("/Ref"), p("/Class"))]);
        let outer = MapFunction::new(vec![(p("/Class"), p("/Prim"))]);
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/Ref")), Some(p("/Prim")));
        assert_eq!(composed.map_source_to_target(&p("/Ref/Child")), Some(p("/Prim/Child")));
    }

    #[test]
    fn compose_with_identity() {
        let m = MapFunction::new(vec![(p("/A"), p("/B"))]);
        let id = MapFunction::identity();
        assert_eq!(id.compose(&m).map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(m.compose(&id).map_source_to_target(&p("/A")), Some(p("/B")));
    }

    #[test]
    fn inverse_roundtrip() {
        let m = MapFunction::new(vec![(p("/Src"), p("/Tgt"))]);
        let inv = m.inverse();
        assert_eq!(inv.map_source_to_target(&p("/Tgt")), Some(p("/Src")));
        assert_eq!(inv.map_source_to_target(&p("/Tgt/Child")), Some(p("/Src/Child")));
        let m2 = inv.inverse();
        assert_eq!(m2.map_source_to_target(&p("/Src")), Some(p("/Tgt")));
    }

    #[test]
    fn compose_chain() {
        let f1 = MapFunction::new(vec![(p("/A"), p("/B"))]);
        let f2 = MapFunction::new(vec![(p("/B"), p("/C"))]);
        let composed = f2.compose(&f1);
        assert_eq!(composed.map_source_to_target(&p("/A")), Some(p("/C")));
        assert_eq!(composed.map_source_to_target(&p("/A/D")), Some(p("/C/D")));
    }

    #[test]
    fn compose_includes_outer_domain_below_inner() {
        let inner = MapFunction::from_pair(p("/A"), p("/B"));
        let outer = MapFunction::from_pair(p("/B/X"), p("/Y"));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/A/X")), Some(p("/Y")));
        assert_eq!(composed.map_source_to_target(&p("/A/X/leaf")), Some(p("/Y/leaf")));
    }

    #[test]
    fn compose_drops_unmappable() {
        let inner = MapFunction::new(vec![(p("/A"), p("/B"))]);
        let outer = MapFunction::new(vec![(p("/C"), p("/D"))]);
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/A")), None);
    }

    #[test]
    fn from_pair_is_single() {
        let m = MapFunction::from_pair(p("/A"), p("/B"));
        assert!(matches!(m.path_map, PathMap::Single(_)));
        assert_eq!(m.map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(m.map_source_to_target(&p("/A/C")), Some(p("/B/C")));
        assert_eq!(m.map_source_to_target(&p("/Other")), None);
        assert_eq!(m.map_target_to_source(&p("/B")), Some(p("/A")));
    }

    #[test]
    fn from_pair_identity_includes_catch_all() {
        let m = MapFunction::from_pair_identity(p("/A"), p("/B"));
        assert_eq!(m.map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(m.map_source_to_target(&p("/A/C")), Some(p("/B/C")));
        assert_eq!(m.map_source_to_target(&p("/Other")), Some(p("/Other")));
        assert_eq!(m.map_source_to_target(&p("/Other/D")), Some(p("/Other/D")));
        assert_eq!(m.map_target_to_source(&p("/B")), Some(p("/A")));
        assert_eq!(m.map_target_to_source(&p("/Other")), Some(p("/Other")));
    }

    #[test]
    fn from_pair_identity_is_not_identity() {
        let m = MapFunction::from_pair_identity(p("/A"), p("/B"));
        assert!(!m.is_identity());
        assert!(!m.is_noop());
        assert!(!m.is_null());
    }

    #[test]
    fn canonicalize_drops_redundant_identity_pair() {
        // The spurious `/B → /B` pair is implied by the root identity and is
        // dropped, so `/B` maps back to `/A`, not to itself.
        let m = MapFunction::new(vec![
            (p("/A"), p("/B")),
            (p("/B"), p("/B")),
            (Path::abs_root(), Path::abs_root()),
        ]);
        assert_eq!(m.map_target_to_source(&p("/B")), Some(p("/A")));
        assert_eq!(m.path_pairs().len(), 1, "the redundant /B -> /B pair is removed");
    }

    #[test]
    fn from_pair_identity_collapses_when_same_source_target() {
        let m = MapFunction::from_pair_identity(p("/A"), p("/A"));
        assert!(m.is_identity());
        assert!(m.is_noop());
        assert_eq!(m.map_source_to_target(&p("/A")), Some(p("/A")));
        assert_eq!(m.map_source_to_target(&p("/Other")), Some(p("/Other")));
    }

    #[test]
    fn compose_with_identity_pairs() {
        let inner = MapFunction::from_pair_identity(p("/B"), p("/A"));
        let outer = MapFunction::from_pair_identity(p("/A"), p("/C"));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/B")), Some(p("/C")));
        assert_eq!(composed.map_source_to_target(&p("/B/X")), Some(p("/C/X")));
        assert_eq!(composed.map_source_to_target(&p("/Other")), Some(p("/Other")));
    }

    #[test]
    fn inverse_preserves_identity_pair() {
        let m = MapFunction::from_pair_identity(p("/Src"), p("/Tgt"));
        let inv = m.inverse();
        assert_eq!(inv.map_source_to_target(&p("/Tgt")), Some(p("/Src")));
        assert_eq!(inv.map_source_to_target(&p("/Tgt/Child")), Some(p("/Src/Child")));
        assert_eq!(inv.map_source_to_target(&p("/Other")), Some(p("/Other")));
    }

    #[test]
    fn new_single_pair_uses_single_variant() {
        let m = MapFunction::new(vec![(p("/X"), p("/Y"))]);
        assert!(matches!(m.path_map, PathMap::Single(_)));
    }

    /// The bijection check (only on [`MapFunction::translate_to_target`]): a path
    /// that maps via the root identity is dropped when a real pair's target
    /// shadows it (C++ `_HasBetterTargetMatch`). The bare
    /// [`map_source_to_target`](MapFunction::map_source_to_target) does not apply
    /// it.
    #[test]
    fn translate_drops_noninvertible_via_root_identity() {
        let m = MapFunction::from_pair_identity(p("/_class_Model"), p("/Model"));
        // /Model maps to itself via root identity, but /_class_Model -> /Model
        // gives a closer inverse, so the forward translation is non-invertible.
        assert_eq!(m.translate_to_target(&p("/Model")), None);
        assert_eq!(m.translate_to_target(&p("/_class_Model")), Some(p("/Model")));
        // The bare prefix map keeps the root-identity result.
        assert_eq!(m.map_source_to_target(&p("/Model")), Some(p("/Model")));
    }

    #[test]
    fn default_time_offset_is_identity() {
        assert!(MapFunction::identity().time_offset().is_identity());
        assert!(MapFunction::from_pair(p("/A"), p("/B")).time_offset().is_identity());
        assert!(MapFunction::from_pair_identity(p("/A"), p("/B"))
            .time_offset()
            .is_identity());
    }

    #[test]
    fn with_time_offset_replaces() {
        let o = sdf::LayerOffset::new(10.0, 2.0);
        let m = MapFunction::from_pair(p("/A"), p("/B")).with_time_offset(o);
        assert_eq!(m.time_offset(), o);
        let o2 = sdf::LayerOffset::new(5.0, 3.0);
        let m2 = m.with_time_offset(o2);
        assert_eq!(m2.time_offset(), o2);
    }

    #[test]
    fn compose_concatenates_time_offsets() {
        let outer = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(10.0, 2.0));
        let inner = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(20.0, 1.0));
        let composed = outer.compose(&inner);
        assert_eq!(composed.time_offset(), sdf::LayerOffset::new(50.0, 2.0));
    }

    #[test]
    fn compose_carries_offset_through_path_identity_fast_path() {
        let outer = MapFunction::from_pair(p("/A"), p("/B")).with_time_offset(sdf::LayerOffset::new(10.0, 2.0));
        let inner = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(20.0, 1.0));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(composed.time_offset(), sdf::LayerOffset::new(50.0, 2.0));

        let outer = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(10.0, 2.0));
        let inner = MapFunction::from_pair(p("/A"), p("/B")).with_time_offset(sdf::LayerOffset::new(20.0, 1.0));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(composed.time_offset(), sdf::LayerOffset::new(50.0, 2.0));
    }

    #[test]
    fn implied_class_conjugates_through_transfer() {
        let transfer = MapFunction::from_pair_identity(p("/Sullivan"), p("/Sullivan_1"));
        let class_arc = MapFunction::from_pair_identity(p("/Sullivan/_class_Rig"), p("/Sullivan/Rig"));
        let implied = transfer.implied_class(&class_arc);
        assert_eq!(
            implied.map_source_to_target(&p("/Sullivan_1/_class_Rig")),
            Some(p("/Sullivan_1/Rig"))
        );
    }

    #[test]
    fn implied_class_identity_transfer_returns_class() {
        let class_arc = MapFunction::from_pair_identity(p("/_class_Rig"), p("/Rig"));
        let implied = MapFunction::identity().implied_class(&class_arc);
        assert_eq!(implied, class_arc);
    }

    #[test]
    fn is_identity_requires_identity_time_offset() {
        let m = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(10.0, 1.0));
        assert!(!m.is_identity());
        assert!(!m.is_noop());
    }
}
