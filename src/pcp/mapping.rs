//! Namespace mapping function (`PcpMapFunction` equivalent).
//!
//! A [`MapFunction`] translates paths from one namespace to another using
//! a set of (source, target) path pairs. Mapping works by finding the
//! longest matching source prefix and applying [`Path::replace_prefix`].
//!
//! This is the foundation for all namespace remapping in USD composition:
//! each arc (reference, inherit, variant, etc.) produces a map function
//! that translates between the arc target's namespace and the referencing
//! prim's namespace.

use crate::sdf::{self, Path};

/// Internal storage for path mapping pairs.
///
/// The single-pair variant avoids a heap allocation for the common case
/// (one composition arc = one pair). [`from_pair`](MapFunction::from_pair)
/// and [`identity`](MapFunction::identity) use this.
/// [`from_pair_identity`](MapFunction::from_pair_identity) uses the multi
/// variant to store the explicit pair alongside the `(/, /)` catch-all.
#[derive(Debug, Clone, PartialEq)]
enum PathMap {
    /// No pairs (null mapping).
    Empty,
    /// Exactly one pair, stored inline without heap allocation.
    Single((Path, Path)),
    /// Multiple pairs sorted by source path length descending.
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

    fn len(&self) -> usize {
        match self {
            PathMap::Empty => 0,
            PathMap::Single(_) => 1,
            PathMap::Multi(pairs) => pairs.len(),
        }
    }

    fn is_empty(&self) -> bool {
        matches!(self, PathMap::Empty)
    }
}

/// A namespace mapping function.
///
/// Stores (source, target) path pairs for longest-prefix matching.
/// The identity mapping maps `/` → `/`.
///
/// Single-pair mappings (the common case for composition arcs) are
/// stored inline without heap allocation.
///
/// Equivalent to C++ [`PcpMapFunction`](https://openusd.org/dev/api/class_pcp_map_function.html).
#[derive(Debug, Clone, PartialEq)]
pub struct MapFunction {
    path_map: PathMap,
    /// Layer time offset associated with this mapping. Composes multiplicatively
    /// with other offsets when [`compose`](Self::compose) is called. Defaults to
    /// [`sdf::LayerOffset::IDENTITY`] for constructors that do not explicitly
    /// set it; callers attach an offset via [`with_time_offset`](Self::with_time_offset).
    time_offset: sdf::LayerOffset,
}

impl MapFunction {
    /// The identity mapping: maps every absolute path to itself.
    pub fn identity() -> Self {
        Self {
            path_map: PathMap::Single((Path::abs_root(), Path::abs_root())),
            time_offset: sdf::LayerOffset::IDENTITY,
        }
    }

    /// A null mapping that maps nothing.
    pub fn null() -> Self {
        Self {
            path_map: PathMap::Empty,
            time_offset: sdf::LayerOffset::IDENTITY,
        }
    }

    /// Creates a mapping from the given (source, target) path pairs.
    ///
    /// Pairs are sorted by source path length descending so that
    /// longest-prefix matching is a simple linear scan.
    pub fn new(pairs: impl Into<Vec<(Path, Path)>>) -> Self {
        let mut pairs: Vec<(Path, Path)> = pairs.into();
        if pairs.len() > 1 {
            pairs = Self::canonicalize(pairs);
        }
        match pairs.len() {
            0 => Self::null(),
            1 => Self {
                path_map: PathMap::Single(pairs.remove(0)),
                time_offset: sdf::LayerOffset::IDENTITY,
            },
            _ => {
                // Sort by source path length descending for longest-prefix-first.
                pairs.sort_by(|a, b| b.0.as_str().len().cmp(&a.0.as_str().len()));
                Self {
                    path_map: PathMap::Multi(pairs),
                    time_offset: sdf::LayerOffset::IDENTITY,
                }
            }
        }
    }

    /// Drops redundant pairs — those a shorter-prefix entry already implies (C++
    /// `PcpMapFunction::Create` canonicalization). For example `(/A, /A)` is
    /// redundant once `(/, /)` is present, and an entry equal to what its parent
    /// prefix maps it to carries no information.
    ///
    /// Removing them does not change any mapping result, but it keeps
    /// [`map_target_to_source`](Self::map_target_to_source) unambiguous: two
    /// pairs sharing a target (one of them a spurious identity) would otherwise
    /// make the reverse lookup order-dependent, which conjugations like the
    /// implied-class map produce.
    fn canonicalize(mut pairs: Vec<(Path, Path)>) -> Vec<(Path, Path)> {
        // Process shorter sources first so each pair is tested against the more
        // general pairs already kept. A pair is redundant when those already map
        // its source to its target — which also subsumes exact duplicates.
        pairs.sort_by(|a, b| a.0.as_str().len().cmp(&b.0.as_str().len()));

        // TODO(perf): `map_via` makes this O(n²); fine for the 2-3 pair maps
        // composition produces today, revisit if larger maps ever arise.
        let mut kept: Vec<(Path, Path)> = Vec::new();
        for (source, target) in pairs {
            if Self::map_via(&kept, &source).as_ref() != Some(&target) {
                kept.push((source, target));
            }
        }
        kept
    }

    /// Maps `path` through `pairs` by longest source-prefix match (the bare
    /// path-translation [`map_source_to_target`](Self::map_source_to_target)
    /// performs, over an arbitrary pair slice).
    fn map_via(pairs: &[(Path, Path)], path: &Path) -> Option<Path> {
        let mut best: Option<Path> = None;
        let mut best_len = 0;
        for (source, target) in pairs {
            let len = source.as_str().len();
            if len >= best_len {
                if let Some(mapped) = path.replace_prefix(source, target) {
                    best = Some(mapped);
                    best_len = len;
                }
            }
        }
        best
    }

    /// Creates a single-pair mapping without the `(/, /)` identity catch-all.
    ///
    /// Paths outside the explicit domain return `None` from
    /// [`map_source_to_target`]. Used for external references and payloads
    /// where the mapping crosses layer stack boundaries and the domain is
    /// restricted to the referenced prim's namespace (spec 10.3.2.1.1).
    ///
    /// See [`from_pair_identity`](Self::from_pair_identity) for the variant
    /// with identity, used for most composition arcs.
    pub fn from_pair(source: Path, target: Path) -> Self {
        Self {
            path_map: PathMap::Single((source, target)),
            time_offset: sdf::LayerOffset::IDENTITY,
        }
    }

    /// Creates a mapping with one explicit pair plus the `(/, /)` identity
    /// catch-all so that paths outside the explicit domain map to themselves.
    ///
    /// This is the standard mapping for composition arcs that operate within
    /// the same layer stack: inherits (spec 10.3.2.3.1), specializes
    /// (10.3.2.4.1), internal references (10.3.2.1.1), variants, and
    /// relocates.
    ///
    /// See [`from_pair`](Self::from_pair) for the variant without identity,
    /// used for external references and payloads.
    pub fn from_pair_identity(source: Path, target: Path) -> Self {
        Self::new(vec![(source, target), (Path::abs_root(), Path::abs_root())])
    }

    /// Returns `true` if this is an identity mapping (identity paths *and*
    /// identity time offset).
    pub fn is_identity(&self) -> bool {
        self.path_map_is_path_identity() && self.time_offset.is_identity()
    }

    /// Returns `true` if this mapping has pairs but none of them remap,
    /// and the time offset is identity — a non-identity offset retimes
    /// values and is not a no-op.
    ///
    /// A weaker check than [`is_identity`]: `(/A, /A)` is a no-op but not
    /// identity. Returns `false` for null (empty) mappings — a null mapping
    /// maps *nothing*, which is distinct from "maps but changes nothing".
    pub fn is_noop(&self) -> bool {
        !self.path_map.is_empty()
            && self.path_map.as_slice().iter().all(|(s, t)| s == t)
            && self.time_offset.is_identity()
    }

    /// Returns the layer time offset associated with this mapping.
    ///
    /// Analogous to C++ `PcpMapFunction::GetTimeOffset`.
    #[inline]
    pub fn time_offset(&self) -> sdf::LayerOffset {
        self.time_offset
    }

    /// Builder: returns this mapping with its time offset replaced.
    ///
    /// Callers that want to compose a new offset atop an existing one should
    /// do the arithmetic explicitly — e.g.
    /// `map.clone().with_time_offset(map.time_offset().concatenate(&sub))`.
    #[inline]
    pub fn with_time_offset(mut self, offset: sdf::LayerOffset) -> Self {
        self.time_offset = offset;
        self
    }

    /// Returns `true` if this mapping maps nothing.
    pub fn is_null(&self) -> bool {
        self.path_map.is_empty()
    }

    /// Returns the (source, target) path pairs.
    pub fn path_pairs(&self) -> &[(Path, Path)] {
        self.path_map.as_slice()
    }

    /// Maps a path from the source namespace to the target namespace.
    ///
    /// Finds the longest source prefix that matches `path` and applies
    /// [`Path::replace_prefix`] to translate it.
    pub fn map_source_to_target(&self, path: &Path) -> Option<Path> {
        for (source, target) in self.path_map.as_slice() {
            if let Some(mapped) = path.replace_prefix(source, target) {
                return Some(mapped);
            }
        }
        None
    }

    /// Maps a path from the target namespace back to the source namespace.
    ///
    /// Finds the longest target prefix that matches `path` and applies
    /// the reverse translation.
    pub fn map_target_to_source(&self, path: &Path) -> Option<Path> {
        // Target entries are not sorted by length, so find the longest match.
        let mut best: Option<Path> = None;
        let mut best_len = 0;
        for (source, target) in self.path_map.as_slice() {
            let tgt_len = target.as_str().len();
            if tgt_len > best_len {
                if let Some(mapped) = path.replace_prefix(target, source) {
                    best = Some(mapped);
                    best_len = tgt_len;
                }
            }
        }
        best
    }

    /// Composes two mappings: applies `inner` first, then `self`, so the result
    /// maps `h(x) = self(inner(x))` (C++ `PcpMapFunction::Compose`).
    ///
    /// True function composition needs both halves:
    ///
    /// 1. Each of `inner`'s pairs `(s, t)` maps to `(s, self(t))` — `inner`'s
    ///    output range carried through `self`.
    /// 2. Each of `self`'s pairs `(s, t)` maps to `(inner⁻¹(s), t)` — `self`'s
    ///    input domain pulled back through `inner`. Without this half a pair
    ///    of `self` whose source lies *below* `inner`'s targets is lost, which
    ///    breaks conjugations like the implied-class map.
    ///
    /// Pairs whose mapping falls outside the other function's domain are
    /// dropped. When a source is produced by both halves, the half-1 pair wins
    /// (a map never sends two targets to one source). Longest-prefix order is
    /// restored by [`MapFunction::new`].
    ///
    /// Time offsets compose too: the outer offset (`self`) is concatenated with
    /// the deeper offset (`inner`) per the spec retiming formula — see
    /// [`sdf::LayerOffset::concatenate`].
    pub fn compose(&self, inner: &MapFunction) -> MapFunction {
        // Skip the concat in the overwhelmingly common case where neither
        // side carries a retiming — composition gets called per Node at
        // `add_child` time, so the four f64 ops per call add up.
        let time_offset = if self.time_offset.is_identity() && inner.time_offset.is_identity() {
            sdf::LayerOffset::IDENTITY
        } else {
            self.time_offset.concatenate(&inner.time_offset)
        };

        // Identity path-shortcuts still apply for paths, but we need to carry
        // the composed time offset through.
        if self.path_map_is_path_identity() {
            return inner.clone().with_time_offset(time_offset);
        }
        if inner.path_map_is_path_identity() {
            return self.clone().with_time_offset(time_offset);
        }

        let mut pairs: Vec<(Path, Path)> = Vec::new();

        // Half 1: inner's output range carried through self.
        for (inner_src, inner_tgt) in inner.path_map.as_slice() {
            if let Some(composed_tgt) = self.map_source_to_target(inner_tgt) {
                pairs.push((inner_src.clone(), composed_tgt));
            }
        }

        // Half 2: self's input domain pulled back through inner. A source
        // already produced by half 1 keeps that (stronger) mapping.
        for (outer_src, outer_tgt) in self.path_map.as_slice() {
            if let Some(source) = inner.map_target_to_source(outer_src) {
                if !pairs.iter().any(|(s, _)| *s == source) {
                    pairs.push((source, outer_tgt.clone()));
                }
            }
        }

        MapFunction::new(pairs).with_time_offset(time_offset)
    }

    /// Internal helper: true iff the path portion is identity (regardless of
    /// time offset). Used by `compose` to take the fast path without
    /// prematurely discarding a non-identity time offset.
    fn path_map_is_path_identity(&self) -> bool {
        self.path_map.len() == 1
            && self.path_map.as_slice()[0].0.as_str() == "/"
            && self.path_map.as_slice()[0].1.as_str() == "/"
    }

    /// Returns the inverse mapping (swaps source and target in each pair).
    ///
    /// The time offset is left as identity because the inverse operation is
    /// unused in time-offset-sensitive contexts and inverting a `scale = 0`
    /// offset is undefined.
    pub fn inverse(&self) -> MapFunction {
        let pairs: Vec<_> = self
            .path_map
            .as_slice()
            .iter()
            .map(|(s, t)| (t.clone(), s.clone()))
            .collect();
        MapFunction::new(pairs)
    }

    /// Returns this mapping with the `(/, /)` root-identity pair added if it is
    /// not already present (C++ `PcpMapFunction::AddRootIdentity`).
    ///
    /// A reference/payload arc maps only its restricted domain (the referenced
    /// prim's namespace). When propagating implied classes, a class rooted
    /// outside that domain must still map across the arc, so the transfer
    /// function is given the root identity catch-all first. The time offset is
    /// preserved.
    pub fn with_root_identity(&self) -> MapFunction {
        let mut pairs: Vec<(Path, Path)> = self.path_map.as_slice().to_vec();
        if !pairs.iter().any(|(s, t)| s.as_str() == "/" && t.as_str() == "/") {
            pairs.push((Path::abs_root(), Path::abs_root()));
        }
        MapFunction::new(pairs).with_time_offset(self.time_offset)
    }

    /// Builds the implied-class map for propagating a class arc across this
    /// transfer arc (C++ `PcpMapFunction::ImpliedClass`).
    ///
    /// `self` is the transfer function `T` — the map-to-parent of the
    /// reference/payload (or other arc) the class is being propagated across —
    /// and `class_arc` is the class arc's own map `C` in the source (referenced)
    /// namespace. The implied class map in the parent (referencing) namespace is
    /// the conjugation `T ∘ C ∘ T⁻¹`: it carries the same class relationship
    /// through the arc so it holds in the parent's namespace, with any
    /// relocations or offsets in `T` flowing through automatically.
    ///
    /// Classes deliberately cross reference encapsulation, so callers pass a `T`
    /// that carries the `(/, /)` identity catch-all (C++ `AddRootIdentity`) to
    /// let a class rooted outside the arc's restricted domain still map.
    pub fn implied_class(&self, class_arc: &MapFunction) -> MapFunction {
        if self.is_identity() {
            return class_arc.clone();
        }
        self.compose(&class_arc.compose(&self.inverse()))
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
        // /RefPrim -> /MyPrim (reference arc)
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
        // /A/B/C should match /A/B (longer) -> /Y/C, not /A -> /X/B/C
        assert_eq!(m.map_source_to_target(&p("/A/B/C")), Some(p("/Y/C")));
        assert_eq!(m.map_source_to_target(&p("/A/C")), Some(p("/X/C")));
    }

    #[test]
    fn compose_simple() {
        // inner: /Ref -> /Class, outer: /Class -> /Prim
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

        let c1 = id.compose(&m);
        assert_eq!(c1.map_source_to_target(&p("/A")), Some(p("/B")));

        let c2 = m.compose(&id);
        assert_eq!(c2.map_source_to_target(&p("/A")), Some(p("/B")));
    }

    #[test]
    fn inverse_roundtrip() {
        let m = MapFunction::new(vec![(p("/Src"), p("/Tgt"))]);
        let inv = m.inverse();
        assert_eq!(inv.map_source_to_target(&p("/Tgt")), Some(p("/Src")));
        assert_eq!(inv.map_source_to_target(&p("/Tgt/Child")), Some(p("/Src/Child")));

        // Inverse of inverse == original
        let m2 = inv.inverse();
        assert_eq!(m2.map_source_to_target(&p("/Src")), Some(p("/Tgt")));
    }

    #[test]
    fn compose_chain() {
        // Three-level: /A -> /B -> /C
        let f1 = MapFunction::new(vec![(p("/A"), p("/B"))]);
        let f2 = MapFunction::new(vec![(p("/B"), p("/C"))]);
        let composed = f2.compose(&f1);
        assert_eq!(composed.map_source_to_target(&p("/A")), Some(p("/C")));
        assert_eq!(composed.map_source_to_target(&p("/A/D")), Some(p("/C/D")));
    }

    #[test]
    fn compose_includes_outer_domain_below_inner() {
        // Half 2 of composition: `self` has a pair whose source lies below
        // `inner`'s target range. `self ∘ inner` must map /A/X -> /Y (inner
        // sends /A -> /B, then self sends /B/X -> /Y). The simplified
        // composition dropped this; the general one pulls the outer domain
        // back through inner.
        let inner = MapFunction::from_pair(p("/A"), p("/B"));
        let outer = MapFunction::from_pair(p("/B/X"), p("/Y"));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/A/X")), Some(p("/Y")));
        assert_eq!(composed.map_source_to_target(&p("/A/X/leaf")), Some(p("/Y/leaf")));
    }

    #[test]
    fn compose_drops_unmappable() {
        // inner maps /A -> /B, outer only maps /C -> /D
        // /B is not in outer's domain, so the composed pair is dropped
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
        // Explicit pair maps normally.
        assert_eq!(m.map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(m.map_source_to_target(&p("/A/C")), Some(p("/B/C")));
        // Identity catch-all passes through unmatched paths.
        assert_eq!(m.map_source_to_target(&p("/Other")), Some(p("/Other")));
        assert_eq!(m.map_source_to_target(&p("/Other/D")), Some(p("/Other/D")));
        // Reverse mapping works the same way.
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
        // A conjugation can yield a map with a spurious identity pair
        // (`/B → /B`) alongside a real one (`/A → /B`), both implied by `/ → /`.
        // Canonicalization drops the redundant pair so the reverse lookup is
        // unambiguous — `/B` maps back to `/A`, not to itself.
        let m = MapFunction::new(vec![
            (p("/A"), p("/B")),
            (p("/B"), p("/B")),
            (Path::abs_root(), Path::abs_root()),
        ]);
        assert_eq!(m.map_target_to_source(&p("/B")), Some(p("/A")));
        assert_eq!(m.path_pairs().len(), 2, "the redundant /B -> /B pair is removed");
    }

    #[test]
    fn from_pair_identity_collapses_when_same_source_target() {
        // When source == target, the explicit pair is redundant with the
        // identity catch-all, so canonicalization drops it and the mapping
        // collapses to the identity (matching C++ `PcpMapFunction::Create`).
        let m = MapFunction::from_pair_identity(p("/A"), p("/A"));
        assert!(m.is_identity());
        assert!(m.is_noop());
        assert_eq!(m.map_source_to_target(&p("/A")), Some(p("/A")));
        assert_eq!(m.map_source_to_target(&p("/Other")), Some(p("/Other")));
    }

    #[test]
    fn compose_with_identity_pairs() {
        // Both mappings carry the identity catch-all.
        let inner = MapFunction::from_pair_identity(p("/B"), p("/A"));
        let outer = MapFunction::from_pair_identity(p("/A"), p("/C"));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/B")), Some(p("/C")));
        assert_eq!(composed.map_source_to_target(&p("/B/X")), Some(p("/C/X")));
        // Identity catch-all propagates through composition.
        assert_eq!(composed.map_source_to_target(&p("/Other")), Some(p("/Other")));
    }

    #[test]
    fn inverse_preserves_identity_pair() {
        let m = MapFunction::from_pair_identity(p("/Src"), p("/Tgt"));
        let inv = m.inverse();
        assert_eq!(inv.map_source_to_target(&p("/Tgt")), Some(p("/Src")));
        assert_eq!(inv.map_source_to_target(&p("/Tgt/Child")), Some(p("/Src/Child")));
        // Identity catch-all survives inversion.
        assert_eq!(inv.map_source_to_target(&p("/Other")), Some(p("/Other")));
    }

    #[test]
    fn new_single_pair_uses_single_variant() {
        let m = MapFunction::new(vec![(p("/X"), p("/Y"))]);
        assert!(matches!(m.path_map, PathMap::Single(_)));
    }

    // ---- Time offset ---------------------------------------------------

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
        // Replacing again overwrites (not composes) — callers compose explicitly.
        let o2 = sdf::LayerOffset::new(5.0, 3.0);
        let m2 = m.with_time_offset(o2);
        assert_eq!(m2.time_offset(), o2);
    }

    #[test]
    fn compose_concatenates_time_offsets() {
        // BasicTimeOffset_root: outer (10,2) compose inner (20,1) = (50,2).
        let outer = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(10.0, 2.0));
        let inner = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(20.0, 1.0));
        let composed = outer.compose(&inner);
        assert_eq!(composed.time_offset(), sdf::LayerOffset::new(50.0, 2.0));
    }

    #[test]
    fn compose_carries_offset_through_path_identity_fast_path() {
        // Outer has an explicit path pair + non-identity offset. Inner is
        // path-identity with its own offset. Composition should keep outer's
        // path and concatenate offsets.
        let outer = MapFunction::from_pair(p("/A"), p("/B")).with_time_offset(sdf::LayerOffset::new(10.0, 2.0));
        let inner = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(20.0, 1.0));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(composed.time_offset(), sdf::LayerOffset::new(50.0, 2.0));

        // Reverse order: outer is identity-path with offset, inner has pair.
        let outer = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(10.0, 2.0));
        let inner = MapFunction::from_pair(p("/A"), p("/B")).with_time_offset(sdf::LayerOffset::new(20.0, 1.0));
        let composed = outer.compose(&inner);
        assert_eq!(composed.map_source_to_target(&p("/A")), Some(p("/B")));
        assert_eq!(composed.time_offset(), sdf::LayerOffset::new(50.0, 2.0));
    }

    #[test]
    fn implied_class_conjugates_through_transfer() {
        // The Sullivan example from C++ `_GetImpliedClass`: Sullivan_1
        // references Sullivan; Sullivan/Rig inherits Sullivan/_class_Rig. The
        // class arc maps /Sullivan/_class_Rig -> /Sullivan/Rig; the reference
        // maps /Sullivan -> /Sullivan_1. The implied class on the referencing
        // side must map /Sullivan_1/_class_Rig -> /Sullivan_1/Rig.
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
        // An identity transfer leaves the class arc unchanged — within the same
        // layer stack there is nothing to move it across.
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
