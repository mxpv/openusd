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

    /// Composes two mappings: applies `inner` first, then `self`.
    ///
    /// The result maps `inner`'s source namespace directly to `self`'s
    /// target namespace. Each of `inner`'s target entries is mapped
    /// through `self` to produce the composed pairs. Pairs whose inner
    /// target falls outside `self`'s domain are silently dropped.
    ///
    /// Time offsets compose as well: the outer offset (`self`) is
    /// concatenated with the deeper offset (`inner`) per the spec retiming
    /// formula — see [`sdf::LayerOffset::concatenate`].
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

        let mut pairs = Vec::new();
        for (inner_src, inner_tgt) in inner.path_map.as_slice() {
            if let Some(composed_tgt) = self.map_source_to_target(inner_tgt) {
                pairs.push((inner_src.clone(), composed_tgt));
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
    fn from_pair_identity_noop_when_same_source_target() {
        // When source == target, the explicit pair is a no-op but the
        // mapping still carries the identity catch-all.
        let m = MapFunction::from_pair_identity(p("/A"), p("/A"));
        assert!(!m.is_identity());
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
    fn is_identity_requires_identity_time_offset() {
        let m = MapFunction::identity().with_time_offset(sdf::LayerOffset::new(10.0, 1.0));
        assert!(!m.is_identity());
        assert!(!m.is_noop());
    }
}
