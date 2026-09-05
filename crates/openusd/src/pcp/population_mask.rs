//! The population mask (C++ `UsdStagePopulationMask`): the set of prim paths a
//! stage exposes.
//!
//! It lives here rather than in `usd` because it is a composition-identity
//! input, not just a query filter: an instance's mask — made relative to the
//! instance through [`PopulationMask::make_relative_to`] — is part of its
//! [`InstanceKey`](super::instancing::InstanceKey), so two instances the mask
//! affects differently share no prototype. `LoadRules` sits here for the same
//! reason. The public spelling stays USD-shaped: `usd` re-exports this as
//! `StagePopulationMask`, matching C++, where `GetPopulationMask` is `UsdStage`
//! API and the mask type itself knows nothing about instancing.

use std::borrow::Cow;

use crate::sdf::{self, Path};

/// Population mask limiting which prim paths a
/// [`Stage`](crate::usd::Stage) exposes (C++ `UsdStagePopulationMask`).
///
/// A mask path includes that prim's subtree. Ancestors of masked paths are also
/// included, so traversal can reach the requested working set.
///
/// The stored paths are a sorted antichain of absolute prim paths (C++
/// `_ValidateAndNormalize`): sorted so equal masks compare and hash equal —
/// required by `InstanceKey` — and free of redundant descendants so membership
/// is one binary search rather than a scan.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PopulationMask {
    /// Sorted, with no path a prefix of another.
    ///
    /// Path order is plain string order, which for the absolute prim paths a
    /// mask may hold puts each path's descendants in one contiguous run
    /// directly after it: the separator `/` sorts below every character a prim
    /// name may begin with, so `/A/C` precedes `/AB`. Every search below relies
    /// on that.
    paths: Vec<Path>,
}

/// Why a path was rejected from a [`PopulationMask`].
///
/// C++ `UsdStagePopulationMask::Add` posts a coding error and drops anything
/// that is not an absolute prim path; this reports it instead of silently
/// coercing the caller's path into a different one.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum PopulationMaskError {
    /// The path did not parse.
    #[error(transparent)]
    Parse(#[from] sdf::PathParseError),
    /// The path parsed but is not an absolute prim path — a relative path, a
    /// property path, or one carrying a `{set=sel}` variant selection.
    #[error("a population mask path must be an absolute prim path, got `{0}`")]
    NotAbsolutePrimPath(Path),
}

impl PopulationMask {
    /// Creates a mask that includes the full stage.
    pub fn all() -> Self {
        Self {
            paths: vec![Path::abs_root()],
        }
    }

    /// Creates an empty mask, which includes nothing.
    pub fn empty() -> Self {
        Self { paths: Vec::new() }
    }

    /// Creates a mask from prim paths, normalizing once: sort, then drop every
    /// path an earlier one already covers. Sorting puts each path's descendants
    /// directly after it, which is exactly the neighbour `dedup_by` compares
    /// against (C++ `SdfPath::RemoveDescendentPaths`).
    pub fn new(paths: impl IntoIterator<Item: sdf::IntoPath>) -> Result<Self, PopulationMaskError> {
        let mut paths: Vec<Path> = paths.into_iter().map(validate).collect::<Result<_, _>>()?;
        paths.sort();
        paths.dedup_by(|candidate, kept| candidate.has_prefix(kept));
        Ok(Self { paths })
    }

    /// Returns a copy of this mask with `path` added.
    pub fn with_path(mut self, path: impl sdf::IntoPath) -> Result<Self, PopulationMaskError> {
        self.add_path(path)?;
        Ok(self)
    }

    /// Adds a prim path to the mask, keeping it a sorted antichain: the path is
    /// inserted at its ordered position, and the descendants it subsumes are
    /// removed as one contiguous range. A path an existing entry already covers
    /// is dropped.
    pub fn add_path(&mut self, path: impl sdf::IntoPath) -> Result<&mut Self, PopulationMaskError> {
        let path = validate(path)?;
        if self.includes_subtree(&path) {
            return Ok(self);
        }
        // Everything `path` covers sorts immediately after it, contiguously.
        let at = self.paths.partition_point(|p| *p < path);
        let end = at + self.paths[at..].partition_point(|p| p.has_prefix(&path));
        self.paths.splice(at..end, [path]);
        Ok(self)
    }

    /// Returns the mask paths, sorted and with redundant descendants removed.
    pub fn paths(&self) -> &[Path] {
        &self.paths
    }

    /// Returns `true` if the mask contains no paths, and so includes nothing.
    pub fn is_empty(&self) -> bool {
        self.paths.is_empty()
    }

    /// Returns `true` if the mask includes the full stage.
    ///
    /// The absolute root covers every path, so normalization reduces a mask
    /// containing it to exactly `[/]`.
    pub fn is_all(&self) -> bool {
        self.paths.first().is_some_and(Path::is_abs_root)
    }

    /// Returns `true` if `path` is inside the population mask — it lies at or
    /// below a mask path, or is an ancestor of one so traversal can reach the
    /// working set (C++ `UsdStagePopulationMask::Includes`).
    ///
    /// Variant selection segments in `path` are stripped before matching so a
    /// mask of `/Prim/Child` still includes opinions authored under
    /// `/Prim{set=sel}Child`.
    pub fn includes(&self, path: &Path) -> bool {
        self.matches(path, false)
    }

    /// Returns `true` if the mask includes `path` and its entire subtree — that
    /// is, `path` is at or below a mask path (C++
    /// `UsdStagePopulationMask::IncludesSubtree`). Being a mere ancestor of a
    /// mask path is not enough, since the rest of the subtree stays excluded.
    ///
    /// Child filtering short-circuits on this: once a subtree is wholly
    /// included, no descendant needs testing.
    pub fn includes_subtree(&self, path: &Path) -> bool {
        self.matches(path, true)
    }

    /// Re-expresses this mask relative to `instance`, for use as an instancing
    /// key ingredient (C++ `Usd_InstanceKey`'s `_MakeMaskRelativeTo`). Mask
    /// paths below `instance`
    /// are re-rooted onto the absolute root; those outside its subtree describe
    /// nothing about it and are dropped.
    ///
    /// An instance whose whole subtree the mask includes keys as
    /// [`all`](Self::all). C++ derives the empty mask for that case and gets
    /// away with it only because it never keys an instance the mask excluded,
    /// which would derive the same empty mask; naming the two apart keeps the
    /// distinction available here.
    pub fn make_relative_to(&self, instance: &Path) -> Self {
        if self.includes_subtree(instance) {
            return Self::all();
        }
        let root = Path::abs_root();
        Self {
            // Already sorted and reduced: re-rooting a subtree's paths onto `/`
            // preserves both, since it strips a shared prefix from each.
            paths: self
                .paths
                .iter()
                .filter_map(|p| p.replace_prefix(instance, &root))
                .collect(),
        }
    }

    /// Whether any mask path relates to `path`: `subtree_only` demands that a
    /// mask path be an ancestor of (or equal to) `path`, while the default also
    /// accepts a mask path *below* `path`.
    ///
    /// One binary search does both. The insertion point's predecessor is the
    /// only possible ancestor, because a prefix sorts before what it prefixes;
    /// the entry at the insertion point is the first candidate descendant.
    fn matches(&self, path: &Path, subtree_only: bool) -> bool {
        if self.is_all() {
            return true;
        }
        // Both normalizations copy the whole path, so borrow the common case:
        // a plain prim path is already in the mask's coordinate space, and the
        // tests that say so only scan.
        let path = if path.is_property_path() || path.contains_prim_variant_selection() {
            Cow::Owned(path.prim_path().strip_all_variant_selections())
        } else {
            Cow::Borrowed(path)
        };
        let path = path.as_ref();
        let at = self.paths.partition_point(|p| p < path);
        // A proper ancestor sorts before `path`, so the entry preceding the
        // insertion point is the only one that can be one.
        if at > 0 && path.has_prefix(&self.paths[at - 1]) {
            return true;
        }
        // An equal entry, and every descendant, sort at the insertion point.
        match self.paths.get(at) {
            Some(entry) if entry == path => true,
            Some(entry) => !subtree_only && entry.has_prefix(path),
            None => false,
        }
    }
}

impl Default for PopulationMask {
    fn default() -> Self {
        Self::all()
    }
}

/// Parses `path` and accepts it only as an absolute prim path — what C++
/// `UsdStagePopulationMask` stores. The pseudo-root is a prim path here even
/// though [`Path::is_prim_path`] excludes it, since it is the spelling of
/// [`PopulationMask::all`].
fn validate(path: impl sdf::IntoPath) -> Result<Path, PopulationMaskError> {
    let path = sdf::try_into_path(path)?;
    if path.is_abs() && (path.is_abs_root() || (path.is_prim_path() && !path.contains_prim_variant_selection())) {
        Ok(path)
    } else {
        Err(PopulationMaskError::NotAbsolutePrimPath(path))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid test path")
    }

    fn mask(paths: &[&str]) -> PopulationMask {
        PopulationMask::new(paths.iter().copied()).expect("valid mask paths")
    }

    /// Construction sorts and drops the descendants an ancestor already
    /// covers, whatever order the caller supplied.
    #[test]
    fn new_normalizes() {
        let m = mask(&["/B/Child", "/A", "/B", "/A/Deep/Er"]);
        assert_eq!(m.paths(), &[p("/A"), p("/B")]);
    }

    /// Adding the absolute root reduces the mask to it alone.
    #[test]
    fn root_subsumes_all() {
        let mut m = mask(&["/A", "/B"]);
        m.add_path("/").expect("root is a valid mask path");
        assert_eq!(m.paths(), &[Path::abs_root()]);
        assert!(m.is_all());
    }

    /// An incremental add keeps the antichain: a covered path is dropped, and
    /// a covering one replaces the run it subsumes.
    #[test]
    fn add_path_reduces() {
        let mut m = mask(&["/A/B"]);
        m.add_path("/A/B/C").expect("valid");
        assert_eq!(m.paths(), &[p("/A/B")], "a covered path is dropped");

        m.add_path("/A").expect("valid");
        assert_eq!(m.paths(), &[p("/A")], "a covering path replaces what it subsumes");
    }

    /// `includes` accepts ancestors of mask paths so traversal can reach the
    /// working set; `includes_subtree` does not.
    #[test]
    fn includes_vs_subtree() {
        let m = mask(&["/World/Hero"]);
        for (path, includes, subtree) in [
            ("/", true, false),
            ("/World", true, false),
            ("/World/Hero", true, true),
            ("/World/Hero/Geom", true, true),
            ("/World/Other", false, false),
        ] {
            assert_eq!(m.includes(&p(path)), includes, "includes {path}");
            assert_eq!(m.includes_subtree(&p(path)), subtree, "includes_subtree {path}");
        }
    }

    /// A variant selection in the queried path is stripped before matching, so
    /// an opinion authored inside a variant still resolves against the mask.
    #[test]
    fn includes_strips_variants() {
        assert!(mask(&["/Prim/Child"]).includes(&p("/Prim{set=sel}Child")));
    }

    /// Only absolute prim paths may be named; a relative, property, or
    /// variant-selection path is reported rather than silently coerced.
    #[test]
    fn rejects_non_prim_paths() {
        for bad in ["A/B", "/A.attr", "/A{set=sel}", "/A{set=sel}B"] {
            assert!(
                PopulationMask::new([bad]).is_err(),
                "{bad} must be rejected from a mask"
            );
        }
    }

    /// `make_relative_to` re-roots the paths below the instance, drops those
    /// outside it, and collapses a fully-included instance to `all`.
    #[test]
    fn make_relative_to_cases() {
        let m = mask(&["/World/A/geom", "/World/B"]);
        assert_eq!(m.make_relative_to(&p("/World/A")).paths(), &[p("/geom")]);
        assert!(
            m.make_relative_to(&p("/World/B")).is_all(),
            "fully included keys as all"
        );
        assert!(
            m.make_relative_to(&p("/Other")).is_empty(),
            "an excluded instance keys as the empty mask"
        );
    }

    /// Equal masks built in different orders compare and hash equal, which is
    /// what lets `InstanceKey` hold one.
    #[test]
    fn equal_masks_hash_equal() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let hash = |m: &PopulationMask| {
            let mut hasher = DefaultHasher::new();
            m.hash(&mut hasher);
            hasher.finish()
        };
        let a = mask(&["/A", "/B/C"]);
        let b = mask(&["/B/C", "/A", "/A/Redundant"]);
        assert_eq!(a, b);
        assert_eq!(hash(&a), hash(&b));
    }
}
