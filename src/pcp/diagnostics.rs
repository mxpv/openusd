//! The collection every recoverable composition diagnostic is reported into.
//!
//! One insertion invariant, shared by every owner: a diagnostic structurally
//! equal to one already held is dropped, and the survivors keep first-seen
//! order. Which owner *stores* a bucket still varies — a bucket disappears
//! with the thing it describes, and that is what retires it — but how a
//! diagnostic enters one does not.

use std::collections::HashSet;
use std::{slice, vec};

use super::CompositionDiagnostic;

/// A set of [`CompositionDiagnostic`]s, unique by structural equality and
/// ordered by first appearance.
///
/// The same failing opinion is evaluated more than once in the ordinary course
/// of composition — a variant-selection search re-runs per declaring node and
/// on task retry, a value-time read re-evaluates on every read, and a
/// repeatable query re-derives whatever its walk produces — so a repeat says
/// nothing new. Uniqueness is the collection's job rather than each producer's,
/// which is what keeps the answer independent of which producer ran.
///
/// A caller that must transform its diagnostics rebuilds through the
/// collection (`into_iter().map(..).collect()`), which re-establishes
/// uniqueness against the new values — a transformation can make two entries
/// equal, and the collection is what decides that.
#[derive(Debug, Default, Clone)]
pub(crate) struct Diagnostics {
    /// The diagnostics in first-seen order — what every reader sees.
    entries: Vec<CompositionDiagnostic>,
    /// Membership index over [`entries`](Self::entries), built only once a
    /// linear scan stops being the cheaper answer.
    ///
    /// Boxed and absent by default because most of these are tiny and there are
    /// very many of them — one pair per cached prim, one per memoized target —
    /// so the empty case costs a pointer and never allocates. A broken stage is
    /// the other extreme: one failure per affected prim, thousands of entries
    /// sharing their leading fields, where scanning per insertion would make
    /// filling the collection quadratic in whole-string comparisons.
    ///
    /// Boxed deliberately: the point of the field is that an absent index costs
    /// one pointer, which an inline `Option<HashSet<_>>` would not.
    #[allow(clippy::box_collection)]
    seen: Option<Box<HashSet<CompositionDiagnostic>>>,
}

impl Diagnostics {
    /// The length at which the membership index starts paying for itself.
    const INDEX_AT: usize = 32;

    /// Reports `diagnostic` unless an equal one is already held.
    pub(crate) fn report(&mut self, diagnostic: CompositionDiagnostic) {
        if self.admit(&diagnostic) {
            self.entries.push(diagnostic);
        }
    }

    /// Whether `diagnostic` is new here, recording it in the membership index
    /// and building that index once the collection has outgrown a linear scan.
    fn admit(&mut self, diagnostic: &CompositionDiagnostic) -> bool {
        if let Some(seen) = &mut self.seen {
            return seen.insert(diagnostic.clone());
        }
        if self.entries.contains(diagnostic) {
            return false;
        }
        if self.entries.len() >= Self::INDEX_AT {
            let mut seen: HashSet<CompositionDiagnostic> = self.entries.iter().cloned().collect();
            seen.insert(diagnostic.clone());
            self.seen = Some(Box::new(seen));
        }
        true
    }

    /// Keeps only the diagnostics satisfying `predicate`.
    pub(crate) fn retain(&mut self, predicate: impl FnMut(&CompositionDiagnostic) -> bool) {
        self.entries.retain(predicate);
        // The index names entries that may be gone; the next insertion past the
        // threshold rebuilds it from what survived.
        self.seen = None;
    }

    /// Discards everything held.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.seen = None;
    }

    /// Whether nothing is held.
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Borrows the diagnostics in first-seen order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = &CompositionDiagnostic> {
        self.entries.iter()
    }

    /// Takes the diagnostics as a plain vector, for a caller handing them out.
    pub(crate) fn into_vec(self) -> Vec<CompositionDiagnostic> {
        self.entries
    }
}

#[cfg(test)]
impl Diagnostics {
    /// How many distinct diagnostics are held.
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }
}

impl Extend<CompositionDiagnostic> for Diagnostics {
    fn extend<T: IntoIterator<Item = CompositionDiagnostic>>(&mut self, diagnostics: T) {
        for diagnostic in diagnostics {
            self.report(diagnostic);
        }
    }
}

impl FromIterator<CompositionDiagnostic> for Diagnostics {
    fn from_iter<T: IntoIterator<Item = CompositionDiagnostic>>(diagnostics: T) -> Self {
        let mut held = Self::default();
        held.extend(diagnostics);
        held
    }
}

impl IntoIterator for Diagnostics {
    type Item = CompositionDiagnostic;
    type IntoIter = vec::IntoIter<CompositionDiagnostic>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

impl<'a> IntoIterator for &'a Diagnostics {
    type Item = &'a CompositionDiagnostic;
    type IntoIter = slice::Iter<'a, CompositionDiagnostic>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::pcp::ArcType;
    use crate::sdf;

    fn unresolved(layer: &str) -> CompositionDiagnostic {
        CompositionDiagnostic::UnresolvedLayer {
            asset_path: layer.to_string(),
            arc: ArcType::Reference,
            introduced_by: "root.usd".to_string(),
            site_path: sdf::path("/Prim").expect("valid path"),
        }
    }

    /// A structurally equal repeat says nothing new, so only the first is kept.
    #[test]
    fn report_deduplicates() {
        let mut held = Diagnostics::default();
        held.report(unresolved("a.usd"));
        held.report(unresolved("a.usd"));
        assert_eq!(held.len(), 1);
    }

    /// A batch keeps first-seen order, and a later repeat does not move the
    /// entry it duplicates.
    #[test]
    fn extend_preserves_order() {
        let mut held = Diagnostics::default();
        held.extend([unresolved("a.usd"), unresolved("b.usd"), unresolved("a.usd")]);
        let order: Vec<&CompositionDiagnostic> = held.iter().collect();
        assert_eq!(order, vec![&unresolved("a.usd"), &unresolved("b.usd")]);
    }

    /// Uniqueness holds identically on both sides of the point where the
    /// membership index is built, so a caller never has to know which side it
    /// is on.
    #[test]
    fn dedups_past_index_threshold() {
        let many: Vec<CompositionDiagnostic> = (0..Diagnostics::INDEX_AT * 2)
            .map(|i| unresolved(&format!("{i}.usd")))
            .collect();
        let mut held: Diagnostics = many.iter().cloned().collect();
        assert_eq!(held.len(), many.len());
        held.extend(many.iter().cloned());
        assert_eq!(held.len(), many.len(), "every repeat is dropped, indexed or not");
        assert_eq!(held.iter().next(), Some(&many[0]), "first-seen order survives");
    }

    /// Dropping a diagnostic forgets it: a bucket that retires an entry and
    /// then rediscovers the same failure must report it again.
    #[test]
    fn retain_forgets_dropped() {
        let mut held: Diagnostics = [unresolved("a.usd"), unresolved("b.usd")].into_iter().collect();
        held.retain(|diagnostic| diagnostic != &unresolved("a.usd"));
        held.report(unresolved("a.usd"));
        assert_eq!(held.len(), 2);
        assert_eq!(
            held.iter().collect::<Vec<_>>(),
            vec![&unresolved("b.usd"), &unresolved("a.usd")],
            "the re-report is a first appearance"
        );
    }

    /// Rebuilding through the collection re-applies uniqueness to the new
    /// values, so a transformation that makes two entries equal collapses
    /// them.
    #[test]
    fn rebuild_dedups_transformed() {
        let held: Diagnostics = [unresolved("a.usd"), unresolved("b.usd")].into_iter().collect();
        assert_eq!(held.len(), 2);
        let stamped: Diagnostics = held
            .into_iter()
            .map(|mut diagnostic| {
                if let CompositionDiagnostic::UnresolvedLayer { asset_path, .. } = &mut diagnostic {
                    *asset_path = "same.usd".to_string();
                }
                diagnostic
            })
            .collect();
        assert_eq!(stamped.len(), 1, "the transformation made them equal");
    }
}
