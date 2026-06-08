//! Namespace element ordering helpers.
//!
//! [`apply_ordering`] mirrors C++ `SdfApplyListOrdering` /
//! `SdfListOp::_ReorderKeysHelper`: each entry named in `order` is moved —
//! together with the run of following entries that are not themselves named in
//! `order` — into the position the order list dictates. Entries that precede the
//! first ordered name keep their place at the front; an entry absent from
//! `order` otherwise travels with the ordered entry it follows.
//!
//! Example: `items = [a, b, c, d, e]`, `order = [c, a]` produces
//! `[c, d, e, a, b]` — `c` carries its trailing `d, e` and `a` carries `b`,
//! emitted in `order` sequence ahead of the (here empty) leading block.
//!
//! [`element_cmp`] is the normative element ordering of core spec §8.2 (C++
//! `TfDictionaryLessThan`).

use std::cmp::Ordering;
use std::iter::Peekable;
use std::str::Chars;

/// Reorders `items` in place according to `order`.
///
/// See the module-level documentation for the precise semantics. The function
/// is a no-op when `order` is empty, `items` is empty, or no entry in `items`
/// appears in `order`.
pub fn apply_ordering<T: Clone + PartialEq>(items: &mut Vec<T>, order: &[T]) {
    if order.is_empty() || items.is_empty() {
        return;
    }

    // Partition `items` into runs: each entry named in `order` starts a run
    // (with that entry first); each entry absent from `order` joins the run of
    // the nearest preceding ordered entry, or a leading block when none
    // precedes it.
    let mut leading: Vec<T> = Vec::new();
    let mut runs: Vec<Vec<T>> = Vec::new();
    for item in items.drain(..) {
        if order.contains(&item) {
            runs.push(vec![item]);
        } else if let Some(run) = runs.last_mut() {
            run.push(item);
        } else {
            leading.push(item);
        }
    }

    // Reassemble: the leading block, then each run in `order` sequence, keyed by
    // its first entry. Removing an emitted run means a name repeated in `order`
    // contributes only once.
    let mut result = leading;
    for name in order {
        if let Some(pos) = runs.iter().position(|run| run.first() == Some(name)) {
            result.extend(runs.remove(pos));
        }
    }
    // Append any runs not claimed by `order` — only possible when a name occurs
    // more than once in `items` (the usual unique-name lists leave none). This
    // keeps `apply_ordering` length-preserving regardless of duplicates.
    for run in runs {
        result.extend(run);
    }
    *items = result;
}

/// Compares two namespace element names by the normative element ordering of
/// core spec §8.2 (C++ `TfDictionaryLessThan`):
///
/// - `_` sorts before all ASCII letters and digits.
/// - ASCII digits sort before ASCII letters; a run of digits compares by numeric
///   value, ignoring leading zeros.
/// - ASCII letters compare case-insensitively.
/// - Every other character (ASCII punctuation and non-ASCII) sorts after ASCII
///   letters, by Unicode code point.
///
/// Callers apply this where the spec mandates element ordering — currently the
/// relocated-in prim children of the composition engine (spec §11.3.1). The base
/// prim-child fold (`primChildren` + `primOrder`) and property names deliberately
/// keep their authored order, so this is not a blanket sort of every composed
/// child.
///
/// The numeric value and case distinctions act as lowest-priority tiebreakers:
/// a run of equal numeric value compares equal so the walk continues, and the
/// remaining rules — a pure case difference orders uppercase first, and equal
/// number runs differing only in leading-zero count order the run with fewer
/// zeros first — decide only when the names are otherwise identical.
pub fn element_cmp(a: &str, b: &str) -> Ordering {
    let mut a = a.chars().peekable();
    let mut b = b.chars().peekable();
    // The earliest case / leading-zero distinction, applied only when the primary
    // walk compares equal end to end.
    let mut tiebreak = Ordering::Equal;
    loop {
        match (a.peek().copied(), b.peek().copied()) {
            // The shorter name (a prefix of the longer) sorts first; otherwise the
            // deferred case / leading-zero tiebreak decides.
            (None, None) => return tiebreak,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (Some(ca), Some(cb)) if ca.is_ascii_digit() && cb.is_ascii_digit() => {
                let (za, zb) = (consume_zeros(&mut a), consume_zeros(&mut b));
                match cmp_digit_runs(&mut a, &mut b) {
                    Ordering::Equal => {
                        if tiebreak == Ordering::Equal {
                            // Equal value: the run with fewer leading zeros sorts first.
                            tiebreak = za.cmp(&zb);
                        }
                    }
                    ord => return ord,
                }
            }
            (Some(ca), Some(cb)) => {
                let (ra, rb) = (category_rank(ca), category_rank(cb));
                if ra != rb {
                    return ra.cmp(&rb);
                }
                // Same category, at most one a digit (digit pairs handled above).
                let (fa, fb) = (ca.to_ascii_lowercase(), cb.to_ascii_lowercase());
                if fa != fb {
                    return (fa as u32).cmp(&(fb as u32));
                }
                if tiebreak == Ordering::Equal && ca != cb {
                    // Same folded letter, a pure case difference: uppercase first.
                    tiebreak = ca.is_ascii_lowercase().cmp(&cb.is_ascii_lowercase());
                }
                a.next();
                b.next();
            }
        }
    }
}

/// The category rank of a single character for [`element_cmp`]: `_` before
/// digits before ASCII letters before any other character (ASCII punctuation and
/// non-ASCII, ordered among themselves by code point).
fn category_rank(c: char) -> u8 {
    if c == '_' {
        0
    } else if c.is_ascii_digit() {
        1
    } else if c.is_ascii_alphabetic() {
        2
    } else {
        3
    }
}

/// Consumes a leading run of `'0'` from a digit run, returning its length.
fn consume_zeros(it: &mut Peekable<Chars>) -> usize {
    let mut zeros = 0;
    while it.next_if_eq(&'0').is_some() {
        zeros += 1;
    }
    zeros
}

/// Compares the significant (leading-zero-stripped) digits of the two digit runs
/// at the front of `a` and `b`, consuming them. A longer run of significant
/// digits is the larger number; equal lengths compare digit by digit.
fn cmp_digit_runs(a: &mut Peekable<Chars>, b: &mut Peekable<Chars>) -> Ordering {
    let mut result = Ordering::Equal;
    loop {
        let da = a.next_if(char::is_ascii_digit);
        let db = b.next_if(char::is_ascii_digit);
        match (da, db) {
            (Some(x), Some(y)) if result == Ordering::Equal && x != y => result = x.cmp(&y),
            (Some(_), Some(_)) => {}
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
            (None, None) => return result,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(items: &[&str]) -> Vec<String> {
        items.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn ordered_names_carry_trailing_run() {
        let mut children = s(&["a", "b", "c", "d", "e"]);
        apply_ordering(&mut children, &s(&["c", "a"]));
        assert_eq!(children, s(&["c", "d", "e", "a", "b"]));
    }

    #[test]
    fn full_reverse_works() {
        let mut children = s(&["a", "b", "c"]);
        apply_ordering(&mut children, &s(&["c", "b", "a"]));
        assert_eq!(children, s(&["c", "b", "a"]));
    }

    #[test]
    fn duplicate_items_are_preserved() {
        // A name repeated in `items` keeps every occurrence (length-preserving),
        // even though the order list claims it once.
        let mut items = s(&["a", "b", "a", "c"]);
        apply_ordering(&mut items, &s(&["a"]));
        assert_eq!(items.len(), 4);
        assert_eq!(items, s(&["a", "b", "a", "c"]));
    }

    #[test]
    fn unknown_names_in_order_are_ignored() {
        let mut children = s(&["a", "b", "c"]);
        apply_ordering(&mut children, &s(&["b", "missing", "a"]));
        assert_eq!(children, s(&["b", "c", "a"]));
    }

    #[test]
    fn leading_block_stays_in_front() {
        let mut children = s(&["p", "q", "b", "a"]);
        apply_ordering(&mut children, &s(&["a", "b"]));
        assert_eq!(children, s(&["p", "q", "a", "b"]));
    }

    #[test]
    fn empty_order_is_noop() {
        let mut children = s(&["a", "b", "c"]);
        apply_ordering(&mut children, &[]);
        assert_eq!(children, s(&["a", "b", "c"]));
    }

    #[test]
    fn no_overlap_is_noop() {
        let mut children = s(&["a", "b", "c"]);
        apply_ordering(&mut children, &s(&["x", "y", "z"]));
        assert_eq!(children, s(&["a", "b", "c"]));
    }

    #[test]
    fn empty_children_is_noop() {
        let mut children: Vec<String> = Vec::new();
        apply_ordering(&mut children, &s(&["a", "b"]));
        assert!(children.is_empty());
    }

    /// The worked example from core spec §8.2, sorted by [`element_cmp`]. `℗`
    /// (U+2117) stands for the spec's non-ASCII example character.
    ///
    /// The expected order follows the spec's stated *rules* (numbers before
    /// letters, applied consistently — the order C++ `TfDictionaryLessThan`
    /// produces), which places the pure-alphabetic `Foobar`/`foobar` after the
    /// `foo`+digits group. The spec's *printed* example lists those two before the
    /// group, which is internally inconsistent: it would require a letter to sort
    /// before a digit (`"b" < "0"`), yet the same example orders `a0` before `ab`,
    /// which requires the opposite (`"0" < "b"`). No total order satisfies both, so
    /// we follow the consistent rule.
    #[test]
    fn element_cmp_spec_example() {
        let mut names = s(&[
            "foobar",
            "Foobar",
            "_foobar",
            "foo_bar",
            "foo001bar001abc",
            "foo001bar002abc",
            "foo0001bar0002xyz",
            "foo00001bar",
            "a0",
            "a℗",
            "ab",
        ]);
        names.sort_by(|x, y| element_cmp(x, y));
        assert_eq!(
            names,
            s(&[
                "_foobar",
                "a0",
                "ab",
                "a℗",
                "foo_bar",
                "foo00001bar",
                "foo001bar001abc",
                "foo001bar002abc",
                "foo0001bar0002xyz",
                "Foobar",
                "foobar",
            ])
        );
    }

    #[test]
    fn element_cmp_tiebreaks() {
        // Pure case difference: uppercase before lowercase.
        assert_eq!(element_cmp("Bar", "bar"), Ordering::Less);
        // Equal numeric value, fewer leading zeros first.
        assert_eq!(element_cmp("a1", "a01"), Ordering::Less);
        // Numeric value dominates digit count.
        assert_eq!(element_cmp("a9", "a10"), Ordering::Less);
        // Identical names compare equal.
        assert_eq!(element_cmp("abc", "abc"), Ordering::Equal);
    }
}
