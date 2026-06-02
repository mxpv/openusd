//! List reordering helper.
//!
//! Mirrors C++ `SdfApplyListOrdering` / `SdfListOp::_ReorderKeysHelper`: each
//! entry named in `order` is moved — together with the run of following entries
//! that are not themselves named in `order` — into the position the order list
//! dictates. Entries that precede the first ordered name keep their place at the
//! front; an entry absent from `order` otherwise travels with the ordered entry
//! it follows.
//!
//! Example: `items = [a, b, c, d, e]`, `order = [c, a]` produces
//! `[c, d, e, a, b]` — `c` carries its trailing `d, e` and `a` carries `b`,
//! emitted in `order` sequence ahead of the (here empty) leading block.

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
}
