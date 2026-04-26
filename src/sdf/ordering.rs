//! Children list reordering helper.
//!
//! Mirrors C++ `Sdf_ApplyOrdering`: names listed in `order` are reshuffled
//! into order-list sequence at the slots they currently occupy in `children`.
//! Names not in the order list keep their positions; names in the order list
//! that are not present in `children` are silently skipped.
//!
//! Example: `children = [a, b, c, d, e]`, `order = [c, a]` produces
//! `[c, b, a, d, e]`.

/// Reorder `children` in place according to `order`.
///
/// See the module-level documentation for the precise semantics. The function
/// is a no-op when either input is empty or when no name in `children`
/// appears in `order`.
pub fn apply_ordering(children: &mut [String], order: &[String]) {
    if order.is_empty() || children.is_empty() {
        return;
    }

    let slots: Vec<usize> = children
        .iter()
        .enumerate()
        .filter_map(|(i, name)| order.contains(name).then_some(i))
        .collect();
    if slots.is_empty() {
        return;
    }

    let projected: Vec<&String> = order.iter().filter(|n| children.contains(*n)).collect();

    for (slot, name) in slots.iter().zip(projected.iter()) {
        children[*slot].clone_from(*name);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(items: &[&str]) -> Vec<String> {
        items.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn reorders_named_subset_in_place() {
        let mut children = s(&["a", "b", "c", "d", "e"]);
        apply_ordering(&mut children, &s(&["c", "a"]));
        assert_eq!(children, s(&["c", "b", "a", "d", "e"]));
    }

    #[test]
    fn full_reverse_works() {
        let mut children = s(&["a", "b", "c"]);
        apply_ordering(&mut children, &s(&["c", "b", "a"]));
        assert_eq!(children, s(&["c", "b", "a"]));
    }

    #[test]
    fn unknown_names_in_order_are_ignored() {
        let mut children = s(&["a", "b", "c"]);
        apply_ordering(&mut children, &s(&["b", "missing", "a"]));
        assert_eq!(children, s(&["b", "a", "c"]));
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
