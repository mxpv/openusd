//! Namespace-aware map keyed by [`Path`].
//!
//! Parallels C++ `SdfPathTable` (`Sdf_PathTable`): a hash map whose entries also
//! carry intrusive parent/child links forming the namespace tree. This gives
//! plain O(1) keyed access *plus* exact subtree operations — [`subtree`] for an
//! iterator over a path and all its namespace descendants (C++
//! `FindSubtreeRange`) and [`remove_subtree`] to erase one — without the O(n)
//! `has_prefix` scan a flat [`HashMap`] would need.
//!
//! Subtree extraction is why a sorted map does not suffice: lexicographic [`Path`]
//! order is not subtree-contiguous, because a sibling sharing the string prefix
//! (`/Foobar`) sorts between descendants `/Foo/Bar` and `/Foo{v=s}` (the variant
//! opener `{` sorts after letters). The explicit child links sidestep this.
//!
//! [`subtree`]: PathTable::subtree
//! [`remove_subtree`]: PathTable::remove_subtree

use std::collections::{BTreeSet, HashMap};

use crate::sdf::Path;

/// A map from [`Path`] to `V` that also tracks the namespace parent/child
/// hierarchy, supporting efficient subtree queries and erasure.
///
/// Ancestors of an inserted path are materialized as value-less intermediate
/// nodes so a [`subtree`](Self::subtree) query can navigate to a prefix that was
/// never itself inserted; they are pruned automatically once they have no
/// value and no children. [`len`](Self::len) and iteration count only
/// value-bearing entries.
#[derive(Debug, Clone)]
pub struct PathTable<V> {
    nodes: HashMap<Path, Node<V>>,
    len: usize,
}

#[derive(Debug, Clone)]
struct Node<V> {
    /// The mapped value, or `None` for an intermediate ancestor-only node.
    value: Option<V>,
    /// Direct namespace children. `BTreeSet` keeps subtree iteration
    /// deterministic regardless of insertion order.
    children: BTreeSet<Path>,
}

impl<V> Default for PathTable<V> {
    fn default() -> Self {
        Self {
            nodes: HashMap::new(),
            len: 0,
        }
    }
}

impl<V> PathTable<V> {
    /// Creates an empty table.
    pub fn new() -> Self {
        Self::default()
    }

    /// Number of value-bearing entries (intermediate nodes are not counted).
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the table holds no value-bearing entries.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes all entries.
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.len = 0;
    }

    /// Returns `true` if `path` holds a value.
    pub fn contains_key(&self, path: &Path) -> bool {
        self.nodes.get(path).is_some_and(|n| n.value.is_some())
    }

    /// Borrows the value at `path`, if any.
    pub fn get(&self, path: &Path) -> Option<&V> {
        self.nodes.get(path).and_then(|n| n.value.as_ref())
    }

    /// Mutably borrows the value at `path`, if any.
    pub fn get_mut(&mut self, path: &Path) -> Option<&mut V> {
        self.nodes.get_mut(path).and_then(|n| n.value.as_mut())
    }

    /// Inserts `value` at `path`, returning the previous value if one was set.
    ///
    /// Creates and links any missing ancestor nodes up to the first already
    /// linked one, so the namespace tree stays connected to the root.
    pub fn insert(&mut self, path: Path, value: V) -> Option<V> {
        if let Some(node) = self.nodes.get_mut(&path) {
            let prev = node.value.replace(value);
            if prev.is_none() {
                self.len += 1;
            }
            return prev;
        }
        self.nodes.insert(
            path.clone(),
            Node {
                value: Some(value),
                children: BTreeSet::new(),
            },
        );
        self.len += 1;
        self.link_ancestors(path);
        None
    }

    /// Returns a mutable reference to the value at `path`, inserting `V::default()`
    /// first if absent. Mirrors `HashMap::entry(..).or_default()`.
    pub fn get_or_insert_default(&mut self, path: &Path) -> &mut V
    where
        V: Default,
    {
        if !self.contains_key(path) {
            self.insert(path.clone(), V::default());
        }
        self.get_mut(path).expect("just inserted")
    }

    /// Removes and returns the value at `path`, pruning the node and any
    /// now-empty intermediate ancestors.
    pub fn remove(&mut self, path: &Path) -> Option<V> {
        let node = self.nodes.get_mut(path)?;
        let value = node.value.take()?;
        self.len -= 1;
        // Keep the node as an intermediate if it still has children; otherwise
        // drop it and prune the ancestor chain.
        if node.children.is_empty() {
            self.nodes.remove(path);
            self.prune_ancestors(path);
        }
        Some(value)
    }

    /// Iterates `(path, &value)` for every value-bearing entry, in unspecified
    /// order.
    pub fn iter(&self) -> impl Iterator<Item = (&Path, &V)> {
        self.nodes.iter().filter_map(|(p, n)| n.value.as_ref().map(|v| (p, v)))
    }

    /// Iterates `(path, &value)` for `prefix` and all of its namespace
    /// descendants (C++ `FindSubtreeRange`), depth-first in deterministic order.
    ///
    /// Yields nothing if `prefix` names no node — value-bearing or intermediate.
    pub fn subtree<'a>(&'a self, prefix: &Path) -> impl Iterator<Item = (&'a Path, &'a V)> {
        let mut out: Vec<(&'a Path, &'a V)> = Vec::new();
        self.collect_subtree(prefix, &mut out);
        out.into_iter()
    }

    /// Removes `prefix` and all of its namespace descendants, returning the
    /// removed value-bearing `(path, value)` pairs. Prunes the ancestor chain
    /// above `prefix`.
    pub fn remove_subtree(&mut self, prefix: &Path) -> Vec<(Path, V)> {
        if !self.nodes.contains_key(prefix) {
            return Vec::new();
        }
        let mut removed = Vec::new();
        self.remove_subtree_into(prefix, &mut removed);
        self.prune_ancestors(prefix);
        removed
    }

    /// Removes `root` and its descendants during a single depth-first walk,
    /// collecting the value-bearing `(path, value)` pairs into `out`.
    fn remove_subtree_into(&mut self, root: &Path, out: &mut Vec<(Path, V)>) {
        // Take the node out first; owning it lets the recursion borrow its
        // child set while the table is mutated, and hands back the owned key
        // so a value-bearing node returns its path without a clone.
        let Some((path, node)) = self.nodes.remove_entry(root) else {
            return;
        };
        for child in &node.children {
            self.remove_subtree_into(child, out);
        }
        if let Some(value) = node.value {
            self.len -= 1;
            out.push((path, value));
        }
    }

    /// Links `path` into the namespace tree by recording it as a child of its
    /// parent, creating intermediate parent nodes as needed and stopping at the
    /// first ancestor that is already present.
    fn link_ancestors(&mut self, path: Path) {
        let mut child = path;
        while let Some(parent) = child.parent() {
            match self.nodes.get_mut(&parent) {
                Some(node) => {
                    node.children.insert(child);
                    // The parent already existed, so its own ancestor links are
                    // already in place.
                    return;
                }
                None => {
                    let mut children = BTreeSet::new();
                    children.insert(child);
                    self.nodes.insert(parent.clone(), Node { value: None, children });
                    child = parent;
                }
            }
        }
    }

    /// Drops value-less, childless ancestors of `path` from its parent upward.
    fn prune_ancestors(&mut self, path: &Path) {
        let mut child = path.clone();
        while let Some(parent) = child.parent() {
            let Some(node) = self.nodes.get_mut(&parent) else {
                return;
            };
            node.children.remove(&child);
            if node.value.is_some() || !node.children.is_empty() {
                return;
            }
            self.nodes.remove(&parent);
            child = parent;
        }
    }

    /// Appends `(path, &value)` for `root` and its descendants, depth-first.
    ///
    /// Path references are sourced from the map's own keys so they carry the
    /// table's lifetime rather than the caller's `root` borrow.
    fn collect_subtree<'a>(&'a self, root: &Path, out: &mut Vec<(&'a Path, &'a V)>) {
        let Some((path, node)) = self.nodes.get_key_value(root) else {
            return;
        };
        if let Some(value) = &node.value {
            out.push((path, value));
        }
        for child in &node.children {
            self.collect_subtree(child, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::path;

    fn p(s: &str) -> Path {
        path(s).expect("valid path")
    }

    #[test]
    fn insert_get_remove() {
        let mut t: PathTable<i32> = PathTable::new();
        assert!(t.is_empty());
        assert_eq!(t.insert(p("/A/B"), 1), None);
        assert_eq!(t.insert(p("/A/B"), 2), Some(1));
        assert_eq!(t.get(&p("/A/B")), Some(&2));
        assert!(t.contains_key(&p("/A/B")));
        assert_eq!(t.len(), 1);
        assert_eq!(t.remove(&p("/A/B")), Some(2));
        assert_eq!(t.remove(&p("/A/B")), None);
        assert!(t.is_empty());
    }

    #[test]
    fn get_mut_edits_in_place() {
        let mut t: PathTable<Vec<i32>> = PathTable::new();
        t.get_or_insert_default(&p("/A")).push(7);
        t.get_or_insert_default(&p("/A")).push(8);
        assert_eq!(t.get(&p("/A")), Some(&vec![7, 8]));
        assert_eq!(t.len(), 1);
    }

    #[test]
    fn intermediate_nodes_uncounted() {
        // Inserting a deep path materializes value-less ancestors that are not
        // counted and not returned as values.
        let mut t: PathTable<i32> = PathTable::new();
        t.insert(p("/A/B/C"), 1);
        assert_eq!(t.len(), 1);
        assert_eq!(t.get(&p("/A")), None);
        assert_eq!(t.get(&p("/A/B")), None);
        assert_eq!(t.iter().count(), 1);
    }

    #[test]
    fn remove_prunes_ancestors() {
        // Removing the only value-bearing leaf drops the intermediate chain.
        let mut t: PathTable<i32> = PathTable::new();
        t.insert(p("/A/B/C"), 1);
        t.remove(&p("/A/B/C"));
        assert!(t.nodes.is_empty(), "intermediate ancestors should be pruned");
    }

    #[test]
    fn remove_keeps_node_with_children() {
        // Removing a value whose node still has descendants keeps it as an
        // intermediate so the subtree stays reachable.
        let mut t: PathTable<i32> = PathTable::new();
        t.insert(p("/A"), 1);
        t.insert(p("/A/B"), 2);
        assert_eq!(t.remove(&p("/A")), Some(1));
        assert_eq!(t.get(&p("/A/B")), Some(&2));
        assert_eq!(t.len(), 1);
    }

    #[test]
    fn subtree_excludes_sibling() {
        // The variant/sibling case a sorted-range scan gets wrong: `/Foobar`
        // shares the string prefix `/Foo` but is not a namespace descendant,
        // while the variant child `/Foo{v=s}` is.
        let mut t: PathTable<i32> = PathTable::new();
        for (path, n) in [("/Foo", 0), ("/Foo.attr", 1), ("/Foo/Bar", 2), ("/Foobar", 3)] {
            t.insert(p(path), n);
        }
        t.insert(p("/Foo{v=s}"), 4);

        let mut got: Vec<&str> = t.subtree(&p("/Foo")).map(|(path, _)| path.as_str()).collect();
        got.sort();
        assert_eq!(got, vec!["/Foo", "/Foo.attr", "/Foo/Bar", "/Foo{v=s}"]);
    }

    #[test]
    fn subtree_from_intermediate_prefix() {
        // A prefix that is itself only an intermediate node still yields its
        // value-bearing descendants.
        let mut t: PathTable<i32> = PathTable::new();
        t.insert(p("/A/B/C"), 1);
        t.insert(p("/A/B/D"), 2);
        let mut got: Vec<&str> = t.subtree(&p("/A/B")).map(|(path, _)| path.as_str()).collect();
        got.sort();
        assert_eq!(got, vec!["/A/B/C", "/A/B/D"]);
    }

    #[test]
    fn subtree_unknown_prefix_empty() {
        let mut t: PathTable<i32> = PathTable::new();
        t.insert(p("/A/B"), 1);
        assert_eq!(t.subtree(&p("/X")).count(), 0);
        assert_eq!(t.subtree(&p("/A/B/C")).count(), 0);
    }

    #[test]
    fn remove_subtree_prunes() {
        let mut t: PathTable<i32> = PathTable::new();
        t.insert(p("/A/B"), 1);
        t.insert(p("/A/B/C"), 2);
        t.insert(p("/A/Sibling"), 3);

        let subtree = t.remove_subtree(&p("/A/B"));
        let mut removed: Vec<&str> = subtree.iter().map(|(p, _)| p.as_str()).collect();
        removed.sort();
        assert_eq!(removed, vec!["/A/B", "/A/B/C"]);
        // The sibling and its ancestor survive; the removed subtree is gone.
        assert_eq!(t.get(&p("/A/Sibling")), Some(&3));
        assert!(!t.contains_key(&p("/A/B")));
        assert!(!t.contains_key(&p("/A/B/C")));
        assert_eq!(t.len(), 1);
    }

    #[test]
    fn remove_subtree_at_root() {
        let mut t: PathTable<i32> = PathTable::new();
        t.insert(p("/A"), 1);
        t.insert(p("/B/C"), 2);
        let removed = t.remove_subtree(&Path::abs_root());
        assert_eq!(removed.len(), 2);
        assert!(t.is_empty());
        assert_eq!(t.nodes.len(), 0);
    }
}
