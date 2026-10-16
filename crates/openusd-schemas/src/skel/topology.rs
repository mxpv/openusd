//! Joint topology — the static parent/child structure of a skeleton.
//!
//! Mirrors Pixar's `UsdSkelTopology`. Holds one `parent` index per
//! joint, with a negative index denoting a root. Built either from a slice of
//! path-encoded joint names (Pixar's standard `joints` token array
//! format — `"Shoulder/Elbow"` ⇒ parent is `"Shoulder"`) or from a
//! pre-computed parent-index array.

use std::collections::HashMap;

/// The parent index [`Topology::from_joint_paths`] gives a root joint. Any
/// negative index marks a root.
pub const NO_PARENT: i32 = -1;

/// Joint topology — parent indices, validation, root tests.
///
/// Indices line up 1:1 with the originating `joints` token array.
/// `parents[i]` is either the index of joint `i`'s parent or negative for a
/// root joint.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Topology {
    parents: Vec<i32>,
}

impl Topology {
    /// Empty topology — no joints.
    pub fn new() -> Self {
        Self { parents: Vec::new() }
    }

    /// Build a topology from a slice of joint path tokens — Pixar's
    /// `joints` token array convention. A joint's parent is its nearest
    /// ancestor path in the array (`"A"` for `"A/B/C"` when `"A/B"` is not
    /// listed), and a joint with no listed ancestor is a root (C++
    /// `UsdSkelTopology(TfSpan<const TfToken>)`).
    ///
    /// Order is preserved: `parents[i]` corresponds to `paths[i]`.
    pub fn from_joint_paths(paths: &[String]) -> Self {
        let by_path = joint_index_map(paths);
        let parents = paths
            .iter()
            .map(|path| {
                let mut ancestor = path.as_str();
                while let Some((parent, _)) = ancestor.rsplit_once('/') {
                    if let Some(&index) = by_path.get(parent) {
                        return index as i32;
                    }
                    ancestor = parent;
                }
                NO_PARENT
            })
            .collect();
        Self { parents }
    }

    /// Build a topology directly from a parent-index array — same
    /// semantics as Pixar's `UsdSkelTopology(VtIntArray)` constructor.
    pub fn from_parents(parents: Vec<i32>) -> Self {
        Self { parents }
    }

    /// Borrow the parent-index array.
    pub fn parents(&self) -> &[i32] {
        &self.parents
    }

    /// Number of joints in this topology.
    pub fn joint_count(&self) -> usize {
        self.parents.len()
    }

    /// Index of joint `i`'s parent, or `None` when `i` is a root or out of
    /// range — callers that need to distinguish should range-check
    /// separately.
    pub fn parent(&self, i: usize) -> Option<usize> {
        self.parents.get(i).and_then(|&parent| usize::try_from(parent).ok())
    }

    /// True when joint `i` has no parent.
    pub fn is_root(&self, i: usize) -> bool {
        self.parent(i).is_none()
    }

    /// Validate that every non-negative parent index refers to a *prior*
    /// joint (parent-before-child ordering — the canonical UsdSkel
    /// invariant, which also rules out cycles). Returns the offending joint
    /// index on failure (C++ `UsdSkelTopology::Validate`).
    pub fn validate(&self) -> Result<(), TopologyError> {
        for (joint, &parent) in self.parents.iter().enumerate() {
            let Ok(index) = usize::try_from(parent) else {
                continue;
            };
            if index == joint {
                return Err(TopologyError::SelfParent { joint });
            }
            if index > joint {
                return Err(TopologyError::ParentNotBeforeChild { joint, parent });
            }
        }
        Ok(())
    }
}

/// Build a `{joint_path → index}` lookup over a `joints` token array.
pub(super) fn joint_index_map(joints: &[String]) -> HashMap<&str, usize> {
    joints.iter().enumerate().map(|(i, p)| (p.as_str(), i)).collect()
}

/// Reasons [`Topology::validate`] can fail.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TopologyError {
    /// A joint names itself as its parent.
    #[error("joint {joint} has itself as its parent")]
    SelfParent { joint: usize },
    /// UsdSkel requires parents to come before children in the
    /// `joints` array. This entry violates that ordering.
    #[error("joint {joint}: parent index {parent} must be less than the joint's own index")]
    ParentNotBeforeChild { joint: usize, parent: i32 },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn paths(items: &[&str]) -> Vec<String> {
        items.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn derives_parents_from_path_encoding() {
        let t = Topology::from_joint_paths(&paths(&["Root", "Root/Hip", "Root/Hip/Knee", "Root/Hip/Other"]));
        assert_eq!(t.parents(), &[NO_PARENT, 0, 1, 1]);
        assert!(t.is_root(0));
        assert!(!t.is_root(1));
        assert_eq!(t.joint_count(), 4);
        t.validate().unwrap();
    }

    #[test]
    fn joints_with_missing_prefix_become_roots() {
        // "Foo/Bar" has no preceding "Foo" entry — it's still a valid
        // joint but with no parent in the topology.
        let t = Topology::from_joint_paths(&paths(&["A", "Foo/Bar"]));
        assert_eq!(t.parents(), &[NO_PARENT, NO_PARENT]);
    }

    #[test]
    fn validate_rejects_forward_parent_reference() {
        // parents[0] = 1 → joint 0 says its parent is joint 1, which
        // comes after it. Spec requires parent < child.
        let t = Topology::from_parents(vec![1, NO_PARENT]);
        assert!(matches!(
            t.validate(),
            Err(TopologyError::ParentNotBeforeChild { joint: 0, parent: 1 })
        ));
    }

    #[test]
    fn validate_rejects_out_of_range_parent() {
        let t = Topology::from_parents(vec![NO_PARENT, 7]);
        assert!(matches!(
            t.validate(),
            Err(TopologyError::ParentNotBeforeChild { joint: 1, parent: 7 })
        ));
    }

    #[test]
    fn validate_rejects_self_parent() {
        let t = Topology::from_parents(vec![NO_PARENT, 1]);
        assert_eq!(t.validate(), Err(TopologyError::SelfParent { joint: 1 }));
    }

    #[test]
    fn negative_parents_are_roots() {
        let t = Topology::from_parents(vec![-2, 0]);
        t.validate().unwrap();
        assert!(t.is_root(0));
    }

    #[test]
    fn parent_is_nearest_listed_ancestor() {
        let t = Topology::from_joint_paths(&paths(&["A", "A/B/C", "A/B/C/D"]));
        assert_eq!(t.parents(), &[NO_PARENT, 0, 1]);
    }
}
