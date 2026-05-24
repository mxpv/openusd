//! Joint topology — the static parent/child structure of a skeleton.
//!
//! Mirrors Pixar's `UsdSkelTopology`. Holds one `parent` index per
//! joint, with `-1` denoting a root. Built either from a slice of
//! path-encoded joint names (Pixar's standard `joints` token array
//! format — `"Shoulder/Elbow"` ⇒ parent is `"Shoulder"`) or from a
//! pre-computed parent-index array.

/// Sentinel value meaning "this joint has no parent" in
/// [`Topology::parents`] / [`Topology::parent`].
pub const NO_PARENT: i32 = -1;

/// Build a `{joint_path → index}` lookup over a `joints` token array.
/// Shared between [`Topology::from_joint_paths`] and the read-side
/// helpers in [`super::types`] so the same hashmap construction isn't
/// duplicated.
pub(super) fn joint_index_map(joints: &[String]) -> std::collections::HashMap<&str, usize> {
    joints.iter().enumerate().map(|(i, p)| (p.as_str(), i)).collect()
}

/// Joint topology — parent indices, validation, root tests.
///
/// Indices line up 1:1 with the originating `joints` token array.
/// `parents[i]` is either the index of joint `i`'s parent or
/// [`NO_PARENT`] for root joints.
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
    /// `joints` token array convention. The path encoding
    /// (`"A/B"` ⇒ parent of `"A/B"` is `"A"`) implies the parent
    /// link. Joints without a `/` (or whose prefix isn't present in
    /// the array) are roots.
    ///
    /// Order is preserved: `parents[i]` corresponds to `paths[i]`.
    pub fn from_joint_paths(paths: &[String]) -> Self {
        let by_path = joint_index_map(paths);
        let parents = paths
            .iter()
            .map(|p| {
                p.rsplit_once('/')
                    .and_then(|(parent, _)| by_path.get(parent).copied().map(|i| i as i32))
                    .unwrap_or(NO_PARENT)
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
    pub fn num_joints(&self) -> usize {
        self.parents.len()
    }

    /// Parent of joint `i`, or [`NO_PARENT`] when `i` is a root.
    /// Returns [`NO_PARENT`] if `i` is out of range — callers that
    /// need to distinguish should range-check separately.
    pub fn parent(&self, i: usize) -> i32 {
        self.parents.get(i).copied().unwrap_or(NO_PARENT)
    }

    /// True when joint `i` has no parent.
    pub fn is_root(&self, i: usize) -> bool {
        self.parent(i) == NO_PARENT
    }

    /// Validate that every parent index either equals [`NO_PARENT`]
    /// or refers to a *prior* joint (parent-before-child ordering —
    /// the canonical UsdSkel invariant). Returns the offending joint
    /// index on failure.
    pub fn validate(&self) -> Result<(), TopologyError> {
        for (i, &p) in self.parents.iter().enumerate() {
            if p == NO_PARENT {
                continue;
            }
            if p < 0 || (p as usize) >= self.parents.len() {
                return Err(TopologyError::ParentOutOfRange { joint: i, parent: p });
            }
            if (p as usize) >= i {
                return Err(TopologyError::ParentNotBeforeChild { joint: i, parent: p });
            }
        }
        Ok(())
    }
}

/// Reasons [`Topology::validate`] can fail.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TopologyError {
    /// A parent index doesn't refer to a joint in this topology.
    #[error("joint {joint}: parent index {parent} is out of range")]
    ParentOutOfRange { joint: usize, parent: i32 },
    /// UsdSkel requires parents to come before children in the
    /// `joints` array. This entry violates that ordering.
    #[error("joint {joint}: parent index {parent} must be less than the joint's own index")]
    ParentNotBeforeChild { joint: usize, parent: i32 },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn paths(items: &[&str]) -> Vec<String> {
        items.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn derives_parents_from_path_encoding() {
        let t = Topology::from_joint_paths(&paths(&["Root", "Root/Hip", "Root/Hip/Knee", "Root/Hip/Other"]));
        assert_eq!(t.parents(), &[NO_PARENT, 0, 1, 1]);
        assert!(t.is_root(0));
        assert!(!t.is_root(1));
        assert_eq!(t.num_joints(), 4);
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
            Err(TopologyError::ParentOutOfRange { joint: 1, parent: 7 })
        ));
    }
}
