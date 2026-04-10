/// Value type representing a list-edit operation.
///
/// `ListOp` is a value type representing an operation that edits a list.
/// It may add or remove items, reorder them, or replace the list entirely.
#[derive(Default, Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct ListOp<T: Default + Clone + PartialEq> {
    #[cfg_attr(feature = "serde", serde(skip))]
    pub explicit: bool,
    #[cfg_attr(feature = "serde", serde(rename = "explicit", skip_serializing_if = "Vec::is_empty"))]
    pub explicit_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "add", skip_serializing_if = "Vec::is_empty"))]
    pub added_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "prepend", skip_serializing_if = "Vec::is_empty"))]
    pub prepended_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "append", skip_serializing_if = "Vec::is_empty"))]
    pub appended_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "delete", skip_serializing_if = "Vec::is_empty"))]
    pub deleted_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "order", skip_serializing_if = "Vec::is_empty"))]
    pub ordered_items: Vec<T>,
}

impl<T: Default + Clone + PartialEq> ListOp<T> {
    /// Returns an iterator over all items that contribute opinions:
    /// explicit, prepended, appended, and added.
    ///
    /// This excludes `deleted_items` and `ordered_items` which control
    /// removal and ordering rather than contributing values.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.explicit_items
            .iter()
            .chain(&self.prepended_items)
            .chain(&self.appended_items)
            .chain(&self.added_items)
    }

    /// Returns true if this list op has no effect (all fields empty, not explicit).
    pub fn is_empty(&self) -> bool {
        !self.explicit
            && self.explicit_items.is_empty()
            && self.added_items.is_empty()
            && self.prepended_items.is_empty()
            && self.appended_items.is_empty()
            && self.deleted_items.is_empty()
            && self.ordered_items.is_empty()
    }

    /// Compose this (stronger) list op with a weaker one, producing a single
    /// equivalent list op.
    ///
    /// This is the Rust equivalent of `SdfListOp::ComposeAndReduce`.
    pub fn combined_with(&self, weaker: &Self) -> Self {
        if self.is_empty() {
            return weaker.clone();
        }
        // Stronger is explicit → weaker is irrelevant.
        if self.explicit {
            return Self {
                explicit: true,
                explicit_items: self.explicit_items.clone(),
                ..Default::default()
            };
        }
        // Weaker is inert → copy stronger.
        if weaker.is_empty() {
            return self.clone();
        }
        // Stronger composable over weaker explicit.
        if weaker.explicit {
            let explicit_items = self
                .prepended_items
                .iter()
                .filter(|e| !self.appended_items.contains(e))
                .chain(weaker.explicit_items.iter().filter(|e| {
                    !self.deleted_items.contains(e)
                        && !self.prepended_items.contains(e)
                        && !self.appended_items.contains(e)
                }))
                .chain(self.appended_items.iter())
                .chain(self.added_items.iter().filter(|e| {
                    !self.prepended_items.contains(e)
                        && !self.appended_items.contains(e)
                        && !weaker.explicit_items.contains(e)
                }))
                .cloned()
                .collect();
            return Self {
                explicit: true,
                explicit_items,
                ..Default::default()
            };
        }
        // Both composable.
        let prepended_items = self
            .prepended_items
            .iter()
            .filter(|e| !self.appended_items.contains(e))
            .chain(weaker.prepended_items.iter().filter(|e| {
                !self.deleted_items.contains(e) && !self.prepended_items.contains(e) && !self.appended_items.contains(e)
            }))
            .cloned()
            .collect();

        let appended_items = weaker
            .appended_items
            .iter()
            .filter(|e| {
                !self.deleted_items.contains(e) && !self.prepended_items.contains(e) && !self.appended_items.contains(e)
            })
            .chain(self.appended_items.iter())
            .cloned()
            .collect();

        let added_items = weaker
            .added_items
            .iter()
            .filter(|e| {
                !self.deleted_items.contains(e)
                    && !self.prepended_items.contains(e)
                    && !self.appended_items.contains(e)
                    && !self.added_items.contains(e)
            })
            .chain(self.added_items.iter())
            .cloned()
            .collect();

        let deleted_items = weaker
            .deleted_items
            .iter()
            .filter(|e| {
                !self.prepended_items.contains(e) && !self.appended_items.contains(e) && !self.added_items.contains(e)
            })
            .chain(self.deleted_items.iter().filter(|e| {
                !weaker.deleted_items.contains(e)
                    && !self.prepended_items.contains(e)
                    && !self.appended_items.contains(e)
                    && !self.added_items.contains(e)
            }))
            .cloned()
            .collect();

        Self {
            prepended_items,
            appended_items,
            added_items,
            deleted_items,
            ..Default::default()
        }
    }

    /// Remove spurious duplicates within this list op.
    ///
    /// Items that appear in `appended_items` are removed from `prepended_items`.
    /// Items that appear in `appended_items` or `prepended_items` are removed
    /// from `deleted_items`.
    pub fn reduced(&self) -> Self {
        if self.explicit {
            return Self {
                explicit: true,
                explicit_items: self.explicit_items.clone(),
                ..Default::default()
            };
        }
        Self {
            prepended_items: self
                .prepended_items
                .iter()
                .filter(|e| !self.appended_items.contains(e))
                .cloned()
                .collect(),
            appended_items: self
                .appended_items
                .iter()
                .chain(
                    self.added_items
                        .iter()
                        .filter(|e| !self.prepended_items.contains(e) && !self.appended_items.contains(e)),
                )
                .cloned()
                .collect(),
            deleted_items: self
                .deleted_items
                .iter()
                .filter(|e| {
                    !self.appended_items.contains(e)
                        && !self.prepended_items.contains(e)
                        && !self.added_items.contains(e)
                })
                .cloned()
                .collect(),
            ..Default::default()
        }
    }

    /// Flatten this list op into its final item list.
    ///
    /// Equivalent to `self.reduced().compose_over(&[])` but avoids the
    /// intermediate allocation.
    pub fn flatten(&self) -> Vec<T> {
        if self.explicit {
            return self.explicit_items.clone();
        }
        self.prepended_items
            .iter()
            .filter(|e| !self.appended_items.contains(e) && !self.added_items.contains(e))
            .chain(self.appended_items.iter())
            .chain(
                self.added_items
                    .iter()
                    .filter(|e| !self.prepended_items.contains(e) && !self.appended_items.contains(e)),
            )
            .cloned()
            .collect()
    }

    /// Applies this list operation on top of a weaker list, producing the composed result.
    ///
    /// Follows USD's list-editing semantics:
    /// - If `self.explicit` is true, the result is `self.explicit_items` (replacing everything).
    /// - Otherwise, starts with `weaker` and applies prepend, append, add, and delete edits.
    pub fn compose_over(&self, weaker: &[T]) -> Vec<T> {
        if self.explicit {
            return self.explicit_items.clone();
        }

        let mut result: Vec<T> = weaker.to_vec();

        // Prepend: insert at front, removing duplicates from the existing list.
        for item in self.prepended_items.iter().rev() {
            result.retain(|x| x != item);
            result.insert(0, item.clone());
        }

        // Append: push to back, removing duplicates from the existing list.
        for item in &self.appended_items {
            result.retain(|x| x != item);
            result.push(item.clone());
        }

        // Add: push to back only if not already present.
        for item in &self.added_items {
            if !result.contains(item) {
                result.push(item.clone());
            }
        }

        // Delete: remove matching items.
        for item in &self.deleted_items {
            result.retain(|x| x != item);
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ListOp composition tests.
    //
    // USD list editing semantics are documented at:
    // https://openusd.org/dev/api/class_sdf_list_op.html
    //
    // In short, a ListOp can either replace the entire list (explicit mode) or
    // apply incremental edits (prepend, append, add, delete) on top of a weaker
    // opinion. These tests verify each operation and their interaction.

    /// Explicit mode replaces the weaker list entirely, regardless of its contents.
    #[test]
    fn list_op_compose_explicit_replaces_all() {
        let op = ListOp {
            explicit: true,
            explicit_items: vec![10, 20],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3]), vec![10, 20]);
    }

    /// Prepended items are inserted at the front of the weaker list in order.
    #[test]
    fn list_op_compose_prepend() {
        let op = ListOp {
            prepended_items: vec![1, 2],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[3, 4]), vec![1, 2, 3, 4]);
    }

    /// When a prepended item already exists in the weaker list, the duplicate
    /// is removed from its old position and the item appears at the front.
    #[test]
    fn list_op_compose_prepend_deduplicates() {
        let op = ListOp {
            prepended_items: vec![2],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3]), vec![2, 1, 3]);
    }

    /// Appended items are added to the back of the weaker list in order.
    #[test]
    fn list_op_compose_append() {
        let op = ListOp {
            appended_items: vec![5, 6],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2]), vec![1, 2, 5, 6]);
    }

    /// When an appended item already exists in the weaker list, the duplicate
    /// is removed from its old position and the item appears at the back.
    #[test]
    fn list_op_compose_append_deduplicates() {
        let op = ListOp {
            appended_items: vec![1],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3]), vec![2, 3, 1]);
    }

    /// Added items are appended only if they are not already present. Unlike
    /// prepend/append, `add` never moves existing items.
    #[test]
    fn list_op_compose_add_only_if_absent() {
        let op = ListOp {
            added_items: vec![2, 4],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3]), vec![1, 2, 3, 4]);
    }

    /// Deleted items are removed from the result regardless of origin.
    #[test]
    fn list_op_compose_delete() {
        let op = ListOp {
            deleted_items: vec![2],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3]), vec![1, 3]);
    }

    /// Operations are applied in order: prepend, append, delete. This test
    /// exercises all three together to verify correct sequencing.
    #[test]
    fn list_op_compose_combined() {
        let op = ListOp {
            prepended_items: vec![0],
            appended_items: vec![99],
            deleted_items: vec![2],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3]), vec![0, 1, 3, 99]);
    }

    /// Composing over an empty weaker list produces results purely from the
    /// stronger operation's items.
    #[test]
    fn list_op_compose_over_empty() {
        let op = ListOp {
            prepended_items: vec![1],
            appended_items: vec![2],
            added_items: vec![3],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[]), vec![1, 2, 3]);
    }

    /// A default (no-op) ListOp preserves the weaker list unchanged.
    #[test]
    fn list_op_compose_noop() {
        let op: ListOp<i32> = ListOp::default();
        assert_eq!(op.compose_over(&[1, 2, 3]), vec![1, 2, 3]);
    }
}
