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
    /// Creates an explicit list op that replaces weaker list opinions.
    pub fn explicit<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            explicit: true,
            explicit_items: items.into_iter().collect(),
            ..Default::default()
        }
    }

    /// Creates a `prepend` list op.
    pub fn prepended<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            prepended_items: items.into_iter().collect(),
            ..Default::default()
        }
    }

    /// Creates an `append` list op.
    pub fn appended<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            appended_items: items.into_iter().collect(),
            ..Default::default()
        }
    }

    /// Creates an `add` list op.
    pub fn added<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            added_items: items.into_iter().collect(),
            ..Default::default()
        }
    }

    /// Creates a `delete` list op.
    pub fn deleted<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            deleted_items: items.into_iter().collect(),
            ..Default::default()
        }
    }

    /// Creates an `order` list op.
    pub fn ordered<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            ordered_items: items.into_iter().collect(),
            ..Default::default()
        }
    }

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

    /// Remove `item` so it is absent from the composed result, mirroring C++
    /// `SdfListEditorProxy::Remove`.
    ///
    /// In explicit mode the explicit list is the whole value, so the entry is
    /// simply dropped. Otherwise any local opinion that would add `item` is
    /// dropped and `item` is recorded in `deleted_items` (unless already
    /// present), which [`combined_with`](Self::combined_with) honors to
    /// suppress the same item authored in a weaker layer. Returns whether
    /// anything changed.
    pub fn remove(&mut self, item: &T) -> bool {
        if self.explicit {
            return remove_one(&mut self.explicit_items, item);
        }
        let mut changed = remove_one(&mut self.explicit_items, item);
        changed |= remove_one(&mut self.added_items, item);
        changed |= remove_one(&mut self.prepended_items, item);
        changed |= remove_one(&mut self.appended_items, item);
        if !self.deleted_items.iter().any(|i| i == item) {
            self.deleted_items.push(item.clone());
            changed = true;
        }
        changed
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
                ordered_items: self.ordered_items.clone(),
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
                ordered_items: merge_ordered(&self.ordered_items, &weaker.ordered_items),
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
            ordered_items: merge_ordered(&self.ordered_items, &weaker.ordered_items),
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
                ordered_items: self.ordered_items.clone(),
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
            ordered_items: self.ordered_items.clone(),
            ..Default::default()
        }
    }

    /// Flatten this list op into its final item list.
    pub fn flatten(&self) -> Vec<T> {
        let mut result = if self.explicit {
            self.explicit_items.clone()
        } else {
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
        };

        if !self.ordered_items.is_empty() {
            apply_ordering(&mut result, &self.ordered_items);
        }

        result
    }

    /// Applies this list operation on top of a weaker list, producing the composed result.
    ///
    /// Implements AOUSD Core Specification §12.2.6 list-op application:
    /// - If `self.explicit` is true, the result is `self.explicit_items` (replacing everything).
    /// - Otherwise, starts with `weaker` and applies prepend, append, add, and delete edits.
    /// - Finally, applies order edits to the matching items in the result.
    pub fn compose_over(&self, weaker: &[T]) -> Vec<T> {
        let mut result = if self.explicit {
            self.explicit_items.clone()
        } else {
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
        };

        if !self.ordered_items.is_empty() {
            apply_ordering(&mut result, &self.ordered_items);
        }

        result
    }
}

/// Remove the first occurrence of `item` from `items`, returning whether it
/// was present.
fn remove_one<T: PartialEq>(items: &mut Vec<T>, item: &T) -> bool {
    let Some(idx) = items.iter().position(|i| i == item) else {
        return false;
    };
    items.remove(idx);
    true
}

/// Merge two `reorder` lists with the stronger taking precedence on
/// duplicates. Mirrors how `prepended_items` are combined: stronger items keep
/// their order, then weaker items not present in the stronger are appended.
fn merge_ordered<T: Clone + PartialEq>(stronger: &[T], weaker: &[T]) -> Vec<T> {
    if weaker.is_empty() {
        return stronger.to_vec();
    }
    if stronger.is_empty() {
        return weaker.to_vec();
    }
    stronger
        .iter()
        .chain(weaker.iter().filter(|e| !stronger.contains(e)))
        .cloned()
        .collect()
}

fn apply_ordering<T: Clone + PartialEq>(items: &mut [T], order: &[T]) {
    if order.is_empty() || items.is_empty() {
        return;
    }

    let slots: Vec<usize> = items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| order.contains(item).then_some(i))
        .collect();
    if slots.is_empty() {
        return;
    }

    let projected: Vec<&T> = order.iter().filter(|item| items.contains(*item)).collect();
    for (slot, item) in slots.into_iter().zip(projected) {
        items[slot].clone_from(item);
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

    #[test]
    fn constructors_populate_one_bucket() {
        let op = ListOp::explicit([10, 20]);
        assert!(op.explicit);
        assert_eq!(op.explicit_items, vec![10, 20]);
        assert!(op.prepended_items.is_empty());
        assert!(op.appended_items.is_empty());
        assert!(op.added_items.is_empty());
        assert!(op.deleted_items.is_empty());
        assert!(op.ordered_items.is_empty());

        let op = ListOp::prepended([1, 2]);
        assert!(!op.explicit);
        assert_eq!(op.prepended_items, vec![1, 2]);

        let op = ListOp::appended([3, 4]);
        assert_eq!(op.appended_items, vec![3, 4]);

        let op = ListOp::added([5, 6]);
        assert_eq!(op.added_items, vec![5, 6]);

        let op = ListOp::deleted([7, 8]);
        assert_eq!(op.deleted_items, vec![7, 8]);

        let op = ListOp::ordered([9, 10]);
        assert_eq!(op.ordered_items, vec![9, 10]);
    }

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

    /// Ordered items are reshuffled only within their existing result slots.
    #[test]
    fn list_op_compose_ordered_items() {
        let op = ListOp {
            ordered_items: vec![3, 1],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3, 4]), vec![3, 2, 1, 4]);
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

    /// `reorder` opinions on the stronger op survive composition with a
    /// composable weaker op and still apply on `flatten()`.
    #[test]
    fn combined_keeps_stronger_reorder() {
        let stronger = ListOp {
            ordered_items: vec![2, 1],
            ..Default::default()
        };
        let weaker = ListOp {
            prepended_items: vec![1, 2],
            ..Default::default()
        };
        let composed = stronger.combined_with(&weaker);
        assert_eq!(composed.ordered_items, vec![2, 1]);
        assert_eq!(composed.flatten(), vec![2, 1]);
    }

    /// `reorder` opinions on the weaker op survive when the stronger is
    /// composable but authors no `reorder` of its own.
    #[test]
    fn combined_keeps_weaker_reorder() {
        let stronger = ListOp {
            prepended_items: vec![3],
            ..Default::default()
        };
        let weaker = ListOp {
            prepended_items: vec![1, 2],
            ordered_items: vec![2, 1],
            ..Default::default()
        };
        let composed = stronger.combined_with(&weaker);
        assert_eq!(composed.ordered_items, vec![2, 1]);
        assert_eq!(composed.flatten(), vec![3, 2, 1]);
    }

    /// When both sides author a `reorder`, the stronger order wins; weaker
    /// entries not in the stronger are appended.
    #[test]
    fn combined_merges_reorder() {
        let stronger = ListOp {
            ordered_items: vec![1, 2],
            ..Default::default()
        };
        let weaker = ListOp {
            prepended_items: vec![1, 2, 3],
            ordered_items: vec![2, 3],
            ..Default::default()
        };
        let composed = stronger.combined_with(&weaker);
        assert_eq!(composed.ordered_items, vec![1, 2, 3]);
        assert_eq!(composed.flatten(), vec![1, 2, 3]);
    }

    /// An explicit stronger op replaces weaker items but still carries its own
    /// `ordered_items` through to `flatten`.
    #[test]
    fn combined_explicit_keeps_reorder() {
        let stronger = ListOp {
            explicit: true,
            explicit_items: vec![1, 2, 3],
            ordered_items: vec![3, 1],
            ..Default::default()
        };
        let weaker = ListOp {
            prepended_items: vec![9],
            ordered_items: vec![9],
            ..Default::default()
        };
        let composed = stronger.combined_with(&weaker);
        assert!(composed.explicit);
        assert_eq!(composed.ordered_items, vec![3, 1]);
        assert_eq!(composed.flatten(), vec![3, 2, 1]);
    }

    /// `reduced()` keeps `ordered_items` intact so a `reorder` opinion still
    /// applies on the eventual `flatten()`.
    #[test]
    fn reduced_keeps_reorder() {
        let op = ListOp {
            prepended_items: vec![1, 2],
            ordered_items: vec![2, 1],
            ..Default::default()
        };
        let reduced = op.reduced();
        assert_eq!(reduced.ordered_items, vec![2, 1]);
        assert_eq!(reduced.flatten(), vec![2, 1]);
    }
}
