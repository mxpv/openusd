use std::hash::{DefaultHasher, Hash, Hasher};
use std::mem;

/// Value type representing a list-edit operation.
///
/// `ListOp` is a value type representing an operation that edits a list.
/// It may add or remove items, reorder them, or replace the list entirely.
///
/// The explicit, prepended, appended and deleted items each hold an item at
/// most once, as C++ `SdfListOp` keeps them: of several equal items the
/// appended ones keep the last and the others the first. Added and ordered
/// items are kept as given.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct ListOp<T> {
    #[cfg_attr(feature = "serde", serde(skip))]
    explicit: bool,
    #[cfg_attr(feature = "serde", serde(rename = "explicit", skip_serializing_if = "Vec::is_empty"))]
    explicit_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "add", skip_serializing_if = "Vec::is_empty"))]
    added_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "prepend", skip_serializing_if = "Vec::is_empty"))]
    prepended_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "append", skip_serializing_if = "Vec::is_empty"))]
    appended_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "delete", skip_serializing_if = "Vec::is_empty"))]
    deleted_items: Vec<T>,
    #[cfg_attr(feature = "serde", serde(rename = "order", skip_serializing_if = "Vec::is_empty"))]
    ordered_items: Vec<T>,
}

impl<T> Default for ListOp<T> {
    fn default() -> Self {
        Self {
            explicit: false,
            explicit_items: Vec::new(),
            added_items: Vec::new(),
            prepended_items: Vec::new(),
            appended_items: Vec::new(),
            deleted_items: Vec::new(),
            ordered_items: Vec::new(),
        }
    }
}

/// One of the lists of items a [`ListOp`] holds (C++ `SdfListOpType`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ListOpType {
    /// The items that replace the list.
    Explicit,
    /// The items appended where the list does not hold them yet.
    Added,
    /// The items moved or added to the front of the list.
    Prepended,
    /// The items moved or added to the back of the list.
    Appended,
    /// The items removed from the list.
    Deleted,
    /// The items whose order the list takes.
    Ordered,
}

impl ListOpType {
    /// Every list, in the order the crate format stores them.
    pub const ALL: [ListOpType; 6] = [
        ListOpType::Explicit,
        ListOpType::Added,
        ListOpType::Prepended,
        ListOpType::Appended,
        ListOpType::Deleted,
        ListOpType::Ordered,
    ];

    /// Whether the list's items contribute opinions: `true` for the
    /// explicit, added, prepended and appended items, `false` for the
    /// deleted and ordered ones, which only remove or reorder.
    pub fn contributes(self) -> bool {
        !matches!(self, ListOpType::Deleted | ListOpType::Ordered)
    }

    /// Which of several equal items the list keeps, or `None` for a list
    /// that keeps them all.
    fn keeps(self) -> Option<Keep> {
        match self {
            ListOpType::Explicit | ListOpType::Prepended | ListOpType::Deleted => Some(Keep::First),
            ListOpType::Appended => Some(Keep::Last),
            ListOpType::Added | ListOpType::Ordered => None,
        }
    }
}

/// Which of several equal items a list keeps.
#[derive(Clone, Copy)]
enum Keep {
    /// The first, where the others are dropped from behind it.
    First,
    /// The last, as appending the items one by one would leave them.
    Last,
}

impl<T: Clone + PartialEq + Hash> ListOp<T> {
    /// Creates an explicit list op that replaces weaker list opinions.
    pub fn explicit<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self::of(ListOpType::Explicit, items)
    }

    /// Creates a `prepend` list op.
    pub fn prepended<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self::of(ListOpType::Prepended, items)
    }

    /// Creates an `append` list op.
    pub fn appended<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self::of(ListOpType::Appended, items)
    }

    /// Creates an `add` list op.
    pub fn added<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self::of(ListOpType::Added, items)
    }

    /// Creates a `delete` list op.
    pub fn deleted<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self::of(ListOpType::Deleted, items)
    }

    /// Creates an `order` list op.
    pub fn ordered<I>(items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self::of(ListOpType::Ordered, items)
    }

    /// A list op holding `items` in the one list `ty` names.
    fn of(ty: ListOpType, items: impl IntoIterator<Item = T>) -> Self {
        let mut op = Self::default();
        op.set_items(ty, items);
        op
    }

    /// Whether the op replaces the list with its explicit items (C++
    /// `IsExplicit`).
    pub fn is_explicit(&self) -> bool {
        self.explicit
    }

    /// Makes the op replace the list or edit it. Every list of items stays
    /// as it stands.
    pub fn set_explicit(&mut self, explicit: bool) {
        self.explicit = explicit;
    }

    /// The items that replace the list.
    pub fn explicit_items(&self) -> &[T] {
        &self.explicit_items
    }

    /// The items appended where the list does not hold them yet.
    pub fn added_items(&self) -> &[T] {
        &self.added_items
    }

    /// The items moved or added to the front of the list.
    pub fn prepended_items(&self) -> &[T] {
        &self.prepended_items
    }

    /// The items moved or added to the back of the list.
    pub fn appended_items(&self) -> &[T] {
        &self.appended_items
    }

    /// The items removed from the list.
    pub fn deleted_items(&self) -> &[T] {
        &self.deleted_items
    }

    /// The items whose order the list takes.
    pub fn ordered_items(&self) -> &[T] {
        &self.ordered_items
    }

    /// The items of the list `ty` names (C++ `GetItems`).
    pub fn items(&self, ty: ListOpType) -> &[T] {
        match ty {
            ListOpType::Explicit => &self.explicit_items,
            ListOpType::Added => &self.added_items,
            ListOpType::Prepended => &self.prepended_items,
            ListOpType::Appended => &self.appended_items,
            ListOpType::Deleted => &self.deleted_items,
            ListOpType::Ordered => &self.ordered_items,
        }
    }

    /// The items of the list `ty` names, by value.
    pub fn into_items(mut self, ty: ListOpType) -> Vec<T> {
        mem::take(self.items_mut(ty))
    }

    /// The list `ty` names, for an edit that leaves no repeated item the
    /// list does not keep.
    fn items_mut(&mut self, ty: ListOpType) -> &mut Vec<T> {
        match ty {
            ListOpType::Explicit => &mut self.explicit_items,
            ListOpType::Added => &mut self.added_items,
            ListOpType::Prepended => &mut self.prepended_items,
            ListOpType::Appended => &mut self.appended_items,
            ListOpType::Deleted => &mut self.deleted_items,
            ListOpType::Ordered => &mut self.ordered_items,
        }
    }

    /// Replaces the items of the list `ty` names, dropping the repeated
    /// ones that list does not keep (C++ `SetItems`). Explicit items make
    /// the op explicit, which they are the whole of; items of any other
    /// list leave that as it stands. Every other list stays as it is.
    pub fn set_items(&mut self, ty: ListOpType, items: impl IntoIterator<Item = T>) {
        self.edit_items(ty, |held| *held = items.into_iter().collect());
        self.explicit |= ty == ListOpType::Explicit;
    }

    /// The op with the items of the list `ty` names replaced as
    /// [`set_items`](Self::set_items) replaces them, for an op of several
    /// lists: `ListOp::prepended([1]).with(ListOpType::Deleted, [2])`.
    pub fn with(mut self, ty: ListOpType, items: impl IntoIterator<Item = T>) -> Self {
        self.set_items(ty, items);
        self
    }

    /// Edits the items of the list `ty` names in place, then drops the
    /// repeated ones that list does not keep.
    pub fn edit_items<R>(&mut self, ty: ListOpType, edit: impl FnOnce(&mut Vec<T>) -> R) -> R {
        let items = self.items_mut(ty);
        let result = edit(items);
        make_unique(items, ty.keeps());
        result
    }

    /// Puts `item` at the end of the list `ty` names where that list does
    /// not hold it yet. Returns whether it was put there.
    pub fn push(&mut self, ty: ListOpType, item: T) -> bool {
        let items = self.items_mut(ty);
        let absent = !items.contains(&item);
        if absent {
            items.push(item);
        }
        absent
    }

    /// Converts every item with `f`, which is told the list each item is
    /// in, dropping those it returns `None` for. Items that convert to equal
    /// ones are dropped as [`set_items`](Self::set_items) drops them.
    pub fn convert<U: Clone + PartialEq + Hash>(self, mut f: impl FnMut(ListOpType, T) -> Option<U>) -> ListOp<U> {
        let mut convert = |ty, items: Vec<T>| -> Vec<U> {
            let mut items = items.into_iter().filter_map(|item| f(ty, item)).collect();
            make_unique(&mut items, ty.keeps());
            items
        };
        ListOp {
            explicit: self.explicit,
            explicit_items: convert(ListOpType::Explicit, self.explicit_items),
            added_items: convert(ListOpType::Added, self.added_items),
            prepended_items: convert(ListOpType::Prepended, self.prepended_items),
            appended_items: convert(ListOpType::Appended, self.appended_items),
            deleted_items: convert(ListOpType::Deleted, self.deleted_items),
            ordered_items: convert(ListOpType::Ordered, self.ordered_items),
        }
    }

    /// Rewrites every item of every list in place, the deleted and ordered
    /// ones included, so a delete or reorder still matches the item it names
    /// once rewritten (e.g. retiming a reference's layer offset). Items that
    /// became equal to another are then dropped as
    /// [`set_items`](Self::set_items) drops them.
    pub fn update(&mut self, mut f: impl FnMut(&mut T)) {
        for ty in ListOpType::ALL {
            self.edit_items(ty, |items| items.iter_mut().for_each(&mut f));
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
        !self.explicit && ListOpType::ALL.into_iter().all(|ty| self.items(ty).is_empty())
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
        self.discard(item) | self.push(ListOpType::Deleted, item.clone())
    }

    /// Drops `item` from the list `ty` names. Returns whether the list held
    /// it.
    pub fn remove_item(&mut self, ty: ListOpType, item: &T) -> bool {
        remove_one(self.items_mut(ty), item)
    }

    /// Drops `item` from every list that contributes it: the explicit,
    /// added, prepended and appended items. Returns whether any held it.
    pub fn discard(&mut self, item: &T) -> bool {
        remove_one(&mut self.explicit_items, item)
            | remove_one(&mut self.added_items, item)
            | remove_one(&mut self.prepended_items, item)
            | remove_one(&mut self.appended_items, item)
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
            let mut explicit_items: Vec<T> = self
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
            // The stronger op's added items are held as given, and may repeat.
            make_unique(&mut explicit_items, Some(Keep::First));
            return Self {
                explicit: true,
                explicit_items,
                ordered_items: merge_ordered(&self.ordered_items, &weaker.ordered_items),
                ..Default::default()
            };
        }
        // Both composable.
        let prepended_items: Vec<T> = self
            .prepended_items
            .iter()
            .filter(|e| !self.appended_items.contains(e))
            .chain(weaker.prepended_items.iter().filter(|e| {
                !self.deleted_items.contains(e) && !self.prepended_items.contains(e) && !self.appended_items.contains(e)
            }))
            .cloned()
            .collect();

        let appended_items: Vec<T> = weaker
            .appended_items
            .iter()
            .filter(|e| {
                !self.deleted_items.contains(e) && !self.prepended_items.contains(e) && !self.appended_items.contains(e)
            })
            .chain(self.appended_items.iter())
            .cloned()
            .collect();

        // Keep the composed op canonical (one bucket per item), mirroring
        // `SdfListOp::ComposeAndReduce`: an item already composed into
        // `prepended` or `appended` must not also appear as an `add`, so every
        // consumer (`iter`, `flatten`) sees it once. Filter both the weaker and
        // the stronger adds against the composed prepend/append sets.
        let in_prepend_or_append = |e: &T| prepended_items.contains(e) || appended_items.contains(e);
        let added_items = weaker
            .added_items
            .iter()
            .filter(|e| !self.deleted_items.contains(e) && !self.added_items.contains(e) && !in_prepend_or_append(e))
            .chain(self.added_items.iter().filter(|e| !in_prepend_or_append(e)))
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
        let mut appended_items = self.appended_items.clone();
        appended_items.extend(self.absent_added());
        Self {
            prepended_items: self
                .prepended_items
                .iter()
                .filter(|e| !self.appended_items.contains(e))
                .cloned()
                .collect(),
            appended_items,
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

    /// Folds `incoming` — a freshly parsed single-operator opinion — into this
    /// list op so successive `prepend`/`append`/`add`/`delete`/`reorder`
    /// statements for one field on the same spec accumulate instead of
    /// overwriting (C++ Sdf builds a single `SdfListOp` per field).
    ///
    /// Explicit and composed (operator) forms are mutually exclusive. An
    /// explicit `incoming` (`field = [...]` or `field = None`) replaces this op
    /// outright; an operator `incoming` puts the field in composed mode,
    /// discarding any prior explicit opinion, then sets each operator sublist it
    /// populates (leaving the other operator sublists intact).
    pub fn merge_op(&mut self, incoming: ListOp<T>) {
        if incoming.explicit {
            *self = incoming;
            return;
        }
        if self.explicit {
            self.explicit = false;
            self.explicit_items.clear();
        }
        for (slot, items) in [
            (&mut self.prepended_items, incoming.prepended_items),
            (&mut self.appended_items, incoming.appended_items),
            (&mut self.added_items, incoming.added_items),
            (&mut self.deleted_items, incoming.deleted_items),
            (&mut self.ordered_items, incoming.ordered_items),
        ] {
            if !items.is_empty() {
                *slot = items;
            }
        }
    }

    /// The added items that are neither prepended nor appended, each once at
    /// its first place: what adding them one by one leaves behind the
    /// prepended and appended items.
    fn absent_added(&self) -> Vec<T> {
        let mut added: Vec<T> = self
            .added_items
            .iter()
            .filter(|e| !self.prepended_items.contains(e) && !self.appended_items.contains(e))
            .cloned()
            .collect();
        make_unique(&mut added, Some(Keep::First));
        added
    }

    /// Flatten this list op into its final item list.
    pub fn flatten(&self) -> Vec<T> {
        let mut result = if self.explicit {
            self.explicit_items.clone()
        } else {
            // Emit each item once, keeping the position sequential `compose_over`
            // would give it. A prepended item keeps its front position unless it
            // is also appended (an append moves it to the back); an item is
            // dropped from `added` only when it already appears as a prepend or
            // append. An item present in two buckets is therefore kept once,
            // not dropped, even when the op is not canonical.
            self.prepended_items
                .iter()
                .filter(|e| !self.appended_items.contains(e))
                .chain(self.appended_items.iter())
                .cloned()
                .chain(self.absent_added())
                .collect()
        };

        if !self.ordered_items.is_empty() {
            super::apply_ordering(&mut result, &self.ordered_items);
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
            super::apply_ordering(&mut result, &self.ordered_items);
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

/// Drop the items of `items` that repeat an earlier one, or with
/// [`Keep::Last`] a later one, keeping the rest in order (C++
/// `SdfListOp::_MakeUnique`). With no `keep`, every item stays.
fn make_unique<T: PartialEq + Hash>(items: &mut Vec<T>, keep: Option<Keep>) {
    let Some(keep) = keep else {
        return;
    };
    // Most lists are a few items long, and are compared item by item.
    const SMALL: usize = 10;
    if items.len() <= SMALL {
        let mut index = 0;
        while index < items.len() {
            let repeated = match keep {
                Keep::First => items[..index].contains(&items[index]),
                Keep::Last => items[index + 1..].contains(&items[index]),
            };
            match repeated {
                true => drop(items.remove(index)),
                false => index += 1,
            }
        }
        return;
    }

    // Equal items hash alike, so they sit in one run of the indices sorted
    // by hash, each run in index order.
    let mut hashed: Vec<(u64, usize)> = items
        .iter()
        .enumerate()
        .map(|(index, item)| {
            let mut state = DefaultHasher::new();
            item.hash(&mut state);
            (state.finish(), index)
        })
        .collect();
    hashed.sort_unstable();
    // Items that all hash apart are all different.
    if hashed.windows(2).all(|pair| pair[0].0 != pair[1].0) {
        return;
    }

    let mut repeated = vec![false; items.len()];
    for run in hashed.chunk_by(|a, b| a.0 == b.0) {
        for (place, &(_, index)) in run.iter().enumerate() {
            let rivals = match keep {
                Keep::First => &run[..place],
                Keep::Last => &run[place + 1..],
            };
            repeated[index] = rivals.iter().any(|&(_, rival)| items[rival] == items[index]);
        }
    }
    let mut repeated = repeated.into_iter();
    items.retain(|_| !repeated.next().unwrap_or(false));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

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

    /// The explicit, prepended and deleted items keep the first of several
    /// equal items and the appended items the last, while added and ordered
    /// items are held as given.
    #[test]
    fn items_held_once() {
        let repeated = [1, 2, 1, 3, 2];
        assert_eq!(ListOp::explicit(repeated).explicit_items(), [1, 2, 3]);
        assert_eq!(ListOp::prepended(repeated).prepended_items(), [1, 2, 3]);
        assert_eq!(ListOp::deleted(repeated).deleted_items(), [1, 2, 3]);
        assert_eq!(ListOp::appended(repeated).appended_items(), [1, 3, 2]);
        assert_eq!(ListOp::added(repeated).added_items(), repeated);
        assert_eq!(ListOp::ordered(repeated).ordered_items(), repeated);

        let op = ListOp::prepended([1]).with(ListOpType::Deleted, [4, 4]);
        assert_eq!(op.items(ListOpType::Prepended), [1]);
        assert_eq!(op.items(ListOpType::Deleted), [4]);
        assert!(!op.is_explicit());
        // Explicit items are an explicit op's.
        assert_eq!(ListOp::default().with(ListOpType::Explicit, [5]), ListOp::explicit([5]));
    }

    /// A list too long to compare pair by pair drops its repeated items in
    /// the same places.
    #[test]
    fn long_list_held_once() {
        let items: Vec<i32> = (0..1000).chain((0..1000).rev()).collect();
        let ascending: Vec<i32> = (0..1000).collect();
        let descending: Vec<i32> = (0..1000).rev().collect();
        assert_eq!(ListOp::prepended(items.clone()).prepended_items(), ascending);
        assert_eq!(ListOp::appended(items).appended_items(), descending);
    }

    /// Items that hash alike without being equal are told apart.
    #[test]
    fn unhashed_field_distinguishes() {
        let reference = |asset: &str, offset: f64| sdf::Reference {
            asset_path: asset.to_owned(),
            layer_offset: sdf::LayerOffset { offset, scale: 1.0 },
            ..Default::default()
        };
        // Enough items to hash, three of them equal to an earlier one.
        let items: Vec<_> = (0..12)
            .map(|n| reference("a.usda", f64::from(n % 9)))
            .chain([reference("b.usda", 0.0)])
            .collect();
        let op = ListOp::prepended(items);
        assert_eq!(op.prepended_items().len(), 10);
        assert_eq!(op.prepended_items()[9], reference("b.usda", 0.0));
    }

    /// An edit in place, and a rewrite of every item, leave no repeated
    /// item behind.
    #[test]
    fn edits_keep_items_once() {
        let mut op = ListOp::prepended([1, 2]);
        let pushed = op.edit_items(ListOpType::Prepended, |items| {
            items.push(1);
            items.len()
        });
        assert_eq!(pushed, 3);
        assert_eq!(op.prepended_items(), [1, 2]);

        let mut op = ListOp::appended([1, 2, 3]).with(ListOpType::Added, [5, 6]);
        op.update(|item| *item /= 2);
        assert_eq!(op.appended_items(), [0, 1]);
        assert_eq!(op.added_items(), [2, 3]);

        let op = ListOp::explicit([1, 2, 3]).with(ListOpType::Deleted, [7]);
        let halved = op.convert(|ty, item| (ty.contributes() || item != 7).then_some(item / 2));
        assert!(halved.is_explicit());
        assert_eq!(halved.explicit_items(), [0, 1]);
        assert!(halved.deleted_items().is_empty());
    }

    /// A repeated added item lands once, where adding the items one by one
    /// puts it.
    #[test]
    fn repeated_add_keeps_first() {
        let op = ListOp::appended([1]).with(ListOpType::Added, [2, 3, 2, 1]);
        assert_eq!(op.flatten(), [1, 2, 3]);
        assert_eq!(op.reduced().flatten(), [1, 2, 3]);
        assert_eq!(op.flatten(), op.compose_over(&[]));
    }

    /// Dropping an item takes it out of every list that contributes it and
    /// leaves the deletes alone.
    #[test]
    fn discard_contributed_item() {
        let mut op = ListOp::prepended([1, 2])
            .with(ListOpType::Appended, [2, 3])
            .with(ListOpType::Deleted, [2]);
        assert!(op.discard(&2));
        assert_eq!(op.prepended_items(), [1]);
        assert_eq!(op.appended_items(), [3]);
        assert_eq!(op.deleted_items(), [2]);
        assert!(!op.discard(&2));
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

    /// Successive single-operator opinions on one spec accumulate into distinct
    /// sublists rather than overwriting.
    #[test]
    fn merge_op_accumulates_operators() {
        let mut op = ListOp::prepended(vec![1]);
        op.merge_op(ListOp::appended(vec![2]));
        assert_eq!(op.prepended_items, vec![1]);
        assert_eq!(op.appended_items, vec![2]);
    }

    /// An explicit opinion replaces any operator opinions merged before it.
    #[test]
    fn merge_op_explicit_replaces() {
        let mut op = ListOp::prepended(vec![1]);
        op.merge_op(ListOp::explicit(vec![9]));
        assert!(op.explicit);
        assert_eq!(op.explicit_items, vec![9]);
        assert!(op.prepended_items.is_empty());
    }

    /// An operator opinion after an explicit one switches the field to composed
    /// mode, discarding the explicit items (`X = [1, 2]; append X = [3]` → only
    /// the append survives).
    #[test]
    fn merge_op_operator_clears_explicit() {
        let mut op = ListOp::explicit(vec![1, 2]);
        op.merge_op(ListOp::appended(vec![3]));
        assert!(!op.explicit);
        assert!(op.explicit_items.is_empty());
        assert_eq!(op.appended_items, vec![3]);
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

    /// Each ordered item carries the run of following unordered items into the
    /// order sequence (C++ `SdfApplyListOrdering`): `3` brings `4`, `1` brings
    /// `2`, emitted as `[3, 4]` then `[1, 2]`.
    #[test]
    fn list_op_compose_ordered_items() {
        let op = ListOp {
            ordered_items: vec![3, 1],
            ..Default::default()
        };
        assert_eq!(op.compose_over(&[1, 2, 3, 4]), vec![3, 4, 1, 2]);
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

    /// A default (no-op) `ListOp` preserves the weaker list unchanged.
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
        assert_eq!(composed.flatten(), vec![3, 1, 2]);
    }

    /// A stronger `add` of an item a weaker layer `prepend`s (or `append`s)
    /// must not leave the item in two buckets — `flatten` would then drop it.
    /// `combined_with` keeps one bucket per item, so `combined_with` + `flatten`
    /// agrees with sequential `compose_over`.
    #[test]
    fn combined_add_over_prepend_canonical() {
        let stronger = ListOp {
            added_items: vec![1],
            ..Default::default()
        };
        let weaker = ListOp {
            prepended_items: vec![1],
            ..Default::default()
        };
        let composed = stronger.combined_with(&weaker);
        // Item 1 stays only in `prepended`, not also in `added`.
        assert_eq!(composed.prepended_items, vec![1]);
        assert!(composed.added_items.is_empty());
        assert_eq!(composed.flatten(), vec![1]);
        assert_eq!(composed.flatten(), stronger.compose_over(&weaker.compose_over(&[])));
    }

    /// The same canonicalization holds when the weaker opinion `append`s the
    /// item the stronger op `add`s.
    #[test]
    fn combined_add_over_append_canonical() {
        let stronger = ListOp {
            added_items: vec![1],
            ..Default::default()
        };
        let weaker = ListOp {
            appended_items: vec![1],
            ..Default::default()
        };
        let composed = stronger.combined_with(&weaker);
        assert_eq!(composed.appended_items, vec![1]);
        assert!(composed.added_items.is_empty());
        assert_eq!(composed.flatten(), vec![1]);
    }

    /// `flatten` keeps an item once even when a (non-canonical) list op places
    /// it in two buckets — e.g. authored as both `prepend` and `add`. It must
    /// not drop the item, and must match what sequential `compose_over` yields.
    #[test]
    fn flatten_keeps_item_in_two_buckets() {
        // prepend + add: kept at the front (compose_over: prepend places it,
        // the redundant add is skipped).
        let prepend_add = ListOp {
            prepended_items: vec![1],
            added_items: vec![1],
            ..Default::default()
        };
        assert_eq!(prepend_add.flatten(), vec![1]);
        assert_eq!(prepend_add.flatten(), prepend_add.compose_over(&[]));

        // append + add: kept at the back.
        let append_add = ListOp {
            appended_items: vec![1],
            added_items: vec![1],
            ..Default::default()
        };
        assert_eq!(append_add.flatten(), vec![1]);
        assert_eq!(append_add.flatten(), append_add.compose_over(&[]));

        // prepend + append: the append moves it to the back.
        let prepend_append = ListOp {
            prepended_items: vec![1, 2],
            appended_items: vec![1],
            ..Default::default()
        };
        assert_eq!(prepend_append.flatten(), vec![2, 1]);
        assert_eq!(prepend_append.flatten(), prepend_append.compose_over(&[]));
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
