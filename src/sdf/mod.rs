//! Scene description foundations.
//!
//! This module contains common data types used by parsers.
//! Roughly this correspond to C++ SDF module <https://openusd.org/dev/api/sdf_page_front.html>

use std::{borrow::Cow, collections::HashMap, fmt::Debug};

use anyhow::Result;
use bytemuck::{Pod, Zeroable};
use strum::{Display, EnumCount, FromRepr};

mod path;
pub mod schema;
mod value;

pub use path::{path, Path};
pub use schema::{ChildrenKey, FieldKey};
pub use value::{Value, ValueConversionError};

/// An enum that specifies the type of an object.
/// Objects are entities that have fields and are addressable by path.
#[repr(u32)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, FromRepr, EnumCount, Display)]
pub enum SpecType {
    // The unknown type has a value of 0 so that SdfSpecType() is unknown.
    #[default]
    Unknown = 0,

    // Real concrete types
    Attribute = 1,
    Connection = 2,
    Expression = 3,
    Mapper = 4,
    MapperArg = 5,
    Prim = 6,
    PseudoRoot = 7,
    Relationship = 8,
    RelationshipTarget = 9,
    Variant = 10,
    VariantSet = 11,
}

#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum Specifier {
    Def,
    Over,
    Class,
}

/// An enum that defines permission levels.
///
/// Permissions control which layers may refer to or express
/// opinions about a prim. Opinions expressed about a prim, or
/// relationships to that prim, by layers that are not allowed
/// permission to access the prim will be ignored.
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum Permission {
    Public,
    Private,
}

/// An enum that identifies variability types for attributes.
/// Variability indicates whether the attribute may vary over time and
/// value coordinates, and if its value comes through authoring or
/// or from its owner.
#[repr(i32)]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, FromRepr)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "camelCase"))]
pub enum Variability {
    #[default]
    Varying,
    Uniform,
}

/// Represents a time offset and scale between layers.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Pod, Zeroable)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct LayerOffset {
    /// Time offset.
    pub offset: f64,
    /// Scale factor.
    pub scale: f64,
}

impl Default for LayerOffset {
    fn default() -> Self {
        Self {
            offset: 0.0,
            scale: 1.0,
        }
    }
}

impl LayerOffset {
    #[inline]
    pub fn new(offset: f64, scale: f64) -> Self {
        Self { offset, scale }
    }

    #[inline]
    pub fn is_valid(&self) -> bool {
        self.offset.is_finite() && self.scale.is_finite()
    }
}

/// Represents a payload and all its meta data.
///
/// A payload represents a prim reference to an external layer. A payload
/// is similar to a prim reference (see SdfReference) with the major
/// difference that payloads are explicitly loaded by the user.
///
/// Unloaded payloads represent a boundary that lazy composition and
/// system behaviors will not traverse across, providing a user-visible
/// way to manage the working set of the scene.
#[derive(Debug, Default, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Payload {
    /// The asset path to the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "asset", skip_serializing_if = "String::is_empty"))]
    pub asset_path: String,
    /// The root prim path to the referenced prim in the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "path", skip_serializing_if = "Path::is_empty"))]
    pub prim_path: Path,
    /// The layer offset to transform time.
    #[cfg_attr(
        feature = "serde",
        serde(rename = "layerOffset", skip_serializing_if = "Option::is_none")
    )]
    pub layer_offset: Option<LayerOffset>,
}

/// Represents a reference and all its meta data.
///
/// A reference is expressed on a prim in a given layer and it identifies a
/// prim in a layer stack. All opinions in the namespace hierarchy
/// under the referenced prim will be composed with the opinions in the
/// namespace hierarchy under the referencing prim.
#[derive(Debug, Default, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub struct Reference {
    /// The asset path to the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "asset", skip_serializing_if = "String::is_empty"))]
    pub asset_path: String,
    /// The path to the referenced prim in the external layer.
    #[cfg_attr(feature = "serde", serde(rename = "path", skip_serializing_if = "Path::is_empty"))]
    pub prim_path: Path,
    /// The layer offset to transform time.
    #[cfg_attr(feature = "serde", serde(rename = "layerOffset"))]
    pub layer_offset: LayerOffset,
    /// The custom data associated with the reference.
    #[cfg_attr(
        feature = "serde",
        serde(rename = "customData", skip_serializing_if = "HashMap::is_empty")
    )]
    pub custom_data: HashMap<String, Value>,
}

/// Value type representing a list-edit operation.
///
/// `ListOp`` is a value type representing an operation that edits a list.
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
                .chain(
                    weaker
                        .explicit_items
                        .iter()
                        .filter(|e| {
                            !self.deleted_items.contains(e)
                                && !self.prepended_items.contains(e)
                                && !self.appended_items.contains(e)
                        }),
                )
                .chain(self.appended_items.iter())
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
                !self.deleted_items.contains(e)
                    && !self.prepended_items.contains(e)
                    && !self.appended_items.contains(e)
            }))
            .cloned()
            .collect();

        let appended_items = weaker
            .appended_items
            .iter()
            .filter(|e| {
                !self.deleted_items.contains(e)
                    && !self.prepended_items.contains(e)
                    && !self.appended_items.contains(e)
            })
            .chain(self.appended_items.iter())
            .cloned()
            .collect();

        let deleted_items = weaker
            .deleted_items
            .iter()
            .filter(|e| !self.prepended_items.contains(e) && !self.appended_items.contains(e))
            .chain(
                self.deleted_items
                    .iter()
                    .filter(|e| {
                        !weaker.deleted_items.contains(e)
                            && !self.prepended_items.contains(e)
                            && !self.appended_items.contains(e)
                    }),
            )
            .cloned()
            .collect();

        Self {
            prepended_items,
            appended_items,
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
            appended_items: self.appended_items.clone(),
            deleted_items: self
                .deleted_items
                .iter()
                .filter(|e| !self.appended_items.contains(e) && !self.prepended_items.contains(e))
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
            .filter(|e| !self.appended_items.contains(e))
            .chain(self.appended_items.iter())
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

pub type IntListOp = ListOp<i32>;
pub type UintListOp = ListOp<u32>;

pub type Int64ListOp = ListOp<i64>;
pub type Uint64ListOp = ListOp<u64>;

pub type StringListOp = ListOp<String>;
pub type TokenListOp = ListOp<String>;
pub type PathListOp = ListOp<Path>;
pub type ReferenceListOp = ListOp<Reference>;
pub type PayloadListOp = ListOp<Payload>;

pub type TimeSampleMap = Vec<(f64, Value)>;

/// Interface to access scene description data similar to `SdfAbstractData` in C++ version of USD.
///
/// `AbstractData` is an anonymous container that owns scene description values.
///
/// For now holds read-only portion of the API.
pub trait AbstractData {
    /// Returns `true` if this data has a spec for the given path.
    fn has_spec(&self, path: &Path) -> bool;

    /// Returns `true` if this data has a field for the given path.
    fn has_field(&self, path: &Path, field: &str) -> bool;

    /// Returns the type of the spec at the given path.
    fn spec_type(&self, path: &Path) -> Option<SpecType>;

    /// Returns the underlying value for the given path.
    ///
    /// # Return
    /// Returns a [Value] enum that wraps possible field's values.
    ///
    /// The value can be either owned or borrowed depending on internals.
    /// In the binary format, the data is typically compressed and/or encoded,
    /// so memory allocation is required to store unpacked result, so
    /// owned values are typically be expected.
    ///
    /// With test parsers, there is a data copy already stored, so
    /// a borrowed value will be returned to avoid unnecessary copies.
    fn get(&self, path: &Path, field: &str) -> Result<Cow<'_, Value>>;

    /// Returns the names of the fields for the given path.
    fn list(&self, path: &Path) -> Option<Vec<String>>;
}

/// A boxed layer data source, used throughout the layer stack.
pub type LayerData = Box<dyn AbstractData>;

/// A single spec in a scene description layer, consisting of a type and a set of fields.
///
/// See [SdfSpec](https://openusd.org/dev/api/class_sdf_spec.html) in the USD documentation.
#[derive(Debug, Clone)]
pub struct Spec {
    /// The type of this spec (prim, attribute, relationship, etc.).
    pub ty: SpecType,
    /// The fields stored on this spec, keyed by field name.
    pub fields: HashMap<String, Value>,
}

impl Spec {
    /// Creates a new empty spec of the given type.
    pub fn new(ty: SpecType) -> Self {
        Self {
            ty,
            fields: Default::default(),
        }
    }

    /// Add a new field to the spec.
    #[inline]
    pub fn add(&mut self, key: impl AsRef<str>, value: impl Into<Value>) {
        self.fields.insert(key.as_ref().to_owned(), value.into());
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
