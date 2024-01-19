//! Scene description foundations.

use std::{collections::HashMap, fmt::Debug};

use anyhow::Result;
use bytemuck::{Pod, Zeroable};
use strum::{Display, EnumCount, FromRepr};

mod path;
mod value;

pub use path::{path, Path};
pub use value::Value;

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
pub enum Permission {
    Public,
    Private,
}

/// An enum that identifies variability types for attributes.
/// Variability indicates whether the attribute may vary over time and
/// value coordinates, and if its value comes through authoring or
/// or from its owner.
#[repr(i32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, FromRepr)]
pub enum Variability {
    Varying,
    Uniform,
}

/// Represents a time offset and scale between layers.
#[repr(C)]
#[derive(Debug, Clone, Copy, Pod, Zeroable)]
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
#[derive(Debug, Default)]
pub struct Payload {
    /// The asset path to the external layer.
    pub asset_path: String,
    /// The root prim path to the referenced prim in the external layer.
    pub prim_path: Path,
    /// The layer offset to transform time.
    pub layer_offset: Option<LayerOffset>,
}

/// Represents a reference and all its meta data.
///
/// A reference is expressed on a prim in a given layer and it identifies a
/// prim in a layer stack. All opinions in the namespace hierarchy
/// under the referenced prim will be composed with the opinions in the
/// namespace hierarchy under the referencing prim.
#[derive(Debug, Default)]
pub struct Reference {
    /// The asset path to the external layer.
    pub asset_path: String,
    /// The path to the referenced prim in the external layer.
    pub prim_path: Path,
    /// The layer offset to transform time.
    pub layer_offset: LayerOffset,
    /// The custom data associated with the reference.
    pub custom_data: HashMap<String, Value>,
}

/// Value type representing a list-edit operation.
///
/// `ListOp`` is a value type representing an operation that edits a list.
/// It may add or remove items, reorder them, or replace the list entirely.
#[derive(Default, Debug)]
pub struct ListOp<T: Default> {
    pub explicit: bool,
    pub explicit_items: Vec<T>,
    pub added_items: Vec<T>,
    pub prepended_items: Vec<T>,
    pub appended_items: Vec<T>,
    pub deleted_items: Vec<T>,
    pub ordered_items: Vec<T>,
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
    fn get(&mut self, path: &Path, field: &str) -> Result<Value>;

    /// Returns the names of the fields for the given path.
    fn list(&self, path: &Path) -> Option<Vec<String>>;
}
