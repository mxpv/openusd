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

mod list_op;

pub use list_op::ListOp;

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

