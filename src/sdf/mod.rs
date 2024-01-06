//! Scene description foundations.

use strum::{Display, EnumCount, FromRepr};

mod path;

pub use path::Path;

/// An enum that specifies the type of an object.
/// Objects are entities that have fields and are addressable by path.
#[repr(u32)]
#[derive(Default, Clone, Copy, PartialEq, Eq, FromRepr, EnumCount, Display)]
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
