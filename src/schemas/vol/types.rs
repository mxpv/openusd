//! Decoded enum + read structs for the [UsdVol](super) schema family.

use super::tokens::*;

/// `vectorDataRoleHint` - the geometric role of a vector-valued field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VectorDataRoleHint {
    /// No role (the spec default).
    #[default]
    NoRole,
    Point,
    Normal,
    Vector,
    Color,
}

impl VectorDataRoleHint {
    pub fn as_token(self) -> &'static str {
        match self {
            VectorDataRoleHint::NoRole => ROLE_NONE,
            VectorDataRoleHint::Point => ROLE_POINT,
            VectorDataRoleHint::Normal => ROLE_NORMAL,
            VectorDataRoleHint::Vector => ROLE_VECTOR,
            VectorDataRoleHint::Color => ROLE_COLOR,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            ROLE_NONE => VectorDataRoleHint::NoRole,
            ROLE_POINT => VectorDataRoleHint::Point,
            ROLE_NORMAL => VectorDataRoleHint::Normal,
            ROLE_VECTOR => VectorDataRoleHint::Vector,
            ROLE_COLOR => VectorDataRoleHint::Color,
            _ => return None,
        })
    }
}

/// The `FieldAsset` attributes shared by `OpenVDBAsset` / `Field3DAsset`
/// (file-backed grid fields). `vectorDataRoleHint` defaults to `None`; the
/// rest have no spec default.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReadFieldAsset {
    /// `filePath` - the volume file on disk.
    pub file_path: Option<String>,
    /// `fieldName` - the field's name within the file.
    pub field_name: Option<String>,
    /// `fieldIndex` - disambiguates multiple fields sharing a name.
    pub field_index: Option<i32>,
    /// `fieldDataType` - the field's data type token.
    pub field_data_type: Option<String>,
    /// `vectorDataRoleHint` (default `None`).
    pub vector_data_role_hint: VectorDataRoleHint,
}

/// An `OpenVDBAsset` prim - a field backed by an OpenVDB grid.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReadOpenVdbAsset {
    /// The shared `FieldAsset` attributes.
    pub base: ReadFieldAsset,
    /// `fieldClass` - the OpenVDB grid class (`levelSet` / `fogVolume` / …).
    pub field_class: Option<String>,
}

/// A `Field3DAsset` prim - a field backed by a Field3D file.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReadField3dAsset {
    /// The shared `FieldAsset` attributes.
    pub base: ReadFieldAsset,
    /// `fieldPurpose` - optional grouping/purpose token.
    pub field_purpose: Option<String>,
}

/// A `Volume` prim - aggregates named fields via `field:<name>`
/// relationships, each targeting a `FieldAsset`-derived prim.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ReadVolume {
    /// `(field name, target prim path)` pairs, sorted by field name.
    pub fields: Vec<(String, String)>,
}
