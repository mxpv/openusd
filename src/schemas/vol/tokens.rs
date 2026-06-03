//! Token constants for the [UsdVol](super) schema family.
//!
//! Mirrors Pixar's `pxr/usd/usdVol/tokens.h`.

// Concrete prim type names.
pub const T_VOLUME: &str = "Volume";
pub const T_OPENVDB_ASSET: &str = "OpenVDBAsset";
pub const T_FIELD3D_ASSET: &str = "Field3DAsset";

/// Relationship namespace prefix used by `Volume` to associate fields:
/// `field:<name>` targets a `FieldAsset`-derived prim.
pub const NS_FIELD: &str = "field:";

// FieldAsset attributes (shared by OpenVDBAsset / Field3DAsset).
pub const A_FILE_PATH: &str = "filePath";
pub const A_FIELD_NAME: &str = "fieldName";
pub const A_FIELD_INDEX: &str = "fieldIndex";
pub const A_FIELD_DATA_TYPE: &str = "fieldDataType";
pub const A_VECTOR_DATA_ROLE_HINT: &str = "vectorDataRoleHint";

// OpenVDBAsset / Field3DAsset specific attributes.
pub const A_FIELD_CLASS: &str = "fieldClass";
pub const A_FIELD_PURPOSE: &str = "fieldPurpose";

// `vectorDataRoleHint` token values.
pub const ROLE_NONE: &str = "None";
pub const ROLE_POINT: &str = "Point";
pub const ROLE_NORMAL: &str = "Normal";
pub const ROLE_VECTOR: &str = "Vector";
pub const ROLE_COLOR: &str = "Color";
