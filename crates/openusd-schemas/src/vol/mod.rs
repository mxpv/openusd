//! UsdVol schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdVol` family — renderable volumes built from file-backed fields. The
//! views build on the [`geom`](crate::geom) chain: a
//! [`Volume`] is a [`geom::Gprim`](crate::geom::Gprim) and the field
//! prims are [`geom::Xformable`](crate::geom::Xformable).
//!
//! ```text
//! geom::Gprim
//!  └ Volume                          (field:<name> relationships)
//! geom::Xformable
//!  └ FieldBase           (abstract; a transformable single field)
//!     └ FieldAsset       (abstract; file-backed grid attributes)
//!        └ OpenVDBAsset / Field3DAsset
//! ```
//!
//! A [`Volume`] aggregates any number of named fields via `field:<name>`
//! relationships, each targeting a field prim. [`FieldAsset`] is the interface
//! carrying the shared file/grid attributes (`filePath` / `fieldName` /
//! `fieldIndex` / `fieldDataType` / `vectorDataRoleHint`); the concrete
//! [`OpenVDBAsset`] (an OpenVDB grid) and [`Field3DAsset`] (a Field3D file) add
//! their own `fieldClass` / `fieldPurpose`.
//!
//! The `ParticleField*` schemas (Gaussian-splat volumes) are generated beside
//! them; the subsystem that consumes them is not modelled here.
//!
//! # Example
//!
//! ```
//! use openusd_schemas::vol::{self, VolumeFieldAssetSchema, VolumeSchema};
//! use openusd::{sdf, usd};
//!
//! let stage = usd::Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda").unwrap();
//!
//! // A field is a file-backed grid prim; `create_file_path_attr` is inherited
//! // from `VolumeFieldAssetSchema`, the trait carrying the shared attributes.
//! let field = vol::OpenVDBAsset::define(&stage, "/Smoke/density").unwrap();
//! field.create_file_path_attr().unwrap().set(sdf::Value::AssetPath("./smoke.vdb".into())).unwrap();
//! field.create_field_name_attr().unwrap().set(sdf::Value::token("density")).unwrap();
//!
//! // A Volume binds named fields through `field:<name>` relationships.
//! let volume = vol::Volume::define(&stage, "/Smoke").unwrap()
//!     .create_field_relationship("density", "/Smoke/density").unwrap();
//!
//! assert_eq!(
//!     volume.field_paths().unwrap(),
//!     vec![("density".to_string(), sdf::path("/Smoke/density").unwrap())],
//! );
//! ```

openusd::include_schema!("usdVol");

mod volume;

pub use volume::FIELD_NAMESPACE;

use openusd::tf;
use tokens::*;

/// The geometric role of a vector-valued field (the `vectorDataRoleHint`
/// token). Per Pixar's spec the default (unauthored) is
/// [`VectorDataRoleHint::NoRole`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VectorDataRoleHint {
    /// No role (the spec default, authored as the token `None`).
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
            VectorDataRoleHint::NoRole => NONE_,
            VectorDataRoleHint::Point => POINT,
            VectorDataRoleHint::Normal => NORMAL,
            VectorDataRoleHint::Vector => VECTOR,
            VectorDataRoleHint::Color => COLOR,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            NONE_ => VectorDataRoleHint::NoRole,
            POINT => VectorDataRoleHint::Point,
            NORMAL => VectorDataRoleHint::Normal,
            VECTOR => VectorDataRoleHint::Vector,
            COLOR => VectorDataRoleHint::Color,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` so the hint passes straight to `Attribute::set` and
// `get::<VectorDataRoleHint>()`.
crate::token_value::impl_token_value!(VectorDataRoleHint);
