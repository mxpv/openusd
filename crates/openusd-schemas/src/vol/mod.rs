//! UsdVol schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdVol` family — renderable volumes built from file-backed fields. The
//! views build on the [`geom`](crate::geom) trait chain: a
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
//! The newer `ParticleField*` schemas (Gaussian-splat volumes) are a separate,
//! larger subsystem and are not covered here.
//!
//! # Example
//!
//! ```
//! use openusd_schemas::vol::{self, FieldAsset};
//! use openusd::{sdf, usd};
//!
//! let stage = usd::Stage::builder().in_memory("scene.usda").unwrap();
//!
//! // A field is a file-backed grid prim; `create_file_path_attr` is inherited
//! // from the `FieldAsset` interface.
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

pub mod tokens;

mod schema;
mod traits;

use openusd::tf;

pub use schema::{Field3DAsset, OpenVDBAsset, Volume};
pub use traits::{FieldAsset, FieldBase};

use tokens::*;

/// Implement the schema-trait chain for a concrete `struct $ty(Prim)` vol
/// newtype. Every arm hand-writes the one `SchemaBase` method (`prim`) and adds
/// the empty membership impls for the chain it names; all trait paths are fully
/// qualified, so the call site only needs the macro in scope.
///
/// - `gprim` is a [`geom::Gprim`](crate::geom::Gprim) (`Volume`).
/// - `field_asset` adds [`FieldBase`] + [`FieldAsset`] on top of
///   [`geom::Xformable`](crate::geom::Xformable) (`OpenVDBAsset`,
///   `Field3DAsset`).
macro_rules! impl_vol_schema {
    (@base $ty:ident) => {
        impl $crate::openusd::usd::SchemaBase for $ty {
            const KIND: $crate::openusd::usd::SchemaKind = $crate::openusd::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::openusd::usd::Prim {
                &self.0
            }
        }
        impl $crate::geom::Imageable for $ty {}
        impl $crate::geom::Xformable for $ty {}
    };
    (gprim $ty:ident) => {
        impl_vol_schema!(@base $ty);
        impl $crate::geom::Boundable for $ty {}
        impl $crate::geom::Gprim for $ty {}
    };
    (field_asset $ty:ident) => {
        impl_vol_schema!(@base $ty);
        impl $crate::vol::FieldBase for $ty {}
        impl $crate::vol::FieldAsset for $ty {}
    };
}

pub(crate) use impl_vol_schema;

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
            VectorDataRoleHint::NoRole => ROLE_NONE,
            VectorDataRoleHint::Point => ROLE_POINT,
            VectorDataRoleHint::Normal => ROLE_NORMAL,
            VectorDataRoleHint::Vector => ROLE_VECTOR,
            VectorDataRoleHint::Color => ROLE_COLOR,
        }
    }

    pub fn from_token(token: impl Into<tf::Token>) -> Option<Self> {
        Some(match token.into().as_str() {
            ROLE_NONE => VectorDataRoleHint::NoRole,
            ROLE_POINT => VectorDataRoleHint::Point,
            ROLE_NORMAL => VectorDataRoleHint::Normal,
            ROLE_VECTOR => VectorDataRoleHint::Vector,
            ROLE_COLOR => VectorDataRoleHint::Color,
            _ => return None,
        })
    }
}

// `From`/`TryFrom<Value>` so the hint passes straight to `Attribute::set` and
// `get::<VectorDataRoleHint>()`.
crate::common::impl_token_value!(VectorDataRoleHint);
