//! The UsdVol interface traits shared across the field views.
//!
//! [`FieldBase`] is the abstract base for a single volume field (C++
//! `UsdVolFieldBase`): a [`geom::Xformable`] prim. [`FieldAsset`] (C++
//! `UsdVolFieldAsset`) extends it with the attributes shared by the
//! file-backed fields ([`OpenVDBAsset`](super::OpenVDBAsset) /
//! [`Field3DAsset`](super::Field3DAsset)). Concrete views implement both
//! through the `impl_vol_schema!(field_asset ...)` macro arm.

use anyhow::Result;

use crate::schemas::geom;
use crate::usd::Attribute;

use super::tokens as tok;

/// The abstract base for a single volume field (C++ `UsdVolFieldBase`). A field
/// is a [`geom::Xformable`] prim, so it carries the full transform / visibility
/// surface; concrete fields are the file-backed [`FieldAsset`] grids.
pub trait FieldBase: geom::Xformable {}

/// The abstract base for a volume field stored as an asset on disk (C++
/// `UsdVolFieldAsset`), shared by [`OpenVDBAsset`](super::OpenVDBAsset) and
/// [`Field3DAsset`](super::Field3DAsset).
pub trait FieldAsset: FieldBase {
    /// The on-disk file holding this field's voxels (`.vdb` for
    /// [`OpenVDBAsset`](super::OpenVDBAsset), `.f3d` for
    /// [`Field3DAsset`](super::Field3DAsset)). Animatable via time samples.
    /// C++ `UsdVolFieldAsset::GetFilePathAttr`.
    ///
    /// Type `asset`. Fetch with `get::<sdf::AssetPath>()?`.
    fn file_path_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_FILE_PATH)
    }

    /// Author `filePath` (`asset`) (C++ `CreateFilePathAttr`). Authored varying
    /// to allow time-sampled volume file sequences.
    fn create_file_path_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_FILE_PATH, "asset")?
            .set_custom(false)?)
    }

    /// The name of the field to read from the file; one file often holds several
    /// (`density`, `temperature`, …). C++ `UsdVolFieldAsset::GetFieldNameAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<Token>()?`.
    fn field_name_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_FIELD_NAME)
    }

    /// Author `fieldName` (`uniform token`) (C++ `CreateFieldNameAttr`).
    fn create_field_name_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_FIELD_NAME, "token")?
            .set_custom(false)?
            .set_variability(crate::sdf::Variability::Uniform)?)
    }

    /// Disambiguates fields in the file that share the same `fieldName`; the
    /// index within that group. Left unauthored when the name alone is
    /// unambiguous. C++ `UsdVolFieldAsset::GetFieldIndexAttr`.
    ///
    /// Type `uniform int`. Fetch with `get::<i32>()?`.
    fn field_index_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_FIELD_INDEX)
    }

    /// Author `fieldIndex` (`uniform int`) (C++ `CreateFieldIndexAttr`).
    fn create_field_index_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_FIELD_INDEX, "int")?
            .set_custom(false)?
            .set_variability(crate::sdf::Variability::Uniform)?)
    }

    /// The value type of each voxel, telling a renderer how to read the grid
    /// (`float`, `double`, `float3`, `half`, …).
    /// C++ `UsdVolFieldAsset::GetFieldDataTypeAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<Token>()?`.
    fn field_data_type_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_FIELD_DATA_TYPE)
    }

    /// Author `fieldDataType` (`uniform token`) (C++ `CreateFieldDataTypeAttr`).
    fn create_field_data_type_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_FIELD_DATA_TYPE, "token")?
            .set_custom(false)?
            .set_variability(crate::sdf::Variability::Uniform)?)
    }

    /// For a vector-valued field, the role its vectors play so a renderer
    /// transforms them correctly (point / normal / vector / color). Meaningless
    /// for scalar fields. C++ `UsdVolFieldAsset::GetVectorDataRoleHintAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<`[`VectorDataRoleHint`](super::VectorDataRoleHint)`>()?`
    /// (defaults to [`VectorDataRoleHint::NoRole`](super::VectorDataRoleHint::NoRole)).
    fn vector_data_role_hint_attr(&self) -> Attribute {
        self.prim().attribute(tok::A_VECTOR_DATA_ROLE_HINT)
    }

    /// Author `vectorDataRoleHint` (`uniform token`)
    /// (C++ `CreateVectorDataRoleHintAttr`). Pass a
    /// [`VectorDataRoleHint`](super::VectorDataRoleHint) to `set`.
    fn create_vector_data_role_hint_attr(&self) -> Result<Attribute> {
        Ok(self
            .prim()
            .create_attribute(tok::A_VECTOR_DATA_ROLE_HINT, "token")?
            .set_custom(false)?
            .set_variability(crate::sdf::Variability::Uniform)?)
    }
}
