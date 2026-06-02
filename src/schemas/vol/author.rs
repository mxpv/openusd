//! Authoring for the [UsdVol](super) schema family.

use anyhow::{bail, Result};

use crate::sdf::Path;
use crate::usd::{Prim, Stage};

use crate::schemas::common::{author_asset, author_int, author_rel_targets, author_token};
use crate::schemas::vol::tokens::*;
use crate::schemas::vol::types::VectorDataRoleHint;

/// Shared setters for the `FieldAsset` attributes, mixed into the
/// `OpenVDBAsset` / `Field3DAsset` author handles.
pub trait FieldAssetSetters: Sized {
    /// Borrow the underlying prim handle.
    fn prim(&self) -> &Prim;

    /// Set `filePath` (`asset`). The UsdVol schema declares this animatable,
    /// so it is authored varying to allow time-sampled volume file sequences.
    fn set_file_path(self, value: impl Into<String>) -> Result<Self> {
        author_asset(self.prim().stage(), self.prim().path(), A_FILE_PATH, value)?;
        Ok(self)
    }

    /// Set `fieldName` (`token`).
    fn set_field_name(self, value: impl Into<String>) -> Result<Self> {
        author_token(self.prim().stage(), self.prim().path(), A_FIELD_NAME, value)?;
        Ok(self)
    }

    /// Set `fieldIndex` (`int`).
    fn set_field_index(self, value: i32) -> Result<Self> {
        author_int(self.prim().stage(), self.prim().path(), A_FIELD_INDEX, value)?;
        Ok(self)
    }

    /// Set `fieldDataType` (`token`).
    fn set_field_data_type(self, value: impl Into<String>) -> Result<Self> {
        author_token(self.prim().stage(), self.prim().path(), A_FIELD_DATA_TYPE, value)?;
        Ok(self)
    }

    /// Set `vectorDataRoleHint` (`token`).
    fn set_vector_data_role_hint(self, value: VectorDataRoleHint) -> Result<Self> {
        author_token(
            self.prim().stage(),
            self.prim().path(),
            A_VECTOR_DATA_ROLE_HINT,
            value.as_token(),
        )?;
        Ok(self)
    }
}

/// Author a `def Volume` prim at `path`. Returns a chainable [`VolumeAuthor`].
pub fn define_volume(stage: &Stage, path: impl Into<Path>) -> Result<VolumeAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_VOLUME)?;
    Ok(VolumeAuthor { prim })
}

pub struct VolumeAuthor {
    prim: Prim,
}

impl VolumeAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Associate field `name` with the `FieldAsset` prim at `target`,
    /// authoring the `field:<name>` relationship. `name` must be non-empty,
    /// otherwise the property name would end in a colon (`field:`), which is
    /// not a valid USD property name.
    pub fn add_field(self, name: &str, target: impl Into<Path>) -> Result<Self> {
        if name.is_empty() {
            bail!("Volume field name must not be empty");
        }
        author_rel_targets(
            self.prim.stage(),
            self.prim.path(),
            &format!("{NS_FIELD}{name}"),
            [target.into()],
        )?;
        Ok(self)
    }
}

/// Author a `def OpenVDBAsset` prim at `path`. Returns a chainable
/// [`OpenVdbAssetAuthor`] with the shared [`FieldAssetSetters`].
pub fn define_openvdb_asset(stage: &Stage, path: impl Into<Path>) -> Result<OpenVdbAssetAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_OPENVDB_ASSET)?;
    Ok(OpenVdbAssetAuthor { prim })
}

pub struct OpenVdbAssetAuthor {
    prim: Prim,
}

impl OpenVdbAssetAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `fieldClass` (`token`) - the OpenVDB grid class.
    pub fn set_field_class(self, value: impl Into<String>) -> Result<Self> {
        author_token(self.prim.stage(), self.prim.path(), A_FIELD_CLASS, value)?;
        Ok(self)
    }
}

impl FieldAssetSetters for OpenVdbAssetAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}

/// Author a `def Field3DAsset` prim at `path`. Returns a chainable
/// [`Field3dAssetAuthor`] with the shared [`FieldAssetSetters`].
pub fn define_field3d_asset(stage: &Stage, path: impl Into<Path>) -> Result<Field3dAssetAuthor> {
    let prim = stage.define_prim(path)?.set_type_name(T_FIELD3D_ASSET)?;
    Ok(Field3dAssetAuthor { prim })
}

pub struct Field3dAssetAuthor {
    prim: Prim,
}

impl Field3dAssetAuthor {
    pub fn into_prim(self) -> Prim {
        self.prim
    }

    /// Set `fieldPurpose` (`token`).
    pub fn set_field_purpose(self, value: impl Into<String>) -> Result<Self> {
        author_token(self.prim.stage(), self.prim.path(), A_FIELD_PURPOSE, value)?;
        Ok(self)
    }
}

impl FieldAssetSetters for Field3dAssetAuthor {
    fn prim(&self) -> &Prim {
        &self.prim
    }
}
