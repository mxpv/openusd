//! Authoring for the [UsdVol](super) schema family.

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::{Prim, Stage};

use crate::schemas::common::{author_rel_targets, author_uniform_token};
use crate::schemas::vol::tokens::*;
use crate::schemas::vol::types::VectorDataRoleHint;

/// Shared setters for the `FieldAsset` attributes, mixed into the
/// `OpenVDBAsset` / `Field3DAsset` author handles.
pub trait FieldAssetSetters<'s>: Sized {
    /// Borrow the underlying prim handle.
    fn prim(&self) -> &Prim<'s>;

    /// Set `filePath` (`uniform asset`).
    fn set_file_path(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_asset(self.prim().stage(), self.prim().path(), A_FILE_PATH, value.into())?;
        Ok(self)
    }

    /// Set `fieldName` (`uniform token`).
    fn set_field_name(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim().stage(), self.prim().path(), A_FIELD_NAME, value)?;
        Ok(self)
    }

    /// Set `fieldIndex` (`uniform int`).
    fn set_field_index(self, value: i32) -> Result<Self> {
        author_uniform_int(self.prim().stage(), self.prim().path(), A_FIELD_INDEX, value)?;
        Ok(self)
    }

    /// Set `fieldDataType` (`uniform token`).
    fn set_field_data_type(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim().stage(), self.prim().path(), A_FIELD_DATA_TYPE, value)?;
        Ok(self)
    }

    /// Set `vectorDataRoleHint` (`uniform token`).
    fn set_vector_data_role_hint(self, value: VectorDataRoleHint) -> Result<Self> {
        author_uniform_token(
            self.prim().stage(),
            self.prim().path(),
            A_VECTOR_DATA_ROLE_HINT,
            value.as_token(),
        )?;
        Ok(self)
    }
}

/// Author a `def Volume` prim at `path`. Returns a chainable [`VolumeAuthor`].
pub fn define_volume<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<VolumeAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_VOLUME)?;
    Ok(VolumeAuthor { prim })
}

pub struct VolumeAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> VolumeAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Associate field `name` with the `FieldAsset` prim at `target`,
    /// authoring the `field:<name>` relationship.
    pub fn add_field(self, name: &str, target: impl Into<Path>) -> Result<Self> {
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
pub fn define_openvdb_asset<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<OpenVdbAssetAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_OPENVDB_ASSET)?;
    Ok(OpenVdbAssetAuthor { prim })
}

pub struct OpenVdbAssetAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> OpenVdbAssetAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `fieldClass` (`uniform token`) - the OpenVDB grid class.
    pub fn set_field_class(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_FIELD_CLASS, value)?;
        Ok(self)
    }
}

impl<'s> FieldAssetSetters<'s> for OpenVdbAssetAuthor<'s> {
    fn prim(&self) -> &Prim<'s> {
        &self.prim
    }
}

/// Author a `def Field3DAsset` prim at `path`. Returns a chainable
/// [`Field3dAssetAuthor`] with the shared [`FieldAssetSetters`].
pub fn define_field3d_asset<'s>(stage: &'s Stage, path: impl Into<Path>) -> Result<Field3dAssetAuthor<'s>> {
    let prim = stage.define_prim(path)?.set_type_name(T_FIELD3D_ASSET)?;
    Ok(Field3dAssetAuthor { prim })
}

pub struct Field3dAssetAuthor<'s> {
    prim: Prim<'s>,
}

impl<'s> Field3dAssetAuthor<'s> {
    pub fn into_prim(self) -> Prim<'s> {
        self.prim
    }

    /// Set `fieldPurpose` (`uniform token`).
    pub fn set_field_purpose(self, value: impl Into<String>) -> Result<Self> {
        author_uniform_token(self.prim.stage(), self.prim.path(), A_FIELD_PURPOSE, value)?;
        Ok(self)
    }
}

impl<'s> FieldAssetSetters<'s> for Field3dAssetAuthor<'s> {
    fn prim(&self) -> &Prim<'s> {
        &self.prim
    }
}

fn author_uniform_asset(stage: &Stage, prim: &Path, name: &str, value: String) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "asset")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::AssetPath(value))?;
    Ok(())
}

fn author_uniform_int(stage: &Stage, prim: &Path, name: &str, value: i32) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "int")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Int(value))?;
    Ok(())
}
