//! The UsdVol prim views: [`Volume`] and the file-backed field assets
//! [`OpenVDBAsset`] / [`Field3DAsset`].

use anyhow::{bail, Result};

use crate::sdf;
use crate::usd::{Attribute, Prim, Relationship, Stage};

use super::impl_vol_schema;
use super::tokens as tok;
use crate::schemas::common::get_typed;

/// A renderable volume (C++ `UsdVolVolume`) — a
/// [`geom::Gprim`](crate::schemas::geom::Gprim) that aggregates any number of
/// named fields. Each field is a `field:<name>` relationship targeting a
/// [`FieldAsset`](super::FieldAsset)-derived prim.
#[derive(Clone, derive_more::Deref)]
pub struct Volume(Prim);

impl Volume {
    /// Author a `def Volume` prim at `path` (C++ `UsdVolVolume::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_VOLUME)?))
    }

    /// Wrap `path` as a `Volume` if it is typed `Volume`
    /// (C++ `UsdVolVolume::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_VOLUME).map(|o| o.map(Self))
    }

    /// Handle to the `field:<name>` relationship binding the field `name` to a
    /// field prim (C++ `UsdVolVolume::GetFieldRelationship`).
    pub fn field_rel(&self, name: &str) -> Relationship {
        self.relationship(format!("{}{name}", tok::NS_FIELD))
    }

    /// Bind field `name` to the field prim at `target`, authoring the
    /// `field:<name>` relationship (C++ `UsdVolVolume::CreateFieldRelationship`).
    /// `name` must be non-empty, otherwise the property name would end in a
    /// colon (`field:`), which is not a valid USD property name.
    pub fn create_field_relationship(self, name: &str, target: impl Into<sdf::Path>) -> Result<Self> {
        if name.is_empty() {
            bail!("Volume field name must not be empty");
        }
        self.create_relationship(format!("{}{name}", tok::NS_FIELD))?
            .set_custom(false)?
            .add_target(target.into())?;
        Ok(self)
    }

    /// `true` when a `field:<name>` relationship is authored on this volume
    /// (C++ `UsdVolVolume::HasFieldRelationship`).
    pub fn has_field_relationship(&self, name: &str) -> Result<bool> {
        let rel = self.path().append_property(format!("{}{name}", tok::NS_FIELD))?;
        Ok(!self.stage().relationship(rel).targets()?.is_empty())
    }

    /// The volume's `(field name, target prim path)` bindings, sorted by field
    /// name (C++ `UsdVolVolume::GetFieldPaths`).
    pub fn field_paths(&self) -> Result<Vec<(String, sdf::Path)>> {
        let mut fields = Vec::new();
        for name in self.stage().prim(self.path().clone()).property_names()? {
            let Some(field_name) = name.strip_prefix(tok::NS_FIELD) else {
                continue;
            };
            let rel = self.path().append_property(&name)?;
            if let Some(target) = self.stage().relationship(rel).targets()?.into_iter().next() {
                fields.push((field_name.to_string(), target));
            }
        }
        fields.sort();
        Ok(fields)
    }
}

impl_vol_schema!(gprim Volume);

/// A field backed by an OpenVDB grid (C++ `UsdVolOpenVDBAsset`) — a
/// [`FieldAsset`](super::FieldAsset) adding the OpenVDB grid class.
#[derive(Clone, derive_more::Deref)]
pub struct OpenVDBAsset(Prim);

impl OpenVDBAsset {
    /// Author a `def OpenVDBAsset` prim at `path`
    /// (C++ `UsdVolOpenVDBAsset::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_OPENVDB_ASSET)?))
    }

    /// Wrap `path` as an `OpenVDBAsset` if it is typed `OpenVDBAsset`
    /// (C++ `UsdVolOpenVDBAsset::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_OPENVDB_ASSET).map(|o| o.map(Self))
    }

    /// The OpenVDB grid class — how the voxels are interpreted: `fogVolume`
    /// (dense data), `levelSet` (a signed-distance surface), `staggered` (a MAC
    /// grid), or `unknown`. C++ `UsdVolOpenVDBAsset::GetFieldClassAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<Token>()?`.
    pub fn field_class_attr(&self) -> Attribute {
        self.attribute(tok::A_FIELD_CLASS)
    }

    /// Author `fieldClass` (`uniform token`) (C++ `CreateFieldClassAttr`).
    pub fn create_field_class_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FIELD_CLASS, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_vol_schema!(field_asset OpenVDBAsset);

/// A field backed by a Field3D file (C++ `UsdVolField3DAsset`) — a
/// [`FieldAsset`](super::FieldAsset) adding the optional field purpose.
#[derive(Clone, derive_more::Deref)]
pub struct Field3DAsset(Prim);

impl Field3DAsset {
    /// Author a `def Field3DAsset` prim at `path`
    /// (C++ `UsdVolField3DAsset::Define`).
    pub fn define(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Self> {
        Ok(Self(stage.define_prim(path)?.set_type_name(tok::T_FIELD3D_ASSET)?))
    }

    /// Wrap `path` as a `Field3DAsset` if it is typed `Field3DAsset`
    /// (C++ `UsdVolField3DAsset::Get`).
    pub fn get(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Option<Self>> {
        get_typed(stage, path, tok::T_FIELD3D_ASSET).map(|o| o.map(Self))
    }

    /// An optional token marking the field's purpose or grouping within a
    /// Field3D file. C++ `UsdVolField3DAsset::GetFieldPurposeAttr`.
    ///
    /// Type `uniform token`. Fetch with `get::<Token>()?`.
    pub fn field_purpose_attr(&self) -> Attribute {
        self.attribute(tok::A_FIELD_PURPOSE)
    }

    /// Author `fieldPurpose` (`uniform token`) (C++ `CreateFieldPurposeAttr`).
    pub fn create_field_purpose_attr(&self) -> Result<Attribute> {
        Ok(self
            .create_attribute(tok::A_FIELD_PURPOSE, "token")?
            .set_custom(false)?
            .set_variability(sdf::Variability::Uniform)?)
    }
}

impl_vol_schema!(field_asset Field3DAsset);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::vol::{FieldAsset, VectorDataRoleHint};
    use crate::tf::Token;

    #[test]
    fn volume_fields_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        Volume::define(&stage, "/V")?
            .create_field_relationship("density", sdf::path("/V/density")?)?
            .create_field_relationship("temperature", sdf::path("/V/temperature")?)?;

        let v = Volume::get(&stage, "/V")?.expect("Volume");
        assert!(v.has_field_relationship("density")?);
        assert_eq!(
            v.field_paths()?,
            vec![
                ("density".to_string(), sdf::path("/V/density")?),
                ("temperature".to_string(), sdf::path("/V/temperature")?),
            ],
        );
        Ok(())
    }

    #[test]
    fn openvdb_asset_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let a = OpenVDBAsset::define(&stage, "/V/density")?;
        a.create_file_path_attr()?
            .set(sdf::Value::AssetPath("./smoke.vdb".into()))?;
        a.create_field_name_attr()?.set(sdf::Value::token("density"))?;
        a.create_field_index_attr()?.set(0)?;
        a.create_field_data_type_attr()?.set(sdf::Value::token("float"))?;
        a.create_vector_data_role_hint_attr()?.set(VectorDataRoleHint::NoRole)?;
        a.create_field_class_attr()?.set(sdf::Value::token("fogVolume"))?;

        let a = OpenVDBAsset::get(&stage, "/V/density")?.expect("OpenVDBAsset");
        assert_eq!(a.field_name_attr().get::<Token>()?.as_deref(), Some("density"));
        assert_eq!(a.field_index_attr().get::<i32>()?, Some(0));
        assert_eq!(
            a.vector_data_role_hint_attr().get::<VectorDataRoleHint>()?,
            Some(VectorDataRoleHint::NoRole)
        );
        assert_eq!(a.field_class_attr().get::<Token>()?.as_deref(), Some("fogVolume"));
        Ok(())
    }

    #[test]
    fn field3d_asset_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let a = Field3DAsset::define(&stage, "/V/vel")?;
        a.create_field_data_type_attr()?.set(sdf::Value::token("float3"))?;
        a.create_vector_data_role_hint_attr()?.set(VectorDataRoleHint::Vector)?;
        a.create_field_purpose_attr()?.set(sdf::Value::token("motion"))?;

        let a = Field3DAsset::get(&stage, "/V/vel")?.expect("Field3DAsset");
        assert_eq!(
            a.vector_data_role_hint_attr().get::<VectorDataRoleHint>()?,
            Some(VectorDataRoleHint::Vector)
        );
        assert_eq!(a.field_purpose_attr().get::<Token>()?.as_deref(), Some("motion"));

        // Cross-type gating: an OpenVDBAsset view rejects a Field3DAsset.
        assert!(OpenVDBAsset::get(&stage, "/V/vel")?.is_none());
        Ok(())
    }

    #[test]
    fn create_field_rejects_empty() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let result = Volume::define(&stage, "/V")?.create_field_relationship("", sdf::path("/V/density")?);
        assert!(result.is_err());
        Ok(())
    }
}
