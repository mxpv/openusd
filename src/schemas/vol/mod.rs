//! UsdVol schema reader + authoring.
//!
//! Decodes and authors Pixar's `UsdVol` family - renderable volumes built
//! from file-backed fields:
//! - [`tokens::T_VOLUME`] (a `Gprim`) aggregates named fields via
//!   `field:<name>` relationships, each targeting a field prim.
//! - [`tokens::T_OPENVDB_ASSET`] / [`tokens::T_FIELD3D_ASSET`] are the
//!   concrete field prims (an OpenVDB grid / a Field3D file), sharing the
//!   `FieldAsset` attributes (filePath / fieldName / fieldIndex /
//!   fieldDataType / vectorDataRoleHint).
//!
//! The newer `ParticleField*` schemas (Gaussian-splat volumes) are a
//! separate, larger subsystem and are not covered here.

pub mod tokens;

mod author;
mod read;
mod types;

pub use author::{
    define_field3d_asset, define_openvdb_asset, define_volume, Field3dAssetAuthor, FieldAssetSetters,
    OpenVdbAssetAuthor, VolumeAuthor,
};
pub use read::{read_field3d_asset, read_openvdb_asset, read_volume};
pub use types::{ReadField3dAsset, ReadFieldAsset, ReadOpenVdbAsset, ReadVolume, VectorDataRoleHint};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;
    use crate::usd::Stage;
    use anyhow::Result;

    #[test]
    fn volume_with_fields_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_volume(&stage, sdf::path("/V")?)?
            .add_field("density", sdf::path("/V/density")?)?
            .add_field("temperature", sdf::path("/V/temperature")?)?;

        let v = read_volume(&stage, &sdf::path("/V")?)?.expect("Volume");
        assert_eq!(
            v.fields,
            vec![
                ("density".to_string(), "/V/density".to_string()),
                ("temperature".to_string(), "/V/temperature".to_string()),
            ],
        );
        Ok(())
    }

    #[test]
    fn openvdb_asset_roundtrip() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_openvdb_asset(&stage, sdf::path("/V/density")?)?
            .set_file_path("./smoke.vdb")?
            .set_field_name("density")?
            .set_field_index(0)?
            .set_field_data_type("float")?
            .set_vector_data_role_hint(VectorDataRoleHint::NoRole)?
            .set_field_class("fogVolume")?;

        let a = read_openvdb_asset(&stage, &sdf::path("/V/density")?)?.expect("OpenVDBAsset");
        assert_eq!(a.base.file_path.as_deref(), Some("./smoke.vdb"));
        assert_eq!(a.base.field_name.as_deref(), Some("density"));
        assert_eq!(a.base.field_index, Some(0));
        assert_eq!(a.base.field_data_type.as_deref(), Some("float"));
        assert_eq!(a.field_class.as_deref(), Some("fogVolume"));
        Ok(())
    }

    #[test]
    fn field3d_asset_and_type_gate() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_field3d_asset(&stage, sdf::path("/V/vel")?)?
            .set_field_data_type("float3")?
            .set_vector_data_role_hint(VectorDataRoleHint::Vector)?
            .set_field_purpose("motion")?;

        let a = read_field3d_asset(&stage, &sdf::path("/V/vel")?)?.expect("Field3DAsset");
        assert_eq!(a.base.vector_data_role_hint, VectorDataRoleHint::Vector);
        assert_eq!(a.field_purpose.as_deref(), Some("motion"));

        // Cross-type gating: an OpenVDBAsset reader rejects a Field3DAsset.
        assert!(read_openvdb_asset(&stage, &sdf::path("/V/vel")?)?.is_none());
        Ok(())
    }
}
