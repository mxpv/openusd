//! Integration test for the `UsdVol` schema views against a fixture.

use openusd::Result;

use openusd::gf;
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::{self, Stage};
use openusd_schemas::vol::{
    self, Field3DAsset, Field3DAssetSchema, OpenVDBAsset, OpenVDBAssetSchema, ParticleField3DGaussianSplatSchema,
    SplatData, VectorDataRoleHint, VolumeFieldAssetSchema,
};

const FIXTURE: &str = "fixtures/usdVol_scene.usda";

#[test]
fn volume_and_fields_from_fixture() -> Result<()> {
    let stage = Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)?;

    let v = vol::Volume::get(&stage, sdf::path("/Smoke")?)?.expect("Volume");
    assert_eq!(
        v.field_paths()?,
        vec![
            ("density".to_string(), sdf::path("/Smoke/density")?),
            ("temperature".to_string(), sdf::path("/Smoke/temperature")?),
        ],
    );

    let vdb = vol::OpenVDBAsset::get(&stage, sdf::path("/Smoke/density")?)?.expect("OpenVDBAsset");
    assert_eq!(
        vdb.file_path_attr().get::<sdf::Value>()?,
        Some(sdf::Value::AssetPath("./smoke.vdb".into()))
    );
    assert_eq!(vdb.field_data_type_attr().get::<Token>()?.as_deref(), Some("float"));
    assert_eq!(vdb.field_class_attr().get::<Token>()?.as_deref(), Some("fogVolume"));

    let f3d = vol::Field3DAsset::get(&stage, sdf::path("/Smoke/temperature")?)?.expect("Field3DAsset");
    assert_eq!(f3d.field_name_attr().get::<Token>()?.as_deref(), Some("temperature"));
    assert_eq!(f3d.field_purpose_attr().get::<Token>()?.as_deref(), Some("heat"));

    // A Volume isn't a field asset.
    assert!(vol::OpenVDBAsset::get(&stage, sdf::path("/Smoke")?)?.is_none());
    Ok(())
}

/// An in-memory stage carrying the schema data, which is what makes a prim its
/// type and resolves the fallbacks its schema declares.
fn memory() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")
}

#[test]
fn field3d_asset_and_type_gate() -> Result<()> {
    let stage = memory()?;
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
fn openvdb_asset_roundtrip() -> Result<()> {
    let stage = memory()?;
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

/// A splat stores each quantity twice over, at float and at half precision,
/// and which one carries the data is read off the data itself: the float
/// attribute where it holds anything, the half one otherwise.
#[test]
fn splat_prefers_authored_precision() -> Result<()> {
    let stage = memory()?;
    let splat = vol::ParticleField3DGaussianSplat::define(&stage, "/Splat")?;
    let in_use = |data| Ok::<_, openusd::Error>(splat.attribute_in_use(data)?.path().clone());

    // Nothing authored: the half attribute answers, holding nothing itself.
    assert_eq!(in_use(SplatData::Positions)?, sdf::path("/Splat.positionsh")?);
    assert!(!splat.uses_float(SplatData::Positions)?, "and says so as a bool");

    // An empty float array is no more authored than none at all.
    let positions = splat.create_positions_attr()?.set(Vec::<gf::Vec3f>::new())?;
    assert_eq!(in_use(SplatData::Positions)?, sdf::path("/Splat.positionsh")?);

    positions.set(vec![gf::vec3f(0.0, 1.0, 2.0)])?;
    assert_eq!(in_use(SplatData::Positions)?, sdf::path("/Splat.positions")?);

    // Each pair answers for itself.
    splat
        .create_scalesh_attr()?
        .set(vec![gf::vec3h(gf::f16::ONE, gf::f16::ONE, gf::f16::ONE)])?;
    assert_eq!(in_use(SplatData::Scales)?, sdf::path("/Splat.scalesh")?);
    Ok(())
}

/// The earliest time sample is what decides it, so a splat animated from an
/// empty first sample still reads as half-precision.
#[test]
fn splat_precision_at_earliest_time() -> Result<()> {
    let stage = memory()?;
    let splat = vol::ParticleField3DGaussianSplat::define(&stage, "/Splat")?;
    splat
        .create_positions_attr()?
        .set_at(Vec::<gf::Vec3f>::new(), usd::TimeCode::from(1.0))?
        .set_at(vec![gf::vec3f(0.0, 0.0, 0.0)], usd::TimeCode::from(2.0))?;

    assert!(!splat.uses_float(SplatData::Positions)?, "the earliest sample is empty");

    // The samples are what is read, not the default: the same shape with a
    // filled first sample answers the other way.
    let filled = vol::ParticleField3DGaussianSplat::define(&stage, "/Filled")?;
    filled
        .create_positions_attr()?
        .set_at(vec![gf::vec3f(0.0, 0.0, 0.0)], usd::TimeCode::from(1.0))?
        .set_at(Vec::<gf::Vec3f>::new(), usd::TimeCode::from(2.0))?;
    assert!(filled.uses_float(SplatData::Positions)?);
    Ok(())
}
