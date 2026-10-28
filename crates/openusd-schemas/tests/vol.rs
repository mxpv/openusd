//! Integration test for the `UsdVol` schema views against a fixture.

use std::collections::BTreeMap;

use openusd::{Result, vt};

use openusd::gf;
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::{self, Stage};
use openusd_schemas::SchemaError;
use openusd_schemas::geom;
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
        BTreeMap::from([
            ("density".to_string(), sdf::path("/Smoke/density")?),
            ("temperature".to_string(), sdf::path("/Smoke/temperature")?),
        ]),
    );

    let vdb = vol::OpenVDBAsset::get(&stage, sdf::path("/Smoke/density")?)?.expect("OpenVDBAsset");
    assert_eq!(
        vdb.file_path_attr().get::<vt::Value>()?,
        Some(vt::Value::AssetPath("./smoke.vdb".into()))
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
    a.create_field_data_type_attr()?.set(vt::Value::token("float3"))?;
    a.create_vector_data_role_hint_attr()?.set(VectorDataRoleHint::Vector)?;
    a.create_field_purpose_attr()?.set(vt::Value::token("motion"))?;

    let a = Field3DAsset::get(&stage, "/V/vel")?.expect("Field3DAsset");
    assert_eq!(a.vector_data_role_hint()?, Some(VectorDataRoleHint::Vector));
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
        .set(vt::Value::AssetPath("./smoke.vdb".into()))?;
    a.create_field_name_attr()?.set(vt::Value::token("density"))?;
    a.create_field_index_attr()?.set(0)?;
    a.create_field_data_type_attr()?.set(vt::Value::token("float"))?;
    a.create_vector_data_role_hint_attr()?.set(VectorDataRoleHint::NoRole)?;
    a.create_field_class_attr()?.set(vt::Value::token("fogVolume"))?;

    let a = OpenVDBAsset::get(&stage, "/V/density")?.expect("OpenVDBAsset");
    assert_eq!(a.field_name_attr().get::<Token>()?.as_deref(), Some("density"));
    assert_eq!(a.field_index()?, Some(0));
    assert_eq!(a.vector_data_role_hint()?, Some(VectorDataRoleHint::NoRole));
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

/// An applied schema that reflects another offers the view through it as a
/// prim type does: the position attribute API is one method from the base API
/// its data comes from, over the same prim.
#[test]
fn attribute_api_reflects_base() -> Result<()> {
    let stage = memory()?;
    let splat = vol::ParticleField3DGaussianSplat::define(&stage, "/Splat")?;
    let positions = vol::ParticleFieldPositionAttributeAPI::apply(&splat)?;

    let base: vol::ParticleFieldPositionBaseAPI = positions.particle_field_position_base_api();
    assert_eq!(base.path(), splat.path());
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

/// `testUsdVolVolume.py:test_VolumeFieldManagement`: bindings composed through
/// a reference, blocked and re-established on the referencing prim.
#[test]
fn field_rels_referenced() -> Result<(), SchemaError> {
    let stage = memory()?;
    geom::Xform::define(&stage, "/base")?;
    let vol = vol::Volume::define(&stage, "/base/volume")?;
    let f1 = Field3DAsset::define(&stage, "/base/volume/f3dField")?;
    let f2 = OpenVDBAsset::define(&stage, "/base/volume/vdbField")?;
    vol.create_field_rel("diffuse", f1.path().clone())?
        .create_field_rel("emissive", f2.path().clone())?;

    stage.define_prim("/volModel")?.references().add(sdf::Reference {
        prim_path: sdf::path("/base")?,
        ..Default::default()
    })?;
    let ref_vol = vol::Volume::get(&stage, "/volModel/volume")?.expect("Volume");
    let diffuse = ("diffuse".to_string(), sdf::path("/volModel/volume/f3dField")?);
    let emissive = ("emissive".to_string(), sdf::path("/volModel/volume/vdbField")?);
    let specular = ("specular".to_string(), sdf::path("/no/such/prim")?);
    assert!(ref_vol.has_field_rel("diffuse")?);
    assert_eq!(ref_vol.field_path("diffuse")?.as_ref(), Some(&diffuse.1));
    assert_eq!(
        ref_vol.field_paths()?,
        BTreeMap::from([diffuse.clone(), emissive.clone()])
    );

    // A block drops the binding but not the relationship.
    assert!(ref_vol.block_field_rel("diffuse")?);
    assert_eq!(ref_vol.field_paths()?, BTreeMap::from([emissive.clone()]));
    assert_eq!(ref_vol.field_path("diffuse")?, None);
    assert!(ref_vol.has_field_rel("diffuse")?);
    assert!(!ref_vol.block_field_rel("unbound")?, "nothing to block");

    // A target need not exist.
    let ref_vol = ref_vol.create_field_rel("specular", specular.1.clone())?;
    assert_eq!(
        ref_vol.field_paths()?,
        BTreeMap::from([emissive.clone(), specular.clone()])
    );
    assert!(ref_vol.has_field_rel("specular")?);

    // Re-establish diffuse locally.
    let ref_vol = ref_vol.create_field_rel("diffuse", diffuse.1.clone())?;
    assert_eq!(ref_vol.field_paths()?, BTreeMap::from([diffuse, emissive, specular]));
    Ok(())
}

/// A second create replaces the targets, and the relationship is the
/// caller's own.
#[test]
fn create_field_replaces() -> Result<(), SchemaError> {
    let stage = memory()?;
    let volume = vol::Volume::define(&stage, "/V")?
        .create_field_rel("density", "/V/a")?
        .create_field_rel("density", "/V/b")?;
    let rel = volume.field_rel("density");
    assert_eq!(rel.targets()?, [sdf::path("/V/b")?]);
    assert!(rel.is_custom()?);
    Ok(())
}

/// A field binds a prim or a property directly on one; a relational attribute
/// or a target path is refused before anything is authored.
#[test]
fn field_target_rejected() -> Result<(), SchemaError> {
    let stage = memory()?;
    let volume = vol::Volume::define(&stage, "/V")?;
    for target in ["/V/f.rel[/T].attr", "/V/f.rel[/T]"] {
        let result = volume.clone().create_field_rel("density", target);
        assert!(
            matches!(&result, Err(SchemaError::FieldTarget { path }) if path.as_str() == target),
            "{target}: {result:?}"
        );
        assert!(!volume.has_field_rel("density")?, "{target} authored nothing");
    }
    let volume = volume.create_field_rel("density", "/V/f.grid")?;
    assert_eq!(volume.field_rel("density").targets()?, [sdf::path("/V/f.grid")?]);
    // A property is a target, but not a bound prim.
    assert_eq!(volume.field_path("density")?, None);
    Ok(())
}
