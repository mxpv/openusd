//! Integration test for the `UsdVol` schema views against a fixture.

use anyhow::Result;

use openusd::schemas::vol::{self, FieldAsset};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdVol_scene.usda";

#[test]
fn volume_and_fields_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;

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
    assert_eq!(vdb.field_data_type_attr().get::<String>()?.as_deref(), Some("float"));
    assert_eq!(vdb.field_class_attr().get::<String>()?.as_deref(), Some("fogVolume"));

    let f3d = vol::Field3DAsset::get(&stage, sdf::path("/Smoke/temperature")?)?.expect("Field3DAsset");
    assert_eq!(f3d.field_name_attr().get::<String>()?.as_deref(), Some("temperature"));
    assert_eq!(f3d.field_purpose_attr().get::<String>()?.as_deref(), Some("heat"));

    // A Volume isn't a field asset.
    assert!(vol::OpenVDBAsset::get(&stage, sdf::path("/Smoke")?)?.is_none());
    Ok(())
}
