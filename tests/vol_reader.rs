//! Integration test for the `UsdVol` schema readers against a fixture.

use anyhow::Result;

use openusd::schemas::vol::{read_field3d_asset, read_openvdb_asset, read_volume};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdVol_scene.usda";

#[test]
fn reads_volume_and_fields_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;

    let v = read_volume(&stage, &sdf::path("/Smoke")?)?.expect("Volume");
    assert_eq!(
        v.fields,
        vec![
            ("density".to_string(), "/Smoke/density".to_string()),
            ("temperature".to_string(), "/Smoke/temperature".to_string()),
        ],
    );

    let vdb = read_openvdb_asset(&stage, &sdf::path("/Smoke/density")?)?.expect("OpenVDBAsset");
    assert_eq!(vdb.base.file_path.as_deref(), Some("./smoke.vdb"));
    assert_eq!(vdb.base.field_data_type.as_deref(), Some("float"));
    assert_eq!(vdb.field_class.as_deref(), Some("fogVolume"));

    let f3d = read_field3d_asset(&stage, &sdf::path("/Smoke/temperature")?)?.expect("Field3DAsset");
    assert_eq!(f3d.base.field_name.as_deref(), Some("temperature"));
    assert_eq!(f3d.field_purpose.as_deref(), Some("heat"));

    // A Volume isn't a field asset.
    assert!(read_openvdb_asset(&stage, &sdf::path("/Smoke")?)?.is_none());
    Ok(())
}
