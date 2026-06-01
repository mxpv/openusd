//! Integration test for the `UsdProc` schema reader against a fixture.

use anyhow::Result;

use openusd::schemas::proc::read_generative_procedural;
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdProc_scene.usda";

#[test]
fn reads_generative_procedural_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    let p = read_generative_procedural(&stage, &sdf::path("/World/Scatter")?)?.expect("GenerativeProcedural");
    assert_eq!(p.procedural_system.as_deref(), Some("Houdini"));

    // A non-GenerativeProcedural prim reads back as None.
    assert!(read_generative_procedural(&stage, &sdf::path("/World")?)?.is_none());
    Ok(())
}
