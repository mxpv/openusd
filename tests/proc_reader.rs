//! Integration test for the UsdProc schema views against a fixture.

use anyhow::Result;

use openusd::schemas::proc::GenerativeProcedural;
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdProc_scene.usda";

#[test]
fn generative_procedural_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    let p = GenerativeProcedural::get(&stage, sdf::path("/World/Scatter")?)?.expect("GenerativeProcedural");
    assert_eq!(p.procedural_system_attr().get::<Token>()?.as_deref(), Some("Houdini"));

    // A non-GenerativeProcedural prim reads back as None.
    assert!(GenerativeProcedural::get(&stage, sdf::path("/World")?)?.is_none());
    Ok(())
}
