//! Integration test for the UsdProc schema views against a fixture.

use openusd::Result;

use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::Stage;
use openusd_schemas::geom::BoundableSchema;
use openusd_schemas::proc::{GenerativeProcedural, GenerativeProceduralSchema};

const FIXTURE: &str = "fixtures/usdProc_scene.usda";

#[test]
fn generative_procedural_from_fixture() -> Result<()> {
    let stage = Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)?;
    let p = GenerativeProcedural::get(&stage, sdf::path("/World/Scatter")?)?.expect("GenerativeProcedural");
    assert_eq!(p.procedural_system_attr().get::<Token>()?.as_deref(), Some("Houdini"));

    // A non-GenerativeProcedural prim reads back as None.
    assert!(GenerativeProcedural::get(&stage, sdf::path("/World")?)?.is_none());
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
fn generative_procedural_roundtrip() -> Result<()> {
    let stage = memory()?;
    let p = GenerativeProcedural::define(&stage, "/World/Proc")?;
    p.create_procedural_system_attr()?
        .set(sdf::Value::Token("Houdini".into()))?;

    let p = GenerativeProcedural::get(&stage, "/World/Proc")?.expect("GenerativeProcedural");
    assert_eq!(
        p.procedural_system_attr().get::<sdf::Value>()?,
        Some(sdf::Value::Token("Houdini".into()))
    );
    // Inherited Boundable accessor is available on the handle.
    assert_eq!(p.extent_attr().get::<sdf::Value>()?, None);
    assert!(GenerativeProcedural::get(&stage, "/Missing")?.is_none());
    Ok(())
}

#[test]
fn get_rejects_non_procedural() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/NotProc")?.set_type_name("Scope")?;
    assert!(GenerativeProcedural::get(&stage, "/NotProc")?.is_none());
    Ok(())
}
