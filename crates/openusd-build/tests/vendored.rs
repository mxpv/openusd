//! The eleven schema libraries OpenUSD ships, generated from the definitions
//! `openusd-schemas` vendors.
//!
//! What the tiny fixture proves about shape, this proves about scale: every
//! kind of declaration upstream actually writes, over six hundred classes, and
//! a registry that answers across all of them at once.

use std::path::PathBuf;

use openusd::tf;
use openusd::usd::{FamilySource, SchemaRegistryBuilder};

/// The libraries in dependency order, each generated from
/// `crates/openusd-schemas/schemas/<library>/schema.usda`.
const LIBRARIES: &[&str] = &[
    "usd",
    "usdGeom",
    "usdLux",
    "usdMedia",
    "usdPhysics",
    "usdProc",
    "usdRender",
    "usdShade",
    "usdSkel",
    "usdUI",
    "usdVol",
];

/// Where the vendored definitions live.
fn schemas() -> PathBuf {
    PathBuf::from(env!("CARGO_WORKSPACE_DIR")).join("crates/openusd-schemas/schemas")
}

/// A builder that resolves every library, since one library's classes inherit
/// from another's: `usdLux`'s light filters are `usdGeom` xformables.
fn configured() -> openusd_build::Builder {
    let mut builder = openusd_build::configure().search_path(schemas());
    for library in LIBRARIES.iter().filter(|library| **library != "usd") {
        let family = library.trim_start_matches("usd").to_lowercase();
        builder = builder.extern_library(*library, format!("crate::{family}"));
    }
    builder
}

/// Every library generates, and the eleven compose into one registry: no
/// declaration this crate cannot represent, no name it cannot mint, no
/// collision between the names it does, and a family for each.
///
/// One test, because generating the eleven is the expensive part and both
/// questions are about the same output.
#[test]
fn every_library_builds_and_registers() {
    let dir = schemas();
    let mut builder = SchemaRegistryBuilder::empty();

    for library in LIBRARIES {
        let output = configured()
            .build_library(dir.join(library).join("schema.usda"))
            .unwrap_or_else(|error| panic!("{library}: {error}"));

        assert_eq!(&output.library_name, library);
        assert!(output.rust.is_some(), "{library} generates views");

        builder = builder
            .family(FamilySource {
                name: library,
                manifest: &output.manifest,
                schematics: &output.schematics,
            })
            .unwrap_or_else(|error| panic!("{library}: {error}"));
    }

    let registry = builder.build().expect("the eleven compose");
    let named = |name: &str| tf::Token::from(name);
    assert!(registry.is_a(&named("Sphere"), &named("Gprim")), "a sphere is a gprim");
    assert!(
        registry.is_a(&named("Mesh"), &named("Imageable")),
        "across three levels"
    );
    assert!(
        registry.is_a(&named("SphereLight"), &named("Xformable")),
        "and across libraries"
    );
}
