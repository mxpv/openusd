//! The eleven schema libraries OpenUSD ships, generated from the definitions
//! `openusd-schemas` vendors.
//!
//! What the tiny fixture proves about shape, this proves about scale: every
//! kind of declaration upstream actually writes, over six hundred classes, and
//! a registry that answers across all of them at once.

use openusd::tf;
use openusd::usd::SchemaRegistryBuilder;
use openusd_build::Views;

mod common;

use common::{LIBRARIES, configured, schemas};

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
            .build_library(dir.join(library).join("schema.usda"), Views::Generate)
            .unwrap_or_else(|error| panic!("{library}: {error}"));

        assert_eq!(output.library_name(), *library);
        assert!(output.views, "{library} generates views");

        builder = output.with_family(|family| builder.register(family));
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
