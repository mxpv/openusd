//! The core `usd` family that `openusd` itself carries.
//!
//! `openusd` cannot generate it at build time — this crate depends on it, so a
//! build script there would be a cycle — and it cannot be left ungenerated
//! either, since a second hand-written copy of the same schemas is a copy that
//! drifts. So it is generated once, committed into `openusd`, and checked here.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite it from what the generator currently
//! produces, then read the diff before committing it.

use std::path::{Path, PathBuf};
use std::sync::LazyLock;

use openusd_build::Views;

mod common;

/// The vendored definitions, which live with the crate that sublayers them
/// rather than being copied a second time into `openusd`.
fn schema() -> PathBuf {
    PathBuf::from(env!("CARGO_WORKSPACE_DIR")).join("crates/openusd-schemas/schemas/usd/schema.usda")
}

/// The committed file, which is `openusd`'s own source.
fn generated() -> PathBuf {
    PathBuf::from(env!("CARGO_WORKSPACE_DIR")).join("crates/openusd/src/usd/core_schemas.rs")
}

/// The core family, generated once for both tests below.
fn built() -> &'static openusd_build::Output {
    static ONCE: LazyLock<openusd_build::Output> = LazyLock::new(|| {
        openusd_build::configure()
            .search_path(schema().parent().and_then(Path::parent).expect("the schemas root"))
            .build_library(schema(), Views::Skip)
            .expect("the core definitions build")
    });
    &ONCE
}

/// What `openusd` carries is what this generator makes of the vendored
/// definitions.
///
/// The views are left out: `openusd::usd` writes its own by hand, and a
/// generated set beside them would collide.
#[test]
fn core_family_is_generated() {
    let output = built();

    assert_eq!(output.library_name(), "usd");
    assert!(!output.views, "the core family's views are hand-written");

    common::matches(&generated(), &output.rust);
}

/// The root C++ registers through `plugInfo.json`, which the vendored
/// definitions declare in its place, reaches the generated family.
#[test]
fn schema_base_is_root() {
    let bases = built().with_family(|family| {
        family
            .schemas()
            .iter()
            .map(|decl| {
                let bases: Vec<String> = decl.declared_bases().iter().map(|base| (*base).to_owned()).collect();
                (decl.identifier().to_owned(), bases)
            })
            .collect::<Vec<_>>()
    });

    let base_of = |identifier: &str| {
        let found = bases.iter().find(|(name, _)| name == identifier);
        found.unwrap_or_else(|| panic!("{identifier} is declared")).1.clone()
    };
    assert!(base_of("SchemaBase").is_empty(), "the root derives from nothing");
    assert_eq!(base_of("Typed"), vec!["SchemaBase"]);
    assert_eq!(base_of("APISchemaBase"), vec!["SchemaBase"]);
    assert_eq!(base_of("CollectionAPI"), vec!["APISchemaBase"]);
}
