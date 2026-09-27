//! A schema reflected from another library, compiled.
//!
//! Reading the emitter's output as text cannot tell whether the path to a
//! borrowed view resolves, whether its constructor is reachable, or whether the
//! method that views the prim through it landed on the right item. This
//! compiles the two libraries `fixtures/reflect` declares — one holding a
//! single-apply API schema, one reflecting it from a prim type and from an
//! applied API schema — and drives the reflected accessors on a stage.
//!
//! `reflect/elsewhere.rs` and `reflect/here.rs` are what the generator writes
//! for the fixture, committed and compiled into this test; the reflecting
//! library is generated with the other placed at `crate::elsewhere`, which is
//! where this test declares it.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite the committed files, then read the
//! diff before committing them. It takes two runs — the first writes the
//! files the second compiles.

use std::path::{Path, PathBuf};

use openusd::usd::{SchemaRegistryBuilder, Stage};
use openusd_build::Views;

use crate::here::CrateSchema;

mod common;

/// The library holding the reflected schema, compiled.
#[allow(
    dead_code,
    reason = "the file carries every item of its library; this test reaches the reflected schema"
)]
mod elsewhere {
    include!("reflect/elsewhere.rs");
}

/// The library reflecting it, compiled.
#[allow(
    dead_code,
    reason = "the file carries every item of its library; this test reaches the reflecting classes"
)]
mod here {
    include!("reflect/here.rs");
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/reflect")
}

fn expected(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/reflect").join(name)
}

/// Both libraries generate as committed, and what was compiled from them
/// reaches the reflected schema: its accessors as the reflecting class's own,
/// and its view, from a prim type's trait and from an applied schema's view
/// alike, over the same prim.
#[test]
fn compiled_reflection() {
    let builder = openusd_build::configure()
        .search_path(fixture())
        .extern_library("testElsewhere", "crate::elsewhere");
    let elsewhere = builder
        .build_library(fixture().join("base.usda"), Views::Generate)
        .expect("the reflected library builds");
    let here = builder
        .build_library(fixture().join("schema.usda"), Views::Generate)
        .expect("the reflecting library builds");

    common::matches(&expected("elsewhere.rs"), &elsewhere.rust);
    common::matches(&expected("here.rs"), &here.rust);

    let registry = SchemaRegistryBuilder::empty()
        .register(elsewhere::SCHEMAS)
        .register(here::SCHEMAS)
        .build()
        .expect("the two families compose");
    let stage = Stage::builder()
        .schema_registry(registry)
        .in_memory("reflect.usda")
        .expect("a stage");

    // The reflected accessors author and read the schema's property as the
    // crate's own, and what they wrote is what the schema's own view reads.
    let crate_ = here::Crate::define(&stage, "/Crate").expect("defines a crate");
    crate_
        .create_weight_attr()
        .expect("authors the reflected attribute")
        .set(2.5)
        .expect("sets it");
    assert_eq!(crate_.weight_attr().get::<f64>().expect("reads"), Some(2.5));
    crate_.create_owner_rel().expect("authors the reflected relationship");

    let thing: elsewhere::ThingAPI = crate_.thing_api();
    assert_eq!(thing.path(), crate_.path());
    assert_eq!(thing.weight_attr().get::<f64>().expect("reads"), Some(2.5));

    // An applied schema that reflects offers the same view, inherent to it.
    let badge = here::BadgeAPI::apply(&crate_).expect("applies the badge");
    let through_badge: elsewhere::ThingAPI = badge.thing_api();
    assert_eq!(through_badge.path(), crate_.path());
    assert_eq!(badge.weight_attr().get::<f64>().expect("reads"), Some(2.5));
}
