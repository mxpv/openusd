//! Everything a small library generates, kept as files beside its schema.
//!
//! The unit tests assert one thing at a time about generated text; this asserts
//! all of it at once, by comparing whole files. A change to any of it — a doc
//! comment, a token, the shape of a constructor — shows up as a reviewable diff
//! rather than as silence, which is what makes the output something a
//! contributor can be held to.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite the expected file from what the
//! generator currently produces, then read the diff before committing it.

use std::path::{Path, PathBuf};

use openusd_build::Views;

mod common;

/// The fixture directory, which holds the schema and what it generates.
fn tiny() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/tiny")
}

/// The whole of what the tiny library generates.
#[test]
fn tiny_library() {
    let output = openusd_build::configure()
        .build_library(tiny().join("schema.usda"), Views::Generate)
        .expect("the fixture generates");

    assert_eq!(output.library_name(), "tiny");
    common::matches(&tiny().join("expected.rs"), &output.rust);
}
