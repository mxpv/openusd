//! Everything a small library generates, kept as files beside its schema.
//!
//! The unit tests assert one thing at a time about generated text; this asserts
//! all of it at once, by comparing whole files. A change to any of it — a doc
//! comment, a token, the shape of a constructor — shows up as a reviewable diff
//! rather than as silence, which is what makes the output something a
//! contributor can be held to.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite the expected files from what the
//! generator currently produces, then read the diff before committing it.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// The fixture directory, which holds the schema and what it generates.
fn tiny() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/tiny")
}

/// Compares one generated file against the expected one beside the schema, or
/// rewrites it when asked to.
fn matches(name: &str, generated: &str) {
    let expected = tiny().join(name);
    if env::var_os("UPDATE_EXPECTED").is_some() {
        fs::write(&expected, generated).expect("writes the expected file");
        return;
    }

    let want = fs::read_to_string(&expected)
        .unwrap_or_else(|_| panic!("{name} is missing; run the test with UPDATE_EXPECTED=1 to write it"));
    // Compared line by line, so a mismatch names the line rather than printing
    // two whole files at each other.
    for (number, (want, got)) in want.lines().zip(generated.lines()).enumerate() {
        assert_eq!(want, got, "{name} differs at line {}", number + 1);
    }
    assert_eq!(
        want.lines().count(),
        generated.lines().count(),
        "{name} differs in length"
    );
}

/// The whole of what the tiny library generates.
#[test]
fn tiny_library() {
    let output = openusd_build::configure()
        .build_library(tiny().join("schema.usda"))
        .expect("the fixture generates");

    assert_eq!(output.library_name, "tiny");
    matches("expected.rs", output.rust.as_deref().expect("a library with views"));
    matches(
        "expected.schematics.usda",
        &output.schematics.export_to_string().expect("exports"),
    );
    matches(
        "expected.manifest.usda",
        &output.manifest.export_to_string().expect("exports"),
    );
}
