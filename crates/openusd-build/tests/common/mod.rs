//! What the generator's integration tests share.
//!
//! Each test binary compiles this module whole and uses part of it, which is
//! what the allow is for: an item is dead only from where one test stands.
#![allow(dead_code)]

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

/// The libraries in dependency order, each generated from
/// `crates/openusd-schemas/schemas/<library>/schema.usda`.
///
/// `usd` is the core family: it declares the roots every other library
/// inherits from, and `openusd` carries its views rather than generating them.
pub const LIBRARIES: &[&str] = &[
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
pub fn schemas() -> PathBuf {
    PathBuf::from(env!("CARGO_WORKSPACE_DIR")).join("crates/openusd-schemas/schemas")
}

/// A builder that resolves every library, since one library's classes inherit
/// from another's: `usdLux`'s light filters are `usdGeom` xformables.
///
/// The Rust path each library's views live at is the one `openusd-schemas`
/// gives them, so a base resolved here is named as that crate would name it.
pub fn configured() -> openusd_build::Builder {
    let mut builder = openusd_build::configure().search_path(schemas());
    for library in LIBRARIES.iter().filter(|library| **library != "usd") {
        let family = library.trim_start_matches("usd").to_lowercase();
        builder = builder.extern_library(*library, format!("crate::{family}"));
    }
    builder
}

/// Compares generated text against the file that records it, or rewrites that
/// file when asked to.
///
/// Run a test using this with `UPDATE_EXPECTED=1` to rewrite what it compares
/// against, then read the diff before committing it: a change to any of it — a
/// doc comment, a token, the shape of a declaration — shows up as a reviewable
/// diff rather than as silence, which is what makes the output something a
/// contributor can be held to.
pub fn matches(expected: &Path, generated: &str) {
    if env::var_os("UPDATE_EXPECTED").is_some() {
        fs::write(expected, generated).expect("writes the expected file");
        return;
    }

    let named = expected.file_name().unwrap_or(expected.as_os_str()).to_string_lossy();
    let want = fs::read_to_string(expected).unwrap_or_else(|_| {
        panic!(
            "{} is missing; run the test with UPDATE_EXPECTED=1 to write it",
            expected.display()
        )
    });

    // Compared line by line, so a mismatch names the line rather than printing
    // two whole files at each other.
    for (number, (want, got)) in want.lines().zip(generated.lines()).enumerate() {
        assert_eq!(want, got, "{named} differs at line {}", number + 1);
    }
    assert_eq!(
        want.lines().count(),
        generated.lines().count(),
        "{named} differs in length"
    );
}
