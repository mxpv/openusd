//! What a small shader-definition layer generates, kept as a file beside it.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite the expected file from what the
//! generator currently produces, then read the diff before committing it.

use std::path::{Path, PathBuf};

mod common;

/// The fixture directory, which holds the definitions and what they generate.
fn nodes() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/nodes")
}

/// The whole of what the node library generates.
#[test]
fn node_library() {
    let output = openusd_build::configure()
        .extern_library("usdShade", "crate::shade")
        .build_shader_defs("tinyNodes", nodes().join("shaderDefs.usda"))
        .expect("the fixture generates");

    common::matches(&nodes().join("expected.rs"), &output.rust);
}

/// A node's view wraps `usdShade`'s `Shader`, so nothing can be generated
/// until that library is placed.
#[test]
fn unplaced_shade_refused() {
    let error = openusd_build::configure()
        .build_shader_defs("tinyNodes", nodes().join("shaderDefs.usda"))
        .expect_err("usdShade is not placed");
    assert!(
        matches!(&error, openusd_build::Error::ShaderDefs { cause, .. } if cause.contains("usdShade")),
        "{error}"
    );
}
