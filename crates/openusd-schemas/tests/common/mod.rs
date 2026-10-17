//! Helpers the schema-family integration tests share.

use std::fs;
use std::path::Path;

use openusd::Result;
use openusd::usd::Stage;

/// A stage opened from `asset`, a path beneath the workspace's `vendor`
/// directory.
#[allow(dead_code, reason = "only the families whose tests open vendor assets call it")]
pub fn vendor(asset: &str) -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(
            Path::new(env!("CARGO_WORKSPACE_DIR"))
                .join("vendor")
                .join(asset)
                .to_str()
                .expect("utf-8 asset path"),
        )
}

/// A stage opened from `usda` source, for the scenes a fixture does not carry.
pub fn from_usda(usda: &str) -> Result<Stage> {
    // Persist the tempdir so it outlives the stage; the process exits at test
    // end, so the OS reclaims it.
    let path = tempfile::tempdir()?.keep().join("scene.usda");
    fs::write(&path, usda)?;
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(path.to_str().unwrap())
}
