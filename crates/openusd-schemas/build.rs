//! Generates the views for every schema family this build enables.
//!
//! A family's definitions are the vendored `schemas/<library>/schema.usda`,
//! and what comes out is what `src/<family>/mod.rs` includes: the views, and
//! the schema data its `register` hands a registry. A family that is not
//! enabled generates nothing, so a build with no features writes no files at
//! all.

use std::env;
use std::path::Path;

/// The families this crate exposes, each as the Cargo feature that enables it
/// and the library its definitions declare.
///
/// The Rust path a library's views live at is what a *later* library inherits
/// through: `usdLux`'s lights are `usdGeom` xformables, so generating the lux
/// views needs to know where the geom ones are. Every family is named for
/// that, whether or not this build generates it, since the feature graph is
/// what keeps a view from deriving from a module that is not there.
const FAMILIES: &[(&str, &str)] = &[
    ("geom", "usdGeom"),
    ("lux", "usdLux"),
    ("media", "usdMedia"),
    ("physics", "usdPhysics"),
    ("proc", "usdProc"),
    ("render", "usdRender"),
    ("shade", "usdShade"),
    ("skel", "usdSkel"),
    ("ui", "usdUI"),
    ("vol", "usdVol"),
];

fn main() {
    let schemas = Path::new("schemas");
    let mut builder = openusd_build::configure().search_path(schemas);
    for (family, library) in FAMILIES {
        builder = builder.extern_library(*library, format!("crate::{family}"));
    }

    for (family, library) in FAMILIES {
        if env::var_os(format!("CARGO_FEATURE_{}", family.to_uppercase())).is_some() {
            builder = builder.schema(schemas.join(library).join("schema.usda"));
        }
    }

    if let Err(error) = builder.generate() {
        panic!("generating schema views: {error}");
    }
}
