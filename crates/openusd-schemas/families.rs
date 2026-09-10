// The families this crate exposes, shared by the build script that generates
// them and the test that checks what it generated.
//
// Included by both rather than declared as a module: `build.rs` is its own
// crate, so a module of the library is not reachable from it. Whatever
// configures the generator has to be the same on both sides — a test
// comparing against a differently-configured generator would be comparing the
// wrong thing — and one copy is how that is guaranteed. Both includers carry
// `use std::path::Path`, which is what `configured` names its argument by.

/// Each family as the Cargo feature that enables it and the library its
/// definitions declare.
///
/// The Rust path a library's views live at is what a *later* library inherits
/// through: `usdLux`'s lights are `usdGeom` xformables, so generating the lux
/// views needs to know where the geom ones are. Every family is named for
/// that, whether or not a build generates it, since the feature graph is what
/// keeps a view from deriving from a module that is not there.
const FAMILIES: [(&str, &str); 10] = [
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

/// A generator that resolves every family, whether or not this build generates
/// it, with `schemas` as the directory their sublayers resolve through.
fn configured(schemas: &Path) -> openusd_build::Builder {
    let mut builder = openusd_build::configure().search_path(schemas);
    for (family, library) in FAMILIES {
        builder = builder.extern_library(library, format!("crate::{family}"));
    }
    builder
}
