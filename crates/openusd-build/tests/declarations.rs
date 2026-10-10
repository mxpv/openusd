//! A declaration-only family, generated and then compiled.
//!
//! A plugin may declare kinds and have no schema library, and the generator
//! writes it a file holding a `SCHEMAS` with no schema in it. Comparing that
//! file as text cannot tell whether it compiles or registers, so
//! `declarations/generated.rs` is the file the generator writes for the
//! `tinyKinds` plugin of `fixtures/tiny/plugInfo.json`, committed and compiled
//! into this test, and registered here.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite the committed file, then read the
//! diff before committing it. It takes two runs: the first writes the file the
//! second compiles.

use std::path::Path;

use openusd::usd;

mod common;

/// The file the generator writes for the plugin, compiled.
mod generated {
    include!("declarations/generated.rs");
}

/// The committed file is what the generator writes, and a registry built from
/// it knows the plugin's kinds.
#[test]
fn compiled_family_registers() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let output = openusd_build::configure()
        .plug_info(manifest.join("fixtures/tiny/plugInfo.json"))
        .build_declarations("tinyKinds")
        .expect("the plugin generates");
    common::matches(&manifest.join("tests/declarations/generated.rs"), &output.rust);

    assert_eq!(generated::SCHEMAS.name(), "tinyKinds");
    assert!(generated::SCHEMAS.schemas().is_empty());

    let registry = usd::SchemaRegistry::builder()
        .register(generated::SCHEMAS)
        .build()
        .expect("the compiled family registers");
    let kinds = registry.kinds();
    assert!(kinds.is_assembly("tinyCrowd") && kinds.is_group("tinyCrowd"));
    assert!(kinds.is_component("tinyProp") && !kinds.is_group("tinyProp"));
    assert!(kinds.has_kind("tinyMarker") && !kinds.is_model("tinyMarker"));
    assert_eq!(kinds.base_kind("tinyMarker"), None, "an empty baseKind is no base");
    // The plugin beside it in the file belongs to another family.
    assert!(!kinds.has_kind("tinyGroup"));
    // A kinds-only family brings no schema with it.
    assert_eq!(
        registry.schema_infos().count(),
        usd::SchemaRegistry::global().schema_infos().count()
    );
}
