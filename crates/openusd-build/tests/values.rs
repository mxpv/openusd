//! What a generated value expression rebuilds, against the value it came from.
//!
//! Every other test reads the emitter's output as text, so an expression that
//! names a type wrongly, loses a component, or does not compile at all reads as
//! a pass. This one compiles it: `values/generated.rs` is the table the
//! generator writes for `fixtures/values/schema.usda`, committed and compiled
//! into this test, and what its expressions rebuild is compared against the
//! values the model carries for the same schema.
//!
//! The fixture is where a value shape earns coverage — it declares a fallback
//! of every kind the generator supports, including the ones with no literal: a
//! blocked default, a dictionary holding values of its own, matrices under
//! three different `gf` names, a half, an asset path and an infinity.
//!
//! The table is generated without views: what is under test is the value
//! expressions, and a view per schema beside them would be noise.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite the committed table, then read the
//! diff before committing it. It takes two runs — the first writes the file the
//! second compiles.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use openusd::sdf;
use openusd_build::Views;

mod common;

/// The table the generator writes for the fixture, compiled.
#[allow(
    dead_code,
    reason = "the table names every property of the fixture; this reads the values, not the names"
)]
mod generated {
    include!("values/generated.rs");
}

fn fixture() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/values")
}

/// Every field of every spec, which for this fixture is every value shape.
fn fields(data: &sdf::Data) -> BTreeMap<String, sdf::Value> {
    data.iter()
        .flat_map(|(path, spec)| {
            spec.fields
                .iter()
                .map(move |(field, value)| (format!("{path}.{field}"), value.clone()))
        })
        .collect()
}

/// The generated expressions rebuild the values the model holds.
///
/// Both sides reach a value a different way: the model's came from composing
/// the schema, and the table's from Rust the emitter wrote and the compiler
/// built. A mistake in [`emit::value`](openusd_build) shows up as a difference
/// between them, which reading the emitted text cannot see.
#[test]
fn compiled_values_match_the_model() {
    let output = openusd_build::configure()
        .search_path(fixture())
        .build_library(fixture().join("schema.usda"), Views::Skip)
        .expect("the values fixture builds");

    common::matches(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/values/generated.rs"),
        &output.rust,
    );

    let from_model = output.with_family(|family| fields(&family.to_data().expect("the declarations build")));
    let from_table = fields(&generated::SCHEMAS.to_data().expect("the compiled table builds"));

    assert_eq!(
        from_table.keys().collect::<Vec<_>>(),
        from_model.keys().collect::<Vec<_>>(),
        "the two carry the same fields"
    );
    for (field, value) in &from_model {
        assert_eq!(&from_table[field], value, "{field} does not rebuild");
    }

    // The fixture exists to reach the shapes with no literal, so a run that
    // stopped covering them would pass having proved nothing.
    let kinds: Vec<sdf::ValueKind> = from_model.values().map(sdf::ValueKind::from).collect();
    for expected in [
        sdf::ValueKind::ValueBlock,
        sdf::ValueKind::Dictionary,
        sdf::ValueKind::Matrix2d,
        sdf::ValueKind::Matrix3d,
        sdf::ValueKind::Matrix4d,
        sdf::ValueKind::Half,
        sdf::ValueKind::Quath,
        sdf::ValueKind::TimeCode,
        sdf::ValueKind::AssetPath,
    ] {
        assert!(kinds.contains(&expected), "the fixture declares a {expected:?}");
    }
}
