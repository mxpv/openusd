//! The ten domain families against the schema data OpenUSD generates for them.
//!
//! This is the only oracle in the workspace that this crate did not produce.
//! Everything else compares one of its outputs against another — the compiled
//! table against the lowering it came from, a golden file against the emitter
//! that wrote it — so a mistake made once in the lowering appears on both sides
//! and neither notices. Upstream's own `generatedSchema.usda` was written by a
//! different program from a different source, and a stage composed against
//! these declarations has to behave like one composed against it.
//!
//! The baselines under `fixtures/upstream/` are copied verbatim from upstream
//! and this test never writes them; re-vendoring is what a version bump does.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::path::Path;

use openusd::sdf::{self, AbstractData};
use openusd_build::Views;

mod common;

/// Every spec a store holds and every field on it, valued.
///
/// Four things are left out, each a place upstream's file and this crate's
/// declarations differ by design: the `documentation` neither registry reads,
/// the layer comment naming whichever generator wrote the file, and the two
/// children keys, because the two order properties differently — upstream keeps
/// the order the schema declared them in, while this crate takes the composed
/// order, which is `sdf::element_cmp`. Nothing resolves a value through that
/// order, so it is a divergence rather than a defect.
fn specs(data: &dyn AbstractData) -> BTreeMap<sdf::Path, BTreeMap<String, sdf::Value>> {
    const APART: [&str; 4] = [
        sdf::FieldKey::Documentation.as_str(),
        sdf::FieldKey::Comment.as_str(),
        sdf::ChildrenKey::PrimChildren.as_str(),
        sdf::ChildrenKey::PropertyChildren.as_str(),
    ];

    data.spec_paths()
        .into_iter()
        .map(|path| {
            let fields = data
                .list_fields(&path)
                .unwrap_or_default()
                .into_iter()
                .filter(|field| !APART.contains(&field.as_str()))
                .filter_map(|field| {
                    let value = data.try_field(&path, &field).ok().flatten().map(Cow::into_owned)?;
                    let value = match field == sdf::FieldKey::CustomData.as_str() {
                        true => emitted_custom_data(value)?,
                        false => value,
                    };
                    Some((field, value))
                })
                .collect();
            (path, fields)
        })
        .collect()
}

/// A spec's `customData` less the brief user documentation upstream carries and
/// this crate drops, `None` once nothing else is left in it — an emptied
/// dictionary meaning the same as an absent one.
fn emitted_custom_data(value: sdf::Value) -> Option<sdf::Value> {
    let mut custom_data = value.try_as_dictionary()?;
    custom_data.remove("userDocBrief");
    (!custom_data.is_empty()).then_some(sdf::Value::Dictionary(custom_data))
}

/// The upstream test corpus, whose own baseline covers what the shipped
/// libraries do not: an API schema restricted per instance, a codeless
/// library, a schema declaring fallback types.
#[test]
fn matches_upstream_corpus() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/testUsdGenSchema");
    let output = openusd_build::configure()
        .search_path(&dir)
        .build_library(dir.join("schema.usda"), Views::Skip)
        .expect("the corpus builds");

    let ours = output.with_family(|family| specs(&family.to_data().expect("the declarations build")));
    let baseline = dir.join("baseline/basic/generatedSchema.usda");
    let baseline = sdf::Layer::open(baseline.to_string_lossy()).expect("the vendored baseline");
    let theirs = specs(baseline.data());

    let missing: Vec<&sdf::Path> = theirs.keys().filter(|path| !ours.contains_key(*path)).collect();
    let extra: Vec<&sdf::Path> = ours.keys().filter(|path| !theirs.contains_key(*path)).collect();
    assert!(missing.is_empty(), "upstream has specs we do not: {missing:?}");
    assert!(extra.is_empty(), "we have specs upstream does not: {extra:?}");
    assert!(theirs.len() > 100, "the whole corpus: {}", theirs.len());

    for (path, fields) in &theirs {
        assert_eq!(&ours[path], fields, "{path} is not what upstream generates");
    }
}

/// Each family carries the same class prims, with the same properties and the
/// same values, as OpenUSD generates for it.
#[test]
fn matches_upstream_schema_data() {
    let baselines = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/upstream");
    let generator = common::configured();

    // Only the schema data is compared, so the views are not generated: they
    // are two thirds of what emitting a family costs and nothing here reads
    // them. `vendored.rs` is what holds them to their own rules.
    let mut compared = 0;
    for library in common::LIBRARIES.iter().filter(|library| **library != "usd") {
        let output = generator
            .build_library(common::schemas().join(library).join("schema.usda"), Views::Skip)
            .unwrap_or_else(|error| panic!("{library}: {error}"));

        let ours = output.with_family(|family| specs(&family.to_data().expect("the declarations build")));

        let baseline = baselines.join(library).join("generatedSchema.usda");
        let baseline = sdf::Layer::open(baseline.to_string_lossy()).expect("the vendored baseline");
        let theirs = specs(baseline.data());

        let missing: Vec<&sdf::Path> = theirs.keys().filter(|path| !ours.contains_key(*path)).collect();
        let extra: Vec<&sdf::Path> = ours.keys().filter(|path| !theirs.contains_key(*path)).collect();
        assert!(
            missing.is_empty(),
            "{library}: upstream has specs we do not: {missing:?}"
        );
        assert!(
            extra.is_empty(),
            "{library}: we have specs upstream does not: {extra:?}"
        );
        assert!(!theirs.is_empty(), "{library}: the baseline carries the family");

        for (path, fields) in &theirs {
            assert_eq!(&ours[path], fields, "{library}: {path} is not what upstream generates");
        }
        compared += theirs.len();
    }
    assert!(compared > 500, "the whole corpus: {compared}");
}
