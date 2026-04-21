//! Round-trip tests for the USDC binary writer.
//!
//! For each `.usdc` fixture: parse, emit, re-parse, assert both in-memory
//! layers are structurally equal.

use std::collections::BTreeMap;
use std::io::Cursor;
use std::path::Path;

use openusd::sdf::{self, path, AbstractData, ChildrenKey, Data, FieldKey, SpecType, Specifier, Value};
use openusd::usdc::{CrateData, CrateWriter};

fn snapshot(data: &dyn AbstractData) -> serde_json::Value {
    let mut out: BTreeMap<String, BTreeMap<String, sdf::Value>> = BTreeMap::new();
    for path in data.paths() {
        let mut fields: BTreeMap<String, sdf::Value> = BTreeMap::new();
        if let Some(names) = data.list(&path) {
            for name in names {
                let v = data.get(&path, &name).unwrap().into_owned();
                fields.insert(name, v);
            }
        }
        out.insert(path.to_string(), fields);
    }
    serde_json::to_value(&out).expect("serialize")
}

fn assert_roundtrip(usdc_path: &Path) {
    let file = std::fs::File::open(usdc_path).unwrap_or_else(|e| panic!("cannot open {}: {e}", usdc_path.display()));
    let original =
        CrateData::open(file, true).unwrap_or_else(|e| panic!("failed to parse {}: {e:#}", usdc_path.display()));

    let mut buf = Vec::new();
    {
        let mut cursor = Cursor::new(&mut buf);
        CrateWriter::write(&original as &dyn AbstractData, &mut cursor)
            .unwrap_or_else(|e| panic!("emit failed for {}: {e:#}", usdc_path.display()));
    }

    let round = CrateData::open(Cursor::new(&buf), true)
        .unwrap_or_else(|e| panic!("re-parse failed for {}: {e:#}", usdc_path.display()));

    let orig_json = snapshot(&original as &dyn AbstractData);
    let round_json = snapshot(&round as &dyn AbstractData);

    let diffs = diff_json::compare_values(&orig_json, &round_json);
    assert!(
        diffs.is_empty(),
        "round-trip mismatch for {}:\n{}",
        usdc_path.display(),
        diff_json::DiffFormatter::new().format(&diffs)
    );
}

macro_rules! binary_tests {
    ($($name:ident => $path:expr),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                assert_roundtrip(Path::new($path));
            }
        )*
    };
}

#[test]
fn compressed_int_array_roundtrips() {
    // Arrays of 4+ integers are emitted through `encode_ints` + LZ4 with
    // the compressed bit set. Anything shorter falls through to a raw POD
    // array. Cover both paths on the same layer.
    let mut data = Data::new();
    let root = sdf::Path::abs_root();
    let root_spec = data.create_spec(root.clone(), SpecType::PseudoRoot);
    root_spec.add(ChildrenKey::PrimChildren, Value::TokenVec(vec!["A".into()]));

    let prim = path("/A").unwrap();
    let prim_spec = data.create_spec(prim.clone(), SpecType::Prim);
    prim_spec.add(FieldKey::Specifier, Value::Specifier(Specifier::Def));
    prim_spec.add(FieldKey::TypeName, Value::Token("Scope".into()));
    prim_spec.add(
        ChildrenKey::PropertyChildren,
        Value::TokenVec(vec!["short".into(), "long".into()]),
    );

    let short_prop = prim.append_property("short").unwrap();
    let short_spec = data.create_spec(short_prop.clone(), SpecType::Attribute);
    short_spec.add(FieldKey::TypeName, Value::Token("int[]".into()));
    short_spec.add(FieldKey::Default, Value::IntVec(vec![1, 2, 3]));

    let long: Vec<i32> = (0..1000).collect();
    let long_prop = prim.append_property("long").unwrap();
    let long_spec = data.create_spec(long_prop.clone(), SpecType::Attribute);
    long_spec.add(FieldKey::TypeName, Value::Token("int[]".into()));
    long_spec.add(FieldKey::Default, Value::IntVec(long.clone()));

    let mut buf = Vec::new();
    CrateWriter::write(&data as &dyn AbstractData, &mut Cursor::new(&mut buf)).expect("write");

    // The 1000-i32 monotonic sequence is 4000 bytes raw. With delta+common
    // coding and LZ4 on top it collapses to a small constant. If this ever
    // regresses past a few hundred bytes, compression is silently broken.
    let raw_long_bytes = (long.len() * std::mem::size_of::<i32>()) as u64;
    assert!(
        (buf.len() as u64) < raw_long_bytes / 4,
        "int array did not compress: total file size {} bytes vs {} raw payload",
        buf.len(),
        raw_long_bytes
    );

    let round = CrateData::open(Cursor::new(&buf), true).expect("re-parse");
    let round_short = (&round as &dyn AbstractData)
        .get(&short_prop, "default")
        .unwrap()
        .into_owned();
    let round_long = (&round as &dyn AbstractData)
        .get(&long_prop, "default")
        .unwrap()
        .into_owned();
    assert_eq!(round_short, Value::IntVec(vec![1, 2, 3]));
    assert_eq!(round_long, Value::IntVec(long));
}

#[test]
fn empty_layer_roundtrips_through_crate_writer() {
    // `cross_empty` covers USDA -> USDC. Make sure a programmatically
    // constructed empty `Data` also writes and reads back successfully, as
    // the writer has conditional branches for empty path/token/field tables.
    let data = Data::new();
    let mut buf = Vec::new();
    CrateWriter::write(&data as &dyn AbstractData, &mut Cursor::new(&mut buf)).expect("empty layer write");

    let round = CrateData::open(Cursor::new(&buf), true).expect("empty layer re-parse");

    let orig_paths = (&data as &dyn AbstractData).paths();
    let round_paths = (&round as &dyn AbstractData).paths();
    assert_eq!(orig_paths, round_paths);

    let orig_json = snapshot(&data as &dyn AbstractData);
    let round_json = snapshot(&round as &dyn AbstractData);
    let diffs = diff_json::compare_values(&orig_json, &round_json);
    assert!(
        diffs.is_empty(),
        "empty-layer mismatch:\n{}",
        diff_json::DiffFormatter::new().format(&diffs)
    );
}

binary_tests! {
    binary_fields => "fixtures/fields.usdc",
    binary_floats => "fixtures/floats.usdc",
    binary_ints => "fixtures/ints.usdc",
    binary_connection => "fixtures/connection.usdc",
    binary_payload => "fixtures/payload.usdc",
    binary_reference => "fixtures/reference.usdc",
    binary_sdf_types => "fixtures/sdf_types.usdc",
    binary_expressions => "fixtures/expressions.usdc",
    binary_timesamples => "fixtures/timesamples.usdc",
}

// Vendor compliance suite.
const VENDOR: &str = "vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary";

macro_rules! vendor_tests {
    ($($name:ident),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                let file = format!("{}/{}.usdc", VENDOR, stringify!($name).trim_start_matches("vendor_"));
                assert_roundtrip(Path::new(&file));
            }
        )*
    };
}

vendor_tests! {
    vendor_gen_bool,
    vendor_gen_uchar,
    vendor_gen_int,
    vendor_gen_uint,
    vendor_gen_int64,
    vendor_gen_uint64,
    vendor_gen_half,
    vendor_gen_float,
    vendor_gen_double,
    vendor_gen_string,
    vendor_gen_token,
    vendor_gen_listops,
    vendor_gen_matrix2d,
    vendor_gen_matrix3d,
    vendor_gen_matrix4d,
    vendor_gen_permissions,
    vendor_gen_quatd,
    vendor_gen_quatf,
    vendor_gen_quath,
    vendor_gen_relocates,
    vendor_gen_timecodes,
    vendor_gen_timesamples,
    vendor_gen_variants,
    vendor_gen_vec2d,
    vendor_gen_vec2f,
    vendor_gen_vec2h,
    vendor_gen_vec2i,
    vendor_gen_vec3d,
    vendor_gen_vec3f,
    vendor_gen_vec3h,
    vendor_gen_vec3i,
    vendor_gen_vec4d,
    vendor_gen_vec4f,
    vendor_gen_vec4h,
    vendor_gen_vec4i,
    vendor_gen_vectors,
}

// Skipped fixtures — these fail during the *read* step, not during writing,
// and are therefore pre-existing reader-side limitations:
//
// - `gen_assetpath.usdc` / `gen_pathexpression.usdc`: reader has no branch for
//   `AssetPath[]` / `PathExpression[]` array ValueReps (hits
//   `Can't unpack array ... as inline value`).
// - `gen_dict.usdc`, `ball.maya.usdc`, `toy_biplane_idle.usdc`,
//   `fender_stratocaster.usdc`: reader explicitly bails on nested dictionaries
//   with `"Nested dictionaries are not supported"` in `read_custom_data`.
// - `gen_splines.usdc`: splines materialise as `Value::ValueVec`, which has no
//   USDC type code (the binary format lacks a heterogeneous-array type).
