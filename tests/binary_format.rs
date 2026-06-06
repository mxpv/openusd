//! Binary format compliance tests.
//!
//! The AOUSD compliance suite ships its binary-parser tests as inline
//! assertions in `file_formats/tests/test_binary.py` rather than as JSON
//! baselines (unlike the text suite). These tests backport those assertions
//! to Rust: each case reads the same `gen_*.usdc` fixture through `CrateData`
//! and asserts the composed `sdf::Value` matches the reference expectation.
//!
//! A few reference cases reach into parser internals (inline-vs-not encoding,
//! half/float bit conversion) that are not observable through `AbstractData`.
//! Those are asserted against the composed value instead, and quaternions are
//! checked in the crate's `(w, x, y, z)` order rather than the on-disk
//! `(x, y, z, w)` layout the Python parser exposes.

// Fixture values mirror the reference suite's literals, some of which sit near
// PI / E; comparing them as data is intentional, not an approximation slip.
#![allow(clippy::approx_constant)]

use std::fs::File;

use openusd::gf::f16;
use openusd::sdf::{self, AbstractData, LayerOffset, Payload, Permission, Specifier, Value, Variability};
use openusd::usdc::CrateData;

const VENDOR: &str = "vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/binary";

/// Open a binary fixture by file name.
fn read(file: &str) -> CrateData<File> {
    let path = format!("{VENDOR}/{file}");
    let f = File::open(&path).unwrap_or_else(|e| panic!("cannot open {path}: {e}"));
    CrateData::open(f, true).unwrap_or_else(|e| panic!("failed to parse {path}: {e:#}"))
}

/// Open a `gen_<name>.usdc` fixture.
fn scene(name: &str) -> CrateData<File> {
    read(&format!("gen_{name}.usdc"))
}

/// Fetch an authored field value, panicking if it is absent.
fn value(data: &CrateData<File>, path: &str, field: &str) -> Value {
    let p = sdf::path(path).unwrap();
    data.get(&p, field)
        .unwrap_or_else(|e| panic!("get {path}.{field}: {e:#}"))
        .into_owned()
}

/// Returns `true` if the field is authored at the path.
fn has_field(data: &CrateData<File>, path: &str, field: &str) -> bool {
    data.has_field(&sdf::path(path).unwrap(), field)
}

/// Assert two component lists agree to `places` decimal places, mirroring
/// Python's `assertAlmostEqual`.
fn assert_close(actual: &[f64], expected: &[f64], places: i32) {
    assert_eq!(
        actual.len(),
        expected.len(),
        "length mismatch: {actual:?} vs {expected:?}"
    );
    let tol = 0.5 * 10f64.powi(-places);
    for (i, (a, b)) in actual.iter().zip(expected).enumerate() {
        assert!((a - b).abs() <= tol, "component {i}: {a} != {b} (places {places})");
    }
}

/// Extract a scalar float value as `f64`.
fn scalar_f64(v: &Value) -> f64 {
    match v {
        Value::Half(x) => x.to_f64(),
        Value::Float(x) => *x as f64,
        Value::Double(x) => *x,
        Value::TimeCode(x) => *x,
        other => panic!("not a scalar float: {other:?}"),
    }
}

/// Extract a scalar float array as `Vec<f64>`.
fn vec_f64(v: &Value) -> Vec<f64> {
    match v {
        Value::HalfVec(a) => a.iter().map(|x| x.to_f64()).collect(),
        Value::FloatVec(a) => a.iter().map(|&x| x as f64).collect(),
        Value::DoubleVec(a) => a.clone(),
        Value::TimeCodeVec(a) => a.clone(),
        other => panic!("not a scalar float array: {other:?}"),
    }
}

/// Extract a single vector/quaternion value as a component list.
fn comps(v: &Value) -> Vec<f64> {
    match v {
        Value::Vec2h(a) => vec![a.x.to_f64(), a.y.to_f64()],
        Value::Vec3h(a) => vec![a.x.to_f64(), a.y.to_f64(), a.z.to_f64()],
        Value::Vec4h(a) => vec![a.x.to_f64(), a.y.to_f64(), a.z.to_f64(), a.w.to_f64()],
        Value::Quath(a) => vec![a.w.to_f64(), a.x.to_f64(), a.y.to_f64(), a.z.to_f64()],
        Value::Vec2f(a) => vec![a.x as f64, a.y as f64],
        Value::Vec3f(a) => vec![a.x as f64, a.y as f64, a.z as f64],
        Value::Vec4f(a) => vec![a.x as f64, a.y as f64, a.z as f64, a.w as f64],
        Value::Quatf(a) => vec![a.w as f64, a.x as f64, a.y as f64, a.z as f64],
        Value::Vec2d(a) => vec![a.x, a.y],
        Value::Vec3d(a) => vec![a.x, a.y, a.z],
        Value::Vec4d(a) => vec![a.x, a.y, a.z, a.w],
        Value::Quatd(a) => vec![a.w, a.x, a.y, a.z],
        Value::Vec2i(a) => vec![a.x as f64, a.y as f64],
        Value::Vec3i(a) => vec![a.x as f64, a.y as f64, a.z as f64],
        Value::Vec4i(a) => vec![a.x as f64, a.y as f64, a.z as f64, a.w as f64],
        other => panic!("not a vector/quat value: {other:?}"),
    }
}

/// Extract a vector/quaternion array as a list of component lists.
fn arr_comps(v: &Value) -> Vec<Vec<f64>> {
    use bytemuck::cast_slice;
    fn h<const N: usize>(a: &[[f16; N]]) -> Vec<Vec<f64>> {
        a.iter().map(|e| e.iter().map(|x| x.to_f64()).collect()).collect()
    }
    fn f<const N: usize>(a: &[[f32; N]]) -> Vec<Vec<f64>> {
        a.iter().map(|e| e.iter().map(|&x| x as f64).collect()).collect()
    }
    fn d<const N: usize>(a: &[[f64; N]]) -> Vec<Vec<f64>> {
        a.iter().map(|e| e.to_vec()).collect()
    }
    fn i<const N: usize>(a: &[[i32; N]]) -> Vec<Vec<f64>> {
        a.iter().map(|e| e.iter().map(|&x| x as f64).collect()).collect()
    }
    match v {
        Value::Vec2hVec(a) => h(cast_slice::<_, [f16; 2]>(a)),
        Value::Vec3hVec(a) => h(cast_slice::<_, [f16; 3]>(a)),
        Value::Vec4hVec(a) => h(cast_slice::<_, [f16; 4]>(a)),
        Value::QuathVec(a) => h(cast_slice::<_, [f16; 4]>(a)),
        Value::Vec2fVec(a) => f(cast_slice::<_, [f32; 2]>(a)),
        Value::Vec3fVec(a) => f(cast_slice::<_, [f32; 3]>(a)),
        Value::Vec4fVec(a) => f(cast_slice::<_, [f32; 4]>(a)),
        Value::QuatfVec(a) => f(cast_slice::<_, [f32; 4]>(a)),
        Value::Vec2dVec(a) => d(cast_slice::<_, [f64; 2]>(a)),
        Value::Vec3dVec(a) => d(cast_slice::<_, [f64; 3]>(a)),
        Value::Vec4dVec(a) => d(cast_slice::<_, [f64; 4]>(a)),
        Value::QuatdVec(a) => d(cast_slice::<_, [f64; 4]>(a)),
        Value::Vec2iVec(a) => i(cast_slice::<_, [i32; 2]>(a)),
        Value::Vec3iVec(a) => i(cast_slice::<_, [i32; 3]>(a)),
        Value::Vec4iVec(a) => i(cast_slice::<_, [i32; 4]>(a)),
        other => panic!("not a vector/quat array: {other:?}"),
    }
}

/// Shared driver for the float fixtures (`half` / `float` / `double`).
fn assert_floats(name: &str, places: i32) {
    let data = scene(name);

    let single = scalar_f64(&value(&data, "/root.single", "default"));
    assert_close(&[single], &[3.1415], places);

    let lut = vec_f64(&value(&data, "/root.array:lut", "default"));
    assert_close(&lut, &[-3.1415, 2.7182, 1.6180], places);

    // `array:ints` is authored with the fixture's float type but holds whole
    // numbers; the reference compares it numerically against `[-1, 0, 1]`.
    let ints = vec_f64(&value(&data, "/root.array:ints", "default"));
    assert_close(&ints, &[-1.0, 0.0, 1.0], places);
}

/// Shared driver for the `string` / `token` fixtures.
fn assert_strings(data: &CrateData<File>) {
    assert_eq!(scalar_str(&value(data, "/root.single", "default")), "Hello/World");
    let array = str_vec(&value(data, "/root.array", "default"));
    assert_eq!(array, vec!["Hello/World", "Good/Bye"]);
}

fn scalar_str(v: &Value) -> String {
    match v {
        Value::String(s) | Value::Token(s) | Value::AssetPath(s) | Value::PathExpression(s) => s.clone(),
        other => panic!("not a string-like value: {other:?}"),
    }
}

fn str_vec(v: &Value) -> Vec<String> {
    match v {
        Value::StringVec(a) | Value::TokenVec(a) => a.clone(),
        other => panic!("not a string-like array: {other:?}"),
    }
}

/// Shared driver for the matrix fixtures.
fn assert_matrices(dim: usize) {
    let data = scene(&format!("matrix{dim}d"));

    let mut single_mat = Vec::new();
    let mut identity = Vec::new();
    for r in 0..dim {
        for c in 0..dim {
            single_mat.push(((r + 1) * (c + 1)) as f64);
            identity.push(if r == c { 1.0 } else { 0.0 });
        }
    }

    let single = mat_f64(&value(&data, "/root.single", "default"));
    assert_eq!(single, single_mat);

    let inlined = mat_f64(&value(&data, "/root.inlined", "default"));
    assert_eq!(inlined, identity);

    let array = mat_array_f64(&value(&data, "/root.array", "default"));
    assert_eq!(array, vec![single_mat.clone(), single_mat]);
}

fn mat_f64(v: &Value) -> Vec<f64> {
    match v {
        Value::Matrix2d(a) => a.0.to_vec(),
        Value::Matrix3d(a) => a.0.to_vec(),
        Value::Matrix4d(a) => a.0.to_vec(),
        other => panic!("not a matrix: {other:?}"),
    }
}

fn mat_array_f64(v: &Value) -> Vec<Vec<f64>> {
    match v {
        Value::Matrix2dVec(a) => a.iter().map(|m| m.0.to_vec()).collect(),
        Value::Matrix3dVec(a) => a.iter().map(|m| m.0.to_vec()).collect(),
        Value::Matrix4dVec(a) => a.iter().map(|m| m.0.to_vec()).collect(),
        other => panic!("not a matrix array: {other:?}"),
    }
}

/// Shared driver for the vector and quaternion fixtures.
fn assert_math(name: &str, dim: usize, integer: bool, places: i32) {
    let data = scene(name);

    let mut single_value: Vec<f64> = vec![3.14, 4.824, 1.225, 5.247][..dim].to_vec();
    let inline_value: Vec<f64> = vec![0.0, 1.0, 2.0, 3.0][..dim].to_vec();
    if integer {
        single_value.iter_mut().for_each(|x| *x = x.ceil());
    }

    let single = comps(&value(&data, "/root.single", "default"));
    assert_close(&single, &single_value, places);

    let inline = comps(&value(&data, "/root.inlined", "default"));
    assert_close(&inline, &inline_value, places);

    let array = arr_comps(&value(&data, "/root.array", "default"));
    for (idx, item) in array.iter().enumerate() {
        let expected = if idx == 1 { &inline_value } else { &single_value };
        assert_close(item, expected, places);
    }
}

#[test]
fn scene_strat() {
    let data = read("fender_stratocaster.usdc");
    assert_eq!(data.paths().len(), 432);
    assert_eq!(
        value(&data, "/", "defaultPrim"),
        Value::Token("fender_stratocaster".into())
    );
}

#[test]
fn scene_plane() {
    let data = read("toy_biplane_idle.usdc");
    assert_eq!(data.paths().len(), 425);
    assert_eq!(
        value(&data, "/", "defaultPrim"),
        Value::Token("toy_biplane_idle".into())
    );
}

#[test]
fn bool_values() {
    let data = scene("bool");
    assert!(!has_field(&data, "/root.unset", "default"));
    assert!(!has_field(&data, "/root.array:unset", "default"));

    assert_eq!(value(&data, "/root.single", "default"), Value::Bool(true));
    assert_eq!(
        value(&data, "/root.array", "default"),
        Value::BoolVec(vec![false, false, true, false, false])
    );
    assert_eq!(
        value(&data, "/root.array", "variability"),
        Value::Variability(Variability::Uniform)
    );
}

#[test]
fn uchar_values() {
    let data = scene("uchar");
    assert_eq!(value(&data, "/root.single", "default"), Value::Uchar(255));
    assert_eq!(
        value(&data, "/root.array", "default"),
        Value::UcharVec(vec![0, 1, 2, 3, 4, 255])
    );
}

#[test]
fn int_values() {
    let data = scene("int");
    assert_eq!(value(&data, "/root.single", "default"), Value::Int(-2147483647));
    assert_eq!(
        value(&data, "/root.array", "default"),
        Value::IntVec(vec![-2147483647, 0, 1, 2, 3, 4, 2147483647])
    );
}

#[test]
fn uint_values() {
    let data = scene("uint");
    assert_eq!(value(&data, "/root.single", "default"), Value::Uint(4294967295));
    assert_eq!(
        value(&data, "/root.array", "default"),
        Value::UintVec(vec![0, 1, 2, 3, 4, 4294967295])
    );
}

#[test]
fn int64_values() {
    let data = scene("int64");
    assert_eq!(
        value(&data, "/root.single", "default"),
        Value::Int64(-9223372036854775807)
    );
    assert_eq!(
        value(&data, "/root.array", "default"),
        Value::Int64Vec(vec![-9223372036854775807, 0, 1, 2, 3, 4, 9223372036854775807])
    );
}

#[test]
fn uint64_values() {
    let data = scene("uint64");
    assert_eq!(
        value(&data, "/root.single", "default"),
        Value::Uint64(18446744073709551615)
    );
    assert_eq!(
        value(&data, "/root.array", "default"),
        Value::Uint64Vec(vec![0, 1, 2, 3, 4, 18446744073709551615])
    );
}

#[test]
fn half_values() {
    assert_floats("half", 2);
}

#[test]
fn float_values() {
    assert_floats("float", 5);
}

#[test]
fn double_values() {
    assert_floats("double", 9);
}

#[test]
fn string_values() {
    assert_strings(&scene("string"));
}

#[test]
fn token_values() {
    assert_strings(&scene("token"));
}

#[test]
fn assetpath_values() {
    assert_strings(&scene("assetpath"));
}

#[test]
fn path_expression_values() {
    let data = scene("pathexpression");
    assert_eq!(
        value(&data, "/root.single", "default"),
        Value::PathExpression("/root/Foo".into())
    );
    let array = str_vec(&value(&data, "/root.array", "default"));
    assert_eq!(array, vec!["/root/Spam", "/root/Eggs"]);
}

#[test]
fn matrix2d_values() {
    assert_matrices(2);
}

#[test]
fn matrix3d_values() {
    assert_matrices(3);
}

#[test]
fn matrix4d_values() {
    assert_matrices(4);
}

#[test]
fn quatd_values() {
    assert_math("quatd", 4, false, 4);
}

#[test]
fn quatf_values() {
    assert_math("quatf", 4, false, 4);
}

#[test]
fn quath_values() {
    assert_math("quath", 4, false, 2);
}

#[test]
fn vec2d_values() {
    assert_math("vec2d", 2, false, 4);
}

#[test]
fn vec2f_values() {
    assert_math("vec2f", 2, false, 4);
}

#[test]
fn vec2h_values() {
    assert_math("vec2h", 2, false, 2);
}

#[test]
fn vec2i_values() {
    assert_math("vec2i", 2, true, 4);
}

#[test]
fn vec3d_values() {
    assert_math("vec3d", 3, false, 4);
}

#[test]
fn vec3f_values() {
    assert_math("vec3f", 3, false, 4);
}

#[test]
fn vec3h_values() {
    assert_math("vec3h", 3, false, 2);
}

#[test]
fn vec3i_values() {
    assert_math("vec3i", 3, true, 4);
}

#[test]
fn vec4d_values() {
    assert_math("vec4d", 4, false, 4);
}

#[test]
fn vec4f_values() {
    assert_math("vec4f", 4, false, 4);
}

#[test]
fn vec4h_values() {
    assert_math("vec4h", 4, false, 2);
}

#[test]
fn vec4i_values() {
    assert_math("vec4i", 4, true, 4);
}

#[test]
fn dictionary_values() {
    let data = scene("dict");
    let custom = value(&data, "/", "customLayerData")
        .try_as_dictionary()
        .expect("customLayerData is not a dictionary");
    let apple = custom["Apple"]
        .clone()
        .try_as_dictionary()
        .expect("Apple is not a dictionary");
    assert_eq!(apple["preferredIblVersion"], Value::Int(2));
}

#[test]
fn relocates_values() {
    let data = scene("relocates");
    let relocates = value(&data, "/", "layerRelocates")
        .try_as_relocates()
        .expect("layerRelocates is not a relocates value");
    assert_eq!(relocates.len(), 1);
    assert_eq!(relocates[0].0, sdf::path("/Egg/Foo").unwrap());
    assert_eq!(relocates[0].1, sdf::path("/Egg/Bar").unwrap());
}

#[test]
fn timecodes_values() {
    let data = scene("timecodes");
    let single = scalar_f64(&value(&data, "/root.single", "default"));
    assert_close(&[single], &[11.0], 7);

    let array = vec_f64(&value(&data, "/root.array", "default"));
    assert_close(&array, &[100.1, 13.1234], 4);
}

#[test]
fn timesamples_values() {
    let data = scene("timesamples");
    let samples = value(&data, "/root.animated", "timeSamples")
        .try_as_time_samples()
        .expect("timeSamples is not a time-sample map");
    let (head, tail) = samples.split_last().expect("at least one sample");
    for (time, sample) in tail {
        assert_close(&[*time], &[scalar_f64(sample)], 4);
    }
    assert_eq!(head.1, Value::ValueBlock);
}

#[test]
fn permissions_values() {
    let data = scene("permissions");
    assert_eq!(
        value(&data, "/Specialize", "permission"),
        Value::Permission(Permission::Private)
    );
}

#[test]
fn variants_values() {
    let data = scene("variants");

    let selection = value(&data, "/root", "variantSelection")
        .try_as_variant_selection_map()
        .expect("variantSelection is not a selection map");
    assert_eq!(selection.get("foo").map(String::as_str), Some("eggs"));

    assert_eq!(value(&data, "/", "primChildren"), Value::TokenVec(vec!["root".into()]));
    assert_eq!(value(&data, "/root", "specifier"), Value::Specifier(Specifier::Def));

    let names = value(&data, "/root", "variantSetNames")
        .try_as_string_list_op()
        .expect("variantSetNames is not a string list op");
    assert!(!names.explicit);
    assert_eq!(names.prepended_items, vec!["foo".to_string()]);
}

#[test]
fn listops_values() {
    let data = scene("listops");

    let api = value(&data, "/root", "apiSchemas")
        .try_as_token_list_op()
        .expect("apiSchemas is not a token list op");
    assert!(api.explicit);
    assert_eq!(api.explicit_items, vec!["MaterialBindingAPI".to_string()]);

    let refs = value(&data, "/root", "references")
        .try_as_reference_list_op()
        .expect("references is not a reference list op");
    assert!(!refs.explicit);
    assert_eq!(refs.prepended_items.len(), 1);
    let r = &refs.prepended_items[0];
    assert_eq!(r.asset_path, "./ref.usda");
    assert_eq!(r.prim_path, sdf::path("/Model").unwrap());
    assert_eq!(r.layer_offset, LayerOffset::new(10.0, 1.0));

    let payloads = value(&data, "/root", "payload")
        .try_as_payload_list_op()
        .expect("payload is not a payload list op");
    assert!(!payloads.explicit);
    assert_eq!(payloads.appended_items.len(), 1);
    let expected = Payload {
        asset_path: "eggs.usda".into(),
        prim_path: sdf::Path::default(),
        layer_offset: Some(LayerOffset::new(0.0, 1.0)),
    };
    assert_eq!(payloads.appended_items[0], expected);

    let targets = value(&data, "/root.foo", "targetPaths")
        .try_as_path_list_op()
        .expect("targetPaths is not a path list op");
    assert!(targets.explicit);
    assert_eq!(
        targets.explicit_items,
        vec![sdf::path("/eggs").unwrap(), sdf::path("/spam").unwrap()]
    );
}

#[test]
fn vectors_values() {
    let data = scene("vectors");

    assert_eq!(
        value(&data, "/", "subLayers"),
        Value::StringVec(vec!["foo.usda".into(), "bar.usda".into(), "baz.usda".into()])
    );
    assert_eq!(
        value(&data, "/", "subLayerOffsets"),
        Value::LayerOffsetVec(vec![
            LayerOffset::new(0.0, 1.0),
            LayerOffset::new(4.5, 1.0),
            LayerOffset::new(1.2, 6.0),
        ])
    );
}

#[test]
fn path_vector() {
    let data = read("ball.maya.usdc");
    let children = value(
        &data,
        "/Ball/Looks/BallMaterial/Base.inputs:baseColor",
        "connectionChildren",
    )
    .try_as_path_vec()
    .expect("connectionChildren is not a path vector");
    assert_eq!(
        children,
        vec![sdf::path("/Ball/Looks/BallMaterial/BallTexture.outputs:resultRGB").unwrap()]
    );
}
