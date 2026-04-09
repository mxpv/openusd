//! Text format compliance tests.
//!
//! Each test parses a `.usda` file from the vendor compliance suite and compares
//! the resulting spec data against the corresponding JSON baseline.

use std::collections::BTreeMap;
use std::path::Path;

use openusd::sdf;
use openusd::usda::TextReader;

const ASSETS: &str = "vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/text";

/// Parse a `.usda` file and compare the spec data against a JSON baseline.
///
/// Builds a `{ path: { field: value, ... }, ... }` map from the parsed data
/// and asserts it matches the expected baseline.
#[cfg(feature = "serde")]
fn assert_text_format(name: &str) {
    let assets = Path::new(ASSETS);
    let usda = assets.join("usda").join(format!("{name}.usda"));
    let baseline = assets.join("baseline").join(format!("{name}.json"));

    let reader =
        TextReader::read(&usda).unwrap_or_else(|e| panic!("failed to parse {}: {e:#}", usda.display()));

    // Build actual output as a sorted map of path → fields.
    let mut actual: BTreeMap<String, BTreeMap<&str, &sdf::Value>> = BTreeMap::new();
    for (path, spec) in reader.iter() {
        let fields: BTreeMap<&str, &sdf::Value> =
            spec.fields.iter().map(|(k, v)| (k.as_str(), v)).collect();
        actual.insert(path.to_string(), fields);
    }

    let mut actual_json = serde_json::to_value(&actual).expect("failed to serialize actual data");
    let mut expected_json: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(&baseline).expect("failed to read baseline"))
            .expect("failed to parse baseline JSON");
    normalize_json(&mut actual_json);
    normalize_json(&mut expected_json);

    let diffs = diff_json::compare_values(&actual_json, &expected_json);
    assert!(
        diffs.is_empty(),
        "mismatch for {name}:\n{}",
        diff_json::DiffFormatter::new().format(&diffs)
    );
}

/// Normalize JSON numbers to avoid false mismatches between our output and the
/// Python-generated baselines. Two sources of noise:
///
/// 1. Integer vs float: Python's JSON encoder preserves the Python type, so
///    a USDA matrix `((0.9, 0, 0, 0), ...)` produces baseline JSON with mixed
///    `0` (int) and `0.9` (float). Our Rust parser stores all components with
///    their declared type (`f64` for matrices), always emitting `0.0`. We
///    normalize whole-number floats to integers on both sides.
///
/// 2. f32 precision: Typed values like `color3f` are stored as `f32` in Rust
///    but as Python `float` (f64) in the reference. When serde serializes `f32`
///    to JSON it round-trips through `f64`, exposing representation noise
///    (e.g. `0.4f32` becomes `0.4000000059604645`). We re-round such values
///    through their shortest `f32` representation to recover the original text.
#[cfg(feature = "serde")]
fn normalize_json(v: &mut serde_json::Value) {
    match v {
        serde_json::Value::Number(n) if n.is_f64() => {
            let f = n.as_f64().unwrap();
            if f.fract() == 0.0 && f.is_finite() && f.abs() < i64::MAX as f64 {
                // Whole-number float → integer.
                *v = serde_json::Value::from(f as i64);
            } else {
                // f32 precision noise → if round-tripping through f32 gives a
                // shorter representation, use it (e.g. 0.4000000059604645 → 0.4).
                let short = format!("{}", f as f32);
                let long = format!("{f}");
                if short.len() < long.len() {
                    if let Ok(clean) = short.parse::<f64>() {
                        *v = serde_json::json!(clean);
                    }
                }
            }
        }
        serde_json::Value::Array(a) => a.iter_mut().for_each(normalize_json),
        serde_json::Value::Object(m) => {
            // The Python baseline encoder omits customData on references/payloads.
            // Strip it from objects that look like references (have "asset" or "layerOffset").
            if m.contains_key("layerOffset") || m.contains_key("asset") {
                m.remove("customData");
            }
            m.values_mut().for_each(normalize_json);
        }
        _ => {}
    }
}

#[cfg(feature = "serde")]
mod text_parser {
    use super::*;

    #[test]
    fn test_empty() {
        assert_text_format("empty");
    }

    #[test]
    fn test_simple() {
        assert_text_format("simple");
    }

    #[test]
    fn test_attributes() {
        assert_text_format("attributes");
    }

    #[test]
    fn test_relations() {
        assert_text_format("relations");
    }

    #[test]
    fn test_primmetadata() {
        assert_text_format("primmetadata");
    }

    #[test]
    fn test_layermetadata() {
        assert_text_format("layermetadata");
    }

    #[test]
    fn test_dictionaries() {
        assert_text_format("dictionaries");
    }

    #[test]
    fn test_splines() {
        assert_text_format("splines");
    }

    #[test]
    fn test_variants() {
        assert_text_format("variants");
    }

    #[test]
    fn test_geometryattributes() {
        assert_text_format("geometryattributes");
    }
}
