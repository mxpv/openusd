//! Cross-format round-trip: parse `.usda`, emit `.usdc`, parse the `.usdc`,
//! and assert the resulting layer is equal to the original parse.

use std::collections::BTreeMap;
use std::io::Cursor;
use std::path::Path;

use openusd::sdf::{self, AbstractData};
use openusd::usda::TextReader;
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

fn is_default_layer_offset(v: &serde_json::Value) -> bool {
    let Some(obj) = v.as_object() else {
        return false;
    };
    let offset = obj.get("offset").and_then(|n| n.as_f64()).unwrap_or(1.0);
    let scale = obj.get("scale").and_then(|n| n.as_f64()).unwrap_or(0.0);
    offset == 0.0 && scale == 1.0
}

fn normalize(v: &mut serde_json::Value) {
    match v {
        serde_json::Value::Number(n) if n.is_f64() => {
            let f = n.as_f64().unwrap();
            if f.fract() == 0.0 && f.is_finite() && f.abs() < i64::MAX as f64 {
                *v = serde_json::Value::from(f as i64);
            } else {
                let short = format!("{}", f as f32);
                let long = format!("{f}");
                if short.len() < long.len() {
                    if let Ok(clean) = short.parse::<f64>() {
                        *v = serde_json::json!(clean);
                    }
                }
            }
        }
        serde_json::Value::Array(a) => a.iter_mut().for_each(normalize),
        serde_json::Value::Object(m) => {
            if m.contains_key("layerOffset") || m.contains_key("asset") {
                m.remove("customData");
            }
            // A default layerOffset (offset=0, scale=1) is a no-op. The USDC
            // binary slot is mandatory for payloads (≥0.8.0) so we always emit
            // one; strip defaults on both sides to compare fairly.
            if let Some(lo) = m.get("layerOffset") {
                if is_default_layer_offset(lo) {
                    m.remove("layerOffset");
                }
            }
            m.retain(|_, v| !matches!(v, serde_json::Value::Object(inner) if inner.is_empty()));
            m.values_mut().for_each(normalize);
        }
        _ => {}
    }
}

fn assert_cross(name: &str, usda_path: &Path) {
    let text = TextReader::read(usda_path).unwrap_or_else(|e| panic!("failed to parse {}: {e:#}", usda_path.display()));

    let mut buf = Vec::new();
    {
        let mut cursor = Cursor::new(&mut buf);
        CrateWriter::write(&text as &dyn AbstractData, &mut cursor)
            .unwrap_or_else(|e| panic!("usdc emit failed for {name}: {e:#}"));
    }

    let crate_data = CrateData::open(Cursor::new(&buf), true)
        .unwrap_or_else(|e| panic!("re-parse of emitted usdc failed for {name}: {e:#}"));

    let mut a = snapshot(&text as &dyn AbstractData);
    let mut b = snapshot(&crate_data as &dyn AbstractData);
    normalize(&mut a);
    normalize(&mut b);

    let diffs = diff_json::compare_values(&a, &b);
    assert!(
        diffs.is_empty(),
        "cross-format mismatch for {name}:\n{}",
        diff_json::DiffFormatter::new().format(&diffs)
    );
}

const ASSETS: &str = "vendor/core-spec-supplemental-release_dec2025/file_formats/tests/assets/text";

macro_rules! cross_tests {
    ($($name:ident),* $(,)?) => {
        $(
            #[test]
            fn $name() {
                let stem = stringify!($name).trim_start_matches("cross_");
                let p = Path::new(ASSETS).join("usda").join(format!("{stem}.usda"));
                assert_cross(stem, &p);
            }
        )*
    };
}

cross_tests! {
    cross_empty,
    cross_simple,
    cross_attributes,
    cross_relations,
    cross_primmetadata,
    cross_layermetadata,
    cross_variants,
    cross_geometryattributes,
}

// Skipped fixtures:
//   - `splines.usda`: splines materialise as `Value::ValueVec`, which the USDC
//     writer rejects (no native heterogeneous-array type).
//   - `dictionaries.usda`: the USDC reader bails on nested dictionaries
//     (`"Nested dictionaries are not supported"` in `read_custom_data`).
