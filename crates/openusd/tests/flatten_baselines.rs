//! Flattened stages against the layers C++ flattened.
//!
//! Each directory of `fixtures/flatten` is a case from the C++ test suite,
//! the instancing cases of `testUsdFlatten2` and the `flatten` case of
//! `testUsdValueClips`, or one written for this suite: `ValueClipsBlocked`, a
//! clip set whose manifest declares an attribute no clip supplies, and
//! `ValueClipsBlockedDefault`, a gap a blocked manifest default fills. A case
//! holds a `root.usda` with the layers it composes and `flat.usda`, the text
//! C++ `UsdStage::ExportToString` wrote for it with no source-file comment
//! (for a case of this suite's own, run through the C++ Python bindings).
//! Flattened and written, each root must come out as C++ wrote it.

use std::fs;

use openusd::usd;

#[test]
fn cpp_flatten_baselines() {
    let mut cases: Vec<_> = fs::read_dir("fixtures/flatten")
        .expect("fixtures/flatten")
        .map(|entry| entry.expect("a directory entry").path())
        .filter(|path| path.is_dir())
        .collect();
    cases.sort();
    assert!(!cases.is_empty());
    let mut failures = Vec::new();
    for case in cases {
        // The baseline is what Python `print` wrote, with a newline of its
        // own, and a checkout that turns line ends into CRLF still holds the
        // same text.
        let expected = fs::read_to_string(case.join("flat.usda"))
            .expect("a baseline")
            .replace("\r\n", "\n");
        let expected = expected.trim_end();
        let root = case.join("root.usda");
        let text = usd::Stage::open(root.to_str().expect("a UTF-8 path"))
            .and_then(|stage| stage.flatten())
            .map_err(|e| format!("flatten: {e:#}"))
            .and_then(|layer| layer.export_to_string().map_err(|e| format!("write: {e:#}")));
        let failure = match text {
            Ok(text) if text.trim_end() == expected => continue,
            Ok(text) => match text
                .lines()
                .zip(expected.lines())
                .enumerate()
                .find(|(_, (got, want))| got != want)
            {
                Some((line, (got, want))) => format!("line {}:\n   wrote: {got}\n  C++ wrote: {want}", line + 1),
                None => format!(
                    "the same lines up to the shorter text, {} bytes written where C++ wrote {}",
                    text.trim_end().len(),
                    expected.len()
                ),
            },
            Err(error) => error,
        };
        failures.push(format!("{}: {failure}", case.display()));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
