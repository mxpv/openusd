//! The text writer against layers C++ wrote.
//!
//! `fixtures/sdf_parsing` holds baselines of C++ `testSdfParsing`, each the
//! text C++ `SdfLayer::Export` wrote for one of its inputs. Read and written
//! back, each must come out byte for byte as C++ wrote it.

use std::fs;

use openusd::sdf;
use openusd::usda::{self, TextWriter};

#[test]
fn cpp_baselines_reexport() {
    let mut paths: Vec<_> = fs::read_dir("fixtures/sdf_parsing")
        .expect("fixtures/sdf_parsing")
        .map(|entry| entry.expect("a directory entry").path())
        .collect();
    paths.sort();
    assert!(!paths.is_empty());
    let mut failures = Vec::new();
    for path in paths {
        // A checkout that turns line ends into CRLF still holds the same text.
        let expected = fs::read_to_string(&path).expect("a baseline").replace("\r\n", "\n");
        let text = usda::read_file(&path)
            .map_err(|e| format!("read: {e:#}"))
            .and_then(|data| {
                TextWriter::write_to_string(&data as &dyn sdf::AbstractData).map_err(|e| format!("write: {e:#}"))
            });
        let failure = match text {
            Ok(text) if text == expected => continue,
            Ok(text) => match text
                .lines()
                .zip(expected.lines())
                .enumerate()
                .find(|(_, (got, want))| got != want)
            {
                Some((line, (got, want))) => format!("line {}:\n   wrote: {got}\n  C++ wrote: {want}", line + 1),
                None => format!(
                    "the same lines up to the shorter text, {} bytes written where C++ wrote {}",
                    text.len(),
                    expected.len()
                ),
            },
            Err(error) => error,
        };
        failures.push(format!("{}: {failure}", path.display()));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
