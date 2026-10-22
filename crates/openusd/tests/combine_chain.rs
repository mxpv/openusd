//! `ListOp` composition compliance tests.
//!
//! Validates `ListOp::combined_with` and `ListOp::reduced` against the vendor
//! JSON baselines.

use std::path::Path;

use openusd::sdf::{ListOp, ListOpType};

const COMBINE_CHAIN: &str = concat!(
    env!("CARGO_WORKSPACE_DIR"),
    "vendor/core-spec-supplemental-release_dec2025/data_types/tests/combine_chain"
);

/// JSON schema for loading vendor test fixtures.
mod schema {
    /// A single test case from the `combine_chain` JSON files.
    #[derive(serde::Deserialize)]
    pub struct Case {
        pub description: String,
        pub chain: Vec<Data>,
        pub combined_reduced: Data,
    }

    /// JSON representation of a `ListOp`.
    #[derive(Debug, Default, serde::Deserialize)]
    #[serde(default)]
    pub struct Data {
        pub explicit_items: Option<Vec<i32>>,
        pub prepended_items: Option<Vec<i32>>,
        pub appended_items: Option<Vec<i32>>,
        pub deleted_items: Option<Vec<i32>>,
    }

    impl Data {
        pub fn matches(&self, op: &super::ListOp<i32>) -> bool {
            let explicit_match = match &self.explicit_items {
                Some(items) => op.is_explicit() && op.explicit_items() == *items,
                None => !op.is_explicit(),
            };
            let prepend_match = op.prepended_items() == self.prepended_items.as_deref().unwrap_or_default();
            let append_match = op.appended_items() == self.appended_items.as_deref().unwrap_or_default();
            let delete_match = op.deleted_items() == self.deleted_items.as_deref().unwrap_or_default();
            explicit_match && prepend_match && append_match && delete_match
        }
    }

    impl From<&Data> for super::ListOp<i32> {
        fn from(data: &Data) -> Self {
            let items = |items: &Option<Vec<i32>>| items.clone().unwrap_or_default();
            let mut op = super::ListOp::default()
                .with(super::ListOpType::Explicit, items(&data.explicit_items))
                .with(super::ListOpType::Prepended, items(&data.prepended_items))
                .with(super::ListOpType::Appended, items(&data.appended_items))
                .with(super::ListOpType::Deleted, items(&data.deleted_items));
            op.set_explicit(data.explicit_items.is_some());
            op
        }
    }
}

fn run_combine_chain(name: &str) {
    let path = Path::new(COMBINE_CHAIN).join(format!("{name}.json"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let cases: Vec<schema::Case> = serde_json::from_str(&json).expect("parse JSON");

    for case in &cases {
        let chain: Vec<ListOp<i32>> = case.chain.iter().map(ListOp::from).collect();

        let combined = chain[1..].iter().fold(chain[0].clone(), |acc, weaker| {
            acc.combined_with(weaker).expect("the spec's ops add nothing")
        });
        let reduced = combined.reduced();

        assert!(
            case.combined_reduced.matches(&reduced),
            "FAILED: {}\n  expected: {:?}\n  got:      {reduced:?}",
            case.description,
            case.combined_reduced,
        );
    }
}

#[test]
fn test_inert_only() {
    run_combine_chain("inert_only");
}

#[test]
fn test_explicit_only() {
    run_combine_chain("explicit_only");
}

#[test]
fn test_composable_only() {
    run_combine_chain("composable_only");
}

#[test]
fn test_prepend_over_composable() {
    run_combine_chain("prepend_over_composable");
}

#[test]
fn test_append_over_composable() {
    run_combine_chain("append_over_composable");
}

#[test]
fn test_prepend_over_explicit() {
    run_combine_chain("prepend_over_explicit");
}

#[test]
fn test_append_over_explicit() {
    run_combine_chain("append_over_explicit");
}

#[test]
fn test_delete_over_explicit() {
    run_combine_chain("delete_over_explicit");
}
