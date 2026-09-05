//! Expression-mode collection integration over the public API: composed
//! `membershipExpression` attributes parsed from `.usda`, `%_` composition
//! across sublayers, collection references, forced modes, and a collection
//! carried across a reference arc.

use openusd::sdf;
use openusd::usd::{self, Collection, PrimPredicate, compute_included_paths, resolve_complete_membership_expression};

fn open() -> usd::Stage {
    usd::Stage::open("fixtures/collections.usda").expect("open collections fixture")
}

fn included(stage: &usd::Stage, coll: &Collection) -> Vec<String> {
    let query = coll.compute_membership_query(stage).expect("query");
    let mut paths: Vec<String> = compute_included_paths(stage, &query, PrimPredicate::DEFAULT)
        .expect("included paths")
        .into_iter()
        .map(|p| p.to_string())
        .collect();
    paths.sort();
    paths
}

#[test]
fn weaker_expression_composes() {
    let stage = open();
    let coll = Collection::new(sdf::path("/Sets").unwrap(), "heroes").unwrap();

    // The strong layer's `%_` picked up the weak layer's expression.
    let expr = coll.membership_expression(&stage).unwrap().expect("authored");
    assert_eq!(expr.to_string(), "/World/Chars/M* /World/Chars/Sully");

    let query = coll.compute_membership_query(&stage).unwrap();
    assert!(!query.uses_path_expansion_rule_map());
    assert!(query.is_path_included(&sdf::path("/World/Chars/Mike").unwrap()));
    assert!(query.is_path_included(&sdf::path("/World/Chars/Sully").unwrap()));
    assert!(!query.is_path_included(&sdf::path("/World/Props/Ball").unwrap()));
}

#[test]
fn collection_reference_expands() {
    let stage = open();
    let coll = Collection::new(sdf::path("/Sets").unwrap(), "combined").unwrap();

    let resolved = resolve_complete_membership_expression(&stage, &coll).expect("resolve");
    assert_eq!(
        resolved.to_string(),
        "/World/Chars/M* /World/Chars/Sully /World/Props//"
    );

    assert_eq!(
        included(&stage, &coll),
        [
            "/World/Chars/Mike",
            "/World/Chars/Sully",
            "/World/Props",
            "/World/Props/Ball",
        ]
    );
}

#[test]
fn expression_across_reference() {
    let stage = open();
    let coll = Collection::new(sdf::path("/RefRoot").unwrap(), "parts").unwrap();

    // Authored as `.//` against /Asset in the referenced layer; composition
    // anchored it there and mapped it into the referencing namespace.
    let expr = coll.membership_expression(&stage).unwrap().expect("authored");
    assert_eq!(expr.to_string(), "/RefRoot//");

    assert_eq!(included(&stage, &coll), ["/RefRoot", "/RefRoot/Bolt"]);
}
