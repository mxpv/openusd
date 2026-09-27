//! Integration test for the UsdSemantics schema views against a fixture.

use openusd::Result;
use openusd::gf;
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::{Prim, Stage, TimeCode};
use openusd_schemas::SchemaError;
use openusd_schemas::semantics::{LabelsAPI, LabelsQuery};

const FIXTURE: &str = "fixtures/usdSemantics_scene.usda";

fn labels(api: &LabelsAPI) -> Result<Option<Vec<Token>>> {
    api.labels_attr().get::<Vec<Token>>()
}

fn tokens(names: &[&str]) -> Vec<Token> {
    names.iter().copied().map(Token::from).collect()
}

fn fixture() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)
}

/// An in-memory stage carrying the schema data, which is what makes a prim its
/// type and resolves the fallbacks its schema declares.
fn memory() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")
}

#[test]
fn labels_from_fixture() -> Result<()> {
    let kitchen = fixture()?.prim("/World/Kitchen")?;

    // The instance name is the taxonomy, so one prim carries a set of labels
    // per taxonomy applied to it.
    let category = LabelsAPI::get_instance(&kitchen, "category")?.expect("the category taxonomy");
    assert_eq!(labels(&category)?, Some(tokens(&["room", "interior"])));
    let style = LabelsAPI::get_instance(&kitchen, "style")?.expect("the style taxonomy");
    assert_eq!(labels(&style)?, Some(tokens(&["modern"])));

    // A taxonomy the prim was never labelled under is not there at all.
    assert!(LabelsAPI::get_instance(&kitchen, "lifecycle")?.is_none());
    Ok(())
}

#[test]
fn taxonomies_from_fixture() -> Result<()> {
    let stage = fixture()?;

    let kitchen = stage.prim("/World/Kitchen")?;
    let mut direct = LabelsAPI::direct_taxonomies(&kitchen)?;
    direct.sort();
    assert_eq!(direct, tokens(&["category", "style"]));

    // A prim carrying no labels of its own is still in reach of its ancestors'
    // taxonomies, since labels inherit down namespace.
    let chair = stage.prim("/World/Kitchen/Chair")?;
    assert!(LabelsAPI::direct_taxonomies(&chair)?.is_empty());
    assert_eq!(LabelsAPI::inherited_taxonomies(&chair)?, tokens(&["category", "style"]));

    // `/World` is labelled under one taxonomy, and has no ancestor to add any.
    let world = stage.prim("/World")?;
    assert_eq!(LabelsAPI::inherited_taxonomies(&world)?, tokens(&["category"]));

    // The pseudo-root carries no schema and no ancestor.
    let root = stage.prim("/")?;
    assert!(LabelsAPI::direct_taxonomies(&root)?.is_empty());
    assert!(LabelsAPI::inherited_taxonomies(&root)?.is_empty());
    Ok(())
}

#[test]
fn labels_roundtrip() -> Result<()> {
    let stage = memory()?;
    let prim = stage.define_prim("/World/Chair")?;

    let category = LabelsAPI::apply(&prim, "category")?;
    category.create_labels_attr()?.set(tokens(&["furniture", "seating"]))?;

    let category = LabelsAPI::get_instance(&prim, "category")?.expect("the applied taxonomy");
    assert_eq!(labels(&category)?, Some(tokens(&["furniture", "seating"])));
    // The property the taxonomy is named by, spelled out.
    assert_eq!(
        category.labels_attr().path(),
        &sdf::path("/World/Chair.semantics:labels:category")?
    );
    Ok(())
}

/// The schema declares an empty array, so a taxonomy applied and left alone
/// reads as carrying no labels rather than as absent.
#[test]
fn unlabelled_taxonomy_reads_empty() -> Result<()> {
    let stage = memory()?;
    let prim = stage.define_prim("/World/Chair")?;
    let category = LabelsAPI::apply(&prim, "category")?;

    assert_eq!(labels(&category)?, Some(Vec::new()));
    Ok(())
}

/// A property path names the instance it belongs to, which is what lets a
/// caller go from an authored label back to the taxonomy it labels under. This
/// family is the one whose namespace prefix is two segments deep, so the split
/// between prefix and taxonomy is what these cases pin.
#[test]
fn instance_at_path_taxonomy() -> Result<()> {
    let path = sdf::path("/World/Chair.semantics:labels:category")?;
    let (prim, taxonomy) = LabelsAPI::instance_at_path(&path).expect("an instance path");

    assert_eq!(prim, sdf::path("/World/Chair")?);
    assert_eq!(taxonomy, Token::from("category"));

    // A taxonomy can be namespaced itself, and everything past the prefix is
    // the taxonomy however many segments it runs to.
    let nested = sdf::path("/World/Chair.semantics:labels:props:fabric")?;
    let (_, taxonomy) = LabelsAPI::instance_at_path(&nested).expect("a namespaced taxonomy");
    assert_eq!(taxonomy, Token::from("props:fabric"));

    // The prefix with nothing after it names no taxonomy.
    let bare = sdf::path("/World/Chair.semantics:labels")?;
    assert!(LabelsAPI::instance_at_path(&bare).is_none());

    // A property of another schema names no taxonomy of this one.
    let other = sdf::path("/World/Chair.visibility")?;
    assert!(LabelsAPI::instance_at_path(&other).is_none());
    Ok(())
}

#[test]
fn labels_from_query() -> Result<(), SchemaError> {
    let stage = fixture()?;
    let query = LabelsQuery::at("category", None)?;

    let kitchen = stage.prim("/World/Kitchen")?;
    assert_eq!(query.direct_labels(&kitchen)?, tokens(&["interior", "room"]));

    // The chair carries no labels of its own, and answers with its ancestors'
    // because labels inherit down namespace.
    let chair = stage.prim("/World/Kitchen/Chair")?;
    assert!(query.direct_labels(&chair)?.is_empty());
    assert_eq!(query.inherited_labels(&chair)?, tokens(&["interior", "room", "set"]));

    assert!(query.has_inherited_label(&chair, &Token::from("set"))?);
    assert!(!query.has_direct_label(&chair, &Token::from("set"))?);
    assert!(!query.has_inherited_label(&chair, &Token::from("outdoors"))?);

    // A query answers under its own taxonomy alone, so the style labels are
    // the style ones and not the category ones.
    let style = LabelsQuery::at("style", None)?;
    assert_eq!(style.inherited_labels(&chair)?, tokens(&["modern"]));

    // A taxonomy nothing is labelled under reaches no prim.
    let unused = LabelsQuery::at("lifecycle", None)?;
    assert!(unused.inherited_labels(&chair)?.is_empty());
    Ok(())
}

#[test]
fn query_refuses_nothing_to_read() {
    // Neither names anything to read: an empty taxonomy no application, an
    // empty interval no time.
    assert!(LabelsQuery::at("", None).is_err());
    assert!(LabelsQuery::over("", 0.0..=1.0).is_err());
    assert!(LabelsQuery::over("category", 5.0..=1.0).is_err());
    // Bounds that meet at an open end hold no time either, nor does one that
    // is not a number.
    assert!(LabelsQuery::over("category", 1.0..1.0).is_err());
    assert!(LabelsQuery::over("category", 1.0..=f64::NAN).is_err());
    assert!(LabelsQuery::over("category", 1.0..=1.0).is_ok());
}

/// A chair on an in-memory stage whose labels change over time.
fn sampled() -> Result<Prim, SchemaError> {
    let stage = memory()?;
    let chair = stage.define_prim("/World/Chair")?;
    LabelsAPI::apply(&chair, "category")?
        .create_labels_attr()?
        .set_at(tokens(&["wip"]), TimeCode::from(1.0))?
        .set_at(tokens(&["final", "approved"]), TimeCode::from(10.0))?;
    Ok(chair)
}

#[test]
fn labels_at_time() -> Result<(), SchemaError> {
    let chair = sampled()?;

    let at = |time: f64| -> Result<Vec<Token>, SchemaError> {
        Ok(LabelsQuery::at("category", TimeCode::from(time))?.direct_labels(&chair)?)
    };
    assert_eq!(at(1.0)?, tokens(&["wip"]));
    // Between samples the earlier one is still what the prim is labelled.
    assert_eq!(at(5.0)?, tokens(&["wip"]));
    assert_eq!(at(10.0)?, tokens(&["approved", "final"]));
    Ok(())
}

#[test]
fn labels_over_interval() -> Result<(), SchemaError> {
    let chair = sampled()?;

    // Every label carried at any sample in the interval, together.
    let whole = LabelsQuery::over("category", 0.0..=20.0)?;
    assert_eq!(whole.direct_labels(&chair)?, tokens(&["approved", "final", "wip"]));

    // An interval ending before the second sample does not reach it.
    let early = LabelsQuery::over("category", 1.0..=5.0)?;
    assert_eq!(early.direct_labels(&chair)?, tokens(&["wip"]));

    // An interval falling between samples holds the earlier one, which is what
    // the prim is labelled throughout it even though no sample lies inside.
    let between = LabelsQuery::over("category", 5.0..=8.0)?;
    assert_eq!(between.direct_labels(&chair)?, tokens(&["wip"]));

    // An open end leaves out the sample sitting on it, where a closed one
    // reads it.
    let up_to = LabelsQuery::over("category", 1.0..10.0)?;
    assert_eq!(up_to.direct_labels(&chair)?, tokens(&["wip"]));
    let through = LabelsQuery::over("category", 1.0..=10.0)?;
    assert_eq!(through.direct_labels(&chair)?, tokens(&["approved", "final", "wip"]));

    // An open start still reads the value held at it, being what the prim is
    // labelled just inside the interval.
    let after_first = LabelsQuery::over("category", gf::Interval::new(1.0, 5.0, false, true))?;
    assert_eq!(after_first.direct_labels(&chair)?, tokens(&["wip"]));
    Ok(())
}

#[test]
fn labels_over_interval_unsampled() -> Result<(), SchemaError> {
    let stage = memory()?;
    let chair = stage.define_prim("/World/Chair")?;
    let category = LabelsAPI::apply(&chair, "category")?;

    // With no samples authored, the interval's start resolves the default, and
    // the schema's fallback empty array behind it.
    let query = LabelsQuery::over("category", 0.0..=10.0)?;
    assert!(query.direct_labels(&chair)?.is_empty());

    category.create_labels_attr()?.set(tokens(&["static"]))?;
    let query = LabelsQuery::over("category", 0.0..=10.0)?;
    assert_eq!(query.direct_labels(&chair)?, tokens(&["static"]));
    Ok(())
}

#[test]
fn labels_after_last_sample() -> Result<(), SchemaError> {
    let chair = sampled()?;

    // A start above every sample is a time like any other, holding the last
    // sample authored rather than reaching back to the first.
    let after = LabelsQuery::over("category", f64::INFINITY..=f64::INFINITY)?;
    assert_eq!(after.direct_labels(&chair)?, tokens(&["approved", "final"]));
    Ok(())
}

#[test]
fn labels_before_first_sample() -> Result<(), SchemaError> {
    let chair = sampled()?;

    // An unbounded start holds no sample of its own, so it reaches back to the
    // earliest one authored.
    let before = LabelsQuery::over("category", ..=0.5)?;
    assert_eq!(before.direct_labels(&chair)?, tokens(&["wip"]));
    Ok(())
}
