//! Integration test for the UsdSemantics schema views against a fixture.

use openusd::Result;
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::Stage;
use openusd_schemas::semantics::LabelsAPI;

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
