//! Composition-invalidation tests: the surgical cache invalidation that
//! `pcp::Changes` drives from a layer's `sdf::ChangeList` — an authoring call
//! drops only the affected prim indices, with a "blow the world" fallback for
//! layer-stack edits. The change-record derivation itself
//! (`sdf::ChangeList::from_overlay`) is unit-tested in `src/sdf/change.rs`.

use std::collections::HashMap;
use std::fs;
use std::path::Path as FsPath;

use anyhow::Result;
use openusd::{pcp, sdf, tf, usd};

#[test]
fn change_list_entry_dedups() {
    let mut cl = sdf::ChangeList::new();
    let p = sdf::Path::abs_root();
    cl.entry_mut(&p).flags |= sdf::ChangeFlags::ADD_NON_INERT_PRIM;
    cl.entry_mut(&p).info_changed.insert(tf::Token::new("specifier"));
    assert_eq!(cl.entries().len(), 1);
    assert!(cl.entries()[0].1.flags.contains(sdf::ChangeFlags::ADD_NON_INERT_PRIM));
    assert!(cl.entries()[0].1.info_changed.contains(&tf::Token::new("specifier")));
}

#[test]
fn change_list_empty_until_entry() {
    let mut cl = sdf::ChangeList::new();
    assert!(cl.is_empty());
    cl.entry_mut(&sdf::Path::abs_root());
    assert!(!cl.is_empty());
}

fn open_in_memory() -> usd::Stage {
    usd::Stage::builder().in_memory("anon.usda").expect("in-memory stage")
}

fn exists(stage: &usd::Stage, path: &str) -> bool {
    stage.prim(path).is_valid().unwrap()
}

fn child_names(stage: &usd::Stage, path: &str) -> Vec<String> {
    stage
        .prim(path)
        .child_names()
        .unwrap()
        .into_iter()
        .map(String::from)
        .collect()
}

/// Warm two sibling prim indices, author at one — the other must stay indexed.
#[test]
fn author_keeps_sibling_indexed() {
    let stage = open_in_memory();
    stage.define_prim("/Foo").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Bar").unwrap().set_type_name("Xform").unwrap();

    let _ = stage.prim(sdf::path("/Foo").unwrap()).type_name().unwrap();
    let _ = stage.prim(sdf::path("/Bar").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
    assert!(stage.is_indexed(&sdf::path("/Bar").unwrap()));

    stage.override_prim("/Foo").unwrap().set_kind("component").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/Bar").unwrap()),
        "/Bar's index must not be dropped when authoring at /Foo",
    );
}

/// A significant change at an ancestor invalidates a self-root-only descendant.
///
/// `/Foo/Bar`'s sole node is the skipped self-Root, so it registers only in the
/// layer-agnostic `by_path` map and never appears in the per-layer subtree
/// lookup. The literal-path subtree drop in `fanout_significant` still reaches
/// it, because it is a namespace descendant of the changed `/Foo`.
#[test]
fn significant_at_ancestor_drops_descendant() {
    let stage = open_in_memory();
    stage.define_prim("/Foo").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Foo/Bar").unwrap().set_type_name("Xform").unwrap();

    let _ = stage.prim(sdf::path("/Foo").unwrap()).type_name().unwrap();
    let _ = stage.prim(sdf::path("/Foo/Bar").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
    assert!(stage.is_indexed(&sdf::path("/Foo/Bar").unwrap()));

    stage.override_prim("/Foo").unwrap().set_instanceable(true).unwrap();

    assert!(
        !stage.is_indexed(&sdf::path("/Foo/Bar").unwrap()),
        "a significant change at /Foo must invalidate its self-root-only descendant /Foo/Bar",
    );
}

/// Attribute value writes never invalidate the owning prim's graph.
#[test]
fn attribute_value_keeps_owner_indexed() {
    let stage = open_in_memory();
    let attr = stage
        .define_prim("/A")
        .unwrap()
        .set_type_name("Xform")
        .unwrap()
        .create_attribute("x", "double")
        .unwrap()
        .set(sdf::Value::Double(1.0))
        .unwrap();

    let _ = stage.prim(sdf::path("/A").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    let attr = attr.set(sdf::Value::Double(2.0)).unwrap();
    assert!(
        stage.is_indexed(&sdf::path("/A").unwrap()),
        "attribute value writes must not invalidate the prim graph",
    );
    assert_eq!(attr.get().unwrap(), Some(sdf::Value::Double(2.0)));
}

/// `instanceable` is a significant-promoter — authoring it drops the index.
#[test]
fn set_instanceable_invalidates_owner() {
    let stage = open_in_memory();
    stage.define_prim("/Inst").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Other").unwrap().set_type_name("Xform").unwrap();
    let _ = stage.prim(sdf::path("/Inst").unwrap()).type_name().unwrap();
    let _ = stage.prim(sdf::path("/Other").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/Inst").unwrap()));

    stage.override_prim("/Inst").unwrap().set_instanceable(true).unwrap();

    assert!(
        !stage.is_indexed(&sdf::path("/Inst").unwrap()),
        "instanceable is a significant-tier field; owner must be invalidated",
    );
    assert!(
        stage.is_indexed(&sdf::path("/Other").unwrap()),
        "unrelated prim must remain indexed",
    );
}

/// `kind` is a spec-only metadata change on an existing prim — the cached
/// index survives, and the new opinion is still visible (live read).
#[test]
fn kind_change_no_op_for_cache() {
    let stage = open_in_memory();
    let prim = stage.define_prim("/A").unwrap().set_type_name("Xform").unwrap();
    let _ = stage.prim(sdf::path("/A").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    prim.set_kind("group").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/A").unwrap()),
        "spec-only field changes must not invalidate the prim graph",
    );
    assert_eq!(stage.prim("/A").kind().unwrap().as_deref(), Some("group"));
}

/// `set_default_prim` is significant-at-root — every cached index drops.
#[test]
fn default_prim_clears_root_cache() {
    let stage = open_in_memory();
    stage.define_prim("/World").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Other").unwrap().set_type_name("Xform").unwrap();

    let _ = stage.prim(sdf::path("/World").unwrap()).type_name().unwrap();
    let _ = stage.prim(sdf::path("/Other").unwrap()).type_name().unwrap();
    assert!(stage.indexed_count() >= 2);

    stage.set_default_prim("World").unwrap();

    assert_eq!(
        stage.indexed_count(),
        0,
        "defaultPrim is significant-at-root; all indices must drop",
    );
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
}

/// `override_prim` on a cached miss invalidates so the over becomes visible.
#[test]
fn override_after_cached_miss() {
    let stage = open_in_memory();
    assert!(!exists(&stage, "/A"));
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    stage.override_prim("/A").unwrap();

    assert!(exists(&stage, "/A"), "inert add must invalidate cached empty index");
}

/// Auto-created ancestor `over`s are recorded so a cached miss on the ancestor
/// path gets invalidated alongside the new leaf.
#[test]
fn define_invalidates_ancestors() {
    let stage = open_in_memory();
    assert!(!exists(&stage, "/A"));
    assert!(!exists(&stage, "/A/B"));

    stage.define_prim("/A/B/C").unwrap().set_type_name("Xform").unwrap();

    assert!(exists(&stage, "/A"), "auto-created /A must be visible");
    assert!(exists(&stage, "/A/B"), "auto-created /A/B must be visible");
    assert!(child_names(&stage, "/A").contains(&"B".to_string()));
    assert!(child_names(&stage, "/A/B").contains(&"C".to_string()));
}

/// `create_attribute` auto-creates the owning prim; the ancestor add must
/// invalidate the cached miss.
#[test]
fn create_attribute_invalidates_owner() {
    let stage = open_in_memory();
    assert!(!exists(&stage, "/Mesh"));

    stage.create_attribute("/Mesh.x", "double").unwrap();

    assert!(
        exists(&stage, "/Mesh"),
        "auto-created owning prim /Mesh must be visible after create_attribute",
    );
}

/// A redundant `define_prim` on an existing prim is a no-op for the cache.
#[test]
fn idempotent_define_preserves_cache() {
    let stage = open_in_memory();
    stage.define_prim("/Foo").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Foo/Child").unwrap();
    let _ = stage.prim(sdf::path("/Foo").unwrap()).type_name().unwrap();
    let _ = stage.prim(sdf::path("/Foo/Child").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
    assert!(stage.is_indexed(&sdf::path("/Foo/Child").unwrap()));

    stage.define_prim("/Foo").unwrap();

    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
    assert!(stage.is_indexed(&sdf::path("/Foo/Child").unwrap()));
}

/// A redundant `override_prim` on an existing spec is a no-op for the cache.
#[test]
fn idempotent_override_preserves_cache() {
    let stage = open_in_memory();
    stage.define_prim("/Foo").unwrap();
    let _ = stage.prim(sdf::path("/Foo").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));

    stage.override_prim("/Foo").unwrap();

    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
}

/// `add_applied_schema` writes `apiSchemas`, which is resolved off the cached
/// prim index — the owner's index must drop.
#[test]
fn add_applied_schema_invalidates_owner() {
    let stage = open_in_memory();
    let prim = stage.define_prim("/A").unwrap().set_type_name("Xform").unwrap();
    assert_eq!(stage.prim(prim.path()).api_schemas().unwrap(), Vec::<tf::Token>::new());
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    prim.add_applied_schema("MaterialBindingAPI").unwrap();

    assert!(
        !stage.is_indexed(&sdf::path("/A").unwrap()),
        "apiSchemas authoring must invalidate the owner's cached prim index",
    );
    assert_eq!(
        stage.prim(sdf::path("/A").unwrap()).api_schemas().unwrap(),
        vec![tf::Token::from("MaterialBindingAPI")],
    );
}

/// Re-setting `defaultPrim` to the current value must not blow the cache.
#[test]
fn idempotent_default_prim_preserves_cache() {
    let stage = open_in_memory();
    stage.define_prim("/World").unwrap();
    stage.set_default_prim("World").unwrap();
    let _ = stage.prim(sdf::path("/World").unwrap()).type_name().unwrap();
    let pre = stage.indexed_count();
    assert!(pre > 0);

    stage.set_default_prim("World").unwrap();

    assert_eq!(
        stage.indexed_count(),
        pre,
        "redundant set_default_prim must not clear cached indices"
    );
}

/// Writes a stage whose `/User` selects a variant through `${SEL}` while
/// `/Other` reads no variable, and opens it — the fixture behind the
/// fine-grained `expressionVariables` invalidation tests.
fn open_variant_fixture(dir: &tempfile::TempDir) -> Result<usd::Stage> {
    let root = dir.path().join("root.usda");
    fs::write(
        &root,
        r#"#usda 1.0
(
    expressionVariables = { string SEL = "x" }
)
def "User" (
    variantSets = "v"
    variants = { string v = "`${SEL}`" }
)
{
    variantSet "v" = {
        "x" { custom double vx = 1 }
        "y" { custom double vy = 2 }
    }
}
def "Other" {
    custom double o = 3
}
"#,
    )?;
    let stage = usd::Stage::open(root.to_str().unwrap())?;
    assert_eq!(stage.attribute("/User.vx").get::<f64>()?, Some(1.0), "SEL=x at open");
    assert_eq!(stage.attribute("/Other.o").get::<f64>()?, Some(3.0));
    assert!(stage.is_indexed(&sdf::path("/User")?));
    assert!(stage.is_indexed(&sdf::path("/Other")?));
    Ok(stage)
}

/// Editing `expressionVariables` to add a name no prim reads keeps every
/// cached index warm — the fine-grained diff finds no dependents (C++
/// `_DidChangeLayerStackExpressionVariables` step 4, empty intersection).
#[test]
fn unused_var_keeps_index() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let stage = open_variant_fixture(&dir)?;

    stage.set_expression_variables(HashMap::from([
        ("SEL".to_string(), sdf::Value::String("x".to_string())),
        ("FREE".to_string(), sdf::Value::String("z".to_string())),
    ]))?;

    assert!(
        stage.is_indexed(&sdf::path("/User")?),
        "/User reads SEL, whose value is unchanged — its index survives"
    );
    assert!(
        stage.is_indexed(&sdf::path("/Other")?),
        "/Other reads no variable — its index survives"
    );
    Ok(())
}

/// Changing a variable's value drops exactly the prims whose builds recorded
/// reading it: `/User`'s variant selection recomposes to the new branch while
/// `/Other` stays indexed.
#[test]
fn used_var_drops_user() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let stage = open_variant_fixture(&dir)?;

    stage.set_expression_variables(HashMap::from([(
        "SEL".to_string(),
        sdf::Value::String("y".to_string()),
    )]))?;

    assert!(
        !stage.is_indexed(&sdf::path("/User")?),
        "/User recorded reading SEL, so its index drops"
    );
    assert!(
        stage.is_indexed(&sdf::path("/Other")?),
        "/Other reads no variable — its index survives"
    );
    assert_eq!(
        stage.attribute("/User.vy").get::<f64>()?,
        Some(2.0),
        "/User recomposes with the new selection"
    );
    assert_eq!(stage.attribute("/User.vx").get::<f64>()?, None);
    Ok(())
}

/// A changed name that feeds a stack's own `${VAR}` sublayer entry is
/// significant for every prim using the stack — the membership swaps — so even
/// a prim reading no variable drops (C++ step 3, the sublayer-dependency hit).
#[test]
fn sublayer_dep_drops_stack() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    fs::write(
        &root,
        r#"#usda 1.0
(
    expressionVariables = { string W = "a" }
    subLayers = [@`"${W}.usda"`@]
)
def "Other" {
    custom double o = 3
}
"#,
    )?;
    fs::write(
        dir.path().join("a.usda"),
        r#"#usda 1.0
def "A" {
    custom double x = 1
}
"#,
    )?;
    fs::write(
        dir.path().join("b.usda"),
        r#"#usda 1.0
def "B" {
    custom double y = 2
}
"#,
    )?;

    let stage = usd::Stage::open(root.to_str().unwrap())?;
    assert_eq!(stage.attribute("/A.x").get::<f64>()?, Some(1.0), "W=a at open");
    assert_eq!(stage.attribute("/Other.o").get::<f64>()?, Some(3.0));

    stage.set_expression_variables(HashMap::from([("W".to_string(), sdf::Value::String("b".to_string()))]))?;

    assert!(
        !stage.is_indexed(&sdf::path("/Other")?),
        "W selects a root-stack sublayer, so the change is stack-significant"
    );
    assert_eq!(
        stage.attribute("/B.y").get::<f64>()?,
        Some(2.0),
        "the newly selected b.usda loads and composes"
    );
    assert_eq!(
        stage.attribute("/A.x").get::<f64>()?,
        None,
        "a.usda's selection dropped"
    );
    Ok(())
}

/// Authoring a reference target's first `expressionVariables` flips the target
/// stack's variable source (root → itself), which resyncs every prim using the
/// stack even though no prim recorded reading a variable (C++ step 2).
#[test]
fn source_change_resyncs() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    fs::write(
        &root,
        r#"#usda 1.0
def "P" (
    references = @t.usda@
) {}
def "Other" {
    custom double o = 3
}
"#,
    )?;
    fs::write(
        dir.path().join("t.usda"),
        r#"#usda 1.0
(
    defaultPrim = "P"
)
def "P" {
    custom double x = 1
}
"#,
    )?;

    let stage = usd::Stage::open(root.to_str().unwrap())?;
    assert_eq!(stage.attribute("/P.x").get::<f64>()?, Some(1.0));
    assert_eq!(stage.attribute("/Other.o").get::<f64>()?, Some(3.0));

    let target_id = stage
        .layer_identifiers()
        .into_iter()
        .find(|id| FsPath::new(id).ends_with("t.usda"))
        .expect("t.usda is loaded");
    stage.layer_mut(&target_id).expect("target layer is live").edit(|e| {
        e.set_expression_variables(HashMap::from([("V".to_string(), sdf::Value::String("x".to_string()))]))
    })?;

    assert!(
        !stage.is_indexed(&sdf::path("/P")?),
        "the target stack's variable source flipped, so its user resyncs"
    );
    assert!(
        stage.is_indexed(&sdf::path("/Other")?),
        "/Other does not use the target stack — its index survives"
    );
    assert_eq!(stage.attribute("/P.x").get::<f64>()?, Some(1.0), "/P recomposes");
    Ok(())
}

/// A root variable read inside a referenced stack: the root edit's delta
/// cascades to the seeded target stack (C++ step 5), and the prim recorded its
/// read through the ancestral sub-build merge, so exactly that prim resyncs
/// and recomposes against the newly selected asset.
#[test]
fn chain_propagation() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    fs::write(
        &root,
        r#"#usda 1.0
(
    expressionVariables = { string V = "x" }
)
def "P" (
    references = @a.usda@</Outer/Inner>
) {}
def "Other" {
    custom double o = 3
}
"#,
    )?;
    fs::write(
        dir.path().join("a.usda"),
        r#"#usda 1.0
def "Outer" (
    references = @`"${V}.usda"`@
)
{
    def "Inner" {}
}
"#,
    )?;
    fs::write(
        dir.path().join("x.usda"),
        r#"#usda 1.0
(
    defaultPrim = "O"
)
def "O" {
    def "Inner" {
        custom double vx = 1
    }
}
"#,
    )?;
    fs::write(
        dir.path().join("y.usda"),
        r#"#usda 1.0
(
    defaultPrim = "O"
)
def "O" {
    def "Inner" {
        custom double vy = 2
    }
}
"#,
    )?;

    let stage = usd::Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.vx").get::<f64>()?,
        Some(1.0),
        "V=x reaches the referenced stack's `${{V}}` reference"
    );
    assert_eq!(stage.attribute("/Other.o").get::<f64>()?, Some(3.0));

    stage.set_expression_variables(HashMap::from([("V".to_string(), sdf::Value::String("y".to_string()))]))?;

    assert!(
        !stage.is_indexed(&sdf::path("/P")?),
        "the delta cascades to the seeded target stack and finds /P's recorded read"
    );
    assert!(
        stage.is_indexed(&sdf::path("/Other")?),
        "/Other reads no variable — its index survives"
    );
    assert_eq!(
        stage.attribute("/P.vy").get::<f64>()?,
        Some(2.0),
        "/P recomposes against the newly selected y.usda"
    );
    assert_eq!(stage.attribute("/P.vx").get::<f64>()?, None);
    Ok(())
}

/// A failed `${VAR}` evaluation records the undefined name as a dependency, so
/// later defining the variable resyncs the prim and the repaired arc composes
/// — without the definition, the failure would pin forever.
#[test]
fn failure_records_dep() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    fs::write(
        &root,
        r#"#usda 1.0
def "P" (
    references = @`${TGT}`@
)
{
    custom double local = 5
}
"#,
    )?;
    fs::write(
        dir.path().join("t.usda"),
        r#"#usda 1.0
(
    defaultPrim = "P"
)
def "P" {
    custom double x = 1
}
"#,
    )?;

    let stage = usd::Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.local").get::<f64>()?,
        Some(5.0),
        "the prim composes past the failed arc expression"
    );
    assert!(
        stage
            .composition_errors()
            .iter()
            .any(|e| matches!(e, pcp::Error::InvalidExpression { .. })),
        "the undefined reference expression is diagnosed"
    );
    assert!(stage.is_indexed(&sdf::path("/P")?));

    stage.set_expression_variables(HashMap::from([(
        "TGT".to_string(),
        sdf::Value::String("t.usda".to_string()),
    )]))?;

    assert_eq!(
        stage.attribute("/P.x").get::<f64>()?,
        Some(1.0),
        "defining TGT resyncs /P and the repaired reference composes"
    );
    assert!(
        stage.composition_errors().is_empty(),
        "the healed expression stops reporting, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A reference fixture still composes correctly through the dependency-aware
/// cache after the change-recording rework.
#[test]
fn reference_fixture_composes() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let path = format!("{manifest}/fixtures/sublayer_override.usda");
    let stage = usd::Stage::open(&path).expect("open sublayer fixture");

    let children = child_names(&stage, "/World");
    assert!(children.contains(&"Cube".to_string()));
    assert!(children.contains(&"Sphere".to_string()));
    assert!(stage.is_indexed(&sdf::path("/World").unwrap()));
}
