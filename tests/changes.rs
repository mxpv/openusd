//! Change-recording and composition-invalidation tests.
//!
//! Covers the `EditProxy` recording delegate — the `sdf::ChangeList` it
//! produces from layer mutations — and the surgical cache invalidation that
//! `pcp::Changes` drives from that list: an authoring call drops only the
//! affected prim indices, with a "blow the world" fallback for layer-stack
//! edits.

use openusd::sdf::AbstractData;
use openusd::{sdf, tf, usd};

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

/// A blank in-memory backend with a pseudo-root, wrapped fresh in a proxy.
fn proxy() -> sdf::EditProxy {
    let mut data = sdf::Data::new();
    data.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot);
    sdf::EditProxy::new(Box::new(data))
}

/// Drain a proxy into a fresh list.
fn drained(p: &mut sdf::EditProxy) -> sdf::ChangeList {
    let mut cl = sdf::ChangeList::new();
    p.take(&mut cl);
    cl
}

fn entry<'a>(cl: &'a sdf::ChangeList, path: &str) -> Option<&'a sdf::ChangeEntry> {
    let path = sdf::path(path).unwrap();
    cl.iter().find(|(p, _)| *p == path).map(|(_, e)| e)
}

/// Whether the recorded entry at `path` carries `flag`.
fn has_flag(cl: &sdf::ChangeList, path: &str, flag: sdf::ChangeFlags) -> bool {
    entry(cl, path).is_some_and(|e| e.flags.contains(flag))
}

/// A freshly created `def` prim records a non-inert add at the leaf, inert
/// adds for the auto-created ancestors, and a property add for an attribute.
/// The auto-stamped `specifier` folds into the add, while an explicit opinion
/// like `typeName` is surfaced in `info_changed` so the classifier can see the
/// structural fields a fresh spec carries.
#[test]
fn records_prim_tree_adds() {
    let mut p = proxy();
    sdf::PrimSpec::new(&mut p, "/A/B/C", sdf::Specifier::Def, "Xform").unwrap();
    sdf::AttributeSpec::new(&mut p, "/A/B/C.size", "double", sdf::Variability::Varying, true).unwrap();
    let cl = drained(&mut p);

    assert!(has_flag(&cl, "/A", sdf::ChangeFlags::ADD_INERT_PRIM));
    assert!(has_flag(&cl, "/A/B", sdf::ChangeFlags::ADD_INERT_PRIM));
    assert!(has_flag(&cl, "/A/B/C", sdf::ChangeFlags::ADD_NON_INERT_PRIM));
    assert!(has_flag(&cl, "/A/B/C.size", sdf::ChangeFlags::ADD_PROPERTY));
    // The auto-stamped specifier folds into the add; the explicit typeName is
    // surfaced, but never a spurious specifier change.
    let leaf = &entry(&cl, "/A/B/C").unwrap().info_changed;
    assert!(leaf.iter().any(|t| t == sdf::FieldKey::TypeName.as_str()));
    assert!(!leaf.iter().any(|t| t == sdf::FieldKey::Specifier.as_str()));
}

/// `over` creates missing specs as `over`, recording inert adds.
#[test]
fn over_records_inert() {
    let mut p = proxy();
    sdf::PrimSpec::over(&mut p, "/X/Y").unwrap();
    let cl = drained(&mut p);
    assert!(has_flag(&cl, "/X", sdf::ChangeFlags::ADD_INERT_PRIM));
    assert!(has_flag(&cl, "/X/Y", sdf::ChangeFlags::ADD_INERT_PRIM));
}

/// A metadata write on a pre-existing prim records `info_changed` for the
/// field — without any add flag.
#[test]
fn records_metadata_on_existing() {
    let mut p = proxy();
    sdf::PrimSpec::new(&mut p, "/A", sdf::Specifier::Def, "").unwrap();
    let _ = drained(&mut p);

    p.set_field(
        &sdf::path("/A").unwrap(),
        sdf::FieldKey::Kind.as_str(),
        sdf::Value::token("component"),
    );
    let cl = drained(&mut p);
    let e = entry(&cl, "/A").unwrap();
    assert!(e.flags.is_empty());
    assert!(e.info_changed.contains(&tf::Token::new("kind")));
}

/// Creating a spec over an existing one replaces it (clearing its fields); the
/// proxy must record that as a change rather than silently dropping it.
#[test]
fn replacing_existing_spec_records() {
    let mut p = proxy();
    sdf::PrimSpec::new(&mut p, "/A", sdf::Specifier::Def, "Xform").unwrap();
    let _ = drained(&mut p);
    assert!(!p.is_dirty());

    p.create_spec(sdf::path("/A").unwrap(), sdf::SpecType::Prim);
    assert!(p.is_dirty(), "replacing an existing spec must record a change");
    assert!(entry(&drained(&mut p), "/A").is_some());
}

/// A root-metadata edit that also materializes the pseudo-root spec (a backend
/// with no pre-stamped `/`) must still record the field change — creating the
/// pseudo-root must not swallow the `defaultPrim` write that follows.
#[test]
fn metadata_creating_pseudo_root_records() {
    let mut p = sdf::EditProxy::new(Box::new(sdf::Data::new()));
    p.create_spec(sdf::Path::abs_root(), sdf::SpecType::PseudoRoot);
    p.set_field(
        &sdf::Path::abs_root(),
        sdf::FieldKey::DefaultPrim.as_str(),
        sdf::Value::token("World"),
    );
    let cl = drained(&mut p);

    let root = sdf::Path::abs_root();
    let e = cl
        .iter()
        .find(|(pp, _)| *pp == root)
        .map(|(_, e)| e)
        .expect("root metadata change recorded");
    assert!(e.info_changed.contains(&tf::Token::new("defaultPrim")));
}

/// Re-authoring an unchanged value records nothing (value-diff idempotence),
/// and a freshly wrapped (populated) backend starts clean (wrap-last).
#[test]
fn noop_and_wrap_last() {
    let mut p = proxy();
    assert!(!p.is_dirty(), "wrapping a populated backend records nothing");

    sdf::PrimSpec::new(&mut p, "/A", sdf::Specifier::Def, "Xform").unwrap();
    let _ = drained(&mut p);

    // Re-define the same def with the same type — no value changes.
    sdf::PrimSpec::new(&mut p, "/A", sdf::Specifier::Def, "Xform").unwrap();
    assert!(!p.is_dirty(), "redundant re-author records nothing");
    assert!(drained(&mut p).is_empty());
}

/// `take` moves entries into the caller's buffer, leaving the proxy empty and
/// ready to record the next op into a reused buffer.
#[test]
fn take_reuses_buffer() {
    let mut p = proxy();
    let mut scratch = sdf::ChangeList::new();

    sdf::PrimSpec::new(&mut p, "/A", sdf::Specifier::Def, "").unwrap();
    p.take(&mut scratch);
    assert!(has_flag(&scratch, "/A", sdf::ChangeFlags::ADD_NON_INERT_PRIM));
    assert!(!p.is_dirty());

    scratch.clear();
    sdf::PrimSpec::new(&mut p, "/B", sdf::Specifier::Def, "").unwrap();
    p.take(&mut scratch);
    assert!(has_flag(&scratch, "/B", sdf::ChangeFlags::ADD_NON_INERT_PRIM));
    assert!(entry(&scratch, "/A").is_none());
}

fn open_in_memory() -> usd::Stage {
    usd::Stage::builder().in_memory("anon.usda").expect("in-memory stage")
}

fn exists(stage: &usd::Stage, path: &str) -> bool {
    stage.prim_at(path).is_valid().unwrap()
}

fn child_names(stage: &usd::Stage, path: &str) -> Vec<String> {
    stage
        .prim_at(path)
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

    let _ = stage.prim_at(sdf::path("/Foo").unwrap()).type_name().unwrap();
    let _ = stage.prim_at(sdf::path("/Bar").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
    assert!(stage.is_indexed(&sdf::path("/Bar").unwrap()));

    stage.override_prim("/Foo").unwrap().set_kind("component").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/Bar").unwrap()),
        "/Bar's index must not be dropped when authoring at /Foo",
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

    let _ = stage.prim_at(sdf::path("/A").unwrap()).type_name().unwrap();
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
    let _ = stage.prim_at(sdf::path("/Inst").unwrap()).type_name().unwrap();
    let _ = stage.prim_at(sdf::path("/Other").unwrap()).type_name().unwrap();
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
    let _ = stage.prim_at(sdf::path("/A").unwrap()).type_name().unwrap();
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    prim.set_kind("group").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/A").unwrap()),
        "spec-only field changes must not invalidate the prim graph",
    );
    assert_eq!(stage.prim_at("/A").kind().unwrap().as_deref(), Some("group"));
}

/// `set_default_prim` is significant-at-root — every cached index drops.
#[test]
fn default_prim_clears_root_cache() {
    let stage = open_in_memory();
    stage.define_prim("/World").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Other").unwrap().set_type_name("Xform").unwrap();

    let _ = stage.prim_at(sdf::path("/World").unwrap()).type_name().unwrap();
    let _ = stage.prim_at(sdf::path("/Other").unwrap()).type_name().unwrap();
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
    let _ = stage.prim_at(sdf::path("/Foo").unwrap()).type_name().unwrap();
    let _ = stage.prim_at(sdf::path("/Foo/Child").unwrap()).type_name().unwrap();
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
    let _ = stage.prim_at(sdf::path("/Foo").unwrap()).type_name().unwrap();
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
    assert_eq!(
        stage.prim_at(prim.path()).api_schemas().unwrap(),
        Vec::<tf::Token>::new()
    );
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    prim.add_applied_schema("MaterialBindingAPI").unwrap();

    assert!(
        !stage.is_indexed(&sdf::path("/A").unwrap()),
        "apiSchemas authoring must invalidate the owner's cached prim index",
    );
    assert_eq!(
        stage.prim_at(sdf::path("/A").unwrap()).api_schemas().unwrap(),
        vec![tf::Token::from("MaterialBindingAPI")],
    );
}

/// Re-setting `defaultPrim` to the current value must not blow the cache.
#[test]
fn idempotent_default_prim_preserves_cache() {
    let stage = open_in_memory();
    stage.define_prim("/World").unwrap();
    stage.set_default_prim("World").unwrap();
    let _ = stage.prim_at(sdf::path("/World").unwrap()).type_name().unwrap();
    let pre = stage.indexed_count();
    assert!(pre > 0);

    stage.set_default_prim("World").unwrap();

    assert_eq!(
        stage.indexed_count(),
        pre,
        "redundant set_default_prim must not clear cached indices"
    );
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
