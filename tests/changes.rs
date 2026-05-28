//! Integration tests for the [`pcp::Changes`] / `sdf::ChangeList` pipeline.
//!
//! Verifies surgical cache invalidation: that an authoring call drops only
//! the affected prim indices, not the whole cache, and that the classifier
//! still falls back to "blow the world" when the change touches the layer
//! stack itself.

use openusd::{sdf, usd};

fn open_in_memory() -> usd::Stage {
    usd::Stage::builder().in_memory("anon.usda").expect("in-memory stage")
}

/// Warm two sibling prim indices, author at one — the other must stay indexed.
#[test]
fn author_at_one_prim_keeps_sibling_indexed() {
    let stage = open_in_memory();
    stage.define_prim("/Foo").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Bar").unwrap().set_type_name("Xform").unwrap();

    // Force both indices into the cache.
    let _ = stage.type_name(&sdf::path("/Foo").unwrap()).unwrap();
    let _ = stage.type_name(&sdf::path("/Bar").unwrap()).unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
    assert!(stage.is_indexed(&sdf::path("/Bar").unwrap()));

    // Author at /Foo only — /Bar's cached index must survive.
    stage.override_prim("/Foo").unwrap().set_kind("component").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/Bar").unwrap()),
        "/Bar's index must not be dropped when authoring at /Foo",
    );
}

/// Attribute value writes never invalidate the owning prim's graph —
/// they are read through to live layer data.
#[test]
fn attribute_value_write_keeps_owner_indexed() {
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

    let _ = stage.type_name(&sdf::path("/A").unwrap()).unwrap();
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    // Set a different value — owner's graph must stay cached, and the new
    // value must be visible.
    let attr = attr.set(sdf::Value::Double(2.0)).unwrap();
    assert!(
        stage.is_indexed(&sdf::path("/A").unwrap()),
        "attribute value writes must not invalidate the prim graph",
    );
    assert_eq!(attr.get().unwrap(), Some(sdf::Value::Double(2.0)));
}

/// `instanceable` is on the significant-promoter list — authoring it must
/// drop the owner's cached index.
#[test]
fn set_instanceable_invalidates_owner() {
    let stage = open_in_memory();
    stage.define_prim("/Inst").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Other").unwrap().set_type_name("Xform").unwrap();
    let _ = stage.type_name(&sdf::path("/Inst").unwrap()).unwrap();
    let _ = stage.type_name(&sdf::path("/Other").unwrap()).unwrap();
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

/// `kind` is a metadata change on a path whose prim already has a spec —
/// not in the significant-promoter set, no spec adds/removes. The cached
/// index must survive, and the new opinion must still be visible because
/// field resolution walks live layer data.
#[test]
fn kind_change_no_op_for_cache() {
    let stage = open_in_memory();
    let prim = stage.define_prim("/A").unwrap().set_type_name("Xform").unwrap();
    let _ = stage.type_name(&sdf::path("/A").unwrap()).unwrap();
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    prim.set_kind("group").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/A").unwrap()),
        "spec-only field changes must not invalidate the prim graph",
    );
    assert_eq!(stage.kind("/A").unwrap().as_deref(), Some("group"));
}

/// `set_default_prim` writes `defaultPrim` at the root, which the
/// classifier promotes to significant-at-root — every cached index drops.
#[test]
fn default_prim_change_clears_root_cache() {
    let stage = open_in_memory();
    stage.define_prim("/World").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Other").unwrap().set_type_name("Xform").unwrap();

    let _ = stage.type_name(&sdf::path("/World").unwrap()).unwrap();
    let _ = stage.type_name(&sdf::path("/Other").unwrap()).unwrap();
    let pre = stage.indexed_count();
    assert!(pre >= 2);

    stage.set_default_prim("World").unwrap();

    // `defaultPrim` triggers a significant change at `/`, which clears
    // every cached index (drop_index_subtree("/") matches all).
    assert_eq!(
        stage.indexed_count(),
        0,
        "defaultPrim is significant-at-root; all indices must drop",
    );
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
}

/// `has_spec` against a path with no opinions caches an empty prim index.
/// `override_prim` on that path must invalidate the cached miss so the
/// subsequent `has_spec` reflects the freshly authored over.
#[test]
fn override_prim_after_cached_miss_invalidates() {
    let stage = open_in_memory();
    // Cached miss: warms an empty index at /A.
    assert!(!stage.has_spec("/A").unwrap());
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    stage.override_prim("/A").unwrap();

    assert!(
        stage.has_spec("/A").unwrap(),
        "inert add must invalidate cached empty index — otherwise has_spec keeps returning the pre-author miss",
    );
}

/// `Layer::create_prim` auto-creates missing ancestor over specs. The
/// change list must record those ancestors so a cached miss on the
/// ancestor path gets invalidated alongside the new leaf.
#[test]
fn define_prim_invalidates_auto_created_ancestors() {
    let stage = open_in_memory();
    // Warm cached misses at /A and /A/B.
    assert!(!stage.has_spec("/A").unwrap());
    assert!(!stage.has_spec("/A/B").unwrap());

    stage.define_prim("/A/B/C").unwrap().set_type_name("Xform").unwrap();

    assert!(
        stage.has_spec("/A").unwrap(),
        "auto-created /A ancestor must be visible after define_prim('/A/B/C')",
    );
    assert!(
        stage.has_spec("/A/B").unwrap(),
        "auto-created /A/B ancestor must be visible",
    );
    assert!(stage.prim_children("/A").unwrap().contains(&"B".to_string()));
    assert!(stage.prim_children("/A/B").unwrap().contains(&"C".to_string()));
}

/// `create_attribute` auto-creates the owning prim (and its ancestors) as
/// `over` specs if missing. Ancestor invalidation must propagate.
#[test]
fn create_attribute_invalidates_auto_created_owner() {
    let stage = open_in_memory();
    assert!(!stage.has_spec("/Mesh").unwrap());

    stage.create_attribute("/Mesh.x", "double").unwrap();

    assert!(
        stage.has_spec("/Mesh").unwrap(),
        "auto-created owning prim /Mesh must be visible after create_attribute",
    );
}

/// A second `define_prim` with the same specifier on an existing prim
/// must be a no-op for the composition cache.
#[test]
fn idempotent_define_prim_preserves_cache() {
    let stage = open_in_memory();
    stage.define_prim("/Foo").unwrap().set_type_name("Xform").unwrap();
    stage.define_prim("/Foo/Child").unwrap();
    let _ = stage.type_name(&sdf::path("/Foo").unwrap()).unwrap();
    let _ = stage.type_name(&sdf::path("/Foo/Child").unwrap()).unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));
    assert!(stage.is_indexed(&sdf::path("/Foo/Child").unwrap()));

    stage.define_prim("/Foo").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/Foo").unwrap()),
        "redundant define_prim with matching specifier must not drop the cached index",
    );
    assert!(
        stage.is_indexed(&sdf::path("/Foo/Child").unwrap()),
        "redundant define_prim must not invalidate descendant indices",
    );
}

/// `override_prim` on a path that already has a spec is a layer-level
/// no-op and must not invalidate the cached index.
#[test]
fn idempotent_override_prim_preserves_cache() {
    let stage = open_in_memory();
    stage.define_prim("/Foo").unwrap();
    let _ = stage.type_name(&sdf::path("/Foo").unwrap()).unwrap();
    assert!(stage.is_indexed(&sdf::path("/Foo").unwrap()));

    stage.override_prim("/Foo").unwrap();

    assert!(
        stage.is_indexed(&sdf::path("/Foo").unwrap()),
        "redundant override_prim on existing spec must not drop the cached index",
    );
}

/// `add_applied_schema` writes `apiSchemas`, which `Cache::api_schemas`
/// resolves off the cached prim index. The classifier must drop the
/// owner's index so the next `api_schemas` query sees the new opinion.
#[test]
fn add_applied_schema_invalidates_owner() {
    let stage = open_in_memory();
    let prim = stage.define_prim("/A").unwrap().set_type_name("Xform").unwrap();
    // Warm the cache.
    assert_eq!(stage.api_schemas(prim.path()).unwrap(), Vec::<String>::new());
    assert!(stage.is_indexed(&sdf::path("/A").unwrap()));

    prim.add_applied_schema("MaterialBindingAPI").unwrap();

    assert!(
        !stage.is_indexed(&sdf::path("/A").unwrap()),
        "apiSchemas authoring must invalidate the owner's cached prim index",
    );
    assert_eq!(
        stage.api_schemas(&sdf::path("/A").unwrap()).unwrap(),
        vec!["MaterialBindingAPI".to_string()],
    );
}

/// `set_default_prim` with the value that's already set must not blow
/// the cache.
#[test]
fn idempotent_set_default_prim_preserves_cache() {
    let stage = open_in_memory();
    stage.define_prim("/World").unwrap();
    stage.set_default_prim("World").unwrap();
    let _ = stage.type_name(&sdf::path("/World").unwrap()).unwrap();
    let pre = stage.indexed_count();
    assert!(pre > 0);

    stage.set_default_prim("World").unwrap();

    assert_eq!(
        stage.indexed_count(),
        pre,
        "redundant set_default_prim must not clear cached indices",
    );
}

/// Verify the basic Dependencies plumbing by opening a fixture with a
/// reference arc and observing through `prim_children` that composition
/// still produces correct results after the new dependency-aware cache.
#[test]
fn reference_fixture_composes_correctly() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let path = format!("{manifest}/fixtures/sublayer_override.usda");
    let stage = usd::Stage::open(&path).expect("open sublayer fixture");

    // Reading children warms the cache via the new dependency-tracking
    // ensure_index path. The composed result is the union of both layers.
    let children = stage.prim_children("/World").unwrap();
    assert!(children.contains(&"Cube".to_string()));
    assert!(children.contains(&"Sphere".to_string()));
    assert!(
        stage.is_indexed(&sdf::path("/World").unwrap()),
        "/World index must be cached after prim_children query",
    );
}
