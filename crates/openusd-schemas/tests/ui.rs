//! Integration test for the `UsdUI` schema views against a fixture.

use openusd::Result;
use openusd::gf;
use openusd::usd::{Object, Property, SchemaBase, Stage};

use openusd::sdf;
use openusd::tf::Token;
use openusd_schemas::ui::{
    Backdrop, BackdropSchema, ExpansionState, Hints, NodeGraphNodeAPI, SceneGraphPrimAPI, hint_keys,
};

const FIXTURE: &str = "fixtures/usdUI_scene.usda";
const HINTS_FIXTURE: &str = "fixtures/usdUI_hints.usda";

/// `testenv/testUsdUIHints/hints.usda`, which authors every hint.
fn hints_stage() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(HINTS_FIXTURE)
}

/// Asserts the object tier of `hints`.
fn check_object<O: Object>(hints: &Hints<O>, display_name: Option<&str>, hidden: bool) -> Result<()> {
    assert_eq!(hints.display_name()?.as_deref(), display_name);
    assert_eq!(hints.is_hidden()?, hidden);
    Ok(())
}

/// Asserts the property tier of `hints`.
fn check_property<O: Property>(hints: &Hints<O>, display_group: Option<&str>, shown_if: Option<&str>) -> Result<()> {
    assert_eq!(hints.display_group()?.as_deref(), display_group);
    assert_eq!(hints.shown_if()?.as_deref(), shown_if);
    Ok(())
}

/// `testUsdUIHints.py:test_Fallbacks`: an object with no hints reads each
/// hint's fallback.
#[test]
fn hints_fallbacks() -> Result<()> {
    let stage = hints_stage()?;
    check_object(&Hints::new(stage.prim("/HintlessPrim")?), None, false)?;

    let attr = Hints::new(stage.attribute("/HintlessPrim.hintlessAttribute")?);
    check_object(&attr, None, false)?;
    check_property(&attr, None, None)?;
    Ok(())
}

/// The hints of an object the stage does not hold read their fallbacks, and
/// a setter is refused without authoring anything.
#[test]
fn missing_object_hints() -> Result<()> {
    let stage = hints_stage()?;
    let missing = Hints::new(stage.prim("/Missing")?);
    check_object(&missing, None, false)?;
    assert!(missing.set_display_name("name").is_err());
    assert!(!stage.prim("/Missing")?.is_valid()?);

    let attr = Hints::new(stage.attribute("/HintlessPrim.missing")?);
    check_property(&attr, None, None)?;
    assert!(attr.set_shown_if("x == 1").is_err());
    Ok(())
}

/// `testUsdUIHints.py:test_RelationshipHintsFromAsset`.
#[test]
fn relationship_hints_asset() -> Result<()> {
    let stage = hints_stage()?;
    let rel = stage.relationship("/HintsPrim.relationship")?;
    let hints = Hints::new(rel.clone());
    assert_eq!(hints.object(), &rel);
    check_property(&hints, Some("a group:a nested group"), Some("x == 3"))?;
    check_object(&hints, Some("a rel"), true)?;
    Ok(())
}

/// `testUsdUIHints.py:test_ObjectHintsSetters`.
#[test]
fn object_hints_setters() -> Result<()> {
    let stage = memory()?;
    let hints = Hints::new(stage.define_prim("/test_ObjectHintsSetters")?);

    assert_eq!(hints.display_name()?, None);
    let hints = hints.set_display_name("displayName")?;
    assert_eq!(hints.display_name()?.as_deref(), Some("displayName"));

    assert!(!hints.is_hidden()?);
    let hints = hints.set_hidden(true)?;
    assert!(hints.is_hidden()?);
    Ok(())
}

/// `testUsdUIHints.py:test_LegacyHintWrites`: a hint setter writes the core
/// field it supersedes too, and `shownIf` has none.
#[test]
fn legacy_hint_writes() -> Result<()> {
    let stage = memory()?;
    let attr = stage
        .define_prim("/test_LegacyHintWrites")?
        .attribute_builder("attr", "int")
        .build()?;
    assert_eq!(attr.display_name()?, None);
    assert_eq!(attr.display_group()?, None);
    assert!(!attr.is_hidden()?);

    let attr = Hints::new(attr)
        .set_display_name("display name")?
        .set_display_group("display group")?
        .set_hidden(true)?
        .set_shown_if("x == 1")?
        .into_object();
    assert_eq!(attr.display_name()?.as_deref(), Some("display name"));
    assert_eq!(attr.display_group()?.as_deref(), Some("display group"));
    assert!(attr.is_hidden()?);
    assert_eq!(
        attr.metadata_by_key(hint_keys::UI_HINTS, hint_keys::SHOWN_IF)?,
        Some(sdf::Value::String("x == 1".into()))
    );
    Ok(())
}

/// The `uiHints` key answers before the core field, and the core field
/// answers alone.
#[test]
fn hint_beats_legacy() -> Result<()> {
    let stage = memory()?;
    let prim = stage.define_prim("/P")?.set_display_name("old")?;
    assert_eq!(Hints::new(prim.clone()).display_name()?.as_deref(), Some("old"));

    let prim = prim.set_metadata_by_key(hint_keys::UI_HINTS, hint_keys::DISPLAY_NAME, "new".to_string())?;
    assert_eq!(Hints::new(prim).display_name()?.as_deref(), Some("new"));
    Ok(())
}

/// A hint of another type reads as absent, and the core field answers.
#[test]
fn hint_wrong_type() -> Result<()> {
    let stage = memory()?;
    let prim = stage
        .define_prim("/P")?
        .set_display_name("legacy")?
        .set_metadata_by_key(hint_keys::UI_HINTS, hint_keys::DISPLAY_NAME, 5)?
        .set_hidden(true)?
        .set_metadata_by_key(hint_keys::UI_HINTS, hint_keys::HIDDEN, "no".to_string())?;
    let hints = Hints::new(prim);
    assert_eq!(hints.display_name()?.as_deref(), Some("legacy"));
    assert!(hints.is_hidden()?);
    Ok(())
}

#[test]
fn ui_from_fixture() -> Result<()> {
    let stage = Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)?;

    let sg = SceneGraphPrimAPI::get(&stage, "/Mat/Surface")?.expect("SceneGraphPrimAPI");
    assert_eq!(sg.display_name_attr().get::<Token>()?.as_deref(), Some("Surface"));
    assert_eq!(sg.display_group_attr().get::<Token>()?.as_deref(), Some("Shading"));

    let node = NodeGraphNodeAPI::get(&stage, "/Mat/Surface")?.expect("NodeGraphNodeAPI");
    assert_eq!(node.pos_attr().get::<[f32; 2]>()?, Some([12.0, 34.0]));
    assert_eq!(node.size_attr().get::<[f32; 2]>()?, Some([180.0, 90.0]));
    assert_eq!(node.stacking_order()?, Some(3));
    assert_eq!(node.display_color_attr().get::<[f32; 3]>()?, Some([0.2, 0.4, 0.8]));
    assert_eq!(node.expansion_state()?, Some(ExpansionState::Minimized));
    assert_eq!(node.doc_uri()?.as_deref(), Some("https://example.com/node"));

    let backdrop = Backdrop::get(&stage, "/Mat/Note")?.expect("Backdrop");
    assert_eq!(
        backdrop.description_attr().get::<Token>()?.as_deref(),
        Some("lighting nodes")
    );

    // A prim without the applied API reads back as None.
    assert!(SceneGraphPrimAPI::get(&stage, sdf::path("/Mat")?)?.is_none());
    Ok(())
}

/// An in-memory stage carrying the schema data, which is what makes a prim its
/// type and resolves the fallbacks its schema declares.
fn memory() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")
}

#[test]
fn backdrop_roundtrip() -> Result<()> {
    let stage = memory()?;
    Backdrop::define(&stage, "/Mat/Note")?
        .create_description_attr()?
        .set(sdf::Value::token("lighting nodes"))?;

    let b = Backdrop::get(&stage, "/Mat/Note")?.expect("Backdrop");
    assert_eq!(b.description_attr().get::<Token>()?.as_deref(), Some("lighting nodes"));
    assert_eq!(Backdrop::KIND, openusd::usd::SchemaKind::ConcreteTyped);
    Ok(())
}

#[test]
fn nodegraph_node_roundtrip() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/Mat/Shader")?.set_type_name("Shader")?;
    let n = NodeGraphNodeAPI::apply(&stage.prim("/Mat/Shader")?)?;
    n.create_pos_attr()?.set(gf::vec2f(12.0, 34.0))?;
    n.create_size_attr()?.set(gf::vec2f(180.0, 90.0))?;
    n.create_stacking_order_attr()?.set(3)?;
    n.create_display_color_attr()?.set(gf::vec3f(0.2, 0.4, 0.8))?;
    n.create_icon_attr()?.set(sdf::Value::AssetPath("./node.png".into()))?;
    n.create_expansion_state_attr()?.set(ExpansionState::Minimized)?;
    n.create_doc_uri_attr()?.set("https://example.com/node".to_string())?;

    let n = NodeGraphNodeAPI::get(&stage, "/Mat/Shader")?.expect("NodeGraphNodeAPI");
    assert_eq!(n.pos()?, Some(gf::vec2f(12.0, 34.0)));
    assert_eq!(n.size_attr().get::<gf::Vec2f>()?, Some(gf::vec2f(180.0, 90.0)));
    assert_eq!(n.stacking_order()?, Some(3));
    assert_eq!(
        n.display_color_attr().get::<gf::Vec3f>()?,
        Some(gf::vec3f(0.2, 0.4, 0.8))
    );
    assert_eq!(n.expansion_state()?, Some(ExpansionState::Minimized));
    assert_eq!(n.doc_uri()?.as_deref(), Some("https://example.com/node"));
    Ok(())
}

#[test]
fn scene_graph_prim_roundtrip() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
    let sg = SceneGraphPrimAPI::apply(&stage.prim("/World/Mesh")?)?;
    sg.create_display_name_attr()?.set(sdf::Value::token("Hero Mesh"))?;
    sg.create_display_group_attr()?.set(sdf::Value::token("Characters"))?;

    let p = SceneGraphPrimAPI::get(&stage, "/World/Mesh")?.expect("SceneGraphPrimAPI");
    assert_eq!(p.display_name_attr().get::<Token>()?.as_deref(), Some("Hero Mesh"));
    assert_eq!(p.display_group_attr().get::<Token>()?.as_deref(), Some("Characters"));

    // Unapplied prim â†’ None.
    stage.define_prim("/Bare")?.set_type_name("Scope")?;
    assert!(SceneGraphPrimAPI::get(&stage, "/Bare")?.is_none());
    Ok(())
}
