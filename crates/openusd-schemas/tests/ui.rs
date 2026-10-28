//! Integration test for the `UsdUI` schema views against a fixture.

mod common;

use openusd::gf;
use openusd::usd::{self, Object, Property, SchemaBase, Stage};
use openusd::{Result, vt};
use openusd_schemas::SchemaError;

use openusd::sdf;
use openusd::tf;
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

/// Asserts the prim tier of `hints`: the two dictionaries, each of their
/// entries read alone, and a group neither holds.
fn check_prim(hints: &Hints<usd::Prim>, expanded: &vt::Dictionary, shown_if: &vt::Dictionary) -> Result<()> {
    assert_eq!(&hints.groups_expanded()?, expanded);
    for (group, value) in expanded.iter() {
        assert_eq!(hints.group_expanded(group)?, value.try_as_bool_ref() == Some(&true));
    }
    assert!(!hints.group_expanded("non-existent")?);

    assert_eq!(&hints.groups_shown_if()?, shown_if);
    for (group, value) in shown_if.iter() {
        assert_eq!(hints.group_shown_if(group)?.as_ref(), value.try_as_string_ref());
    }
    assert_eq!(hints.group_shown_if("non-existent")?, None);
    Ok(())
}

/// Asserts the attribute tier of `hints`.
fn check_attribute(hints: &Hints<usd::Attribute>, labels: &vt::Dictionary, order: &[&str]) -> Result<()> {
    assert_eq!(&hints.value_labels()?, labels);
    assert_eq!(
        hints.value_labels_order()?,
        order.iter().map(|&s| tf::Token::from(s)).collect::<Vec<_>>()
    );
    Ok(())
}

/// A dictionary of `entries`.
fn dict<const N: usize>(entries: [(&str, vt::Value); N]) -> vt::Dictionary {
    entries
        .into_iter()
        .map(|(key, value)| (key.to_owned(), value))
        .collect()
}

/// `testUsdUIHints.py:test_Fallbacks`: an object with no hints reads each
/// hint's fallback.
#[test]
fn hints_fallbacks() -> Result<()> {
    let stage = hints_stage()?;
    let prim = Hints::new(stage.prim("/HintlessPrim")?);
    check_object(&prim, None, false)?;
    check_prim(&prim, &vt::Dictionary::default(), &vt::Dictionary::default())?;

    let attr = Hints::new(stage.attribute("/HintlessPrim.hintlessAttribute")?);
    check_object(&attr, None, false)?;
    check_property(&attr, None, None)?;
    check_attribute(&attr, &vt::Dictionary::default(), &[])?;
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
        Some(vt::Value::String("x == 1".into()))
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
    assert_eq!(sg.display_name_attr().get::<tf::Token>()?.as_deref(), Some("Surface"));
    assert_eq!(sg.display_group_attr().get::<tf::Token>()?.as_deref(), Some("Shading"));

    let node = NodeGraphNodeAPI::get(&stage, "/Mat/Surface")?.expect("NodeGraphNodeAPI");
    assert_eq!(node.pos_attr().get::<[f32; 2]>()?, Some([12.0, 34.0]));
    assert_eq!(node.size_attr().get::<[f32; 2]>()?, Some([180.0, 90.0]));
    assert_eq!(node.stacking_order()?, Some(3));
    assert_eq!(node.display_color_attr().get::<[f32; 3]>()?, Some([0.2, 0.4, 0.8]));
    assert_eq!(node.expansion_state()?, Some(ExpansionState::Minimized));
    assert_eq!(node.doc_uri()?.as_deref(), Some("https://example.com/node"));

    let backdrop = Backdrop::get(&stage, "/Mat/Note")?.expect("Backdrop");
    assert_eq!(
        backdrop.description_attr().get::<tf::Token>()?.as_deref(),
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
        .set(vt::Value::token("lighting nodes"))?;

    let b = Backdrop::get(&stage, "/Mat/Note")?.expect("Backdrop");
    assert_eq!(
        b.description_attr().get::<tf::Token>()?.as_deref(),
        Some("lighting nodes")
    );
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
    n.create_icon_attr()?.set(vt::Value::AssetPath("./node.png".into()))?;
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
    sg.create_display_name_attr()?.set(vt::Value::token("Hero Mesh"))?;
    sg.create_display_group_attr()?.set(vt::Value::token("Characters"))?;

    let p = SceneGraphPrimAPI::get(&stage, "/World/Mesh")?.expect("SceneGraphPrimAPI");
    assert_eq!(p.display_name_attr().get::<tf::Token>()?.as_deref(), Some("Hero Mesh"));
    assert_eq!(
        p.display_group_attr().get::<tf::Token>()?.as_deref(),
        Some("Characters")
    );

    // Unapplied prim â†’ None.
    stage.define_prim("/Bare")?.set_type_name("Scope")?;
    assert!(SceneGraphPrimAPI::get(&stage, "/Bare")?.is_none());
    Ok(())
}

/// `testUsdUIHints.py:test_PrimHintsFromAsset`.
#[test]
fn prim_hints_asset() -> Result<()> {
    let stage = hints_stage()?;
    let hints = Hints::new(stage.prim("/HintsPrim")?);
    check_prim(
        &hints,
        &dict([
            ("a group", vt::Value::Bool(true)),
            ("a group:a nested group", vt::Value::Bool(false)),
        ]),
        &dict([("a group", vt::Value::from("x == 1"))]),
    )?;
    check_object(&hints, Some("a prim"), true)?;
    Ok(())
}

/// `testUsdUIHints.py:test_PrimHintsSetters`.
#[test]
fn prim_hints_setters() -> Result<(), SchemaError> {
    let stage = memory()?;
    let hints = Hints::new(stage.define_prim("/test_PrimHintsSetters")?);
    check_prim(&hints, &vt::Dictionary::default(), &vt::Dictionary::default())?;
    assert!(!hints.group_expanded("group:subgroup")?);

    let hints = hints.set_groups_expanded([("group", true), ("group:subgroup", true)])?;
    let mut expanded = dict([
        ("group", vt::Value::Bool(true)),
        ("group:subgroup", vt::Value::Bool(true)),
    ]);
    check_prim(&hints, &expanded, &vt::Dictionary::default())?;
    assert!(!hints.group_expanded("group2")?);

    let hints = hints.set_group_expanded("group2", true)?;
    expanded.insert("group2".into(), vt::Value::Bool(true));
    check_prim(&hints, &expanded, &vt::Dictionary::default())?;

    let hints = hints.set_groups_shown_if([("group", "x == 1")])?;
    check_prim(&hints, &expanded, &dict([("group", vt::Value::from("x == 1"))]))?;
    assert_eq!(hints.group_shown_if("group2")?, None);

    let hints = hints.set_group_shown_if("group2", "x == 2")?;
    check_prim(
        &hints,
        &expanded,
        &dict([
            ("group", vt::Value::from("x == 1")),
            ("group2", vt::Value::from("x == 2")),
        ]),
    )?;
    Ok(())
}

/// A nested group's expansion is one top-level key of the dictionary.
#[test]
fn group_expanded_flat() -> Result<(), SchemaError> {
    let stage = memory()?;
    let hints = Hints::new(stage.define_prim("/P")?).set_group_expanded("A:B", true)?;
    assert_eq!(hints.groups_expanded()?, dict([("A:B", vt::Value::Bool(true))]));
    assert!(hints.group_expanded("A:B")?);
    Ok(())
}

/// A nested group's shown-if expression nests in the dictionary, as the
/// group extends the key path.
#[test]
fn group_shown_nested() -> Result<()> {
    let stage = memory()?;
    let hints = Hints::new(stage.define_prim("/P")?).set_group_shown_if("A:B", "x == 1")?;
    assert_eq!(
        hints.groups_shown_if()?,
        dict([("A", vt::Value::Dictionary(dict([("B", vt::Value::from("x == 1"))])))])
    );
    assert_eq!(hints.group_shown_if("A:B")?.as_deref(), Some("x == 1"));
    Ok(())
}

/// An empty group name is an empty key of the expansion dictionary.
#[test]
fn group_expanded_empty() -> Result<(), SchemaError> {
    let stage = memory()?;
    let hints = Hints::new(stage.define_prim("/P")?).set_group_expanded("", true)?;
    assert_eq!(hints.groups_expanded()?, dict([("", vt::Value::Bool(true))]));
    assert!(hints.group_expanded("")?);
    Ok(())
}

/// An empty group name ends the key path in an empty component, which is an
/// empty key of the shown-if dictionary, as `TfStringSplit` keeps it.
#[test]
fn group_shown_empty() -> Result<()> {
    let stage = memory()?;
    let hints = Hints::new(stage.define_prim("/P")?).set_group_shown_if("", "x == 1")?;
    assert_eq!(hints.groups_shown_if()?, dict([("", vt::Value::from("x == 1"))]));
    assert_eq!(hints.group_shown_if("")?.as_deref(), Some("x == 1"));
    Ok(())
}

/// A stage whose root layer, the edit target, sublayers `weak.usda`, which
/// authors `/P` with the `uiHints` entries `hints` (`usda` source).
fn weaker_hints_stage(hints: &str) -> Result<(tempfile::TempDir, Stage)> {
    let weak = format!("#usda 1.0\n\ndef \"P\" (\n    uiHints = {{\n        {hints}\n    }}\n)\n{{\n}}\n");
    let root = "#usda 1.0\n(\n    subLayers = [@./weak.usda@]\n)\n";
    common::open_files(&[("weak.usda", &weak), ("root.usda", root)], "root.usda")
}

/// The text of `stage`'s root layer.
fn root_text(stage: &Stage) -> Result<String> {
    Ok(stage.root_layer().export_to_string()?)
}

/// The text of `stage`'s root layer and of the layer it sublayers.
fn layer_texts(stage: &Stage) -> Result<[String; 2]> {
    let weak = stage
        .layer_identifiers()
        .into_iter()
        .find(|id| id.ends_with("weak.usda"))
        .expect("the weak layer is on the stage");
    let weak = stage.layer(&weak).expect("the weak layer").export_to_string()?;
    Ok([root_text(stage)?, weak])
}

/// Setting one group's expansion writes the whole composed dictionary to the
/// edit target, the entries a weaker layer authors included.
#[test]
fn group_expanded_weaker() -> Result<(), SchemaError> {
    let (_dir, stage) = weaker_hints_stage("dictionary displayGroupsExpanded = { bool old = 1 }")?;
    assert!(!root_text(&stage)?.contains("old"));
    let hints = Hints::new(stage.prim("/P")?).set_group_expanded("new", false)?;

    let root = root_text(&stage)?;
    assert!(root.contains("old") && root.contains("new"), "{root}");
    assert_eq!(
        hints.groups_expanded()?,
        dict([("old", vt::Value::Bool(true)), ("new", vt::Value::Bool(false))])
    );
    Ok(())
}

/// A weaker layer's entry of the wrong type refuses the read-modify-write,
/// and no layer changes.
#[test]
fn group_expanded_malformed() -> Result<(), SchemaError> {
    let (_dir, stage) =
        weaker_hints_stage("dictionary displayGroupsExpanded = { bool good = 1\n string bad = \"yes\" }")?;
    let before = layer_texts(&stage)?;
    let result = Hints::new(stage.prim("/P")?).set_group_expanded("new", true);
    assert!(
        matches!(
            &result,
            Err(SchemaError::HintEntryType { key: hint_keys::DISPLAY_GROUPS_EXPANDED, entry }) if entry == "bad"
        ),
        "{result:?}"
    );
    assert_eq!(layer_texts(&stage)?, before);
    Ok(())
}

/// Setting one group's shown-if expression writes that key path alone, beside
/// an entry of another type, which stays as authored.
#[test]
fn group_shown_sibling() -> Result<()> {
    let (_dir, stage) = weaker_hints_stage("dictionary displayGroupsShownIf = { int bad = 5 }")?;
    let hints = Hints::new(stage.prim("/P")?).set_group_shown_if("good", "x == 1")?;
    assert_eq!(
        hints.groups_shown_if()?,
        dict([("bad", vt::Value::Int(5)), ("good", vt::Value::from("x == 1"))])
    );
    Ok(())
}

/// `testUsdUIHints.py:test_AttributeHintsFromAsset`.
#[test]
fn attribute_hints_asset() -> Result<()> {
    let stage = hints_stage()?;
    let hints = Hints::new(stage.attribute("/HintsPrim.attribute")?);
    check_attribute(
        &hints,
        &dict([
            ("low", vt::Value::Int(1)),
            ("med", vt::Value::Int(2)),
            ("high", vt::Value::Int(3)),
        ]),
        &["low", "med", "high"],
    )?;
    check_property(&hints, Some("a group"), Some("x == 2"))?;
    check_object(&hints, Some("an attr"), true)?;
    Ok(())
}

/// `testUsdUIHints.py:test_AttributeHintsSetters`.
#[test]
fn attribute_hints_setters() -> Result<()> {
    let stage = memory()?;
    let attr = stage
        .define_prim("/test_AttributeHintsSetters")?
        .attribute_builder("newAttribute", "int")
        .build()?;
    let hints = Hints::new(attr);
    check_attribute(&hints, &vt::Dictionary::default(), &[])?;

    let labels = dict([("round", vt::Value::Int(1)), ("square", vt::Value::Int(2))]);
    let hints = hints.set_value_labels(labels.clone())?;
    check_attribute(&hints, &labels, &[])?;

    let hints = hints.set_value_labels_order(["square", "round"])?;
    check_attribute(&hints, &labels, &["square", "round"])?;
    Ok(())
}

/// `testUsdUIHints.py:test_AuthorValueLabels`: each label authors its value,
/// on an `int` attribute and on a `token[]` one, and a label no value has
/// authors nothing.
#[test]
fn apply_value_labels() -> Result<(), SchemaError> {
    let stage = hints_stage()?;
    for (path, initial) in [
        ("/HintsPrim.attribute", vt::Value::Int(1)),
        ("/HintsPrim.tokenArrayAttr", vt::Value::TokenVec(Vec::new())),
    ] {
        let hints = Hints::new(stage.attribute(path)?);
        assert_eq!(hints.object().get::<vt::Value>()?, Some(initial), "{path}");
        for (label, value) in &hints.value_labels()? {
            assert!(hints.apply_value_label(label)?, "{path} {label}");
            assert_eq!(
                hints.object().get::<vt::Value>()?.as_ref(),
                Some(value),
                "{path} {label}"
            );
        }

        let current = hints.object().get::<vt::Value>()?;
        assert!(!hints.apply_value_label("non-existent")?);
        assert_eq!(hints.object().get::<vt::Value>()?, current);
    }
    Ok(())
}

/// A label whose value has another type than the attribute's is refused,
/// and the value stays as it was.
#[test]
fn value_label_mismatch() -> Result<(), SchemaError> {
    let stage = memory()?;
    let attr = stage
        .define_prim("/P")?
        .attribute_builder("count", "int")
        .set(3)
        .build()?;
    let hints = Hints::new(attr).set_value_labels(dict([("bad", vt::Value::from("three"))]))?;
    assert!(hints.apply_value_label("bad").is_err());
    assert_eq!(hints.object().get::<i32>()?, Some(3));
    Ok(())
}
