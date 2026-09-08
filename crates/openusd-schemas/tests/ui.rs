//! Integration test for the `UsdUI` schema views against a fixture.

use openusd::Result;
use openusd::gf;
use openusd::usd::{SchemaBase, Stage};

use openusd::sdf;
use openusd::tf::Token;
use openusd_schemas::ui::{Backdrop, BackdropSchema, ExpansionState, NodeGraphNodeAPI, SceneGraphPrimAPI};

const FIXTURE: &str = "fixtures/usdUI_scene.usda";

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
    assert_eq!(node.stacking_order_attr().get::<i32>()?, Some(3));
    assert_eq!(node.display_color_attr().get::<[f32; 3]>()?, Some([0.2, 0.4, 0.8]));
    assert_eq!(
        node.expansion_state_attr().get::<ExpansionState>()?,
        Some(ExpansionState::Minimized)
    );
    assert_eq!(
        node.doc_uri_attr().get::<String>()?.as_deref(),
        Some("https://example.com/node")
    );

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
    assert_eq!(n.pos_attr().get::<gf::Vec2f>()?, Some(gf::vec2f(12.0, 34.0)));
    assert_eq!(n.size_attr().get::<gf::Vec2f>()?, Some(gf::vec2f(180.0, 90.0)));
    assert_eq!(n.stacking_order_attr().get::<i32>()?, Some(3));
    assert_eq!(
        n.display_color_attr().get::<gf::Vec3f>()?,
        Some(gf::vec3f(0.2, 0.4, 0.8))
    );
    assert_eq!(
        n.expansion_state_attr().get::<ExpansionState>()?,
        Some(ExpansionState::Minimized)
    );
    assert_eq!(
        n.doc_uri_attr().get::<String>()?.as_deref(),
        Some("https://example.com/node")
    );
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
