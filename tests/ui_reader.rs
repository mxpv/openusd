//! Integration test for the `UsdUI` schema views against a fixture.

use anyhow::Result;

use openusd::schemas::ui::{Backdrop, ExpansionState, NodeGraphNodeAPI, SceneGraphPrimAPI};
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdUI_scene.usda";

#[test]
fn ui_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;

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
