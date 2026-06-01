//! Integration test for the `UsdUI` schema readers against a fixture.

use anyhow::Result;

use openusd::schemas::ui::{read_backdrop, read_nodegraph_node, read_scene_graph_prim, ExpansionState};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdUI_scene.usda";

#[test]
fn reads_ui_from_fixture() -> Result<()> {
    let stage = Stage::open(FIXTURE)?;
    let shader = sdf::path("/Mat/Surface")?;

    let sg = read_scene_graph_prim(&stage, &shader)?.expect("SceneGraphPrimAPI");
    assert_eq!(sg.display_name.as_deref(), Some("Surface"));
    assert_eq!(sg.display_group.as_deref(), Some("Shading"));

    let node = read_nodegraph_node(&stage, &shader)?.expect("NodeGraphNodeAPI");
    assert_eq!(node.pos, Some([12.0, 34.0]));
    assert_eq!(node.size, Some([180.0, 90.0]));
    assert_eq!(node.stacking_order, Some(3));
    assert_eq!(node.display_color, Some([0.2, 0.4, 0.8]));
    assert_eq!(node.expansion_state, Some(ExpansionState::Minimized));
    assert_eq!(node.doc_uri.as_deref(), Some("https://example.com/node"));

    let backdrop = read_backdrop(&stage, &sdf::path("/Mat/Note")?)?.expect("Backdrop");
    assert_eq!(backdrop.description.as_deref(), Some("lighting nodes"));

    // A prim without the applied API reads back as None.
    assert!(read_scene_graph_prim(&stage, &sdf::path("/Mat")?)?.is_none());
    Ok(())
}
