//! The core family's generated views over the public API.
//!
//! [`usd::CollectionAPI`] and [`usd::ClipsAPI`] carry hand-written behaviour
//! and are tested with it. The colour-space views carry none, so these check
//! that what the generator gave them — application, instance naming, the
//! declared properties — works on a stage.

use openusd::usd::{self, ColorSpaceAPI, ColorSpaceDefinitionAPI};
use openusd::{sdf, tf};

fn stage() -> usd::Stage {
    usd::Stage::builder()
        .in_memory("anon.usda")
        .expect("an in-memory stage")
}

/// A single-apply schema applies, is found again, and authors its property
/// under the name the schema declares.
#[test]
fn color_space_applies() {
    let stage = stage();
    let prim = stage.define_prim("/World").expect("a prim");
    assert!(ColorSpaceAPI::get(&stage, "/World").expect("a read").is_none());

    let api = ColorSpaceAPI::apply(&prim).expect("applies");
    api.create_color_space_name_attr()
        .expect("authors")
        .set(sdf::Value::token("lin_rec709_scene"))
        .expect("sets");

    let found = ColorSpaceAPI::get(&stage, "/World").expect("a read").expect("applied");
    assert_eq!(
        found.color_space_name_attr().path().to_string(),
        "/World.colorSpace:name"
    );
    assert_eq!(
        found.color_space_name_attr().get::<tf::Token>().expect("a read"),
        Some(tf::Token::from("lin_rec709_scene"))
    );
}

/// A multiple-apply schema keeps each instance apart: its properties live
/// under the instance name, and enumeration finds exactly what was applied.
#[test]
fn color_space_definition_instances() {
    let stage = stage();
    let prim = stage.define_prim("/World").expect("a prim");

    let custom = ColorSpaceDefinitionAPI::apply(&prim, "custom").expect("applies");
    ColorSpaceDefinitionAPI::apply(&prim, "other").expect("applies");
    assert_eq!(custom.name().as_str(), "custom");

    custom.create_gamma_attr().expect("authors").set(2.2_f32).expect("sets");
    assert_eq!(
        custom.gamma_attr().path().to_string(),
        "/World.colorSpaceDefinition:custom:gamma"
    );

    let found = ColorSpaceDefinitionAPI::get_instance(&prim, "custom")
        .expect("a read")
        .expect("applied");
    assert_eq!(found.gamma_attr().get::<f32>().expect("a read"), Some(2.2));

    let mut names: Vec<String> = ColorSpaceDefinitionAPI::get_all(&prim)
        .expect("a read")
        .iter()
        .map(|instance| instance.name().to_string())
        .collect();
    names.sort();
    assert_eq!(names, ["custom", "other"]);
    assert!(
        ColorSpaceDefinitionAPI::get_instance(&prim, "absent")
            .expect("a read")
            .is_none()
    );
}
