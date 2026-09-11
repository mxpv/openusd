//! Integration tests for the `UsdRender` schema views and the computed
//! render spec, against a hand-authored fixture scene.

use openusd::Result;
use openusd::gf;

use openusd::sdf::{self, Value};
use openusd::tf::Token;
use openusd::usd::Stage;
use openusd_schemas::render::{
    AspectRatioConformPolicy, Pass, PassSchema, Product, ProductSchema, ProductType, Settings, SettingsBaseSchema,
    SettingsSchema, SourceType, Var, VarSchema, compute_render_spec,
};

const FIXTURE: &str = "fixtures/usdRender_scene.usda";

fn open() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)
}

/// A `renderSettingsPrimPath` authored in the session layer overrides the
/// root layer's opinion, matching C++ `UsdStage::GetMetadata` composition.
#[test]
fn session_layer_overrides_settings_path() -> Result<()> {
    let stage = Stage::builder()
        .session_layer("fixtures/usdRender_session.usda")
        .open(FIXTURE)?;
    let path = Settings::stage_settings_path(&stage)?.expect("renderSettingsPrimPath");
    assert_eq!(path.as_str(), "/Render/sessionSettings");
    Ok(())
}

#[test]
fn reads_render_settings() -> Result<()> {
    let stage = open()?;
    let s = Settings::get(&stage, "/Render/settings")?.expect("Settings");
    assert_eq!(
        s.resolution_attr().get::<Value>()?.and_then(|v| v.try_as_vec_2i()),
        Some(openusd::gf::vec2i(1920, 1080))
    );
    assert_eq!(
        s.aspect_ratio_conform_policy_attr().get::<AspectRatioConformPolicy>()?,
        Some(AspectRatioConformPolicy::ExpandAperture)
    );
    assert_eq!(s.camera_rel().targets()?, vec![sdf::path("/World/Camera")?]);
    assert_eq!(
        s.included_purposes_attr()
            .get::<Value>()?
            .and_then(|v| v.try_as_token_vec())
            .map(|toks| toks.into_iter().map(String::from).collect::<Vec<String>>()),
        Some(vec!["default".to_string(), "render".to_string()])
    );
    assert_eq!(
        s.rendering_color_space_attr().get::<Token>()?.as_deref(),
        Some("lin_rec709")
    );
    assert_eq!(s.products_rel().targets()?, vec![sdf::path("/Render/products/beauty")?]);
    Ok(())
}

#[test]
fn reads_products_and_vars() -> Result<()> {
    let stage = open()?;
    let p = Product::get(&stage, "/Render/products/beauty")?.expect("Product");
    assert_eq!(p.product_type_attr().get::<ProductType>()?, Some(ProductType::Raster));
    assert_eq!(p.product_name_attr().get::<Token>()?.as_deref(), Some("beauty.exr"));
    // Product override of the settings 1920×1080.
    assert_eq!(
        p.resolution_attr().get::<Value>()?.and_then(|v| v.try_as_vec_2i()),
        Some(openusd::gf::vec2i(1024, 512))
    );
    assert_eq!(
        p.ordered_vars_rel().targets()?,
        vec![sdf::path("/Render/vars/color")?, sdf::path("/Render/vars/alpha")?]
    );

    let color = Var::get(&stage, "/Render/vars/color")?.expect("Var");
    assert_eq!(color.data_type_attr().get::<Token>()?.as_deref(), Some("color3f"));
    assert_eq!(color.source_type_attr().get::<SourceType>()?, Some(SourceType::Raw));
    assert_eq!(color.source_name_attr().get::<String>()?.as_deref(), Some("Ci"));
    Ok(())
}

#[test]
fn resolves_stage_settings_path() -> Result<()> {
    let stage = open()?;
    let path = Settings::stage_settings_path(&stage)?.expect("renderSettingsPrimPath");
    assert_eq!(path.as_str(), "/Render/settings");
    Ok(())
}

#[test]
fn computes_render_spec_end_to_end() -> Result<()> {
    let stage = open()?;
    let spec = compute_render_spec(&stage, &sdf::path("/Render/settings")?, &["ri"])?.expect("RenderSpec");

    // One product, two vars (color + alpha), referenced by index.
    assert_eq!(spec.products.len(), 1);
    assert_eq!(spec.render_vars.len(), 2);
    assert_eq!(spec.products[0].render_var_indices, vec![0, 1]);

    let p = &spec.products[0];
    // Product overrides resolution; camera inherited from the settings.
    assert_eq!(p.resolution, [1024, 512]);
    assert_eq!(p.camera_path.as_deref(), Some("/World/Camera"));
    // expandAperture: square 24×24 aperture vs a 2:1 image → width grows to 48.
    assert!((p.aperture_size[0] - 48.0).abs() < 1e-3);
    assert!((p.aperture_size[1] - 24.0).abs() < 1e-3);

    // The `ri:` delegate setting rides along on the settings level.
    assert_eq!(spec.namespaced_settings.len(), 1);
    assert_eq!(spec.namespaced_settings[0].0, "ri:hider:maxsamples");

    // Purposes carried from the settings.
    assert_eq!(spec.included_purposes, vec!["default", "render"]);
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
fn render_pass_roundtrip() -> Result<()> {
    let stage = memory()?;
    let p = Pass::define(&stage, "/Render/Passes/beauty")?;
    p.create_pass_type_attr()?.set(sdf::Value::token("prman"))?;
    p.create_command_attr()?.set(Value::StringVec(vec![
        "prman".into(),
        "-t:0".into(),
        "{fileName}".into(),
    ]))?;
    p.create_file_name_attr()?
        .set(Value::AssetPath("./beauty.rib".into()))?;
    p.create_render_source_rel()?.add_target("/Render/Settings")?;

    let p = Pass::get(&stage, "/Render/Passes/beauty")?.expect("Pass");
    assert_eq!(p.pass_type_attr().get::<Token>()?.as_deref(), Some("prman"));
    assert_eq!(
        p.command_attr().get::<Value>()?.and_then(|v| v.try_as_string_vec()),
        Some(vec!["prman".to_string(), "-t:0".to_string(), "{fileName}".to_string()])
    );
    assert_eq!(p.render_source_rel().targets()?, vec![sdf::path("/Render/Settings")?]);
    Ok(())
}

#[test]
fn render_product_roundtrip() -> Result<()> {
    let stage = memory()?;
    let p = Product::define(&stage, "/Render/Products/beauty")?;
    p.create_product_type_attr()?.set(ProductType::Raster)?;
    p.create_product_name_attr()?.set(sdf::Value::token("beauty.exr"))?;
    // A product-level override of an inherited base attribute.
    p.create_resolution_attr()?.set(gf::vec2i(512, 512))?;
    p.create_ordered_vars_rel()?.add_target("/Render/Vars/color")?;

    let p = Product::get(&stage, "/Render/Products/beauty")?.expect("Product");
    assert_eq!(p.product_type_attr().get::<ProductType>()?, Some(ProductType::Raster));
    assert_eq!(p.product_name_attr().get::<Token>()?.as_deref(), Some("beauty.exr"));
    assert_eq!(
        p.resolution_attr().get::<Value>()?.and_then(|v| v.try_as_vec_2i()),
        Some(gf::vec2i(512, 512))
    );
    assert_eq!(p.ordered_vars_rel().targets()?, vec![sdf::path("/Render/Vars/color")?]);
    Ok(())
}

#[test]
fn render_settings_roundtrip() -> Result<()> {
    let stage = memory()?;
    let s = Settings::define(&stage, "/Render/Settings")?;
    s.create_resolution_attr()?.set(gf::vec2i(1280, 720))?;
    s.create_aspect_ratio_conform_policy_attr()?
        .set(AspectRatioConformPolicy::AdjustApertureWidth)?;
    s.create_camera_rel()?.add_target("/World/Cam")?;
    s.create_products_rel()?.add_target("/Render/Products/beauty")?;
    s.create_included_purposes_attr()?
        .set(Value::TokenVec(vec!["default".into(), "render".into()]))?;
    s.create_rendering_color_space_attr()?
        .set(sdf::Value::token("lin_rec709"))?;

    let s = Settings::get(&stage, "/Render/Settings")?.expect("Settings");
    assert_eq!(
        s.resolution_attr().get::<Value>()?.and_then(|v| v.try_as_vec_2i()),
        Some(gf::vec2i(1280, 720))
    );
    assert_eq!(
        s.aspect_ratio_conform_policy_attr().get::<AspectRatioConformPolicy>()?,
        Some(AspectRatioConformPolicy::AdjustApertureWidth)
    );
    assert_eq!(s.camera_rel().targets()?, vec![sdf::path("/World/Cam")?]);
    assert_eq!(s.products_rel().targets()?, vec![sdf::path("/Render/Products/beauty")?]);
    assert_eq!(
        s.rendering_color_space_attr().get::<Token>()?.as_deref(),
        Some("lin_rec709")
    );

    // A non-Settings prim reads back as None.
    stage.define_prim("/NotSettings")?.set_type_name("Scope")?;
    assert!(Settings::get(&stage, "/NotSettings")?.is_none());
    Ok(())
}

#[test]
fn render_var_roundtrip() -> Result<()> {
    let stage = memory()?;
    let v = Var::define(&stage, "/Render/Vars/N")?;
    v.create_data_type_attr()?.set(sdf::Value::token("normal3f"))?;
    v.create_source_name_attr()?.set("Nworld".to_string())?;
    v.create_source_type_attr()?.set(SourceType::Primvar)?;

    let v = Var::get(&stage, "/Render/Vars/N")?.expect("Var");
    assert_eq!(v.data_type_attr().get::<Token>()?.as_deref(), Some("normal3f"));
    assert_eq!(v.source_name_attr().get::<String>()?.as_deref(), Some("Nworld"));
    assert_eq!(v.source_type_attr().get::<SourceType>()?, Some(SourceType::Primvar));
    Ok(())
}
