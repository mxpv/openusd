//! Integration tests for the `UsdRender` schema reader and the computed
//! render spec, against a hand-authored fixture scene.

use anyhow::Result;

use openusd::schemas::render::{
    compute_render_spec, get_stage_render_settings, read_render_product, read_render_settings, read_render_var,
    AspectRatioConformPolicy, ProductType, SourceType,
};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdRender_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

/// A `renderSettingsPrimPath` authored in the session layer overrides the
/// root layer's opinion, matching C++ `UsdStage::GetMetadata` composition.
#[test]
fn session_layer_overrides_settings_prim_path() -> Result<()> {
    let stage = Stage::builder()
        .session_layer("fixtures/usdRender_session.usda")
        .open(FIXTURE)?;
    let path = get_stage_render_settings(&stage)?.expect("renderSettingsPrimPath");
    assert_eq!(path.as_str(), "/Render/sessionSettings");
    Ok(())
}

#[test]
fn reads_render_settings() -> Result<()> {
    let stage = open()?;
    let s = read_render_settings(&stage, &sdf::path("/Render/settings")?)?.expect("RenderSettings");
    assert_eq!(s.base.resolution, [1920, 1080]);
    assert_eq!(
        s.base.aspect_ratio_conform_policy,
        AspectRatioConformPolicy::ExpandAperture
    );
    assert_eq!(s.base.camera.as_deref(), Some("/World/Camera"));
    assert_eq!(s.included_purposes, vec!["default", "render"]);
    assert_eq!(s.material_binding_purposes, vec!["full".to_string(), String::new()]);
    assert_eq!(s.rendering_color_space.as_deref(), Some("lin_rec709"));
    assert_eq!(s.products, vec!["/Render/products/beauty".to_string()]);
    Ok(())
}

#[test]
fn reads_products_and_vars() -> Result<()> {
    let stage = open()?;
    let p = read_render_product(&stage, &sdf::path("/Render/products/beauty")?)?.expect("RenderProduct");
    assert_eq!(p.product_type, ProductType::Raster);
    assert_eq!(p.product_name, "beauty.exr");
    assert_eq!(p.base.resolution, [1024, 512]); // product override of the settings 1920×1080
    assert_eq!(
        p.ordered_vars,
        vec!["/Render/vars/color".to_string(), "/Render/vars/alpha".to_string()]
    );

    let color = read_render_var(&stage, &sdf::path("/Render/vars/color")?)?.expect("RenderVar");
    assert_eq!(color.data_type, "color3f");
    assert_eq!(color.source_type, SourceType::Raw);
    assert_eq!(color.source_name, "Ci");
    Ok(())
}

#[test]
fn resolves_stage_render_settings_metadata() -> Result<()> {
    let stage = open()?;
    let path = get_stage_render_settings(&stage)?.expect("renderSettingsPrimPath");
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
