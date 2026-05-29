//! Integration tests for the [`openusd::schemas::shade`] module:
//! reading a hand-authored UsdShade fixture, and a full author →
//! read-back roundtrip on an in-memory stage.

use anyhow::Result;
use openusd::schemas::shade::{
    self, bind_material, define_material, define_shader, find_shade_prims, read_direct_binding, read_preview_surface,
    resolve_surface_shader, Channel,
};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdShade_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

#[test]
fn finds_every_shade_prim() -> Result<()> {
    let stage = open()?;
    let prims = find_shade_prims(&stage)?;
    assert_eq!(prims.materials, vec!["/World/Looks/BrickMat".to_string()]);
    assert!(prims.shaders.contains(&"/World/Looks/BrickMat/Surface".to_string()));
    assert!(prims.shaders.contains(&"/World/Looks/BrickMat/DiffuseTex".to_string()));
    Ok(())
}

#[test]
fn resolves_surface_terminal_to_shader() -> Result<()> {
    let stage = open()?;
    let shader = resolve_surface_shader(&stage, &sdf::path("/World/Looks/BrickMat")?)?.expect("surface shader");
    assert_eq!(shader.as_str(), "/World/Looks/BrickMat/Surface");
    Ok(())
}

#[test]
fn reads_preview_surface_channels_from_fixture() -> Result<()> {
    let stage = open()?;
    let ps = read_preview_surface(&stage, &sdf::path("/World/Looks/BrickMat")?)?.expect("UsdPreviewSurface");

    // diffuseColor is driven by a UsdUVTexture.
    assert_eq!(ps.diffuse_color.texture(), Some("./textures/brick_albedo.png"));
    // metallic / roughness / opacity are scalars.
    assert_eq!(ps.roughness.value(), Some(&0.8));
    assert_eq!(ps.metallic.value(), Some(&0.0));
    assert_eq!(ps.opacity.value(), Some(&1.0));
    // unauthored channels stay unset.
    assert!(!ps.emissive_color.is_set());
    assert!(matches!(ps.ior, Channel::Unset));
    Ok(())
}

#[test]
fn reads_material_bindings_from_fixture() -> Result<()> {
    let stage = open()?;
    let mesh = sdf::path("/World/Brick")?;

    // Direct all-purpose binding.
    let bound = read_direct_binding(&stage, &mesh, "")?.expect("all-purpose binding");
    assert_eq!(bound.as_str(), "/World/Looks/BrickMat");
    // Purpose-restricted preview binding.
    let preview = read_direct_binding(&stage, &mesh, "preview")?.expect("preview binding");
    assert_eq!(preview.as_str(), "/World/Looks/BrickMat");
    Ok(())
}

#[test]
fn author_then_read_back_roundtrip() -> Result<()> {
    let stage = Stage::builder().in_memory("anon.usda")?;
    stage.define_prim("/World")?.set_type_name("Xform")?;
    stage.define_prim("/World/Looks")?.set_type_name("Scope")?;
    stage.define_prim("/World/Geo")?.set_type_name("Mesh")?;

    // Texture → diffuseColor; scalar metallic/roughness.
    let tex = define_shader(&stage, sdf::path("/World/Looks/M/Albedo")?)?.set_id("UsdUVTexture")?;
    tex.create_input("file", "asset")?
        .set(sdf::Value::AssetPath("./wood.png".into()))?;
    tex.create_output("rgb", "float3")?;

    let surface = define_shader(&stage, sdf::path("/World/Looks/M/Surface")?)?.set_id("UsdPreviewSurface")?;
    surface
        .create_input("diffuseColor", "color3f")?
        .set_connections([sdf::path("/World/Looks/M/Albedo.outputs:rgb")?])?;
    surface.create_input("metallic", "float")?.set(sdf::Value::Float(1.0))?;
    surface
        .create_input("roughness", "float")?
        .set(sdf::Value::Float(0.3))?;
    surface.create_output("surface", "token")?;

    define_material(&stage, sdf::path("/World/Looks/M")?)?
        .connect_surface(sdf::path("/World/Looks/M/Surface.outputs:surface")?)?;

    bind_material(&stage, sdf::path("/World/Geo")?, sdf::path("/World/Looks/M")?)?;

    // Read everything back.
    let ps = read_preview_surface(&stage, &sdf::path("/World/Looks/M")?)?.expect("UsdPreviewSurface");
    assert_eq!(ps.diffuse_color.texture(), Some("./wood.png"));
    assert_eq!(ps.metallic.value(), Some(&1.0));
    assert_eq!(ps.roughness.value(), Some(&0.3));

    let bound = read_direct_binding(&stage, &sdf::path("/World/Geo")?, "")?.expect("binding");
    assert_eq!(bound.as_str(), "/World/Looks/M");
    assert!(stage.has_api_schema(&sdf::path("/World/Geo")?, "MaterialBindingAPI")?);

    // The shade-prim walk sees the authored material + shaders.
    let prims = shade::find_shade_prims(&stage)?;
    assert!(prims.materials.contains(&"/World/Looks/M".to_string()));
    assert_eq!(prims.shaders.len(), 2);
    Ok(())
}
