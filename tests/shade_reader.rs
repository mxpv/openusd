//! Integration tests for the [`openusd::schemas::shade`] module: reading a
//! hand-authored UsdShade fixture, and a full author → read-back roundtrip on
//! an in-memory stage.

use anyhow::Result;
use openusd::schemas::shade::{self, Channel, Connectable, Material, MaterialBindingAPI, Shader};
use openusd::sdf;
use openusd::usd::{PrimPredicate, Stage};

const FIXTURE: &str = "fixtures/usdShade_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

/// Every `Material` on the stage, found by traversing and gating each prim
/// through `Material::get` — the C++-style `prim.IsA<UsdShadeMaterial>()` filter.
fn materials(stage: &Stage) -> Result<Vec<Material>> {
    typed(stage, Material::get)
}

/// Every `Shader` on the stage (`prim.IsA<UsdShadeShader>()`).
fn shaders(stage: &Stage) -> Result<Vec<Shader>> {
    typed(stage, Shader::get)
}

/// Traverse `stage` and collect the prims that `get` resolves to a view.
fn typed<S>(stage: &Stage, get: impl Fn(&Stage, sdf::Path) -> Result<Option<S>>) -> Result<Vec<S>> {
    let mut paths = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT_PROXIES, |p| paths.push(p.clone()))?;
    paths.into_iter().filter_map(|p| get(stage, p).transpose()).collect()
}

#[test]
fn finds_every_shade_prim() -> Result<()> {
    let stage = open()?;
    let material_paths: Vec<_> = materials(&stage)?
        .iter()
        .map(|m| m.path().as_str().to_string())
        .collect();
    let shader_paths: Vec<_> = shaders(&stage)?.iter().map(|s| s.path().as_str().to_string()).collect();
    assert_eq!(material_paths, vec!["/World/Looks/BrickMat".to_string()]);
    assert!(shader_paths.contains(&"/World/Looks/BrickMat/Surface".to_string()));
    assert!(shader_paths.contains(&"/World/Looks/BrickMat/DiffuseTex".to_string()));
    Ok(())
}

#[test]
fn resolves_surface_terminal_to_shader() -> Result<()> {
    let stage = open()?;
    let mat = Material::get(&stage, "/World/Looks/BrickMat")?.expect("Material");
    let shader = mat.compute_surface_source()?.expect("surface shader");
    assert_eq!(shader.path().as_str(), "/World/Looks/BrickMat/Surface");
    Ok(())
}

#[test]
fn reads_preview_surface_channels_from_fixture() -> Result<()> {
    let stage = open()?;
    let ps = shade::read_preview_surface(&stage, &sdf::path("/World/Looks/BrickMat")?)?.expect("UsdPreviewSurface");

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
    let binding = MaterialBindingAPI::get(&stage, "/World/Brick")?.expect("MaterialBindingAPI");

    // Direct all-purpose binding.
    let bound = binding.direct_binding("")?.expect("all-purpose binding");
    assert_eq!(bound.as_str(), "/World/Looks/BrickMat");
    // Purpose-restricted preview binding.
    let preview = binding.direct_binding("preview")?.expect("preview binding");
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
    let tex = Shader::define(&stage, "/World/Looks/M/Albedo")?;
    tex.create_id_attr()?.set("UsdUVTexture".to_string())?;
    tex.create_input("file", "asset")?
        .set(sdf::Value::AssetPath("./wood.png".into()))?;
    tex.create_output("rgb", "float3")?;

    let surface = Shader::define(&stage, "/World/Looks/M/Surface")?;
    surface.create_id_attr()?.set("UsdPreviewSurface".to_string())?;
    surface
        .create_input("diffuseColor", "color3f")?
        .set_connections([sdf::path("/World/Looks/M/Albedo.outputs:rgb")?])?;
    surface.create_input("metallic", "float")?.set(sdf::Value::Float(1.0))?;
    surface
        .create_input("roughness", "float")?
        .set(sdf::Value::Float(0.3))?;
    surface.create_output("surface", "token")?;

    Material::define(&stage, "/World/Looks/M")?
        .create_surface_output()?
        .set_connections([sdf::path("/World/Looks/M/Surface.outputs:surface")?])?;

    MaterialBindingAPI::apply(&stage, sdf::path("/World/Geo")?)?.bind(sdf::path("/World/Looks/M")?)?;

    // Read everything back.
    let ps = shade::read_preview_surface(&stage, &sdf::path("/World/Looks/M")?)?.expect("UsdPreviewSurface");
    assert_eq!(ps.diffuse_color.texture(), Some("./wood.png"));
    assert_eq!(ps.metallic.value(), Some(&1.0));
    assert_eq!(ps.roughness.value(), Some(&0.3));

    let binding = MaterialBindingAPI::get(&stage, "/World/Geo")?.expect("MaterialBindingAPI");
    assert_eq!(binding.direct_binding("")?.expect("binding").as_str(), "/World/Looks/M");

    // A stage traversal gated through the typed views sees the authored
    // material + its two shaders.
    assert!(Material::get(&stage, sdf::path("/World/Looks/M")?)?.is_some());
    assert_eq!(shaders(&stage)?.len(), 2);
    Ok(())
}
