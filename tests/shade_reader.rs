//! Integration tests for the [`openusd::schemas::shade`] module: reading a
//! hand-authored UsdShade fixture, and a full author → read-back roundtrip on
//! an in-memory stage.

use std::fs;

use openusd::Result;
use openusd::schemas::SchemaError;
use openusd::schemas::shade::{self, Channel, Connectable, ImplementationSource, Material, MaterialBindingAPI, Shader};
use openusd::{sdf, tf, usd};

const FIXTURE: &str = "fixtures/usdShade_scene.usda";

fn open() -> Result<usd::Stage> {
    usd::Stage::open(FIXTURE)
}

/// Every `Material` on the stage, found by traversing and gating each prim
/// through `Material::get` — the C++-style `prim.IsA<UsdShadeMaterial>()` filter.
fn materials(stage: &usd::Stage) -> Result<Vec<Material>> {
    typed(stage, Material::get)
}

/// Every `Shader` on the stage (`prim.IsA<UsdShadeShader>()`).
fn shaders(stage: &usd::Stage) -> Result<Vec<Shader>> {
    typed(stage, Shader::get)
}

/// Traverse `stage` and collect the prims that `get` resolves to a view.
fn typed<S>(stage: &usd::Stage, get: impl Fn(&usd::Stage, sdf::Path) -> Result<Option<S>>) -> Result<Vec<S>> {
    let mut paths = Vec::new();
    stage.traverse(usd::PrimPredicate::DEFAULT_PROXIES, |p| paths.push(p.clone()))?;
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
fn resolves_surface_terminal_to_shader() -> Result<(), SchemaError> {
    let stage = open()?;
    let mat = Material::get(&stage, "/World/Looks/BrickMat")?.expect("Material");
    let terminal = mat.compute_surface_source(&[])?.expect("surface terminal");
    let source = terminal.sources().first().expect("surface source");
    assert_eq!(
        source.shader().expect("shader source").path().as_str(),
        "/World/Looks/BrickMat/Surface"
    );
    Ok(())
}

#[test]
fn reads_preview_surface_channels_from_fixture() -> Result<(), SchemaError> {
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
fn author_then_read_back_roundtrip() -> Result<(), SchemaError> {
    let stage = usd::Stage::builder().in_memory("anon.usda")?;
    stage.define_prim("/World")?.set_type_name("Xform")?;
    stage.define_prim("/World/Looks")?.set_type_name("Scope")?;
    stage.define_prim("/World/Geo")?.set_type_name("Mesh")?;

    // Texture → diffuseColor; scalar metallic/roughness.
    let tex = Shader::define(&stage, "/World/Looks/M/Albedo")?;
    tex.create_id_attr()?.set(sdf::Value::token("UsdUVTexture"))?;
    tex.create_input("file", "asset")?
        .set(sdf::Value::AssetPath("./wood.png".into()))?;
    tex.create_output("rgb", "float3")?;

    let surface = Shader::define(&stage, "/World/Looks/M/Surface")?;
    surface.create_id_attr()?.set(sdf::Value::token("UsdPreviewSurface"))?;
    surface
        .create_input("diffuseColor", "color3f")?
        .set_connections(["/World/Looks/M/Albedo.outputs:rgb"])?;
    surface.create_input("metallic", "float")?.set(sdf::Value::Float(1.0))?;
    surface
        .create_input("roughness", "float")?
        .set(sdf::Value::Float(0.3))?;
    surface.create_output("surface", "token")?;

    Material::define(&stage, "/World/Looks/M")?
        .create_surface_output()?
        .set_connections(["/World/Looks/M/Surface.outputs:surface"])?;

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

#[test]
fn reads_node_def_source() -> Result<()> {
    let directory = tempfile::tempdir()?;
    let source_path = directory.path().join("shader.osl");
    fs::write(&source_path, "shader Example() {}")?;
    let scene_path = directory.path().join("scene.usda");
    fs::write(
        &scene_path,
        r#"#usda 1.0
def Shader "Source"
{
    uniform token info:implementationSource = "sourceAsset"
    uniform asset info:osl:sourceAsset = @./shader.osl@
}
"#,
    )?;

    let scene = scene_path.to_string_lossy();
    let stage = usd::Stage::open(scene.as_ref())?;
    let shader = Shader::get(&stage, "/Source")?.expect("Shader");
    assert_eq!(shader.implementation_source()?, ImplementationSource::SourceAsset);
    assert_eq!(shader.source_types()?, vec![tf::Token::from("osl")]);

    let asset = shader.source_asset("osl")?.expect("OSL source asset");
    assert_eq!(asset.authored_path, "./shader.osl");
    let resolved = source_path.canonicalize()?;
    assert_eq!(asset.resolved_path(), Some(resolved.to_string_lossy().as_ref()));
    Ok(())
}

#[test]
fn authors_node_def_source() -> Result<()> {
    let directory = tempfile::tempdir()?;
    let scene_path = directory.path().join("scene.usda");
    let scene = scene_path.to_string_lossy().into_owned();

    let stage = usd::Stage::builder().in_memory("anon.usda")?;
    let shader = Shader::define(&stage, "/Source")?;
    shader.set_source_asset("./shader.mdl", "mdl")?;
    shader.set_source_asset_subidentifier("Main", "mdl")?;
    shader.set_sdr_metadata_by_key("role", "surface")?;
    shader
        .create_input("gain", "float")?
        .set_sdr_metadata_by_key("widget", "slider")?;
    stage.root_layer().export(&scene)?;

    // Everything the setters chose survives a round trip through the text
    // format, the implementation source they selected included.
    let stage = usd::Stage::open(&scene)?;
    let shader = Shader::get(&stage, "/Source")?.expect("Shader");
    assert_eq!(shader.implementation_source()?, ImplementationSource::SourceAsset);
    assert_eq!(shader.source_types()?, vec![tf::Token::from("mdl")]);
    assert_eq!(
        shader.source_asset("mdl")?.expect("MDL asset").authored_path,
        "./shader.mdl"
    );
    assert_eq!(shader.source_asset_subidentifier("mdl")?.as_deref(), Some("Main"));
    assert_eq!(shader.sdr_metadata_by_key("role")?.as_deref(), Some("surface"));

    let gain = shader.inputs()?.pop().expect("gain input");
    assert_eq!(gain.base_name(), "gain");
    assert_eq!(gain.sdr_metadata_by_key("widget")?.as_deref(), Some("slider"));
    Ok(())
}
