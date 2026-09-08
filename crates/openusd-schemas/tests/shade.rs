//! Integration tests for the [`openusd_schemas::shade`] module: reading a
//! hand-authored UsdShade fixture, and a full author → read-back roundtrip on
//! an in-memory stage.

use std::fs;

use openusd::Result;
use openusd::{sdf, tf, usd};
use openusd_schemas::SchemaError;
use openusd_schemas::shade::Connectable;
use openusd_schemas::shade::{
    self, AttributeType, Channel, Connectability, ImplementationSource, Material, MaterialBindingAPI, NodeGraph,
    Output, Shader, TerminalKind, base_name,
};

const FIXTURE: &str = "fixtures/usdShade_scene.usda";

fn open() -> Result<usd::Stage> {
    usd::Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)
}

/// An in-memory stage carrying the schema data, which is what makes a prim its
/// type and resolves the fallbacks its schema declares.
fn memory() -> Result<usd::Stage> {
    usd::Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")
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
    let stage = usd::Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")?;
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

    MaterialBindingAPI::apply(&stage.prim(sdf::path("/World/Geo")?)?)?.bind(sdf::path("/World/Looks/M")?)?;

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
    let stage = usd::Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(scene.as_ref())?;
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

    let stage = usd::Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")?;
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
    let stage = usd::Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(&scene)?;
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

#[test]
fn shader_id_and_inputs() -> Result<()> {
    let stage = memory()?;
    let shader = Shader::define(&stage, "/Mat/Surface")?;
    shader.create_id_attr()?.set(sdf::Value::token("UsdPreviewSurface"))?;
    shader
        .create_input("diffuseColor", "color3f")?
        .set(sdf::Value::vec3f(0.8_f32, 0.2, 0.2))?;
    shader.create_output("surface", "token")?;

    let shader = Shader::get(&stage, "/Mat/Surface")?.expect("Shader");
    assert_eq!(shader.id()?.as_deref(), Some("UsdPreviewSurface"));
    assert_eq!(
        shader.input("diffuseColor").get::<sdf::Value>()?,
        Some(sdf::Value::vec3f(0.8_f32, 0.2, 0.2))
    );
    assert!(shader.inputs()?.iter().any(|input| input.base_name() == "diffuseColor"));
    assert!(stage.attribute("/Mat/Surface.outputs:surface")?.is_defined()?);
    Ok(())
}

#[test]
fn lists_skip_relationships() -> Result<()> {
    let stage = memory()?;
    let shader = Shader::define(&stage, "/Mat/Surface")?;
    shader.create_input("roughness", "float")?;
    shader.create_output("surface", "token")?;
    shader.create_relationship("inputs:binding")?;
    shader.create_relationship("outputs:binding")?;

    let inputs = shader.inputs()?;
    assert_eq!(inputs.len(), 1);
    assert_eq!(inputs[0].base_name(), "roughness");

    let outputs = shader.outputs()?;
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].base_name(), "surface");
    Ok(())
}

#[test]
fn shader_source_asset() -> Result<()> {
    let stage = memory()?;
    let shader = Shader::define(&stage, "/Mat/MdlShader")?;
    shader
        .create_implementation_source_attr()?
        .set(ImplementationSource::SourceAsset)?;
    shader
        .create_source_asset_attr()?
        .set(sdf::Value::AssetPath("./OmniPBR.mdl".into()))?;
    shader
        .create_source_asset_subidentifier_attr()?
        .set(sdf::Value::token("OmniPBR"))?;

    let shader = Shader::get(&stage, "/Mat/MdlShader")?.expect("Shader");
    assert_eq!(
        shader.implementation_source_attr().get::<ImplementationSource>()?,
        Some(ImplementationSource::SourceAsset)
    );
    Ok(())
}

#[test]
fn material_surface_terminal() -> Result<(), SchemaError> {
    let stage = memory()?;
    Shader::define(&stage, "/Mat/Surface")?
        .create_id_attr()?
        .set(sdf::Value::token("UsdPreviewSurface"))?;
    Shader::get(&stage, "/Mat/Surface")?
        .expect("Shader")
        .create_output("surface", "token")?;
    let shader_out = sdf::path("/Mat/Surface.outputs:surface")?;
    let mat = Material::define(&stage, "/Mat")?;
    mat.create_surface_output()?.set_connections([shader_out.clone()])?;

    let mat = Material::get(&stage, "/Mat")?.expect("Material");
    assert_eq!(mat.surface_output().connections()?, vec![shader_out]);
    let terminal = mat.compute_surface_source(&[])?.expect("surface terminal");
    assert_eq!(terminal.kind(), TerminalKind::Surface);
    assert!(terminal.render_context().is_empty());
    assert_eq!(terminal.sources().len(), 1);
    let source = terminal.sources().first().expect("surface source");
    assert_eq!(source.shader().expect("shader source").path().as_str(), "/Mat/Surface");
    assert_eq!(source.source_name(), "surface");
    assert_eq!(source.source_type(), AttributeType::Output);
    Ok(())
}

#[test]
fn surface_through_node_graph() -> Result<(), SchemaError> {
    let stage = memory()?;
    let shader = Shader::define(&stage, "/Mat/NG/Surface")?;
    let shader_output = shader.create_output("surface", "token")?;
    let graph = NodeGraph::define(&stage, "/Mat/NG")?;
    graph.create_output("surface", "token")?.connect_to(&shader_output)?;
    Material::define(&stage, "/Mat")?
        .create_surface_output()?
        .connect_to(&graph.output("surface"))?;

    // The terminal names the node graph, but the shader inside it is what
    // drives the surface.
    let mat = Material::get(&stage, "/Mat")?.expect("Material");
    let terminal = mat.compute_surface_source(&[])?.expect("surface terminal");
    let source = terminal.sources().first().expect("surface source");
    assert_eq!(
        source.shader().expect("shader source").path().as_str(),
        "/Mat/NG/Surface"
    );
    Ok(())
}

#[test]
fn material_render_context_terminal() -> Result<()> {
    let stage = memory()?;
    let src = sdf::path("/Mat/RiSurface.outputs:surface")?;
    Material::define(&stage, "/Mat")?
        .create_surface_output_for("ri")?
        .set_connections([src])?;
    assert!(stage.attribute("/Mat.outputs:ri:surface")?.is_defined()?);
    Ok(())
}

#[test]
fn terminal_output_enumeration() -> Result<(), SchemaError> {
    let stage = memory()?;
    let material = Material::define(&stage, "/Mat")?;
    material.create_surface_output_for("ri")?;
    material.create_output("surface:preview", "token")?;
    material.create_surface_output_for("mtlx:standard")?;
    material.create_surface_output()?;
    material.create_displacement_output_for("ri")?;
    material.create_volume_output_for("ri")?;

    let surface_outputs = material.surface_outputs()?;
    let names: Vec<&str> = surface_outputs.iter().map(Output::base_name).collect();
    assert_eq!(names[0], "surface");
    assert_eq!(names.len(), 3);
    assert!(names.contains(&"ri:surface"));
    assert!(names.contains(&"mtlx:standard:surface"));
    assert_eq!(material.displacement_outputs()?.len(), 1);
    assert_eq!(material.volume_outputs()?.len(), 1);
    assert_eq!(material.surface_output_for("ri")?.full_name(), "outputs:ri:surface");
    assert_eq!(
        material.displacement_output_for("ri")?.full_name(),
        "outputs:ri:displacement"
    );
    assert_eq!(material.volume_output_for("ri")?.full_name(), "outputs:ri:volume");
    Ok(())
}

#[test]
fn node_graph_interface() -> Result<()> {
    let stage = memory()?;
    let ng = NodeGraph::define(&stage, "/NG")?;
    ng.create_input("gain", "float")?.set(sdf::Value::Float(2.0))?;
    ng.create_output("out", "color3f")?;
    let ng = NodeGraph::get(&stage, "/NG")?.expect("NodeGraph");
    assert_eq!(ng.input("gain").get::<f32>()?, Some(2.0));
    assert!(ng.outputs()?.iter().any(|output| output.base_name() == "out"));
    Ok(())
}

#[test]
fn connect_connectability_render_type() -> Result<()> {
    let stage = memory()?;
    let tex = NodeGraph::define(&stage, "/Mat/Tex")?;
    tex.create_output("rgb", "float3")?;

    let surf = Shader::define(&stage, "/Mat/Surface")?;
    // The typed connection method keeps the input view for chaining.
    surf.create_input("diffuseColor", "color3f")?
        .connect_to(&tex.output("rgb"))?;
    assert_eq!(
        surf.input("diffuseColor").connections()?,
        vec![sdf::path("/Mat/Tex.outputs:rgb")?]
    );

    // Connectability defaults to Full, and round-trips once authored.
    assert_eq!(surf.input("diffuseColor").connectability()?, Connectability::Full);
    surf.input("diffuseColor")
        .set_connectability(Connectability::InterfaceOnly)?;
    assert_eq!(
        surf.input("diffuseColor").connectability()?,
        Connectability::InterfaceOnly
    );

    // Render type round-trips on both an input and an output.
    surf.input("diffuseColor").set_render_type("color")?;
    assert_eq!(surf.input("diffuseColor").render_type()?.as_deref(), Some("color"));
    tex.output("rgb").set_render_type("color")?;
    assert_eq!(tex.output("rgb").render_type()?.as_deref(), Some("color"));

    // `base_name` strips the namespace prefix.
    assert_eq!(base_name("inputs:diffuseColor"), "diffuseColor");
    assert_eq!(base_name("outputs:rgb"), "rgb");
    Ok(())
}
