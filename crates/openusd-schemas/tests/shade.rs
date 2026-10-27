//! Integration tests for the [`openusd_schemas::shade`] module: reading a
//! hand-authored UsdShade fixture, and a full author → read-back roundtrip on
//! an in-memory stage.

use std::fs;

use openusd::Result;
use openusd::{sdf, tf, usd};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::{self, FamilyType};
use openusd_schemas::shade::Connectable;
use openusd_schemas::shade::{
    self, AttributeType, Channel, Connectability, ImplementationSource, Material, MaterialBindingAPI, NodeGraph,
    Output, Shader, TerminalKind, base_name,
};

mod common;

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
    let terminal = mat.surface_source(&[])?.expect("surface terminal");
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
    assert_eq!(bound.material_path().as_str(), "/World/Looks/BrickMat");
    // Purpose-restricted preview binding.
    let preview = binding.direct_binding("preview")?.expect("preview binding");
    assert_eq!(preview.material_path().as_str(), "/World/Looks/BrickMat");
    assert_eq!(preview.rel().path().as_str(), "/World/Brick.material:binding:preview");

    // Resolution reports the binding that won beside the material.
    let resolved = binding
        .resolve_binding("preview", &mut shade::BindingCache::default())?
        .expect("resolved");
    assert_eq!(resolved.rel().name(), "material:binding:preview");
    assert_eq!(
        resolved.material()?.expect("a Material").path().as_str(),
        "/World/Looks/BrickMat"
    );
    Ok(())
}

/// The material-bind subsets a vendor asset authors are listed with the
/// partition their mesh declares, each bound to a material of its own.
#[test]
fn vendor_material_bind_subsets() -> Result<()> {
    let stage =
        common::vendor("usd-wg-assets/full_assets/Vehicles/USD_Mini_Car_Kit/assets/vehicles/sedan/geo/sedanGeo.usda")?;
    let binding = MaterialBindingAPI::from_prim_unchecked(stage.prim("/sedan")?);
    assert_eq!(binding.subsets()?.len(), 5);
    assert_eq!(binding.subset_family_type()?, FamilyType::Partition);
    let first = MaterialBindingAPI::get(&stage, "/sedan/_4_frontLightMax")?.expect("applied");
    let direct = first.direct_binding("")?.expect("bound");
    assert_eq!(direct.material_path().as_str(), "/Materials/frontLightMax");
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
    tex.node_def()
        .create_id_attr()?
        .set(sdf::Value::token("UsdUVTexture"))?;
    tex.create_input("file", "asset")?
        .set(sdf::Value::AssetPath("./wood.png".into()))?;
    tex.create_output("rgb", "float3")?;

    let surface = Shader::define(&stage, "/World/Looks/M/Surface")?;
    surface
        .node_def()
        .create_id_attr()?
        .set(sdf::Value::token("UsdPreviewSurface"))?;
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
    assert_eq!(
        binding.direct_binding("")?.expect("binding").material_path().as_str(),
        "/World/Looks/M"
    );

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
    assert_eq!(shader.node_def().implementation()?, ImplementationSource::SourceAsset);
    assert_eq!(shader.node_def().source_types()?, vec![tf::Token::from("osl")]);

    let asset = shader.node_def().source_asset("osl")?.expect("OSL source asset");
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
    shader.node_def().set_source_asset("./shader.mdl", "mdl")?;
    shader.node_def().set_source_asset_subidentifier("Main", "mdl")?;
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
    assert_eq!(shader.node_def().implementation()?, ImplementationSource::SourceAsset);
    assert_eq!(shader.node_def().source_types()?, vec![tf::Token::from("mdl")]);
    assert_eq!(
        shader.node_def().source_asset("mdl")?.expect("MDL asset").authored_path,
        "./shader.mdl"
    );
    assert_eq!(
        shader.node_def().source_asset_subidentifier("mdl")?.as_deref(),
        Some("Main")
    );
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
    shader
        .node_def()
        .create_id_attr()?
        .set(sdf::Value::token("UsdPreviewSurface"))?;
    shader
        .create_input("diffuseColor", "color3f")?
        .set(sdf::Value::vec3f(0.8_f32, 0.2, 0.2))?;
    shader.create_output("surface", "token")?;

    let shader = Shader::get(&stage, "/Mat/Surface")?.expect("Shader");
    assert_eq!(shader.node_def().shader_id()?.as_deref(), Some("UsdPreviewSurface"));
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
    shader.node_def().set_source_asset("./OmniPBR.mdl", "")?;
    shader.node_def().set_source_asset_subidentifier("OmniPBR", "")?;

    let shader = Shader::get(&stage, "/Mat/MdlShader")?.expect("Shader");
    assert_eq!(
        shader
            .node_def()
            .implementation_source_attr()
            .get::<ImplementationSource>()?,
        Some(ImplementationSource::SourceAsset)
    );
    Ok(())
}

#[test]
fn material_surface_terminal() -> Result<(), SchemaError> {
    let stage = memory()?;
    Shader::define(&stage, "/Mat/Surface")?
        .node_def()
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
    let terminal = mat.surface_source(&[])?.expect("surface terminal");
    assert_eq!(terminal.kind(), TerminalKind::Surface);
    assert!(terminal.render_context().is_empty());
    assert_eq!(terminal.sources().len(), 1);
    let source = terminal.sources().first().expect("surface source");
    assert_eq!(source.shader().expect("shader source").path().as_str(), "/Mat/Surface");
    assert_eq!(source.name(), "surface");
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
    let terminal = mat.surface_source(&[])?.expect("surface terminal");
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
    // The schema declares the universal terminals. Each is listed before
    // anything is authored.
    assert_eq!(material.surface_outputs()?.len(), 1);
    assert_eq!(material.surface_outputs()?[0].base_name(), "surface");

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
    // Each lists the declared universal terminal and the one `ri` terminal.
    assert_eq!(material.displacement_outputs()?.len(), 2);
    assert_eq!(material.volume_outputs()?.len(), 2);
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
fn connect_connectability_render_type() -> Result<(), SchemaError> {
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

/// `testUsdShadeHasConnectableAPI.cpp`: the shading types are connectable and
/// a Sphere is not, by type and by prim.
#[test]
fn has_connectable_api() -> Result<()> {
    let schemas = openusd_schemas::schema_registry();
    for schema in ["Shader", "Material", "NodeGraph"] {
        assert!(
            shade::ConnectableAPI::has_connectable_api(&schemas, &tf::Token::from(schema)),
            "{schema}"
        );
    }
    assert!(!shade::ConnectableAPI::has_connectable_api(
        &schemas,
        &tf::Token::from("Sphere")
    ));

    let stage = memory()?;
    Material::define(&stage, "/Mat")?;
    Shader::define(&stage, "/Mat/Shader")?;
    let material = shade::ConnectableAPI::from_prim(stage.prim("/Mat")?)?.expect("a Material is connectable");
    assert!(material.is_container()? && material.requires_encapsulation()?);
    let shader = shade::ConnectableAPI::from_prim(stage.prim("/Mat/Shader")?)?.expect("a Shader is connectable");
    assert!(!shader.is_container()? && shader.requires_encapsulation()?);
    let sphere = stage.define_prim("/Sphere")?.set_type_name("Sphere")?;
    assert!(shade::ConnectableAPI::from_prim(sphere)?.is_none());
    Ok(())
}

/// `testUsdShadeConnectability.py:test_Basic`: every `CanConnect` it asks.
#[test]
fn connectability_basic() -> Result<(), SchemaError> {
    let stage = memory()?;
    let full = Connectability::Full;
    let interface_only = Connectability::InterfaceOnly;
    let material = Material::define(&stage, "/Material")?;
    let node_graph = NodeGraph::define(&stage, "/Material/NodeGraph")?;
    let shader = Shader::define(&stage, "/Material/Shader")?;
    let nested_shader = Shader::define(&stage, "/Material/NodeGraph/NestedShader")?;
    let nested_shader2 = Shader::define(&stage, "/Material/NodeGraph2/NestedShader")?;

    let float_interface = material.create_input("floatInput", "float")?;
    let float_mat_out = material.create_output("fOut", "float")?;
    // A Material, a derived container, passes nothing through.
    assert!(!float_mat_out.can_connect(float_interface.attribute())?);
    // A Material input does not connect to an attribute on itself.
    let x = stage.prim("/Material")?.create_attribute("x", "double")?;
    assert!(!float_interface.can_connect(&x)?);

    let color_interface = material
        .create_input("colorInput", "color3f")?
        .set_connectability(interface_only)?;
    let color_mat_out = material.create_output("colorOutput", "color3f")?;

    // Shader inputs are full, and connect to their container's inputs.
    let shader_float = shader.create_input("shaderFloat", "float")?;
    let shader_color = shader.create_input("shaderColor", "color3f")?;
    assert!(shader_color.can_connect(color_interface.attribute())?);
    assert!(shader_float.can_connect(float_interface.attribute())?);

    let shader_out_color = shader.create_output("color", "color3f")?;
    let shader_out_float = shader.create_output("fOut", "float")?;
    let node_graph_float = node_graph.create_input("nodeGraphFlIn", "float")?;

    // Shader outputs connect to nothing.
    assert!(!shader_out_float.can_connect(float_interface.attribute())?);
    assert!(!shader_out_float.can_connect(shader_float.attribute())?);
    assert!(!shader_out_float.can_connect(node_graph_float.attribute())?);

    // A Material input connects to an output of a shader it holds.
    let float_interface = float_interface.set_connectability(full)?;
    let color_interface = color_interface.set_connectability(full)?;
    assert!(float_interface.can_connect(shader_out_float.attribute())?);
    assert!(color_interface.can_connect(shader_out_color.attribute())?);

    // An input connects to its container's input.
    assert!(node_graph_float.can_connect(float_interface.attribute())?);

    // An interfaceOnly NodeGraph input does not connect to an output; a full
    // one does.
    let node_graph_float = node_graph_float.set_connectability(interface_only)?;
    assert!(!node_graph_float.can_connect(shader_out_float.attribute())?);
    let node_graph_float = node_graph_float.set_connectability(full)?;
    assert!(node_graph_float.can_connect(shader_out_float.attribute())?);

    let node_graph_color = node_graph
        .create_input("nodeGraphColor", "color3f")?
        .set_connectability(interface_only)?;
    assert!(!node_graph_color.can_connect(shader_out_color.attribute())?);
    assert!(!node_graph_color.can_connect(color_mat_out.attribute())?);
    // Nor to a full input, nor, by encapsulation, to an interfaceOnly one on
    // a shader.
    assert!(!node_graph_color.can_connect(shader_color.attribute())?);
    let shader_color = shader_color.set_connectability(interface_only)?;
    assert!(!node_graph_color.can_connect(shader_color.attribute())?);

    // A nested shader input does not reach an interface beyond its nearest
    // container, whatever the interface's connectability.
    let float_interface = float_interface.set_connectability(full)?;
    let nested_float = nested_shader
        .create_input("nestedShaderFloat", "float")?
        .set_connectability(interface_only)?;
    assert!(!nested_float.can_connect(float_interface.attribute())?);
    let float_interface = float_interface.set_connectability(interface_only)?;
    assert!(!nested_float.can_connect(float_interface.attribute())?);

    // A NodeGraph input does not connect to its own child's output, full or
    // interfaceOnly.
    let nested_out = nested_shader.create_output("fOut", "float")?;
    let node_graph_float = node_graph_float.set_connectability(full)?;
    assert!(!node_graph_float.can_connect(nested_out.attribute())?);
    let node_graph_float = node_graph_float.set_connectability(interface_only)?;
    assert!(!node_graph_float.can_connect(nested_out.attribute())?);

    // A shader input does not reach into another NodeGraph.
    let nested2_float = nested_shader2.create_input("nestedShaderFloat", "float")?;
    assert!(!nested2_float.can_connect(node_graph_float.attribute())?);
    Ok(())
}

/// A shader at `/Mat/Consumer` with a `float` input `in`, and shaders at
/// `/Mat/A`, `/Mat/B` and `/Mat/C` that author nothing.
fn consumer() -> Result<(usd::Stage, shade::Input)> {
    let stage = memory()?;
    let consumer = Shader::define(&stage, "/Mat/Consumer")?;
    for path in ["/Mat/A", "/Mat/B", "/Mat/C"] {
        Shader::define(&stage, path)?;
    }
    let input = consumer.create_input("in", "float")?;
    Ok((stage, input))
}

/// The shader at `path`.
fn shader(stage: &usd::Stage, path: &str) -> Result<Shader> {
    Ok(Shader::get(stage, path)?.expect("Shader"))
}

/// One explicit list of mixed inputs and outputs, which the sources read back
/// connect again (C++ `testUsdShadeConnectability.py`'s `test_Basic`).
#[test]
fn set_connected_sources() -> Result<(), SchemaError> {
    let (stage, input) = consumer()?;
    let sources: [shade::ShadingAttribute; 2] = [
        shader(&stage, "/Mat/A")?.output("out").into(),
        shader(&stage, "/Mat/B")?.input("value").into(),
    ];
    let input = input.set_connected_sources(sources)?;
    let authored = [sdf::path("/Mat/A.outputs:out")?, sdf::path("/Mat/B.inputs:value")?];
    assert_eq!(input.connections()?, authored);

    let read_back: Vec<_> = input
        .connected_sources()?
        .into_sources()
        .into_iter()
        .map(|source| source.attribute())
        .collect();
    let input = input.set_connected_sources(read_back)?;
    assert_eq!(input.connections()?, authored);
    Ok(())
}

/// Appending and prepending edit the explicit list in place.
#[test]
fn append_prepend_order() -> Result<(), SchemaError> {
    let (stage, input) = consumer()?;
    let input = input
        .connect_to(&shader(&stage, "/Mat/A")?.output("out"))?
        .connect_to_with(
            &shader(&stage, "/Mat/B")?.output("out"),
            shade::ConnectionModification::Append,
        )?
        .connect_to_with(
            &shader(&stage, "/Mat/C")?.output("out"),
            shade::ConnectionModification::Prepend,
        )?;
    assert_eq!(
        input.connections()?,
        [
            sdf::path("/Mat/C.outputs:out")?,
            sdf::path("/Mat/A.outputs:out")?,
            sdf::path("/Mat/B.outputs:out")?,
        ]
    );
    Ok(())
}

/// One source is disconnected, then every source, then the opinion cleared.
#[test]
fn disconnect_one_source() -> Result<(), SchemaError> {
    let (stage, input) = consumer()?;
    let a = shader(&stage, "/Mat/A")?.output("out");
    let b = shader(&stage, "/Mat/B")?.output("out");
    let input = input
        .connect_to(&a)?
        .connect_to_with(&b, shade::ConnectionModification::Append)?;
    assert!(input.disconnect_source(&a)?);
    assert_eq!(input.connections()?, [sdf::path("/Mat/B.outputs:out")?]);
    let input = input.disconnect()?;
    assert!(input.connections()?.is_empty());
    let input = input.clear_sources()?;
    assert!(input.connections()?.is_empty());
    Ok(())
}

/// Over a weaker layer's connection, a disconnect blocks it and a clear lets
/// it compose again (C++ `testUsdShadeShaders.py`).
#[test]
fn clear_vs_disconnect() -> Result<(), SchemaError> {
    let (_dir, stage) = common::open_files(
        &[
            (
                "weak.usda",
                "#usda 1.0\ndef Shader \"Source\" {\n    float outputs:out\n}\n\
                 def Shader \"Consumer\" {\n    float inputs:in.connect = </Source.outputs:out>\n}\n",
            ),
            ("root.usda", "#usda 1.0\n(\n    subLayers = [@./weak.usda@]\n)\n"),
        ],
        "root.usda",
    )?;
    let input = shader(&stage, "/Consumer")?.input("in");
    assert_eq!(input.connections()?, [sdf::path("/Source.outputs:out")?]);
    let input = input.disconnect()?;
    assert!(input.connections()?.is_empty());
    let input = input.clear_sources()?;
    assert_eq!(input.connections()?, [sdf::path("/Source.outputs:out")?]);
    Ok(())
}

/// An output nothing defines is authored with the consumer's type (C++
/// `testUsdShadeShaders.py`).
#[test]
fn source_created_typed() -> Result<(), SchemaError> {
    let stage = memory()?;
    let consumer = Shader::define(&stage, "/Mat/Consumer")?;
    let source = Shader::define(&stage, "/Mat/Source")?.output("colorOut");
    assert!(!source.attribute().is_defined()?);
    consumer.create_input("color", "color3f")?.connect_to(&source)?;
    assert!(source.attribute().is_defined()?);
    assert_eq!(source.attribute().type_name()?, Some(sdf::ValueTypeName::COLOR3F));
    assert!(!source.attribute().is_custom()?);
    Ok(())
}

/// An input-typed source is authored as an input.
#[test]
fn input_source_created() -> Result<(), SchemaError> {
    let (stage, input) = consumer()?;
    let source = shader(&stage, "/Mat/A")?.input("floatInput");
    input.connect_to(&source)?;
    let created = stage.attribute("/Mat/A.inputs:floatInput")?;
    assert!(created.is_defined()?);
    assert_eq!(created.type_name()?, Some(sdf::ValueTypeName::FLOAT));
    Ok(())
}

/// A source to author where nothing declares a type is refused.
#[test]
fn untyped_source_refused() -> Result<(), SchemaError> {
    let (stage, _) = consumer()?;
    let untyped = shader(&stage, "/Mat/Consumer")?.input("untyped");
    let error = untyped
        .connect_to(&shader(&stage, "/Mat/A")?.output("out"))
        .err()
        .expect("no type to author the source with");
    assert!(
        matches!(error, SchemaError::UntypedConnectionSource { .. }),
        "{error:?}"
    );
    Ok(())
}

/// The bases and variations of C++ `testUsdShadeMaterialAuthoring.py`.
const BASES: [&str; 3] = ["Hair", "Skin", "Nails"];
const VARIATIONS: [&str; 2] = ["Wet", "Dry"];

/// A stage holding `/ModelShading` as its default prim, in centimeters with Y
/// up.
fn shading_stage() -> Result<(usd::Stage, usd::Prim), SchemaError> {
    let stage = memory()?;
    geom::set_stage_up_axis(&stage, geom::UpAxis::Y)?;
    stage.set_stage_metadata("metersPerUnit", geom::linear_units::CENTIMETERS)?;
    let root = stage.define_prim("/ModelShading")?;
    stage.set_default_prim("ModelShading")?;
    Ok((stage, root))
}

/// An internal reference to the prim at `path`.
fn reference(path: &str) -> Result<sdf::Reference> {
    Ok(sdf::Reference {
        prim_path: sdf::path(path)?,
        ..Default::default()
    })
}

/// `/ShadingDefs`, an `over` holding a surface and a displacement shader per
/// base and variation, and per base a material that references them and
/// connects its terminals to them inside each variation. Answers the
/// materials.
fn shading_defs(stage: &usd::Stage) -> Result<Vec<usd::Prim>, SchemaError> {
    geom::Scope::define(stage, "/ShadingDefs/Shaders")?;
    geom::Scope::define(stage, "/ShadingDefs/Materials")?;
    let mut materials = Vec::new();
    for base in BASES {
        let path = format!("/ShadingDefs/Materials/{base}Material");
        let material = Material::define(stage, path.as_str())?;
        material.references().add(reference("/ShadingDefs/Shaders")?)?;
        for variation in VARIATIONS {
            let surface = format!("{base}{variation}Surface");
            let displacement = format!("{base}{variation}Displacement");
            Shader::define(stage, format!("/ShadingDefs/Shaders/{surface}").as_str())?
                .create_output("surface", "token")?;
            Shader::define(stage, format!("/ShadingDefs/Shaders/{displacement}").as_str())?
                .create_output("displacement", "token")?;

            let _context = stage.edit_context(material.variant_edit_target(variation, None)?)?;
            let surface = shader(stage, &format!("{path}/{surface}"))?.output("surface");
            let displacement = shader(stage, &format!("{path}/{displacement}"))?.output("displacement");
            material.create_surface_output()?.connect_to(&surface)?;
            material.create_displacement_output()?.connect_to(&displacement)?;
        }
        materials.push(material.into());
    }
    stage.prim("/ShadingDefs")?.set_specifier(sdf::Specifier::Over)?;
    Ok(materials)
}

/// The hair material's terminals connect to the wet or dry shaders that
/// `root`'s `materialVariant` selection names.
fn validate_material_switch(stage: &usd::Stage, root: &usd::Prim) -> Result<(), SchemaError> {
    let hair = "/ModelShading/Materials/HairMaterial";
    let material = Material::get(stage, hair)?.expect("HairMaterial");
    let source = |output: Output| -> Result<sdf::Path, SchemaError> {
        let sources = output.connected_sources()?.into_sources();
        Ok(sources.first().expect("a connected source").path().clone())
    };
    for variation in ["Wet", "Dry"] {
        root.variant_sets().set_selection("materialVariant", variation)?;
        assert_eq!(
            source(material.surface_output())?,
            sdf::path(format!("{hair}/Hair{variation}Surface.outputs:surface"))?
        );
        assert_eq!(
            source(material.displacement_output())?,
            sdf::path(format!("{hair}/Hair{variation}Displacement.outputs:displacement"))?
        );
    }
    Ok(())
}

/// `layer` written as text is the C++ baseline at `baseline`, byte for byte.
fn assert_baseline(layer: &sdf::Layer, baseline: &str) -> Result<()> {
    // A checkout that turns line ends into CRLF still holds the same text.
    let expected = fs::read_to_string(baseline).expect("baseline").replace("\r\n", "\n");
    assert_eq!(layer.export_to_string().map_err(openusd::Error::from)?, expected);
    Ok(())
}

/// A master variant on a separate `over`, referenced into the root beside the
/// shading, authors C++'s layer and switches the materials (C++
/// `testUsdShadeMaterialAuthoring.py`).
#[test]
fn master_variant_tree() -> Result<(), SchemaError> {
    let (stage, root) = shading_stage()?;
    let materials = shading_defs(&stage)?;
    let master = stage.override_prim("/MaterialBindingVariants")?;
    Material::create_master_variant(&master, &materials, None)?;
    for target in ["/MaterialBindingVariants", "/ShadingDefs"] {
        root.references().add(reference(target)?)?;
    }
    assert_baseline(&stage.root_layer(), "fixtures/usdShade_char_shading.usda")?;
    validate_material_switch(&stage, &root)
}

/// A master variant on the root, switching the materials it composes through
/// its reference to the shading.
#[test]
fn master_variant_compact() -> Result<(), SchemaError> {
    let (stage, root) = shading_stage()?;
    shading_defs(&stage)?;
    root.references().add(reference("/ShadingDefs")?)?;
    let materials = BASES
        .iter()
        .map(|base| stage.prim(format!("/ModelShading/Materials/{base}Material")))
        .collect::<Result<Vec<_>, _>>()?;
    Material::create_master_variant(&root, &materials, None)?;
    assert_baseline(&stage.root_layer(), "fixtures/usdShade_char_shading_compact.usda")?;
    validate_material_switch(&stage, &root)
}

/// Each check on the master and its materials fails with its own error.
#[test]
fn master_variant_errors() -> Result<(), SchemaError> {
    let stage = memory()?;
    let master = stage.define_prim("/Master")?;
    let wet = Material::define(&stage, "/Wet")?;
    wet.variant_edit_target("Wet", None)?;
    let both = Material::define(&stage, "/Both")?;
    for variation in VARIATIONS {
        both.variant_edit_target(variation, None)?;
    }
    let plain: usd::Prim = Material::define(&stage, "/Plain")?.into();
    let other = memory()?;
    let foreign: usd::Prim = Material::define(&other, "/Wet")?.into();
    let wet: usd::Prim = wet.into();
    let both: usd::Prim = both.into();

    let error = |master: &usd::Prim, materials: &[usd::Prim]| {
        Material::create_master_variant(master, materials, None).expect_err("a refused master variant")
    };
    assert!(matches!(error(&master, &[]), SchemaError::NoMaterials { .. }));
    assert!(matches!(
        error(&master, &[wet.clone(), foreign]),
        SchemaError::ForeignStage { .. }
    ));
    assert!(matches!(
        error(&master, &[plain]),
        SchemaError::NoMaterialVariants { .. }
    ));
    assert!(matches!(
        error(&master, &[wet.clone(), both]),
        SchemaError::MismatchedMaterialVariants { .. }
    ));
    assert!(matches!(
        error(&stage.prim("/Missing")?, &[wet]),
        SchemaError::Core(openusd::Error::Authoring(usd::StageAuthoringError::PrimNotValid { .. }))
    ));
    assert!(!master.variant_sets().contains("materialVariant")?);
    Ok(())
}

/// A material under the master whose variants were authored locally keeps its
/// own selection over the master's, as in C++, and follows the master once
/// that selection is cleared.
#[test]
fn master_variant_local_material() -> Result<(), SchemaError> {
    let stage = memory()?;
    let root = stage.define_prim("/Root")?;
    let material = Material::define(&stage, "/Root/Mat")?;
    for variation in VARIATIONS {
        material.variant_edit_target(variation, None)?;
    }
    Material::create_master_variant(&root, &[material.clone().into()], None)?;
    let selected = |master: &str| -> Result<Option<String>, SchemaError> {
        root.variant_sets().set_selection("materialVariant", master)?;
        Ok(material.material_variant().selection()?)
    };
    assert_eq!(selected("Wet")?.as_deref(), Some("Dry"));

    material.material_variant().clear_selection()?;
    assert_eq!(selected("Wet")?.as_deref(), Some("Wet"));
    assert_eq!(selected("Dry")?.as_deref(), Some("Dry"));
    Ok(())
}

/// A connection authored inside a material variant creates its missing
/// source there.
#[test]
fn source_created_in_variant() -> Result<(), SchemaError> {
    let stage = memory()?;
    let material = Material::define(&stage, "/Mat")?;
    let source = Shader::define(&stage, "/Mat/Source")?.output("out");
    {
        let _context = stage.edit_context(material.variant_edit_target("Wet", None)?)?;
        material.create_surface_output()?.connect_to(&source)?;
    }
    let layer = stage.root_layer();
    let in_variant = sdf::path("/Mat{materialVariant=Wet}Source.outputs:out")?;
    assert!(layer.attribute(&in_variant)?.is_some());
    assert!(layer.attribute("/Mat/Source.outputs:out")?.is_none());
    drop(layer);
    assert_eq!(
        material.surface_output().connections()?,
        [sdf::path("/Mat/Source.outputs:out")?]
    );
    Ok(())
}
