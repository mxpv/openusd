//! The `.mtlx` format through a stage: the documents of `usd-wg-assets`
//! composed by reference, by payload and as a root layer, and their
//! translations pinned against the layers under `tests/expected/`.
//!
//! The goldens regenerate with `UPDATE_EXPECTED=1`. `fixtures/usd_mtlx`
//! holds documents of C++ `testUsdMtlxFileFormat` with the layers C++
//! `usdMtlx` wrote for them.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use openusd::{sdf, usd, vt};

type Result<T = ()> = std::result::Result<T, Box<dyn std::error::Error>>;

fn vendor(relative: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../vendor/usd-wg-assets")
        .join(relative)
}

fn stage(root: &Path) -> Result<usd::Stage> {
    Ok(usd::Stage::builder()
        .format(&openusd_mtlx::MTLX)
        .open(root.to_str().expect("utf-8 path"))?)
}

/// The value of `attr` on the prim at `prim`.
fn value(stage: &usd::Stage, prim: &str, attr: &str) -> Result<Option<vt::Value>> {
    Ok(stage.prim(prim)?.attribute(attr).get::<vt::Value>()?)
}

/// The asset path `attr` holds on the prim at `prim`.
fn asset(stage: &usd::Stage, prim: &str, attr: &str) -> Result<sdf::AssetPath> {
    Ok(value(stage, prim, attr)?
        .and_then(vt::Value::try_as_asset_path)
        .expect("an asset path"))
}

/// The layer the document at `path` reads as, in `usda` text.
fn exported(path: &Path) -> Result<String> {
    let registry = sdf::LayerRegistry::default().with_format(&openusd_mtlx::MTLX);
    let layer = registry
        .find_or_open(path.to_str().expect("utf-8 path"))?
        .expect("resolves");
    let text = layer.borrow().export_to_string()?;
    Ok(text)
}

/// The one connection of `attr` on the prim at `prim`.
fn source(stage: &usd::Stage, prim: &str, attr: &str) -> Result<String> {
    let connections = stage.prim(prim)?.attribute(attr).connections()?;
    assert_eq!(connections.len(), 1, "{prim}.{attr}: {connections:?}");
    Ok(connections[0].to_string())
}

/// The teapot binds two materials from two `.mtlx` files it references:
/// each composes into a `Material`, its shader and its node graph.
#[test]
fn referenced_documents() -> Result {
    let stage = stage(&vendor("test_assets/MaterialXTest/basicTextured.usda"))?;
    let brass = "/MaterialX/Materials/Tiled_Brass";
    assert_eq!(
        stage.prim(brass)?.type_name()?.as_ref().map(|t| t.as_str()),
        Some("Material")
    );
    assert_eq!(
        source(&stage, brass, "outputs:mtlx:surface")?,
        format!("{brass}/SR_brass1.outputs:surface")
    );
    assert_eq!(
        value(&stage, &format!("{brass}/SR_brass1"), "info:id")?,
        Some(vt::Value::token("ND_standard_surface_surfaceshader"))
    );
    assert_eq!(value(&stage, brass, "inputs:metalness")?, Some(vt::Value::Float(1.0)));
    assert_eq!(
        source(&stage, &format!("{brass}/SR_brass1"), "inputs:coat_color")?,
        format!("{brass}/NG_brass1.outputs:out_color")
    );
    // The node graph composes under the material, its connections mapped
    // there through the internal reference.
    let graph = format!("{brass}/NG_brass1");
    assert_eq!(
        source(&stage, &graph, "outputs:out_color")?,
        format!("{graph}/image_color.outputs:out")
    );
    let image = stage.prim(format!("{graph}/image_color"))?;
    assert_eq!(
        image.attribute("info:id").get::<vt::Value>()?,
        Some(vt::Value::token("ND_tiledimage_color3"))
    );
    let file = image.attribute("inputs:file");
    assert_eq!(file.color_space()?.as_ref().map(|t| t.as_str()), Some("srgb_texture"));
    // `fileprefix` is folded in, as MaterialX's `flattenFilenames` folds it.
    let asset = asset(&stage, &format!("{graph}/image_color"), "inputs:file")?;
    // The document's own `colorspace` is not written on an input.
    assert_eq!(
        stage
            .prim(format!("{brass}/SR_brass1"))?
            .attribute("inputs:base_color")
            .color_space()?,
        None
    );
    assert_eq!(asset.asset_path(), "./textures/./textures/brass_color.jpg");

    let plastic = "/MaterialX/Materials/USD_Plastic";
    assert!(source(&stage, plastic, "outputs:mtlx:surface")?.ends_with(".outputs:surface"));
    Ok(())
}

/// A material reached by a payload composes as through a reference, and its
/// asset paths anchor at the `.mtlx`, not at the layer naming it.
#[test]
fn payload_anchors_at_document() -> Result {
    let dir = tempfile::tempdir()?;
    let looks = dir.path().join("looks");
    fs::create_dir_all(looks.join("textures"))?;
    fs::write(looks.join("textures/albedo.png"), b"")?;
    fs::write(
        looks.join("lib.mtlx"),
        r#"<materialx version="1.39">
             <image name="albedo" type="color3"><input name="file" type="filename" value="textures/albedo.png" /></image>
             <standard_surface name="surf" type="surfaceshader"><input name="base_color" type="color3" nodename="albedo" /></standard_surface>
             <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="surf" /></surfacematerial>
           </materialx>"#,
    )?;
    let shot = dir.path().join("shots/shot.usda");
    fs::create_dir_all(shot.parent().expect("a parent"))?;
    fs::write(
        &shot,
        "#usda 1.0\ndef Material \"Look\" (payload = @../looks/lib.mtlx@</MaterialX/Materials/m>)\n{\n}\n",
    )?;
    let stage = stage(&shot)?;
    assert_eq!(
        source(&stage, "/Look", "outputs:mtlx:surface")?,
        "/Look/surf.outputs:surface"
    );
    let asset = asset(&stage, "/Look/NodeGraphs/albedo", "inputs:file")?;
    let resolved = asset.resolved_path().expect("resolves");
    assert_eq!(
        Path::new(resolved).canonicalize()?,
        looks.join("textures/albedo.png").canonicalize()?
    );
    Ok(())
}

/// A `.mtlx` opened as a stage's root layer is a stage of its materials.
#[test]
fn root_layer() -> Result {
    let stage = stage(&vendor("test_assets/MaterialXTest/usd_preview_surface_plastic.mtlx"))?;
    let material = stage.prim("/MaterialX/Materials/USD_Plastic")?;
    assert!(material.is_valid()?);
    assert_eq!(
        material.attribute("config:mtlx:version").get::<vt::Value>()?,
        Some(vt::Value::String("1.38".into()))
    );
    Ok(())
}

/// A node of `nprlib` composes with its nodedef's `info:id` and output.
#[test]
fn nprlib_nodes() -> Result {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("npr.mtlx");
    fs::write(
        &path,
        r#"<materialx version="1.39">
             <nodegraph name="g">
               <viewdirection name="v" type="vector3" nodedef="ND_viewdirection_vector3" />
               <facingratio name="f" type="float"><input name="viewdirection" type="vector3" nodename="v" /></facingratio>
               <output name="out" type="float" nodename="f" />
             </nodegraph>
             <standard_surface name="s" type="surfaceshader"><input name="base" type="float" nodegraph="g" output="out" /></standard_surface>
             <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s" /></surfacematerial>
           </materialx>"#,
    )?;
    let stage = stage(&path)?;
    let graph = "/MaterialX/Materials/m/g";
    let view = stage.prim(format!("{graph}/v"))?;
    assert_eq!(
        view.attribute("info:id").get::<vt::Value>()?,
        Some(vt::Value::token("ND_viewdirection_vector3"))
    );
    assert_eq!(
        view.attribute("outputs:out").type_name()?.as_ref().map(|t| t.as_str()),
        Some("float3")
    );
    assert_eq!(
        value(&stage, &format!("{graph}/f"), "info:id")?,
        Some(vt::Value::token("ND_facingratio_float"))
    );
    assert_eq!(
        source(&stage, &format!("{graph}/f"), "inputs:viewdirection")?,
        format!("{graph}/v.outputs:out")
    );
    Ok(())
}

/// A registry without the format reads no `.mtlx`.
#[test]
fn needs_format() {
    let path = vendor("test_assets/MaterialXTest/usd_preview_surface_plastic.mtlx");
    assert!(usd::Stage::builder().open(path.to_str().expect("utf-8 path")).is_err());
}

/// Documents of `usd-wg-assets` translate exactly as pinned under
/// `tests/expected/`, what they report included.
#[test]
fn vendor_goldens() -> Result {
    let registry = sdf::LayerRegistry::default().with_format(&openusd_mtlx::MTLX);
    let expected = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/expected");
    let update = env::var_os("UPDATE_EXPECTED").is_some();
    let mut documents = Vec::new();
    for dir in [
        "test_assets/MaterialXTest",
        "full_assets/StandardShaderBall/example_materials",
        "full_assets/OpenChessSet/assets/Rook",
    ] {
        for entry in fs::read_dir(vendor(dir))? {
            let path = entry?.path();
            if path.extension().is_some_and(|e| e == "mtlx") {
                documents.push(path);
            }
        }
    }
    documents.sort();
    assert!(documents.len() >= 6, "{documents:?}");
    let mut failures = Vec::new();
    for path in &documents {
        let layer = registry
            .find_or_open(path.to_str().expect("utf-8 path"))?
            .expect("resolves");
        let layer = layer.borrow();
        let text = layer.export_to_string()?;
        let golden = expected.join(path.with_extension("usda").file_name().expect("a name"));
        if update {
            fs::create_dir_all(&expected)?;
            fs::write(&golden, &text)?;
        } else if fs::read_to_string(&golden)? != text {
            failures.push(format!("{} differs from {}", path.display(), golden.display()));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}

/// What the translation cannot represent it reports in the layer's
/// `customLayerData`.
#[test]
fn reports_warnings() -> Result {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("w.mtlx");
    fs::write(
        &path,
        r#"<materialx version="1.39">
             <subsurface_bsdf name="b" type="BSDF"><input name="radius" type="vector3" value="1, 1, 1" /></subsurface_bsdf>
             <surface name="s" type="surfaceshader"><input name="bsdf" type="BSDF" nodename="b" /></surface>
             <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s" /></surfacematerial>
             <look name="l" />
           </materialx>"#,
    )?;
    let registry = sdf::LayerRegistry::default().with_format(&openusd_mtlx::MTLX);
    let layer = registry
        .find_or_open(path.to_str().expect("utf-8 path"))?
        .expect("resolves");
    let layer = layer.borrow();
    let data = layer
        .pseudo_root()
        .expect("a pseudo-root")
        .field(sdf::FieldKey::CustomLayerData.as_str())?
        .and_then(vt::Value::try_as_dictionary)
        .expect("customLayerData");
    let warnings = data
        .get_at("mtlx:warnings")
        .and_then(vt::Value::try_as_string_vec_ref)
        .expect("warnings");
    assert_eq!(
        warnings,
        &[
            "<look> elements are not translated".to_owned(),
            "b: no subsurface_bsdf nodedef takes radius (vector3); written as ND_subsurface_bsdf".to_owned(),
        ]
    );
    // Still translated, so a renderer can read it.
    let stage = stage(&path)?;
    assert_eq!(
        value(&stage, "/MaterialX/NodeGraphs/b", "info:id")?,
        Some(vt::Value::token("ND_subsurface_bsdf"))
    );
    Ok(())
}

/// Documents of C++ `testUsdMtlxFileFormat` translate into the layers C++
/// `usdMtlx` wrote for them, but for the version: C++ writes the one
/// MaterialX upgraded the document to.
#[test]
fn cpp_baselines() -> Result {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/usd_mtlx");
    for name in ["GraphlessNodes", "usd_preview_surface_gold"] {
        let text = exported(&fixtures.join(name).with_extension("mtlx"))?;
        let expected = fs::read_to_string(fixtures.join(name).with_extension("usda"))?
            .replace("\r\n", "\n")
            .replace("config:mtlx:version = \"1.39\"", "config:mtlx:version = \"1.38\"");
        assert_eq!(text, expected, "{name}");
    }
    Ok(())
}

/// A document reads the documents it includes, each found from the one
/// including it, whether or not it declares the `xi` prefix.
#[test]
fn includes_read() -> Result {
    let dir = tempfile::tempdir()?;
    fs::create_dir_all(dir.path().join("lib/deep"))?;
    fs::write(
        dir.path().join("lib/deep/defs.mtlx"),
        r#"<materialx version="1.39">
             <nodedef name="ND_mine" node="mine"><input name="tint" type="color3" /><output name="out" type="surfaceshader" /></nodedef>
           </materialx>"#,
    )?;
    fs::write(
        dir.path().join("lib/shaders.mtlx"),
        r#"<materialx version="1.39" xmlns:xi="http://www.w3.org/2001/XInclude">
             <xi:include href="deep/defs.mtlx" />
             <mine name="s" type="surfaceshader"><input name="tint" type="color3" value="1, 0, 0" /></mine>
           </materialx>"#,
    )?;
    let path = dir.path().join("look.mtlx");
    fs::write(
        &path,
        r#"<materialx version="1.39">
             <xi:include href="lib/shaders.mtlx" />
             <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s" /></surfacematerial>
           </materialx>"#,
    )?;
    let stage = stage(&path)?;
    assert_eq!(
        value(&stage, "/MaterialX/Materials/m/s", "info:id")?,
        Some(vt::Value::token("ND_mine"))
    );
    assert_eq!(
        value(&stage, "/MaterialX/Materials/m", "inputs:tint")?,
        Some(vt::Value::Vec3f([1.0, 0.0, 0.0].into()))
    );
    Ok(())
}

/// A document that includes itself, or a document that is not there, does
/// not read.
#[test]
fn bad_includes_fail() -> Result {
    let dir = tempfile::tempdir()?;
    let registry = sdf::LayerRegistry::default().with_format(&openusd_mtlx::MTLX);
    for (name, href, reason) in [
        ("cycle.mtlx", "cycle.mtlx", "forms a cycle"),
        ("lost.mtlx", "none.mtlx", "does not resolve"),
    ] {
        let path = dir.path().join(name);
        fs::write(
            &path,
            format!(r#"<materialx version="1.39"><xi:include href="{href}" /></materialx>"#),
        )?;
        let error = registry
            .find_or_open(path.to_str().expect("utf-8 path"))
            .expect_err("does not read")
            .to_string();
        assert!(error.contains(reason), "{error}");
    }
    Ok(())
}

/// What a material carries beside its surface: the base it inherits from,
/// a light shader's terminal, a token as a primvar, and the documentation
/// and interface metadata of its inputs.
#[test]
fn material_extras() -> Result {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("m.mtlx");
    fs::write(
        &path,
        r#"<materialx version="1.39" colorspace="acescg" cms="ocio">
             <nodegraph name="g" doc="A graph">
               <input name="gain" type="float" value="2" uiname="Gain" uifolder="Look/Main" helptext="How bright" />
               <input name="tint" type="color3" value="1, 1, 1" colorspace="lin_rec709" />
               <input name="plain" type="color3" value="1, 1, 1" />
               <multiply name="ns:mul" type="float"><input name="in1" type="float" interfacename="gain" /></multiply>
               <output name="out" type="float" nodename="ns:mul" />
             </nodegraph>
             <point_light name="lamp" type="lightshader" doc="A lamp">
               <input name="intensity" type="float" nodegraph="g" output="out" />
               <token name="mumble" type="string" value="shout" />
             </point_light>
             <surfacematerial name="base" type="material" />
             <surfacematerial name="m" type="material" inherit="base" doc="A material">
               <input name="lightshader" type="lightshader" nodename="lamp" />
             </surfacematerial>
           </materialx>"#,
    )?;
    let text = exported(&path)?;
    for expected in [
        "colorManagementSystem = \"ocio\"",
        "doc = \"A material\"",
        "prepend specializes = </MaterialX/Materials/base>",
        "token outputs:light.connect = </MaterialX/Materials/m/lamp.outputs:light>",
        "string primvars:mumble = \"shout\"",
        "float inputs:intensity.connect = </MaterialX/Materials/m/g.outputs:out>",
        "uniform token info:id = \"ND_point_light\"",
        "doc = \"A graph\"",
        "displayGroup = \"Look:Main\"",
        "displayName = \"Gain\"",
        "doc = \"How bright\"",
        "def Shader \"ns__mul\"",
        "float outputs:out.connect = </MaterialX/NodeGraphs/g/ns__mul.outputs:out>",
    ] {
        assert!(text.contains(expected), "no {expected} in:\n{text}");
    }
    // A colour space is written where it is not the document's.
    let stage = stage(&path)?;
    let graph = stage.prim("/MaterialX/NodeGraphs/g")?;
    assert_eq!(
        graph
            .attribute("inputs:tint")
            .color_space()?
            .as_ref()
            .map(|t| t.as_str()),
        Some("lin_rec709")
    );
    assert_eq!(graph.attribute("inputs:plain").color_space()?, None);
    Ok(())
}

/// A file an included document names beside itself resolves there, not
/// beside the document that includes it, by a path that stays relative to
/// the document opened; a document two others include is read once.
#[test]
fn included_files_anchor() -> Result {
    let dir = tempfile::tempdir()?;
    for sub in ["lib/tex", "tex"] {
        fs::create_dir_all(dir.path().join(sub))?;
        fs::write(dir.path().join(sub).join("a.png"), b"")?;
    }
    fs::write(
        dir.path().join("lib/shared.mtlx"),
        r#"<materialx version="1.39" fileprefix="tex/">
             <image name="albedo" type="color3"><input name="file" type="filename" value="a.png" /></image>
             <image name="tiles" type="color3"><input name="file" type="filename" value="t.<UDIM>.png" /></image>
           </materialx>"#,
    )?;
    for name in ["one", "two"] {
        fs::write(
            dir.path().join("lib").join(name).with_extension("mtlx"),
            r#"<materialx version="1.39"><xi:include href="shared.mtlx" /></materialx>"#,
        )?;
    }
    let path = dir.path().join("look.mtlx");
    fs::write(
        &path,
        r#"<materialx version="1.39">
             <xi:include href="lib/one.mtlx" />
             <xi:include href="lib/two.mtlx" />
             <standard_surface name="s" type="surfaceshader">
               <input name="base_color" type="color3" nodename="albedo" />
               <input name="coat_color" type="color3" nodename="tiles" />
             </standard_surface>
             <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s" /></surfacematerial>
           </materialx>"#,
    )?;
    let composed = stage(&path)?;
    let asset = asset(&composed, "/MaterialX/Materials/m/NodeGraphs/albedo", "inputs:file")?;
    assert_eq!(
        Path::new(asset.resolved_path().expect("resolves")).canonicalize()?,
        dir.path().join("lib/tex/a.png").canonicalize()?
    );
    // A pattern naming no file anchors beside the library too.
    let tiles = self::asset(&composed, "/MaterialX/Materials/m/NodeGraphs/tiles", "inputs:file")?;
    assert_eq!(tiles.asset_path(), "lib/tex/t.<UDIM>.png");

    // A library included by an absolute path anchors its names at itself.
    let absolute = dir.path().join("absolute.mtlx");
    fs::write(
        &absolute,
        format!(
            r#"<materialx version="1.39">
                 <xi:include href="{}" />
                 <standard_surface name="s" type="surfaceshader"><input name="coat_color" type="color3" nodename="tiles" /></standard_surface>
                 <surfacematerial name="m" type="material"><input name="surfaceshader" type="surfaceshader" nodename="s" /></surfacematerial>
               </materialx>"#,
            dir.path().join("lib/shared.mtlx").display()
        ),
    )?;
    let composed = stage(&absolute)?;
    let tiles = self::asset(&composed, "/MaterialX/Materials/m/NodeGraphs/tiles", "inputs:file")?;
    let pattern = Path::new(tiles.asset_path());
    assert!(pattern.is_absolute(), "{pattern:?}");
    assert!(pattern.ends_with("lib/tex/t.<UDIM>.png"), "{pattern:?}");
    Ok(())
}
