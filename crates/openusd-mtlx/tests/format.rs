//! The `.mtlx` format through a stage: the documents of `usd-wg-assets`
//! composed by reference, by payload and as a root layer, and their
//! translations pinned against the layers under `tests/expected/`.
//!
//! The goldens regenerate with `UPDATE_EXPECTED=1`.

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
    let Some(vt::Value::AssetPath(asset)) = file.get::<vt::Value>()? else {
        panic!("no file")
    };
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
    let file = stage.prim("/Look/NodeGraphs/albedo")?.attribute("inputs:file");
    let Some(vt::Value::AssetPath(asset)) = file.get::<vt::Value>()? else {
        panic!("no file")
    };
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
    let update = std::env::var_os("UPDATE_EXPECTED").is_some();
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
    let Some(Ok(Some(vt::Value::Dictionary(data)))) = layer
        .pseudo_root()
        .map(|root| root.field(sdf::FieldKey::CustomLayerData.as_str()))
    else {
        panic!("no customLayerData")
    };
    let Some(vt::Value::StringVec(warnings)) = data.get_at("mtlx:warnings") else {
        panic!("no warnings: {data:?}")
    };
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
