//! Value resolution anchors and resolves `asset` / `asset[]` paths against
//! the layer of the strongest opinion, populating `AssetPath::resolved_path`.

use std::fs;

use openusd::sdf;
use openusd::usd::Stage;

#[test]
fn resolved_path_populated() {
    let dir = tempfile::tempdir().expect("tempdir");
    let tex = dir.path().join("tex.png");
    fs::write(&tex, b"x").expect("write asset");
    let usda = dir.path().join("scene.usda");
    fs::write(
        &usda,
        concat!(
            "#usda 1.0\n",
            "def Material \"M\"\n{\n",
            "    asset inputs:file = @./tex.png@\n",
            "    asset[] inputs:files = [@./tex.png@, @./missing.png@]\n",
            "}\n",
        ),
    )
    .expect("write layer");

    let stage = Stage::open(usda.to_str().unwrap()).expect("open stage");
    let canonical = tex.canonicalize().unwrap().to_string_lossy().into_owned();

    // Scalar `asset`: authored path preserved, resolved path filled in.
    let asset = stage
        .attribute_at(sdf::path("/M.inputs:file").unwrap())
        .get::<sdf::AssetPath>()
        .unwrap()
        .expect("asset value");
    assert_eq!(asset.as_str(), "./tex.png");
    assert_eq!(asset.resolved_path(), Some(canonical.as_str()));

    // `asset[]`: each element resolved against the same layer; a missing
    // target stays unresolved.
    let files = stage
        .attribute_at(sdf::path("/M.inputs:files").unwrap())
        .get::<Vec<sdf::AssetPath>>()
        .unwrap()
        .expect("asset array value");
    assert_eq!(files.len(), 2);
    assert_eq!(files[0].resolved_path(), Some(canonical.as_str()));
    assert_eq!(files[1].as_str(), "./missing.png");
    assert_eq!(files[1].resolved_path(), None);

    // The time-aware read anchors the default-sourced value the same way.
    let at_time = stage
        .attribute_at(sdf::path("/M.inputs:file").unwrap())
        .get_at::<sdf::AssetPath>(openusd::usd::TimeCode::new(0.0))
        .unwrap()
        .expect("asset value at time");
    assert_eq!(at_time.resolved_path(), Some(canonical.as_str()));
}

/// Resolution owns the derived resolved path: an authored value that carries a
/// stale resolved path does not survive a read where the path is unresolvable.
#[test]
fn stale_resolved_path_cleared() {
    let stage = Stage::builder().in_memory("stale.usda").expect("in-memory stage");
    stage.define_prim("/M").expect("define prim");
    stage
        .create_attribute("/M.inputs:file", "asset")
        .expect("create attribute")
        .set(sdf::AssetPath::with_resolved_path("./missing.png", "/stale/location"))
        .expect("set asset");

    let asset = stage
        .attribute_at(sdf::path("/M.inputs:file").unwrap())
        .get::<sdf::AssetPath>()
        .unwrap()
        .expect("asset value");
    assert_eq!(asset.as_str(), "./missing.png");
    assert_eq!(asset.resolved_path(), None);
}

/// An asset path authored as a variable expression is evaluated against the
/// layer's `expressionVariables` before anchoring and resolution.
#[test]
fn expression_evaluated_and_resolved() {
    let dir = tempfile::tempdir().expect("tempdir");
    let tex = dir.path().join("tex.png");
    fs::write(&tex, b"x").expect("write asset");
    let usda = dir.path().join("scene.usda");
    fs::write(
        &usda,
        concat!(
            "#usda 1.0\n",
            "(\n",
            "    expressionVariables = {\n",
            "        string NAME = \"tex\"\n",
            "    }\n",
            ")\n",
            "def Material \"M\"\n{\n",
            "    asset inputs:file = @`\"./${NAME}.png\"`@\n",
            "}\n",
        ),
    )
    .expect("write layer");

    let stage = Stage::open(usda.to_str().unwrap()).expect("open stage");
    let canonical = tex.canonicalize().unwrap().to_string_lossy().into_owned();

    let asset = stage
        .attribute_at(sdf::path("/M.inputs:file").unwrap())
        .get::<sdf::AssetPath>()
        .unwrap()
        .expect("asset value");
    // Authored path keeps the expression; evaluated path substitutes the var.
    assert_eq!(asset.as_str(), "`\"./${NAME}.png\"`");
    assert_eq!(asset.evaluated_path(), Some("./tex.png"));
    assert_eq!(asset.asset_path(), "./tex.png");
    assert_eq!(asset.resolved_path(), Some(canonical.as_str()));
}
