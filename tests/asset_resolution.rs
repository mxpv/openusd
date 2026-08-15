//! Value resolution anchors and resolves `asset` / `asset[]` paths against
//! the layer of the strongest opinion, populating `AssetPath::resolved_path`.

use std::fs;

use openusd::sdf;
use openusd::usd::{self, Stage};

/// Writes `source` as `scene.usda` under `dir` and opens it.
fn open_scene(dir: &tempfile::TempDir, source: &str) -> Stage {
    let usda = dir.path().join("scene.usda");
    fs::write(&usda, source).expect("write layer");
    Stage::open(usda.to_str().unwrap()).expect("open stage")
}

/// The composed `asset` value at `path`, which must be authored.
fn asset_at(stage: &Stage, path: &str) -> sdf::AssetPath {
    stage
        .attribute(path)
        .expect("attribute")
        .get::<sdf::AssetPath>()
        .expect("read")
        .expect("asset value")
}

/// The authored site of every reported invalid-expression diagnostic.
fn expression_error_sites(stage: &Stage) -> Vec<sdf::Path> {
    stage
        .composition_errors()
        .into_iter()
        .filter_map(|e| match e {
            openusd::pcp::Error::InvalidExpression { site_path, .. } => Some(site_path),
            _ => None,
        })
        .collect()
}

#[test]
fn resolved_path_populated() {
    let dir = tempfile::tempdir().expect("tempdir");
    let tex = dir.path().join("tex.png");
    fs::write(&tex, b"x").expect("write asset");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0\n",
            "def Material \"M\"\n{\n",
            "    asset inputs:file = @./tex.png@\n",
            "    asset[] inputs:files = [@./tex.png@, @./missing.png@]\n",
            "}\n",
        ),
    );
    let canonical = tex.canonicalize().unwrap().to_string_lossy().into_owned();

    // Scalar `asset`: authored path preserved, resolved path filled in.
    let asset = stage
        .attribute("/M.inputs:file")
        .unwrap()
        .get::<sdf::AssetPath>()
        .unwrap()
        .expect("asset value");
    assert_eq!(asset.as_str(), "./tex.png");
    assert_eq!(asset.resolved_path(), Some(canonical.as_str()));

    // `asset[]`: each element resolved against the same layer; a missing
    // target stays unresolved.
    let files = stage
        .attribute("/M.inputs:files")
        .unwrap()
        .get::<Vec<sdf::AssetPath>>()
        .unwrap()
        .expect("asset array value");
    assert_eq!(files.len(), 2);
    assert_eq!(files[0].resolved_path(), Some(canonical.as_str()));
    assert_eq!(files[1].as_str(), "./missing.png");
    assert_eq!(files[1].resolved_path(), None);

    // The time-aware read anchors the default-sourced value the same way.
    let at_time = stage
        .attribute("/M.inputs:file")
        .unwrap()
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
        .attribute("/M.inputs:file")
        .unwrap()
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
    let stage = open_scene(
        &dir,
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
    );
    let canonical = tex.canonicalize().unwrap().to_string_lossy().into_owned();

    let asset = stage
        .attribute("/M.inputs:file")
        .unwrap()
        .get::<sdf::AssetPath>()
        .unwrap()
        .expect("asset value");
    // Authored path keeps the expression; evaluated path substitutes the var.
    assert_eq!(asset.as_str(), "`\"./${NAME}.png\"`");
    assert_eq!(asset.evaluated_path(), Some("./tex.png"));
    assert_eq!(asset.asset_path(), "./tex.png");
    assert_eq!(asset.resolved_path(), Some(canonical.as_str()));
}

/// A malformed asset-path expression is reported, not dropped silently — the
/// same diagnostic a reference or payload arc records for its asset path.
/// Repeated reads keep reporting it exactly once.
#[test]
fn bad_expression_reported_once() {
    let dir = tempfile::tempdir().expect("tempdir");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0
",
            "def Material \"M\"
{
",
            "    asset inputs:file = @`\"./${NAME}.png\" +`@
",
            "}
",
        ),
    );

    let asset = asset_at(&stage, "/M.inputs:file");
    assert_eq!(
        asset.as_str(),
        "`\"./${NAME}.png\" +`",
        "the authored expression is kept"
    );
    assert!(asset.evaluated_path().is_none(), "a failed expression derives nothing");
    assert_eq!(expression_error_sites(&stage).len(), 1, "the failure is reported");

    asset_at(&stage, "/M.inputs:file");
    asset_at(&stage, "/M.inputs:file");
    assert_eq!(
        expression_error_sites(&stage).len(),
        1,
        "re-reading does not duplicate it"
    );
}

/// The reported site is the path in the layer that authored the expression,
/// not the composed stage path — they differ across a reference arc.
#[test]
fn error_names_authored_site() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0
def \"Ref\" (
    references = @t.usda@
) {}
",
    )
    .expect("write root");
    fs::write(
        dir.path().join("t.usda"),
        concat!(
            "#usda 1.0
(
    defaultPrim = \"P\"
)
",
            "def \"P\" {
",
            "    asset inputs:file = @`\"./${NAME}.png\" +`@
",
            "}
",
        ),
    )
    .expect("write target");

    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap()).expect("open stage");
    assert!(asset_at(&stage, "/Ref.inputs:file").evaluated_path().is_none());
    assert_eq!(
        expression_error_sites(&stage),
        vec![sdf::path("/P.inputs:file").unwrap()],
        "the site is the authored path in t.usda, not the composed /Ref.inputs:file"
    );
}

/// A recorded diagnostic does not outlive the edit that fixed it. The edit is
/// a plain value change, which drops no prim index, so the revision bump is the
/// only thing that can clear a value-time asset error — nothing records it as a
/// dependency.
#[test]
fn fixing_value_clears_error() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("tex.png"), b"x").expect("write asset");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0
",
            "def Material \"M\"
{
",
            "    asset inputs:file = @`\"./tex.png\" +`@
",
            "}
",
        ),
    );
    assert!(
        asset_at(&stage, "/M.inputs:file").resolved_path().is_none(),
        "a malformed expression derives nothing"
    );
    assert_eq!(expression_error_sites(&stage).len(), 1, "and is reported");

    stage
        .attribute("/M.inputs:file")
        .expect("attribute")
        .set(sdf::AssetPath::new("./tex.png"))
        .expect("author a literal path");

    assert!(
        asset_at(&stage, "/M.inputs:file").resolved_path().is_some(),
        "the repaired value resolves"
    );
    assert!(
        stage.composition_errors().is_empty(),
        "the diagnostic does not outlive the edit that fixed it, got {:?}",
        stage.composition_errors()
    );
}

/// A time-sampled `asset` resolves like a default-sourced one: the selected
/// sample is anchored against, and evaluated with the variables of, the layer
/// that authored the samples. A cached `AttributeQuery` replays it identically.
#[test]
fn time_sampled_expression_resolved() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("a.png"), b"a").expect("write asset");
    fs::write(dir.path().join("b.png"), b"b").expect("write asset");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0\n",
            "(\n    expressionVariables = { string DIR = \".\" }\n)\n",
            "def Material \"M\"\n{\n",
            "    asset inputs:file.timeSamples = {\n",
            "        0: @`\"${DIR}/a.png\"`@,\n",
            "        10: @`\"${DIR}/b.png\"`@,\n",
            "    }\n",
            "}\n",
        ),
    );
    let attr = stage.attribute("/M.inputs:file").expect("attribute");
    let query = stage.attribute_query("/M.inputs:file").expect("query");

    for (time, leaf) in [(0.0, "./a.png"), (10.0, "./b.png")] {
        let direct = attr
            .get_at::<sdf::AssetPath>(usd::TimeCode::from(time))
            .expect("read")
            .expect("asset value");
        assert_eq!(direct.evaluated_path(), Some(leaf), "direct read at {time}");
        assert!(direct.resolved_path().is_some(), "direct read resolves at {time}");

        let replayed = query
            .get_at::<sdf::AssetPath>(usd::TimeCode::from(time))
            .expect("query read")
            .expect("asset value");
        assert_eq!(
            replayed.evaluated_path(),
            direct.evaluated_path(),
            "the cached query replays the direct read at {time}"
        );
        assert_eq!(replayed.resolved_path(), direct.resolved_path());
    }
}

/// Only the sample a read selects is evaluated, so a malformed expression
/// authored at one time is not reported by a read at another (see
/// `AttributeValueSource::TimeSamples`).
#[test]
fn unselected_sample_not_reported() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(dir.path().join("a.png"), b"a").expect("write asset");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0\n",
            "def Material \"M\"\n{\n",
            "    asset inputs:file.timeSamples = {\n",
            "        0: @`\"./a.png\"`@,\n",
            "        10: @`\"./b.png\" +`@,\n",
            "    }\n",
            "}\n",
        ),
    );
    let query = stage.attribute_query("/M.inputs:file").expect("query");
    let at_zero = query
        .get_at::<sdf::AssetPath>(usd::TimeCode::from(0.0))
        .expect("read")
        .expect("asset value");
    assert_eq!(at_zero.evaluated_path(), Some("./a.png"));
    assert!(
        stage.composition_errors().is_empty(),
        "the malformed sample at time 10 was never selected, got {:?}",
        stage.composition_errors()
    );

    assert!(
        query
            .get_at::<sdf::AssetPath>(usd::TimeCode::from(10.0))
            .expect("read")
            .expect("asset value")
            .evaluated_path()
            .is_none()
    );
    assert_eq!(stage.composition_errors().len(), 1, "reading it does report it");
}

/// The authored site of an expression inside a variant is the variant-decorated
/// path, which the composed stage path strips.
#[test]
fn error_names_variant_site() {
    let dir = tempfile::tempdir().expect("tempdir");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0
",
            "def Material \"M\" (
",
            "    variantSets = \"v\"
",
            "    variants = { string v = \"sel\" }
",
            ")
{
",
            "    variantSet \"v\" = {
",
            "        \"sel\" {
",
            "            asset inputs:file = @`\"./x.png\" +`@
",
            "        }
",
            "    }
",
            "}
",
        ),
    );
    asset_at(&stage, "/M.inputs:file");

    assert_eq!(
        expression_error_sites(&stage),
        vec![sdf::path("/M{v=sel}.inputs:file").unwrap()],
        "the site keeps the variant selection the composed path strips"
    );
}

/// A cached value source replays without re-entering resolution, so its
/// diagnostic must survive anything that is not an edit. Materializing a
/// prototype drops indices mid-query — it composes more of the scene rather
/// than invalidating it — and must not take unrelated diagnostics with it.
#[test]
fn lazy_prototype_keeps_error() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("t.usda"),
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    def \"Inner\" { custom double y = 2 }\n}\n",
    )
    .expect("write target");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0\n",
            "def Material \"M\"\n{\n",
            "    asset inputs:file = @`\"./x.png\" +`@\n",
            "}\n",
            "def \"A\" (\n    references = @t.usda@\n    instanceable = true\n) {}\n",
            "def \"B\" (\n    references = @t.usda@\n    instanceable = true\n) {}\n",
        ),
    );

    let query = stage.attribute_query("/M.inputs:file").expect("query");
    assert!(
        query
            .get_at::<sdf::AssetPath>(usd::TimeCode::from(0.0))
            .expect("read")
            .expect("asset value")
            .evaluated_path()
            .is_none()
    );
    assert_eq!(expression_error_sites(&stage).len(), 1, "the failure is reported");

    // Reading through an instance proxy mints and materializes the shared
    // prototype, which drops indices without advancing the revision.
    assert_eq!(
        stage.attribute("/A/Inner.y").expect("attr").get::<f64>().unwrap(),
        Some(2.0)
    );

    query
        .get_at::<sdf::AssetPath>(usd::TimeCode::from(0.0))
        .expect("read")
        .expect("asset value");
    assert_eq!(
        expression_error_sites(&stage).len(),
        1,
        "the diagnostic survives an unrelated prototype materialization"
    );
}
