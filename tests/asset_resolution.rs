//! Value resolution anchors and resolves `asset` / `asset[]` paths against
//! the layer of the strongest opinion, populating `AssetPath::resolved_path`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;

use openusd::ar;
use openusd::pcp;
use openusd::sdf;
use openusd::usd::{self, Stage};
use openusd::usdz::ArchiveWriter;

/// Writes `source` as `scene.usda` under `dir` and opens it against the
/// process-wide schemas.
fn open_scene(dir: &tempfile::TempDir, source: &str) -> Stage {
    open_scene_with(dir, source, usd::SchemaRegistry::global().clone())
}

/// Writes `source` as `scene.usda` under `dir` and opens it against `registry`.
fn open_scene_with(dir: &tempfile::TempDir, source: &str, registry: Arc<usd::SchemaRegistry>) -> Stage {
    let usda = dir.path().join("scene.usda");
    fs::write(&usda, source).expect("write layer");
    Stage::builder()
        .schema_registry(registry)
        .open(usda.to_str().unwrap())
        .expect("open stage")
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

/// The composed `asset` value at `path` at `time`, which must be authored.
fn asset_at_time(stage: &Stage, path: &str, time: f64) -> sdf::AssetPath {
    stage
        .attribute(path)
        .expect("attribute")
        .get_at::<sdf::AssetPath>(usd::TimeCode::from(time))
        .expect("read")
        .expect("asset value")
}

/// Asserts `asset` resolved to a location ending in `suffix`, compared with
/// forward slashes so the check reads the same on Windows. `what` names the
/// anchor the suffix is proving.
fn assert_resolved_under(asset: &sdf::AssetPath, suffix: &str, what: &str) {
    let resolved = asset.resolved_path().expect("the value resolves");
    assert!(
        resolved.replace('\\', "/").contains(suffix),
        "expected {what} ({suffix}), got {resolved}"
    );
}

/// Whether the stage reports a clip it could not read.
fn reports_unreadable_clip(stage: &Stage) -> bool {
    stage
        .composition_errors()
        .iter()
        .any(|e| matches!(e, pcp::CompositionError::UnreadableClip { .. }))
}

/// The authored site of every reported invalid-expression diagnostic.
fn expression_error_sites(stage: &Stage) -> Vec<sdf::Path> {
    stage
        .composition_errors()
        .into_iter()
        .filter_map(|e| match e {
            pcp::CompositionError::InvalidExpression { site_path, .. } => Some(site_path),
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
    let query = stage.attribute_query("/M.inputs:file").expect("query");

    for (time, leaf) in [(0.0, "./a.png"), (10.0, "./b.png")] {
        let direct = asset_at_time(&stage, "/M.inputs:file", time);
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

/// A clip-sourced `asset` anchors on the *clip's own layer*, not on the layer
/// that authored the clip metadata, while its `${VAR}` resolves against the
/// variables of the node that introduced the clips. The clips live in a
/// subdirectory, so a relative path resolves only under the right anchor.
#[test]
fn clip_sample_anchor() {
    let dir = tempfile::tempdir().expect("tempdir");
    let sub = dir.path().join("sub");
    fs::create_dir(&sub).expect("mkdir");
    fs::write(sub.join("texA.png"), b"a").expect("write asset");
    fs::write(sub.join("fallback.png"), b"f").expect("write asset");
    fs::write(
        sub.join("clip0.usda"),
        "#usda 1.0\ndef \"Model\" {\n    asset file.timeSamples = {\n        0: @`\"./tex${SUF}.png\"`@,\n    }\n}\n",
    )
    .expect("write clip0");
    fs::write(sub.join("clip1.usda"), "#usda 1.0\ndef \"Model\" {\n}\n").expect("write clip1");
    fs::write(
        sub.join("manifest.usda"),
        "#usda 1.0\ndef \"Model\" {\n    asset file = @./fallback.png@\n}\n",
    )
    .expect("write manifest");

    let stage = open_scene(
        &dir,
        r#"#usda 1.0
(
    defaultPrim = "Model"
    expressionVariables = { string SUF = "A" }
)
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./sub/clip0.usda@, @./sub/clip1.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0), (10, 1)]
            asset manifestAssetPath = @./sub/manifest.usda@
        }
    }
)
{
    asset file
}
"#,
    );

    // The active clip's sample: evaluated against the introducing stack's
    // variables and anchored on the clip layer.
    let active = asset_at_time(&stage, "/Model.file", 0.0);
    assert_eq!(active.evaluated_path(), Some("./texA.png"));
    assert_resolved_under(&active, "/sub/texA.png", "the clip layer's anchor");

    // A gap in the active clip falls to the manifest default, which anchors on
    // the manifest layer rather than on either clip.
    let fallback = asset_at_time(&stage, "/Model.file", 10.0);
    assert_eq!(fallback.as_str(), "./fallback.png");
    assert_resolved_under(&fallback, "/sub/fallback.png", "the manifest layer's anchor");
}

/// `interpolateMissingClipValues` fills a gap from the surrounding clips, and
/// each contributing value is resolved against its own clip layer before
/// anything combines them. An asset path does not interpolate, so the bracket
/// holds the lower clip's value — which therefore carries the lower clip's
/// anchor, not the active clip's.
#[test]
fn clip_gap_anchor() {
    let dir = tempfile::tempdir().expect("tempdir");
    let lo = dir.path().join("lo");
    let hi = dir.path().join("hi");
    fs::create_dir(&lo).expect("mkdir");
    fs::create_dir(&hi).expect("mkdir");
    fs::write(lo.join("tex.png"), b"l").expect("write asset");
    fs::write(hi.join("tex.png"), b"h").expect("write asset");
    // The low and high clips each carry a sample naming the same relative path;
    // only the anchor distinguishes them.
    for at in [&lo, &hi] {
        fs::write(
            at.join("clip.usda"),
            r#"#usda 1.0
def "Model" {
    asset file.timeSamples = {
        0: @./tex.png@,
    }
}
"#,
        )
        .expect("write clip");
    }
    // The middle clip declares nothing, so it is the gap.
    fs::write(
        dir.path().join("mid.usda"),
        "#usda 1.0
def \"Model\" {
}
",
    )
    .expect("write mid");
    fs::write(
        dir.path().join("manifest.usda"),
        r#"#usda 1.0
def "Model" {
    asset file
}
"#,
    )
    .expect("write manifest");

    let stage = open_scene(
        &dir,
        r#"#usda 1.0
(
    defaultPrim = "Model"
)
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./lo/clip.usda@, @./mid.usda@, @./hi/clip.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0), (10, 1), (20, 2)]
            asset manifestAssetPath = @./manifest.usda@
            bool interpolateMissingClipValues = true
        }
    }
)
{
    asset file
}
"#,
    );

    // Inside the middle clip's window both sides contribute; the hold picks the
    // lower one, already anchored on the low clip.
    let gap = asset_at_time(&stage, "/Model.file", 15.0);
    assert_eq!(gap.as_str(), "./tex.png");
    assert_resolved_under(&gap, "/lo/tex.png", "the lower clip's anchor, held through the gap");

    // The high clip's own window anchors on the high clip, proving the two
    // relative paths really do resolve differently.
    let high = asset_at_time(&stage, "/Model.file", 20.0);
    assert_resolved_under(&high, "/hi/tex.png", "the high clip's anchor");
}

/// A malformed expression in a clip-sourced `asset` reports through the clip
/// cache's own diagnostics, which merge into the same query channel a composed
/// opinion's failure uses.
#[test]
fn clip_bad_expression_reported() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("clip.usda"),
        "#usda 1.0\ndef \"Model\" {\n    asset file.timeSamples = {\n        0: @`\"./x.png\" +`@,\n    }\n}\n",
    )
    .expect("write clip");
    fs::write(
        dir.path().join("manifest.usda"),
        "#usda 1.0\ndef \"Model\" {\n    asset file\n}\n",
    )
    .expect("write manifest");

    let stage = open_scene(
        &dir,
        r#"#usda 1.0
(
    defaultPrim = "Model"
)
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0)]
            asset manifestAssetPath = @./manifest.usda@
        }
    }
)
{
    asset file
}
"#,
    );

    let value = asset_at_time(&stage, "/Model.file", 0.0);
    assert!(value.evaluated_path().is_none(), "a failed expression derives nothing");
    assert_eq!(
        expression_error_sites(&stage),
        vec![sdf::path("/Model.file").unwrap()],
        "the site is the attribute's path inside the clip"
    );
}

/// A gap fill reads both brackets but returns only one, so a malformed
/// expression in the discarded upper clip must not be reported for a value
/// nobody sees — the same rule an unselected time sample follows.
#[test]
fn clip_gap_ignores_upper() {
    let dir = tempfile::tempdir().expect("tempdir");
    let lo = dir.path().join("lo");
    fs::create_dir(&lo).expect("mkdir");
    fs::write(lo.join("tex.png"), b"l").expect("write asset");
    fs::write(
        lo.join("clip.usda"),
        r#"#usda 1.0
def "Model" {
    asset file.timeSamples = {
        0: @./tex.png@,
    }
}
"#,
    )
    .expect("write low clip");
    // The later clip's sample is malformed; the hold never selects it.
    fs::write(
        dir.path().join("hi.usda"),
        r#"#usda 1.0
def "Model" {
    asset file.timeSamples = {
        0: @`"./x.png" +`@,
    }
}
"#,
    )
    .expect("write high clip");
    fs::write(
        dir.path().join("mid.usda"),
        "#usda 1.0
def \"Model\" {
}
",
    )
    .expect("write mid");
    fs::write(
        dir.path().join("manifest.usda"),
        r#"#usda 1.0
def "Model" {
    asset file
}
"#,
    )
    .expect("write manifest");

    let stage = open_scene(
        &dir,
        r#"#usda 1.0
(
    defaultPrim = "Model"
)
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./lo/clip.usda@, @./mid.usda@, @./hi.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0), (10, 1), (20, 2)]
            asset manifestAssetPath = @./manifest.usda@
            bool interpolateMissingClipValues = true
        }
    }
)
{
    asset file
}
"#,
    );

    let gap = asset_at_time(&stage, "/Model.file", 15.0);
    assert_resolved_under(&gap, "/lo/tex.png", "the lower clip's anchor");
    assert!(
        stage.composition_errors().is_empty(),
        "the discarded upper bracket must not report, got {:?}",
        stage.composition_errors()
    );

    // Reading the high clip's own window does report it.
    assert!(
        asset_at_time(&stage, "/Model.file", 20.0).evaluated_path().is_none(),
        "the malformed sample derives nothing when it is the one selected"
    );
    assert_eq!(expression_error_sites(&stage).len(), 1);
}

/// Writes a clip layer under `dir` holding `v` time samples, one per entry.
fn write_clip(dir: &tempfile::TempDir, name: &str, samples: &[(f64, f64)]) {
    let entries: String = samples
        .iter()
        .map(|(t, v)| format!("            {t}: {v:?},\n"))
        .collect();
    fs::write(
        dir.path().join(name),
        format!("#usda 1.0\n\ndef \"P\"\n{{\n    double v.timeSamples = {{\n{entries}    }}\n}}\n"),
    )
    .expect("write clip");
}

/// The composed `double` at `path` and `time`.
fn value_at(stage: &Stage, path: &str, time: f64) -> Option<f64> {
    stage
        .attribute(path)
        .expect("attribute")
        .get_at::<f64>(usd::TimeCode::from(time))
        .expect("read")
}

/// A stage whose `clips` metadata is `fields`, with `SHOT` in scope.
fn clip_scene(dir: &tempfile::TempDir, shot: &str, fields: &str) -> Stage {
    open_scene(
        dir,
        &format!(
            concat!(
                "#usda 1.0\n",
                "(\n",
                "    expressionVariables = {{ string SHOT = \"{shot}\" }}\n",
                ")\n",
                "def \"P\" (\n",
                "    clips = {{\n",
                "        dictionary default = {{\n",
                "{fields}",
                "            string primPath = \"/P\"\n",
                "        }}\n",
                "    }}\n",
                ")\n",
                "{{\n",
                "    double v\n",
                "}}\n",
            ),
            shot = shot,
            fields = fields,
        ),
    )
}

/// A `templateAssetPath` whose pattern comes from a variable expands to the
/// sequence the evaluated pattern names, so the clips are found and sourced.
/// The pattern must be evaluated before its `#` groups are read.
#[test]
fn clip_template_expression() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s010.1.usda", &[(1.0, 11.0)]);
    write_clip(&dir, "s010.2.usda", &[(2.0, 22.0)]);
    let stage = clip_scene(
        &dir,
        "s010",
        concat!(
            "            asset templateAssetPath = @`\"./${SHOT}.#.usda\"`@\n",
            "            double templateStartTime = 1\n",
            "            double templateEndTime = 2\n",
            "            double templateStride = 1\n",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), Some(11.0));
    assert_eq!(value_at(&stage, "/P.v", 2.0), Some(22.0));
    assert!(stage.composition_errors().is_empty());
}

/// C++ authors `templateAssetPath` as a `string`, so the pattern arrives
/// string-typed from any asset it wrote. An expression in it is evaluated just
/// as the `asset`-typed spelling is.
#[test]
fn clip_string_template_expression() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s140.1.usda", &[(1.0, 140.0)]);
    let stage = clip_scene(
        &dir,
        "s140",
        concat!(
            "            string templateAssetPath = '`\"./${SHOT}.#.usda\"`'\n",
            "            double templateStartTime = 1\n",
            "            double templateEndTime = 1\n",
            "            double templateStride = 1\n",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), Some(140.0));
    assert!(stage.composition_errors().is_empty());
}

/// An expression element of an explicit `assetPaths` is evaluated, so the clip
/// it names is opened and sources the value.
#[test]
fn clip_asset_paths_expression() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s020.usda", &[(1.0, 33.0)]);
    let stage = clip_scene(
        &dir,
        "s020",
        concat!(
            "            asset[] assetPaths = [@`\"./${SHOT}.usda\"`@]\n",
            "            double2[] active = [(1, 0)]\n",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), Some(33.0));
    assert!(stage.composition_errors().is_empty());
}

/// An expression `manifestAssetPath` is evaluated, so the manifest it names is
/// the one that gates the set. The clip's `v` is declared only by that manifest,
/// so a path left unevaluated gates the set out entirely.
#[test]
fn clip_manifest_expression() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s030.usda", &[(1.0, 44.0)]);
    fs::write(
        dir.path().join("s030_man.usda"),
        "#usda 1.0\n\ndef \"P\"\n{\n    double v\n}\n",
    )
    .expect("write manifest");
    let stage = clip_scene(
        &dir,
        "s030",
        concat!(
            "            asset[] assetPaths = [@./s030.usda@]\n",
            "            asset manifestAssetPath = @`\"./${SHOT}_man.usda\"`@\n",
            "            double2[] active = [(1, 0)]\n",
        ),
    );

    assert_eq!(
        value_at(&stage, "/P.v", 1.0),
        Some(44.0),
        "the manifest the expression names is the one that gates the set"
    );
    assert!(stage.composition_errors().is_empty());
}

/// A `manifestAssetPath` authored as an array is not a scalar asset path, so
/// the set ignores it and synthesizes a manifest instead. A malformed
/// expression inside the field nobody reads must not drop the set.
#[test]
fn clip_array_manifest_ignored() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s150.usda", &[(1.0, 150.0)]);
    let stage = clip_scene(
        &dir,
        "s150",
        concat!(
            "            asset[] assetPaths = [@./s150.usda@]
",
            "            asset[] manifestAssetPath = [@`\"./m.usda\" +`@]
",
            "            double2[] active = [(1, 0)]
",
        ),
    );

    assert_eq!(
        value_at(&stage, "/P.v", 1.0),
        Some(150.0),
        "the set resolves through a synthesized manifest"
    );
    assert!(
        stage.composition_errors().is_empty(),
        "the unread field is not evaluated: {:?}",
        stage.composition_errors()
    );
}

/// The same rule for a `templateAssetPath` authored as an array: the set has no
/// usable asset field either way, but the one it never reads is not evaluated,
/// so no diagnostic blames the author for it.
#[test]
fn clip_array_template_ignored() {
    let dir = tempfile::tempdir().expect("tempdir");
    let stage = clip_scene(
        &dir,
        "s160",
        concat!(
            "            asset[] templateAssetPath = [@`\"./${SHOT}.#.usda\" +`@]
",
            "            double templateStartTime = 1
",
            "            double templateEndTime = 1
",
            "            double templateStride = 1
",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), None, "the set has no usable asset field");
    assert!(
        stage.composition_errors().is_empty(),
        "the unread field is not evaluated: {:?}",
        stage.composition_errors()
    );
}

/// A malformed expression in a clip asset path is reported once, at the site
/// that authored it, and drops its set rather than reaching the resolver as a
/// literal — which would report a second, misleading unreadable-clip error.
#[test]
fn clip_metadata_expression_error() {
    let dir = tempfile::tempdir().expect("tempdir");
    let stage = clip_scene(
        &dir,
        "s040",
        concat!(
            "            asset[] assetPaths = [@`\"./${SHOT}.usda\" +`@]\n",
            "            double2[] active = [(1, 0)]\n",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), None, "the set contributes nothing");
    assert_eq!(expression_error_sites(&stage), vec![sdf::path("/P").expect("path")]);
    assert!(
        !reports_unreadable_clip(&stage),
        "the failed expression is reported once, not twice: {:?}",
        stage.composition_errors()
    );
}

/// Editing the variable moves the set to the clips the new value names. Nothing
/// records a per-variable dependency for a value-time read, so the revision bump
/// every edit funnels through is what re-resolves the clips.
#[test]
fn clip_expression_reevaluated() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s050.usda", &[(1.0, 55.0)]);
    write_clip(&dir, "s060.usda", &[(1.0, 66.0)]);
    let stage = clip_scene(
        &dir,
        "s050",
        concat!(
            "            asset[] assetPaths = [@`\"./${SHOT}.usda\"`@]\n",
            "            double2[] active = [(1, 0)]\n",
        ),
    );
    assert_eq!(value_at(&stage, "/P.v", 1.0), Some(55.0));

    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let resynced = resynced.clone();
        stage.add_sink(move |_stage: &Stage, change: &usd::CommittedChange<'_>| {
            resynced
                .borrow_mut()
                .extend(change.asset_paths_resynced.iter().cloned());
        })
    };

    let root = stage.root_layer().identifier().to_string();
    stage
        .layer_mut(&root)
        .expect("the root layer is live")
        .edit(|e| {
            e.set_expression_variables(HashMap::from([(
                "SHOT".to_string(),
                sdf::Value::String("s060".to_string()),
            )]))
        })
        .expect("author variables");

    assert_eq!(value_at(&stage, "/P.v", 1.0), Some(66.0));
    assert_eq!(
        *resynced.borrow(),
        vec![sdf::Path::abs_root()],
        "the asset-path channel names what may re-resolve — the whole stage here, \
         since the variables that moved are the root stack's"
    );
}

/// Explicit `assetPaths` win over a `templateAssetPath`, so a malformed
/// expression in the template nobody reads must neither drop the set nor be
/// reported: only the fields a set actually uses are evaluated.
#[test]
fn clip_ignored_template_skipped() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s070.usda", &[(1.0, 88.0)]);
    let stage = clip_scene(
        &dir,
        "s070",
        concat!(
            "            asset[] assetPaths = [@`\"./${SHOT}.usda\"`@]\n",
            "            asset templateAssetPath = @`\"./${SHOT}.#.usda\" +`@\n",
            "            double templateStartTime = 1\n",
            "            double templateEndTime = 2\n",
            "            double templateStride = 1\n",
            "            double2[] active = [(1, 0)]\n",
        ),
    );

    assert_eq!(
        value_at(&stage, "/P.v", 1.0),
        Some(88.0),
        "the explicit paths still win"
    );
    assert!(
        stage.composition_errors().is_empty(),
        "the ignored template is never evaluated: {:?}",
        stage.composition_errors()
    );
}

/// Whether a set is explicit is the strict `asset[]` read, the same one
/// `parse_set` uses to choose between explicit paths and a template. A
/// wrongly-typed `assetPaths` is unauthored to both, so the template is read —
/// and therefore must be evaluated.
#[test]
fn clip_mistyped_assets_template() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s100.1.usda", &[(1.0, 99.0)]);
    let stage = clip_scene(
        &dir,
        "s100",
        concat!(
            "            string[] assetPaths = [\"./ignored.usda\"]
",
            "            asset templateAssetPath = @`\"./${SHOT}.#.usda\"`@
",
            "            double templateStartTime = 1
",
            "            double templateEndTime = 1
",
            "            double templateStride = 1
",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), Some(99.0));
    assert!(stage.composition_errors().is_empty());
}

/// A set whose `assetPaths` is wrongly typed reads its template instead, so the
/// mistyped field is never evaluated — an expression that would not evaluate
/// there must not drop a set that never reads it.
#[test]
fn clip_mistyped_assets_unevaluated() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_clip(&dir, "s110.1.usda", &[(1.0, 111.0)]);
    let stage = clip_scene(
        &dir,
        "s110",
        concat!(
            "            asset assetPaths = @`\"./x.usda\" +`@\n",
            "            asset templateAssetPath = @`\"./${SHOT}.#.usda\"`@\n",
            "            double templateStartTime = 1\n",
            "            double templateEndTime = 1\n",
            "            double templateStride = 1\n",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), Some(111.0));
    assert!(
        stage.composition_errors().is_empty(),
        "the unread field is not evaluated: {:?}",
        stage.composition_errors()
    );
}

/// A manifest synthesized from a set's clips is memoized on the set, whose
/// identity is its authored paths — so moving the expression to different clips
/// must not reuse a manifest generated from the old ones.
#[test]
fn clip_expression_remanifests() {
    let dir = tempfile::tempdir().expect("tempdir");
    fs::write(
        dir.path().join("s120.usda"),
        "#usda 1.0\n\ndef \"P\"\n{\n    double a.timeSamples = {\n        1: 7.0,\n    }\n}\n",
    )
    .expect("write clip");
    fs::write(
        dir.path().join("s130.usda"),
        "#usda 1.0\n\ndef \"P\"\n{\n    double b.timeSamples = {\n        1: 8.0,\n    }\n}\n",
    )
    .expect("write clip");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0\n",
            "(\n",
            "    expressionVariables = { string SHOT = \"s120\" }\n",
            ")\n",
            "def \"P\" (\n",
            "    clips = {\n",
            "        dictionary default = {\n",
            "            asset[] assetPaths = [@`\"./${SHOT}.usda\"`@]\n",
            "            double2[] active = [(1, 0)]\n",
            "            string primPath = \"/P\"\n",
            "        }\n",
            "    }\n",
            ")\n",
            "{\n",
            "    double a\n",
            "    double b\n",
            "}\n",
        ),
    );
    assert_eq!(value_at(&stage, "/P.a", 1.0), Some(7.0));

    let root = stage.root_layer().identifier().to_string();
    stage
        .layer_mut(&root)
        .expect("the root layer is live")
        .edit(|e| {
            e.set_expression_variables(HashMap::from([(
                "SHOT".to_string(),
                sdf::Value::String("s130".to_string()),
            )]))
        })
        .expect("author variables");

    assert_eq!(
        value_at(&stage, "/P.b", 1.0),
        Some(8.0),
        "the manifest is regenerated from the clips the expression now names"
    );
}

/// The same malformed expression in two sets drops both. The diagnostic is
/// recorded once, so a set cannot be judged by whether it grew the error list.
#[test]
fn clip_duplicate_bad_expression() {
    let dir = tempfile::tempdir().expect("tempdir");
    let stage = open_scene(
        &dir,
        concat!(
            "#usda 1.0\n",
            "(\n",
            "    expressionVariables = { string SHOT = \"s080\" }\n",
            ")\n",
            "def \"P\" (\n",
            "    clips = {\n",
            "        dictionary a = {\n",
            "            asset[] assetPaths = [@`\"./${SHOT}.usda\" +`@]\n",
            "            double2[] active = [(1, 0)]\n",
            "            string primPath = \"/P\"\n",
            "        }\n",
            "        dictionary b = {\n",
            "            asset[] assetPaths = [@`\"./${SHOT}.usda\" +`@]\n",
            "            double2[] active = [(1, 0)]\n",
            "            string primPath = \"/P\"\n",
            "        }\n",
            "    }\n",
            ")\n",
            "{\n",
            "    double v\n",
            "}\n",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), None, "neither set contributes");
    assert!(
        !reports_unreadable_clip(&stage),
        "the second set's expression must not reach the resolver: {:?}",
        stage.composition_errors()
    );
}

/// An asset path evaluating to the expression-language `None` names no clip.
/// It is accepted silently — but the authored expression must never be handed
/// to resolution as though it were a file name.
#[test]
fn clip_expression_none_silent() {
    let dir = tempfile::tempdir().expect("tempdir");
    let stage = clip_scene(
        &dir,
        "s090",
        concat!(
            "            asset[] assetPaths = [@`None`@]\n",
            "            double2[] active = [(1, 0)]\n",
        ),
    );

    assert_eq!(value_at(&stage, "/P.v", 1.0), None, "the set names no clip");
    assert!(
        stage.composition_errors().is_empty(),
        "`None` is accepted silently, not attempted as a path: {:?}",
        stage.composition_errors()
    );
}

// Schema-declared `asset` fallbacks. A fallback is authored in a schematics
// layer that belongs to no layer stack, so the schema tier anchors it rather
// than composition — and only when the family said where it resolved from.

/// Manifest for the family declaring the concrete type `Widget`.
const WIDGET_MANIFEST: &str = r#"#usda 1.0

def "Typed"
{
    uniform token schemaKind = "abstractBase"
}

def "APISchemaBase"
{
    uniform token schemaKind = "abstractBase"
}

def "Widget"
{
    uniform token schemaKind = "concreteTyped"
    uniform token[] bases = ["Typed"]
}
"#;

/// Manifest for a second family, so a composed property's two contributors can
/// come from schematics at different locations.
const FILE_API_MANIFEST: &str = r#"#usda 1.0

def "FileAPI"
{
    uniform token schemaKind = "singleApplyAPI"
    uniform token[] bases = ["APISchemaBase"]
}
"#;

/// A resolver that echoes the anchor it was handed back into the identifier,
/// so a test can prove the registry passed a location through untouched. Its
/// identifiers are not filesystem paths, which is the point: canonicalizing one
/// would destroy it.
struct EchoAnchorResolver;

impl ar::Resolver for EchoAnchorResolver {
    fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
        match anchor {
            Some(anchor) => format!("{}|{asset_path}", anchor.to_string_lossy()),
            None => asset_path.to_string(),
        }
    }

    fn resolve(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
        Some(ar::ResolvedPath::new(asset_path))
    }

    fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
        self.resolve(asset_path)
    }

    fn open_asset(&self, _resolved_path: &ar::ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
        Err(io::Error::other("this resolver opens nothing"))
    }
}

/// Class-prim schematics declaring `Widget.inputs:file` with `default` as its
/// authored fallback.
fn widget_schematics(default: &str) -> String {
    format!("#usda 1.0\n\nclass Widget \"Widget\"\n{{\n    asset inputs:file = {default}\n}}\n")
}

/// A registry declaring the concrete type `Widget` from `schematics`, said to
/// have resolved from `location`.
fn widget_registry(schematics: &str, location: Option<&ar::ResolvedPath>) -> Arc<usd::SchemaRegistry> {
    usd::SchemaRegistry::builder()
        .family(usd::FamilySource {
            name: "widget",
            manifest: WIDGET_MANIFEST,
            schematics,
            resolved_location: location,
        })
        .expect("family registers")
        .build()
        .expect("registry builds")
}

/// A registry whose two families sit at different locations, so which one
/// anchored a composed fallback is visible in the resolved path.
fn two_family_registry(
    core_schematics: &str,
    core_location: &ar::ResolvedPath,
    ext_schematics: &str,
    ext_location: &ar::ResolvedPath,
) -> Arc<usd::SchemaRegistry> {
    usd::SchemaRegistry::builder()
        .family(usd::FamilySource {
            name: "core",
            manifest: WIDGET_MANIFEST,
            schematics: core_schematics,
            resolved_location: Some(core_location),
        })
        .expect("core registers")
        .family(usd::FamilySource {
            name: "ext",
            manifest: FILE_API_MANIFEST,
            schematics: ext_schematics,
            resolved_location: Some(ext_location),
        })
        .expect("ext registers")
        .build()
        .expect("registry builds")
}

/// An in-memory stage over `registry` holding one `Widget`, so every read of
/// `/W.inputs:file` comes from the schema alone.
fn widget_stage(registry: Arc<usd::SchemaRegistry>) -> Stage {
    widget_stage_from(Stage::builder(), registry)
}

/// [`widget_stage`] over an already-configured builder, for a stage that also
/// needs its own resolver.
fn widget_stage_from(builder: usd::StageBuilder, registry: Arc<usd::SchemaRegistry>) -> Stage {
    let stage = builder
        .schema_registry(registry)
        .in_memory("anon.usda")
        .expect("open stage");
    stage
        .define_prim("/W")
        .expect("define prim")
        .set_type_name("Widget")
        .expect("set type");
    stage
}

/// Creates `dir/<name>` and returns it with the location a family whose
/// schematics sits there registers under.
fn schema_dir(dir: &tempfile::TempDir, name: &str) -> (PathBuf, ar::ResolvedPath) {
    let schemas = dir.path().join(name);
    fs::create_dir(&schemas).expect("create schema directory");
    let location = ar::ResolvedPath::new(schemas.join("generatedSchema.usda"));
    (schemas, location)
}

/// A stage whose `Widget` class prim declares `core_property` and overrides the
/// `FileAPI` built-in that declares `inputs:file` too, with the two families
/// registered in sibling directories so the resolved path names which one the
/// value came from.
fn composed_widget(core_property: &str) -> (tempfile::TempDir, Stage) {
    let dir = tempfile::tempdir().expect("tempdir");
    let (core, core_location) = schema_dir(&dir, "core");
    let (ext, ext_location) = schema_dir(&dir, "ext");
    fs::write(core.join("core.png"), b"png").expect("write core texture");
    fs::write(core.join("ext.png"), b"png").expect("write core decoy");
    fs::write(ext.join("ext.png"), b"png").expect("write ext texture");

    let core_schematics = format!(
        r#"#usda 1.0

class Widget "Widget" (
    apiSchemas = ["FileAPI"]
    customData = {{
        token[] apiSchemaOverridePropertyNames = ["inputs:file"]
    }}
)
{{
    {core_property}
}}
"#
    );
    let ext_schematics = "#usda 1.0\n\nclass \"FileAPI\"\n{\n    asset inputs:file = @./ext.png@\n}\n";

    let registry = two_family_registry(&core_schematics, &core_location, ext_schematics, &ext_location);
    (dir, widget_stage(registry))
}

/// A stage whose `Widget.inputs:file` falls back to `default`, declared by
/// schematics registered as resolving from a `schemas` directory that holds
/// `tex.png`. The directory is returned so it outlives the stage.
fn located_widget(default: &str) -> (tempfile::TempDir, Stage) {
    let dir = tempfile::tempdir().expect("tempdir");
    let (schemas, location) = schema_dir(&dir, "schemas");
    fs::write(schemas.join("tex.png"), b"png").expect("write texture");

    let stage = widget_stage(widget_registry(&widget_schematics(default), Some(&location)));
    (dir, stage)
}

/// A family registered with no location anchors nothing, which is the position
/// C++ is always in — `UsdSchemaRegistry` opens every `generatedSchema.usda`
/// anonymously. The authored path names a file that really does exist in the
/// process working directory, so an unanchored resolve would find it.
#[test]
fn unlocated_schema_keeps_relative() {
    // Whatever the working directory happens to be, an unanchored relative path
    // resolves against it — so the fixture is a file that is really there.
    let present = fs::read_dir(".")
        .expect("the working directory is readable")
        .flatten()
        .find(|entry| entry.file_type().is_ok_and(|kind| kind.is_file()))
        .expect("the working directory holds a file to name");
    let authored = format!("./{}", present.file_name().to_string_lossy());

    let stage = widget_stage(widget_registry(&widget_schematics(&format!("@{authored}@")), None));
    let asset = asset_at(&stage, "/W.inputs:file");

    assert_eq!(asset.as_str(), authored);
    assert_eq!(asset.resolved_path(), None, "an unlocated schema anchors nothing");
}

/// The same boundary for a path that needs no anchor at all: an absolute
/// fallback from an unlocated family is still left exactly as authored.
#[test]
fn unlocated_schema_keeps_absolute() {
    let dir = tempfile::tempdir().expect("tempdir");
    let texture = dir.path().join("tex.png");
    fs::write(&texture, b"png").expect("write texture");
    let authored = texture.to_string_lossy().replace('\\', "/");

    let schematics = widget_schematics(&format!("@{authored}@"));
    let stage = widget_stage(widget_registry(&schematics, None));
    let asset = asset_at(&stage, "/W.inputs:file");

    assert_eq!(
        asset.resolved_path(),
        None,
        "an unlocated schema anchors nothing, absolute or not"
    );
}

/// An empty resolved path is how a resolver reports that it found nothing, so
/// registering one is an error rather than a location that anchors nowhere.
#[test]
fn empty_schema_location_rejected() {
    let nowhere = ar::ResolvedPath::new("");
    let registered = usd::SchemaRegistry::builder().family(usd::FamilySource {
        name: "widget",
        manifest: WIDGET_MANIFEST,
        schematics: &widget_schematics("@./tex.png@"),
        resolved_location: Some(&nowhere),
    });

    assert!(
        registered.is_err(),
        "an empty location is a failed resolution, not a location"
    );
}

/// A fallback anchors on the schematics that declared it, not on the stage's
/// root layer: both directories hold a `tex.png` and the schema's one wins.
#[test]
fn fallback_anchors_on_schema() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (schemas, location) = schema_dir(&dir, "schemas");
    fs::write(schemas.join("tex.png"), b"png").expect("write schema texture");
    fs::write(dir.path().join("tex.png"), b"png").expect("write scene texture");

    let registry = widget_registry(&widget_schematics("@./tex.png@"), Some(&location));
    let stage = open_scene_with(&dir, "#usda 1.0\n\ndef Widget \"W\"\n{\n}\n", registry);

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_resolved_under(&asset, "/schemas/tex.png", "the schematics directory");
}

/// An authored opinion still wins over the fallback, and still anchors on its
/// own layer rather than on the schema.
#[test]
fn authored_beats_schema_anchor() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (schemas, location) = schema_dir(&dir, "schemas");
    fs::write(schemas.join("tex.png"), b"png").expect("write schema texture");
    fs::write(dir.path().join("scene.png"), b"png").expect("write scene texture");

    let registry = widget_registry(&widget_schematics("@./tex.png@"), Some(&location));
    let source = "#usda 1.0\n\ndef Widget \"W\"\n{\n    asset inputs:file = @./scene.png@\n}\n";
    let stage = open_scene_with(&dir, source, registry);

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_eq!(asset.as_str(), "./scene.png");
    assert_resolved_under(&asset, "/scene.png", "the layer that authored the opinion");
}

/// The location a family was registered with reaches the resolver verbatim:
/// the registry neither canonicalizes nor re-resolves it, so a resolver whose
/// locations are not filesystem paths keeps working.
#[test]
fn schema_location_used_verbatim() {
    let location = ar::ResolvedPath::new("vault://schemas/generatedSchema.usda");
    let registry = widget_registry(&widget_schematics("@./tex.png@"), Some(&location));
    let stage = widget_stage_from(Stage::builder().resolver(EchoAnchorResolver), registry);

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_eq!(
        asset.resolved_path(),
        Some("vault://schemas/generatedSchema.usda|./tex.png"),
        "the registered location reached the resolver unchanged",
    );
}

/// A schematics inside a package anchors its fallbacks in that package, the
/// way a layer read out of one does.
#[test]
fn packaged_schema_anchors_inside() {
    let dir = tempfile::tempdir().expect("tempdir");
    let package = dir.path().join("schemas.usdz");
    {
        let mut writer = ArchiveWriter::create(&package).expect("create archive");
        writer
            .add_layer("gen/generatedSchema.usda", b"#usda 1.0\n")
            .expect("add schematics");
        writer.add_layer("gen/tex.png", b"png").expect("add texture");
        writer.finish().expect("finish archive");
    }

    let package = package.to_string_lossy().replace('\\', "/");
    let location = ar::ResolvedPath::new(format!("{package}[gen/generatedSchema.usda]"));
    let stage = widget_stage(widget_registry(&widget_schematics("@./tex.png@"), Some(&location)));

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_resolved_under(&asset, "[gen/tex.png]", "the package holding the schematics");
}

/// Every element of an `asset[]` fallback is anchored on its own terms: a
/// relative one against the schematics, an absolute one on itself, and an empty
/// one names nothing.
#[test]
fn mixed_asset_array_fallback() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (schemas, location) = schema_dir(&dir, "schemas");
    fs::write(schemas.join("near.png"), b"png").expect("write near texture");
    let far = dir.path().join("far.png");
    fs::write(&far, b"png").expect("write far texture");
    let far = far.to_string_lossy().replace('\\', "/");

    let schematics = format!(
        "#usda 1.0\n\nclass Widget \"Widget\"\n{{\n    asset[] inputs:files = [@./near.png@, @@, @{far}@]\n}}\n"
    );
    let stage = widget_stage(widget_registry(&schematics, Some(&location)));

    let values = stage
        .attribute("/W.inputs:files")
        .expect("attribute")
        .get::<sdf::Value>()
        .expect("read")
        .expect("asset array value")
        .try_as_asset_path_vec()
        .expect("the fallback is asset-array-typed");

    assert_resolved_under(&values[0], "/schemas/near.png", "the schematics directory");
    assert!(values[1].is_empty(), "the empty element stays empty");
    assert_eq!(
        values[1].resolved_path(),
        None,
        "an element naming nothing resolves to nothing"
    );
    assert_resolved_under(&values[2], "/far.png", "the absolute path it was authored with");
}

/// A located family whose fallback names a file that is not there resolves to
/// nothing — the same empty resolved path an unlocated family gives, reached by
/// a different route, so neither state can stand in for the other.
#[test]
fn located_schema_missing_asset() {
    let (_dir, stage) = located_widget("@./absent.png@");

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_eq!(asset.as_str(), "./absent.png", "the authored path is kept");
    assert_eq!(asset.resolved_path(), None, "the anchor resolved to nothing");

    // The anchoring itself still ran: a sibling that does exist resolves.
    let (_dir, stage) = located_widget("@./tex.png@");
    assert!(asset_at(&stage, "/W.inputs:file").resolved_path().is_some());
}

/// An expression in a fallback is left exactly as authored and reports nothing:
/// a schematics layer is in no layer stack, so there are no variables in scope
/// for the author to have been wrong about.
#[test]
fn expression_fallback_unevaluated() {
    let (_dir, stage) = located_widget("@`\"./${NAME}.png\"`@");

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_eq!(asset.evaluated_path(), None, "no scope means no evaluation");
    assert_eq!(
        asset.resolved_path(),
        None,
        "an unevaluated expression is not a file name"
    );
    assert!(
        expression_error_sites(&stage).is_empty(),
        "no scope means no diagnostic"
    );
}

/// A timed read reaches the fallback through the same anchoring as an untimed
/// one, so `AttributeQuery` and `Attribute` agree.
#[test]
fn fallback_asset_timed_read() {
    let (_dir, stage) = located_widget("@./tex.png@");
    let attribute = stage.attribute("/W.inputs:file").expect("attribute");

    let untimed = asset_at(&stage, "/W.inputs:file");
    let timed = usd::AttributeQuery::new(&attribute)
        .get_at::<sdf::AssetPath>(usd::TimeCode::from(0.0))
        .expect("read")
        .expect("asset value");

    assert_eq!(untimed.resolved_path(), timed.resolved_path());
    assert!(
        untimed.resolved_path().is_some(),
        "the located schema anchors both reads"
    );
}

/// A composed property anchors on the contributor that authored its `default`:
/// here the class prim's own override does, so the override's family wins over
/// the API schema it composes with.
#[test]
fn composed_default_from_override() {
    let (_dir, stage) = composed_widget("asset inputs:file = @./core.png@");

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_eq!(asset.as_str(), "./core.png", "the override supplies the value");
    assert_resolved_under(
        &asset,
        "/core/core.png",
        "the family whose override authored the default",
    );
}

/// The other direction: the class prim overrides the declaration but authors no
/// `default`, so the value — and therefore the anchor — comes from the weaker
/// API schema's own family.
#[test]
fn composed_default_from_weaker() {
    let (_dir, stage) = composed_widget("asset inputs:file");

    let asset = asset_at(&stage, "/W.inputs:file");
    assert_eq!(asset.as_str(), "./ext.png", "the API schema supplies the value");
    assert_resolved_under(&asset, "/ext/ext.png", "the family that authored the default");
}

/// The parity boundary: only the fallback *value* is anchored. The same schema
/// declaration read as metadata comes back exactly as authored, as it does in
/// C++, where a fallback metadatum is taken straight off the prim definition.
#[test]
fn schema_metadatum_stays_unanchored() {
    let (_dir, stage) = located_widget("@./tex.png@");
    let attribute = stage.attribute("/W.inputs:file").expect("attribute");

    assert!(
        asset_at(&stage, "/W.inputs:file").resolved_path().is_some(),
        "the value read is anchored",
    );

    let declared = attribute
        .get_metadata::<sdf::Value>("default")
        .expect("read metadata")
        .expect("the schema declares a default")
        .try_as_asset_path()
        .expect("the declaration is asset-typed");
    assert_eq!(
        declared.resolved_path(),
        None,
        "a schema value read as metadata is not anchored"
    );
}
