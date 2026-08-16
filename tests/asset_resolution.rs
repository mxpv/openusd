//! Value resolution anchors and resolves `asset` / `asset[]` paths against
//! the layer of the strongest opinion, populating `AssetPath::resolved_path`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::rc::Rc;

use openusd::pcp;
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
        .any(|e| matches!(e, pcp::Error::UnreadableClip { .. }))
}

/// The authored site of every reported invalid-expression diagnostic.
fn expression_error_sites(stage: &Stage) -> Vec<sdf::Path> {
    stage
        .composition_errors()
        .into_iter()
        .filter_map(|e| match e {
            pcp::Error::InvalidExpression { site_path, .. } => Some(site_path),
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
