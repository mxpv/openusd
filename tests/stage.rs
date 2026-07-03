//! Integration tests for `usd::Stage` exercised purely through its public
//! API: opening composed stages, querying composition results, value
//! resolution, prim/attribute/relationship handles, instancing, value
//! clips, and stage-tier authoring.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use anyhow::Result;
use openusd::ar::Resolver as _;
use openusd::usd::{
    CommittedChange, EditTarget, EditTargetArc, InitialLoadSet, PrimPredicate, PrimStatus, Stage, StageAuthoringError,
    StagePopulationMask, StageSink,
};
use openusd::usdz::ArchiveWriter;
use openusd::{ar, gf, pcp, sdf, tf, usd};

/// A [`StageSink`] for tests: holds optional closures for the composed-change and
/// lifecycle hooks a test cares about, recording into shared state it inspects
/// afterward.
#[derive(Default)]
#[allow(clippy::type_complexity)]
struct RecordingSink {
    after: Option<Box<dyn Fn(&Stage, &CommittedChange<'_>)>>,
    edit_target: Option<Box<dyn Fn(&Stage)>>,
    muting: Option<Box<dyn Fn(&Stage, &str, bool)>>,
}

impl StageSink for RecordingSink {
    fn after_commit(&self, stage: &Stage, change: &CommittedChange<'_>) {
        if let Some(f) = &self.after {
            f(stage, change);
        }
    }
    fn edit_target_changed(&self, stage: &Stage) {
        if let Some(f) = &self.edit_target {
            f(stage);
        }
    }
    fn layer_muting_changed(&self, stage: &Stage, layer: &str, muted: bool) {
        if let Some(f) = &self.muting {
            f(stage, layer, muted);
        }
    }
}

/// An [`sdf::LayerSink`] for tests: optional closures for the layer-tier
/// pre-commit (with veto) and post-commit hooks.
#[allow(clippy::type_complexity)]
#[derive(Default)]
struct RecordingLayerSink {
    before: Option<Box<dyn Fn(&sdf::PendingLayerChange<'_>) -> Result<(), sdf::sink::Error>>>,
    after: Option<Box<dyn Fn(&str, &sdf::ChangeList)>>,
}

impl sdf::LayerSink for RecordingLayerSink {
    fn before_commit(&self, change: &sdf::PendingLayerChange<'_>) -> Result<(), sdf::sink::Error> {
        match &self.before {
            Some(f) => f(change),
            None => Ok(()),
        }
    }
    fn after_commit(&self, layer: &str, changes: &sdf::ChangeList) {
        if let Some(f) = &self.after {
            f(layer, changes);
        }
    }
}

const VENDOR_COMPOSITION: &str = "vendor/usd-wg-assets/test_assets/foundation/stage_composition";

fn manifest_dir() -> String {
    std::env::var("CARGO_MANIFEST_DIR").unwrap()
}

fn composition_path(relative: &str) -> String {
    format!("{}/{VENDOR_COMPOSITION}/{relative}", manifest_dir())
}

fn fixture_path(relative: &str) -> String {
    format!("{}/fixtures/{relative}", manifest_dir())
}

// Composed-scene query shims used throughout these tests: each routes
// through the handle that now owns the query so the assertions stay terse.
fn child_names(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
    Ok(stage.prim(path).child_names()?.into_iter().map(String::from).collect())
}

fn prop_names(stage: &Stage, path: impl Into<sdf::Path>) -> Result<Vec<String>> {
    Ok(stage
        .prim(path)
        .property_names()?
        .into_iter()
        .map(String::from)
        .collect())
}

fn connections(stage: &Stage, attr: &sdf::Path) -> Result<Vec<sdf::Path>> {
    stage.attribute(attr).connections()
}

fn rel_targets(stage: &Stage, rel: &sdf::Path) -> Result<Vec<sdf::Path>> {
    stage.relationship(rel).targets()
}

fn fwd_targets(stage: &Stage, rel: &sdf::Path) -> Result<Vec<sdf::Path>> {
    stage.relationship(rel).forwarded_targets()
}

/// Number of `UnresolvedSublayer` collection diagnostics the stage reports for
/// `asset_path` — the assertion the muted-diagnostic tests share.
fn unresolved_sublayer_count(stage: &Stage, asset_path: &str) -> usize {
    stage
        .composition_errors()
        .iter()
        .filter(|e| matches!(e, pcp::Error::UnresolvedSublayer { asset_path: a, .. } if a == asset_path))
        .count()
}

/// Whether the stage reports an `UnresolvedSublayer` for `asset_path`.
fn reports_unresolved_sublayer(stage: &Stage, asset_path: &str) -> bool {
    unresolved_sublayer_count(stage, asset_path) > 0
}

// --- Basic stage opening (vendor/usd-wg-assets) ---

#[test]
fn missing_sublayer_retained() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n)\ndef \"Root\" {}\n",
    )?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(stage.composition_errors().iter().any(|error| matches!(
        error,
        pcp::Error::UnresolvedSublayer {
            asset_path,
            introduced_by,
        } if asset_path == "missing.usda" && introduced_by.ends_with("root.usda")
    )));
    assert!(stage.prim("/Root").is_valid()?);
    Ok(())
}

/// A missing sublayer under a muted branch raises no diagnostic: the muted layer
/// and its whole subtree contribute nothing to composition, so its absent
/// descendants are not stage errors. The same missing sublayer that surfaces as
/// `UnresolvedSublayer` without the mute is filtered out with it.
#[test]
fn muted_branch_suppresses_missing() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let muted = dir.path().join("muted.usda");
    // `root` sublayers `muted`, which in turn sublayers a file that does not exist.
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@muted.usda@]\n)\n")?;
    std::fs::write(&muted, "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n)\n")?;
    let root_path = root.to_str().unwrap();

    // Without muting, the missing sublayer under `muted` is reported.
    let plain = Stage::open(root_path)?;
    assert!(
        reports_unresolved_sublayer(&plain, "missing.usda"),
        "an unmuted missing sublayer must be reported, got {:?}",
        plain.composition_errors()
    );

    // Muting `muted.usda` prunes its subtree, so its missing sublayer is silent.
    let muted_stage = Stage::builder().mute(["muted.usda"]).open(root_path)?;
    assert!(
        !reports_unresolved_sublayer(&muted_stage, "missing.usda"),
        "a missing sublayer under a muted branch must raise no diagnostic, got {:?}",
        muted_stage.composition_errors()
    );
    Ok(())
}

/// Muting a layer that is itself a missing sublayer suppresses its
/// `UnresolvedSublayer` diagnostic — a muted layer contributes nothing whether it
/// resolves or not, so its absence is not reported.
#[test]
fn muted_missing_sublayer_suppressed() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@gone.usda@]\n)\n")?;
    let root_path = root.to_str().unwrap();

    let plain = Stage::open(root_path)?;
    assert!(
        reports_unresolved_sublayer(&plain, "gone.usda"),
        "an unmuted missing sublayer is reported"
    );

    let muted = Stage::builder().mute(["gone.usda"]).open(root_path)?;
    assert!(
        !reports_unresolved_sublayer(&muted, "gone.usda"),
        "muting the missing sublayer suppresses its diagnostic, got {:?}",
        muted.composition_errors()
    );
    Ok(())
}

/// A missing sublayer reached through both a muted and an unmuted branch of one
/// stack is still reported. The muted branch is declared (and loaded) first, but
/// the diagnostic decision is made from the graph's reachability, not the load
/// order, so the unmuted branch that genuinely needs it keeps its
/// `UnresolvedSublayer`.
#[test]
fn muted_diamond_keeps_active() -> Result<()> {
    let dir = tempfile::tempdir()?;
    // `root` sublayers `muted` (declared first, so walked first) then `active`;
    // both sublayer the same missing layer.
    std::fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\n(\n    subLayers = [@muted.usda@, @active.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("muted.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared_missing.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("active.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared_missing.usda@]\n)\n",
    )?;
    let root_path = dir.path().join("root.usda");
    let root_path = root_path.to_str().unwrap();

    // With `muted.usda` muted, its reference to the missing layer is suppressed,
    // but `active.usda` still contributes it, so the diagnostic must survive.
    let stage = Stage::builder().mute(["muted.usda"]).open(root_path)?;
    assert_eq!(
        unresolved_sublayer_count(&stage, "shared_missing.usda"),
        1,
        "the unmuted branch's missing sublayer must be reported exactly once, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A *readable, shared* layer reached through both a muted and an unmuted branch
/// keeps the diagnostics for its own missing descendants. `shared` loads once
/// (deduplicated by identity), and its missing sublayer is reported because
/// `shared` is reachable through the unmuted `active` branch, regardless of which
/// branch reaches it first.
#[test]
fn muted_diamond_keeps_descendant() -> Result<()> {
    let dir = tempfile::tempdir()?;
    // Both `muted` (walked first) and `active` sublayer the same readable `shared`
    // layer, which in turn sublayers a missing one.
    std::fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\n(\n    subLayers = [@muted.usda@, @active.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("muted.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("active.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("shared.usda"),
        "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n)\n",
    )?;
    let root_path = dir.path().join("root.usda");
    let root_path = root_path.to_str().unwrap();

    let stage = Stage::builder().mute(["muted.usda"]).open(root_path)?;
    assert!(
        reports_unresolved_sublayer(&stage, "missing.usda"),
        "the shared layer is reachable through the unmuted branch, so its missing sublayer must be reported, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// Muting a branch suppresses its missing-sublayer diagnostic and unmuting
/// restores it. The loader records the raw diagnostic once; filtering happens at
/// report time against the current composed state, so the one-shot error is never
/// discarded and reappears when the branch rejoins composition.
#[test]
fn unmute_restores_diagnostic() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\n(\n    subLayers = [@muted.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("muted.usda"),
        "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n)\n",
    )?;
    let root_path = dir.path().join("root.usda");
    let root_path = root_path.to_str().unwrap();

    let stage = Stage::builder().mute(["muted.usda"]).open(root_path)?;
    assert!(
        !reports_unresolved_sublayer(&stage, "missing.usda"),
        "while muted the missing sublayer must be silent, got {:?}",
        stage.composition_errors()
    );

    stage.unmute_layer("muted.usda");
    assert!(
        reports_unresolved_sublayer(&stage, "missing.usda"),
        "unmuting the branch must restore its missing-sublayer diagnostic, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// `composition_errors()` does not flicker with cache warmth: a reference
/// target's missing-sublayer diagnostic stays reported after an unrelated mute
/// evicts the prim index that first reached the target. The effective set is the
/// composed stacks, not the currently-cached indices, so an eviction cannot hide a
/// valid diagnostic. (Muting the arc's own authoring layer likewise keeps the
/// diagnostic — a deliberate conservative over-report; see the pcp "Muted sublayer
/// diagnostics" remaining-work note.)
#[test]
fn muted_diagnostic_survives_eviction() -> Result<()> {
    let dir = tempfile::tempdir()?;
    // `/A` references `target` (which has a missing sublayer); the unrelated
    // sublayer `s` also contributes an opinion to `/A`, so muting `s` evicts `/A`'s
    // index without touching the `/A -> target` arc authored in the root.
    std::fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\n(\n    subLayers = [@s.usda@]\n)\ndef \"A\" (\n    references = @target.usda@\n) {}\n",
    )?;
    std::fs::write(
        dir.path().join("s.usda"),
        "#usda 1.0\nover \"A\" {\n    custom int x = 1\n}\n",
    )?;
    std::fs::write(
        dir.path().join("target.usda"),
        "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n    defaultPrim = \"T\"\n)\ndef \"T\" {}\n",
    )?;
    let root_path = dir.path().join("root.usda");
    let root_path = root_path.to_str().unwrap();

    let stage = Stage::open(root_path)?;
    let _ = child_names(&stage, "/A")?;
    assert!(
        reports_unresolved_sublayer(&stage, "missing.usda"),
        "the reached target's missing sublayer is reported"
    );

    // Muting the unrelated `s` evicts `/A`'s cached index; the diagnostic must not
    // vanish with the eviction.
    stage.mute_layer("s.usda");
    assert!(
        reports_unresolved_sublayer(&stage, "missing.usda"),
        "an unrelated mute evicting the cached index must not hide the diagnostic, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// Muting a reference target that has already loaded suppresses the target's own
/// missing-sublayer diagnostic: the muted target root resolves to an empty stack,
/// so it drops out of the composed-stack effective set and no longer counts as an
/// effective referrer.
#[test]
fn mute_loaded_target_suppresses() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\ndef \"A\" (\n    references = @target.usda@\n) {}\n",
    )?;
    std::fs::write(
        dir.path().join("target.usda"),
        "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n    defaultPrim = \"T\"\n)\ndef \"T\" {}\n",
    )?;
    let root_path = dir.path().join("root.usda");
    let root_path = root_path.to_str().unwrap();

    let stage = Stage::open(root_path)?;
    // Composing `/A` loads the target and records its missing sublayer.
    let _ = child_names(&stage, "/A")?;
    assert!(
        reports_unresolved_sublayer(&stage, "missing.usda"),
        "the loaded target's missing sublayer is reported"
    );

    stage.mute_layer("target.usda");
    // Recompose `/A` so it records the now-muted target as an external target.
    let _ = child_names(&stage, "/A")?;
    assert!(
        !reports_unresolved_sublayer(&stage, "missing.usda"),
        "muting the target suppresses its own sublayer diagnostic, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A layer that authors the same missing sublayer twice reports it once. The
/// loader deduplicates failures per referrer, so a duplicate `subLayers` entry
/// does not double the diagnostic — while a genuinely separate referrer still
/// reports its own (see `muted_diamond_keeps_active`).
#[test]
fn duplicate_missing_reported_once() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("root.usda"),
        "#usda 1.0\n(\n    subLayers = [@missing.usda@, @missing.usda@]\n)\n",
    )?;
    let stage = Stage::open(dir.path().join("root.usda").to_str().unwrap())?;
    assert_eq!(
        unresolved_sublayer_count(&stage, "missing.usda"),
        1,
        "a duplicate missing sublayer is reported once, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A missing sublayer of a reference target opened on demand surfaces the same
/// `UnresolvedSublayer` diagnostic as a missing root sublayer: composition reaches
/// the target lazily, so the load barrier records it. The target still loads, so
/// the reference composes (`/P.x` resolves).
#[test]
fn lazy_ref_missing_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let target = dir.path().join("target.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @target.usda@\n) {}\n")?;
    std::fs::write(
        &target,
        "#usda 1.0\n(\n    subLayers = [@missing.usda@]\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    custom double x = 1\n}\n",
    )?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0)),
        "the reference target loads despite its missing sublayer"
    );
    assert!(
        stage.composition_errors().iter().any(|error| matches!(
            error,
            pcp::Error::UnresolvedSublayer { asset_path, introduced_by }
                if asset_path == "missing.usda" && introduced_by.ends_with("target.usda")
        )),
        "expected UnresolvedSublayer, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A reference target that resolves but cannot be parsed is reported
/// `MalformedLayer` (carrying the parse error) rather than silently dropped, and
/// composition still completes — the demanding prim composes without the arc
/// instead of looping on the unreadable target.
#[test]
fn lazy_ref_unreadable_target() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let target = dir.path().join("broken.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @broken.usda@\n) {}\n")?;
    // Resolves (the file exists) but the parser rejects the body.
    std::fs::write(&target, "#usda 1.0\ndef Broken {{{ not valid\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(stage.prim("/P").is_valid()?, "/P still composes without the arc");
    assert!(
        stage.composition_errors().iter().any(|error| matches!(
            error,
            pcp::Error::MalformedLayer { asset_path, reason, .. }
                if asset_path.contains("broken.usda") && !reason.is_empty()
        )),
        "expected MalformedLayer carrying the parse error, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A reference target that failed to read on first demand is retried after an
/// edit clears the recorded failure, so a repaired asset composes.
#[test]
fn failed_load_retried_after_edit() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let target = dir.path().join("target.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @target.usda@\n) {}\n")?;
    std::fs::write(&target, "#usda 1.0\ndef Broken {{{ not valid\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(stage.prim("/P").is_valid()?);
    assert!(
        stage.composition_errors().iter().any(|e| matches!(
            e,
            pcp::Error::MalformedLayer { asset_path, .. } if asset_path.contains("target.usda")
        )),
        "the unreadable target is reported malformed"
    );

    // Repair the file, then author an unrelated prim: the edit clears the recorded
    // failure so the next query re-demands the now-readable target.
    std::fs::write(
        &target,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    custom double x = 7\n}\n",
    )?;
    stage.define_prim("/Trigger")?;

    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0)),
        "the repaired reference composes once the failure is cleared"
    );
    Ok(())
}

/// A cold direct query into a descendant of an instanceable reference (no prior
/// traversal) composes through the prototype, not an empty namespace: the
/// instance-proxy redirect is not memoized while the reference layer is still
/// being demanded.
#[test]
fn instance_proxy_cold_query() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let proto = dir.path().join("proto.usda");
    std::fs::write(
        &root,
        "#usda 1.0\ndef \"World\" {\n    def \"Inst\" (\n        instanceable = true\n        references = @proto.usda@\n    ) {}\n}\n",
    )?;
    std::fs::write(
        &proto,
        "#usda 1.0\n(\n    defaultPrim = \"Proto\"\n)\ndef \"Proto\" {\n    def \"Child\" {\n        custom double x = 3\n    }\n}\n",
    )?;

    let stage = Stage::open(root.to_str().unwrap())?;
    // The first query is the descendant read; it must demand proto.usda, compose
    // the instance, and resolve through the prototype rather than memoizing an
    // identity redirect against the not-yet-loaded reference.
    assert_eq!(
        stage
            .attribute("/World/Inst/Child.x")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(3.0))
    );
    Ok(())
}

/// A reference target's `subLayers` expression resolves against the *referencing*
/// layer stack's variables: the root sets `${V}` but the target only authors the
/// expression, so the on-demand load must carry the referrer's composed
/// expression variables into the target's sublayer evaluation (the closer-to-root
/// referrer wins). Without them `${V}` is unresolved and the sublayer never loads.
#[test]
fn lazy_ref_inherited_expr_var() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("prod"))?;
    let root = dir.path().join("root.usda");
    let target = dir.path().join("target.usda");
    let over = dir.path().join("prod").join("over.usda");
    std::fs::write(
        &root,
        "#usda 1.0\n(\n    expressionVariables = { string V = \"prod\" }\n)\ndef \"P\" (\n    references = @target.usda@\n) {}\n",
    )?;
    std::fs::write(
        &target,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n    subLayers = [@`\"${V}/over.usda\"`@]\n)\ndef \"P\" {}\n",
    )?;
    std::fs::write(&over, "#usda 1.0\ndef \"P\" {\n    custom double x = 9\n}\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(9.0)),
        "the target's `${{V}}` sublayer resolves against the referrer's variable"
    );
    Ok(())
}

/// A root-layer `subLayers` expression composes the layer it names: the
/// expression resolves against the root layer's own `expressionVariables`, so the
/// sublayer edge forms and its prims contribute (the demand path is exercised by
/// [`lazy_ref_inherited_expr_var`]; this covers the root-stack build).
#[test]
fn expr_sublayer_composes() -> Result<()> {
    let stage = Stage::open(&fixture_path("expr_sublayer.usda"))?;
    assert_eq!(stage.layer_count(), 2, "root + the expression-resolved sublayer");
    assert_eq!(
        stage.root_prims()?.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        ["World"],
        "the expression sublayer's prim composes onto the stage"
    );
    Ok(())
}

/// A `${VAR}` sublayer resolves against a variable authored on an *intermediate*
/// sublayer ancestor — neither the layer that authors the expression nor the
/// root. The root sublayers `a`; `a` defines `V` and sublayers `b`; `b`'s `${V}`
/// sublayer must compose against `a`'s value, threaded down from the intermediate
/// layer.
#[test]
fn intermediate_expr_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let a = dir.path().join("a.usda");
    let b = dir.path().join("b.usda");
    let leaf = dir.path().join("leaf.usda");
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@a.usda@]\n)\n")?;
    std::fs::write(
        &a,
        "#usda 1.0\n(\n    expressionVariables = { string V = \"leaf\" }\n    subLayers = [@b.usda@]\n)\n",
    )?;
    std::fs::write(&b, "#usda 1.0\n(\n    subLayers = [@`\"${V}.usda\"`@]\n)\n")?;
    std::fs::write(&leaf, "#usda 1.0\ndef \"P\" {\n    custom double x = 7\n}\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0)),
        "the intermediate layer's variable resolves the deeper expression sublayer"
    );
    Ok(())
}

/// A reference target's `${VAR}` sublayer resolves against a variable authored on
/// a *non-root* referencing layer. The root references `mid`; `mid` defines `V`
/// and references `target`; `target`'s `${V}` sublayer must resolve against
/// `mid`'s value — the variable is on neither `target` nor the root, so the
/// referrer's composed variables carried across the arc are what resolve it.
#[test]
fn cross_ref_expr_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let mid = dir.path().join("mid.usda");
    let target = dir.path().join("target.usda");
    let over = dir.path().join("over.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @mid.usda@\n) {}\n")?;
    std::fs::write(
        &mid,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n    expressionVariables = { string V = \"over\" }\n)\ndef \"P\" (\n    references = @target.usda@\n) {}\n",
    )?;
    std::fs::write(
        &target,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n    subLayers = [@`\"${V}.usda\"`@]\n)\ndef \"P\" {}\n",
    )?;
    std::fs::write(&over, "#usda 1.0\ndef \"P\" {\n    custom double x = 9\n}\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(9.0)),
        "the referrer's variable resolves the target's `${{V}}` sublayer"
    );
    Ok(())
}

/// A reference authored inside a `.usdz` package targets a sibling layer in the
/// same archive: it resolves package-relative (not against the host
/// filesystem), so the sibling's opinion composes onto the prim and no
/// composition error is reported.
#[test]
fn lazy_ref_inside_usdz_resolves() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let package = dir.path().join("package.usdz");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @package.usdz@\n) {}\n")?;
    // The package's first (root) layer references a sibling layer inside the
    // same archive, which authors an opinion on the prim.
    {
        let mut writer = ArchiveWriter::create(&package)?;
        writer.add_layer(
            "scene.usda",
            b"#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" (\n    references = @other.usda@\n) {}\n",
        )?;
        writer.add_layer(
            "other.usda",
            b"#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    custom int probe = 7\n}\n",
        )?;
        writer.finish()?;
    }

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(stage.prim("/P").is_valid()?, "/P composes from the package");
    assert!(
        stage.composition_errors().is_empty(),
        "the in-package reference should resolve cleanly, got {:?}",
        stage.composition_errors()
    );
    assert_eq!(
        stage
            .attribute("/P.probe")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Int(7)),
        "the sibling layer's opinion composes through the in-package reference"
    );
    Ok(())
}

/// A reference authored inside a `.usdz` package targets a sibling layer that
/// is not present in the archive: the missing entry is unresolved (not merely
/// unreadable), so composition reports
/// [`UnresolvedLayer`](pcp::Error::UnresolvedLayer) and the rest of the prim
/// still composes.
#[test]
fn lazy_ref_inside_usdz_missing() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let package = dir.path().join("package.usdz");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @package.usdz@\n) {}\n")?;
    // The package's first layer references a sibling that is never added.
    {
        let mut writer = ArchiveWriter::create(&package)?;
        writer.add_layer(
            "scene.usda",
            b"#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" (\n    references = @other.usda@\n) {}\n",
        )?;
        writer.finish()?;
    }

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(stage.prim("/P").is_valid()?, "/P still composes from the package layer");
    assert!(
        stage.composition_errors().iter().any(|error| matches!(
            error,
            pcp::Error::UnresolvedLayer { asset_path, .. } if asset_path.ends_with("other.usda]")
        )),
        "expected UnresolvedLayer for the missing in-package target, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A reference to a present-but-empty `.usdz` (no packaged USD layer) reports a
/// [`MalformedLayer`](pcp::Error::MalformedLayer) carrying the real reason —
/// the package resolved but could not be read — rather than being silently
/// dropped as a missing asset or surfacing a "failed to resolve" diagnostic.
#[test]
fn lazy_ref_empty_usdz_malformed() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let package = dir.path().join("empty.usdz");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @empty.usdz@\n) {}\n")?;
    // A valid ZIP archive with no packaged USD layer.
    ArchiveWriter::create(&package)?.finish()?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(stage.prim("/P").is_valid()?, "/P still composes from its own opinion");
    assert!(
        stage.composition_errors().iter().any(|error| matches!(
            error,
            pcp::Error::MalformedLayer { asset_path, reason, .. }
                if asset_path.ends_with("empty.usdz") && reason.contains("USDZ archive")
        )),
        "expected MalformedLayer with the package read reason, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A `.usdz` whose default (first) layer sits in a sub-directory references a
/// sibling by a relative path. The reference must anchor against the package's
/// real path (the package-relative default layer,
/// `pkg.usdz[Scenes/root.usda]`),
/// not the bare package identifier, so the sibling resolves at
/// `pkg.usdz[Scenes/other.usda]` and its opinion composes.
#[test]
fn usdz_subdir_first_layer_anchors() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let package = dir.path().join("package.usdz");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @package.usdz@\n) {}\n")?;
    // Both packaged layers live under `Scenes/`; the first is the default layer.
    {
        let mut writer = ArchiveWriter::create(&package)?;
        writer.add_layer(
            "Scenes/root.usda",
            b"#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" (\n    references = @other.usda@\n) {}\n",
        )?;
        writer.add_layer(
            "Scenes/other.usda",
            b"#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    custom int probe = 9\n}\n",
        )?;
        writer.finish()?;
    }

    let stage = Stage::open(root.to_str().unwrap())?;
    assert!(
        stage.composition_errors().is_empty(),
        "the sub-directory in-package reference should resolve cleanly, got {:?}",
        stage.composition_errors()
    );
    assert_eq!(
        stage
            .attribute("/P.probe")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Int(9)),
        "the sibling under Scenes/ composes through the in-package reference"
    );
    Ok(())
}

/// An `asset`-valued attribute pointing at a `.usdz` package resolves to the
/// package path itself, not a path anchored into the package's first layer:
/// the asset is the package, and consumers key on the package path.
#[test]
fn asset_value_usdz_is_package_path() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let package = dir.path().join("model.usdz");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" {\n    custom asset a = @model.usdz@\n}\n")?;
    {
        let mut writer = ArchiveWriter::create(&package)?;
        writer.add_layer("root.usda", b"#usda 1.0\ndef \"M\" {}\n")?;
        writer.finish()?;
    }

    let stage = Stage::open(root.to_str().unwrap())?;
    let value = stage
        .attribute("/P.a")
        .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?
        .expect("asset value resolves");
    let asset = value.try_as_asset_path().expect("attribute is asset-typed");
    let resolved = asset.resolved_path().expect("asset path is resolved");
    assert!(
        resolved.ends_with("model.usdz"),
        "asset value should resolve to the bare package path, got {resolved:?}",
    );
    assert!(
        !resolved.contains('['),
        "asset value must not be anchored into the package, got {resolved:?}",
    );
    Ok(())
}

/// A reference target's present-but-corrupt sublayer is dropped on its own —
/// reported [`MalformedSublayer`](pcp::Error::MalformedSublayer) — while the
/// target itself still composes (its own opinion resolves). The bad sublayer
/// must not fail the whole reference target.
#[test]
fn lazy_ref_corrupt_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let target = dir.path().join("target.usda");
    let broken = dir.path().join("broken.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @target.usda@\n) {}\n")?;
    std::fs::write(
        &target,
        "#usda 1.0\n(\n    subLayers = [@broken.usda@]\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    custom double x = 1\n}\n",
    )?;
    // Resolves (the file exists) but the parser rejects the body.
    std::fs::write(&broken, "#usda 1.0\ndef Broken {{{ not valid\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0)),
        "the target composes despite its corrupt sublayer"
    );
    assert!(
        stage.composition_errors().iter().any(|error| matches!(
            error,
            pcp::Error::MalformedSublayer { asset_path, introduced_by, reason }
                if asset_path == "broken.usda" && introduced_by.ends_with("target.usda") && !reason.is_empty()
        )),
        "expected MalformedSublayer carrying the parse error, got {:?}",
        stage.composition_errors()
    );
    Ok(())
}

/// A not-yet-loaded reference target under a nested referrer is muted by the
/// path that resolves, from the stage root, to its canonical identifier (C++
/// `Pcp_MutedLayers`): the model under `sub/` is muted as `"sub/model.usda"` and
/// never opened.
#[test]
fn mute_nested_reference_target() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("sub"))?;
    let root = dir.path().join("root.usda");
    let mid = dir.path().join("sub").join("mid.usda");
    let model = dir.path().join("sub").join("model.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @sub/mid.usda@\n) {}\n")?;
    std::fs::write(
        &mid,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" (\n    references = @model.usda@\n) {}\n",
    )?;
    std::fs::write(
        &model,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    custom double x = 1\n}\n",
    )?;

    let opened = Rc::new(RefCell::new(Vec::new()));
    let stage = Stage::builder()
        .resolver(RecordingResolver::new(opened.clone()))
        .mute(["sub/model.usda"])
        .open(root.to_str().unwrap())?;

    // Compose /P, following the nested reference to mid.usda and reaching the
    // muted model reference; its identifier matches the muted one, so it is
    // recognized at the demand point and never read.
    assert!(stage.prim("/P").is_valid()?);
    let opened_has = |needle: &str| opened.borrow().iter().any(|p| p.contains(needle));
    assert!(opened_has("mid.usda"), "the nested referrer must load");
    assert!(
        !opened_has("model.usda"),
        "the muted nested target must never be opened, got {:?}",
        opened.borrow()
    );
    Ok(())
}

/// The arc's authoring layer is consulted, not only the root: a reference
/// authored in `detail/extra.usda` (a sublayer of the referenced `target.usda`)
/// resolves `@model.usda@` under `detail/`, so muting `"detail/model.usda"` — the
/// path resolving from the root to that target's canonical identifier — mutes it.
#[test]
fn mute_target_under_nested_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("detail"))?;
    let root = dir.path().join("root.usda");
    let target = dir.path().join("target.usda");
    let extra = dir.path().join("detail").join("extra.usda");
    let model = dir.path().join("detail").join("model.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @target.usda@\n) {}\n")?;
    // target.usda sublayers a layer in detail/, which authors the relative model
    // reference — so the arc's authoring layer is not the stack's root layer.
    std::fs::write(
        &target,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n    subLayers = [@detail/extra.usda@]\n)\ndef \"P\" {}\n",
    )?;
    std::fs::write(&extra, "#usda 1.0\ndef \"P\" (\n    references = @model.usda@\n) {}\n")?;
    std::fs::write(
        &model,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n)\ndef \"P\" {\n    custom double x = 1\n}\n",
    )?;

    let opened = Rc::new(RefCell::new(Vec::new()));
    let stage = Stage::builder()
        .resolver(RecordingResolver::new(opened.clone()))
        .mute(["detail/model.usda"])
        .open(root.to_str().unwrap())?;

    assert!(stage.prim("/P").is_valid()?);
    let opened_has = |needle: &str| opened.borrow().iter().any(|p| p.contains(needle));
    assert!(opened_has("extra.usda"), "the authoring sublayer must load");
    assert!(
        !opened_has("model.usda"),
        "the muted target under the nested sublayer must not be opened, got {:?}",
        opened.borrow()
    );
    Ok(())
}

/// Muting keys on the canonical identifier: a layer muted by a relative spelling
/// is the same entry as its absolute spelling, so re-muting the absolute is a
/// no-op, both spellings read as muted, and unmuting through either fully restores
/// it — and every notice carries the canonical identifier, whatever spelling was
/// passed, so a listener mirroring the muted set by identifier stays in sync.
#[test]
fn mute_alternate_spelling() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let weak = dir.path().join("weak.usda");
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@weak.usda@]\n)\ndef \"P\" {}\n")?;
    std::fs::write(&weak, "#usda 1.0\ndef \"P\" {\n    custom double x = 1\n}\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    let abs = weak.to_str().unwrap();
    // The identifier both spellings resolve to (what muting stores and notifies).
    let canonical = ar::DefaultResolver::new().create_identifier(abs, None);
    let read_x = || stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0));

    let muted = Rc::new(RefCell::new(Vec::<String>::new()));
    let unmuted = Rc::new(RefCell::new(Vec::<String>::new()));
    let _token = {
        let (muted, unmuted) = (muted.clone(), unmuted.clone());
        stage.add_sink(RecordingSink {
            muting: Some(Box::new(move |_stage, layer, is_muted| {
                if is_muted {
                    muted.borrow_mut().push(layer.to_string());
                } else {
                    unmuted.borrow_mut().push(layer.to_string());
                }
            })),
            ..Default::default()
        })
    };

    assert_eq!(
        read_x()?,
        Some(sdf::Value::Double(1.0)),
        "weak contributes x until muted"
    );

    // Mute by the relative spelling, then the absolute spelling names the same
    // canonical identifier, so re-muting it is a no-op.
    stage.mute_layer("weak.usda");
    assert!(
        stage.is_layer_muted(abs),
        "the absolute spelling reads the same muted layer"
    );
    stage.mute_layer(abs);
    assert_eq!(
        stage.muted_layers(),
        vec![canonical.clone()],
        "both spellings are one canonical entry"
    );
    assert_eq!(read_x()?, None, "the muted weak layer contributes nothing");

    // Unmute through the other spelling; the layer is fully restored.
    stage.unmute_layer(abs);
    assert!(
        !stage.is_layer_muted("weak.usda"),
        "unmuting any spelling unmutes the layer"
    );
    assert!(stage.muted_layers().is_empty());
    assert_eq!(
        read_x()?,
        Some(sdf::Value::Double(1.0)),
        "the unmuted weak layer contributes again"
    );

    // One notice each, both carrying the canonical identifier (not the spelling
    // passed): the redundant mute fired nothing.
    assert_eq!(*muted.borrow(), vec![canonical.clone()]);
    assert_eq!(*unmuted.borrow(), vec![canonical]);
    Ok(())
}

/// Open-time muting dedups co-resolving spellings the same way the runtime path
/// does: seeding one loaded layer under both a relative and an absolute spelling
/// lists it once and mutes it.
#[test]
fn mute_open_dedup() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let weak = dir.path().join("weak.usda");
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@weak.usda@]\n)\ndef \"P\" {}\n")?;
    std::fs::write(&weak, "#usda 1.0\ndef \"P\" {\n    custom double x = 1\n}\n")?;
    let abs = weak.to_str().unwrap();

    let stage = Stage::builder().mute(["weak.usda", abs]).open(root.to_str().unwrap())?;
    assert_eq!(
        stage.muted_layers().len(),
        1,
        "two spellings of one loaded layer seed a single mute, got {:?}",
        stage.muted_layers()
    );
    assert!(stage.is_layer_muted("weak.usda") && stage.is_layer_muted(abs));
    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None,
        "the muted weak layer contributes nothing"
    );
    Ok(())
}

/// A nested sublayer is muted by the path that resolves, from the stage root, to
/// its canonical identifier: `sub/weak.usda` drops from the stack and unmutes
/// through its absolute spelling (the same identifier).
#[test]
fn mute_nested_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("sub"))?;
    let root = dir.path().join("root.usda");
    let mid = dir.path().join("sub").join("mid.usda");
    let weak = dir.path().join("sub").join("weak.usda");
    std::fs::write(
        &root,
        "#usda 1.0\n(\n    subLayers = [@sub/mid.usda@]\n)\ndef \"P\" {}\n",
    )?;
    std::fs::write(&mid, "#usda 1.0\n(\n    subLayers = [@weak.usda@]\n)\n")?;
    std::fs::write(&weak, "#usda 1.0\ndef \"P\" {\n    custom double x = 1\n}\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    let abs = weak.to_str().unwrap();
    let read_x = || stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0));
    assert_eq!(
        read_x()?,
        Some(sdf::Value::Double(1.0)),
        "the nested sublayer contributes x"
    );

    // Mute by the root-relative path; `weak.usda` lives under `sub/`.
    stage.mute_layer("sub/weak.usda");
    assert!(
        stage.is_layer_muted(abs),
        "the muted nested layer reads as muted by absolute path"
    );
    assert_eq!(read_x()?, None, "the muted nested sublayer drops from the stack");

    stage.unmute_layer(abs);
    assert!(
        !stage.is_layer_muted("sub/weak.usda"),
        "unmuting by an alternate spelling unmutes it"
    );
    assert_eq!(
        read_x()?,
        Some(sdf::Value::Double(1.0)),
        "the unmuted nested sublayer contributes again"
    );
    Ok(())
}

/// An unevaluable expression `subLayers` entry drops only that sublayer: the
/// reference target still composes its own opinions and its valid sublayer,
/// rather than the bad expression failing the whole target load.
#[test]
fn bad_expr_sublayer_dropped() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let target = dir.path().join("target.usda");
    let over = dir.path().join("over.usda");
    std::fs::write(&root, "#usda 1.0\ndef \"P\" (\n    references = @target.usda@\n) {}\n")?;
    // The second sublayer uses an undefined expression variable; the first is valid.
    std::fs::write(
        &target,
        "#usda 1.0\n(\n    defaultPrim = \"P\"\n    subLayers = [@over.usda@, @`\"${UNDEFINED}.usda\"`@]\n)\ndef \"P\" {\n    custom double x = 1\n}\n",
    )?;
    std::fs::write(&over, "#usda 1.0\ndef \"P\" {\n    custom double y = 2\n}\n")?;

    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/P.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0)),
        "the target's own opinion composes despite the bad expression sublayer"
    );
    assert_eq!(
        stage.attribute("/P.y").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(2.0)),
        "the valid sublayer still composes"
    );
    assert!(
        !stage.composition_errors().is_empty(),
        "the dropped expression sublayer is reported"
    );
    Ok(())
}

/// A single-layer .usda file should load with correct defaultPrim and
/// root prim list.
#[test]
fn open_single_layer() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    assert_eq!(stage.layer_count(), 1);
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    assert_eq!(
        stage.root_prims()?.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        ["World"]
    );

    Ok(())
}

/// Default traversal should visit active, loaded, defined, non-abstract prims.
#[test]
fn traverse_uses_default_predicate() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;

    assert_eq!(prims, vec!["/World", "/World/CubeActive"]);

    Ok(())
}

/// Exhaustive traversal should preserve raw composed hierarchy traversal.
#[test]
fn traverse_all_visits_every_composed_prim() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

    assert_eq!(prims, vec!["/World", "/World/CubeInactive", "/World/CubeActive"]);

    Ok(())
}

/// A prim defined only in the stronger sublayer should appear in composed
/// children alongside prims from the weaker layer.
#[test]
fn sublayer_children_union() -> Result<()> {
    let path = fixture_path("sublayer_override.usda");
    let stage = Stage::open(&path)?;

    let children = child_names(&stage, "/World")?;
    // Override layer adds Sphere; base layer defines Cube.
    assert!(children.contains(&"Cube".to_string()), "Cube from base layer");
    assert!(children.contains(&"Sphere".to_string()), "Sphere from override layer");

    Ok(())
}

/// The sublayer_same_folder vendor test asset should open correctly with
/// 2 layers and expose the sublayer's prims through composition.
#[test]
fn sublayer_prims_from_weaker_layer() -> Result<()> {
    let path = composition_path("subLayer/sublayer_same_folder.usda");
    let stage = Stage::open(&path)?;

    assert_eq!(stage.layer_count(), 2);
    assert_eq!(stage.default_prim().as_deref(), Some("World"));

    // The weaker sublayer (_stage.usda) defines /World/Cube.
    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;
    assert!(prims.contains(&"/World/Cube".to_string()));

    Ok(())
}

/// Vendor test: reference_same_folder.usda references _stage.usda with
/// defaultPrim. The referenced layer's /World/Cube should appear under the
/// referencing prim.
#[test]
fn reference_default_prim_from_external_layer() -> Result<()> {
    let path = composition_path("references/reference_same_folder.usda");
    let stage = Stage::open(&path)?;

    // /World references _stage.usda's defaultPrim ("World"),
    // so /World/Cube should come from the referenced layer.
    let children = child_names(&stage, "/World")?;
    assert!(
        children.contains(&"Cube".to_string()),
        "Cube from referenced layer should appear under /World"
    );

    Ok(())
}

/// An external reference with an explicit prim path should remap the
/// target prim into the referencing prim's namespace.
/// ref_prim.usda: /World/RefPrim references @ref_target.usda@</Source>.
#[test]
fn reference_explicit_prim_path() -> Result<()> {
    let path = fixture_path("ref_prim.usda");
    let stage = Stage::open(&path)?;

    // /Source/Child in ref_target.usda should appear as /World/RefPrim/Child.
    let children = child_names(&stage, "/World/RefPrim")?;
    assert!(
        children.contains(&"Child".to_string()),
        "referenced children should be namespace-remapped"
    );

    Ok(())
}

// --- Inherit composition ---

/// class_inherit.usda: cubeWithoutSetColor inherits from /_myClass which
/// defines displayColor = green. The prim should pick up the class property.
#[test]
fn inherit_from_class() -> Result<()> {
    let path = composition_path("class_inherit.usda");
    let stage = Stage::open(&path)?;

    // The inherited property should be visible.
    let props = prop_names(&stage, "/World/cubeWithoutSetColor")?;
    assert!(
        props.contains(&"primvars:displayColor".to_string()),
        "inherited property should be visible"
    );

    Ok(())
}

// --- Payload composition ---

/// Vendor test: payload_same_folder.usda has a payload to _stage.usda.
/// The payload's prim hierarchy should be composed into the stage.
#[test]
fn payload_pulls_children() -> Result<()> {
    let path = composition_path("payload/payload_same_folder.usda");
    let stage = Stage::open(&path)?;

    // The payload target layer has /World/Cube. Since /World is the payload
    // target, /World/Cube should appear.
    let children = child_names(&stage, "/World")?;
    assert!(
        children.contains(&"Cube".to_string()),
        "Cube from payload layer should appear under /World"
    );

    Ok(())
}

// --- Session layer ---

/// Opens a stage with session_layer.usda over session_root.usda.
fn open_with_session() -> Result<Stage> {
    let root = fixture_path("session_root.usda");
    let session = fixture_path("session_layer.usda");
    Stage::builder().session_layer(&session).open(&root)
}

/// A `${VAR}` sublayer in the root layer resolves against an expression variable
/// authored only on the session layer, and the named layer is loaded from disk:
/// the session is part of the root layer stack, so its variables seed the root's
/// sublayer collection, not just an already-interned lookup.
#[test]
fn session_var_loads_sublayer() -> Result<()> {
    let root = fixture_path("session_expr_sublayer/root.usda");
    let session = fixture_path("session_expr_sublayer/session.usda");
    let stage = Stage::builder().session_layer(&session).open(&root)?;
    assert_eq!(
        stage.attribute("/A.x").get::<f64>()?,
        Some(1.0),
        "the session WHICH variable loads and resolves the root's expression sublayer"
    );
    Ok(())
}

/// Muting a session layer at open time prunes its whole sublayer subtree from the
/// variables that drive root `${VAR}` sublayer collection, not just the exact
/// layer: `strong.usda` (muted) sublayers `vars.usda` (WHICH="b"), `weak.usda`
/// authors WHICH="a", so muting `strong` must compose WHICH="a" and open a.usda —
/// the weaker opinion's sublayer — not the muted subtree's b.usda.
#[test]
fn muted_session_collects_sublayer() -> Result<()> {
    let root = fixture_path("session_expr_mute/root.usda");
    let session = fixture_path("session_expr_mute/session.usda");
    let stage = Stage::builder()
        .session_layer(&session)
        .mute([fixture_path("session_expr_mute/strong.usda")])
        .open(&root)?;
    assert_eq!(
        stage.attribute("/A.x").get::<f64>()?,
        Some(1.0),
        "muting the stronger session opinion composes the weaker's root sublayer (a.usda)"
    );
    Ok(())
}

/// A muted session subtree is pruned after resolving its expression-valued
/// sublayer paths with the session stack variables. The descendant `vars.usda`
/// must not contribute `WHICH=b` after `strong.usda` is muted.
#[test]
fn muted_session_expr_subtree() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let session = dir.path().join("session.usda");
    let strong = dir.path().join("strong.usda");
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@`\"${WHICH}.usda\"`@]\n)\n")?;
    std::fs::write(
        &session,
        "#usda 1.0\n(\n    expressionVariables = {\n        string CHILD = \"vars\"\n    }\n    subLayers = [@strong.usda@, @weak.usda@]\n)\n",
    )?;
    std::fs::write(&strong, "#usda 1.0\n(\n    subLayers = [@`\"${CHILD}.usda\"`@]\n)\n")?;
    std::fs::write(
        dir.path().join("vars.usda"),
        "#usda 1.0\n(\n    expressionVariables = {\n        string WHICH = \"b\"\n    }\n)\n",
    )?;
    std::fs::write(
        dir.path().join("weak.usda"),
        "#usda 1.0\n(\n    expressionVariables = {\n        string WHICH = \"a\"\n    }\n)\n",
    )?;
    std::fs::write(
        dir.path().join("a.usda"),
        "#usda 1.0\ndef \"A\" {\n    custom double x = 1\n}\n",
    )?;
    std::fs::write(
        dir.path().join("b.usda"),
        "#usda 1.0\ndef \"A\" {\n    custom double x = 2\n}\n",
    )?;

    let stage = Stage::builder()
        .session_layer(session.to_str().expect("utf-8 temp path"))
        .mute([strong.to_str().expect("utf-8 temp path")])
        .open(root.to_str().expect("utf-8 temp path"))?;
    assert_eq!(
        stage.attribute("/A.x").get::<f64>()?,
        Some(1.0),
        "the muted expression subtree's WHICH=b does not select b.usda"
    );
    Ok(())
}

/// Open-time muted session paths are anchored against the resolved root layer,
/// not the bare package path. A packaged root whose default layer is
/// `dir/root.usda` therefore mutes `dir/strong.usda` for a relative
/// `mute("strong.usda")` request.
#[test]
fn packaged_root_mute_anchor() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let package = dir.path().join("package.usdz");
    {
        let mut writer = ArchiveWriter::create(&package)?;
        writer.add_layer(
            "dir/root.usda",
            b"#usda 1.0\n(\n    subLayers = [@`\"${WHICH}.usda\"`@]\n)\n",
        )?;
        writer.add_layer(
            "dir/session.usda",
            b"#usda 1.0\n(\n    subLayers = [@strong.usda@, @weak.usda@]\n)\n",
        )?;
        writer.add_layer(
            "dir/strong.usda",
            b"#usda 1.0\n(\n    expressionVariables = {\n        string WHICH = \"b\"\n    }\n)\n",
        )?;
        writer.add_layer(
            "dir/weak.usda",
            b"#usda 1.0\n(\n    expressionVariables = {\n        string WHICH = \"a\"\n    }\n)\n",
        )?;
        writer.add_layer("dir/a.usda", b"#usda 1.0\ndef \"A\" {\n    custom double x = 1\n}\n")?;
        writer.add_layer("dir/b.usda", b"#usda 1.0\ndef \"A\" {\n    custom double x = 2\n}\n")?;
        writer.finish()?;
    }

    let package = package.to_string_lossy();
    let session = format!("{package}[dir/session.usda]");
    let stage = Stage::builder()
        .session_layer(session)
        .mute(["strong.usda"])
        .open(&package)?;
    assert_eq!(
        stage.attribute("/A.x").get::<f64>()?,
        Some(1.0),
        "mute(\"strong.usda\") is anchored relative to the packaged root layer"
    );
    Ok(())
}

/// A stage opened without a session layer should report no session layer.
#[test]
fn no_session_layer_by_default() -> Result<()> {
    let stage = Stage::open(&fixture_path("session_root.usda"))?;

    assert!(!stage.has_session_layer());
    assert!(stage.session_layer().is_none());
    assert_eq!(stage.layer_count(), 1);

    Ok(())
}

/// `defaultPrim` should come from the root layer, not the session layer.
#[test]
fn session_layer_does_not_affect_default_prim() -> Result<()> {
    let stage = open_with_session()?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

/// Children defined only in the root layer should still be visible
/// when a session layer is present.
#[test]
fn session_layer_preserves_children() -> Result<()> {
    let stage = open_with_session()?;

    let children = child_names(&stage, "/World")?;
    assert!(
        children.contains(&"Child".to_string()),
        "root layer's children should be visible: got {children:?}"
    );

    Ok(())
}

#[test]
fn api_schemas_returns_applied_schemas() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let geo = sdf::Path::new("/World/Geo")?;
    let schemas = stage.prim(geo.clone()).api_schemas()?;
    assert!(schemas.contains(&tf::Token::from("MaterialBindingAPI")));
    assert!(schemas.contains(&tf::Token::from("SkelBindingAPI")));
    Ok(())
}

#[test]
fn api_schemas_compose_list_ops() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        append apiSchemas = ["WeakAPI", "RemovedAPI"]
    )
    {
    }
}
"#,
    )?;
    std::fs::write(
        dir.path().join("middle.usda"),
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "World"
{
    over "Geo" (
        prepend apiSchemas = ["StrongAPI"]
    )
    {
    }
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @middle.usda@
    ]
)

over "World"
{
    over "Geo" (
        delete apiSchemas = ["RemovedAPI"]
    )
    {
    }
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let schemas = stage.prim(sdf::Path::new("/World/Geo")?).api_schemas()?;
    assert_eq!(schemas, vec![tf::Token::from("StrongAPI"), tf::Token::from("WeakAPI")]);
    Ok(())
}

#[test]
fn api_schemas_compose_reorder_list_op() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        apiSchemas = ["A", "B", "C"]
    )
    {
    }
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "World"
{
    over "Geo" (
        reorder apiSchemas = ["C", "A"]
    )
    {
    }
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let schemas = stage.prim(sdf::Path::new("/World/Geo")?).api_schemas()?;
    assert_eq!(
        schemas,
        vec![tf::Token::from("C"), tf::Token::from("A"), tf::Token::from("B")]
    );
    Ok(())
}

/// Inherit arc: a class authoring `apiSchemas` contributes to the
/// inheriting prim's composed list, with the local prim's edits applied
/// on top. `has_api_schema` (the surface physics / skel readers depend
/// on) sees both opinions.
#[test]
fn api_schemas_via_inherit() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

class "_Base" (
    prepend apiSchemas = ["BaseAPI"]
)
{
}

def Xform "World"
{
    def Mesh "Geo" (
        inherits = </_Base>
        prepend apiSchemas = ["LocalAPI"]
    )
    {
    }
}
"#,
    )?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let geo = sdf::Path::new("/World/Geo")?;
    assert_eq!(
        stage.prim(geo.clone()).api_schemas()?,
        vec![tf::Token::from("LocalAPI"), tf::Token::from("BaseAPI")],
    );
    assert!(stage.prim(geo.clone()).has_api_schema("BaseAPI")?);
    assert!(stage.prim(geo.clone()).has_api_schema("LocalAPI")?);
    Ok(())
}

/// Reference arc: a referenced asset's `apiSchemas` compose into the
/// referencing prim's list, with the local layer's edits applied on top.
#[test]
fn api_schemas_via_reference() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Source"
)

def Mesh "Source" (
    prepend apiSchemas = ["AssetAPI"]
)
{
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def Xform "World"
{
    def "Geo" (
        references = @asset.usda@
        prepend apiSchemas = ["LocalAPI"]
    )
    {
    }
}
"#,
    )?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let geo = sdf::Path::new("/World/Geo")?;
    assert_eq!(
        stage.prim(geo.clone()).api_schemas()?,
        vec![tf::Token::from("LocalAPI"), tf::Token::from("AssetAPI")],
    );
    Ok(())
}

/// Variant arc: a selected variant authoring `apiSchemas` contributes to
/// the variant-set-owning prim's composed list.
#[test]
fn api_schemas_via_variant() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def Xform "World"
{
    def Mesh "Geo" (
        variants = {
            string mode = "full"
        }
        prepend variantSets = "mode"
        prepend apiSchemas = ["LocalAPI"]
    )
    {
        variantSet "mode" = {
            "full" (
                prepend apiSchemas = ["VariantAPI"]
            ) {
            }
            "empty" {
            }
        }
    }
}
"#,
    )?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let geo = sdf::Path::new("/World/Geo")?;
    let schemas = stage.prim(geo.clone()).api_schemas()?;
    assert!(
        schemas.contains(&tf::Token::from("VariantAPI")),
        "variant contribution missing: {schemas:?}",
    );
    assert!(
        schemas.contains(&tf::Token::from("LocalAPI")),
        "local contribution missing: {schemas:?}",
    );
    Ok(())
}

/// Property paths resolve to the owning prim's schemas (matches the
/// `specifier` / `kind` convention).
#[test]
fn api_schemas_property_path() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let prim = sdf::Path::new("/World/Geo")?;
    let prop = sdf::Path::new("/World/Geo.points")?;
    assert_eq!(stage.prim(prop).api_schemas()?, stage.prim(prim).api_schemas()?);
    Ok(())
}

#[test]
fn connection_paths_compose_list_ops() -> Result<()> {
    // Stack: weak sublayer authors `append`; root layer authors
    // `prepend`. `connection_paths` must fold edits across both
    // layers, not return only the strongest layer's list op.
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def Shader "Mat"
{
    color3f outputs:out
    append color3f inputs:in.connect = [</Mat.outputs:out>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "Mat"
{
    prepend color3f inputs:in.connect = [</Mat.outputs:strong>]
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let conns = connections(&stage, &sdf::Path::new("/Mat.inputs:in")?)?;
    assert_eq!(
        conns,
        vec![
            sdf::Path::new("/Mat.outputs:strong")?,
            sdf::Path::new("/Mat.outputs:out")?
        ]
    );
    Ok(())
}

#[test]
fn relationship_targets_compose_list_ops() -> Result<()> {
    // Weak sublayer appends a target; root prepends one. Raw targets must
    // fold list-op edits across both layers (spec 12.2.6, 12.4).
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0

def "Set"
{
    def "A" {}
    def "B" {}
    append rel members = [</Set/B>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0
(
    subLayers = [
        @weak.usda@
    ]
)

over "Set"
{
    prepend rel members = [</Set/A>]
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let targets = rel_targets(&stage, &sdf::Path::new("/Set.members")?)?;
    assert_eq!(targets, vec![sdf::Path::new("/Set/A")?, sdf::Path::new("/Set/B")?]);
    Ok(())
}

#[test]
fn relationship_targets_remap_reference() -> Result<()> {
    // Targets authored in a referenced asset's namespace resolve into the
    // referencing prim's namespace (spec 12.4 raw targets across arcs).
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Source"
)

def "Source"
{
    def "Child" {}
    rel members = [</Source/Child>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def "Inst" (
    references = @asset.usda@
)
{
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let targets = rel_targets(&stage, &sdf::Path::new("/Inst.members")?)?;
    assert_eq!(targets, vec![sdf::Path::new("/Inst/Child")?]);
    Ok(())
}

#[test]
fn forwarded_targets_honor_mask() -> Result<()> {
    // Forwarding must not read a relationship on a masked-out prim, so the
    // chain through /Hidden.rel contributes nothing; a direct prim target
    // to the masked prim is still returned (raw target value, not a query).
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def "Vis"
{
    rel chain = [</Hidden.rel>]
    rel direct = [</Hidden>]
}

def "Hidden"
{
    rel rel = [</Hidden/Geom>]
    def "Geom" {}
}
"#,
    )?;

    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/Vis"]))
        .open(root.to_str().expect("utf-8 temp path"))?;

    // /Hidden is masked out: its relationship is not followed.
    assert!(fwd_targets(&stage, &sdf::Path::new("/Vis.chain")?)?.is_empty());
    // A direct prim target is still returned, matching raw targets.
    assert_eq!(
        fwd_targets(&stage, &sdf::Path::new("/Vis.direct")?)?,
        vec![sdf::Path::new("/Hidden")?]
    );
    Ok(())
}

#[test]
fn connection_paths_remap_reference() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Source"
)

def Shader "Source"
{
    color3f outputs:out
    color3f inputs:in.connect = [</Source.outputs:out>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def Shader "Mat" (
    references = @asset.usda@
)
{
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let input = sdf::Path::new("/Mat.inputs:in")?;
    let output = sdf::Path::new("/Mat.outputs:out")?;
    assert_eq!(connections(&stage, &input)?, vec![output.clone()]);

    let graph = usd::ConnectionGraph::from_stage(&stage)?;
    assert_eq!(graph.sources(&input), std::slice::from_ref(&output));
    assert_eq!(graph.sinks(&output), &[input]);
    Ok(())
}

#[test]
fn api_schemas_empty_for_prim_without_schemas() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let props = sdf::Path::new("/World/Props")?;
    assert!(stage.prim(props).api_schemas()?.is_empty());
    Ok(())
}

#[test]
fn has_api_schema_matches_applied() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    let geo = sdf::Path::new("/World/Geo")?;
    assert!(stage.prim(geo.clone()).has_api_schema("MaterialBindingAPI")?);
    assert!(!stage.prim(geo.clone()).has_api_schema("SkelRootAPI")?);
    Ok(())
}

#[test]
fn type_name_returns_prim_type() -> Result<()> {
    let stage = Stage::open("fixtures/api_schemas.usda")?;
    assert_eq!(
        stage.prim(sdf::Path::new("/World/Geo")?).type_name()?.as_deref(),
        Some("Mesh")
    );
    assert_eq!(
        stage.prim(sdf::Path::new("/World")?).type_name()?.as_deref(),
        Some("Xform")
    );
    Ok(())
}

fn open_stage_queries_fixture() -> Result<Stage> {
    Stage::open("fixtures/stage_queries.usda")
}

#[test]
fn active_loaded() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert!(stage.prim("/World/ActiveParent/Child").is_active()?);
    assert!(stage.prim("/World/ActiveParent/Child").is_loaded()?);

    assert!(!stage.prim("/World/InactiveParent").is_active()?);
    assert!(!stage.prim("/World/InactiveParent/Child").is_active()?);
    assert!(!stage.prim("/World/InactiveParent/Child").is_loaded()?);

    assert!(!stage.prim("/World/Missing").is_active()?);
    Ok(())
}

/// Records every layer the wrapped resolver opens, to verify lazy loading: a
/// reference/payload target is read from disk only when composition reaches its
/// arc, never at stage-open time.
struct RecordingResolver {
    inner: ar::DefaultResolver,
    opened: Rc<RefCell<Vec<String>>>,
}

impl RecordingResolver {
    fn new(opened: Rc<RefCell<Vec<String>>>) -> Self {
        Self {
            inner: ar::DefaultResolver::new(),
            opened,
        }
    }
}

impl ar::Resolver for RecordingResolver {
    fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
        self.inner.create_identifier(asset_path, anchor)
    }
    fn resolve(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
        self.inner.resolve(asset_path)
    }
    fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
        self.inner.resolve_for_new_asset(asset_path)
    }
    fn open_asset(&self, resolved_path: &ar::ResolvedPath) -> std::io::Result<Box<dyn ar::Asset>> {
        self.opened.borrow_mut().push(resolved_path.to_string());
        self.inner.open_asset(resolved_path)
    }
    fn identity(&self) -> String {
        self.inner.identity()
    }
}

/// A reference target is opened only when composition reaches its arc, not at
/// stage-open time, and then exactly once.
#[test]
fn lazy_reference_loads_on_demand() -> Result<()> {
    let path = composition_path("references/reference_same_folder.usda");
    let opened = Rc::new(RefCell::new(Vec::new()));
    let stage = Stage::builder()
        .resolver(RecordingResolver::new(opened.clone()))
        .open(&path)?;

    let opened_has = |needle: &str| opened.borrow().iter().any(|p| p.contains(needle));

    // Opening the stage reads only the root layer; the reference target stays
    // closed until composition reaches the arc on `/World`.
    assert!(opened_has("reference_same_folder"));
    assert!(!opened_has("_stage.usda"), "reference target must not load at open");
    assert_eq!(stage.layer_count(), 1);

    // Composing `/World` follows its reference, opening the target exactly once.
    let _ = child_names(&stage, "/World")?;
    assert!(opened_has("_stage.usda"), "composing the prim must load its reference");
    assert_eq!(stage.layer_count(), 2);
    let target_opens = opened.borrow().iter().filter(|p| p.contains("_stage.usda")).count();
    assert_eq!(target_opens, 1, "the reference target loads exactly once");
    Ok(())
}

/// A muted reference target contributes nothing and is never read from disk,
/// even once composition reaches its arc, and surfaces a `MutedAssetPath`
/// diagnostic.
#[test]
fn muted_reference_target_not_opened() -> Result<()> {
    let path = composition_path("references/reference_same_folder.usda");
    let target = composition_path("references/_stage.usda");
    let opened = Rc::new(RefCell::new(Vec::new()));
    // Mute the reference target by its canonical identifier.
    let muted_id = ar::DefaultResolver::new().create_identifier(&target, None);
    let stage = Stage::builder()
        .resolver(RecordingResolver::new(opened.clone()))
        .mute([muted_id])
        .open(&path)?;

    // Composing `/World` reaches the muted reference; it is recognized as muted
    // before the loader would open it.
    let _ = child_names(&stage, "/World")?;
    assert!(
        !opened.borrow().iter().any(|p| p.contains("_stage.usda")),
        "a muted reference target must never be opened"
    );
    let errors = stage.composition_errors();
    let muted = errors
        .iter()
        .filter(|e| {
            matches!(
                e,
                pcp::Error::MutedAssetPath { arc: pcp::ArcType::Reference, asset_path, .. }
                    if asset_path.contains("_stage.usda")
            )
        })
        .count();
    assert_eq!(
        muted, 1,
        "a muted reference target must surface exactly one MutedAssetPath diagnostic, got {errors:?}"
    );
    Ok(())
}

/// Unmuting a reference target that was muted *before it ever loaded* recomposes
/// the referrer: the arc was skipped at the demand point (the target never
/// interned, so the layer-keyed mute fanout cannot find the referrer), and the
/// unmute fans out by the target's canonical identifier instead — dropping the
/// stale index so the load barrier finally opens the target on the next query.
#[test]
fn unmute_unloaded_reference_recomposes() -> Result<()> {
    let path = composition_path("references/reference_same_folder.usda");
    let target = composition_path("references/_stage.usda");
    let opened = Rc::new(RefCell::new(Vec::new()));
    let muted_id = ar::DefaultResolver::new().create_identifier(&target, None);
    let stage = Stage::builder()
        .resolver(RecordingResolver::new(opened.clone()))
        .mute([muted_id.clone()])
        .open(&path)?;

    // While muted, the reference is skipped and its target is never opened, so
    // `/World` composes with no referenced children.
    assert_eq!(child_names(&stage, "/World")?, Vec::<String>::new());
    assert!(
        !opened.borrow().iter().any(|p| p.contains("_stage.usda")),
        "a muted reference target must never be opened"
    );

    // Unmuting the never-loaded target must recompose `/World`: the load barrier
    // opens the target on demand and the reference brings in its children.
    stage.unmute_layer(&muted_id);
    assert_eq!(
        child_names(&stage, "/World")?,
        vec!["Cube"],
        "unmuting a never-loaded reference target recomposes the referrer"
    );
    assert!(
        opened.borrow().iter().any(|p| p.contains("_stage.usda")),
        "unmuting must let the load barrier open the now-unmuted target"
    );
    Ok(())
}

#[test]
fn load_none() -> Result<()> {
    let path = composition_path("payload/payload_same_folder.usda");

    let loaded = Stage::open(&path)?;
    // Lazy loading: only the root layer is loaded until composition reaches the
    // payload arc on `/World`.
    assert_eq!(loaded.layer_count(), 1);
    assert!(loaded.prim("/World").is_loaded()?);
    assert_eq!(child_names(&loaded, "/World")?, vec!["Cube"]);
    // Composing `/World` pulled its payload target in, so it is now loaded.
    assert_eq!(loaded.layer_count(), 2);

    let unloaded = Stage::builder().load(InitialLoadSet::LoadNone).open(&path)?;
    assert_eq!(unloaded.load(), InitialLoadSet::LoadNone);
    assert_eq!(unloaded.layer_count(), 1);
    assert!(!unloaded.prim("/World").is_loaded()?);
    assert_eq!(child_names(&unloaded, "/World")?, Vec::<String>::new());

    let mut prims = Vec::new();
    unloaded.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;
    assert!(prims.is_empty());
    Ok(())
}

#[test]
fn defined_abstract() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert_eq!(stage.prim("/World/OverOnly").specifier()?, Some(sdf::Specifier::Over));
    assert!(stage.prim("/World/ActiveParent/Child").is_defined()?);
    assert!(!stage.prim("/World/OverOnly").is_defined()?);
    assert!(!stage.prim("/World/OverParent/Child").is_defined()?);

    assert!(stage.prim("/World/ClassParent/Child").is_defined()?);
    assert!(stage.prim("/World/ClassParent").is_abstract()?);
    assert!(stage.prim("/World/ClassParent/Child").is_abstract()?);
    assert!(!stage.prim("/World/ActiveParent/Child").is_abstract()?);
    Ok(())
}

#[test]
fn instance_flag() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert!(stage.prim("/World/Instance").has_composition_arc()?);
    assert!(stage.prim("/World/Instance").is_instance()?);

    assert!(!stage.prim("/World/InstanceableNoArc").has_composition_arc()?);
    assert!(!stage.prim("/World/InstanceableNoArc").is_instance()?);
    Ok(())
}

/// An instance prim's children come only from its composition arcs; a
/// local-only child is discarded (spec 11.3.3).
#[test]
fn instance_children_from_arcs_only() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing.usda"))?;

    let mut children = child_names(&stage, "/Instance")?;
    children.sort();
    assert_eq!(children, vec!["Child".to_string()]);

    // A plain (non-instance) reference still merges local and referenced
    // children.
    let mut non_instance = child_names(&stage, "/NonInstance")?;
    non_instance.sort();
    assert_eq!(non_instance, vec!["Child".to_string(), "LocalOnly".to_string()]);
    Ok(())
}

/// Instances sharing a prototype resolve descendant values identically and
/// expose the prototype's children (spec 11.3.3).
#[test]
fn shared_instances_resolve_identically() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    assert_eq!(
        stage
            .attribute("/A/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    assert_eq!(
        stage
            .attribute("/B/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    assert_eq!(
        stage
            .attribute("/C/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(9.0))
    );

    assert_eq!(child_names(&stage, "/A")?, vec!["Child".to_string()]);
    assert_eq!(child_names(&stage, "/B")?, vec!["Child".to_string()]);
    Ok(())
}

/// `get_prototype` / `get_instances` group instances by shared composition,
/// and the prototype namespace is addressable (spec 11.3.3).
#[test]
fn prototype_queries() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    let proto = stage.prim("/A").prototype()?;
    assert!(proto.is_some());
    assert_eq!(stage.prim("/B").prototype()?, proto); // same composition → shared
    assert_ne!(stage.prim("/C").prototype()?, proto); // different prototype
    assert_eq!(stage.prim("/Proto").prototype()?, None); // not an instance

    let proto = proto.unwrap();
    // Returned sorted by path, so callers need not sort themselves.
    let instances: Vec<String> = stage
        .prim(proto.clone())
        .instances()
        .iter()
        .map(|p| p.to_string())
        .collect();
    assert_eq!(instances, vec!["/A".to_string(), "/B".to_string()]);

    // The prototype namespace is addressable and resolves to the shared
    // (arc-only) subtree.
    assert!(stage.prim(proto.clone()).is_prototype());
    let child = sdf::path(format!("{proto}/Child"))?;
    assert!(stage.prim(child.clone()).is_in_prototype());
    assert_eq!(
        stage
            .attribute(child.append_property("size")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    Ok(())
}

/// Prototype queries respect the population mask: a masked-out instance is
/// not instanced and never appears among a prototype's instances.
#[test]
fn prototype_queries_masked() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/A"]))
        .open(&fixture_path("instancing_shared.usda"))?;

    // /A is in the mask; /B (which shares /A's prototype) is not.
    assert!(stage.prim("/A").is_instance()?);
    assert!(!stage.prim("/B").is_instance()?);

    let proto = stage.prim("/A").prototype()?;
    assert!(proto.is_some());
    assert_eq!(stage.prim("/B").prototype()?, None);

    // The masked-out /B is excluded from the prototype's instance list.
    let proto = proto.unwrap();
    assert_eq!(stage.prim(proto.clone()).instances(), vec![sdf::path("/A")?]);
    assert_eq!(stage.prototypes(), vec![proto]);
    Ok(())
}

/// A nested instance (an instance inside a prototype's subtree) is
/// recognized, resolves values within the queried instance, and shares its
/// own prototype across the outer instances (spec 11.3.3).
#[test]
fn nested_instances() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_nested.usda"))?;

    assert_eq!(
        stage
            .attribute("/A/Sub/L.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );
    assert_eq!(
        stage
            .attribute("/B/Sub/L.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );

    // The nested prims are instances and share one prototype.
    assert!(stage.prim("/A/Sub").is_instance()?);
    assert!(stage.prim("/B/Sub").is_instance()?);
    let nested = stage.prim("/A/Sub").prototype()?;
    assert!(nested.is_some());
    assert_eq!(stage.prim("/B/Sub").prototype()?, nested);

    // The outer instances share a distinct prototype.
    let outer = stage.prim("/A").prototype()?;
    assert_eq!(stage.prim("/B").prototype()?, outer);
    assert_ne!(outer, nested);

    // The nested subtree is also reachable through the outer prototype.
    let outer = outer.unwrap();
    assert_eq!(
        stage
            .attribute(sdf::path(format!("{outer}/Sub/L.v"))?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );
    Ok(())
}

/// A connection inside an instance subtree resolves within the queried
/// instance, not the shared canonical instance (spec 11.3.3 + 11.3.4).
#[test]
fn instance_connection_remaps_to_instance() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

    // Query /I1 first so it becomes canonical.
    assert_eq!(
        connections(&stage, &sdf::path("/I1/Dst.inputs:in")?)?,
        vec![sdf::path("/I1/Src.outputs:out")?]
    );
    // /I2 shares the prototype; its connection must point into /I2.
    assert_eq!(
        connections(&stage, &sdf::path("/I2/Dst.inputs:in")?)?,
        vec![sdf::path("/I2/Src.outputs:out")?]
    );
    Ok(())
}

/// A connection on a prototype *descendant* resolves in the prototype
/// namespace when queried directly on the prototype, and remaps to the
/// queried instance when reached through a proxy (spec 11.3.3 + 12.4).
#[test]
fn prototype_descendant_target_remap() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

    // Query an instance proxy first to register the prototype; the target
    // remaps into that instance's namespace.
    assert_eq!(
        connections(&stage, &sdf::path("/I1/Dst.inputs:in")?)?,
        vec![sdf::path("/I1/Src.outputs:out")?]
    );

    // The same connection queried directly on the prototype descendant stays
    // in the prototype namespace (no instance to remap to).
    let proto = stage.prim("/I1").prototype()?.expect("I1 is an instance");
    let dst_in = proto.append_path("Dst")?.append_property("inputs:in")?;
    assert_eq!(
        connections(&stage, &dst_in)?,
        vec![proto.append_path("Src")?.append_property("outputs:out")?]
    );
    Ok(())
}

/// Forwarding through a relationship that lives inside an instance
/// prototype resolves within the queried instance: the prototype rel is
/// classified correctly (not mistaken for a terminal) and its targets
/// remap into the instance namespace (spec 11.3.3 + 12.4).
#[test]
fn forwarded_targets_through_instance() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("asset.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Proto"
)

def "Proto"
{
    def "Target" {}
    rel direct = [</Proto/Target>]
    rel chain = [</Proto.direct>]
}
"#,
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        r#"#usda 1.0

def "I1" (
    instanceable = true
    references = @asset.usda@
)
{
}

def "I2" (
    instanceable = true
    references = @asset.usda@
)
{
}
"#,
    )?;

    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    // chain -> direct (a prototype relationship) -> Target. Each hop stays
    // in the queried instance's namespace.
    assert_eq!(
        fwd_targets(&stage, &sdf::path("/I1.chain")?)?,
        vec![sdf::path("/I1/Target")?]
    );
    assert_eq!(
        fwd_targets(&stage, &sdf::path("/I2.chain")?)?,
        vec![sdf::path("/I2/Target")?]
    );
    Ok(())
}

/// Connection and schema readers descend into instance subtrees, so
/// content inside an instance is not silently skipped. Public traversal
/// stops at instances, but these readers need the full composed namespace.
#[test]
fn readers_index_instanced_content() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_connections.usda"))?;

    let graph = usd::ConnectionGraph::from_stage(&stage)?;
    // The connection lives inside the instance /I1; the reader must descend
    // into the instance proxy to index it.
    assert_eq!(
        graph.sources(&sdf::path("/I1/Dst.inputs:in")?),
        &[sdf::path("/I1/Src.outputs:out")?]
    );
    Ok(())
}

/// Default traversal stops at instance prims; `with_instance_proxies`
/// descends into their subtrees (spec 11.3.3).
#[test]
fn traversal_instance_proxies() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    let mut default = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| default.push(p.to_string()))?;
    assert!(default.contains(&"/A".to_string()));
    assert!(!default.contains(&"/A/Child".to_string()));

    let mut proxies = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT.with_instance_proxies(true), |p| {
        proxies.push(p.to_string())
    })?;
    assert!(proxies.contains(&"/A/Child".to_string()));
    Ok(())
}

/// A property authored at an instance root is local to the instance and
/// does not leak onto the shared prototype root (spec 11.3.3): the prototype
/// composes only the referenced opinions.
#[test]
fn prototype_root_drops_instance_overrides() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_root_override.usda"))?;

    // The instance root keeps its local overrides.
    assert_eq!(
        stage
            .attribute("/A.shared")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(7.0))
    );
    assert_eq!(
        stage
            .attribute("/A.rootOnly")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(42.0))
    );

    // The shared prototype root drops them: the overridden property falls
    // back to the referenced value and the instance-only property is gone.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(
        stage
            .attribute(proto.append_property("shared")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    assert_eq!(
        stage
            .attribute(proto.append_property("rootOnly")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );
    Ok(())
}

/// A query on the deterministic synthetic prototype path before any instance
/// composes must not leave the prototype root empty: materialization keys off
/// the registry's mint signal, so it overwrites any stale empty index cached
/// at `/__Prototype_N` (spec 11.3.3).
#[test]
fn prototype_root_survives_early_query() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_root_override.usda"))?;

    // Touch the deterministic synthetic path before any instance registers;
    // this caches an empty index at /__Prototype_0.
    assert_eq!(
        stage
            .attribute("/__Prototype_0.shared")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );

    // Composing the instance mints and materializes /__Prototype_0.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(proto.as_str(), "/__Prototype_0");

    // The prototype root now holds the real composition, not the stale empty
    // index that the guard would otherwise have mistaken for it.
    assert_eq!(
        stage
            .attribute(proto.append_property("shared")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    Ok(())
}

/// A query on a synthetic prototype *descendant* before any instance
/// registers caches a stale empty index and an identity redirection; minting
/// the prototype must evict both so the descendant resolves the shared
/// content rather than the stale synthetic composition (spec 11.3.3).
#[test]
fn prototype_descendant_survives_early_query() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    // Touch the synthetic descendant before any instance registers; this
    // caches an empty index at /__Prototype_0/Child and memoizes its path as
    // an identity (non-redirected) mapping.
    assert_eq!(
        stage
            .attribute("/__Prototype_0/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );

    // Composing the instance mints and materializes /__Prototype_0.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(proto.as_str(), "/__Prototype_0");

    // The descendant now resolves the shared content: minting evicted the
    // stale empty index and identity redirection under /__Prototype_0, so the
    // query recomposes it in place from the materialized prototype root.
    assert_eq!(
        stage
            .attribute(proto.append_path("Child")?.append_property("size")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    Ok(())
}

/// An `AttributeQuery` built on a synthetic prototype descendant before any
/// instance registers must self-heal once the prototype materializes: the
/// empty source is not memoized, so a later read picks up the shared content
/// even though materialization is lazy and does not advance the cache revision
/// (spec 11.3.3).
#[test]
fn query_self_heals_prototype_materialization() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    // Use the query before any instance registers: the synthetic path resolves
    // to nothing yet, and the empty source must not be cached.
    let q = stage.attribute_query("/__Prototype_0/Child.size");
    assert_eq!(q.get_at::<sdf::Value>(usd::TimeCode::new(0.0))?, None);

    // Composing an instance mints and materializes /__Prototype_0 — a lazy step
    // that does not bump the cache revision.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(proto.as_str(), "/__Prototype_0");

    // The same query now resolves the shared content rather than the stale None.
    assert_eq!(q.get_at::<f64>(usd::TimeCode::new(0.0))?, Some(5.0));
    Ok(())
}

/// A property authored inside a variant selected on an instance is shared
/// content (the selection defines the prototype) and must resolve on the
/// materialized prototype root (spec 11.3.3).
#[test]
fn prototype_root_keeps_variant_opinions() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_variant_root.usda"))?;

    // The instance resolves the variant-authored property.
    assert_eq!(
        stage
            .attribute("/A.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );

    // So must the prototype root: the variant opinion lives at the instance's
    // own namespace (/A{v=x}), and rebasing must not move the spec lookup off
    // it.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(
        stage
            .attribute(proto.append_property("picked")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    Ok(())
}

/// A relationship/connection target authored at a prototype's root resolves
/// into the prototype namespace on the materialized prototype root, and into
/// each instance's namespace on the instances (spec 11.3.3 + 12.4). Exercises
/// the root rebase (`rebase_root`) of the prototype-root map.
#[test]
fn prototype_root_target_remap() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_root_target.usda"))?;

    // On the instances the targets stay in each instance's own namespace.
    assert_eq!(
        rel_targets(&stage, &sdf::path("/A.myrel")?)?,
        vec![sdf::path("/A/Target")?]
    );
    assert_eq!(
        connections(&stage, &sdf::path("/A.inputs:in")?)?,
        vec![sdf::path("/A.outputs:out")?]
    );
    assert_eq!(
        rel_targets(&stage, &sdf::path("/B.myrel")?)?,
        vec![sdf::path("/B/Target")?]
    );

    // On the materialized prototype root they resolve into the prototype
    // namespace, not the canonical instance's.
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    assert_eq!(
        rel_targets(&stage, &proto.append_property("myrel")?)?,
        vec![proto.append_path("Target")?]
    );
    assert_eq!(
        connections(&stage, &proto.append_property("inputs:in")?)?,
        vec![proto.append_property("outputs:out")?]
    );
    Ok(())
}

/// The resolved variant selection is part of the instancing key: instances
/// of one reference share a prototype iff their selections match (spec
/// 11.3.3). /A and /C select `x` and share; /B selects `y` and is distinct.
#[test]
fn variant_selection_keys_prototype() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_variant_distinct.usda"))?;

    let proto = |p: &str| -> Result<sdf::Path> {
        stage
            .prim(p)
            .prototype()?
            .ok_or_else(|| anyhow::anyhow!("{p} is not an instance"))
    };

    // Same selection (`x`) shares one prototype; the other selection (`y`)
    // gets a distinct one.
    assert_eq!(proto("/A")?, proto("/C")?);
    assert_ne!(proto("/A")?, proto("/B")?);

    // Each prototype resolves its own variant content.
    assert_eq!(
        stage
            .attribute("/A.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    assert_eq!(
        stage
            .attribute("/B.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(2.0))
    );
    assert_eq!(
        stage
            .attribute("/C.picked")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    Ok(())
}

/// A prototype is populated when at least one of its instances is in the
/// population mask (spec 11.3.3): the synthetic `/__Prototype_N` namespace is
/// never named in a user mask, yet its shared content stays readable through
/// the masked instance.
#[test]
fn prototype_visible_under_mask() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/A"]))
        .open(&fixture_path("instancing_shared.usda"))?;

    // /A is in the mask and is an instance; its prototype is reachable.
    assert!(stage.prim("/A").is_instance()?);
    let proto = stage.prim("/A").prototype()?.expect("A is an instance");

    // The prototype's shared content is readable even though /__Prototype_N
    // is never named in the mask, because instance /A is.
    let child = proto.append_path("Child")?;
    assert!(stage.prim(child.clone()).is_valid()?);
    assert_eq!(
        stage
            .attribute(child.append_property("size")?)
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );

    // A prototype with no masked instance stays hidden: /B (and so the
    // prototype it would otherwise expose) is outside the mask.
    assert!(!stage.mask().includes(&sdf::path("/B")?));
    Ok(())
}

/// A prototype's namespace can contain a nested instance: that nested prim
/// is itself an instance and mints its own prototype, and a prim beneath it
/// is an instance proxy of the nested prototype rather than plain prototype
/// content (spec 11.3.3).
#[test]
fn nested_instance_in_prototype() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_nested_in_prototype.usda"))?;

    let proto = stage.prim("/A").prototype()?.expect("A is an instance");

    // The proxy chain through the instance namespace resolves the nested
    // value (/A/Nested is itself an instance).
    assert!(stage.prim("/A/Nested").is_instance()?);
    assert_eq!(
        stage
            .attribute("/A/Nested/Leaf.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(3.0))
    );

    // Inside the prototype namespace, the nested prim is an instance and
    // mints its own, distinct prototype.
    let nested = stage.prim(proto.append_path("Nested")?);
    assert!(nested.is_instance()?);
    let nested_proto = nested.prototype()?.expect("nested prim is an instance");
    assert_ne!(nested_proto, proto);

    // A prim beneath the nested instance (inside the prototype namespace) is
    // an instance proxy of the nested prototype — previously this was
    // reported as plain prototype content.
    let leaf = stage.prim(proto.append_path("Nested")?.append_path("Leaf")?);
    assert!(leaf.is_instance_proxy()?);
    let in_proto = leaf.prim_in_prototype()?.expect("Leaf is an instance proxy");
    assert_eq!(in_proto.path(), &nested_proto.append_path("Leaf")?);
    Ok(())
}

/// An instance's descendant is an instance proxy that maps to a prim in the
/// shared prototype; the instance root and non-instanced prims are not
/// proxies (spec 11.3.3).
#[test]
fn instance_proxy_api() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_shared.usda"))?;

    assert!(!stage.prim("/A").is_instance_proxy()?);
    assert!(stage.prim("/A/Child").is_instance_proxy()?);

    let proto = stage.prim("/A").prototype()?.expect("A is an instance");
    let in_proto = stage
        .prim("/A/Child")
        .prim_in_prototype()?
        .expect("Child is an instance proxy");
    assert_eq!(in_proto.path(), &proto.append_path("Child")?);
    assert!(in_proto.is_in_prototype());

    // A prim in the prototype namespace is in a prototype, not a proxy.
    assert!(!in_proto.is_instance_proxy()?);

    // A nonexistent path under an instance is not a proxy, and has no prim in
    // the prototype.
    assert!(!stage.prim("/A/Missing").is_instance_proxy()?);
    assert!(stage.prim("/A/Missing").prim_in_prototype()?.is_none());
    Ok(())
}

/// Local opinions on an instance's descendants are discarded; values come
/// from the arc (spec 11.3.3).
#[test]
fn instance_descendant_ignores_local_override() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing.usda"))?;

    // Instance: the local `over Child { size = 999 }` is ignored.
    assert_eq!(
        stage
            .attribute("/Instance/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );

    // Non-instance: the local override wins as usual.
    assert_eq!(
        stage
            .attribute("/NonInstance/Child.size")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(999.0))
    );
    Ok(())
}

#[test]
fn instance_descendant_ignores_local_arc() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_local_arc.usda"))?;

    // The local `over Child (references = </Other/Child>)` carries its own
    // arc; both the local opinion and the node that arc spawns are
    // discarded, so the value comes from the prototype, not /Other/Child.
    assert_eq!(
        stage
            .attribute("/A/Child.v")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(1.0))
    );
    Ok(())
}

#[test]
fn model_hierarchy() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert_eq!(stage.prim("/World").kind()?.as_deref(), Some("assembly"));
    assert!(stage.prim("/World").is_model()?);
    assert!(stage.prim("/World").is_group()?);

    assert!(stage.prim("/World/Group").is_model()?);
    assert!(stage.prim("/World/Group").is_group()?);
    assert!(stage.prim("/World/Group/Component").is_model()?);
    assert!(stage.prim("/World/Group/Component").is_component()?);

    assert!(!stage.prim("/World/Group/Subcomponent").is_model()?);
    assert!(stage.prim("/World/Group/Subcomponent").is_subcomponent()?);

    assert_eq!(
        stage.prim("/World/InvalidComponentParent/Component").kind()?.as_deref(),
        Some("component")
    );
    assert!(!stage.prim("/World/InvalidComponentParent/Component").is_model()?);
    assert!(!stage.prim("/World/InvalidComponentParent/Component").is_component()?);
    Ok(())
}

#[test]
fn prim_status_bits() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    assert_eq!(
        stage.prim_status("/World/ClassParent/Child")?,
        PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::ABSTRACT
    );

    assert_eq!(
        stage.prim_status("/World/Instance")?,
        PrimStatus::ACTIVE | PrimStatus::LOADED | PrimStatus::DEFINED | PrimStatus::INSTANCE
    );
    Ok(())
}

#[test]
fn traverse_default() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::DEFAULT, |p| prims.push(p.as_str().to_string()))?;

    assert!(prims.contains(&"/World".to_string()));
    assert!(prims.contains(&"/World/ActiveParent".to_string()));
    assert!(prims.contains(&"/World/ActiveParent/Child".to_string()));
    assert!(prims.contains(&"/World/Instance".to_string()));

    assert!(!prims.contains(&"/World/InactiveParent".to_string()));
    assert!(!prims.contains(&"/World/InactiveParent/Child".to_string()));
    assert!(!prims.contains(&"/World/OverOnly".to_string()));
    assert!(!prims.contains(&"/World/OverParent".to_string()));
    assert!(!prims.contains(&"/World/OverParent/Child".to_string()));
    assert!(!prims.contains(&"/World/ClassParent".to_string()));
    assert!(!prims.contains(&"/World/ClassParent/Child".to_string()));
    Ok(())
}

#[test]
fn traverse_all_predicate() -> Result<()> {
    let stage = open_stage_queries_fixture()?;

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;

    assert!(prims.contains(&"/World/InactiveParent".to_string()));
    assert!(prims.contains(&"/World/InactiveParent/Child".to_string()));
    assert!(prims.contains(&"/World/OverOnly".to_string()));
    assert!(prims.contains(&"/World/OverParent/Child".to_string()));
    assert!(prims.contains(&"/World/ClassParent".to_string()));
    assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
    Ok(())
}

#[test]
fn custom_predicate() -> Result<()> {
    let stage = open_stage_queries_fixture()?;
    let predicate = PrimPredicate::new(PrimStatus::ACTIVE | PrimStatus::DEFINED, PrimStatus::empty());

    let mut prims = Vec::new();
    stage.traverse(predicate, |p| prims.push(p.as_str().to_string()))?;

    assert!(prims.contains(&"/World/ClassParent".to_string()));
    assert!(prims.contains(&"/World/ClassParent/Child".to_string()));
    assert!(!prims.contains(&"/World/InactiveParent".to_string()));
    assert!(!prims.contains(&"/World/OverOnly".to_string()));
    Ok(())
}

// --- Stage-tier authoring ---

fn in_memory_stage() -> Result<Stage> {
    Stage::builder().in_memory("anon.usda")
}

#[test]
fn author_default_prim() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.set_default_prim("World")?;
    stage.define_prim("/World")?.set_type_name("Xform")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

#[test]
fn default_prim_rejects_path() -> Result<()> {
    let stage = in_memory_stage()?;
    let err = stage.set_default_prim("/World").unwrap_err();
    assert!(matches!(
        err,
        StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. })
    ));
    Ok(())
}

/// Modern OpenUSD allows nested `defaultPrim` values like `"World/Char"`.
/// The write contract must match what the read path will accept.
#[test]
fn default_prim_accepts_nested() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.set_default_prim("World/Mesh")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World/Mesh"));
    Ok(())
}

/// A stage opened from a file is editable — every backend implements the
/// field-level write API — so authoring into its root layer succeeds.
#[test]
fn file_loaded_stage_is_editable() -> Result<()> {
    let stage = Stage::open(&composition_path("subLayer/sublayer_same_folder.usda"))?;
    stage.define_prim("/X")?;
    stage.set_default_prim("World")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

#[test]
fn edit_target_out_of_range() -> Result<()> {
    let stage = in_memory_stage()?;
    let err = stage
        .set_edit_target(EditTarget::for_layer("missing-layer"))
        .unwrap_err();
    assert!(matches!(err, StageAuthoringError::LayerNotFound { .. }));
    Ok(())
}

/// A local edit target maps scene paths to themselves, so authoring is
/// unchanged from the bare-`layer_index` behavior.
#[test]
fn edit_target_local_is_identity() -> Result<()> {
    let target = EditTarget::for_layer("test");
    let path = sdf::path("/A/B")?;
    assert_eq!(target.map_to_spec_path(&path), Some(path));
    Ok(())
}

/// A variant edit target rewrites scene paths into the `{set=sel}`
/// namespace; paths outside the variant prim map to themselves.
#[test]
fn variant_target_maps_selection() -> Result<()> {
    let target = EditTarget::for_local_direct_variant("test", sdf::path("/Prim{set=sel}")?);
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim/child")?),
        Some(sdf::path("/Prim{set=sel}child")?)
    );
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim.attr")?),
        Some(sdf::path("/Prim{set=sel}.attr")?)
    );
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Other")?),
        Some(sdf::path("/Other")?)
    );
    Ok(())
}

/// A bad target is rejected at `edit_context`, leaving the current target
/// unchanged.
#[test]
fn edit_context_rejects_bad_target() -> Result<()> {
    let stage = in_memory_stage()?;
    let before = stage.edit_target().layer_identifier().to_string();
    let result = stage.edit_context(EditTarget::for_layer("missing-layer"));
    assert!(matches!(result, Err(StageAuthoringError::LayerNotFound { .. })));
    assert_eq!(stage.edit_target().layer_identifier(), before);
    Ok(())
}

/// Authoring the variant-owning prim itself through a variant target maps
/// to the bare variant selection, which is not a prim — it must error, not
/// panic.
#[test]
fn define_prim_at_variant_leaf_errors() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.edit_target().layer_identifier().to_string();
    stage.define_prim("/Prim")?;
    stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
    // `/Prim` maps to the variant selection `/Prim{set=sel}`.
    assert!(matches!(
        stage.define_prim("/Prim"),
        Err(StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. }))
    ));
    Ok(())
}

/// In-memory stage with `/Prim` inheriting a local class `/_Class`, so the
/// inherit arc's source layer is the writable root.
fn inherit_stage() -> Result<Stage> {
    let stage = in_memory_stage()?;
    stage.define_prim("/_Class")?;
    stage.define_prim("/Prim")?.set_metadata(
        sdf::FieldKey::InheritPaths.as_str(),
        sdf::Value::PathListOp(sdf::PathListOp::prepended([sdf::path("/_Class")?])),
    )?;
    Ok(stage)
}

/// An arc target on a reference captures the referenced layer and maps composed
/// paths down into its namespace.
#[test]
fn edit_target_for_reference_node() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let target = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    assert!(target.layer_identifier().ends_with("ref_target.usda"));
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/World/MyPrim/Child")?),
        Some(sdf::path("/Source/Child")?)
    );
    Ok(())
}

/// An inherit arc target captures the class-owning layer and maps the composed
/// path to the class path.
#[test]
fn edit_target_for_inherit_node() -> Result<()> {
    let stage = inherit_stage()?;
    let target = stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Inherit)?;
    assert_eq!(target.layer_identifier(), stage.root_layer().identifier());
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim/Child")?),
        Some(sdf::path("/_Class/Child")?)
    );
    Ok(())
}

/// A prim with no arc of the requested kind has no arc target.
#[test]
fn edit_target_no_matching_arc() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Prim")?;
    assert!(matches!(
        stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Reference),
        Err(StageAuthoringError::NoArcNode { .. })
    ));
    Ok(())
}

/// Authoring through an inherit arc target lands the opinion at the class path
/// in the source layer, not at the composed path, and it composes back.
#[test]
fn edit_target_authors_into_class() -> Result<()> {
    let stage = inherit_stage()?;
    let target = stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Inherit)?;
    {
        let _ctx = stage.edit_context(target)?;
        stage.define_prim("/Prim/Child")?;
    }
    assert!(stage.prim("/Prim/Child").is_valid()?);
    assert!(stage.root_layer().data().has_spec(&sdf::path("/_Class/Child")?));
    assert!(!stage.root_layer().data().has_spec(&sdf::path("/Prim/Child")?));
    Ok(())
}

/// `map_to_spec_path` re-maps an embedded relationship target through the same
/// arc mapping (C++ `MapToSpecPath` step 2).
#[test]
fn map_spec_path_remaps_embedded_target() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let target = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/World/MyPrim.rel[/World/MyPrim/Child]")?),
        Some(sdf::path("/Source.rel[/Source/Child]")?)
    );
    Ok(())
}

/// An embedded target outside the arc's co-domain rejects the whole path.
#[test]
fn map_spec_path_rejects_outside_target() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let target = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/World/MyPrim.rel[/Elsewhere]")?),
        None
    );
    Ok(())
}

/// A local target's identity mapping leaves an embedded target untouched.
#[test]
fn map_spec_path_local_keeps_target() -> Result<()> {
    let target = EditTarget::for_layer("test");
    let path = sdf::path("/A.rel[/B].attr")?;
    assert_eq!(target.map_to_spec_path(&path), Some(path));
    Ok(())
}

/// A variant target maps an embedded target without leaving a variant
/// selection on the target path (target paths never carry selections).
#[test]
fn map_spec_path_variant_strips_target() -> Result<()> {
    let target = EditTarget::for_local_direct_variant("test", sdf::path("/Prim{set=sel}")?);
    assert_eq!(
        target.map_to_spec_path(&sdf::path("/Prim.rel[/Prim/T]")?),
        Some(sdf::path("/Prim{set=sel}.rel[/Prim/T]")?)
    );
    Ok(())
}

/// `edit_target_root` names the root layer with an identity mapping and equals
/// the default target installed at open.
#[test]
fn edit_target_root_matches_default() -> Result<()> {
    let stage = in_memory_stage()?;
    let target = stage.edit_target_root();
    assert_eq!(target.layer_identifier(), stage.root_layer().identifier());
    assert_eq!(target.map_to_spec_path(&sdf::path("/A/B")?), Some(sdf::path("/A/B")?));
    assert_eq!(stage.edit_target(), target);
    Ok(())
}

/// `edit_target_session` names the strongest session layer, or is `None` when
/// the stage has no session layer.
#[test]
fn edit_target_session() -> Result<()> {
    let stage = open_with_session()?;
    let target = stage.edit_target_session().expect("session layer");
    assert_eq!(
        target.layer_identifier(),
        stage.session_layer().expect("session layer").identifier()
    );

    assert!(in_memory_stage()?.edit_target_session().is_none());
    Ok(())
}

/// A stage-bound target is rejected by a stage with a different root layer
/// stack identity; a stage-agnostic `for_layer` target is still accepted, and a
/// cloned handle to the same stage accepts its sibling's bound target.
#[test]
fn layer_stack_id_distinguishes_stages() -> Result<()> {
    let stage_a = Stage::builder().in_memory("anon_a.usda")?;
    let stage_b = Stage::builder().in_memory("anon_b.usda")?;
    let bound = stage_a.edit_target_root();
    assert!(matches!(
        stage_b.set_edit_target(bound.clone()),
        Err(StageAuthoringError::EditTargetWrongStage)
    ));
    let root_b = stage_b.root_layer().identifier().to_string();
    assert!(stage_b.set_edit_target(EditTarget::for_layer(root_b)).is_ok());

    // A cloned handle shares the same `StageInner`, so it has the same root
    // layer stack identity and accepts the target built against its sibling.
    let stage_a_clone = stage_a.clone();
    assert!(stage_a_clone.set_edit_target(bound).is_ok());
    Ok(())
}

/// Anonymous root layers are unique per stage even when opened with the same
/// tag, so two such stages have distinct layer stack identities and reject each
/// other's edit targets.
#[test]
fn anonymous_stages_are_distinct() -> Result<()> {
    let stage_a = Stage::builder().in_memory("same.usda")?;
    let stage_b = Stage::builder().in_memory("same.usda")?;
    assert_ne!(stage_a.root_layer().identifier(), stage_b.root_layer().identifier());
    assert!(matches!(
        stage_b.set_edit_target(stage_a.edit_target_root()),
        Err(StageAuthoringError::EditTargetWrongStage)
    ));
    Ok(())
}

/// A target naming a layer is valid; one naming no layer is null and invalid.
#[test]
fn edit_target_null_and_valid() -> Result<()> {
    let valid = EditTarget::for_layer("layer");
    assert!(!valid.is_null());
    assert!(valid.is_valid());

    let null = EditTarget::for_layer("");
    assert!(null.is_null());
    assert!(!null.is_valid());
    Ok(())
}

/// `compose_over` layers a variant refinement onto a reference target, so a
/// stage write resolves through both into the nested spec path; a null target
/// composes to the other.
#[test]
fn edit_target_compose_over() -> Result<()> {
    let stage = Stage::open(&fixture_path("ref_external.usda"))?;
    let weaker = stage.edit_target_for_node(&sdf::path("/World/MyPrim")?, EditTargetArc::Reference)?;
    let stronger = EditTarget::for_local_direct_variant(weaker.layer_identifier(), sdf::path("/Source{set=sel}")?);

    let composed = stronger.compose_over(&weaker);
    assert_eq!(composed.layer_identifier(), weaker.layer_identifier());
    assert_eq!(
        composed.map_to_spec_path(&sdf::path("/World/MyPrim/Child")?),
        Some(sdf::path("/Source{set=sel}Child")?)
    );

    assert_eq!(EditTarget::for_layer("").compose_over(&weaker), weaker);
    Ok(())
}

/// Composing targets bound to stages with different layer stack identities
/// yields a null target, keeping the cross-stage guard intact.
#[test]
fn compose_over_cross_stack_null() -> Result<()> {
    let stage_a = Stage::builder().in_memory("anon_a.usda")?;
    let stage_b = Stage::builder().in_memory("anon_b.usda")?;
    let composed = stage_a.edit_target_root().compose_over(&stage_b.edit_target_root());
    assert!(composed.is_null());
    Ok(())
}

/// A stage-bound target is accepted by a freshly opened stage with the same
/// root layer, session, and resolver context: layer-stack identity is by
/// composition input, not by stage instance.
#[test]
fn layer_stack_id_same_inputs() -> Result<()> {
    let path = fixture_path("ref_external.usda");
    let stage_a = Stage::open(&path)?;
    let stage_b = Stage::open(&path)?;
    assert!(stage_b.set_edit_target(stage_a.edit_target_root()).is_ok());
    Ok(())
}

/// Authoring a time sample through an arc target with a non-identity layer
/// offset keys the sample at the inverse-mapped source time, so it reads back
/// at the original stage time once composition re-applies the offset.
#[test]
fn arc_target_retimes_time_sample() -> Result<()> {
    let stage = in_memory_stage()?;
    // `/Prim` references `/Source` with a (offset = 10) layer offset, so a
    // source-layer time `t` composes to stage time `t + 10`.
    stage.define_prim("/Source")?.create_attribute("x", "double")?;
    stage.define_prim("/Prim")?.set_metadata(
        sdf::FieldKey::References.as_str(),
        sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
            prim_path: sdf::path("/Source")?,
            layer_offset: sdf::LayerOffset::new(10.0, 1.0),
            ..Default::default()
        }])),
    )?;

    let target = stage.edit_target_for_node(&sdf::path("/Prim")?, EditTargetArc::Reference)?;
    // Stage time 15 inverse-maps to source time 5.
    assert_eq!(target.map_to_spec_time(15.0), 5.0);
    {
        let _ctx = stage.edit_context(target)?;
        stage
            .attribute("/Prim.x")
            .set_at(sdf::Value::Double(42.0), usd::TimeCode::new(15.0))?;
    }

    // The sample landed at source time 5 in the root layer...
    let samples = stage.attribute("/Source.x").time_samples()?.expect("samples");
    assert_eq!(samples, vec![(5.0, sdf::Value::Double(42.0))]);
    // ...and reads back at stage time 15 through the offset reference.
    assert_eq!(
        stage.attribute("/Prim.x").get_at::<f64>(usd::TimeCode::new(15.0))?,
        Some(42.0)
    );
    Ok(())
}

/// `time_sample_times` retimes samples brought in through a non-identity arc
/// offset identically to the full `time_samples()` map and to `value_at`.
#[test]
fn time_sample_times_retimed() -> Result<()> {
    let stage = in_memory_stage()?;
    // `/Prim` references `/Source` with offset 10, scale 1: a source time `t`
    // composes to stage time `t + 10`.
    stage
        .define_prim("/Source")?
        .create_attribute("x", "double")?
        .set_at(sdf::Value::Double(1.0), usd::TimeCode::new(0.0))?
        .set_at(sdf::Value::Double(3.0), usd::TimeCode::new(10.0))?;
    stage.define_prim("/Prim")?.set_metadata(
        sdf::FieldKey::References.as_str(),
        sdf::Value::ReferenceListOp(sdf::ReferenceListOp::prepended([sdf::Reference {
            prim_path: sdf::path("/Source")?,
            layer_offset: sdf::LayerOffset::new(10.0, 1.0),
            ..Default::default()
        }])),
    )?;

    let attr = stage.attribute("/Prim.x");
    let map = attr.time_samples()?.expect("samples");
    let retimed_keys: Vec<f64> = map.iter().map(|(t, _)| *t).collect();
    assert_eq!(retimed_keys, vec![10.0, 20.0]);
    assert_eq!(attr.time_sample_times()?, retimed_keys);
    assert_eq!(attr.num_time_samples()?, 2);
    // The retimed times read back as live samples through the offset arc.
    assert_eq!(attr.get_at::<f64>(usd::TimeCode::new(10.0))?, Some(1.0));
    assert_eq!(attr.get_at::<f64>(usd::TimeCode::new(20.0))?, Some(3.0));
    Ok(())
}

/// A prim outside the population mask reports no sample times and a zero count,
/// matching the masked behavior of value resolution.
#[test]
fn time_sample_times_masked() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/B"]))
        .in_memory("anon.usda")?;
    stage
        .define_prim("/A")?
        .create_attribute("x", "double")?
        .set_at(sdf::Value::Double(1.0), usd::TimeCode::new(0.0))?
        .set_at(sdf::Value::Double(3.0), usd::TimeCode::new(10.0))?;
    stage.define_prim("/B")?.create_attribute("y", "double")?;

    let masked = stage.attribute("/A.x");
    assert!(masked.time_sample_times()?.is_empty());
    assert_eq!(masked.num_time_samples()?, 0);
    Ok(())
}

/// An arc target on an instance-proxy path redirects to the shared prototype:
/// it finds the arc authored inside the prototype and maps in the prototype's
/// namespace, so a prototype path remaps to the arc source while the proxy
/// path does not reach it.
#[test]
fn edit_target_for_instance_proxy() -> Result<()> {
    let stage = Stage::open(&fixture_path("instancing_nested_reference.usda"))?;
    let proxy = sdf::path("/World/Inst/OtherChild")?;
    let target = stage.edit_target_for_node(&proxy, EditTargetArc::Reference)?;
    assert!(target.layer_identifier().ends_with("instancing_nested_reference.usda"));

    // The prototype-namespace path remaps to the shared arc source; the proxy
    // path falls outside the mapping's domain, so it does not reach that source.
    let proto = stage
        .prim("/World/Inst")
        .prototype()?
        .expect("instance has a prototype");
    let proto_child = proto.append_path(sdf::path("OtherChild")?)?;
    let source = target.map_to_spec_path(&proto_child).expect("prototype path maps");
    assert_ne!(source, proto_child, "prototype path remaps to the arc source");
    assert_ne!(target.map_to_spec_path(&proxy), Some(source));
    Ok(())
}

// --- Value clips (spec 12.3.4) ---

fn clip_asset(name: &str) -> String {
    format!(
        "{}/vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets/{name}/entry.usd",
        manifest_dir()
    )
}

fn value_f64(stage: &Stage, attr: &str, time: f64) -> Option<f64> {
    match stage
        .attribute(attr)
        .get_at::<sdf::Value>(usd::TimeCode::new(time))
        .expect("value_at")
    {
        Some(sdf::Value::Float(v)) => Some(v as f64),
        Some(sdf::Value::Double(v)) => Some(v),
        Some(sdf::Value::Int64(v)) => Some(v as f64),
        _ => None,
    }
}

fn write_clip_scene(dir: &std::path::Path, root_body: &str, manifest_body: &str, clip_body: &str) -> Result<String> {
    std::fs::write(dir.join("root.usda"), root_body)?;
    std::fs::write(dir.join("manifest.usda"), manifest_body)?;
    std::fs::write(dir.join("clip.usda"), clip_body)?;
    Ok(dir.join("root.usda").to_string_lossy().into_owned())
}

/// Value-clip sample times surface through the introspection accessors (spec
/// 12.3.4): the template set schedules clip.1 at stage 1 and clip.2 at stage 2,
/// so `/Model.size` — which authors no local `timeSamples` — reports those.
#[test]
fn clip_time_samples_gathered() -> Result<()> {
    let stage = Stage::open(&fixture_path("clip_template/root.usda"))?;
    let size = stage.attribute("/Model.size");
    assert_eq!(size.time_sample_times()?, vec![1.0, 2.0]);
    assert_eq!(size.num_time_samples()?, 2);
    assert!(size.value_might_be_time_varying()?);
    assert_eq!(size.time_samples_in_interval(1.5..=3.0)?, vec![2.0]);
    Ok(())
}

/// With `interpolateMissingClipValues`, the activation boundary of a declared
/// but empty middle clip is a genuine value-change point — the active clip
/// switches and the held value gives way to the cross-clip interpolation — so
/// `time_sample_times` reports it, agreeing with `value_at` (spec 12.3.4.7).
#[test]
fn clip_interpolate_missing_boundary_is_a_sample() -> Result<()> {
    let stage = Stage::open(&fixture_path("clip_missing_interp/root.usda"))?;
    let size = stage.attribute("/Model.size");
    // clipA@0, the empty-clip boundary at 10, and clipC@20.
    assert_eq!(size.time_sample_times()?, vec![0.0, 10.0, 20.0]);
    // The reported boundary at 10 is real: the value jumps there (clipA holds
    // 0 up to the switch, then the interpolated gap begins at 50).
    assert_eq!(value_f64(&stage, "/Model.size", 9.999), Some(0.0));
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(50.0));
    Ok(())
}

/// A clip overrides a referenced attribute that has no local opinion: the
/// clip's samples win over the reference's (spec 12.3.4.5).
#[test]
fn clip_basic_overrides_reference() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_basic"))?;
    // clip.usd authors size = stage time; the reference authors negatives.
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(10.0));
    assert_eq!(value_f64(&stage, "/Model.size", 7.0), Some(7.0)); // interpolated
    Ok(())
}

/// An attribute resolved through value clips routes the query through the full
/// resolution path (clips are time-dependent), so the query reproduces `get_at`
/// at every time code.
#[test]
fn query_clip_fallback() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_basic"))?;
    let attr = stage.attribute("/Model.size");
    let q = attr.query();
    for t in [0.0, 7.0, 10.0, 15.0] {
        assert_eq!(
            q.get_at::<sdf::Value>(usd::TimeCode::new(t))?,
            attr.get_at(usd::TimeCode::new(t))?
        );
    }
    assert_eq!(q.get_at::<f32>(usd::TimeCode::new(7.0))?, Some(7.0));
    Ok(())
}

/// Local time samples beat clips; a clip beats a referenced attribute that
/// has no local opinion (spec 12.3.4.5).
#[test]
fn clip_strength_local_vs_reference() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_advanced"))?;
    // `local` has a local opinion → local wins (10, not the clip's -10).
    assert_eq!(value_f64(&stage, "/Model.local", 10.0), Some(10.0));
    // `ref` has no local opinion → the clip wins (-10, not the reference's 10).
    assert_eq!(value_f64(&stage, "/Model.ref", 10.0), Some(-10.0));
    Ok(())
}

#[test]
fn clip_local_default_wins() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float localDefault = 3
}
"#,
        r#"#usda 1.0
def "Model"
{
    float localDefault
}
"#,
        r#"#usda 1.0
def "Model"
{
    float localDefault.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(&root)?;
    assert_eq!(value_f64(&stage, "/Model.localDefault", 0.0), Some(3.0));
    Ok(())
}

/// A local `default` shadows a value clip in introspection just as it does in
/// value resolution (spec 12.3.4.5): the value is the constant default, so the
/// attribute reports no sample times and is not time-varying — the clip's
/// schedule must not leak through.
#[test]
fn clip_local_default_no_time_samples() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float localDefault = 3
}
"#,
        r#"#usda 1.0
def "Model"
{
    float localDefault
}
"#,
        r#"#usda 1.0
def "Model"
{
    float localDefault.timeSamples = {
        0: 7,
        5: 9,
    }
}
"#,
    )?;

    let stage = Stage::open(&root)?;
    let attr = stage.attribute("/Model.localDefault");
    assert_eq!(value_f64(&stage, "/Model.localDefault", 0.0), Some(3.0));
    assert!(attr.time_sample_times()?.is_empty());
    assert_eq!(attr.num_time_samples()?, 0);
    assert!(!attr.value_might_be_time_varying()?);
    Ok(())
}

/// A constant local `default` shadows a multi-clip set: `value_at` is the
/// constant default at every time, so `value_might_be_time_varying` must be
/// false even though the shadowed clip set switches active clips. The clip
/// schedule is only consulted once clips are the winning source.
#[test]
fn clip_shadowed_default_not_varying() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@, @./clip.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0), (10, 1)]
        }
    }
)
{
    float size = 3
}
"#,
        "#usda 1.0\ndef \"Model\"\n{\n    float size\n}\n",
        "#usda 1.0\ndef \"Model\"\n{\n    float size.timeSamples = { 0: 7, 5: 9 }\n}\n",
    )?;

    let stage = Stage::open(&root)?;
    let attr = stage.attribute("/Model.size");
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(3.0));
    assert_eq!(value_f64(&stage, "/Model.size", 12.0), Some(3.0));
    assert!(attr.time_sample_times()?.is_empty());
    assert!(!attr.value_might_be_time_varying()?);
    Ok(())
}

/// A manifest-less clip set sources only attributes its clips actually author.
/// `size` (authored by the clip) reports the clip sample times, while `other`
/// (not authored) reports none rather than the clip's activation schedule —
/// matching the fall-through in value resolution.
#[test]
fn clip_manifestless_unauthored_no_times() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("clip.usda"),
        "#usda 1.0\ndef \"Model\"\n{\n    float size.timeSamples = { 0: 10, 4: 20 }\n}\n",
    )?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size
    float other
}
"#,
    )?;

    let stage = Stage::open(&dir.path().join("root.usda").to_string_lossy())?;
    // The clip authors `size`, so its sample times surface.
    assert_eq!(stage.attribute("/Model.size").time_sample_times()?, vec![0.0, 4.0]);
    // The clip never authors `other`: no spurious clip-boundary sample times.
    let other = stage.attribute("/Model.other");
    assert!(other.time_sample_times()?.is_empty());
    assert_eq!(other.num_time_samples()?, 0);
    Ok(())
}

/// A manifest-less set participates only via the clips its `active` schedule
/// names. Here `active` selects only the empty clip while an unscheduled clip
/// authors samples, so `value_at` falls through to the referenced `timeSamples`
/// — and introspection must surface those arc times, not the empty clip's none.
#[test]
fn clip_manifestless_unscheduled_clip() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("sampled.usda"),
        "#usda 1.0\ndef \"Model\"\n{\n    float size.timeSamples = { 0: 1, 4: 2 }\n}\n",
    )?;
    std::fs::write(dir.path().join("empty.usda"), "#usda 1.0\ndef \"Model\"\n{\n}\n")?;
    std::fs::write(
        dir.path().join("ref.usda"),
        "#usda 1.0\n(\n    defaultPrim = \"Model\"\n)\ndef \"Model\"\n{\n    float size.timeSamples = { 5: 50, 8: 80 }\n}\n",
    )?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Model"
)
def "Model" (
    references = @./ref.usda@
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./sampled.usda@, @./empty.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 1)]
        }
    }
)
{
    float size
}
"#,
    )?;

    let stage = Stage::open(&dir.path().join("root.usda").to_string_lossy())?;
    let size = stage.attribute("/Model.size");
    // The scheduled clip (index 1) is empty, so the set does not source `size`;
    // introspection reports the reference arc's times, agreeing with value_at.
    assert_eq!(size.time_sample_times()?, vec![5.0, 8.0]);
    assert_eq!(value_f64(&stage, "/Model.size", 5.0), Some(50.0));
    assert_eq!(value_f64(&stage, "/Model.size", 8.0), Some(80.0));
    Ok(())
}

/// A manifest-less clip set whose later clip authors nothing still reports that
/// clip's activation boundary as a sample time, because the value changes there:
/// clip0 holds its lone sample back over stage `[0, 10)`, then clip1 (empty)
/// falls through to the reference at `t >= 10`. The reported boundary at 10 is
/// the sole `value_at` change point, so introspection agrees with resolution —
/// no under-reporting (the missed switch) and no arc bleed-through (the
/// reference's `5.0`, a time where the held value never changes).
#[test]
fn clip_manifestless_held_boundary() -> Result<()> {
    let stage = Stage::open(&fixture_path("clip_manifestless_held/root.usda"))?;
    let size = stage.attribute("/Model.size");
    assert_eq!(size.time_sample_times()?, vec![10.0]);
    assert_eq!(size.num_time_samples()?, 1);
    // Two active clips can each serve a different value, so the attribute is
    // time-varying even though the discrete sample count is one.
    assert!(size.value_might_be_time_varying()?);
    // value_at agrees: clip0 holds 50 backward, clip1 falls through to the
    // reference's 999 from the switch at 10.
    assert_eq!(value_f64(&stage, "/Model.size", 5.0), Some(50.0));
    assert_eq!(value_f64(&stage, "/Model.size", 9.999), Some(50.0));
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(999.0));
    Ok(())
}

/// A manifest-less clip set with an empty interior window reports that window's
/// boundary too: clip0 and clip2 author samples, the middle clip authors
/// nothing, and `value_at` changes at each boundary, so all are reported.
#[test]
fn clip_manifestless_interior_empty() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("clip0.usda"),
        "#usda 1.0\ndef \"Model\"\n{\n    float size.timeSamples = { 0: 0, 2: 2 }\n}\n",
    )?;
    std::fs::write(dir.path().join("clip1.usda"), "#usda 1.0\ndef \"Model\"\n{\n}\n")?;
    std::fs::write(
        dir.path().join("clip2.usda"),
        "#usda 1.0\ndef \"Model\"\n{\n    float size.timeSamples = { 20: 20, 22: 22 }\n}\n",
    )?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    defaultPrim = "Model"
)
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip0.usda@, @./clip1.usda@, @./clip2.usda@]
            string primPath = "/Model"
            double2[] active = [(0, 0), (10, 1), (20, 2)]
        }
    }
)
{
    float size
}
"#,
    )?;
    let stage = Stage::open(&dir.path().join("root.usda").to_string_lossy())?;
    let size = stage.attribute("/Model.size");
    // clip0's samples, the empty middle window's boundary at 10, clip2's samples.
    assert_eq!(size.time_sample_times()?, vec![0.0, 2.0, 10.0, 20.0, 22.0]);
    // value_at changes at every reported time: held 2 up to the empty window,
    // None across it, clip2's samples from 20.
    assert_eq!(value_f64(&stage, "/Model.size", 5.0), Some(2.0));
    assert_eq!(value_f64(&stage, "/Model.size", 9.999), Some(2.0));
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), None);
    assert_eq!(value_f64(&stage, "/Model.size", 20.0), Some(20.0));
    Ok(())
}

/// Local `timeSamples` shadow a value clip in introspection just as in value
/// resolution (spec 12.3.4.5): `time_sample_times` reports the local sample
/// times, not the clip's, and `value_at` reads the local samples — the two
/// agree on which source wins.
#[test]
fn clip_local_timesamples_shadow_clips() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size.timeSamples = {
        0: 1,
        10: 3,
    }
}
"#,
        "#usda 1.0\ndef \"Model\"\n{\n    float size\n}\n",
        "#usda 1.0\ndef \"Model\"\n{\n    float size.timeSamples = { 1: 100, 5: 500 }\n}\n",
    )?;

    let stage = Stage::open(&root)?;
    let size = stage.attribute("/Model.size");
    // Local timeSamples win: their times are reported, not the clip's {1, 5}.
    assert_eq!(size.time_sample_times()?, vec![0.0, 10.0]);
    assert_eq!(size.num_time_samples()?, 2);
    // value_at agrees: the local samples drive the value (1 and 3 at their
    // times), not the clip's 100 / 500 — so introspection and resolution pick
    // the same source.
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(1.0));
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(3.0));
    Ok(())
}

#[test]
fn clip_anchor_sublayer() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("sub"))?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    subLayers = [@./sub/weak.usda@]
)

over "Model" (
    clips = {
        dictionary default = {
            double2[] times = [(0, 0)]
        }
    }
)
{
}
"#,
    )?;
    std::fs::write(
        dir.path().join("sub").join("weak.usda"),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("sub").join("manifest.usda"),
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("sub").join("clip.usda"),
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(7.0));
    Ok(())
}

#[test]
fn clip_anchor_reference() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::create_dir(dir.path().join("asset"))?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
def "ShotModel" (
    references = @./asset/model.usda@</Model>
)
{
}
"#,
    )?;
    std::fs::write(
        dir.path().join("asset").join("model.usda"),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("asset").join("manifest.usda"),
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("asset").join("clip.usda"),
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
    assert_eq!(value_f64(&stage, "/ShotModel.size", 0.0), Some(7.0));
    Ok(())
}

#[test]
fn clip_metadata_retimed() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(
        dir.path().join("root.usda"),
        r#"#usda 1.0
(
    subLayers = [@./weak.usda@ (offset = 10)]
)
"#,
    )?;
    std::fs::write(
        dir.path().join("weak.usda"),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
            double2[] times = [(0, 0), (5, 5)]
        }
    }
)
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("manifest.usda"),
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
    )?;
    std::fs::write(
        dir.path().join("clip.usda"),
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 0,
        5: 5
    }
}
"#,
    )?;

    let stage = Stage::open(dir.path().join("root.usda").to_string_lossy().as_ref())?;
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(0.0));
    assert_eq!(value_f64(&stage, "/Model.size", 15.0), Some(5.0));
    Ok(())
}

#[test]
fn clip_initial_jump() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
            double2[] times = [(0, 0), (0, 25), (10, 35)]
        }
    }
)
{
    float size
}
"#,
        r#"#usda 1.0
def "Model"
{
    float size
}
"#,
        r#"#usda 1.0
def "Model"
{
    float size.timeSamples = {
        0: 0.0,
        25: 25.0,
        35: 35.0
    }
}
"#,
    )?;

    let stage = Stage::open(&root)?;
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(25.0));
    assert_eq!(value_f64(&stage, "/Model.size", 5.0), Some(30.0));
    Ok(())
}

/// Active-clip selection switches clips by stage time and maps stage time
/// to clip time through the timing curve (spec 12.3.4.3, 12.3.4.4).
#[test]
fn clip_multi_active_switch() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_multi"))?;
    // Stage 10 → clip1 at clip time 10 → -10.
    assert_eq!(value_f64(&stage, "/Model_1.size", 10.0), Some(-10.0));
    // Stage 22 → clip2 active, clip time 6 → -26.
    assert_eq!(value_f64(&stage, "/Model_1.size", 22.0), Some(-26.0));
    Ok(())
}

/// Clip set strength falls back to name order when `clipSets` is unauthored
/// (spec 12.3.4.1): `clip_a` outranks `clip_b` regardless of text order.
#[test]
fn clip_sets_default_order() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_sets"))?;
    // clip_a (primPath /ClipA) wins: attr at stage 0 → 10, not 100.
    assert_eq!(value_f64(&stage, "/DefaultOrderTest.attr", 0.0), Some(10.0));
    assert_eq!(value_f64(&stage, "/DefaultOrderTest.attr", 1.0), Some(20.0));
    Ok(())
}

/// The timing curve maps stage time to clip time, including a jump
/// discontinuity at stage 20 (spec 12.3.4.4, 12.3.4.8).
#[test]
fn clip_timings_curve() -> Result<()> {
    let stage = Stage::open(&clip_asset("clip_timings"))?;
    assert_eq!(value_f64(&stage, "/Model.size", 0.0), Some(10.0));
    assert_eq!(value_f64(&stage, "/Model.size", 10.0), Some(15.0));
    assert_eq!(value_f64(&stage, "/Model.size", 20.0), Some(10.0)); // jump → "at and after"
    assert_eq!(value_f64(&stage, "/Model.size", 30.0), Some(15.0));
    Ok(())
}

// --- Sublayer mutation / layer-graph construction ---

/// A weak sublayer carrying one opinion, for the sublayer-mutation tests.
fn opinion_layer(identifier: &str, value: f64) -> Result<sdf::Layer> {
    let mut layer = sdf::Layer::new_anonymous(identifier);
    layer.edit(|e| {
        sdf::AttributeSpec::new(e.data_mut(), "/A.x", "double", sdf::Variability::Varying, true)?
            .set_default(sdf::Value::Double(value));
        Ok(())
    })?;
    Ok(layer)
}

/// The parent layer's authored `subLayers` asset paths.
fn authored_sublayers(stage: &Stage) -> Vec<String> {
    let root = stage.root_layer();
    root.pseudo_root().and_then(|pr| pr.sublayers()).unwrap_or_default()
}

/// `insert_layer` both composes the new layer's opinion and authors the
/// parent's `subLayers` metadata, so the edit persists on save.
#[test]
fn insert_layer_authors_metadata() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;
    let root_id = stage.root_layer().identifier().to_string();

    let weak = opinion_layer("weak.usda", 5.0)?;
    let weak_id = weak.identifier().to_string();
    stage.insert_layer(&root_id, 0, weak, sdf::LayerOffset::IDENTITY)?;

    assert_eq!(
        stage.attribute("/A.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );
    assert_eq!(authored_sublayers(&stage), vec![weak_id]);
    Ok(())
}

/// `remove_layer` drops both the composed opinion and the parent's
/// authored `subLayers` entry.
#[test]
fn remove_layer_clears_metadata() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;
    let root_id = stage.root_layer().identifier().to_string();
    let weak = opinion_layer("weak.usda", 5.0)?;
    let weak_id = weak.identifier().to_string();
    stage.insert_layer(&root_id, 0, weak, sdf::LayerOffset::IDENTITY)?;
    assert_eq!(
        stage.attribute("/A.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Double(5.0))
    );

    assert!(stage.remove_layer(&root_id, &weak_id)?, "a sublayer was removed");

    assert_eq!(
        stage.attribute("/A.x").get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None,
        "the removed sublayer's opinion is gone"
    );
    assert!(
        authored_sublayers(&stage).is_empty(),
        "the removed sublayer's subLayers entry is gone"
    );
    Ok(())
}

/// Inserting a sublayer under a file-loaded (and thus editable) parent
/// succeeds and adds exactly one node to the graph.
#[test]
fn insert_layer_into_file_loaded_parent() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(&root, "#usda 1.0\n")?;
    let stage = Stage::open(root.to_str().expect("utf-8 temp path"))?;
    let root_id = stage.root_layer().identifier().to_string();
    let before = stage.layer_count();

    stage.insert_layer(
        &root_id,
        0,
        opinion_layer("weak.usda", 5.0)?,
        sdf::LayerOffset::IDENTITY,
    )?;

    assert_eq!(
        stage.layer_count(),
        before + 1,
        "the inserted sublayer adds exactly one node"
    );
    Ok(())
}

/// Inserting under a parent that is not in the stage fails with
/// `LayerNotFound` and adds no node.
#[test]
fn insert_layer_missing_parent() -> Result<()> {
    let stage = Stage::builder().in_memory("root.usda")?;

    let err = stage
        .insert_layer(
            "nope.usda",
            0,
            opinion_layer("weak.usda", 5.0)?,
            sdf::LayerOffset::IDENTITY,
        )
        .unwrap_err();

    assert!(matches!(err, StageAuthoringError::LayerNotFound { .. }));
    assert_eq!(stage.layer_count(), 1, "no node added for a missing parent");
    Ok(())
}

/// A layer reached through both the session and the root collections is
/// collapsed to one node, keeping the layer count, id set, and root/session
/// split consistent. The session sublayers `shared.usda` and the root
/// sublayers it too, so the four collected layers fold to three nodes.
#[test]
fn from_layers_dedups_order() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(dir.path().join("shared.usda"), "#usda 1.0\n")?;
    std::fs::write(
        dir.path().join("session.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n",
    )?;
    let root = dir.path().join("root.usda");
    std::fs::write(&root, "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n")?;

    let stage = Stage::builder()
        .session_layer(dir.path().join("session.usda").to_string_lossy().into_owned())
        .open(root.to_str().expect("utf-8 temp path"))?;

    assert_eq!(
        stage.layer_count(),
        3,
        "the duplicate shared layer collapses to one node"
    );
    let ids = stage.layer_identifiers();
    let unique: std::collections::HashSet<_> = ids.iter().collect();
    assert_eq!(ids.len(), unique.len(), "no duplicate id survives");
    assert!(
        stage.root_layer().identifier().ends_with("root.usda"),
        "the root stays the first non-session layer after dedup"
    );
    Ok(())
}

/// When the stage root is itself reached as a session sublayer, the root slot
/// collapses onto that shared node — but the root must still resolve to the
/// shared layer, not slip to its own dependency or vanish.
#[test]
fn from_layers_root_shared_with_session() -> Result<()> {
    let dir = tempfile::tempdir()?;
    std::fs::write(dir.path().join("dep.usda"), "#usda 1.0\n")?;
    std::fs::write(
        dir.path().join("shared.usda"),
        "#usda 1.0\n(\n    subLayers = [@dep.usda@]\n)\n",
    )?;
    std::fs::write(
        dir.path().join("session.usda"),
        "#usda 1.0\n(\n    subLayers = [@shared.usda@]\n)\n",
    )?;
    // Open the shared layer itself as the stage root: it is also reached as a
    // session sublayer, so the root slot collapses onto that node.
    let shared = dir.path().join("shared.usda");
    let stage = Stage::builder()
        .session_layer(dir.path().join("session.usda").to_string_lossy().into_owned())
        .open(shared.to_str().expect("utf-8 temp path"))?;

    assert_eq!(stage.layer_count(), 3, "the shared root/session layer is one node");
    assert!(
        stage.root_layer().identifier().ends_with("shared.usda"),
        "the root resolves to the shared layer, not the next dependency"
    );
    Ok(())
}

// --- Stage-tier authoring verified through composed handles ---

#[test]
fn define_prim() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/World")?.set_type_name("Xform")?;
    stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
    assert!(stage.prim("/World").is_defined()?);
    assert!(stage.prim("/World/Mesh").is_defined()?);
    assert_eq!(stage.prim("/World").type_name()?.as_deref(), Some("Xform"));
    assert_eq!(stage.prim("/World/Mesh").type_name()?.as_deref(), Some("Mesh"));
    Ok(())
}

/// A query that misses (the prim is not yet authored) caches the miss; authoring
/// the prim must invalidate that cache so the next query sees it.
#[test]
fn authoring_invalidates_cached_miss() -> Result<()> {
    let stage = in_memory_stage()?;
    assert!(!stage.prim("/World").is_valid()?);

    stage.define_prim("/World")?.set_type_name("Xform")?;

    assert!(stage.prim("/World").is_valid()?);
    assert_eq!(stage.prim("/World").type_name()?.as_deref(), Some("Xform"));
    Ok(())
}

#[test]
fn override_prim() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.override_prim("/A/B")?;
    assert_eq!(stage.prim("/A").specifier()?, Some(sdf::Specifier::Over));
    assert_eq!(stage.prim("/A/B").specifier()?, Some(sdf::Specifier::Over));
    Ok(())
}

// --- Incremental invalidation: per-field change classification ---

/// Authoring `permission = private` on an inherited class is inert metadata:
/// composition never enforces it (C++'s counterpart is compiled out for
/// `Usd`-mode caches), so the inherited opinion keeps resolving unchanged and no
/// recompose is needed.
#[test]
fn permission_edit_does_not_inert_opinion() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        "#usda 1.0\n\ndef \"Class\"\n{\n    custom double attr = 5\n}\n\ndef \"Inst\" (\n    inherits = </Class>\n)\n{\n}\n",
    )?;
    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        stage.attribute("/Inst.attr").get::<sdf::Value>()?,
        Some(sdf::Value::Double(5.0)),
        "the inherited opinion contributes before the permission edit",
    );

    stage.prim("/Class").set_metadata(
        sdf::FieldKey::Permission.as_str(),
        sdf::Value::Permission(sdf::Permission::Private),
    )?;

    assert_eq!(
        stage.attribute("/Inst.attr").get::<sdf::Value>()?,
        Some(sdf::Value::Double(5.0)),
        "permission is inert metadata; the inherited opinion still resolves",
    );
    Ok(())
}

/// Authoring `clips` on a prim that had none is read live through the cached
/// index's spec sites — clips need no classifier entry, since every value view
/// rebuilds against the revision bump. The authored clip set overrides the
/// reference's time samples once present (spec 12.3.4.5).
#[test]
fn clips_edit_resolves_live() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let clip = dir.path().join("clip.usda");
    let manifest = dir.path().join("manifest.usda");
    let referenced = dir.path().join("ref.usda");
    std::fs::write(
        &clip,
        "#usda 1.0\n\ndef \"Model\"\n{\n    double size.timeSamples = {\n        0: 0,\n        10: 10,\n    }\n}\n",
    )?;
    std::fs::write(&manifest, "#usda 1.0\n\ndef \"Model\"\n{\n    double size\n}\n")?;
    std::fs::write(
        &referenced,
        "#usda 1.0\n\ndef \"Model\"\n{\n    double size.timeSamples = {\n        0: -1,\n        10: -10,\n    }\n}\n",
    )?;
    std::fs::write(
        &root,
        format!(
            "#usda 1.0\n\ndef \"Model\" (\n    references = @{}@</Model>\n)\n{{\n}}\n",
            referenced.display()
        ),
    )?;
    let stage = Stage::open(root.to_str().unwrap())?;
    assert_eq!(
        value_f64(&stage, "/Model.size", 10.0),
        Some(-10.0),
        "the reference time sample resolves before any clips are authored",
    );

    let prim = stage.prim("/Model");
    let api = usd::ClipsAPI::new(&prim);
    api.set_clip_asset_paths("default", vec![clip.display().to_string()])?;
    api.set_clip_prim_path("default", "/Model")?;
    api.set_clip_manifest_asset_path("default", manifest.display().to_string())?;
    api.set_clip_active("default", vec![gf::vec2d(0.0, 0.0)])?;

    assert_eq!(
        value_f64(&stage, "/Model.size", 10.0),
        Some(10.0),
        "the authored clip set overrides the reference time sample",
    );
    Ok(())
}

/// The cache memoizes a relationship's resolved targets on first query; editing
/// its `targetPaths` must drop that memo so the next query recomposes them.
/// Regression guard for the property-tier (`did_change_targets`) consumer.
#[test]
fn target_edit_drops_memo() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A")?;
    stage.define_prim("/B")?;
    stage.define_prim("/C")?;
    stage
        .prim("/A")
        .create_relationship("r")?
        .set_targets([sdf::path("/B")?])?;

    // First query populates the memo.
    assert_eq!(stage.relationship("/A.r").targets()?, vec![sdf::path("/B")?]);

    stage.relationship("/A.r").set_targets([sdf::path("/C")?])?;
    assert_eq!(
        stage.relationship("/A.r").targets()?,
        vec![sdf::path("/C")?],
        "the re-authored targets must be visible, not the memoized list",
    );
    Ok(())
}

/// A relationship inherited from a class translates the class's targets into the
/// inheriting prim's namespace. Editing the class relationship must fan out to
/// the inheriting prim's memo (a referenced site's edit restales the translated
/// targets), not just the class's own.
#[test]
fn target_edit_fans_out_to_dependent() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Class")?;
    stage.define_prim("/Class/Local")?;
    stage.define_prim("/Class/Other")?;
    stage
        .prim("/Class")
        .create_relationship("r")?
        .set_targets([sdf::path("/Class/Local")?])?;
    stage.define_prim("/Inst")?.set_metadata(
        sdf::FieldKey::InheritPaths.as_str(),
        sdf::Value::PathListOp(sdf::PathListOp::prepended([sdf::path("/Class")?])),
    )?;
    stage.define_prim("/Inst/Local")?;
    stage.define_prim("/Inst/Other")?;

    // First query memoizes the inherited relationship's translated targets.
    assert_eq!(
        stage.relationship("/Inst.r").targets()?,
        vec![sdf::path("/Inst/Local")?],
        "the inherited target translates into the instance namespace",
    );

    stage
        .relationship("/Class.r")
        .set_targets([sdf::path("/Class/Other")?])?;
    assert_eq!(
        stage.relationship("/Inst.r").targets()?,
        vec![sdf::path("/Inst/Other")?],
        "editing the class relationship restales the inheriting prim's memo",
    );
    Ok(())
}

/// Removing the relationship spec that authored the memoized targets must drop
/// the memo so the next query recomposes. The removal carries only
/// `REMOVE_PROPERTY`, so the producer surfaces the removed `targetPaths` to route
/// it through `did_change_targets`; without that the stale `[/B]` would persist.
#[test]
fn target_spec_removal_drops_memo() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A")?;
    stage.define_prim("/B")?;
    stage
        .prim("/A")
        .create_relationship("r")?
        .set_targets([sdf::path("/B")?])?;

    // Populate the memo.
    assert_eq!(stage.relationship("/A.r").targets()?, vec![sdf::path("/B")?]);

    assert!(stage.remove_property("/A.r")?);
    assert_eq!(
        stage.relationship("/A.r").targets()?,
        Vec::<sdf::Path>::new(),
        "the removed relationship's memoized targets must not persist",
    );
    Ok(())
}

/// A relationship-target value edit is a changed-info edit on the property, not a
/// whole-prim resync: the change notice's `resynced` must not name the owning
/// prim, while `changed_info_only` names the edited relationship.
#[test]
fn target_edit_is_info_only_not_resync() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A")?;
    stage.define_prim("/B")?;
    stage.define_prim("/C")?;
    stage
        .prim("/A")
        .create_relationship("r")?
        .set_targets([sdf::path("/B")?])?;

    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let info: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let (resynced, info) = (resynced.clone(), info.clone());
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            resynced.borrow_mut().extend(oc.resynced.iter().cloned());
            info.borrow_mut().extend(oc.changed_info_only.iter().cloned());
        })
    };
    stage.relationship("/A.r").set_targets([sdf::path("/C")?])?;

    assert!(
        !resynced.borrow().contains(&sdf::path("/A")?),
        "a target value edit must not resync the owning prim"
    );
    assert!(
        info.borrow().contains(&sdf::path("/A.r")?),
        "the edited relationship is reported as changed-info"
    );
    Ok(())
}

/// Removing an attribute is a structural removal, not a changed-info edit: the
/// removed property must not appear in `changed_info_only`, where a consumer
/// reading its value would find it gone.
#[test]
fn attr_removal_not_info_only() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.create_attribute("/P.size", "double")?;

    let info: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let info = info.clone();
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            info.borrow_mut().extend(oc.changed_info_only.iter().cloned());
        })
    };
    assert!(stage.remove_property("/P.size")?);

    assert!(
        !info.borrow().contains(&sdf::path("/P.size")?),
        "a removed attribute must not be reported as a changed-info edit"
    );
    Ok(())
}

/// Removing a relationship that had authored targets surfaces its `targetPaths`
/// for memo invalidation, but that internal signal must not surface the gone
/// property as a changed-info edit — the removal is structural, not info-only.
#[test]
fn rel_removal_not_info_only() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A")?;
    stage.define_prim("/B")?;
    stage
        .prim("/A")
        .create_relationship("r")?
        .set_targets([sdf::path("/B")?])?;

    let info: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let info = info.clone();
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            info.borrow_mut().extend(oc.changed_info_only.iter().cloned());
        })
    };
    assert!(stage.remove_property("/A.r")?);

    assert!(
        !info.borrow().contains(&sdf::path("/A.r")?),
        "a removed relationship with targets must not be reported as a changed-info edit"
    );
    Ok(())
}

/// A connection authored in a class that targets an instance of that class is
/// dropped per `_TargetInClassAndTargetsInstance` — a decision that composes the
/// target prim to read its instance status. The resolved list must not be served
/// from a stale memo after the target prim's instance status changes. `Owner` and
/// `Target` are top-level siblings, so editing `Target` does not fan out to drop
/// `Owner`'s index (their only common ancestor is the pseudo-root); the memo
/// itself must recognize it read cross-prim instance state and resolve live.
#[test]
fn instance_target_memo_not_stale() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    std::fs::write(
        &root,
        "#usda 1.0\n\nclass \"Class\"\n{\n    double x\n    add double x.connect = [</Target.y>]\n    double y\n}\n\n\
         def \"Owner\" (\n    inherits = </Class>\n)\n{\n}\n\ndef \"Target\" (\n    inherits = </Class>\n)\n{\n}\n",
    )?;
    let attr = "/Owner.x";
    let target = sdf::path("/Target")?;
    let drop_inherit = || sdf::Value::PathListOp(sdf::PathListOp::explicit(Vec::<sdf::Path>::new()));

    // Stage A: query first (populating any memo). `Target` is an instance of
    // `Class`, so the class connection to it is dropped. Then drop `Target`'s
    // inherit so it is no longer an instance, and re-query.
    let a = Stage::open(root.to_str().unwrap())?;
    let before = a.attribute(attr).connections()?;
    a.prim(target.clone())
        .set_metadata(sdf::FieldKey::InheritPaths.as_str(), drop_inherit())?;
    let after_cached = a.attribute(attr).connections()?;

    // Stage B: apply the same edit before any query, so its result is composed
    // from scratch with no memo in play.
    let b = Stage::open(root.to_str().unwrap())?;
    b.prim(target)
        .set_metadata(sdf::FieldKey::InheritPaths.as_str(), drop_inherit())?;
    let fresh = b.attribute(attr).connections()?;

    assert_eq!(after_cached, fresh, "the cached path must agree with a fresh compose");
    assert_ne!(
        before, after_cached,
        "the edit must change the result (guards against a vacuous test)"
    );
    Ok(())
}

// --- Adapted from in-module tests: value resolution, existence, authoring ---

/// A direct arc to a `permission = private` site composes normally:
/// `permission` is inert metadata for composition (spec 10.3.3), matching C++'s
/// own arc/target permission enforcement, which is compiled out for `Usd`-mode
/// caches and therefore never runs for a `UsdStage`.
#[test]
fn permission_private_inherit_composes_normally() -> Result<()> {
    let path = format!(
        "{}/vendor/core-spec-supplemental-release_dec2025/composition/tests/assets/\
             ErrorPermissionDenied_root/usda/root.usd",
        manifest_dir()
    );
    let stage = Stage::builder().open(&path)?;

    // /Model inherits the private /_PrivateClass; the inherited opinion stays
    // visible and composing it raises no error.
    assert!(
        stage
            .prim("/Model")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "attr"),
        "private inherit must stay visible"
    );
    assert!(
        stage.composition_errors().is_empty(),
        "permission = private must not raise a composition error"
    );

    Ok(())
}

/// Reading a field from a single-layer stage should return the authored value.
#[test]
fn field_single_layer() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    // CubeInactive composes as inactive; CubeActive as active.
    assert!(!stage.prim("/World/CubeInactive").is_active()?);
    assert!(stage.prim("/World/CubeActive").is_active()?);

    Ok(())
}

// --- Sublayer composition ---

/// sublayer_override.usda sublayers sublayer_base.usda. Both layers define
/// /World/Cube but with different displayColor values. The stronger (override)
/// layer's opinion should win (first-opinion-wins rule).
#[test]
fn sublayer_stronger_opinion_wins() -> Result<()> {
    let path = fixture_path("sublayer_override.usda");
    let stage = Stage::open(&path)?;

    assert_eq!(stage.layer_count(), 2);

    // /World/Cube.primvars:displayColor is overridden to blue [(0,0,1)] in
    // the stronger layer, base has red [(1,0,0)].
    let prop_path = sdf::Path::new("/World/Cube")?.append_property("primvars:displayColor")?;
    let value = stage.attribute(&prop_path).get::<sdf::Value>()?;
    assert!(value.is_some(), "displayColor should have a composed value");

    // The composed value must come from the stronger layer (blue),
    // not the weaker layer (red). Verify by checking it's not the base red.
    let value = value.unwrap();
    let base_red = sdf::Value::Vec3fVec(vec![gf::vec3f(1.0, 0.0, 0.0)]);
    assert_ne!(value, base_red, "stronger layer opinion should win over weaker");

    Ok(())
}

/// The active.usda vendor test has prims with active=true/false metadata.
/// Verify field resolution returns the correct authored values.
#[test]
fn field_active_metadata() -> Result<()> {
    let path = composition_path("active.usda");
    let stage = Stage::open(&path)?;

    assert!(!stage.prim("/World/CubeInactive").is_active()?);
    assert!(stage.prim("/World/CubeActive").is_active()?);

    Ok(())
}

// --- Reference composition ---

/// An external reference with defaultPrim should pull the referenced prim's
/// children into the referencing prim's namespace.
/// ref_external.usda: /World/MyPrim references ref_target.usda (defaultPrim="Source").
/// ref_target.usda defines /Source/Child with displayColor.
#[test]
fn reference_external_default_prim() -> Result<()> {
    let path = fixture_path("ref_external.usda");
    let stage = Stage::open(&path)?;

    // /World/MyPrim should exist via the reference.
    assert!(stage.prim("/World/MyPrim").is_valid()?);

    // /World/MyPrim/Child should be reachable via namespace remapping.
    let children = child_names(&stage, "/World/MyPrim")?;
    assert!(
        children.contains(&"Child".to_string()),
        "referenced children should be visible"
    );

    Ok(())
}

/// class_inherit.usda: cubeWithSetColor inherits from /_myClass but
/// overrides displayColor locally. Local opinion (red) should win
/// over the inherited opinion (green).
#[test]
fn inherit_local_opinion_wins() -> Result<()> {
    let path = composition_path("class_inherit.usda");
    let stage = Stage::open(&path)?;

    // The local displayColor (red) should win over inherited (green).
    let prop = sdf::Path::new("/World/cubeWithSetColor")?.append_property("primvars:displayColor")?;
    let value = stage.attribute(&prop).get::<sdf::Value>()?;
    assert!(value.is_some());

    // Verify it's the local red, not the inherited green.
    let green = sdf::Value::Vec3fVec(vec![gf::vec3f(0.0, 0.8, 0.0)]);
    assert_ne!(value.unwrap(), green, "local opinion should win over inherited");

    Ok(())
}

// --- Variant selection ---

/// The local opinion on radius (1) should be stronger than the variant's (2).
#[test]
fn variant_local_opinion_wins() -> Result<()> {
    let path = format!(
        "{}/vendor/usd-wg-assets/docs/CompositionPuzzles/VariantSetAndLocal1/puzzle_1.usda",
        manifest_dir()
    );
    let stage = Stage::open(&path)?;

    // The local radius=1 should win over variant radius=2.
    let prop = sdf::Path::new("/World/Sphere")?.append_property("radius")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(1.0), "local opinion (1) should win over variant (2)");

    Ok(())
}

// --- Specialize composition ---

/// The local opinion on displayColor (yellow) should win over the
/// specialized source's displayColor (red).
#[test]
fn specialize_local_opinion_wins() -> Result<()> {
    let path = composition_path("inherit_and_specialize.usda");
    let stage = Stage::open(&path)?;

    let prop = sdf::Path::new("/World/cubeScene/specializes")?.append_property("primvars:displayColor")?;
    let value = stage.attribute(&prop).get::<sdf::Value>()?;
    assert!(value.is_some());

    // Local is yellow (0.8, 0.8, 0), source is red (0.8, 0, 0).
    let red = sdf::Value::Vec3fVec(vec![gf::vec3f(0.8, 0.0, 0.0)]);
    assert_ne!(value.unwrap(), red, "local opinion should win over specialized");

    Ok(())
}

/// A prim with `instanceable = true` composes as instanceable.
#[test]
fn instanceable_true_parses_and_is_readable() -> Result<()> {
    let path = fixture_path("instanceable_metadata.usda");
    let stage = Stage::open(&path)?;

    assert!(stage.prim("/Root/InstancePrototype").is_instanceable()?);

    Ok(())
}

/// A prim with `instanceable = false` composes as not instanceable.
#[test]
fn instanceable_false_parses_and_is_readable() -> Result<()> {
    let path = fixture_path("instanceable_metadata.usda");
    let stage = Stage::open(&path)?;

    assert!(!stage.prim("/Root/NotInstanceable").is_instanceable()?);

    Ok(())
}

/// A prim without `instanceable` metadata defaults to not instanceable.
#[test]
fn instanceable_absent_defaults_false() -> Result<()> {
    let path = fixture_path("instanceable_metadata.usda");
    let stage = Stage::open(&path)?;

    assert!(!stage.prim("/Root").is_instanceable()?);

    Ok(())
}

// --- Variant fallback selection ---

/// A variant fallback should select the specified variant when no authored
/// selection exists. The prim should expose opinions from the fallback variant.
#[test]
fn variant_fallback_selects_preferred() -> Result<()> {
    let path = fixture_path("variant_fallback.usda");
    let fallbacks = pcp::VariantFallbackMap::new().add("shadingComplexity", ["simple"]);
    let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

    // /NoSelection has no authored selection. With fallback "simple",
    // the complexity field should be 0.5 (not 1.0 from "full").
    let prop = sdf::Path::new("/NoSelection")?.append_property("complexity")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(0.5), "fallback 'simple' should give complexity=0.5");

    Ok(())
}

/// An authored selection should take priority over a variant fallback at the
/// stage level.
#[test]
fn variant_fallback_does_not_override_authored() -> Result<()> {
    let path = fixture_path("variant_fallback.usda");
    let fallbacks = pcp::VariantFallbackMap::new().add("shadingComplexity", ["none"]);
    let stage = Stage::builder().variant_fallbacks(fallbacks).open(&path)?;

    // /Root has authored selection "full". Even with fallback "none",
    // the authored selection should win.
    let prop = sdf::Path::new("/Root")?.append_property("complexity")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(1.0), "authored 'full' should win over fallback 'none'");

    Ok(())
}

// --- Inherit child propagation ---

/// A prim that inherits a class should expose the class's children even
/// when the inheriting prim has no local override for them.
#[test]
fn inherit_child_exists_without_local_override() -> Result<()> {
    let path = fixture_path("inherit_child_propagation.usda");
    let stage = Stage::open(&path)?;

    // /Instance inherits /BaseClass which has child /BaseClass/Child.
    // /Instance/Child should exist even though Instance has no local "Child".
    let children = child_names(&stage, "/Instance")?;
    assert!(
        children.contains(&"Child".to_string()),
        "inherited child should appear: got {children:?}"
    );

    // The inherited property should be accessible.
    assert!(
        stage
            .prim("/Instance/Child")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "name"),
        "property from inherited child should be visible"
    );

    Ok(())
}

/// Nested children from an inherited class should propagate through
/// multiple levels even without local overrides at any level.
#[test]
fn inherit_nested_child_propagation() -> Result<()> {
    let path = fixture_path("inherit_nested_child.usda");
    let stage = Stage::open(&path)?;

    // /Prim inherits /Base. /Base/A/B exists with val=1.0.
    // /Prim/A should exist, /Prim/A/B should exist.
    let a_children = child_names(&stage, "/Prim")?;
    assert!(
        a_children.contains(&"A".to_string()),
        "first-level child: got {a_children:?}"
    );

    let b_children = child_names(&stage, "/Prim/A")?;
    assert!(
        b_children.contains(&"B".to_string()),
        "second-level child: got {b_children:?}"
    );

    assert!(
        stage
            .prim("/Prim/A/B")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "val"),
        "deeply nested inherited property should be visible"
    );

    Ok(())
}

/// Children should propagate through an inherit chain (Leaf → Middle → GrandBase).
#[test]
fn inherit_chain_child_propagation() -> Result<()> {
    let path = fixture_path("inherit_chain_child.usda");
    let stage = Stage::open(&path)?;

    // /Leaf inherits /Middle which inherits /GrandBase.
    // /GrandBase/Deep exists with x=42. /Leaf/Deep should exist.
    let children = child_names(&stage, "/Leaf")?;
    assert!(
        children.contains(&"Deep".to_string()),
        "chain-inherited child: got {children:?}"
    );

    assert!(
        stage
            .prim("/Leaf/Deep")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "x"),
        "property from chain-inherited child should be visible"
    );

    Ok(())
}

/// A session layer's opinions should be stronger than the root layer's.
#[test]
fn session_layer_opinion_wins() -> Result<()> {
    let stage = open_with_session()?;

    assert!(stage.has_session_layer());
    assert_eq!(stage.layer_count(), 2);
    assert!(stage
        .session_layer()
        .expect("configured session layer")
        .identifier()
        .ends_with("session_layer.usda"));

    let prop = sdf::Path::new("/World")?.append_property("radius")?;
    let value = stage.attribute(&prop).get::<f64>()?;
    assert_eq!(value, Some(99.0), "session layer opinion should win");

    Ok(())
}

/// The session layer can add properties not present in the root layer.
#[test]
fn session_layer_adds_properties() -> Result<()> {
    let stage = open_with_session()?;

    let prop = sdf::Path::new("/World")?.append_property("visibility")?;
    let value = stage.attribute(&prop).get::<String>()?;
    assert_eq!(value, Some("hidden".to_string()));

    Ok(())
}

/// The root layer's properties not overridden by the session layer
/// should still be accessible.
#[test]
fn session_layer_preserves_root_opinions() -> Result<()> {
    let stage = open_with_session()?;

    let prop = sdf::Path::new("/World")?.append_property("name")?;
    let value = stage.attribute(&prop).get::<String>()?;
    assert_eq!(value, Some("root".to_string()));

    Ok(())
}

#[test]
fn mask_traverse() -> Result<()> {
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/World/ActiveParent/Child"]))
        .open("fixtures/stage_queries.usda")?;

    assert_eq!(
        stage.root_prims()?.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        ["World"]
    );
    assert_eq!(child_names(&stage, "/World")?, vec!["ActiveParent"]);
    assert_eq!(child_names(&stage, "/World/ActiveParent")?, vec!["Child"]);

    assert!(stage.prim("/World").is_valid()?);
    assert!(stage.prim("/World/ActiveParent/Child").is_valid()?);
    assert!(!stage.prim("/World/Group").is_valid()?);
    assert_eq!(stage.prim("/World/Group").kind()?, None);

    let mut prims = Vec::new();
    stage.traverse(PrimPredicate::ALL, |p| prims.push(p.as_str().to_string()))?;
    assert_eq!(
        prims,
        vec!["/World", "/World/ActiveParent", "/World/ActiveParent/Child"]
    );
    Ok(())
}

#[test]
fn mask_skips_dependency() -> Result<()> {
    let path = composition_path("references/reference_invalid.usda");
    let stage = Stage::builder()
        .mask(StagePopulationMask::new(["/World/cube"]))
        .open(&path)?;

    assert_eq!(
        stage.root_prims()?.iter().map(|t| t.as_str()).collect::<Vec<_>>(),
        ["World"]
    );
    assert_eq!(child_names(&stage, "/World")?, vec!["cube"]);
    assert!(!stage.prim("/World/invalid_reference").is_valid()?);
    Ok(())
}

/// `Stage::custom_layer_data` reads the root layer's `customLayerData`
/// dictionary (C++ `UsdStage::GetRootLayer()->GetCustomLayerData`).
#[test]
fn custom_layer_data() -> Result<()> {
    let stage = in_memory_stage()?;
    assert!(stage.custom_layer_data()?.is_none());

    let dict = sdf::Value::Dictionary([("tool".to_string(), sdf::Value::String("rs".into()))].into());
    stage.set_custom_layer_data(dict)?;

    let Some(sdf::Value::Dictionary(read)) = stage.custom_layer_data()? else {
        panic!("customLayerData should resolve to a dictionary");
    };
    assert_eq!(read.get("tool"), Some(&sdf::Value::String("rs".into())));
    Ok(())
}

#[test]
fn create_attribute() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Sphere")?.set_type_name("Sphere")?;
    stage.create_attribute("/Sphere.radius", "double")?;

    let attr = stage.attribute("/Sphere.radius");
    assert_eq!(attr.type_name()?.as_deref(), Some("double"));
    assert!(attr.is_custom()?, "generic attributes are authored custom");
    // The property composes as an attribute (not a relationship).
    let radius = sdf::Path::new("/Sphere.radius")?;
    let attrs = stage.prim("/Sphere").attributes()?;
    assert!(attrs.iter().any(|a| a.path() == &radius));
    Ok(())
}

#[test]
fn create_relationship() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Mesh")?.set_type_name("Mesh")?;
    let rel = stage
        .create_relationship("/Mesh.material:binding")?
        .set_variability(sdf::Variability::Uniform)?;

    assert!(rel.is_custom()?, "generic relationships are authored custom");
    // The property composes as a relationship (not an attribute).
    let binding = sdf::Path::new("/Mesh.material:binding")?;
    let rels = stage.prim("/Mesh").relationships()?;
    assert!(rels.iter().any(|r| r.path() == &binding));
    Ok(())
}

/// `defaultPrim` writes target the root layer regardless of `EditTarget`
/// (mirrors C++ `UsdStage::SetDefaultPrim` going through `GetRootLayer`).
/// In-memory root with a file-loaded session layer; setting the edit
/// target to the read-only session layer must not block the write.
#[test]
fn default_prim_targets_root() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    let session_id = stage.session_layer().expect("session layer").identifier().to_string();
    stage.set_edit_target(EditTarget::for_layer(session_id))?;
    stage.set_default_prim("World")?;
    assert_eq!(stage.default_prim().as_deref(), Some("World"));
    Ok(())
}

/// Exercises `StageBuilder::in_memory`'s session-layer branch: the
/// anonymous root must end up at `session_layer_count`, the edit target
/// must point there, and authoring on the in-memory root must work
/// (with the session layer remaining read-only).
#[test]
fn in_memory_session_layer() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    assert!(stage.has_session_layer());
    assert_eq!(stage.layer_count(), 2);
    assert_eq!(stage.edit_target().layer_identifier(), stage.root_layer().identifier());
    stage.define_prim("/World")?.set_type_name("Xform")?;
    assert!(stage.prim("/World").is_defined()?);
    Ok(())
}

/// `edit_context` restores the previous edit target when the guard drops.
#[test]
fn edit_context_restores_on_drop() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    let root_id = stage.root_layer().identifier().to_string();
    let session_id = stage.session_layer().expect("session layer").identifier().to_string();
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    {
        let _ctx = stage.edit_context(EditTarget::for_layer(session_id.clone()))?;
        assert_eq!(stage.edit_target().layer_identifier(), session_id);
    }
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    Ok(())
}

/// The guard restores the target even when the scope exits early via `?`.
#[test]
fn edit_context_restores_on_error() -> Result<()> {
    let session = fixture_path("session_layer.usda");
    let stage = Stage::builder().session_layer(&session).in_memory("anon.usda")?;
    let root_id = stage.root_layer().identifier().to_string();
    let session_id = stage.session_layer().expect("session layer").identifier().to_string();
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    let authored: std::result::Result<(), StageAuthoringError> = (|| {
        let _ctx = stage.edit_context(EditTarget::for_layer(session_id))?;
        // Authoring a prim at a property path is invalid; the write fails and
        // `?` returns from this closure with the guard still in scope.
        stage.define_prim("/A.x")?;
        Ok(())
    })();
    assert!(authored.is_err());
    assert_eq!(stage.edit_target().layer_identifier(), root_id);
    Ok(())
}

/// A significant edit inside a variant must invalidate the composed
/// (variant-stripped) prim, whose cache key is not on the variant path's
/// ancestor chain.
#[test]
fn variant_edit_invalidates_stripped_path() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.edit_target().layer_identifier().to_string();
    stage.define_prim("/Prim")?;

    // Cache a composed miss at the scene path.
    assert!(!stage.prim("/Prim/child").is_valid()?);
    assert!(stage.is_indexed(&sdf::path("/Prim/child")?));

    // Author the child inside the variant: `/Prim/child` -> `/Prim{set=sel}child`.
    stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
    stage.define_prim("/Prim/child")?;

    // The stripped composed key must be dropped so the next query rebuilds.
    assert!(!stage.is_indexed(&sdf::path("/Prim/child")?));
    Ok(())
}

#[test]
fn clip_skips_missing_attr() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = write_clip_scene(
        dir.path(),
        r#"#usda 1.0
def "Model" (
    clips = {
        dictionary default = {
            asset[] assetPaths = [@./clip.usda@]
            asset manifestAssetPath = @./manifest.usda@
            string primPath = "/Model"
            double2[] active = [(0, 0)]
        }
    }
)
{
}
"#,
        r#"#usda 1.0
def "Model"
{
    float ghost
}
"#,
        r#"#usda 1.0
def "Model"
{
    float ghost.timeSamples = {
        0: 7
    }
}
"#,
    )?;

    let stage = Stage::open(&root)?;
    assert!(
        !stage
            .prim("/Model")
            .property_names()?
            .iter()
            .any(|n| n.as_str() == "ghost"),
        "the clip must not fabricate an attribute"
    );
    assert_eq!(
        stage
            .attribute("/Model.ghost")
            .get_at::<sdf::Value>(usd::TimeCode::new(0.0))?,
        None
    );
    Ok(())
}

// Stage change listeners (C++ `UsdNotice`), exercised through the public API.

/// A listener installed with `set_listener` fires once per edit, and the
/// notice's `resynced` paths name the prim whose composition changed.
#[test]
fn listener_fires_on_define() -> Result<()> {
    let stage = in_memory_stage()?;
    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let count = Rc::new(Cell::new(0u32));
    let _token = {
        let (resynced, count) = (resynced.clone(), count.clone());
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            count.set(count.get() + 1);
            resynced.borrow_mut().extend(oc.resynced.iter().cloned());
        })
    };
    stage.define_prim("/World")?;
    assert_eq!(count.get(), 1);
    assert!(resynced.borrow().contains(&sdf::Path::new("/World")?));
    Ok(())
}

/// A pure value edit reports its path under `changed_info_only` (not
/// `resynced`), and `changed_fields` names the authored field.
#[test]
fn listener_info_only() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/World")?;
    let attr = stage.create_attribute("/World.size", "double")?;
    let info: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let has_default = Rc::new(Cell::new(false));
    let _token = {
        let (info, resynced, has_default) = (info.clone(), resynced.clone(), has_default.clone());
        let size = sdf::Path::new("/World.size")?;
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            info.borrow_mut().extend(oc.changed_info_only.iter().cloned());
            resynced.borrow_mut().extend(oc.resynced.iter().cloned());
            if oc.changed_fields(&size).iter().any(|t| t.as_str() == "default") {
                has_default.set(true);
            }
        })
    };
    attr.set(2.0_f64)?;
    assert!(info.borrow().contains(&sdf::Path::new("/World.size")?));
    assert!(resynced.borrow().is_empty());
    assert!(has_default.get());
    Ok(())
}

/// An info-only edit authored through a variant edit target reports its path
/// in stage namespace (`/Prim.size`), translated from the `{set=sel}` layer
/// namespace through the target's mapping, not the raw spec path. The
/// stage-namespace path round-trips through `changed_fields`, which translates
/// it back to the `{set=sel}` change-list key.
#[test]
fn listener_info_under_variant_target() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.edit_target().layer_identifier().to_string();
    stage.define_prim("/Prim")?;
    stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;
    // Create the attribute inside the variant before installing the listener, so
    // the listener only observes the info-only `set` below.
    let attr = stage.create_attribute("/Prim.size", "double")?;

    let info: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let has_default = Rc::new(Cell::new(false));
    let _token = {
        let (info, has_default) = (info.clone(), has_default.clone());
        let size = sdf::path("/Prim.size")?;
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            info.borrow_mut().extend(oc.changed_info_only.iter().cloned());
            // `changed_fields` takes the stage-namespace path from
            // `changed_info_only` and finds the field under the layer key.
            if oc.changed_fields(&size).iter().any(|t| t.as_str() == "default") {
                has_default.set(true);
            }
        })
    };
    attr.set(2.0_f64)?;

    assert!(info.borrow().contains(&sdf::path("/Prim.size")?));
    assert!(!info.borrow().contains(&sdf::path("/Prim{set=sel}.size")?));
    assert!(has_default.get());
    Ok(())
}

/// A structural edit through a variant edit target reports its resynced path in
/// stage namespace (`/Prim/child`). The literal authored path the change
/// pipeline fans out (`/Prim{set=sel}child`) must not leak into `resynced`.
#[test]
fn listener_resync_under_variant_target() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.edit_target().layer_identifier().to_string();
    stage.define_prim("/Prim")?;
    stage.set_edit_target(EditTarget::for_local_direct_variant(root, sdf::path("/Prim{set=sel}")?))?;

    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let resynced = resynced.clone();
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            resynced.borrow_mut().extend(oc.resynced.iter().cloned());
        })
    };
    stage.define_prim("/Prim/child")?;

    assert!(resynced.borrow().contains(&sdf::path("/Prim/child")?));
    assert!(!resynced.borrow().contains(&sdf::path("/Prim{set=sel}child")?));
    Ok(())
}

/// Switching the edit target delivers `EditTargetChanged`; re-setting the same
/// target is a no-op and fires nothing.
#[test]
fn listener_edit_target_changed() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.root_layer().identifier().to_string();
    let sub = sdf::Layer::new_anonymous("sub.usda");
    let sub_id = sub.identifier().to_string();
    stage.insert_layer(&root, 0, sub, sdf::LayerOffset::IDENTITY)?;
    let count = Rc::new(Cell::new(0u32));
    let _token = {
        let count = count.clone();
        stage.add_sink(RecordingSink {
            edit_target: Some(Box::new(move |_stage| count.set(count.get() + 1))),
            ..Default::default()
        })
    };
    stage.set_edit_target(EditTarget::for_layer(sub_id.clone()))?;
    assert_eq!(count.get(), 1);
    stage.set_edit_target(EditTarget::for_layer(sub_id))?;
    assert_eq!(count.get(), 1);
    Ok(())
}

/// An `EditContext` fires `EditTargetChanged` on both entry and restore, so a
/// listener tracking the edit target stays consistent across the scope.
#[test]
fn listener_edit_context_restore() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.root_layer().identifier().to_string();
    let sub = sdf::Layer::new_anonymous("sub.usda");
    let sub_id = sub.identifier().to_string();
    stage.insert_layer(&root, 0, sub, sdf::LayerOffset::IDENTITY)?;
    let count = Rc::new(Cell::new(0u32));
    let _token = {
        let count = count.clone();
        stage.add_sink(RecordingSink {
            edit_target: Some(Box::new(move |_stage| count.set(count.get() + 1))),
            ..Default::default()
        })
    };
    {
        let _ctx = stage.edit_context(EditTarget::for_layer(sub_id))?;
        assert_eq!(count.get(), 1); // entry fired
    } // drop restores the previous target → fires again
    assert_eq!(count.get(), 2);
    Ok(())
}

/// Muting and unmuting a layer deliver `LayerMutingChanged` with the changed
/// identifiers; a redundant mute/unmute fires nothing.
#[test]
fn listener_layer_muting() -> Result<()> {
    let stage = in_memory_stage()?;
    let muted = Rc::new(RefCell::new(Vec::<String>::new()));
    let unmuted = Rc::new(RefCell::new(Vec::<String>::new()));
    let _token = {
        let (muted, unmuted) = (muted.clone(), unmuted.clone());
        stage.add_sink(RecordingSink {
            muting: Some(Box::new(move |_stage, layer, is_muted| {
                if is_muted {
                    muted.borrow_mut().push(layer.to_string());
                } else {
                    unmuted.borrow_mut().push(layer.to_string());
                }
            })),
            ..Default::default()
        })
    };
    stage.mute_layer("weak.usda");
    stage.mute_layer("weak.usda"); // already muted — no notice
    stage.unmute_layer("weak.usda");
    stage.unmute_layer("weak.usda"); // already unmuted — no notice
    assert_eq!(*muted.borrow(), vec!["weak.usda".to_string()]);
    assert_eq!(*unmuted.borrow(), vec!["weak.usda".to_string()]);
    Ok(())
}

/// After `remove_sink`, no further changes are delivered.
#[test]
fn unset_stops_delivery() -> Result<()> {
    let stage = in_memory_stage()?;
    let count = Rc::new(Cell::new(0u32));
    let id = {
        let count = count.clone();
        stage.add_sink(move |_: &Stage, _: &CommittedChange<'_>| count.set(count.get() + 1))
    };
    stage.define_prim("/A")?;
    assert_eq!(count.get(), 1);
    stage.remove_sink(id);
    stage.define_prim("/B")?;
    assert_eq!(count.get(), 1);
    Ok(())
}

/// A layer sink's `before_commit` sees the staged edit — the edited layer, its
/// non-empty overlay, and the derived change record — before the overlay
/// commits, fired by an edit routed through the stage.
#[test]
fn layer_sink_sees_staged() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.root_layer().identifier().to_string();
    let seen = Rc::new(RefCell::new(String::new()));
    let staged = Rc::new(Cell::new(false));
    {
        let (seen, staged) = (seen.clone(), staged.clone());
        stage
            .layer_mut(&root)
            .expect("root layer")
            .add_sink(RecordingLayerSink {
                before: Some(Box::new(move |change| {
                    seen.replace(change.layer_identifier.to_string());
                    if !change.overlay.is_empty() && !change.change_list.is_empty() {
                        staged.set(true);
                    }
                    Ok(())
                })),
                ..Default::default()
            });
    }
    stage.define_prim("/World")?;
    assert_eq!(*seen.borrow(), root, "before_commit saw the edited layer");
    assert!(
        staged.get(),
        "the staged overlay and change list are populated pre-commit"
    );
    Ok(())
}

/// A layer sink's `before_commit` rejection aborts the edit: the error surfaces
/// as [`StageAuthoringError::Rejected`] and the staged change rolls back,
/// leaving the prim uncreated.
#[test]
fn layer_sink_veto_rolls_back() -> Result<()> {
    let stage = in_memory_stage()?;
    let root = stage.root_layer().identifier().to_string();
    stage
        .layer_mut(&root)
        .expect("root layer")
        .add_sink(RecordingLayerSink {
            before: Some(Box::new(|_change| {
                Err(sdf::sink::Error::new("policy forbids this edit"))
            })),
            ..Default::default()
        });
    let result = stage.define_prim("/World");
    assert!(matches!(result, Err(StageAuthoringError::Rejected(_))));
    assert!(!stage.prim("/World").is_valid()?, "the rejected edit rolled back");
    Ok(())
}

/// A batched namespace edit delivers one composed `after_commit` for the whole
/// batch, and a dry run fires nothing.
#[test]
fn namespace_edit_fires_sink() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A/B")?;
    let after = Rc::new(Cell::new(0u32));
    {
        let after = after.clone();
        stage.add_sink(move |_: &Stage, _: &CommittedChange<'_>| after.set(after.get() + 1));
    }
    let mut editor = usd::NamespaceEditor::new(&stage);
    editor.delete_prim("/A/B");
    // A dry run proves the batch applies but commits nothing — no sink fires.
    editor.can_apply().unwrap();
    assert_eq!(after.get(), 0, "a dry run does not reach after_commit");
    editor.apply()?;
    assert_eq!(after.get(), 1, "the namespace edit delivered after_commit once");
    assert!(!stage.prim("/A/B").is_valid()?);
    Ok(())
}

/// A layer sink's veto on any layer aborts a multi-layer namespace edit
/// wholesale: every layer rolls back, leaving the composed scene untouched.
#[test]
fn namespace_edit_veto_atomic() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A/B")?;
    let root = stage.root_layer().identifier().to_string();
    stage
        .layer_mut(&root)
        .expect("root layer")
        .add_sink(RecordingLayerSink {
            before: Some(Box::new(|_| Err(sdf::sink::Error::new("locked")))),
            ..Default::default()
        });
    let mut editor = usd::NamespaceEditor::new(&stage);
    editor.delete_prim("/A/B");
    assert!(matches!(
        editor.apply(),
        Err(usd::NamespaceEditError::Stage(StageAuthoringError::Rejected(_)))
    ));
    assert!(stage.prim("/A/B").is_valid()?, "the vetoed batch left the prim intact");
    Ok(())
}

/// An edit authored through a `Prim` handle (not a `Stage` method) still fires
/// the sink — capture is stage-level, not method-level.
#[test]
fn sink_handle_edit_fires() -> Result<()> {
    let stage = in_memory_stage()?;
    let prim = stage.define_prim("/World")?;
    let count = Rc::new(Cell::new(0u32));
    {
        let count = count.clone();
        stage.add_sink(move |_: &Stage, _: &CommittedChange<'_>| count.set(count.get() + 1));
    }
    prim.set_type_name("Xform")?;
    assert_eq!(count.get(), 1, "a handle edit reaches the stage's sink");
    Ok(())
}

/// A sink observes only edits committed after it was installed; a prior edit is
/// not replayed to it.
#[test]
fn sink_only_sees_edits_after_install() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/Before")?;
    let count = Rc::new(Cell::new(0u32));
    {
        let count = count.clone();
        stage.add_sink(move |_: &Stage, _: &CommittedChange<'_>| count.set(count.get() + 1));
    }
    stage.define_prim("/After")?;
    assert_eq!(count.get(), 1, "only the post-install edit is observed");
    Ok(())
}

/// A layer-stack-significant edit (here `timeCodesPerSecond`) drops every
/// cached index, so the notice reports a stage-wide resync at the pseudo-root
/// rather than an empty `resynced`.
#[test]
fn listener_layer_stack_resync() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/World")?;
    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let resynced = resynced.clone();
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            resynced.borrow_mut().extend(oc.resynced.iter().cloned());
        })
    };
    stage.set_time_codes_per_second(48.0)?;
    assert!(resynced.borrow().contains(&sdf::Path::abs_root()));
    Ok(())
}

/// A sink may author another edit from within `after_commit`: the re-entrant
/// authoring tail takes only a snapshot of the sink list (and the other cells
/// are released before the fire), so it does not panic.
#[test]
fn listener_reentrant_author() -> Result<()> {
    let stage = in_memory_stage()?;
    let done = Rc::new(Cell::new(false));
    let _token = {
        let done = done.clone();
        stage.add_sink(move |stage: &Stage, _change: &CommittedChange<'_>| {
            if !done.replace(true) {
                stage.define_prim("/Nested").unwrap();
            }
        })
    };
    stage.define_prim("/World")?;
    assert!(stage.prim("/Nested").is_valid()?);
    Ok(())
}

/// An idempotent author records no change, so the sink does not fire.
#[test]
fn empty_edit_no_fire() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A")?;
    let count = Rc::new(Cell::new(0u32));
    let _token = {
        let count = count.clone();
        stage.add_sink(move |_: &Stage, _: &CommittedChange<'_>| count.set(count.get() + 1))
    };
    stage.define_prim("/A")?;
    assert_eq!(count.get(), 0);
    Ok(())
}

/// `remove_prim` erases the prim spec, drops it from the parent's children, and
/// resyncs its path; a second removal is a no-op.
#[test]
fn remove_prim_drops_spec() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A/B")?;
    assert!(stage.prim("/A/B").is_valid()?);
    let resynced: Rc<RefCell<Vec<sdf::Path>>> = Rc::new(RefCell::new(Vec::new()));
    let _token = {
        let resynced = resynced.clone();
        stage.add_sink(move |_stage: &Stage, oc: &CommittedChange<'_>| {
            resynced.borrow_mut().extend(oc.resynced.iter().cloned());
        })
    };
    assert!(stage.remove_prim("/A/B")?);
    assert!(!stage.prim("/A/B").is_valid()?);
    assert!(!child_names(&stage, "/A")?.contains(&"B".to_string()));
    assert!(resynced.borrow().contains(&sdf::path("/A/B")?));
    // Nothing left to remove.
    assert!(!stage.remove_prim("/A/B")?);
    Ok(())
}

/// `remove_property` erases the attribute spec and drops it from the owning
/// prim's properties; a second removal is a no-op.
#[test]
fn remove_property_drops_spec() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A")?;
    stage.create_attribute("/A.size", "double")?;
    assert!(stage.prim("/A").property_names()?.iter().any(|t| t == "size"));

    assert!(stage.remove_property("/A.size")?);
    assert!(!stage.prim("/A").property_names()?.iter().any(|t| t == "size"));
    assert!(stage.prim("/A").is_valid()?);
    assert!(!stage.remove_property("/A.size")?);
    Ok(())
}

/// Each removal API rejects the wrong path kind rather than crossing into the
/// other: a property path on `remove_prim`, a prim path on `remove_property`.
#[test]
fn remove_rejects_wrong_path_kind() -> Result<()> {
    let stage = in_memory_stage()?;
    stage.define_prim("/A")?;
    stage.create_attribute("/A.size", "double")?;

    assert!(matches!(
        stage.remove_prim("/A.size"),
        Err(StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. }))
    ));
    assert!(matches!(
        stage.remove_property("/A"),
        Err(StageAuthoringError::Layer(sdf::AuthoringError::InvalidPath { .. }))
    ));

    // The rejected calls left both specs intact.
    assert!(stage.prim("/A").is_valid()?);
    assert!(stage.prim("/A").property_names()?.iter().any(|t| t == "size"));
    Ok(())
}
