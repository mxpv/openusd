//! Backport of the AOUSD value-resolution compliance suite
//! (`vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/
//! test_value_resolution.py`).
//!
//! The reference suite hardcodes its expectations inline rather than shipping
//! JSON baselines, so each `test_*` method is transcribed here against the
//! `usd::Stage` value-resolution surface (`Attribute::get_at`, composed
//! `default` reads, and `Stage::set_interpolation`).
//!
//! The reference's `ValueResolutionProcess` return names the tier that
//! answered. Here that is [`process`], read from
//! `Attribute::resolve_info_at`.
//!
//! Fallbacks (spec 12.3.5, 13.3.2.4). A value no layer authors resolves
//! through the prim definition's fallbacks, and past them to the fallback
//! of the `default` field itself, the empty sentinel. The reference asserts
//! that tier (`ValueResolutionProcess.Fallback`) and returns a placeholder
//! `0.0` it does not assert. The fixtures' `XForm` is no schema type, so the
//! tier answers with the sentinel: no value. `fallback_tier` reads a
//! fallback a definition does supply.
//!
//! Splines (spec 12.5.3). The reference names the tier
//! (`ValueResolutionProcess.Splines`, between time samples and the default)
//! and stubs its evaluation, with no fixture. `spline_tier` holds the core
//! to that order; `tests/splines.rs` and `tests/spline_eval.rs` cover the
//! evaluation.

use std::fs;

use openusd::Result;
use openusd::sdf::path;
use openusd::usd::{self, ResolveInfoSource};
use openusd::vt::Value;

const ASSETS: &str = concat!(
    env!("CARGO_WORKSPACE_DIR"),
    "vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets"
);

fn open(name: &str) -> Result<usd::Stage> {
    usd::Stage::open(&format!("{ASSETS}/{name}/entry.usd"))
}

/// Pulls a scalar `f64` out of a `float`/`double` value for comparison.
fn scalar(v: Option<Value>) -> Option<f64> {
    match v {
        Some(Value::Float(x)) => Some(x as f64),
        Some(Value::Double(x)) => Some(x),
        _ => None,
    }
}

/// The tier that answers a read, as the reference's
/// `ValueResolutionProcess` names it.
#[derive(Debug, PartialEq)]
enum Process {
    Default,
    TimeSamples,
    Splines,
    ValueClips,
    /// No authored tier answers: the prim definition's fallback does, or
    /// past it the empty sentinel of the `default` field.
    Fallback,
}

/// The tier that answers a read of `attr` at `time`, the default time where
/// it is `None`.
fn process(stage: &usd::Stage, attr: &str, time: Option<f64>) -> Result<Process> {
    let info = stage.attribute(attr)?.resolve_info_at(time.map(usd::TimeCode::new))?;
    Ok(match info.source() {
        ResolveInfoSource::Default => Process::Default,
        ResolveInfoSource::TimeSamples => Process::TimeSamples,
        ResolveInfoSource::Spline => Process::Splines,
        ResolveInfoSource::ValueClips => Process::ValueClips,
        ResolveInfoSource::Fallback | ResolveInfoSource::None => Process::Fallback,
    })
}

fn value_at(stage: &usd::Stage, attr: &str, time: f64) -> Option<f64> {
    scalar(
        stage
            .attribute(attr)
            .unwrap()
            .get_at::<Value>(usd::TimeCode::new(time))
            .expect("value_at"),
    )
}

/// `test_default`: at the default time code the composed `default` opinion
/// wins, even though `timeSamples` are also authored on the attribute.
#[test]
fn default_opinion() -> Result<()> {
    let stage = open("default")?;
    let default = stage.prim(path("/Root")?)?.attribute("root").get::<Value>()?;
    assert_eq!(scalar(default), Some(2.0));
    Ok(())
}

/// `test_timesamples`: linear interpolation, end clamping, and held mode over
/// `timeSamples = {1: 5, 30: 10, 40: 15}`.
#[test]
fn timesamples_linear() -> Result<()> {
    let stage = open("timesamples")?;
    assert_eq!(value_at(&stage, "/Root.root", 1.0), Some(5.0));
    assert_eq!(value_at(&stage, "/Root.root", 40.0), Some(15.0));

    // Between samples 1 (→5) and 30 (→10): strictly inside (5, 10).
    let mid = value_at(&stage, "/Root.root", 15.0).expect("interpolated");
    assert!(mid > 5.0 && mid < 10.0, "expected (5, 10), got {mid}");

    // Out of range clamps to the nearest end sample.
    assert_eq!(value_at(&stage, "/Root.root", 60.0), Some(15.0));
    assert_eq!(value_at(&stage, "/Root.root", 0.5), Some(5.0));
    Ok(())
}

/// `test_interpolationType`: interpolation is linear until it is set, and
/// held once it is.
#[test]
fn interpolation_type() -> Result<()> {
    let stage = open("timesamples")?;
    assert_eq!(stage.interpolation(), usd::InterpolationType::Linear);
    stage.set_interpolation(usd::InterpolationType::Held);
    assert_eq!(stage.interpolation(), usd::InterpolationType::Held);
    Ok(())
}

/// `test_timesamples` (fallback branch): a read at the default time when no
/// default is authored is answered by the fallback tier. The samples answer
/// a time, and not the default time.
#[test]
fn timesamples_fallback() -> Result<()> {
    let stage = open("timesamples")?;
    assert_eq!(process(&stage, "/Root.root", None)?, Process::Fallback);
    assert_eq!(process(&stage, "/Root.root", Some(15.0))?, Process::TimeSamples);

    // No definition declares `root`, so the tier answers with the empty
    // sentinel, and the samples are still an authored opinion.
    let attr = stage.attribute("/Root.root")?;
    assert_eq!(attr.get::<Value>()?, None);
    assert!(attr.resolve_info_at(None)?.has_authored_value_opinion());
    Ok(())
}

/// The `fallback` fixture: a prim with no attribute at all. Nothing authors
/// `root` and no definition declares it, so it has no value at any time.
#[test]
fn fallback_unauthored() -> Result<()> {
    let stage = open("fallback")?;
    assert!(stage.prim(path("/Root")?)?.is_valid()?);
    let attr = stage.attribute("/Root.root")?;
    assert_eq!(attr.get::<Value>()?, None);
    assert_eq!(value_at(&stage, "/Root.root", 1.0), None);
    assert_eq!(process(&stage, "/Root.root", None)?, Process::Fallback);
    assert_eq!(process(&stage, "/Root.root", Some(1.0))?, Process::Fallback);
    assert!(!attr.resolve_info()?.has_authored_value_opinion());
    Ok(())
}

/// Spec 12.2.8: an attribute no layer authors resolves to the fallback its
/// prim definition supplies, at the default time and at any other, and an
/// authored opinion answers before it.
#[test]
fn fallback_tier() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    fs::write(
        &root,
        "#usda 1.0\ndef \"Root\" (\n    prepend apiSchemas = [\"CollectionAPI:all\"]\n)\n{\n}\n",
    )?;
    let stage = usd::Stage::open(root.to_str().expect("a UTF-8 path"))?;
    let attr = stage.attribute("/Root.collection:all:expansionRule")?;

    let fallback = Value::token("expandPrims");
    assert_eq!(attr.get::<Value>()?, Some(fallback.clone()));
    assert_eq!(attr.get_at::<Value>(usd::TimeCode::new(15.0))?, Some(fallback));
    assert_eq!(attr.resolve_info()?.source(), ResolveInfoSource::Fallback);
    assert_eq!(
        attr.resolve_info_at(usd::TimeCode::new(15.0))?.source(),
        ResolveInfoSource::Fallback
    );

    let attr = attr.set(Value::token("explicitOnly"))?;
    assert_eq!(attr.get::<Value>()?, Some(Value::token("explicitOnly")));
    assert_eq!(attr.resolve_info()?.source(), ResolveInfoSource::Default);
    Ok(())
}

/// Spec 12.5.3, in the reference's order of tiers: at a time, a spec's time
/// samples answer, then its spline, then its default; at the default time
/// the default alone answers.
#[test]
fn spline_tier() -> Result<()> {
    let dir = tempfile::tempdir()?;
    let root = dir.path().join("root.usda");
    let curve = "{ bezier, 0: 0; post curve (2, 0), 8: 16; pre (2, 0) }";
    fs::write(
        &root,
        format!(
            "#usda 1.0\ndef XForm \"Root\"\n{{\n    \
             float root = 2\n    float root.spline = {curve}\n    \
             float sampled = 2\n    float sampled.timeSamples = {{ 1: 5, 30: 10 }}\n    float sampled.spline = {curve}\n}}\n"
        ),
    )?;
    let stage = usd::Stage::open(root.to_str().expect("a UTF-8 path"))?;
    let source = |attr: &str, time: Option<f64>| -> Result<ResolveInfoSource> {
        let time = time.map(usd::TimeCode::new);
        Ok(stage.attribute(attr)?.resolve_info_at(time)?.source())
    };

    // The spline: its knots' values at the knots, a symmetric ease between
    // them, and the end values held outside.
    assert_eq!(value_at(&stage, "/Root.root", 0.0), Some(0.0));
    assert_eq!(value_at(&stage, "/Root.root", 4.0), Some(8.0));
    assert_eq!(value_at(&stage, "/Root.root", 8.0), Some(16.0));
    assert_eq!(value_at(&stage, "/Root.root", 60.0), Some(16.0));
    let eased = value_at(&stage, "/Root.root", 1.0).expect("a value on the curve");
    assert!(
        eased > 0.0 && eased < 2.0,
        "eased in below the straight line, got {eased}"
    );
    assert_eq!(source("/Root.root", Some(4.0))?, ResolveInfoSource::Spline);

    // The default answers the default time.
    let default = stage.attribute("/Root.root")?.get::<Value>()?;
    assert_eq!(scalar(default), Some(2.0));
    assert_eq!(source("/Root.root", None)?, ResolveInfoSource::Default);

    // Time samples answer before the spline does.
    assert_eq!(value_at(&stage, "/Root.sampled", 1.0), Some(5.0));
    assert_eq!(source("/Root.sampled", Some(4.0))?, ResolveInfoSource::TimeSamples);
    Ok(())
}

/// `test_timesamples` (held branch): held mode returns the nearest previous
/// authored sample.
#[test]
fn timesamples_held() -> Result<()> {
    let stage = open("timesamples")?;
    stage.set_interpolation(usd::InterpolationType::Held);
    assert_eq!(value_at(&stage, "/Root.root", 15.0), Some(5.0));
    assert_eq!(value_at(&stage, "/Root.root", 30.0), Some(10.0));
    Ok(())
}

/// `test_clip_basic`: a clip overrides a referenced attribute that has no local
/// opinion — `size` reads the clip's `size = stageTime` (spec 12.3.4.5).
#[test]
fn clip_basic() -> Result<()> {
    let stage = open("clip_basic")?;
    assert_eq!(value_at(&stage, "/Model.size", 0.0), Some(0.0));
    assert_eq!(value_at(&stage, "/Model.size", 5.0), Some(5.0));
    Ok(())
}

/// `test_clip_advanced`: a stronger local opinion beats the clip, while a clip
/// beats a weaker referenced opinion (spec 12.3.4.5).
#[test]
fn clip_advanced() -> Result<()> {
    let stage = open("clip_advanced")?;

    // `local` has a stronger local opinion → values come from the root layer.
    assert_eq!(value_at(&stage, "/Model.local", 0.0), Some(0.0));
    assert_eq!(value_at(&stage, "/Model.local", 5.0), Some(5.0));
    assert_eq!(value_at(&stage, "/Model.local", 10.0), Some(10.0));
    assert_eq!(value_at(&stage, "/Model.local", 15.0), Some(15.0));
    assert_eq!(value_at(&stage, "/Model.local", 20.0), Some(20.0));
    assert_eq!(value_at(&stage, "/Model.local", 25.0), Some(20.0)); // clamped

    // `ref` is authored on a weaker layer → the clip's negative values win.
    assert_eq!(value_at(&stage, "/Model.ref", 0.0), Some(0.0));
    assert_eq!(value_at(&stage, "/Model.ref", 5.0), Some(-5.0));
    assert_eq!(value_at(&stage, "/Model.ref", 10.0), Some(-10.0));
    assert_eq!(value_at(&stage, "/Model.ref", 20.0), Some(-20.0));
    assert_eq!(value_at(&stage, "/Model.ref", 25.0), Some(-25.0));
    assert_eq!(value_at(&stage, "/Model.ref", 30.0), Some(-25.0)); // out of clip range
    Ok(())
}

/// `test_clip_sets`: with no authored `clipSets` order, sets resolve in name
/// order — `clip_a` outranks `clip_b` despite `clip_b` appearing first
/// (spec 12.3.4.1).
#[test]
fn clip_sets() -> Result<()> {
    let stage = open("clip_sets")?;
    assert_eq!(value_at(&stage, "/DefaultOrderTest.attr", 0.0), Some(10.0));
    assert_eq!(value_at(&stage, "/DefaultOrderTest.attr", 1.0), Some(20.0));
    assert_eq!(value_at(&stage, "/DefaultOrderTest.attr", 2.0), Some(30.0));
    Ok(())
}

/// `test_clip_multi`: `active` switches between two clips, and the timing curve
/// jump at the clip boundary selects clip1 just before stage 16 and clip2 at
/// stage 16 (spec 12.3.4.3, 12.3.4.8). The reference uses `timeCode.safe_step`
/// to land just before the jump; here that is stage time `16 - epsilon`.
#[test]
fn clip_multi() -> Result<()> {
    let stage = open("clip_multi")?;
    let round1 = |t: f64| (value_at(&stage, "/Model_1.size", t).unwrap() * 10.0).round() / 10.0;

    assert_eq!(round1(5.0), -5.0);
    assert_eq!(round1(10.0), -10.0);
    // Just before the clip boundary at stage 16 → still clip1.
    assert_eq!(round1(16.0 - 1e-9), -15.0);
    // At stage 16 → clip2, which maps to clip time 0.
    assert_eq!(round1(16.0), -23.0);
    assert_eq!(round1(19.0), -23.0);
    assert_eq!(round1(22.0), -26.0);
    assert_eq!(round1(25.0), -29.0);
    Ok(())
}

/// `test_clip_timings`: the stage-to-clip timing curve, including the jump
/// discontinuity at stage 20 (spec 12.3.4.4, 12.3.4.8).
///
/// The in-range expectations are transcribed verbatim. The reference's
/// out-of-range expectations (`50 → 25`, `-1 → 0`) are NOT reproduced: they
/// stem from a bug in the sample implementation's `map_stagetime_to_cliptime`,
/// which returns the stage time (pair element 0) instead of the boundary clip
/// time (element 1) for out-of-range queries — contradicting its own comment
/// ("return the first available clip time"). Per spec 12.3.4.4 the curve clamps
/// to the boundary clip time, so the core returns the clip time at stage 40
/// (`20`) and stage 0 (`10`) respectively.
#[test]
fn clip_timings() -> Result<()> {
    let stage = open("clip_timings")?;
    let round1 = |t: f64| (value_at(&stage, "/Model.size", t).unwrap() * 10.0).round() / 10.0;

    assert_eq!(round1(0.0), 10.0);
    assert_eq!(round1(15.0), 17.5);
    assert_eq!(round1(30.0), 15.0);
    assert_eq!(round1(40.0), 20.0);
    // Out of range clamps to the boundary clip time (spec 12.3.4.4), not the
    // reference's buggy stage-time pass-through (which yields 25 / 0).
    assert_eq!(round1(50.0), 20.0); // out of range high → clip time at stage 40
    assert_eq!(round1(-1.0), 10.0); // out of range low → clip time at stage 0
    Ok(())
}
