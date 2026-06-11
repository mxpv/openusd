//! Backport of the AOUSD value-resolution compliance suite
//! (`vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/
//! test_value_resolution.py`).
//!
//! The reference suite hardcodes its expectations inline rather than shipping
//! JSON baselines, so each `test_*` method is transcribed here against the
//! `usd::Stage` value-resolution surface (`Attribute::get_at`, composed
//! `default` reads, and `Stage::set_interpolation_type`).
//!
//! Excluded — not yet supported by the core:
//! - Attribute type fallbacks and the reference's `ValueResolutionProcess`
//!   return. The reference returns `(fallbackVal=0.0, Fallback)` for an
//!   attribute with no authored opinion; the core returns `None`. The two
//!   `ValueResolutionProcess.Fallback` assertions in `test_timesamples` and the
//!   `fallback` fixture are therefore omitted.
//! - Spline interpolation (`InterpolationType.Spline`). The reference stubs it
//!   too and no fixture asserts spline values.

use anyhow::Result;
use openusd::sdf::{path, Value};
use openusd::usd;

const ASSETS: &str = "vendor/core-spec-supplemental-release_dec2025/value_resolution/tests/assets";

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

fn value_at(stage: &usd::Stage, attr: &str, time: f64) -> Option<f64> {
    scalar(
        stage
            .attribute_at(path(attr).unwrap())
            .get_at::<Value>(usd::TimeCode::new(time))
            .expect("value_at"),
    )
}

/// `test_default`: at the default time code the composed `default` opinion
/// wins, even though `timeSamples` are also authored on the attribute.
#[test]
fn default_opinion() -> Result<()> {
    let stage = open("default")?;
    let default = stage.prim_at(path("/Root")?).attribute("root").get::<Value>()?;
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

/// `test_timesamples` (held branch): held mode returns the nearest previous
/// authored sample.
#[test]
fn timesamples_held() -> Result<()> {
    let stage = open("timesamples")?;
    stage.set_interpolation_type(usd::InterpolationType::Held);
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
