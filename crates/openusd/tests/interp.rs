//! Integration tests for `Attribute::get_at` — the universal
//! time-sample evaluator wired through stage composition.

use openusd::Result;
use openusd::sdf::path;
use openusd::usd;
use openusd::vt::Value;

const FIXTURE: &str = "fixtures/interp_scene.usda";

fn open() -> Result<usd::Stage> {
    usd::Stage::open(FIXTURE)
}

#[test]
fn default_interpolation_is_linear() -> Result<()> {
    let stage = open()?;
    assert_eq!(stage.interpolation(), usd::InterpolationType::Linear);
    Ok(())
}

#[test]
fn linear_double_midpoint() -> Result<()> {
    let stage = open()?;
    let v = stage
        .attribute(path("/Prim.scalar")?)?
        .get_at::<Value>(usd::TimeCode::new(5.0))?
        .unwrap();
    assert_eq!(v, Value::Double(10.0));
    Ok(())
}

#[test]
fn linear_vec3f_componentwise() -> Result<()> {
    let stage = open()?;
    let v = stage
        .attribute(path("/Prim.vec")?)?
        .get_at::<Value>(usd::TimeCode::new(5.0))?
        .unwrap();
    assert_eq!(v, Value::vec3f(5.0_f32, 10.0, 15.0));
    Ok(())
}

#[test]
fn linear_quatf_uses_slerp() -> Result<()> {
    let stage = open()?;
    let v = stage
        .attribute(path("/Prim.rot")?)?
        .get_at::<Value>(usd::TimeCode::new(5.0))?
        .unwrap();
    if let Value::Quatf(q) = v {
        let expected_w = std::f32::consts::FRAC_PI_4.cos();
        let expected_x = std::f32::consts::FRAC_PI_4.sin();
        assert!((q.w - expected_w).abs() < 1e-5, "w: {q:?}");
        assert!((q.x - expected_x).abs() < 1e-5, "x: {q:?}");
        assert!(q.y.abs() < 1e-5);
        assert!(q.z.abs() < 1e-5);
    } else {
        panic!("expected Quatf, got {v:?}");
    }
    Ok(())
}

#[test]
fn unsupported_type_falls_back_to_held() -> Result<()> {
    let stage = open()?;
    // Token in linear mode → spec mandates held fallback. A `token` value
    // isn't in §12.5.2's linear-supported set.
    let v = stage
        .attribute(path("/Prim.label")?)?
        .get_at::<Value>(usd::TimeCode::new(5.0))?
        .unwrap();
    match v {
        Value::Token(s) => assert_eq!(s.as_str(), "alpha"),
        Value::String(s) => assert_eq!(s, "alpha"),
        other => panic!("expected token/string `alpha`, got {other:?}"),
    }
    Ok(())
}

#[test]
fn held_mode_returns_previous_sample() -> Result<()> {
    let stage = open()?;
    stage.set_interpolation(usd::InterpolationType::Held);
    let v = stage
        .attribute(path("/Prim.scalar")?)?
        .get_at::<Value>(usd::TimeCode::new(5.0))?
        .unwrap();
    // Previous sample is at t=0 with value 0.0.
    assert_eq!(v, Value::Double(0.0));
    Ok(())
}

#[test]
fn blocked_sample_holds() -> Result<()> {
    let stage = open()?;
    let attr = stage.attribute(path("/Prim.blocked")?)?;
    let at = |t: f64| attr.get_at::<Value>(usd::TimeCode::new(t));
    // The block is the later sample: the earlier one holds.
    assert_eq!(at(5.0)?, Some(Value::Double(1.0)));
    // At the block, and between it and the next sample, there is no value.
    assert_eq!(at(10.0)?, None);
    assert_eq!(at(15.0)?, None);
    assert_eq!(at(20.0)?, Some(Value::Double(3.0)));
    Ok(())
}

#[test]
fn before_first_sample_clamps() -> Result<()> {
    let stage = open()?;
    let v = stage
        .attribute(path("/Prim.scalar")?)?
        .get_at::<Value>(usd::TimeCode::new(-100.0))?
        .unwrap();
    assert_eq!(v, Value::Double(0.0));
    Ok(())
}

#[test]
fn after_last_sample_clamps() -> Result<()> {
    let stage = open()?;
    let v = stage
        .attribute(path("/Prim.scalar")?)?
        .get_at::<Value>(usd::TimeCode::new(100.0))?
        .unwrap();
    assert_eq!(v, Value::Double(20.0));
    Ok(())
}

#[test]
fn falls_back_to_default_when_no_timesamples() -> Result<()> {
    let stage = open()?;
    let v = stage
        .attribute(path("/Prim.static")?)?
        .get_at::<Value>(usd::TimeCode::new(5.0))?
        .unwrap();
    assert_eq!(v, Value::Double(42.0));
    Ok(())
}

#[test]
fn set_interpolation_type_via_builder() -> Result<()> {
    let stage = usd::Stage::builder()
        .interpolation(usd::InterpolationType::Held)
        .open(FIXTURE)?;
    assert_eq!(stage.interpolation(), usd::InterpolationType::Held);
    let v = stage
        .attribute(path("/Prim.scalar")?)?
        .get_at::<Value>(usd::TimeCode::new(5.0))?
        .unwrap();
    assert_eq!(v, Value::Double(0.0));
    Ok(())
}
