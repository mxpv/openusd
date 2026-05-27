//! Integration tests for `Stage::value_at` — the universal
//! time-sample evaluator wired through stage composition.

use anyhow::Result;
use openusd::sdf::{path, Value};
use openusd::usd;

const FIXTURE: &str = "fixtures/interp_scene.usda";

fn open() -> Result<usd::Stage> {
    usd::Stage::open(FIXTURE)
}

#[test]
fn default_interpolation_is_linear() -> Result<()> {
    let stage = open()?;
    assert_eq!(stage.interpolation_type(), usd::InterpolationType::Linear);
    Ok(())
}

#[test]
fn linear_double_midpoint() -> Result<()> {
    let stage = open()?;
    let v = stage.value_at(path("/Prim.scalar")?, 5.0)?.unwrap();
    assert_eq!(v, Value::Double(10.0));
    Ok(())
}

#[test]
fn linear_vec3f_componentwise() -> Result<()> {
    let stage = open()?;
    let v = stage.value_at(path("/Prim.vec")?, 5.0)?.unwrap();
    assert_eq!(v, Value::Vec3f([5.0, 10.0, 15.0]));
    Ok(())
}

#[test]
fn linear_quatf_uses_slerp() -> Result<()> {
    let stage = open()?;
    let v = stage.value_at(path("/Prim.rot")?, 5.0)?.unwrap();
    if let Value::Quatf(q) = v {
        let expected_w = std::f32::consts::FRAC_PI_4.cos();
        let expected_x = std::f32::consts::FRAC_PI_4.sin();
        assert!((q[0] - expected_w).abs() < 1e-5, "w: {q:?}");
        assert!((q[1] - expected_x).abs() < 1e-5, "x: {q:?}");
        assert!(q[2].abs() < 1e-5);
        assert!(q[3].abs() < 1e-5);
    } else {
        panic!("expected Quatf, got {v:?}");
    }
    Ok(())
}

#[test]
fn unsupported_type_falls_back_to_held() -> Result<()> {
    let stage = open()?;
    // Token in linear mode → spec mandates held fallback. The USDA
    // parser stores `token` values as `Value::String`; either way it
    // isn't in §12.5.2's linear-supported set.
    let v = stage.value_at(path("/Prim.label")?, 5.0)?.unwrap();
    match v {
        Value::Token(s) | Value::String(s) => assert_eq!(s, "alpha"),
        other => panic!("expected token/string `alpha`, got {other:?}"),
    }
    Ok(())
}

#[test]
fn held_mode_returns_previous_sample() -> Result<()> {
    let stage = open()?;
    stage.set_interpolation_type(usd::InterpolationType::Held);
    let v = stage.value_at(path("/Prim.scalar")?, 5.0)?.unwrap();
    // Previous sample is at t=0 with value 0.0.
    assert_eq!(v, Value::Double(0.0));
    Ok(())
}

#[test]
fn blocked_sample_returns_none() -> Result<()> {
    let stage = open()?;
    // Bracketing pair includes a ValueBlock — Stage::value_at returns None.
    assert!(stage.value_at(path("/Prim.blocked")?, 5.0)?.is_none());
    // At the blocked sample itself.
    assert!(stage.value_at(path("/Prim.blocked")?, 10.0)?.is_none());
    Ok(())
}

#[test]
fn before_first_sample_clamps() -> Result<()> {
    let stage = open()?;
    let v = stage.value_at(path("/Prim.scalar")?, -100.0)?.unwrap();
    assert_eq!(v, Value::Double(0.0));
    Ok(())
}

#[test]
fn after_last_sample_clamps() -> Result<()> {
    let stage = open()?;
    let v = stage.value_at(path("/Prim.scalar")?, 100.0)?.unwrap();
    assert_eq!(v, Value::Double(20.0));
    Ok(())
}

#[test]
fn falls_back_to_default_when_no_timesamples() -> Result<()> {
    let stage = open()?;
    let v = stage.value_at(path("/Prim.static")?, 5.0)?.unwrap();
    assert_eq!(v, Value::Double(42.0));
    Ok(())
}

#[test]
fn set_interpolation_type_via_builder() -> Result<()> {
    let stage = usd::Stage::builder()
        .interpolation_type(usd::InterpolationType::Held)
        .open(FIXTURE)?;
    assert_eq!(stage.interpolation_type(), usd::InterpolationType::Held);
    let v = stage.value_at(path("/Prim.scalar")?, 5.0)?.unwrap();
    assert_eq!(v, Value::Double(0.0));
    Ok(())
}
