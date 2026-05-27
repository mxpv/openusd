//! Readers for the intrinsic primitive shapes — Cube, Sphere,
//! Cylinder, Capsule, Cone, Plane.
//!
//! Each reader returns the populated struct (or `None` when the
//! prim's `typeName` doesn't match the requested shape). Unauthored
//! attributes fall back to Pixar's documented defaults.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read a `Cube` prim. Returns `None` when the prim isn't typed `Cube`.
pub fn read_cube(stage: &Stage, prim: &Path) -> Result<Option<ReadCube>> {
    if stage.type_name(prim)?.as_deref() != Some(T_CUBE) {
        return Ok(None);
    }
    Ok(Some(ReadCube {
        size: read_double(stage, prim, A_SIZE)?.unwrap_or(2.0),
    }))
}

/// Read a `Sphere` prim. Returns `None` when the prim isn't typed
/// `Sphere`.
pub fn read_sphere(stage: &Stage, prim: &Path) -> Result<Option<ReadSphere>> {
    if stage.type_name(prim)?.as_deref() != Some(T_SPHERE) {
        return Ok(None);
    }
    Ok(Some(ReadSphere {
        radius: read_double(stage, prim, A_RADIUS)?.unwrap_or(1.0),
    }))
}

/// Read a `Cylinder` prim. Returns `None` when the prim isn't typed
/// `Cylinder`.
pub fn read_cylinder(stage: &Stage, prim: &Path) -> Result<Option<ReadCylinder>> {
    if stage.type_name(prim)?.as_deref() != Some(T_CYLINDER) {
        return Ok(None);
    }
    Ok(Some(ReadCylinder {
        radius: read_double(stage, prim, A_RADIUS)?.unwrap_or(1.0),
        height: read_double(stage, prim, A_HEIGHT)?.unwrap_or(2.0),
        axis: read_axis(stage, prim)?,
    }))
}

/// Read a `Capsule` prim. Returns `None` when the prim isn't typed
/// `Capsule`.
pub fn read_capsule(stage: &Stage, prim: &Path) -> Result<Option<ReadCapsule>> {
    if stage.type_name(prim)?.as_deref() != Some(T_CAPSULE) {
        return Ok(None);
    }
    Ok(Some(ReadCapsule {
        radius: read_double(stage, prim, A_RADIUS)?.unwrap_or(0.5),
        height: read_double(stage, prim, A_HEIGHT)?.unwrap_or(1.0),
        axis: read_axis(stage, prim)?,
    }))
}

/// Read a `Cone` prim. Returns `None` when the prim isn't typed `Cone`.
pub fn read_cone(stage: &Stage, prim: &Path) -> Result<Option<ReadCone>> {
    if stage.type_name(prim)?.as_deref() != Some(T_CONE) {
        return Ok(None);
    }
    Ok(Some(ReadCone {
        radius: read_double(stage, prim, A_RADIUS)?.unwrap_or(1.0),
        height: read_double(stage, prim, A_HEIGHT)?.unwrap_or(2.0),
        axis: read_axis(stage, prim)?,
    }))
}

/// Read a `Plane` prim. Returns `None` when the prim isn't typed
/// `Plane`.
pub fn read_plane(stage: &Stage, prim: &Path) -> Result<Option<ReadPlane>> {
    if stage.type_name(prim)?.as_deref() != Some(T_PLANE) {
        return Ok(None);
    }
    Ok(Some(ReadPlane {
        width: read_double(stage, prim, A_WIDTH)?.unwrap_or(2.0),
        length: read_double(stage, prim, A_LENGTH)?.unwrap_or(2.0),
        axis: read_axis(stage, prim)?,
    }))
}

// ────────────────────────────────────────────────────────────────────────
// internal helpers
// ────────────────────────────────────────────────────────────────────────

fn read_axis(stage: &Stage, prim: &Path) -> Result<Axis> {
    let attr = prim.append_property(A_AXIS)?;
    Ok(match stage.field::<Value>(attr, "default")? {
        Some(Value::Token(s) | Value::String(s)) => Axis::from_token(&s).unwrap_or_default(),
        _ => Axis::default(),
    })
}

fn read_double(stage: &Stage, prim: &Path, name: &str) -> Result<Option<f64>> {
    let attr = prim.append_property(name)?;
    Ok(match stage.field::<Value>(attr, "default")? {
        Some(Value::Double(d)) => Some(d),
        Some(Value::Float(f)) => Some(f as f64),
        _ => None,
    })
}
