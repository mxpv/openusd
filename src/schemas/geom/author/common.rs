//! Shared low-level authoring helpers used across the per-prim
//! modules. Wraps [`crate::usd::Stage`]'s public authoring API with
//! default choices that match per-attribute schema declarations in
//! `usdGeom/schema.usda` (variability, type name, custom flag).

#![allow(dead_code)]

use anyhow::Result;

use crate::sdf::{Path, Value, Variability};
use crate::usd::Stage;

pub(super) fn author_token(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token")?
        .set_custom(false)?
        .set(Value::Token(value.into()))?;
    Ok(())
}

pub(super) fn author_uniform_token(stage: &Stage, prim: &Path, name: &str, value: impl Into<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::Token(value.into()))?;
    Ok(())
}

pub(super) fn author_uniform_token_vec(stage: &Stage, prim: &Path, name: &str, tokens: Vec<String>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "token[]")?
        .set_variability(Variability::Uniform)?
        .set_custom(false)?
        .set(Value::TokenVec(tokens))?;
    Ok(())
}

pub(super) fn author_float(stage: &Stage, prim: &Path, name: &str, value: f32) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float")?
        .set_custom(false)?
        .set(Value::Float(value))?;
    Ok(())
}

pub(super) fn author_double(stage: &Stage, prim: &Path, name: &str, value: f64) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "double")?
        .set_custom(false)?
        .set(Value::Double(value))?;
    Ok(())
}

pub(super) fn author_bool(stage: &Stage, prim: &Path, name: &str, value: bool) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "bool")?
        .set_custom(false)?
        .set(Value::Bool(value))?;
    Ok(())
}

pub(super) fn author_int_vec(stage: &Stage, prim: &Path, name: &str, value: Vec<i32>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "int[]")?
        .set_custom(false)?
        .set(Value::IntVec(value))?;
    Ok(())
}

pub(super) fn author_vec3f_array(stage: &Stage, prim: &Path, name: &str, value: Vec<[f32; 3]>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "vector3f[]")?
        .set_custom(false)?
        .set(Value::Vec3fVec(value))?;
    Ok(())
}

pub(super) fn author_point3f_array(stage: &Stage, prim: &Path, name: &str, value: Vec<[f32; 3]>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "point3f[]")?
        .set_custom(false)?
        .set(Value::Vec3fVec(value))?;
    Ok(())
}

pub(super) fn author_color3f_array(stage: &Stage, prim: &Path, name: &str, value: Vec<[f32; 3]>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "color3f[]")?
        .set_custom(false)?
        .set(Value::Vec3fVec(value))?;
    Ok(())
}

pub(super) fn author_float_array(stage: &Stage, prim: &Path, name: &str, value: Vec<f32>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float[]")?
        .set_custom(false)?
        .set(Value::FloatVec(value))?;
    Ok(())
}

pub(super) fn author_double_array(stage: &Stage, prim: &Path, name: &str, value: Vec<f64>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "double[]")?
        .set_custom(false)?
        .set(Value::DoubleVec(value))?;
    Ok(())
}

pub(super) fn author_quatf_array(stage: &Stage, prim: &Path, name: &str, value: Vec<[f32; 4]>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "quatf[]")?
        .set_custom(false)?
        .set(Value::QuatfVec(value))?;
    Ok(())
}

pub(super) fn author_int64_array(stage: &Stage, prim: &Path, name: &str, value: Vec<i64>) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "int64[]")?
        .set_custom(false)?
        .set(Value::Int64Vec(value))?;
    Ok(())
}

pub(super) fn author_vec3f_pair_array(stage: &Stage, prim: &Path, name: &str, value: [[f32; 3]; 2]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float3[]")?
        .set_custom(false)?
        .set(Value::Vec3fVec(vec![value[0], value[1]]))?;
    Ok(())
}

pub(super) fn author_vec3f(stage: &Stage, prim: &Path, name: &str, value: [f32; 3]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "vector3f")?
        .set_custom(false)?
        .set(Value::Vec3f(value))?;
    Ok(())
}

pub(super) fn author_double3(stage: &Stage, prim: &Path, name: &str, value: [f64; 3]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "double3")?
        .set_custom(false)?
        .set(Value::Vec3d(value))?;
    Ok(())
}

pub(super) fn author_float3_scalar(stage: &Stage, prim: &Path, name: &str, value: [f32; 3]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "float3")?
        .set_custom(false)?
        .set(Value::Vec3f(value))?;
    Ok(())
}

pub(super) fn author_float_scalar_named_type(
    stage: &Stage,
    prim: &Path,
    name: &str,
    type_name: &str,
    value: f32,
) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, type_name)?
        .set_custom(false)?
        .set(Value::Float(value))?;
    Ok(())
}

pub(super) fn author_quatf_scalar(stage: &Stage, prim: &Path, name: &str, value: [f32; 4]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "quatf")?
        .set_custom(false)?
        .set(Value::Quatf(value))?;
    Ok(())
}

pub(super) fn author_matrix4d(stage: &Stage, prim: &Path, name: &str, value: [f64; 16]) -> Result<()> {
    let attr_path = prim.append_property(name)?;
    stage
        .create_attribute(attr_path, "matrix4d")?
        .set_custom(false)?
        .set(Value::Matrix4d(value))?;
    Ok(())
}

pub(super) fn author_rel_targets<I, P>(stage: &Stage, prim: &Path, name: &str, targets: I) -> Result<()>
where
    I: IntoIterator<Item = P>,
    P: Into<Path>,
{
    let rel_path = prim.append_property(name)?;
    let paths: Vec<Path> = targets.into_iter().map(Into::into).collect();
    stage
        .create_relationship(rel_path)?
        .set_custom(false)?
        .set_targets(paths)?;
    Ok(())
}
