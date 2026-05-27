//! Reader functions for the [UsdGeom](super) schema family.
//!
//! This commit covers the *cross-cutting* readers — visibility,
//! purpose, extent, proxyPrim, kind — which apply to every concrete
//! UsdGeom prim. Per-shape readers (Mesh, Cube, Camera, …) land in
//! follow-up commits.

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read `visibility` on an Imageable prim. Returns
/// [`Visibility::Inherited`] when unauthored — that's the spec
/// default. This reader sees only the value authored *directly* on
/// `prim`; consumers that need the effective composed visibility
/// (taking ancestor `invisible` opinions into account) walk
/// ancestors with [`compute_visibility`].
pub fn read_visibility(stage: &Stage, prim: &Path) -> Result<Visibility> {
    Ok(read_token(stage, prim, A_VISIBILITY)?
        .as_deref()
        .and_then(Visibility::from_token)
        .unwrap_or_default())
}

/// Resolve the effective `visibility` for `prim` per the UsdGeom
/// inheritance rule: an `invisible` opinion on any ancestor prunes
/// the subtree. Returns [`Visibility::Invisible`] when any ancestor
/// (including `prim` itself) authors `invisible`, otherwise
/// [`Visibility::Inherited`].
pub fn compute_visibility(stage: &Stage, prim: &Path) -> Result<Visibility> {
    let mut cur = prim.clone();
    loop {
        if read_visibility(stage, &cur)? == Visibility::Invisible {
            return Ok(Visibility::Invisible);
        }
        if cur.as_str() == "/" {
            return Ok(Visibility::Inherited);
        }
        match cur.parent() {
            Some(p) => cur = p,
            None => return Ok(Visibility::Inherited),
        }
    }
}

/// Read `purpose` on an Imageable prim. Returns [`Purpose::Default`]
/// when unauthored. Sees only the direct opinion; use
/// [`compute_purpose`] for the inherited value.
pub fn read_purpose(stage: &Stage, prim: &Path) -> Result<Purpose> {
    Ok(read_token(stage, prim, A_PURPOSE)?
        .as_deref()
        .and_then(Purpose::from_token)
        .unwrap_or_default())
}

/// Resolve the effective `purpose` for `prim`. Per the UsdGeom spec,
/// purpose is inherited from the closest ancestor with an authored
/// opinion; `default` is the fallback when no ancestor authors one.
pub fn compute_purpose(stage: &Stage, prim: &Path) -> Result<Purpose> {
    let mut cur = prim.clone();
    loop {
        if let Some(token) = read_token(stage, &cur, A_PURPOSE)? {
            if let Some(p) = Purpose::from_token(&token) {
                return Ok(p);
            }
        }
        if cur.as_str() == "/" {
            return Ok(Purpose::Default);
        }
        match cur.parent() {
            Some(p) => cur = p,
            None => return Ok(Purpose::Default),
        }
    }
}

/// Read `extent` on a Boundable prim. The attribute is authored as
/// `float3[2]` — `[min, max]` corners in the prim's local space.
/// Returns `None` when unauthored (consumer is expected to compute
/// a bound from the prim's geometry attributes in that case).
pub fn read_extent(stage: &Stage, prim: &Path) -> Result<Option<[[f32; 3]; 2]>> {
    let arr = read_vec3f_vec(stage, prim, A_EXTENT)?;
    Ok(if arr.len() >= 2 { Some([arr[0], arr[1]]) } else { None })
}

/// Read the `proxyPrim` relationship target — the proxy-purpose prim
/// linked from a render-purpose prim. Returns `None` when unauthored.
pub fn read_proxy_prim(stage: &Stage, prim: &Path) -> Result<Option<String>> {
    read_rel_first_target(stage, prim, REL_PROXY_PRIM)
}

/// Read the `kind` metadata authored on `prim` (model hierarchy
/// classification — `"component" / "assembly" / "group" / "subcomponent"`
/// or a custom token). Returns `None` when unauthored.
pub fn read_kind(stage: &Stage, prim: &Path) -> Result<Option<String>> {
    stage.field::<String>(prim.clone(), FieldKey::Kind)
}

/// Walk the entire stage once and return categorised path lists for
/// every UsdGeom prim type the reader recognises. Saves callers from
/// re-walking the stage for each schema family.
///
/// `imageables` is the union — every prim with a recognised
/// `typeName` lands there *plus* any prim that authors a `visibility`
/// or `purpose` opinion (the second clause catches Imageable
/// subclasses we don't otherwise enumerate, like lights, which inherit
/// Imageable but live in UsdLux).
pub fn find_geom_prims(stage: &Stage) -> Result<GeomPrims> {
    let mut out = GeomPrims::default();
    stage.traverse(|path| {
        let p = path.as_str().to_string();
        let mut counted = false;
        if let Ok(Some(type_name)) = stage.type_name(path) {
            match type_name.as_str() {
                T_XFORM => {
                    out.xforms.push(p.clone());
                    counted = true;
                }
                T_SCOPE => {
                    out.scopes.push(p.clone());
                    counted = true;
                }
                T_MESH => {
                    out.meshes.push(p.clone());
                    counted = true;
                }
                T_CUBE => {
                    out.cubes.push(p.clone());
                    counted = true;
                }
                T_SPHERE => {
                    out.spheres.push(p.clone());
                    counted = true;
                }
                T_CYLINDER => {
                    out.cylinders.push(p.clone());
                    counted = true;
                }
                T_CAPSULE => {
                    out.capsules.push(p.clone());
                    counted = true;
                }
                T_CONE => {
                    out.cones.push(p.clone());
                    counted = true;
                }
                T_PLANE => {
                    out.planes.push(p.clone());
                    counted = true;
                }
                T_BASIS_CURVES => {
                    out.basis_curves.push(p.clone());
                    counted = true;
                }
                T_NURBS_CURVES => {
                    out.nurbs_curves.push(p.clone());
                    counted = true;
                }
                T_NURBS_PATCH => {
                    out.nurbs_patches.push(p.clone());
                    counted = true;
                }
                T_HERMITE_CURVES => {
                    out.hermite_curves.push(p.clone());
                    counted = true;
                }
                T_POINTS => {
                    out.points.push(p.clone());
                    counted = true;
                }
                T_TET_MESH => {
                    out.tet_meshes.push(p.clone());
                    counted = true;
                }
                T_GEOM_SUBSET => {
                    out.geom_subsets.push(p.clone());
                    counted = true;
                }
                T_CAMERA => {
                    out.cameras.push(p.clone());
                    counted = true;
                }
                T_POINT_INSTANCER => {
                    out.point_instancers.push(p.clone());
                    counted = true;
                }
                _ => {}
            }
        }
        // Only Token / String opinions count — visibility / purpose
        // are uniform token attributes per the schema. Other Value
        // types (e.g. accidentally authored `bool visibility = false`)
        // are ignored by read_visibility / read_purpose, so the walker
        // mustn't treat them as imageable opinions either.
        let has_imageable_opinion = counted
            || matches!(read_token(stage, path, A_VISIBILITY), Ok(Some(_)))
            || matches!(read_token(stage, path, A_PURPOSE), Ok(Some(_)));
        if has_imageable_opinion {
            out.imageables.push(p);
        }
    })?;
    Ok(out)
}

// ────────────────────────────────────────────────────────────────────────
// internal value helpers
// ────────────────────────────────────────────────────────────────────────

fn read_attr_default(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    let attr_path = prim.append_property(name)?;
    stage.field::<Value>(attr_path, FieldKey::Default)
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::Token(s)) | Some(Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_vec3f_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Vec<[f32; 3]>> {
    Ok(match read_attr_default(stage, prim, name)? {
        Some(Value::Vec3fVec(v)) => v,
        Some(Value::Vec3dVec(v)) => v.into_iter().map(|a| [a[0] as f32, a[1] as f32, a[2] as f32]).collect(),
        Some(Value::Vec3hVec(v)) => v
            .into_iter()
            .map(|a| [a[0].to_f32(), a[1].to_f32(), a[2].to_f32()])
            .collect(),
        _ => Vec::new(),
    })
}

fn read_rel_first_target(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    let rel_path = prim.append_property(rel_name)?;
    let raw = stage.field::<Value>(rel_path, "targetPaths")?;
    let paths = match raw {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    };
    Ok(paths.into_iter().next().map(|p| p.as_str().to_string()))
}
