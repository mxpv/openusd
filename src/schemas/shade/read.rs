//! Readers for the [UsdShade](super) schema family — walk authored
//! shading networks back into typed data.
//!
//! The core operations are connection-following: given a connectable
//! property (`inputs:` / `outputs:`), read its composed value and/or
//! the property it's wired to via `connectionPaths`. Higher-level
//! readers (`read_material`) chase the Material's surface terminal
//! through to the shader that drives it.

use anyhow::Result;

use crate::sdf::{Path, Value};
use crate::usd::Stage;

use super::tokens::{A_INFO_ID, NS_INPUTS, NS_OUTPUTS, TERMINAL_SURFACE, T_MATERIAL, T_NODE_GRAPH, T_SHADER};

/// Composed default value of `inputs:<base>` on `prim`, if authored.
pub fn read_input_value(stage: &Stage, prim: &Path, base: &str) -> Result<Option<Value>> {
    let attr = prim.append_property(&format!("{NS_INPUTS}{base}"))?;
    stage.field::<Value>(attr, "default")
}

/// Composed `connectionPaths` of `inputs:<base>` on `prim`. Empty when
/// the input isn't connected.
pub fn read_input_connections(stage: &Stage, prim: &Path, base: &str) -> Result<Vec<Path>> {
    read_connections(stage, &prim.append_property(&format!("{NS_INPUTS}{base}"))?)
}

/// Composed `connectionPaths` of `outputs:<base>` on `prim`.
pub fn read_output_connections(stage: &Stage, prim: &Path, base: &str) -> Result<Vec<Path>> {
    read_connections(stage, &prim.append_property(&format!("{NS_OUTPUTS}{base}"))?)
}

/// Composed `connectionPaths` of any property path, flattened.
pub fn read_connections(stage: &Stage, attr: &Path) -> Result<Vec<Path>> {
    Ok(match stage.field::<Value>(attr.clone(), "connectionPaths")? {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    })
}

/// List the authored input base names (without the `inputs:` prefix)
/// on `prim`.
pub fn input_names(stage: &Stage, prim: &Path) -> Result<Vec<String>> {
    Ok(stage
        .prim_properties(prim.clone())?
        .into_iter()
        .filter_map(|p| p.strip_prefix(NS_INPUTS).map(str::to_string))
        .collect())
}

/// List the authored output base names (without the `outputs:` prefix)
/// on `prim`.
pub fn output_names(stage: &Stage, prim: &Path) -> Result<Vec<String>> {
    Ok(stage
        .prim_properties(prim.clone())?
        .into_iter()
        .filter_map(|p| p.strip_prefix(NS_OUTPUTS).map(str::to_string))
        .collect())
}

/// Resolve a Material's surface terminal to the Shader prim that drives
/// it. Follows `Material.outputs:surface.connect` to the connected
/// shader output, then returns the owning Shader prim path. Tries the
/// universal render context first, falling back to any authored
/// context-specific `surface` terminal.
///
/// Returns `None` when the prim isn't a Material or no surface terminal
/// is connected.
pub fn resolve_surface_shader(stage: &Stage, material: &Path) -> Result<Option<Path>> {
    if stage.type_name(material)?.as_deref() != Some(T_MATERIAL) {
        return Ok(None);
    }
    // Universal terminal first.
    let universal = material.append_property(&format!("outputs:{TERMINAL_SURFACE}"))?;
    let mut conns = read_connections(stage, &universal)?;
    if conns.is_empty() {
        // Fall back to the first authored context-specific surface terminal,
        // e.g. `outputs:ri:surface`.
        for prop in stage.prim_properties(material.clone())? {
            if prop.starts_with(NS_OUTPUTS) && prop.ends_with(&format!(":{TERMINAL_SURFACE}")) {
                conns = read_connections(stage, &material.append_property(&prop)?)?;
                if !conns.is_empty() {
                    break;
                }
            }
        }
    }
    let Some(source) = conns.into_iter().next() else {
        return Ok(None);
    };
    // The connection target is a property path (`/Mat/Surface.outputs:surface`);
    // the shader prim is its owning prim.
    Ok(Some(source.prim_path()))
}

/// The `info:id` token on a Shader prim, if authored.
pub fn read_shader_id(stage: &Stage, shader: &Path) -> Result<Option<String>> {
    Ok(
        match stage.field::<Value>(shader.append_property(A_INFO_ID)?, "default")? {
            Some(Value::Token(t)) | Some(Value::String(t)) => Some(t),
            _ => None,
        },
    )
}

/// Categorised paths from a single stage walk over the shade prims.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ShadePrims {
    pub materials: Vec<String>,
    pub node_graphs: Vec<String>,
    pub shaders: Vec<String>,
}

/// Walk the stage once and bucket every Material / NodeGraph / Shader
/// prim by type.
pub fn find_shade_prims(stage: &Stage) -> Result<ShadePrims> {
    let mut out = ShadePrims::default();
    let mut err: Result<()> = Ok(());
    stage.traverse(crate::usd::PrimPredicate::DEFAULT_PROXIES, |path| {
        if err.is_err() {
            return;
        }
        match stage.type_name(path) {
            Ok(Some(t)) if t == T_MATERIAL => out.materials.push(path.as_str().to_string()),
            Ok(Some(t)) if t == T_NODE_GRAPH => out.node_graphs.push(path.as_str().to_string()),
            Ok(Some(t)) if t == T_SHADER => out.shaders.push(path.as_str().to_string()),
            Ok(_) => {}
            Err(e) => err = Err(e),
        }
    })?;
    err?;
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn resolves_surface_and_lists_io() -> Result<()> {
        use crate::schemas::shade::{define_material, define_shader};

        let stage = Stage::builder().in_memory("anon.usda")?;
        let shader = define_shader(&stage, sdf::path("/Mat/Surface")?)?.set_id("UsdPreviewSurface")?;
        shader
            .create_input("diffuseColor", "color3f")?
            .set(Value::Vec3f([1.0, 0.0, 0.0]))?;
        shader.create_output("surface", "token")?;
        define_material(&stage, sdf::path("/Mat")?)?.connect_surface(sdf::path("/Mat/Surface.outputs:surface")?)?;

        let resolved = resolve_surface_shader(&stage, &sdf::path("/Mat")?)?.expect("surface shader");
        assert_eq!(resolved.as_str(), "/Mat/Surface");
        assert_eq!(read_shader_id(&stage, &resolved)?.as_deref(), Some("UsdPreviewSurface"));

        let inputs = input_names(&stage, &resolved)?;
        assert!(inputs.contains(&"diffuseColor".to_string()));
        assert_eq!(
            read_input_value(&stage, &resolved, "diffuseColor")?,
            Some(Value::Vec3f([1.0, 0.0, 0.0])),
        );
        Ok(())
    }

    #[test]
    fn follows_input_connection() -> Result<()> {
        use crate::schemas::shade::define_shader;

        let stage = Stage::builder().in_memory("anon.usda")?;
        let tex = define_shader(&stage, sdf::path("/Mat/Tex")?)?.set_id("UsdUVTexture")?;
        tex.create_output("rgb", "float3")?;
        let surf = define_shader(&stage, sdf::path("/Mat/Surface")?)?.set_id("UsdPreviewSurface")?;
        surf.create_input("diffuseColor", "color3f")?
            .set_connections([sdf::path("/Mat/Tex.outputs:rgb")?])?;

        let conns = read_input_connections(&stage, &sdf::path("/Mat/Surface")?, "diffuseColor")?;
        assert_eq!(conns, vec![sdf::path("/Mat/Tex.outputs:rgb")?]);
        // The connected source's owning prim is the texture shader.
        assert_eq!(conns[0].prim_path().as_str(), "/Mat/Tex");
        Ok(())
    }

    #[test]
    fn find_shade_prims_buckets_by_type() -> Result<()> {
        use crate::schemas::shade::{define_material, define_node_graph, define_shader};

        let stage = Stage::builder().in_memory("anon.usda")?;
        // `Looks` is a real (defined) Scope so the default traversal
        // predicate descends into it.
        stage.define_prim("/Looks")?.set_type_name("Scope")?;
        define_material(&stage, sdf::path("/Looks/Mat")?)?;
        define_shader(&stage, sdf::path("/Looks/Mat/Surface")?)?;
        define_node_graph(&stage, sdf::path("/Looks/Graph")?)?;

        let prims = find_shade_prims(&stage)?;
        assert!(prims.materials.contains(&"/Looks/Mat".to_string()));
        assert!(prims.shaders.contains(&"/Looks/Mat/Surface".to_string()));
        assert!(prims.node_graphs.contains(&"/Looks/Graph".to_string()));
        Ok(())
    }
}
