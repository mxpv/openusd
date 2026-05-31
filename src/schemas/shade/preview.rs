//! Readers for the canonical `UsdPreviewSurface` + `UsdUVTexture`
//! shader graph.
//!
//! `UsdPreviewSurface` is the portable shading model every USD consumer
//! understands. This module resolves a Material's surface shader, checks
//! it's a `UsdPreviewSurface`, and harvests each channel as either a
//! scalar default or — when the input connects to a `UsdUVTexture` —
//! the texture's `inputs:file` asset path.
//!
//! Only the native `UsdPreviewSurface` / `UsdUVTexture` ids are handled.
//! Renderer-specific shader dialects (MDL / OmniPBR / MaterialX
//! `standard_surface`) are intentionally out of scope — consumers that
//! need them can dispatch on [`read_shader_id`](super::read_shader_id)
//! themselves.

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use super::connectable::input_path;
use super::read::{read_input_connections, read_input_value, read_shader_id, resolve_surface_shader};
use super::tokens::{
    PS_CLEARCOAT, PS_CLEARCOAT_ROUGHNESS, PS_DIFFUSE_COLOR, PS_EMISSIVE_COLOR, PS_IOR, PS_METALLIC, PS_NORMAL,
    PS_OCCLUSION, PS_OPACITY, PS_OPACITY_THRESHOLD, PS_ROUGHNESS, PS_SPECULAR_COLOR, SHADER_ID_PREVIEW_SURFACE,
    SHADER_ID_UV_TEXTURE, TEX_FILE,
};

/// One UsdPreviewSurface channel: either a constant value, a texture
/// asset path (the input connects to a `UsdUVTexture`), or unauthored.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum Channel<T> {
    /// Not authored — the renderer uses the schema default.
    #[default]
    Unset,
    /// A constant value authored directly on the input.
    Value(T),
    /// The input connects to a `UsdUVTexture`; carries its
    /// `inputs:file` asset path.
    Texture(String),
}

impl<T> Channel<T> {
    pub fn value(&self) -> Option<&T> {
        match self {
            Channel::Value(v) => Some(v),
            _ => None,
        }
    }

    pub fn texture(&self) -> Option<&str> {
        match self {
            Channel::Texture(p) => Some(p.as_str()),
            _ => None,
        }
    }

    pub fn is_set(&self) -> bool {
        !matches!(self, Channel::Unset)
    }
}

/// Decoded `UsdPreviewSurface`. Every channel is a [`Channel`] —
/// scalar, texture, or unset. Colour channels are `[f32; 3]`, scalar
/// channels `f32`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadPreviewSurface {
    /// Shader prim path this was read from.
    pub shader: String,
    pub diffuse_color: Channel<[f32; 3]>,
    pub emissive_color: Channel<[f32; 3]>,
    pub specular_color: Channel<[f32; 3]>,
    pub metallic: Channel<f32>,
    pub roughness: Channel<f32>,
    pub clearcoat: Channel<f32>,
    pub clearcoat_roughness: Channel<f32>,
    pub opacity: Channel<f32>,
    pub opacity_threshold: Channel<f32>,
    pub ior: Channel<f32>,
    /// `normal` input — only its texture form is meaningful (a normal map).
    pub normal: Channel<[f32; 3]>,
    pub occlusion: Channel<f32>,
}

/// Resolve `material`'s surface shader and, if it's a
/// `UsdPreviewSurface`, decode every channel. Returns `None` when the
/// material has no surface shader or the shader isn't a
/// `UsdPreviewSurface`.
pub fn read_preview_surface(stage: &Stage, material: &Path) -> Result<Option<ReadPreviewSurface>> {
    let Some(shader) = resolve_surface_shader(stage, material)? else {
        return Ok(None);
    };
    if read_shader_id(stage, &shader)?.as_deref() != Some(SHADER_ID_PREVIEW_SURFACE) {
        return Ok(None);
    }

    Ok(Some(ReadPreviewSurface {
        shader: shader.as_str().to_string(),
        diffuse_color: read_color_channel(stage, &shader, PS_DIFFUSE_COLOR)?,
        emissive_color: read_color_channel(stage, &shader, PS_EMISSIVE_COLOR)?,
        specular_color: read_color_channel(stage, &shader, PS_SPECULAR_COLOR)?,
        metallic: read_scalar_channel(stage, &shader, PS_METALLIC)?,
        roughness: read_scalar_channel(stage, &shader, PS_ROUGHNESS)?,
        clearcoat: read_scalar_channel(stage, &shader, PS_CLEARCOAT)?,
        clearcoat_roughness: read_scalar_channel(stage, &shader, PS_CLEARCOAT_ROUGHNESS)?,
        opacity: read_scalar_channel(stage, &shader, PS_OPACITY)?,
        opacity_threshold: read_scalar_channel(stage, &shader, PS_OPACITY_THRESHOLD)?,
        ior: read_scalar_channel(stage, &shader, PS_IOR)?,
        normal: read_color_channel(stage, &shader, PS_NORMAL)?,
        occlusion: read_scalar_channel(stage, &shader, PS_OCCLUSION)?,
    }))
}

/// Upper bound on connection hops [`resolve_asset_value`] follows before
/// giving up, guarding against connection cycles.
const MAX_CONNECTION_HOPS: usize = 8;

/// If `shader`'s `inputs:<base>` connects to a `UsdUVTexture`, return
/// that texture's `inputs:file` asset path.
fn connected_texture_file(stage: &Stage, shader: &Path, base: &str) -> Result<Option<String>> {
    let conns = read_input_connections(stage, shader, base)?;
    let Some(source) = conns.into_iter().next() else {
        return Ok(None);
    };
    let tex_prim = source.prim_path();
    if read_shader_id(stage, &tex_prim)?.as_deref() != Some(SHADER_ID_UV_TEXTURE) {
        return Ok(None);
    }
    resolve_asset_value(stage, &input_path(&tex_prim, TEX_FILE)?)
}

/// Resolve an `asset`-typed input to its authored path. When the input is
/// connected — e.g. a Material interface input that drives the texture's
/// `inputs:file` — the connection is followed to the property carrying the
/// value. Returns `None` when no asset value is reachable.
///
/// TODO: the returned path is the raw authored token; anchoring it to the
/// layer that authored the opinion is not yet done.
fn resolve_asset_value(stage: &Stage, attr: &Path) -> Result<Option<String>> {
    let mut current = attr.clone();
    for _ in 0..MAX_CONNECTION_HOPS {
        if let Some(source) = stage.connection_paths(&current)?.into_iter().next() {
            current = source;
            continue;
        }
        return Ok(match stage.field::<Value>(current, FieldKey::Default.as_str())? {
            Some(Value::AssetPath(p)) | Some(Value::String(p)) | Some(Value::Token(p)) => Some(p),
            _ => None,
        });
    }
    Ok(None)
}

fn read_color_channel(stage: &Stage, shader: &Path, base: &str) -> Result<Channel<[f32; 3]>> {
    if let Some(file) = connected_texture_file(stage, shader, base)? {
        return Ok(Channel::Texture(file));
    }
    Ok(match read_input_value(stage, shader, base)? {
        Some(Value::Vec3f(v)) => Channel::Value(v),
        Some(Value::Vec3d(v)) => Channel::Value([v[0] as f32, v[1] as f32, v[2] as f32]),
        Some(Value::Vec3h(v)) => Channel::Value([v[0].to_f32(), v[1].to_f32(), v[2].to_f32()]),
        _ => Channel::Unset,
    })
}

fn read_scalar_channel(stage: &Stage, shader: &Path, base: &str) -> Result<Channel<f32>> {
    if let Some(file) = connected_texture_file(stage, shader, base)? {
        return Ok(Channel::Texture(file));
    }
    Ok(match read_input_value(stage, shader, base)? {
        Some(Value::Float(f)) => Channel::Value(f),
        Some(Value::Double(d)) => Channel::Value(d as f32),
        Some(Value::Half(h)) => Channel::Value(h.to_f32()),
        Some(Value::Int(i)) => Channel::Value(i as f32),
        _ => Channel::Unset,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf;

    #[test]
    fn reads_scalar_and_textured_channels() -> Result<()> {
        use crate::schemas::shade::{define_material, define_shader};

        let stage = Stage::builder().in_memory("anon.usda")?;

        // A UsdUVTexture feeding diffuseColor; roughness/metallic are scalars.
        let tex = define_shader(&stage, sdf::path("/Mat/DiffuseTex")?)?.set_id("UsdUVTexture")?;
        tex.create_input("file", "asset")?
            .set(Value::AssetPath("./albedo.png".into()))?;
        tex.create_output("rgb", "float3")?;

        let surf = define_shader(&stage, sdf::path("/Mat/Surface")?)?.set_id("UsdPreviewSurface")?;
        surf.create_input("diffuseColor", "color3f")?
            .set_connections([sdf::path("/Mat/DiffuseTex.outputs:rgb")?])?;
        surf.create_input("roughness", "float")?.set(Value::Float(0.4))?;
        surf.create_input("metallic", "float")?.set(Value::Float(1.0))?;
        surf.create_output("surface", "token")?;

        define_material(&stage, sdf::path("/Mat")?)?.connect_surface(sdf::path("/Mat/Surface.outputs:surface")?)?;

        let ps = read_preview_surface(&stage, &sdf::path("/Mat")?)?.expect("UsdPreviewSurface");
        assert_eq!(ps.shader, "/Mat/Surface");
        assert_eq!(ps.diffuse_color.texture(), Some("./albedo.png"));
        assert_eq!(ps.roughness.value(), Some(&0.4));
        assert_eq!(ps.metallic.value(), Some(&1.0));
        // Unauthored channels stay Unset.
        assert!(!ps.opacity.is_set());
        assert!(!ps.ior.is_set());
        Ok(())
    }

    #[test]
    fn interface_driven_texture() -> Result<()> {
        use crate::schemas::shade::{define_material, define_shader};

        let stage = Stage::builder().in_memory("anon.usda")?;

        // The texture's file path is driven by a Material interface input
        // rather than authored directly on the texture.
        let mat = define_material(&stage, sdf::path("/Mat")?)?;
        mat.create_input("diffuseTexFile", "asset")?
            .set(Value::AssetPath("./albedo.png".into()))?;

        let tex = define_shader(&stage, sdf::path("/Mat/DiffuseTex")?)?.set_id("UsdUVTexture")?;
        tex.create_input("file", "asset")?
            .set_connections([sdf::path("/Mat.inputs:diffuseTexFile")?])?;
        tex.create_output("rgb", "float3")?;

        let surf = define_shader(&stage, sdf::path("/Mat/Surface")?)?.set_id("UsdPreviewSurface")?;
        surf.create_input("diffuseColor", "color3f")?
            .set_connections([sdf::path("/Mat/DiffuseTex.outputs:rgb")?])?;
        surf.create_output("surface", "token")?;
        mat.connect_surface(sdf::path("/Mat/Surface.outputs:surface")?)?;

        let ps = read_preview_surface(&stage, &sdf::path("/Mat")?)?.expect("UsdPreviewSurface");
        assert_eq!(ps.diffuse_color.texture(), Some("./albedo.png"));
        Ok(())
    }

    #[test]
    fn non_preview_surface_returns_none() -> Result<()> {
        use crate::schemas::shade::{define_material, define_shader};

        let stage = Stage::builder().in_memory("anon.usda")?;
        define_shader(&stage, sdf::path("/Mat/Surface")?)?.set_id("ND_standard_surface_surfaceshader")?;
        define_material(&stage, sdf::path("/Mat")?)?.connect_surface(sdf::path("/Mat/Surface.outputs:surface")?)?;
        assert!(read_preview_surface(&stage, &sdf::path("/Mat")?)?.is_none());
        Ok(())
    }
}
