//! The `UsdPreviewSurface` reader.
//!
//! `UsdPreviewSurface` is the portable shading model every USD consumer
//! understands. [`read_preview_surface`] resolves a [`Material`]'s surface
//! shader, checks it is a `UsdPreviewSurface`, and harvests each channel as
//! either a scalar default or — when the input connects to a `UsdUVTexture` —
//! the texture's `inputs:file` asset path. Renderer-specific shader dialects
//! (MDL / OmniPBR / MaterialX `standard_surface`) are intentionally out of
//! scope; consumers that need them dispatch on
//! [`Shader::id`](super::Shader::id).

use anyhow::Result;

use crate::{gf, sdf, usd};

use super::tokens::*;
use super::{Connectable, Input, Material, ProducerFilter, Shader};

/// One UsdPreviewSurface channel: either a constant value, a texture asset path
/// (the input connects to a `UsdUVTexture`), or unauthored.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum Channel<T> {
    /// Not authored — the renderer uses the schema default.
    #[default]
    Unset,
    /// A constant value authored directly on the input.
    Value(T),
    /// The input connects to a `UsdUVTexture`; carries its `inputs:file` asset
    /// path.
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

/// Decoded `UsdPreviewSurface`. Every channel is a [`Channel`] — scalar,
/// texture, or unset. Colour channels are `gf::Vec3f`, scalar channels `f32`.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ReadPreviewSurface {
    /// Shader prim path this was read from.
    pub shader: String,
    pub diffuse_color: Channel<gf::Vec3f>,
    pub emissive_color: Channel<gf::Vec3f>,
    pub specular_color: Channel<gf::Vec3f>,
    pub metallic: Channel<f32>,
    pub roughness: Channel<f32>,
    pub clearcoat: Channel<f32>,
    pub clearcoat_roughness: Channel<f32>,
    pub opacity: Channel<f32>,
    pub opacity_threshold: Channel<f32>,
    pub ior: Channel<f32>,
    /// `normal` input — only its texture form is meaningful (a normal map).
    pub normal: Channel<gf::Vec3f>,
    pub occlusion: Channel<f32>,
}

/// Resolve `material`'s surface shader and, if it is a `UsdPreviewSurface`,
/// decode every channel. Returns `None` when the material has no surface shader
/// or the shader is not a `UsdPreviewSurface`.
pub fn read_preview_surface(stage: &usd::Stage, material: &sdf::Path) -> Result<Option<ReadPreviewSurface>> {
    let Some(material) = Material::get(stage, material.clone())? else {
        return Ok(None);
    };
    let Some(terminal) = material.compute_surface_source(&[])? else {
        return Ok(None);
    };
    let Some(source) = terminal.sources().first() else {
        return Ok(None);
    };
    let shader = source.shader();
    if shader.id()?.as_deref() != Some(SHADER_ID_PREVIEW_SURFACE) {
        return Ok(None);
    }

    Ok(Some(ReadPreviewSurface {
        shader: shader.path().as_str().to_string(),
        diffuse_color: read_color_channel(shader, PS_DIFFUSE_COLOR)?,
        emissive_color: read_color_channel(shader, PS_EMISSIVE_COLOR)?,
        specular_color: read_color_channel(shader, PS_SPECULAR_COLOR)?,
        metallic: read_scalar_channel(shader, PS_METALLIC)?,
        roughness: read_scalar_channel(shader, PS_ROUGHNESS)?,
        clearcoat: read_scalar_channel(shader, PS_CLEARCOAT)?,
        clearcoat_roughness: read_scalar_channel(shader, PS_CLEARCOAT_ROUGHNESS)?,
        opacity: read_scalar_channel(shader, PS_OPACITY)?,
        opacity_threshold: read_scalar_channel(shader, PS_OPACITY_THRESHOLD)?,
        ior: read_scalar_channel(shader, PS_IOR)?,
        normal: read_color_channel(shader, PS_NORMAL)?,
        occlusion: read_scalar_channel(shader, PS_OCCLUSION)?,
    }))
}

/// If `shader`'s `inputs:<base>` resolves to a `UsdUVTexture`, return that
/// texture's `inputs:file` asset path.
///
/// The input is resolved to the shader output that produces it, so a texture
/// reached through a NodeGraph interface is found the same as one wired
/// directly.
fn connected_texture_file(shader: &Shader, base: &str) -> Result<Option<String>> {
    let produced = shader
        .input(base)
        .value_producing_attributes(ProducerFilter::ShaderOutputsOnly)?;
    let Some(source) = produced.first() else {
        return Ok(None);
    };
    let stage = shader.stage();
    let Some(tex) = Shader::get(stage, source.path().prim_path())? else {
        return Ok(None);
    };
    if tex.id()?.as_deref() != Some(SHADER_ID_UV_TEXTURE) {
        return Ok(None);
    }
    resolve_asset_value(&tex.input(TEX_FILE))
}

/// Resolve an `asset`-typed input to its authored path. When the input is
/// connected — e.g. a Material interface input that drives the texture's
/// `inputs:file` — the connection is followed to the property carrying the
/// value. Returns `None` when no asset value is reachable.
///
/// TODO: the returned path is the raw authored token; anchoring it to the layer
/// that authored the opinion is not yet done.
fn resolve_asset_value(input: &Input) -> Result<Option<String>> {
    let produced = input.value_producing_attributes(ProducerFilter::Any)?;
    let Some(source) = produced.first() else {
        return Ok(None);
    };
    Ok(source
        .attribute()
        .get::<sdf::Value>()?
        .as_ref()
        .and_then(sdf::Value::as_str)
        .map(str::to_owned))
}

fn read_color_channel(shader: &Shader, base: &str) -> Result<Channel<gf::Vec3f>> {
    if let Some(file) = connected_texture_file(shader, base)? {
        return Ok(Channel::Texture(file));
    }
    Ok(match shader.input(base).get::<sdf::Value>()? {
        Some(sdf::Value::Vec3f(v)) => Channel::Value(v),
        Some(sdf::Value::Vec3d(v)) => Channel::Value(gf::vec3f(v.x as f32, v.y as f32, v.z as f32)),
        Some(sdf::Value::Vec3h(v)) => Channel::Value(gf::vec3f(v.x.to_f32(), v.y.to_f32(), v.z.to_f32())),
        _ => Channel::Unset,
    })
}

fn read_scalar_channel(shader: &Shader, base: &str) -> Result<Channel<f32>> {
    if let Some(file) = connected_texture_file(shader, base)? {
        return Ok(Channel::Texture(file));
    }
    Ok(match shader.input(base).get::<sdf::Value>()? {
        Some(sdf::Value::Float(f)) => Channel::Value(f),
        Some(sdf::Value::Double(d)) => Channel::Value(d as f32),
        Some(sdf::Value::Half(h)) => Channel::Value(h.to_f32()),
        Some(sdf::Value::Int(i)) => Channel::Value(i as f32),
        _ => Channel::Unset,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_and_textured_channels() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;

        // A UsdUVTexture feeding diffuseColor; roughness/metallic are scalars.
        let tex = Shader::define(&stage, "/Mat/DiffuseTex")?;
        tex.create_id_attr()?.set(sdf::Value::token("UsdUVTexture"))?;
        tex.create_input("file", "asset")?
            .set(sdf::Value::AssetPath("./albedo.png".into()))?;
        tex.create_output("rgb", "float3")?;

        let surf = Shader::define(&stage, "/Mat/Surface")?;
        surf.create_id_attr()?.set(sdf::Value::token("UsdPreviewSurface"))?;
        surf.create_input("diffuseColor", "color3f")?
            .set_connections([sdf::path("/Mat/DiffuseTex.outputs:rgb")?])?;
        surf.create_input("roughness", "float")?.set(sdf::Value::Float(0.4))?;
        surf.create_input("metallic", "float")?.set(sdf::Value::Float(1.0))?;
        surf.create_output("surface", "token")?;

        Material::define(&stage, "/Mat")?
            .create_surface_output()?
            .set_connections([sdf::path("/Mat/Surface.outputs:surface")?])?;

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
        let stage = usd::Stage::builder().in_memory("anon.usda")?;

        // The texture's file path is driven by a Material interface input rather
        // than authored directly on the texture.
        let mat = Material::define(&stage, "/Mat")?;
        mat.create_input("diffuseTexFile", "asset")?
            .set(sdf::Value::AssetPath("./albedo.png".into()))?;

        let tex = Shader::define(&stage, "/Mat/DiffuseTex")?;
        tex.create_id_attr()?.set(sdf::Value::token("UsdUVTexture"))?;
        tex.create_input("file", "asset")?
            .set_connections([sdf::path("/Mat.inputs:diffuseTexFile")?])?;
        tex.create_output("rgb", "float3")?;

        let surf = Shader::define(&stage, "/Mat/Surface")?;
        surf.create_id_attr()?.set(sdf::Value::token("UsdPreviewSurface"))?;
        surf.create_input("diffuseColor", "color3f")?
            .set_connections([sdf::path("/Mat/DiffuseTex.outputs:rgb")?])?;
        surf.create_output("surface", "token")?;
        mat.create_surface_output()?
            .set_connections([sdf::path("/Mat/Surface.outputs:surface")?])?;

        let ps = read_preview_surface(&stage, &sdf::path("/Mat")?)?.expect("UsdPreviewSurface");
        assert_eq!(ps.diffuse_color.texture(), Some("./albedo.png"));
        Ok(())
    }

    #[test]
    fn non_preview_surface_none() -> Result<()> {
        let stage = usd::Stage::builder().in_memory("anon.usda")?;
        let surf = Shader::define(&stage, "/Mat/Surface")?;
        surf.create_id_attr()?
            .set(sdf::Value::token("ND_standard_surface_surfaceshader"))?;
        surf.create_output("surface", "token")?;
        Material::define(&stage, "/Mat")?
            .create_surface_output()?
            .set_connections([sdf::path("/Mat/Surface.outputs:surface")?])?;
        assert!(read_preview_surface(&stage, &sdf::path("/Mat")?)?.is_none());
        Ok(())
    }
}
