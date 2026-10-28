//! The `UsdPreviewSurface` reader.
//!
//! `UsdPreviewSurface` is the portable shading model every USD consumer
//! understands. [`read_preview_surface`] resolves a [`Material`]'s surface
//! shader, checks it is a `UsdPreviewSurface`, and harvests each channel as
//! either a scalar default or — when the input connects to a `UsdUVTexture` —
//! the texture's `inputs:file` asset path, anchored at the layer that authored
//! it and resolved when the asset is found. Renderer-specific shader dialects
//! (MDL / OmniPBR / MaterialX `standard_surface`) are intentionally out of
//! scope; consumers that need them dispatch on
//! [`NodeDefAPI::shader_id`](super::NodeDefAPI::shader_id).

use openusd::Result;

use crate::SchemaError;

use openusd::{gf, sdf, usd, vt};

use super::nodes::{PreviewSurface, UVTexture};
use super::tokens::*;
use super::{ConnectableContext, Input, Material, ProducerFilter, Shader, TerminalKind};

/// One UsdPreviewSurface channel: either a constant value, a texture asset path
/// (the input connects to a `UsdUVTexture`), or unauthored.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum Channel<T> {
    /// Not authored — the renderer uses the schema default.
    #[default]
    Unset,
    /// A constant value authored directly on the input.
    Value(T),
    /// The input connects to a `UsdUVTexture`; carries its `inputs:file` value,
    /// resolved when the asset is found.
    Texture(sdf::AssetPath),
}

impl<T> Channel<T> {
    pub fn value(&self) -> Option<&T> {
        match self {
            Channel::Value(v) => Some(v),
            _ => None,
        }
    }

    pub fn texture(&self) -> Option<&sdf::AssetPath> {
        match self {
            Channel::Texture(p) => Some(p),
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
    pub shader: sdf::Path,
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
/// decode every channel. The universal surface terminal is consulted first;
/// when it resolves nothing, the authored render-context surface terminals
/// are tried in sorted order, so a context-only material still decodes.
/// Returns `None` when no terminal yields a `UsdPreviewSurface` shader.
pub fn read_preview_surface(
    stage: &usd::Stage,
    material: &sdf::Path,
) -> Result<Option<ReadPreviewSurface>, SchemaError> {
    ConnectableContext::default().read_preview_surface(stage, material)
}

impl ConnectableContext {
    /// `material`'s `UsdPreviewSurface`, as [`read_preview_surface`] decodes
    /// it, each prim the connections reach asked of this context whether it
    /// is a container.
    pub fn read_preview_surface(
        &self,
        stage: &usd::Stage,
        material: &sdf::Path,
    ) -> Result<Option<ReadPreviewSurface>, SchemaError> {
        let Some(material) = Material::get(stage, material.clone())? else {
            return Ok(None);
        };
        let Some(terminal) = resolve_surface_terminal(self, &material)? else {
            return Ok(None);
        };
        let Some(source) = terminal.sources().first() else {
            return Ok(None);
        };
        let Some(shader) = source.shader() else {
            return Ok(None);
        };
        let Some(surface) = PreviewSurface::from_shader(shader.clone())? else {
            return Ok(None);
        };

        Ok(Some(ReadPreviewSurface {
            shader: shader.path().clone(),
            diffuse_color: read_color_channel(self, &surface.diffuse_color_input())?,
            emissive_color: read_color_channel(self, &surface.emissive_color_input())?,
            specular_color: read_color_channel(self, &surface.specular_color_input())?,
            metallic: read_scalar_channel(self, &surface.metallic_input())?,
            roughness: read_scalar_channel(self, &surface.roughness_input())?,
            clearcoat: read_scalar_channel(self, &surface.clearcoat_input())?,
            clearcoat_roughness: read_scalar_channel(self, &surface.clearcoat_roughness_input())?,
            opacity: read_scalar_channel(self, &surface.opacity_input())?,
            opacity_threshold: read_scalar_channel(self, &surface.opacity_threshold_input())?,
            ior: read_scalar_channel(self, &surface.ior_input())?,
            normal: read_color_channel(self, &surface.normal_input())?,
            occlusion: read_scalar_channel(self, &surface.occlusion_input())?,
        }))
    }
}

/// Resolve the surface terminal: the universal context first, then the
/// authored render-context terminals in sorted order for a stable choice.
fn resolve_surface_terminal(
    context: &ConnectableContext,
    material: &Material,
) -> Result<Option<super::ResolvedTerminal>, SchemaError> {
    if let Some(terminal) = context.terminal_source(material, TerminalKind::Surface, &[])? {
        return Ok(Some(terminal));
    }
    let suffix = format!(":{}", SURFACE);
    let mut contexts: Vec<String> = material
        .surface_outputs()?
        .iter()
        .filter_map(|output| output.base_name().strip_suffix(&suffix))
        .map(String::from)
        .collect();
    contexts.sort();
    if contexts.is_empty() {
        return Ok(None);
    }
    let contexts: Vec<&str> = contexts.iter().map(String::as_str).collect();
    context.terminal_source(material, TerminalKind::Surface, &contexts)
}

/// If `input` resolves to a `UsdUVTexture`, return that texture's
/// `inputs:file` asset path.
///
/// The input is resolved to the shader output that produces it, so a texture
/// reached through a NodeGraph interface is found the same as one wired
/// directly.
fn connected_texture_file(context: &ConnectableContext, input: &Input) -> Result<Option<sdf::AssetPath>, SchemaError> {
    let produced = context.value_producing_attributes(input.clone(), ProducerFilter::ShaderOutputsOnly)?;
    let Some(source) = produced.first() else {
        return Ok(None);
    };
    let Some(shader) = Shader::get(input.attribute().stage(), source.path().prim_path())? else {
        return Ok(None);
    };
    let Some(texture) = UVTexture::from_shader(shader)? else {
        return Ok(None);
    };
    resolve_asset_value(context, &texture.file_input())
}

/// The asset value of an `asset`-typed input. A connected input, such as a
/// texture's `inputs:file` driven by a Material interface input, reads the
/// property its connection reaches. The value is anchored at the layer that
/// authored that property's opinion. Returns `None` when no asset value is
/// reachable or the value is the empty path `@@`.
fn resolve_asset_value(context: &ConnectableContext, input: &Input) -> Result<Option<sdf::AssetPath>, SchemaError> {
    let produced = context.value_producing_attributes(input.clone(), ProducerFilter::Any)?;
    let Some(source) = produced.first() else {
        return Ok(None);
    };
    Ok(source
        .attribute()
        .get::<sdf::AssetPath>()?
        .filter(|asset| !asset.is_empty()))
}

/// A colour channel: the texture feeding `input`, else the value the shader
/// authors on it, widened to `f32` components.
fn read_color_channel(context: &ConnectableContext, input: &Input) -> Result<Channel<gf::Vec3f>, SchemaError> {
    if let Some(file) = connected_texture_file(context, input)? {
        return Ok(Channel::Texture(file));
    }
    Ok(match input.get::<vt::Value>()? {
        Some(vt::Value::Vec3f(v)) => Channel::Value(v),
        Some(vt::Value::Vec3d(v)) => Channel::Value(gf::vec3f(v.x as f32, v.y as f32, v.z as f32)),
        Some(vt::Value::Vec3h(v)) => Channel::Value(gf::vec3f(v.x.to_f32(), v.y.to_f32(), v.z.to_f32())),
        _ => Channel::Unset,
    })
}

/// A scalar channel: the texture feeding `input`, else the value the shader
/// authors on it, as `f32`.
fn read_scalar_channel(context: &ConnectableContext, input: &Input) -> Result<Channel<f32>, SchemaError> {
    if let Some(file) = connected_texture_file(context, input)? {
        return Ok(Channel::Texture(file));
    }
    Ok(match input.get::<vt::Value>()? {
        Some(vt::Value::Float(f)) => Channel::Value(f),
        Some(vt::Value::Double(d)) => Channel::Value(d as f32),
        Some(vt::Value::Half(h)) => Channel::Value(h.to_f32()),
        Some(vt::Value::Int(i)) => Channel::Value(i as f32),
        _ => Channel::Unset,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shade::Connectable;

    use openusd::Result;

    #[test]
    fn context_only_surface() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let surf = Shader::define(&stage, "/Mat/Surface")?;
        surf.node_def()
            .create_id_attr()?
            .set(vt::Value::token("UsdPreviewSurface"))?;
        surf.create_input("roughness", "float")?.set(vt::Value::Float(0.4))?;
        surf.create_output("surface", "token")?;

        // Only a render-context surface terminal is authored; the reader
        // falls back to it when the universal terminal resolves nothing.
        Material::define(&stage, "/Mat")?
            .create_surface_output_for("ri")?
            .set_connections(["/Mat/Surface.outputs:surface"])?;

        let ps = read_preview_surface(&stage, &sdf::path("/Mat")?)?.expect("context-only decodes");
        assert_eq!(ps.shader, sdf::path("/Mat/Surface")?);
        assert_eq!(ps.roughness.value(), Some(&0.4));
        Ok(())
    }

    #[test]
    fn scalar_and_textured_channels() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;

        // A UsdUVTexture feeding diffuseColor; roughness/metallic are scalars.
        let tex = Shader::define(&stage, "/Mat/DiffuseTex")?;
        tex.node_def().create_id_attr()?.set(vt::Value::token("UsdUVTexture"))?;
        tex.create_input("file", "asset")?
            .set(vt::Value::AssetPath("./albedo.png".into()))?;
        tex.create_output("rgb", "float3")?;

        let surf = Shader::define(&stage, "/Mat/Surface")?;
        surf.node_def()
            .create_id_attr()?
            .set(vt::Value::token("UsdPreviewSurface"))?;
        surf.create_input("diffuseColor", "color3f")?
            .set_connections(["/Mat/DiffuseTex.outputs:rgb"])?;
        surf.create_input("roughness", "float")?.set(vt::Value::Float(0.4))?;
        surf.create_input("metallic", "float")?.set(vt::Value::Float(1.0))?;
        surf.create_output("surface", "token")?;

        Material::define(&stage, "/Mat")?
            .create_surface_output()?
            .set_connections(["/Mat/Surface.outputs:surface"])?;

        let ps = read_preview_surface(&stage, &sdf::path("/Mat")?)?.expect("UsdPreviewSurface");
        assert_eq!(ps.shader, sdf::path("/Mat/Surface")?);
        assert_eq!(ps.diffuse_color.texture(), Some(&sdf::AssetPath::new("./albedo.png")));
        assert_eq!(ps.roughness.value(), Some(&0.4));
        assert_eq!(ps.metallic.value(), Some(&1.0));
        // Unauthored channels stay Unset.
        assert!(!ps.opacity.is_set());
        assert!(!ps.ior.is_set());
        Ok(())
    }

    #[test]
    fn interface_driven_texture() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;

        // The texture's file path is driven by a Material interface input rather
        // than authored directly on the texture.
        let mat = Material::define(&stage, "/Mat")?;
        mat.create_input("diffuseTexFile", "asset")?
            .set(vt::Value::AssetPath("./albedo.png".into()))?;

        let tex = Shader::define(&stage, "/Mat/DiffuseTex")?;
        tex.node_def().create_id_attr()?.set(vt::Value::token("UsdUVTexture"))?;
        tex.create_input("file", "asset")?
            .set_connections(["/Mat.inputs:diffuseTexFile"])?;
        tex.create_output("rgb", "float3")?;

        let surf = Shader::define(&stage, "/Mat/Surface")?;
        surf.node_def()
            .create_id_attr()?
            .set(vt::Value::token("UsdPreviewSurface"))?;
        surf.create_input("diffuseColor", "color3f")?
            .set_connections(["/Mat/DiffuseTex.outputs:rgb"])?;
        surf.create_output("surface", "token")?;
        mat.create_surface_output()?
            .set_connections(["/Mat/Surface.outputs:surface"])?;

        let ps = read_preview_surface(&stage, &sdf::path("/Mat")?)?.expect("UsdPreviewSurface");
        assert_eq!(ps.diffuse_color.texture(), Some(&sdf::AssetPath::new("./albedo.png")));
        Ok(())
    }

    #[test]
    fn non_preview_surface_none() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let surf = Shader::define(&stage, "/Mat/Surface")?;
        surf.node_def()
            .create_id_attr()?
            .set(vt::Value::token("ND_standard_surface_surfaceshader"))?;
        surf.create_output("surface", "token")?;
        Material::define(&stage, "/Mat")?
            .create_surface_output()?
            .set_connections(["/Mat/Surface.outputs:surface"])?;
        assert!(read_preview_surface(&stage, &sdf::path("/Mat")?)?.is_none());
        Ok(())
    }
}
