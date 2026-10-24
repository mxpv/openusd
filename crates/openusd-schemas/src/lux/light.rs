//! What a light and a light filter add to their generated views: the
//! collections that link them to the geometry they affect, and the shader
//! each render context draws them with.

use openusd::Result;
use openusd::usd::{self, SchemaBase};
use openusd::{sdf, tf};

use super::{LightAPI, LightFilterSchema, tokens};

impl LightAPI {
    /// The collection of the geometry the light illuminates (C++
    /// `UsdLuxLightAPI::GetLightLinkCollectionAPI`). On a prim `LightAPI`
    /// applies to, the schema includes the root, and a light with nothing
    /// authored links to everything.
    pub fn light_link_collection(&self) -> usd::CollectionAPI {
        usd::CollectionAPI::from_prim_unchecked(self.prim().clone(), tokens::LIGHT_LINK)
    }

    /// The collection of the geometry that casts the light's shadows (C++
    /// `UsdLuxLightAPI::GetShadowLinkCollectionAPI`). On a prim `LightAPI`
    /// applies to, the schema includes the root, and a light with nothing
    /// authored is shadowed by everything.
    pub fn shadow_link_collection(&self) -> usd::CollectionAPI {
        usd::CollectionAPI::from_prim_unchecked(self.prim().clone(), tokens::SHADOW_LINK)
    }

    /// The `<context>:light:shaderId` attribute that names the light's
    /// shader for `render_context`, `light:shaderId` for an empty one, or
    /// `None` where it is not defined (C++
    /// `UsdLuxLightAPI::GetShaderIdAttrForRenderContext`).
    pub fn shader_id_attr_for(&self, render_context: &str) -> Result<Option<usd::Attribute>> {
        shader_id_attr(self.prim(), tokens::LIGHT_SHADER_ID, render_context)
    }

    /// The declaration of the `shader_id_attr_for(render_context)`
    /// attribute, a uniform `token`. Give it a value and `build` it to
    /// author both as one edit.
    pub fn shader_id_attr_builder_for(&self, render_context: &str) -> usd::AttributeBuilder<'static> {
        shader_id_builder(self.prim(), tokens::LIGHT_SHADER_ID, render_context)
    }

    /// Author the `shader_id_attr_for(render_context)` attribute with no
    /// value (C++ `UsdLuxLightAPI::CreateShaderIdAttrForRenderContext`).
    pub fn create_shader_id_attr_for(&self, render_context: &str) -> Result<usd::Attribute> {
        Ok(self.shader_id_attr_builder_for(render_context).build()?)
    }

    /// The light's shader for the first of `render_contexts`, in order, that
    /// names a non-empty one, else the one `light:shaderId` names, or `None`
    /// where that is empty too (C++ `UsdLuxLightAPI::GetShaderId`).
    pub fn shader_id_for(&self, render_contexts: &[&str]) -> Result<Option<tf::Token>> {
        shader_id(self.prim(), tokens::LIGHT_SHADER_ID, render_contexts)
    }
}

/// What every light filter adds to its generated view (C++
/// `UsdLuxLightFilter`), for [`LightFilter`](super::LightFilter) and
/// [`PluginLightFilter`](super::PluginLightFilter) alike.
pub trait LightFilterExt: LightFilterSchema {
    /// The collection of the geometry the filter applies to (C++
    /// `UsdLuxLightFilter::GetFilterLinkCollectionAPI`). The filter's schema
    /// includes the root, and a filter with nothing authored applies to
    /// everything.
    fn filter_link_collection(&self) -> usd::CollectionAPI {
        usd::CollectionAPI::from_prim_unchecked(self.prim().clone(), tokens::FILTER_LINK)
    }

    /// The `<context>:lightFilter:shaderId` attribute that names the
    /// filter's shader for `render_context`, `lightFilter:shaderId` for an
    /// empty one, or `None` where it is not defined (C++
    /// `UsdLuxLightFilter::GetShaderIdAttrForRenderContext`).
    fn shader_id_attr_for(&self, render_context: &str) -> Result<Option<usd::Attribute>> {
        shader_id_attr(self.prim(), tokens::LIGHT_FILTER_SHADER_ID, render_context)
    }

    /// The declaration of the `shader_id_attr_for(render_context)`
    /// attribute, a uniform `token`. Give it a value and `build` it to
    /// author both as one edit.
    fn shader_id_attr_builder_for(&self, render_context: &str) -> usd::AttributeBuilder<'static> {
        shader_id_builder(self.prim(), tokens::LIGHT_FILTER_SHADER_ID, render_context)
    }

    /// Author the `shader_id_attr_for(render_context)` attribute with no
    /// value (C++ `UsdLuxLightFilter::CreateShaderIdAttrForRenderContext`).
    fn create_shader_id_attr_for(&self, render_context: &str) -> Result<usd::Attribute> {
        Ok(self.shader_id_attr_builder_for(render_context).build()?)
    }

    /// The filter's shader for the first of `render_contexts`, in order,
    /// that names a non-empty one, else the one `lightFilter:shaderId`
    /// names, or `None` where that is empty too (C++
    /// `UsdLuxLightFilter::GetShaderId`).
    fn shader_id_for(&self, render_contexts: &[&str]) -> Result<Option<tf::Token>> {
        shader_id(self.prim(), tokens::LIGHT_FILTER_SHADER_ID, render_contexts)
    }
}

impl<T: LightFilterSchema> LightFilterExt for T {}

/// The name of the `base` shader id attribute for `render_context`: `base`
/// itself for an empty context, else `<context>:<base>` (C++
/// `_GetShaderIdAttrName`).
fn shader_id_name(base: &str, render_context: &str) -> tf::Token {
    match render_context {
        "" => tf::Token::from(base),
        context => tf::Token::from(format!("{context}:{base}")),
    }
}

/// The `base` shader id attribute of `prim` for `render_context`, where it
/// is defined.
fn shader_id_attr(prim: &usd::Prim, base: &str, render_context: &str) -> Result<Option<usd::Attribute>> {
    let attribute = prim.attribute(shader_id_name(base, render_context));
    Ok(attribute.is_defined()?.then_some(attribute))
}

/// The declaration of the `base` shader id attribute of `prim` for
/// `render_context` (C++ `CreateShaderIdAttrForRenderContext`).
fn shader_id_builder(prim: &usd::Prim, base: &str, render_context: &str) -> usd::AttributeBuilder<'static> {
    prim.attribute_builder(shader_id_name(base, render_context), sdf::ValueTypeName::TOKEN)
        .custom(false)
        .variability(sdf::Variability::Uniform)
}

/// The shader the first of `render_contexts` names on `prim` through the
/// `base` attribute, else the one `base` names. An attribute no layer or
/// schema defines reads no value.
fn shader_id(prim: &usd::Prim, base: &str, render_contexts: &[&str]) -> Result<Option<tf::Token>> {
    let read = |name: tf::Token| -> Result<Option<tf::Token>> {
        Ok(prim.attribute(name).get::<tf::Token>()?.filter(|id| !id.is_empty()))
    };
    for &render_context in render_contexts {
        if let Some(id) = read(shader_id_name(base, render_context))? {
            return Ok(Some(id));
        }
    }
    read(tf::Token::from(base))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A render context namespaces the universal attribute's name.
    #[test]
    fn shader_id_name_context() {
        assert_eq!(shader_id_name(tokens::LIGHT_SHADER_ID, ""), "light:shaderId");
        assert_eq!(shader_id_name(tokens::LIGHT_SHADER_ID, "ri"), "ri:light:shaderId");
        assert_eq!(
            shader_id_name(tokens::LIGHT_FILTER_SHADER_ID, "ri"),
            "ri:lightFilter:shaderId"
        );
    }
}
