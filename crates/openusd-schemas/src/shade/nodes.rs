//! The shader nodes `usdShaders` defines: `UsdPreviewSurface`, `UsdUVTexture`,
//! the primvar readers and `UsdTransform2d`.
//!
//! Each view is a [`Shader`](super::Shader) authoring the node's `info:id`,
//! with an accessor per input and output the node declares and a typed read of
//! each input that falls back to the value the node's definition gives it.
//! [`tokens`] names every node id and every input and output.

openusd::include_schema!("usdShaders");

#[cfg(test)]
mod tests {
    use super::{PreviewSurface, UVTexture, tokens};
    use crate::SchemaError;
    use crate::shade::{Connectable, Shader};
    use openusd::gf;
    use openusd::sdf;
    use openusd::tf;
    use openusd::usd::SchemaBase;

    /// A defined node is a `Shader` authoring its id, and reads back as the
    /// node through the id alone.
    #[test]
    fn define_round_trip() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let surface = PreviewSurface::define(&stage, "/Mat/Surface")?;
        assert_eq!(surface.shader().id()?.as_deref(), Some(tokens::USD_PREVIEW_SURFACE));

        let found = PreviewSurface::get(&stage, "/Mat/Surface")?.expect("a PreviewSurface");
        assert_eq!(found.shader().path(), surface.shader().path());
        assert!(UVTexture::get(&stage, "/Mat/Surface")?.is_none(), "another node's id");
        assert!(PreviewSurface::get(&stage, "/Missing")?.is_none());
        Ok(())
    }

    /// An input reads what the shader authors, else the value the node's
    /// definition gives it.
    #[test]
    fn input_falls_back() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let surface = PreviewSurface::define(&stage, "/Surface")?;
        assert_eq!(surface.diffuse_color()?, Some(gf::vec3f(0.18, 0.18, 0.18)));
        assert_eq!(surface.opacity_mode()?, Some(tf::Token::new("transparent")));

        surface
            .shader()
            .create_input(tokens::ROUGHNESS, sdf::ValueTypeName::FLOAT)?
            .set(0.25_f32)?;
        assert_eq!(surface.roughness()?, Some(0.25));
        assert_eq!(
            surface.roughness_input().attribute().path().as_str(),
            "/Surface.inputs:roughness"
        );
        Ok(())
    }

    /// A value of another type than the input declares is no value of it, so
    /// the definition's answers, as a schema attribute's typed read skips one.
    #[test]
    fn mistyped_input_falls_back() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let surface = PreviewSurface::define(&stage, "/Surface")?;
        surface
            .shader()
            .create_input(tokens::ROUGHNESS, sdf::ValueTypeName::DOUBLE)?
            .set(0.25_f64)?;
        assert_eq!(surface.roughness()?, Some(0.5), "the definition's fallback");
        Ok(())
    }

    /// A `Shader` of another id is not the node.
    #[test]
    fn other_id_refused() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Other")?;
        shader.create_id_attr()?.set(sdf::Value::token("ND_standard_surface"))?;
        assert!(PreviewSurface::from_shader(shader)?.is_none());
        Ok(())
    }
}
