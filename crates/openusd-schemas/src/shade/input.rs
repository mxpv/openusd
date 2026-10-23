//! Typed view over a UsdShade `inputs:` attribute.

use openusd::Result;

use openusd::usd::{Object, Property};
use openusd::{sdf, usd};

use super::impl_shading_attribute;
use super::tokens::{CONNECTABILITY, INPUTS};
use super::{Connectability, ConnectionTarget, ShadingAttribute};

/// A UsdShade input backed by an `inputs:<base>` USD attribute
/// (C++ `UsdShadeInput`).
///
/// An input carries the value a shading node consumes, either authored on the
/// attribute itself or produced upstream through its connections. The view
/// preserves the input namespace invariant while dereferencing to the
/// underlying [`usd::Attribute`] for generic value and metadata queries.
#[derive(Clone, derive_more::Deref)]
pub struct Input {
    attribute: usd::Attribute,
}

impl_shading_attribute!(Input, INPUTS);

impl Input {
    /// The input's `connectability`, defaulting to [`Connectability::Full`]
    /// (C++ `UsdShadeInput::GetConnectability`).
    pub fn connectability(&self) -> Result<Connectability> {
        Ok(self
            .attribute
            .metadata::<Connectability>(CONNECTABILITY)?
            .unwrap_or_default())
    }

    /// Author this input's `connectability` metadata
    /// (C++ `UsdShadeInput::SetConnectability`).
    pub fn set_connectability(self, connectability: Connectability) -> Result<Self, usd::StageAuthoringError> {
        self.attribute
            .set_metadata(CONNECTABILITY, connectability)
            .map(Self::new)
    }

    /// Drop this input's local `connectability` opinion
    /// (C++ `UsdShadeInput::ClearConnectability`).
    pub fn clear_connectability(self) -> Result<Self, usd::StageAuthoringError> {
        self.attribute.clear_metadata(CONNECTABILITY).map(Self::new)
    }

    /// Author this input's `doc` field (C++
    /// `UsdShadeInput::SetDocumentation`).
    pub fn set_doc(self, doc: impl Into<String>) -> Result<Self, usd::StageAuthoringError> {
        self.attribute.set_doc(doc).map(Self::new)
    }

    /// Author this input's `displayGroup` (C++
    /// `UsdShadeInput::SetDisplayGroup`).
    pub fn set_display_group(self, display_group: impl Into<String>) -> Result<Self, usd::StageAuthoringError> {
        self.attribute.set_display_group(display_group).map(Self::new)
    }
}

impl From<Input> for ShadingAttribute {
    fn from(input: Input) -> Self {
        ShadingAttribute::Input(input)
    }
}

impl ConnectionTarget for Input {
    fn target_path(&self) -> &sdf::Path {
        self.attribute().path()
    }
}

#[cfg(test)]
mod tests {
    use openusd::Result;
    use openusd::usd::{Object, Property};

    use crate::shade::{Connectability, Connectable, NodeGraph, Shader};

    #[test]
    fn invalid_base_name_reads_empty() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Mat/Surface")?;

        // A base name USD rejects addresses no property, so the view reads
        // back empty instead of panicking.
        let input = shader.input("diffuse color");
        assert_eq!(input.full_name(), "");
        assert_eq!(input.base_name(), "");
        assert_eq!(input.get::<f32>()?, None);
        assert!(input.connected_sources()?.sources().is_empty());
        Ok(())
    }

    #[test]
    fn single_source_queries() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let tex = NodeGraph::define(&stage, "/Mat/Tex")?;
        let rgb = tex.create_output("rgb", "float3")?;
        let surface = Shader::define(&stage, "/Mat/Surface")?;
        let color = surface.create_input("diffuseColor", "color3f")?;
        assert!(!color.has_connected_source()?);
        assert!(color.connected_source()?.is_none());

        let color = color.connect_to(&rgb)?;
        assert!(color.has_connected_source()?);
        let source = color.connected_source()?.expect("connected");
        assert_eq!(source.path().as_str(), "/Mat/Tex.outputs:rgb");

        assert!(color.disconnect_source(&rgb)?);
        assert!(!color.disconnect_source(&rgb)?, "already removed");
        assert!(!color.has_connected_source()?);
        Ok(())
    }

    /// Disconnecting blocks a weaker layer's connection; clearing the sources
    /// lets it compose again.
    #[test]
    fn disconnect_and_clear_sources() -> Result<()> {
        let (_dir, stage) = crate::tests::layered(&[(
            "weak.usda",
            r#"
def Material "Mat" {
    def Shader "Tex" { float3 outputs:rgb }
    def Shader "Surface" {
        color3f inputs:diffuseColor.connect = </Mat/Tex.outputs:rgb>
    }
}
"#,
        )])?;
        let surface = Shader::get(&stage, "/Mat/Surface")?.expect("a Shader");
        let color = surface.input("diffuseColor");
        assert!(color.has_connected_source()?);

        let color = color.disconnect()?;
        assert!(color.connections()?.is_empty());

        let color = color.clear_sources()?;
        assert_eq!(
            color.connected_source()?.expect("the weaker layer's").path().as_str(),
            "/Mat/Tex.outputs:rgb"
        );

        // Removing the one source deletes it on the edit target, which the
        // weaker layer's opinion does not survive.
        let rgb = Shader::get(&stage, "/Mat/Tex")?.expect("a Shader").output("rgb");
        assert!(color.disconnect_source(&rgb)?);
        assert!(!color.has_connected_source()?);
        Ok(())
    }

    #[test]
    fn connectability_cleared() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Surface")?;
        let input = shader
            .create_input("scale", "float")?
            .set_connectability(Connectability::InterfaceOnly)?;
        assert_eq!(input.connectability()?, Connectability::InterfaceOnly);
        let input = input.clear_connectability()?;
        assert_eq!(input.connectability()?, Connectability::Full);
        Ok(())
    }

    /// The setters keep the input view; the reads come through the attribute.
    #[test]
    fn doc_and_display_group() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let shader = Shader::define(&stage, "/Surface")?;
        let input = shader
            .create_input("scale", "float")?
            .set_doc("Scales the result.")?
            .set_display_group("Basic")?;
        assert_eq!(input.doc()?.as_deref(), Some("Scales the result."));
        assert_eq!(input.display_group()?.as_deref(), Some("Basic"));
        assert_eq!(input.base_name(), "scale");
        Ok(())
    }
}
