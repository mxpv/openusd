//! Typed view over a UsdShade `inputs:` attribute.

use crate::Result;

use crate::{sdf, usd};

use super::impl_shading_attribute;
use super::tokens::{META_CONNECTABILITY, NS_INPUTS};
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

impl_shading_attribute!(Input, NS_INPUTS);

impl Input {
    /// The input's `connectability`, defaulting to [`Connectability::Full`]
    /// (C++ `UsdShadeInput::GetConnectability`).
    pub fn connectability(&self) -> Result<Connectability> {
        Ok(self
            .attribute
            .get_metadata::<Connectability>(META_CONNECTABILITY)?
            .unwrap_or_default())
    }

    /// Author this input's `connectability` metadata
    /// (C++ `UsdShadeInput::SetConnectability`).
    pub fn set_connectability(self, connectability: Connectability) -> Result<Self, usd::StageAuthoringError> {
        Ok(Self {
            attribute: self.attribute.set_metadata(META_CONNECTABILITY, connectability)?,
        })
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
    use crate::Result;

    use crate::schemas::shade::{Connectable, Shader};
    use crate::usd::Stage;

    #[test]
    fn invalid_base_name_reads_empty() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
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
}
