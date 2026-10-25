//! What a stage says about which `Settings` it renders through, which
//! is stage metadata rather than a property of the prim.

use openusd::Result;
use openusd::sdf;
use openusd::usd::Stage;

use super::{Settings, StageMetadata};

impl Settings {
    /// The `Settings` the stage renders through by default, the prim its
    /// `renderSettingsPrimPath` metadata names (C++
    /// `UsdRenderSettings::GetStageRenderSettings`). `None` where the metadata
    /// names nothing, or names a path that is not a `Settings` prim.
    ///
    /// A path the metadata holds that does not parse is an error, where C++
    /// answers no settings.
    pub fn stage_settings(stage: &Stage) -> Result<Option<Settings>> {
        match Self::stage_settings_path(stage)? {
            Some(path) => Self::get(stage, path),
            None => Ok(None),
        }
    }

    /// The path the stage's `renderSettingsPrimPath` metadata holds, composed
    /// from the session layer over the root layer, or `None` where it is
    /// empty, the field's declared default.
    pub fn stage_settings_path(stage: &Stage) -> Result<Option<sdf::Path>> {
        Ok(stage
            .render_settings_prim_path()?
            .filter(|path| !path.is_empty())
            .map(|path| sdf::Path::new(path.as_str()))
            .transpose()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stage whose `renderSettingsPrimPath` is `path`, holding a `Settings`
    /// prim at `/Settings` and a `Scope` at `/Scope`.
    fn stage(path: &str) -> Result<Stage> {
        let stage = crate::tests::stage("anon.usda")?;
        Settings::define(&stage, "/Settings")?;
        stage.define_prim("/Scope")?.set_type_name("Scope")?;
        stage.set_render_settings_prim_path(path.to_string())?;
        Ok(stage)
    }

    #[test]
    fn stage_settings_typed() -> Result<()> {
        let settings = Settings::stage_settings(&stage("/Settings")?)?.expect("the stage's settings");
        assert_eq!(settings.path().as_str(), "/Settings");
        Ok(())
    }

    #[test]
    fn stage_settings_not_settings() -> Result<()> {
        assert!(Settings::stage_settings(&stage("/Scope")?)?.is_none());
        Ok(())
    }

    /// A property of the `Settings` prim names no settings.
    #[test]
    fn stage_settings_property_path() -> Result<()> {
        assert!(Settings::stage_settings(&stage("/Settings.camera")?)?.is_none());
        Ok(())
    }
}
