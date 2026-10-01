//! What a stage says about which `Settings` it renders through, which
//! is stage metadata rather than a property of the prim.

use openusd::Result;
use openusd::sdf;
use openusd::usd::Stage;

use super::{Settings, StageMetadata};

impl Settings {
    /// Resolve the stage's default `Settings` from the
    /// `renderSettingsPrimPath` stage metadata (C++
    /// `UsdRenderSettings::GetStageRenderSettings`). Composes a session-layer
    /// opinion over the root layer; returns `None` where the path is empty,
    /// which is the field's declared default.
    pub fn stage_settings_path(stage: &Stage) -> Result<Option<sdf::Path>> {
        Ok(stage
            .render_settings_prim_path()?
            .filter(|path| !path.is_empty())
            .map(|path| sdf::Path::new(path.as_str()))
            .transpose()?)
    }
}
