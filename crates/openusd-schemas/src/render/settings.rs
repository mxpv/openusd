//! What a stage says about which `Settings` it renders through, which
//! is stage metadata rather than a property of the prim.

use openusd::Result;
use openusd::sdf::{self, Value};
use openusd::usd::Stage;

use super::Settings;
use super::tokens;

impl Settings {
    /// Resolve the stage's default `Settings` from the
    /// `renderSettingsPrimPath` stage metadata (C++
    /// `UsdRenderSettings::GetStageRenderSettings`). Composes a session-layer
    /// opinion over the root layer; returns `None` when unauthored.
    ///
    /// Read-only: authoring this stage metadata needs a generic stage-metadata
    /// setter the core `Stage` API does not yet expose.
    pub fn stage_settings_path(stage: &Stage) -> Result<Option<sdf::Path>> {
        Ok(stage
            .stage_metadata(tokens::RENDER_SETTINGS_PRIM_PATH)?
            .as_ref()
            .and_then(Value::as_str)
            .map(sdf::Path::new)
            .transpose()?)
    }
}
