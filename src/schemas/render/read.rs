//! Reader functions for the [UsdRender](super) schema family.
//!
//! UsdRender attributes are `uniform` (not time-sampled), so the readers
//! take no `time` argument — each returns the attribute's `default`
//! field, matching Pixar's `UsdAttribute::Get(value)` no-time semantic.
//! Unauthored attributes fall back to the documented defaults via the
//! `Default` impls in [`super::types`].

use anyhow::Result;

use crate::sdf::{FieldKey, Path, Value};
use crate::usd::Stage;

use super::tokens::*;
use super::types::*;

/// Read the attributes shared by `RenderSettings` / `RenderProduct` via
/// their abstract base `RenderSettingsBase`. Per-field fallback to the
/// spec default ([`ReadSettingsBase::default`]) for any unauthored attr.
///
/// Not type-gated — both concrete schemas carry these attributes, and the
/// computed render spec reads the base off each prim regardless of which.
pub fn read_settings_base(stage: &Stage, prim: &Path) -> Result<ReadSettingsBase> {
    read_base_with_fallback(stage, prim, &ReadSettingsBase::default())
}

/// Read the base attributes on a `RenderProduct`, layering authored
/// product opinions over the already-resolved settings `base`.
///
/// This is the product-overrides-settings rule (spec): a product attribute
/// overrides the settings value **only if it is explicitly authored on the
/// product** — mirroring C++ `_Get(attr, val, getDefaultValue=false)`,
/// which uses the value only when `attr.HasAuthoredValue()`. An unauthored
/// product attribute inherits the (fallback-resolved) settings value, never
/// the bare spec default.
pub fn read_base_overriding(stage: &Stage, product: &Path, base: &ReadSettingsBase) -> Result<ReadSettingsBase> {
    read_base_with_fallback(stage, product, base)
}

/// Reads each base attribute, falling back to the matching field of
/// `fallback` for any unauthored attribute. With `fallback = defaults`
/// this resolves the spec fallbacks; with `fallback = settings-base` it
/// implements the product override.
fn read_base_with_fallback(stage: &Stage, prim: &Path, fallback: &ReadSettingsBase) -> Result<ReadSettingsBase> {
    Ok(ReadSettingsBase {
        resolution: read_int2(stage, prim, A_RESOLUTION)?.unwrap_or(fallback.resolution),
        pixel_aspect_ratio: read_f32(stage, prim, A_PIXEL_ASPECT_RATIO)?.unwrap_or(fallback.pixel_aspect_ratio),
        aspect_ratio_conform_policy: read_token(stage, prim, A_ASPECT_RATIO_CONFORM_POLICY)?
            .and_then(|t| AspectRatioConformPolicy::from_token(&t))
            .unwrap_or(fallback.aspect_ratio_conform_policy),
        data_window_ndc: read_float4(stage, prim, A_DATA_WINDOW_NDC)?.unwrap_or(fallback.data_window_ndc),
        instantaneous_shutter: read_bool(stage, prim, A_INSTANTANEOUS_SHUTTER)?
            .unwrap_or(fallback.instantaneous_shutter),
        disable_motion_blur: read_bool(stage, prim, A_DISABLE_MOTION_BLUR)?.unwrap_or(fallback.disable_motion_blur),
        disable_depth_of_field: read_bool(stage, prim, A_DISABLE_DEPTH_OF_FIELD)?
            .unwrap_or(fallback.disable_depth_of_field),
        camera: read_rel_first_target(stage, prim, REL_CAMERA)?.or_else(|| fallback.camera.clone()),
    })
}

/// Read a `RenderSettings` prim — the inherited base attributes plus
/// the top-level configuration. Returns `None` when `prim` is not typed
/// `RenderSettings`, so a caller can't fabricate a defaulted struct from
/// an arbitrary prim.
pub fn read_render_settings(stage: &Stage, prim: &Path) -> Result<Option<ReadRenderSettings>> {
    if stage.type_name(prim)?.as_deref() != Some(T_RENDER_SETTINGS) {
        return Ok(None);
    }
    let d = ReadRenderSettings::default();
    Ok(Some(ReadRenderSettings {
        base: read_settings_base(stage, prim)?,
        products: read_rel_targets(stage, prim, REL_PRODUCTS)?,
        included_purposes: read_token_vec(stage, prim, A_INCLUDED_PURPOSES)?.unwrap_or(d.included_purposes),
        material_binding_purposes: read_token_vec(stage, prim, A_MATERIAL_BINDING_PURPOSES)?
            .unwrap_or(d.material_binding_purposes),
        rendering_color_space: read_token(stage, prim, A_RENDERING_COLOR_SPACE)?,
    }))
}

/// Read a `RenderProduct` prim. Returns `None` when `prim` is not typed
/// `RenderProduct`.
pub fn read_render_product(stage: &Stage, prim: &Path) -> Result<Option<ReadRenderProduct>> {
    if stage.type_name(prim)?.as_deref() != Some(T_RENDER_PRODUCT) {
        return Ok(None);
    }
    Ok(Some(ReadRenderProduct {
        base: read_settings_base(stage, prim)?,
        product_type: read_token(stage, prim, A_PRODUCT_TYPE)?
            .and_then(|t| ProductType::from_token(&t))
            .unwrap_or_default(),
        product_name: read_token(stage, prim, A_PRODUCT_NAME)?.unwrap_or_default(),
        ordered_vars: read_rel_targets(stage, prim, REL_ORDERED_VARS)?,
    }))
}

/// Read a `RenderVar` prim. Returns `None` when `prim` is not typed
/// `RenderVar`.
pub fn read_render_var(stage: &Stage, prim: &Path) -> Result<Option<ReadRenderVar>> {
    if stage.type_name(prim)?.as_deref() != Some(T_RENDER_VAR) {
        return Ok(None);
    }
    let d = ReadRenderVar::default();
    Ok(Some(ReadRenderVar {
        data_type: read_token(stage, prim, A_DATA_TYPE)?.unwrap_or(d.data_type),
        source_name: read_token(stage, prim, A_SOURCE_NAME)?.unwrap_or(d.source_name),
        source_type: read_token(stage, prim, A_SOURCE_TYPE)?
            .and_then(|t| SourceType::from_token(&t))
            .unwrap_or(d.source_type),
    }))
}

/// Resolve the stage's default `RenderSettings` prim from the
/// `renderSettingsPrimPath` root-layer metadata (spec). Returns `None`
/// when the metadata is unauthored.
///
/// Read-only: authoring this stage metadata needs a generic root-layer
/// metadata setter that the core `Stage` API does not yet expose.
pub fn get_stage_render_settings(stage: &Stage) -> Result<Option<Path>> {
    Ok(
        match stage.field::<Value>(Path::abs_root(), META_RENDER_SETTINGS_PRIM_PATH)? {
            Some(Value::String(s) | Value::Token(s)) => Some(Path::new(&s)?),
            _ => None,
        },
    )
}

/// Read a `RenderPass` prim. Returns `None` when `prim` is not typed
/// `RenderPass`. The `renderVisibility` / `cameraVisibility` / `prune` /
/// `matte` collection memberships are not modelled yet (only their
/// `includeRoot` flags are read).
pub fn read_render_pass(stage: &Stage, prim: &Path) -> Result<Option<ReadRenderPass>> {
    if stage.type_name(prim)?.as_deref() != Some(T_RENDER_PASS) {
        return Ok(None);
    }
    let d = ReadRenderPass::default();
    Ok(Some(ReadRenderPass {
        pass_type: read_token(stage, prim, A_PASS_TYPE)?,
        command: read_token_vec(stage, prim, A_COMMAND)?.unwrap_or_default(),
        file_name: read_asset(stage, prim, A_FILE_NAME)?,
        render_source: read_rel_first_target(stage, prim, REL_RENDER_SOURCE)?,
        input_passes: read_rel_targets(stage, prim, REL_INPUT_PASSES)?,
        render_visibility_include_root: read_bool(stage, prim, A_RENDER_VISIBILITY_INCLUDE_ROOT)?
            .unwrap_or(d.render_visibility_include_root),
        camera_visibility_include_root: read_bool(stage, prim, A_CAMERA_VISIBILITY_INCLUDE_ROOT)?
            .unwrap_or(d.camera_visibility_include_root),
    }))
}

/// Read a camera prim's `(horizontalAperture, verticalAperture)`, falling
/// back to `UsdGeomCamera`'s defaults `(20.955, 15.2908)` mm. Reads the
/// aperture attributes by name so it needs no dependency on the `geom`
/// feature — the conform policy only needs these two floats.
pub fn read_camera_aperture(stage: &Stage, camera: &Path) -> Result<[f32; 2]> {
    Ok([
        read_f32(stage, camera, "horizontalAperture")?.unwrap_or(20.955),
        read_f32(stage, camera, "verticalAperture")?.unwrap_or(15.2908),
    ])
}

// ── value-read helpers ──────────────────────────────────────────────

fn attr_value(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Value>> {
    stage.field::<Value>(prim.append_property(name)?, FieldKey::Default)
}

/// Narrow a `f64` to `f32`, clamping to the finite `f32` range so a large
/// authored double can't silently become `inf`.
fn f64_to_f32(d: f64) -> f32 {
    d.clamp(f32::MIN as f64, f32::MAX as f64) as f32
}

fn read_f32(stage: &Stage, prim: &Path, name: &str) -> Result<Option<f32>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Float(f)) => Some(f),
        Some(Value::Double(d)) => Some(f64_to_f32(d)),
        Some(Value::Half(h)) => Some(h.to_f32()),
        _ => None,
    })
}

fn read_bool(stage: &Stage, prim: &Path, name: &str) -> Result<Option<bool>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    })
}

fn read_token(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Token(s) | Value::String(s)) => Some(s),
        _ => None,
    })
}

fn read_int2(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[i32; 2]>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Vec2i(v)) => Some(v),
        _ => None,
    })
}

fn read_float4(stage: &Stage, prim: &Path, name: &str) -> Result<Option<[f32; 4]>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::Vec4f(v)) => Some(v),
        Some(Value::Vec4d(v)) => Some([f64_to_f32(v[0]), f64_to_f32(v[1]), f64_to_f32(v[2]), f64_to_f32(v[3])]),
        _ => None,
    })
}

fn read_token_vec(stage: &Stage, prim: &Path, name: &str) -> Result<Option<Vec<String>>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::TokenVec(v) | Value::StringVec(v)) => Some(v),
        _ => None,
    })
}

fn read_asset(stage: &Stage, prim: &Path, name: &str) -> Result<Option<String>> {
    Ok(match attr_value(stage, prim, name)? {
        Some(Value::AssetPath(s) | Value::String(s) | Value::Token(s)) => Some(s),
        _ => None,
    })
}

fn read_rel_targets(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Vec<String>> {
    let rel_path = prim.append_property(rel_name)?;
    let paths = match stage.field::<Value>(rel_path, FieldKey::TargetPaths)? {
        Some(Value::PathListOp(op)) => op.flatten(),
        Some(Value::PathVec(v)) => v,
        _ => Vec::new(),
    };
    Ok(paths.into_iter().map(|p| p.as_str().to_string()).collect())
}

fn read_rel_first_target(stage: &Stage, prim: &Path, rel_name: &str) -> Result<Option<String>> {
    Ok(read_rel_targets(stage, prim, rel_name)?.into_iter().next())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::schemas::render::{define_render_product, define_render_settings, SettingsBaseSetters};
    use crate::sdf;

    /// A product attribute overrides the settings value only where the
    /// product authors it; everything else inherits the resolved settings.
    #[test]
    fn product_overrides_only_authored_attrs() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_settings(&stage, sdf::path("/Render/Settings")?)?
            .set_resolution([1920, 1080])?
            .set_pixel_aspect_ratio(2.0)?;
        // Product authors only `resolution`.
        define_render_product(&stage, sdf::path("/Render/Products/p")?)?.set_resolution([512, 512])?;

        let settings_base = read_settings_base(&stage, &sdf::path("/Render/Settings")?)?;
        let resolved = read_base_overriding(&stage, &sdf::path("/Render/Products/p")?, &settings_base)?;
        assert_eq!(resolved.resolution, [512, 512]); // overridden by the product
        assert!((resolved.pixel_aspect_ratio - 2.0).abs() < 1e-6); // inherited from settings
        Ok(())
    }

    /// A product that authors nothing inherits the settings verbatim — and
    /// an unauthored product attribute inherits the *settings* value, not
    /// the bare spec default.
    #[test]
    fn product_without_opinions_inherits_settings() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        define_render_settings(&stage, sdf::path("/Render/Settings")?)?
            .set_resolution([800, 600])?
            .set_aspect_ratio_conform_policy(AspectRatioConformPolicy::CropAperture)?;
        define_render_product(&stage, sdf::path("/Render/Products/p")?)?;

        let settings_base = read_settings_base(&stage, &sdf::path("/Render/Settings")?)?;
        let resolved = read_base_overriding(&stage, &sdf::path("/Render/Products/p")?, &settings_base)?;
        assert_eq!(resolved, settings_base);
        assert_eq!(resolved.resolution, [800, 600]);
        // Not the ExpandAperture spec default — the settings value carries.
        assert_eq!(
            resolved.aspect_ratio_conform_policy,
            AspectRatioConformPolicy::CropAperture
        );
        Ok(())
    }

    #[test]
    fn camera_aperture_reads_authored_then_defaults() -> Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let cam = stage.define_prim(sdf::path("/World/Cam")?)?.set_type_name("Camera")?;
        stage
            .create_attribute(cam.path().append_property("horizontalAperture")?, "float")?
            .set(Value::Float(36.0))?;
        // verticalAperture left unauthored → falls back to the USD default.
        let aperture = read_camera_aperture(&stage, &sdf::path("/World/Cam")?)?;
        assert!((aperture[0] - 36.0).abs() < 1e-4);
        assert!((aperture[1] - 15.2908).abs() < 1e-4);
        Ok(())
    }
}
