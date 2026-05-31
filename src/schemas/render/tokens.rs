//! Token constants for the [UsdRender](super) schema family.
//!
//! Centralised so consumers match against canonical strings instead of
//! retyping literals. Mirrors the grouping in Pixar's
//! `pxr/usd/usdRender/tokens.h`.

// ── Concrete + abstract prim type names ─────────────────────────────
/// Abstract base of both [`T_RENDER_SETTINGS`] and [`T_RENDER_PRODUCT`];
/// carries the shared camera + framing attributes.
pub const T_RENDER_SETTINGS_BASE: &str = "RenderSettingsBase";
pub const T_RENDER_SETTINGS: &str = "RenderSettings";
pub const T_RENDER_PRODUCT: &str = "RenderProduct";
pub const T_RENDER_VAR: &str = "RenderVar";
pub const T_RENDER_PASS: &str = "RenderPass";
/// Denoise pass — a `dev`-era schema, not in core `release`.
pub const T_RENDER_DENOISE_PASS: &str = "RenderDenoisePass";

// ── RenderSettingsBase attributes (shared) ──────────────────────────
pub const A_RESOLUTION: &str = "resolution";
pub const A_PIXEL_ASPECT_RATIO: &str = "pixelAspectRatio";
pub const A_ASPECT_RATIO_CONFORM_POLICY: &str = "aspectRatioConformPolicy";
pub const A_DATA_WINDOW_NDC: &str = "dataWindowNDC";
/// Deprecated in the C++ `UsdRender` schema, superseded by
/// [`A_DISABLE_MOTION_BLUR`]; still read so older assets round-trip.
pub const A_INSTANTANEOUS_SHUTTER: &str = "instantaneousShutter";
pub const A_DISABLE_MOTION_BLUR: &str = "disableMotionBlur";
pub const A_DISABLE_DEPTH_OF_FIELD: &str = "disableDepthOfField";
/// `camera` relationship — targets the primary `UsdGeomCamera`.
pub const REL_CAMERA: &str = "camera";

// ── RenderSettings attributes ───────────────────────────────────────
pub const REL_PRODUCTS: &str = "products";
pub const A_INCLUDED_PURPOSES: &str = "includedPurposes";
pub const A_MATERIAL_BINDING_PURPOSES: &str = "materialBindingPurposes";
pub const A_RENDERING_COLOR_SPACE: &str = "renderingColorSpace";

// ── RenderProduct attributes ────────────────────────────────────────
pub const A_PRODUCT_TYPE: &str = "productType";
/// Note: `productName` is *not* `uniform` (unlike most base attrs).
pub const A_PRODUCT_NAME: &str = "productName";
pub const REL_ORDERED_VARS: &str = "orderedVars";

// ── RenderVar attributes ────────────────────────────────────────────
pub const A_DATA_TYPE: &str = "dataType";
pub const A_SOURCE_NAME: &str = "sourceName";
pub const A_SOURCE_TYPE: &str = "sourceType";

// ── RenderPass attributes ───────────────────────────────────────────
pub const A_PASS_TYPE: &str = "passType";
pub const A_COMMAND: &str = "command";
pub const A_FILE_NAME: &str = "fileName";
pub const REL_RENDER_SOURCE: &str = "renderSource";
pub const REL_INPUT_PASSES: &str = "inputPasses";

// RenderPass multiple-apply CollectionAPI instance names (`prune` /
// `matte` are `dev`-era). The membership relationships are authored as
// `collection:<name>:…`; each instance also carries a
// `collection:<name>:includeRoot` bool.
pub const COLLECTION_RENDER_VISIBILITY: &str = "renderVisibility";
pub const COLLECTION_CAMERA_VISIBILITY: &str = "cameraVisibility";
pub const COLLECTION_PRUNE: &str = "prune";
pub const COLLECTION_MATTE: &str = "matte";
pub const A_RENDER_VISIBILITY_INCLUDE_ROOT: &str = "collection:renderVisibility:includeRoot";
pub const A_CAMERA_VISIBILITY_INCLUDE_ROOT: &str = "collection:cameraVisibility:includeRoot";

// ── RenderDenoisePass attributes (dev) ──────────────────────────────
pub const A_DENOISE_ENABLE: &str = "denoiseEnable";
pub const REL_DENOISE_PASS: &str = "denoisePass";

// ── aspectRatioConformPolicy token values ───────────────────────────
pub const CONFORM_EXPAND_APERTURE: &str = "expandAperture";
pub const CONFORM_CROP_APERTURE: &str = "cropAperture";
pub const CONFORM_ADJUST_APERTURE_WIDTH: &str = "adjustApertureWidth";
pub const CONFORM_ADJUST_APERTURE_HEIGHT: &str = "adjustApertureHeight";
pub const CONFORM_ADJUST_PIXEL_ASPECT_RATIO: &str = "adjustPixelAspectRatio";

// ── productType token values ────────────────────────────────────────
pub const PRODUCT_TYPE_RASTER: &str = "raster";
pub const PRODUCT_TYPE_DEEP_RASTER: &str = "deepRaster";

// ── sourceType token values ─────────────────────────────────────────
pub const SOURCE_TYPE_RAW: &str = "raw";
pub const SOURCE_TYPE_PRIMVAR: &str = "primvar";
pub const SOURCE_TYPE_LPE: &str = "lpe";
pub const SOURCE_TYPE_INTRINSIC: &str = "intrinsic";

// ── Stage metadata ──────────────────────────────────────────────────
/// Root/session-layer metadata naming the default `RenderSettings` prim.
pub const META_RENDER_SETTINGS_PRIM_PATH: &str = "renderSettingsPrimPath";
