//! Decoded structs and enums returned by [`super::read`] functions.
//!
//! Pixar's defaults are baked into each `Default` impl so callers that
//! don't want to deal with `Option<f32>` everywhere can `unwrap_or_default()`
//! to get spec-correct fallbacks. Authored opinions override.

use super::tokens::*;

/// `UsdLuxDomeLight.inputs:texture:format` token values.
///
/// Per Pixar's schema the default is [`TextureFormat::Automatic`] —
/// the renderer picks based on the image aspect ratio.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TextureFormat {
    #[default]
    Automatic,
    Latlong,
    MirroredBall,
    Angular,
    CubeMapVerticalCross,
}

impl TextureFormat {
    pub fn as_token(self) -> &'static str {
        match self {
            TextureFormat::Automatic => TEXTURE_FORMAT_AUTOMATIC,
            TextureFormat::Latlong => TEXTURE_FORMAT_LATLONG,
            TextureFormat::MirroredBall => TEXTURE_FORMAT_MIRRORED_BALL,
            TextureFormat::Angular => TEXTURE_FORMAT_ANGULAR,
            TextureFormat::CubeMapVerticalCross => TEXTURE_FORMAT_CUBE_MAP_VERTICAL_CROSS,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            TEXTURE_FORMAT_AUTOMATIC => TextureFormat::Automatic,
            TEXTURE_FORMAT_LATLONG => TextureFormat::Latlong,
            TEXTURE_FORMAT_MIRRORED_BALL => TextureFormat::MirroredBall,
            TEXTURE_FORMAT_ANGULAR => TextureFormat::Angular,
            TEXTURE_FORMAT_CUBE_MAP_VERTICAL_CROSS => TextureFormat::CubeMapVerticalCross,
            _ => return None,
        })
    }
}

/// `UsdLuxDomeLight_1.poleAxis` token values.
///
/// Selects which axis points to the dome's "north pole" — i.e. which
/// axis the texture wraps around. Pixar's spec default is
/// [`PoleAxis::SceneUp`], which defers to the stage's `upAxis` metadata.
/// Only meaningful on `DomeLight_1`; legacy `DomeLight` has no
/// equivalent attribute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PoleAxis {
    #[default]
    SceneUp,
    Y,
    Z,
}

impl PoleAxis {
    pub fn as_token(self) -> &'static str {
        match self {
            PoleAxis::SceneUp => POLE_AXIS_SCENE_UP,
            PoleAxis::Y => POLE_AXIS_Y,
            PoleAxis::Z => POLE_AXIS_Z,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            POLE_AXIS_SCENE_UP => PoleAxis::SceneUp,
            POLE_AXIS_Y => PoleAxis::Y,
            POLE_AXIS_Z => PoleAxis::Z,
            _ => return None,
        })
    }
}

/// `UsdLuxLightListAPI.lightList:cacheBehavior` token values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LightListCacheBehavior {
    /// Use the cached `lightList` rel and also continue traversing
    /// children for any additional lights. Spec default.
    #[default]
    ConsumeAndContinue,
    /// Use the cached `lightList` only; don't recurse into children.
    ConsumeAndHalt,
    /// Ignore the cache and traverse normally.
    Ignore,
}

impl LightListCacheBehavior {
    pub fn as_token(self) -> &'static str {
        match self {
            LightListCacheBehavior::ConsumeAndContinue => CACHE_BEHAVIOR_CONSUME_AND_CONTINUE,
            LightListCacheBehavior::ConsumeAndHalt => CACHE_BEHAVIOR_CONSUME_AND_HALT,
            LightListCacheBehavior::Ignore => CACHE_BEHAVIOR_IGNORE,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            CACHE_BEHAVIOR_CONSUME_AND_CONTINUE => LightListCacheBehavior::ConsumeAndContinue,
            CACHE_BEHAVIOR_CONSUME_AND_HALT => LightListCacheBehavior::ConsumeAndHalt,
            CACHE_BEHAVIOR_IGNORE => LightListCacheBehavior::Ignore,
            _ => return None,
        })
    }
}

/// `UsdLuxLightAPI` — the common light parameters every UsdLux light
/// prim inherits.
///
/// Defaults match Pixar's schema exactly: intensity 1, exposure 0,
/// diffuse 1, specular 1, normalize off, white colour, color
/// temperature disabled (default 6500 K when enabled).
#[derive(Debug, Clone, PartialEq)]
pub struct ReadLight {
    /// Path of the light prim carrying these inputs.
    pub path: String,
    /// `inputs:intensity` — relative scalar; combine with `2^exposure`.
    pub intensity: f32,
    /// `inputs:exposure` — stops above/below base intensity.
    pub exposure: f32,
    /// `inputs:diffuse` — diffuse-only multiplier.
    pub diffuse: f32,
    /// `inputs:specular` — specular-only multiplier.
    pub specular: f32,
    /// `inputs:normalize` — when true, divides intensity by the light's
    /// authored surface area. Spec default false.
    pub normalize: bool,
    /// `inputs:color` — sRGB linearised colour multiplier.
    pub color: [f32; 3],
    /// `inputs:enableColorTemperature` — when true the renderer
    /// computes the colour from [`Self::color_temperature`] instead of
    /// using [`Self::color`].
    pub enable_color_temperature: bool,
    /// `inputs:colorTemperature` — Kelvin. Spec default 6500.
    pub color_temperature: f32,
    /// `light:filters` rel targets — light-filter prims that modify
    /// this light's contribution. Empty when unauthored.
    pub filters: Vec<String>,
}

impl Default for ReadLight {
    fn default() -> Self {
        Self {
            path: String::new(),
            intensity: 1.0,
            exposure: 0.0,
            diffuse: 1.0,
            specular: 1.0,
            normalize: false,
            color: [1.0, 1.0, 1.0],
            enable_color_temperature: false,
            color_temperature: 6500.0,
            filters: Vec::new(),
        }
    }
}

/// `UsdLuxDistantLight` — directional / sun-style parallel light.
///
/// `angle` (in degrees) is the half-angle of the disc subtended by
/// the sun. Spec default 0.53° (the real sun's apparent angular
/// diameter ÷ 2). `intensity` defaults to 50000 (overriding LightAPI's
/// default of 1.0), because the spec models DistantLight as the sun
/// hitting Earth at ~50000 lux.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadDistantLight {
    pub common: ReadLight,
    pub angle_deg: f32,
}

impl Default for ReadDistantLight {
    fn default() -> Self {
        Self {
            common: ReadLight {
                intensity: 50000.0, // DistantLight overrides LightAPI's 1.0
                ..ReadLight::default()
            },
            angle_deg: 0.53,
        }
    }
}

/// `UsdLuxSphereLight`. Becomes a spot light when `ShapingAPI`'s cone
/// is authored.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadSphereLight {
    pub common: ReadLight,
    pub radius: f32,
    /// `treatAsPoint` — when true, the renderer treats the light as
    /// a zero-radius point (faster, no soft shadows).
    pub treat_as_point: bool,
}

impl Default for ReadSphereLight {
    fn default() -> Self {
        Self {
            common: ReadLight::default(),
            radius: 0.5,
            treat_as_point: false,
        }
    }
}

/// `UsdLuxRectLight` — rectangular area light. `texture:file` lets
/// the light be coloured from a texture (typical for softboxes /
/// projector-style setups).
#[derive(Debug, Clone, PartialEq)]
pub struct ReadRectLight {
    pub common: ReadLight,
    pub width: f32,
    pub height: f32,
    pub texture_file: Option<String>,
}

impl Default for ReadRectLight {
    fn default() -> Self {
        Self {
            common: ReadLight::default(),
            width: 1.0,
            height: 1.0,
            texture_file: None,
        }
    }
}

/// `UsdLuxDiskLight` — circular area light.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadDiskLight {
    pub common: ReadLight,
    pub radius: f32,
}

impl Default for ReadDiskLight {
    fn default() -> Self {
        Self {
            common: ReadLight::default(),
            radius: 0.5,
        }
    }
}

/// `UsdLuxCylinderLight` — tube / strip light.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadCylinderLight {
    pub common: ReadLight,
    pub length: f32,
    pub radius: f32,
    /// `treatAsLine` — analogous to `treatAsPoint` on SphereLight.
    pub treat_as_line: bool,
}

impl Default for ReadCylinderLight {
    fn default() -> Self {
        Self {
            common: ReadLight::default(),
            length: 1.0,
            radius: 0.5,
            treat_as_line: false,
        }
    }
}

/// `UsdLuxDomeLight` — image-based environment light.
///
/// `guideRadius` is a viewport-aid radius for the dome's visualisation
/// gizmo (it doesn't affect rendering). Spec default 1.0e5.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadDomeLight {
    pub common: ReadLight,
    /// `inputs:texture:file` — HDR / EXR environment map asset path.
    pub texture_file: Option<String>,
    /// `inputs:texture:format` — how the texture is unwrapped onto the
    /// dome. Spec default [`TextureFormat::Automatic`].
    pub texture_format: TextureFormat,
    /// `portals` rel targets — `UsdLuxPortalLight` prims that act as
    /// optical entry points for sampling this dome.
    pub portals: Vec<String>,
    pub guide_radius: f32,
    /// `DomeLight_1.poleAxis` — `None` on legacy `DomeLight` prims
    /// (the attribute doesn't exist there) and on `DomeLight_1` prims
    /// that don't author it.
    pub pole_axis: Option<PoleAxis>,
}

impl Default for ReadDomeLight {
    fn default() -> Self {
        Self {
            common: ReadLight::default(),
            texture_file: None,
            texture_format: TextureFormat::Automatic,
            portals: Vec::new(),
            guide_radius: 1.0e5,
            pole_axis: None,
        }
    }
}

/// `UsdLuxGeometryLight` — uses an arbitrary UsdGeom prim as the
/// emissive surface.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ReadGeometryLight {
    pub common: ReadLight,
    /// `geometry` rel — target prim to use as the light's surface.
    pub geometry: Option<String>,
}

/// `UsdLuxPortalLight` — an aperture for sampling a parent
/// `UsdLuxDomeLight` more efficiently from indoor scenes.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadPortalLight {
    pub common: ReadLight,
    pub width: f32,
    pub height: f32,
}

impl Default for ReadPortalLight {
    fn default() -> Self {
        Self {
            common: ReadLight::default(),
            width: 1.0,
            height: 1.0,
        }
    }
}

/// Dispatch enum for [`super::read::read_light`].
#[derive(Debug, Clone, PartialEq)]
pub enum ReadAnyLight {
    Distant(ReadDistantLight),
    Sphere(ReadSphereLight),
    Rect(ReadRectLight),
    Disk(ReadDiskLight),
    Cylinder(ReadCylinderLight),
    Dome(ReadDomeLight),
    Geometry(ReadGeometryLight),
    Portal(ReadPortalLight),
}

/// `UsdLuxShapingAPI` — focus / cone / IES profile, applied to any
/// light prim that wants directional shaping.
#[derive(Debug, Clone, PartialEq)]
pub struct ReadShaping {
    /// `inputs:shaping:focus` — exponent on the cosine falloff towards
    /// the light's primary axis. 0 disables focus (default).
    pub focus: f32,
    /// `inputs:shaping:focusTint` — colour mixed in at off-axis
    /// angles. Default `(0, 0, 0)` = no tint.
    pub focus_tint: [f32; 3],
    /// `inputs:shaping:cone:angle` — spotlight cone half-angle in
    /// degrees. Spec default 90 (i.e. effectively disabled — full
    /// hemisphere).
    pub cone_angle_deg: f32,
    /// `inputs:shaping:cone:softness` — `[0, 1]` feather between the
    /// hard cone edge (0) and a smooth falloff (1).
    pub cone_softness: f32,
    /// `inputs:shaping:ies:file` — photometric IES profile asset.
    pub ies_file: Option<String>,
    /// `inputs:shaping:ies:angleScale` — scales the IES profile's
    /// solid angle. 0 = no scale.
    pub ies_angle_scale: f32,
    /// `inputs:shaping:ies:normalize` — when true, normalises the IES
    /// profile's peak to 1.
    pub ies_normalize: bool,
}

impl Default for ReadShaping {
    fn default() -> Self {
        Self {
            focus: 0.0,
            focus_tint: [0.0, 0.0, 0.0],
            cone_angle_deg: 90.0,
            cone_softness: 0.0,
            ies_file: None,
            ies_angle_scale: 0.0,
            ies_normalize: false,
        }
    }
}

/// `UsdLuxShadowAPI` — shadow casting controls.
///
/// `distance` and `falloff` default to `-1.0` per Pixar — the
/// sentinel for "no maximum distance / no falloff". Renderers
/// treat negative values as "infinite".
#[derive(Debug, Clone, PartialEq)]
pub struct ReadShadow {
    /// `inputs:shadow:enable` — spec default true. When false the
    /// light still illuminates but doesn't occlude anything.
    pub enable: bool,
    /// `inputs:shadow:color` — colour tint applied to occluded
    /// surfaces. Default `(0, 0, 0)` = full black.
    pub color: [f32; 3],
    /// `inputs:shadow:distance` — max ray distance for shadow tests.
    /// `-1.0` (default) = unlimited.
    pub distance: f32,
    /// `inputs:shadow:falloff` — distance at which the shadow
    /// contribution falls off. `-1.0` (default) = no falloff.
    pub falloff: f32,
    /// `inputs:shadow:falloffGamma` — gamma applied to the falloff
    /// curve. Default 1.0.
    pub falloff_gamma: f32,
}

impl Default for ReadShadow {
    fn default() -> Self {
        Self {
            enable: true,
            color: [0.0, 0.0, 0.0],
            distance: -1.0,
            falloff: -1.0,
            falloff_gamma: 1.0,
        }
    }
}

/// `UsdLuxLightListAPI` — pre-computed list of lights under a prim,
/// usually authored on a root / asset prim to avoid traversal.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ReadLightList {
    /// `lightList` rel — paths of every light covered by the cache.
    pub lights: Vec<String>,
    /// `lightList:cacheBehavior` — controls how renderers should
    /// interpret the cache. Spec default
    /// [`LightListCacheBehavior::ConsumeAndContinue`].
    pub cache_behavior: LightListCacheBehavior,
}

/// Result of [`super::read::find_lux_prims`] — categorised path
/// lists from a single stage walk.
#[derive(Debug, Clone, Default)]
pub struct LuxPrims {
    pub distant: Vec<String>,
    pub sphere: Vec<String>,
    pub rect: Vec<String>,
    pub disk: Vec<String>,
    pub cylinder: Vec<String>,
    pub dome: Vec<String>,
    pub geometry: Vec<String>,
    pub portal: Vec<String>,
    pub light_filters: Vec<String>,
    /// Prims that carry `LightAPI`, `MeshLightAPI`, or
    /// `VolumeLightAPI` as an applied schema *without* being one of
    /// the concrete UsdLux light types already bucketed above. This is
    /// how renderers turn arbitrary meshes / volumes into emissive
    /// surfaces; consumers shouldn't have to repeat the apiSchemas walk.
    pub light_api: Vec<String>,
    /// Prims with `ShapingAPI` applied (typically spot lights).
    pub shaping: Vec<String>,
    /// Prims with `ShadowAPI` applied.
    pub shadow: Vec<String>,
    /// Prims with `LightListAPI` applied (root prims with cached light
    /// lists).
    pub light_list: Vec<String>,
}
