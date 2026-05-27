//! Token constants for the [UsdLux](super) schema family.
//!
//! Centralised so consumers can match against canonical strings instead of
//! retyping literals. Mirrors the grouping in Pixar's
//! `pxr/usd/usdLux/tokens.h`.

// ── Concrete light prim type names ──────────────────────────────────────
pub const T_DISTANT_LIGHT: &str = "DistantLight";
pub const T_SPHERE_LIGHT: &str = "SphereLight";
pub const T_RECT_LIGHT: &str = "RectLight";
pub const T_DISK_LIGHT: &str = "DiskLight";
pub const T_CYLINDER_LIGHT: &str = "CylinderLight";
pub const T_DOME_LIGHT: &str = "DomeLight";
pub const T_DOME_LIGHT_1: &str = "DomeLight_1";
pub const T_GEOMETRY_LIGHT: &str = "GeometryLight";
pub const T_PORTAL_LIGHT: &str = "PortalLight";
pub const T_LIGHT_FILTER: &str = "LightFilter";
pub const T_PLUGIN_LIGHT: &str = "PluginLight";
pub const T_PLUGIN_LIGHT_FILTER: &str = "PluginLightFilter";

// ── API schemas ─────────────────────────────────────────────────────────
pub const API_LIGHT: &str = "LightAPI";
pub const API_SHAPING: &str = "ShapingAPI";
pub const API_SHADOW: &str = "ShadowAPI";
pub const API_LIGHT_LIST: &str = "LightListAPI";
pub const API_MESH_LIGHT: &str = "MeshLightAPI";
pub const API_VOLUME_LIGHT: &str = "VolumeLightAPI";

// ── LightAPI attribute names ────────────────────────────────────────────
pub const A_INTENSITY: &str = "inputs:intensity";
pub const A_EXPOSURE: &str = "inputs:exposure";
pub const A_DIFFUSE: &str = "inputs:diffuse";
pub const A_SPECULAR: &str = "inputs:specular";
pub const A_NORMALIZE: &str = "inputs:normalize";
pub const A_COLOR: &str = "inputs:color";
pub const A_ENABLE_COLOR_TEMPERATURE: &str = "inputs:enableColorTemperature";
pub const A_COLOR_TEMPERATURE: &str = "inputs:colorTemperature";
pub const REL_FILTERS: &str = "light:filters";

// ── Concrete light attribute names ──────────────────────────────────────
// DistantLight
pub const A_ANGLE: &str = "inputs:angle";

// SphereLight / DiskLight / CylinderLight
pub const A_RADIUS: &str = "inputs:radius";
pub const A_TREAT_AS_POINT: &str = "treatAsPoint";
pub const A_TREAT_AS_LINE: &str = "treatAsLine";

// RectLight / CylinderLight / PortalLight
pub const A_WIDTH: &str = "inputs:width";
pub const A_HEIGHT: &str = "inputs:height";
pub const A_LENGTH: &str = "inputs:length";

// RectLight / DomeLight
pub const A_TEXTURE_FILE: &str = "inputs:texture:file";
pub const A_TEXTURE_FORMAT: &str = "inputs:texture:format";

// DomeLight extras
pub const REL_PORTALS: &str = "portals";
pub const A_GUIDE_RADIUS: &str = "guideRadius";
// DomeLight_1 only.
pub const A_POLE_AXIS: &str = "poleAxis";
pub const POLE_AXIS_SCENE_UP: &str = "scene";
pub const POLE_AXIS_Y: &str = "Y";
pub const POLE_AXIS_Z: &str = "Z";

// GeometryLight
pub const REL_GEOMETRY: &str = "geometry";

// DomeLight texture:format token values.
pub const TEXTURE_FORMAT_AUTOMATIC: &str = "automatic";
pub const TEXTURE_FORMAT_LATLONG: &str = "latlong";
pub const TEXTURE_FORMAT_MIRRORED_BALL: &str = "mirroredBall";
pub const TEXTURE_FORMAT_ANGULAR: &str = "angular";
pub const TEXTURE_FORMAT_CUBE_MAP_VERTICAL_CROSS: &str = "cubeMapVerticalCross";

// ── ShapingAPI attribute names ──────────────────────────────────────────
pub const A_SHAPING_FOCUS: &str = "inputs:shaping:focus";
pub const A_SHAPING_FOCUS_TINT: &str = "inputs:shaping:focusTint";
pub const A_SHAPING_CONE_ANGLE: &str = "inputs:shaping:cone:angle";
pub const A_SHAPING_CONE_SOFTNESS: &str = "inputs:shaping:cone:softness";
pub const A_SHAPING_IES_FILE: &str = "inputs:shaping:ies:file";
pub const A_SHAPING_IES_ANGLE_SCALE: &str = "inputs:shaping:ies:angleScale";
pub const A_SHAPING_IES_NORMALIZE: &str = "inputs:shaping:ies:normalize";

// ── ShadowAPI attribute names ───────────────────────────────────────────
pub const A_SHADOW_ENABLE: &str = "inputs:shadow:enable";
pub const A_SHADOW_COLOR: &str = "inputs:shadow:color";
pub const A_SHADOW_DISTANCE: &str = "inputs:shadow:distance";
pub const A_SHADOW_FALLOFF: &str = "inputs:shadow:falloff";
pub const A_SHADOW_FALLOFF_GAMMA: &str = "inputs:shadow:falloffGamma";

// ── LightListAPI attribute / relationship names ─────────────────────────
pub const REL_LIGHT_LIST: &str = "lightList";
pub const A_LIGHT_LIST_CACHE_BEHAVIOR: &str = "lightList:cacheBehavior";

// LightListAPI.cacheBehavior token values.
pub const CACHE_BEHAVIOR_CONSUME_AND_CONTINUE: &str = "consumeAndContinue";
pub const CACHE_BEHAVIOR_CONSUME_AND_HALT: &str = "consumeAndHalt";
pub const CACHE_BEHAVIOR_IGNORE: &str = "ignore";
