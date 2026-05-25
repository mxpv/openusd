//! Token constants for the [UsdGeom](super) schema family.
//!
//! Centralised so consumers can match against canonical strings instead
//! of retyping literals. Mirrors the grouping in Pixar's
//! `pxr/usd/usdGeom/tokens.h`.

// ── Abstract / concrete prim type names ─────────────────────────────────
pub const T_XFORM: &str = "Xform";
pub const T_SCOPE: &str = "Scope";
pub const T_MESH: &str = "Mesh";
pub const T_CUBE: &str = "Cube";
pub const T_SPHERE: &str = "Sphere";
pub const T_CYLINDER: &str = "Cylinder";
pub const T_CAPSULE: &str = "Capsule";
pub const T_CONE: &str = "Cone";
pub const T_PLANE: &str = "Plane";
pub const T_BASIS_CURVES: &str = "BasisCurves";
pub const T_NURBS_CURVES: &str = "NurbsCurves";
pub const T_NURBS_PATCH: &str = "NurbsPatch";
pub const T_HERMITE_CURVES: &str = "HermiteCurves";
pub const T_POINTS: &str = "Points";
pub const T_TET_MESH: &str = "TetMesh";
pub const T_GEOM_SUBSET: &str = "GeomSubset";
pub const T_CAMERA: &str = "Camera";
pub const T_POINT_INSTANCER: &str = "PointInstancer";

// ── Imageable attribute names (every Gprim inherits these) ──────────────
pub const A_VISIBILITY: &str = "visibility";
pub const A_PURPOSE: &str = "purpose";
pub const REL_PROXY_PRIM: &str = "proxyPrim";

// Visibility token values (§ UsdGeomImageable).
pub const VISIBILITY_INHERITED: &str = "inherited";
pub const VISIBILITY_INVISIBLE: &str = "invisible";

// Purpose token values (§ UsdGeomImageable).
pub const PURPOSE_DEFAULT: &str = "default";
pub const PURPOSE_RENDER: &str = "render";
pub const PURPOSE_PROXY: &str = "proxy";
pub const PURPOSE_GUIDE: &str = "guide";

// ── Boundable attribute names ───────────────────────────────────────────
pub const A_EXTENT: &str = "extent";

// ── Gprim shared attributes ─────────────────────────────────────────────
pub const A_DOUBLE_SIDED: &str = "doubleSided";
pub const A_ORIENTATION: &str = "orientation";

// ── Intrinsic-shape attributes ──────────────────────────────────────────
pub const A_SIZE: &str = "size";
pub const A_RADIUS: &str = "radius";
pub const A_HEIGHT: &str = "height";
pub const A_AXIS: &str = "axis";
pub const A_WIDTH: &str = "width";
pub const A_LENGTH: &str = "length";

// Axis token values (radial shapes + Plane).
pub const AXIS_X: &str = "X";
pub const AXIS_Y: &str = "Y";
pub const AXIS_Z: &str = "Z";

// ── Camera attribute names ──────────────────────────────────────────────
pub const A_FOCAL_LENGTH: &str = "focalLength";
pub const A_HORIZONTAL_APERTURE: &str = "horizontalAperture";
pub const A_VERTICAL_APERTURE: &str = "verticalAperture";
pub const A_HORIZONTAL_APERTURE_OFFSET: &str = "horizontalApertureOffset";
pub const A_VERTICAL_APERTURE_OFFSET: &str = "verticalApertureOffset";
pub const A_F_STOP: &str = "fStop";
pub const A_FOCUS_DISTANCE: &str = "focusDistance";
pub const A_PROJECTION: &str = "projection";
pub const A_CLIPPING_RANGE: &str = "clippingRange";
pub const A_CLIPPING_PLANES: &str = "clippingPlanes";
pub const A_SHUTTER_OPEN: &str = "shutter:open";
pub const A_SHUTTER_CLOSE: &str = "shutter:close";
pub const A_EXPOSURE: &str = "exposure";
pub const A_EXPOSURE_ISO: &str = "exposure:iso";
pub const A_EXPOSURE_TIME: &str = "exposure:time";
pub const A_EXPOSURE_F_STOP: &str = "exposure:fStop";
pub const A_EXPOSURE_RESPONSIVITY: &str = "exposure:responsivity";
pub const A_STEREO_ROLE: &str = "stereoRole";

// Projection token values.
pub const PROJECTION_PERSPECTIVE: &str = "perspective";
pub const PROJECTION_ORTHOGRAPHIC: &str = "orthographic";

// Stereo-role token values.
pub const STEREO_ROLE_MONO: &str = "mono";
pub const STEREO_ROLE_LEFT: &str = "left";
pub const STEREO_ROLE_RIGHT: &str = "right";

// Orientation token values.
pub const ORIENTATION_RIGHT_HANDED: &str = "rightHanded";
pub const ORIENTATION_LEFT_HANDED: &str = "leftHanded";

// ── Common model-hierarchy metadata field (not a UsdGeom attribute, but
//    the geom readers surface it for convenience). ───────────────────────
pub const META_KIND: &str = "kind";
