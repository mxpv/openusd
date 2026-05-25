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

// Orientation token values.
pub const ORIENTATION_RIGHT_HANDED: &str = "rightHanded";
pub const ORIENTATION_LEFT_HANDED: &str = "leftHanded";

// ── Common model-hierarchy metadata field (not a UsdGeom attribute, but
//    the geom readers surface it for convenience). ───────────────────────
pub const META_KIND: &str = "kind";
