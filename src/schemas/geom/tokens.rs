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

// ── PointBased attribute names (shared by Mesh, Points, Curves, …) ──────
pub const A_POINTS: &str = "points";
pub const A_NORMALS: &str = "normals";
pub const A_VELOCITIES: &str = "velocities";
pub const A_ACCELERATIONS: &str = "accelerations";

// ── Mesh attribute names ────────────────────────────────────────────────
pub const A_FACE_VERTEX_COUNTS: &str = "faceVertexCounts";
pub const A_FACE_VERTEX_INDICES: &str = "faceVertexIndices";
pub const A_SUBDIVISION_SCHEME: &str = "subdivisionScheme";
pub const A_INTERPOLATE_BOUNDARY: &str = "interpolateBoundary";
pub const A_FACE_VARYING_LINEAR_INTERPOLATION: &str = "faceVaryingLinearInterpolation";
pub const A_TRIANGLE_SUBDIVISION_RULE: &str = "triangleSubdivisionRule";
pub const A_HOLE_INDICES: &str = "holeIndices";
pub const A_CORNER_INDICES: &str = "cornerIndices";
pub const A_CORNER_SHARPNESSES: &str = "cornerSharpnesses";
pub const A_CREASE_INDICES: &str = "creaseIndices";
pub const A_CREASE_LENGTHS: &str = "creaseLengths";
pub const A_CREASE_SHARPNESSES: &str = "creaseSharpnesses";

// Mesh subdivision scheme token values.
pub const SUBDIV_SCHEME_NONE: &str = "none";
pub const SUBDIV_SCHEME_CATMULL_CLARK: &str = "catmullClark";
pub const SUBDIV_SCHEME_LOOP: &str = "loop";
pub const SUBDIV_SCHEME_BILINEAR: &str = "bilinear";

// ── GeomSubset attribute names ──────────────────────────────────────────
pub const A_FAMILY_NAME: &str = "familyName";
pub const A_ELEMENT_TYPE: &str = "elementType";
pub const A_INDICES: &str = "indices";

// GeomSubset elementType token values.
pub const ELEMENT_TYPE_FACE: &str = "face";
pub const ELEMENT_TYPE_POINT: &str = "point";
pub const ELEMENT_TYPE_EDGE: &str = "edge";
pub const ELEMENT_TYPE_TETRAHEDRON: &str = "tetrahedron";

// Pixar's canonical material-binding family name on GeomSubsets.
pub const FAMILY_NAME_MATERIAL_BIND: &str = "materialBind";

// ── Primvar metadata field names ────────────────────────────────────────
pub const PRIMVARS_NAMESPACE: &str = "primvars:";
pub const META_INTERPOLATION: &str = "interpolation";
pub const META_ELEMENT_SIZE: &str = "elementSize";

// Primvar interpolation token values.
pub const INTERP_CONSTANT: &str = "constant";
pub const INTERP_UNIFORM: &str = "uniform";
pub const INTERP_VARYING: &str = "varying";
pub const INTERP_VERTEX: &str = "vertex";
pub const INTERP_FACE_VARYING: &str = "faceVarying";

// ── Curves common attribute names ───────────────────────────────────────
pub const A_CURVE_VERTEX_COUNTS: &str = "curveVertexCounts";
pub const A_WIDTHS: &str = "widths";

// BasisCurves attribute names + token values.
pub const A_TYPE: &str = "type";
pub const A_BASIS: &str = "basis";
pub const A_WRAP: &str = "wrap";
pub const CURVE_TYPE_LINEAR: &str = "linear";
pub const CURVE_TYPE_CUBIC: &str = "cubic";
pub const CURVE_BASIS_BEZIER: &str = "bezier";
pub const CURVE_BASIS_BSPLINE: &str = "bspline";
pub const CURVE_BASIS_CATMULL_ROM: &str = "catmullRom";
pub const CURVE_BASIS_HERMITE: &str = "hermite";
pub const CURVE_WRAP_NONPERIODIC: &str = "nonperiodic";
pub const CURVE_WRAP_PERIODIC: &str = "periodic";
pub const CURVE_WRAP_PINNED: &str = "pinned";

// NurbsCurves + NurbsPatch attribute names.
pub const A_ORDER: &str = "order";
pub const A_KNOTS: &str = "knots";
pub const A_RANGES: &str = "ranges";
pub const A_U_VERTEX_COUNT: &str = "uVertexCount";
pub const A_V_VERTEX_COUNT: &str = "vVertexCount";
pub const A_U_ORDER: &str = "uOrder";
pub const A_V_ORDER: &str = "vOrder";
pub const A_U_KNOTS: &str = "uKnots";
pub const A_V_KNOTS: &str = "vKnots";
pub const A_U_RANGE: &str = "uRange";
pub const A_V_RANGE: &str = "vRange";

// HermiteCurves attribute names.
pub const A_TANGENTS: &str = "tangents";

// Points attribute names.
pub const A_IDS: &str = "ids";

// TetMesh attribute names.
pub const A_TET_VERTEX_INDICES: &str = "tetVertexIndices";
pub const A_SURFACE_FACE_VERTEX_INDICES: &str = "surfaceFaceVertexIndices";

// ── PointInstancer attribute / relationship names ───────────────────────
pub const REL_PROTOTYPES: &str = "prototypes";
pub const A_PROTO_INDICES: &str = "protoIndices";
pub const A_POSITIONS: &str = "positions";
pub const A_ORIENTATIONS: &str = "orientations";
pub const A_ORIENTATIONS_F: &str = "orientationsf";
pub const A_SCALES: &str = "scales";
pub const A_ANGULAR_VELOCITIES: &str = "angularVelocities";
pub const A_INVISIBLE_IDS: &str = "invisibleIds";
pub const META_INACTIVE_IDS: &str = "inactiveIds";

// Orientation token values.
pub const ORIENTATION_RIGHT_HANDED: &str = "rightHanded";
pub const ORIENTATION_LEFT_HANDED: &str = "leftHanded";

// ── Common model-hierarchy metadata field (not a UsdGeom attribute, but
//    the geom readers surface it for convenience). ───────────────────────
pub const META_KIND: &str = "kind";
