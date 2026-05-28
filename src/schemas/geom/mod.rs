//! UsdGeom schema reader.
//!
//! Decodes Pixar's `UsdGeom` schema family from a composed
//! [`crate::Stage`]. UsdGeom is the largest schema family in the
//! reference implementation; this module ships its surface in
//! incremental layers:
//!
//! 1. Cross-cutting Imageable / Boundable readers (this commit).
//! 2. Xformable + xformOp evaluator.
//! 3. Intrinsic shapes (Cube, Sphere, Cylinder, Capsule, Cone, Plane, Xform).
//! 4. Camera.
//! 5. Mesh + GeomSubset + PrimvarsAPI.
//! 6. Curves, NurbsPatch, Points, TetMesh.
//! 7. PointInstancer.
//!
//! # Conventions
//!
//! Reader functions return values in the scene's authored units.
//! Matrices are row-major flattened 4×4 (`[f64; 16]`) — see
//! [`crate::math`] for the helpers that compose them.
//!
//! # Inheritance
//!
//! `visibility` and `purpose` are inherited down namespace. The
//! `read_*` helpers report only the value authored directly on the
//! queried prim; use [`compute_visibility`] / [`compute_purpose`] to
//! resolve the effective value walking ancestors.

pub mod tokens;

mod author;
mod camera;
mod curves;
mod instancer;
mod mesh;
mod read;
mod shapes;
mod types;
mod xform;

pub use author::{
    apply_imageable_overrides, define_capsule, define_cone, define_cube, define_cylinder, define_plane, define_scope,
    define_sphere, define_xform, set_extent, set_orient, set_purpose, set_rotate_x, set_rotate_xyz, set_rotate_y,
    set_rotate_z, set_scale, set_transform, set_translate, set_visibility, set_xform_op_order, CapsuleAuthor,
    ConeAuthor, CubeAuthor, CylinderAuthor, ImageableAuthor, PlaneAuthor, SphereAuthor,
};
pub use camera::read_camera;
pub use curves::{
    read_basis_curves, read_hermite_curves, read_nurbs_curves, read_nurbs_patch, read_points, read_tet_mesh,
};
pub use instancer::read_point_instancer;
pub use mesh::{read_mesh, read_primvar_float, read_primvar_vec2f, read_primvar_vec3f, read_subset};
pub use read::{
    compute_purpose, compute_visibility, find_geom_prims, read_extent, read_kind, read_proxy_prim, read_purpose,
    read_visibility,
};
pub use shapes::{read_capsule, read_cone, read_cube, read_cylinder, read_plane, read_sphere};
pub use types::{
    Axis, CurveBasis, CurveType, CurveWrap, ElementType, FaceVaryingLinearInterpolation, GeomPrims,
    InterpolateBoundary, Interpolation, Orientation, PatchForm, Primvar, Projection, Purpose, ReadBasisCurves,
    ReadCamera, ReadCapsule, ReadCone, ReadCube, ReadCylinder, ReadHermiteCurves, ReadMesh, ReadNurbsCurves,
    ReadNurbsPatch, ReadPlane, ReadPointInstancer, ReadPoints, ReadSphere, ReadSubset, ReadTetMesh, StereoRole,
    SubdivisionScheme, TriangleSubdivisionRule, Visibility,
};
pub use xform::{compute_local_to_parent_transform, read_xform_op_order, resets_xform_stack};
