//! Authoring helpers for the [UsdGeom](super) schema family.
//!
//! Mirrors the per-schema reader surface in [`super::read`] /
//! [`super::xform`] / [`super::shapes`] / `mesh` / `curves` /
//! `camera` / `instancer` with the inverse direction — each
//! `define_*` / `apply_*` helper authors a typed prim or sets the
//! schema-defined attributes that the matching reader decodes
//! losslessly.
//!
//! The helpers wrap [`crate::usd::Stage`]'s authoring entry points;
//! they only know which type tokens, attribute names, and token-allowed
//! values Pixar's `usdGeom/schema.usda` requires. Composition, layer
//! routing, and save flow through the same APIs a hand-rolled
//! authoring call would use.

mod camera;
mod common;
mod curves;
mod imageable;
mod mesh;
mod shapes;
mod xform;

pub use camera::{define_camera, CameraAuthor};
pub use curves::{
    define_basis_curves, define_hermite_curves, define_nurbs_curves, define_nurbs_patch, define_point_instancer,
    define_points, define_tet_mesh, BasisCurvesAuthor, HermiteCurvesAuthor, NurbsCurvesAuthor, NurbsPatchAuthor,
    PointInstancerAuthor, PointsAuthor, TetMeshAuthor,
};
pub use imageable::{apply_imageable_overrides, set_extent, set_purpose, set_visibility, ImageableAuthor};
pub use mesh::{define_mesh, define_subset, MeshAuthor, SubsetAuthor};
pub use shapes::{
    define_capsule, define_cone, define_cube, define_cylinder, define_plane, define_scope, define_sphere, define_xform,
    CapsuleAuthor, ConeAuthor, CubeAuthor, CylinderAuthor, PlaneAuthor, SphereAuthor,
};
pub use xform::{
    set_orient, set_rotate_x, set_rotate_xyz, set_rotate_y, set_rotate_z, set_scale, set_transform, set_translate,
    set_xform_op_order,
};
