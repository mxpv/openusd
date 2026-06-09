//! Integration tests for the UsdGeom schema views, exercised against the
//! `usdGeom_scene.usda` fixture: the cross-cutting Imageable / Boundable
//! surface, the `Xformable` transform stack, and every concrete prim view.

use anyhow::Result;
use openusd::gf::{Matrix4d, Vec3f};
use openusd::schemas::geom::{
    self, Axis, BasisCurves, Boundable, Camera, Capsule, Cone, Cube, Curves, Cylinder, ElementType, GeomSubset, Gprim,
    HermiteCurves, Imageable, InterpolateBoundary, Interpolation, Mesh, NurbsCurves, NurbsPatch, PatchForm, Plane,
    PointBased, PointInstancer, Points, Projection, Purpose, Sphere, StereoRole, SubdivisionScheme, TetMesh,
    Visibility, Xform, Xformable,
};
use openusd::sdf;
use openusd::usd::{Attribute, Stage};

const FIXTURE: &str = "fixtures/usdGeom_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

fn xform(stage: &Stage, path: &str) -> Result<Xform> {
    Ok(Xform::get(stage, sdf::path(path)?)?.expect("Xform"))
}

/// The directly-authored `visibility` opinion, defaulting to `Inherited`
/// (mirrors the old `read_visibility` over a typed view).
fn direct_visibility(view: &impl Imageable) -> Result<Visibility> {
    Ok(view
        .visibility_attr()
        .get::<String>()?
        .as_deref()
        .and_then(Visibility::from_token)
        .unwrap_or_default())
}

/// The directly-authored `purpose` opinion, defaulting to `Default`.
fn direct_purpose(view: &impl Imageable) -> Result<Purpose> {
    Ok(view
        .purpose_attr()
        .get::<String>()?
        .as_deref()
        .and_then(Purpose::from_token)
        .unwrap_or_default())
}

/// Length of an authored array attribute, or 0 when unauthored.
fn array_len(attr: &Attribute, kind: impl Fn(sdf::Value) -> usize) -> Result<usize> {
    Ok(attr.get()?.map(kind).unwrap_or(0))
}

fn vec3f_len(v: sdf::Value) -> usize {
    v.try_as_vec_3f_vec().map(|a| a.len()).unwrap_or(0)
}

// ── Imageable: visibility / purpose / proxyPrim ───────────────────

#[test]
fn defaults_when_visibility_unauthored() -> Result<()> {
    let stage = open()?;
    let hero = Mesh::get(&stage, sdf::path("/World/Geometry/Hero")?)?.expect("Mesh");
    assert_eq!(direct_visibility(&hero)?, Visibility::Inherited);
    Ok(())
}

#[test]
fn reads_authored_visibility() -> Result<()> {
    let stage = open()?;
    let ball = Sphere::get(&stage, sdf::path("/World/Geometry/InvisibleBall")?)?.expect("Sphere");
    assert_eq!(direct_visibility(&ball)?, Visibility::Invisible);
    Ok(())
}

#[test]
fn compute_visibility_inherits_invisible_from_ancestor() -> Result<()> {
    let stage = open()?;
    // HiddenChild has no authored visibility, but /World/Hidden is
    // invisible — so the composed visibility should be Invisible.
    let child = Sphere::get(&stage, sdf::path("/World/Hidden/HiddenChild")?)?.expect("Sphere");
    assert_eq!(child.compute_visibility()?, Visibility::Invisible);
    // Hero is not under any invisible ancestor.
    let hero = Mesh::get(&stage, sdf::path("/World/Geometry/Hero")?)?.expect("Mesh");
    assert_eq!(hero.compute_visibility()?, Visibility::Inherited);
    Ok(())
}

#[test]
fn reads_authored_purpose() -> Result<()> {
    let stage = open()?;
    let hero = Mesh::get(&stage, sdf::path("/World/Geometry/Hero")?)?.expect("Mesh");
    assert_eq!(direct_purpose(&hero)?, Purpose::Render);
    let proxy = Mesh::get(&stage, sdf::path("/World/Geometry/HeroProxy")?)?.expect("Mesh");
    assert_eq!(direct_purpose(&proxy)?, Purpose::Proxy);
    let guide = Cube::get(&stage, sdf::path("/World/Geometry/GuideCube")?)?.expect("Cube");
    assert_eq!(direct_purpose(&guide)?, Purpose::Guide);
    Ok(())
}

#[test]
fn default_purpose_is_default() -> Result<()> {
    let stage = open()?;
    let cam = Camera::get(&stage, sdf::path("/World/Cam")?)?.expect("Camera");
    assert_eq!(direct_purpose(&cam)?, Purpose::Default);
    Ok(())
}

#[test]
fn compute_purpose_walks_ancestors() -> Result<()> {
    let stage = open()?;
    // HeroProxy authors its own purpose — no inheritance needed.
    let proxy = Mesh::get(&stage, sdf::path("/World/Geometry/HeroProxy")?)?.expect("Mesh");
    assert_eq!(proxy.compute_purpose()?, Purpose::Proxy);
    // Cam authors nothing → default fallback.
    let cam = Camera::get(&stage, sdf::path("/World/Cam")?)?.expect("Camera");
    assert_eq!(cam.compute_purpose()?, Purpose::Default);
    Ok(())
}

#[test]
fn reads_proxy_prim_rel() -> Result<()> {
    let stage = open()?;
    let hero = Mesh::get(&stage, sdf::path("/World/Geometry/Hero")?)?.expect("Mesh");
    let targets = hero.proxy_prim_rel().targets()?;
    assert_eq!(targets.first().map(|p| p.as_str()), Some("/World/Geometry/HeroProxy"));
    Ok(())
}

// ── Boundable: extent ─────────────────────────────────────────────

#[test]
fn reads_extent_when_authored() -> Result<()> {
    let stage = open()?;
    let hero = Mesh::get(&stage, sdf::path("/World/Geometry/Hero")?)?.expect("Mesh");
    assert_eq!(
        hero.extent_attr().get()?,
        Some(sdf::Value::Vec3fVec(vec![
            openusd::gf::Vec3f {
                x: -1.0,
                y: -1.0,
                z: -1.0
            },
            openusd::gf::Vec3f { x: 1.0, y: 1.0, z: 1.0 },
        ]))
    );
    Ok(())
}

#[test]
fn extent_unauthored_returns_none() -> Result<()> {
    let stage = open()?;
    let cam = Camera::get(&stage, sdf::path("/World/Cam")?)?.expect("Camera");
    // Camera is Xformable but not Boundable, so it has no `extent`; the
    // /World/Cam prim authors none either way.
    assert!(cam.attribute("extent").get::<sdf::Value>()?.is_none());
    Ok(())
}

// ── Xformable / xformOpOrder ──────────────────────────────────────

#[test]
fn xform_op_order_returns_authored_stack() -> Result<()> {
    let stage = open()?;
    let order = xform(&stage, "/World/TRS")?.xform_op_order()?.expect("authored");
    assert_eq!(order, vec!["xformOp:translate", "xformOp:rotateY", "xformOp:scale"]);
    Ok(())
}

#[test]
fn xform_op_order_none_when_unauthored() -> Result<()> {
    let stage = open()?;
    // `/World` is an Xform with no authored stack.
    assert!(xform(&stage, "/World")?.xform_op_order()?.is_none());
    Ok(())
}

#[test]
fn resets_xform_stack_detects_sentinel() -> Result<()> {
    let stage = open()?;
    assert!(xform(&stage, "/World/Detached")?.resets_xform_stack()?);
    assert!(!xform(&stage, "/World/TRS")?.resets_xform_stack()?);
    Ok(())
}

#[test]
fn unauthored_xform_is_identity() -> Result<()> {
    let stage = open()?;
    let m = xform(&stage, "/World")?.local_to_parent_transform(0.0)?;
    assert_eq!(m, Matrix4d::IDENTITY);
    Ok(())
}

#[test]
fn matrix_op_round_trips_to_authored_matrix() -> Result<()> {
    let stage = open()?;
    let m = xform(&stage, "/World/MatrixOp")?.local_to_parent_transform(0.0)?;
    assert_eq!(m.0[12..15], [5.0, 6.0, 7.0]);
    Ok(())
}

#[test]
fn invert_prefix_inverts_the_op() -> Result<()> {
    let stage = open()?;
    // Authored translate (4, 0, 0), then !invert! it → translation row (-4, 0, 0).
    let m = xform(&stage, "/World/Inverted")?.local_to_parent_transform(0.0)?;
    assert_eq!(m.0[12..15], [-4.0, 0.0, 0.0]);
    Ok(())
}

#[test]
fn rotate_xyz_matches_pixar_composition() -> Result<()> {
    // Pixar's `rotateXYZ` in `pxr/usd/usdGeom/xformOp.cpp` composes
    // as `xRot * yRot * zRot` (row-vector matrices, leftmost applies
    // first to v). Test rotateXYZ(0, 90°, 0) on +X: Ry(90°) takes
    // +X to -Z.
    let stage = open()?;
    let m = xform(&stage, "/World/EulerXYZ")?.local_to_parent_transform(0.0)?;
    let p = m.transform_point(Vec3f { x: 1.0, y: 0.0, z: 0.0 });
    assert!(p.x.abs() < 1e-5, "x: {}", p.x);
    assert!(p.y.abs() < 1e-5, "y: {}", p.y);
    assert!((p.z + 1.0).abs() < 1e-5, "z: {} (expected -1)", p.z);
    Ok(())
}

#[test]
fn trs_stack_composes_in_authored_order() -> Result<()> {
    let stage = open()?;
    // Order is translate → rotateY(90°) → scale(2,2,2). In USD's row-
    // vector convention, the first op is most local — applied first
    // to the point. So a vertex at (0, 0, 0) on this prim moves like:
    //   1. translate to (1, 2, 3)
    //   2. rotate by 90° about Y around the origin (not the
    //      translated point): (1, 2, 3) → (3, 2, -1)
    //   3. scale by 2: → (6, 4, -2)
    let m = xform(&stage, "/World/TRS")?.local_to_parent_transform(0.0)?;
    let p = m.transform_point(Vec3f { x: 0.0, y: 0.0, z: 0.0 });
    assert!((p.x - 6.0).abs() < 1e-4, "x: {}", p.x);
    assert!((p.y - 4.0).abs() < 1e-4, "y: {}", p.y);
    assert!((p.z + 2.0).abs() < 1e-4, "z: {}", p.z);
    Ok(())
}

#[test]
fn xform_double_precision() -> Result<()> {
    let stage = open()?;

    let translate = xform(&stage, "/World/DoubleTranslate")?.local_to_parent_transform(0.0)?;
    assert_eq!(translate[12], 16_777_217.0);

    let scale = xform(&stage, "/World/DoubleScale")?.local_to_parent_transform(0.0)?;
    assert_eq!(scale[0], 16_777_217.0);

    let scalar = xform(&stage, "/World/DoubleScalarOps")?.local_to_parent_transform(0.0)?;
    assert_eq!(scalar[12], 16_777_217.0);
    assert_eq!(scalar[5], 16_777_217.0);

    let orient = xform(&stage, "/World/DoubleOrient")?.local_to_parent_transform(0.0)?;
    assert!(orient[0].abs() < 1e-12, "x axis scale term: {}", orient[0]);

    Ok(())
}

// ── Intrinsic shapes ──────────────────────────────────────────────

#[test]
fn cube_authored_size() -> Result<()> {
    let stage = open()?;
    let cube = Cube::get(&stage, sdf::path("/World/Shapes/AuthoredCube")?)?.expect("Cube");
    assert_eq!(cube.size_attr().get()?, Some(sdf::Value::Double(3.0)));
    Ok(())
}

#[test]
fn unauthored_cube_size_is_none() -> Result<()> {
    // No schema registry yet, so an unauthored attribute reads back as `None`
    // rather than the spec fallback.
    let stage = open()?;
    let cube = Cube::get(&stage, sdf::path("/World/Shapes/DefaultCube")?)?.expect("Cube");
    assert_eq!(cube.size_attr().get::<sdf::Value>()?, None);
    Ok(())
}

#[test]
fn cube_get_rejects_non_cube() -> Result<()> {
    let stage = open()?;
    assert!(Cube::get(&stage, sdf::path("/World/Shapes/Ball")?)?.is_none());
    Ok(())
}

#[test]
fn sphere_authored_radius() -> Result<()> {
    let stage = open()?;
    let s = Sphere::get(&stage, sdf::path("/World/Shapes/Ball")?)?.expect("Sphere");
    assert_eq!(s.radius_attr().get()?, Some(sdf::Value::Double(4.5)));
    Ok(())
}

#[test]
fn cylinder_with_y_axis() -> Result<()> {
    let stage = open()?;
    let c = Cylinder::get(&stage, sdf::path("/World/Shapes/Pipe")?)?.expect("Cylinder");
    assert_eq!(c.radius_attr().get()?, Some(sdf::Value::Double(0.25)));
    assert_eq!(c.height_attr().get()?, Some(sdf::Value::Double(2.0)));
    assert_eq!(c.axis_attr().get()?, Some(sdf::Value::token("Y")));
    Ok(())
}

#[test]
fn capsule_with_x_axis() -> Result<()> {
    let stage = open()?;
    let c = Capsule::get(&stage, sdf::path("/World/Shapes/Pill")?)?.expect("Capsule");
    assert_eq!(c.radius_attr().get()?, Some(sdf::Value::Double(0.1)));
    assert_eq!(c.height_attr().get()?, Some(sdf::Value::Double(0.5)));
    assert_eq!(c.axis_attr().get()?, Some(sdf::Value::token("X")));
    Ok(())
}

#[test]
fn cone_unauthored_axis_is_none() -> Result<()> {
    let stage = open()?;
    let c = Cone::get(&stage, sdf::path("/World/Shapes/Pyramid")?)?.expect("Cone");
    assert_eq!(c.radius_attr().get()?, Some(sdf::Value::Double(1.5)));
    assert_eq!(c.height_attr().get()?, Some(sdf::Value::Double(4.0)));
    assert_eq!(c.axis_attr().get::<sdf::Value>()?, None);
    Ok(())
}

#[test]
fn plane_dimensions_and_axis() -> Result<()> {
    let stage = open()?;
    let p = Plane::get(&stage, sdf::path("/World/Shapes/Ground")?)?.expect("Plane");
    assert_eq!(p.width_attr().get()?, Some(sdf::Value::Double(10.0)));
    assert_eq!(p.length_attr().get()?, Some(sdf::Value::Double(8.0)));
    assert_eq!(p.axis_attr().get()?, Some(sdf::Value::token("Y")));
    assert_eq!(p.double_sided_attr().get::<sdf::Value>()?, None);
    Ok(())
}

#[test]
fn axis_token_round_trip() {
    assert_eq!(Axis::X.as_token(), "X");
    assert_eq!(Axis::Y.as_token(), "Y");
    assert_eq!(Axis::Z.as_token(), "Z");
    assert_eq!(Axis::from_token("X"), Some(Axis::X));
    assert_eq!(Axis::from_token("bogus"), None);
    // The default is Z per Pixar spec.
    assert_eq!(Axis::default(), Axis::Z);
}

// ── Camera ────────────────────────────────────────────────────────

#[test]
fn camera_authored_attrs() -> Result<()> {
    let stage = open()?;
    let c = Camera::get(&stage, sdf::path("/World/AuthoredCam")?)?.expect("Camera");
    assert_eq!(c.focal_length_attr().get()?, Some(sdf::Value::Float(35.0)));
    assert_eq!(c.f_stop_attr().get()?, Some(sdf::Value::Float(2.8)));
    assert_eq!(c.projection_attr().get()?, Some(sdf::Value::token("perspective")));
    assert_eq!(c.stereo_role_attr().get()?, Some(sdf::Value::token("left")));
    Ok(())
}

#[test]
fn camera_unauthored_attrs_are_none() -> Result<()> {
    let stage = open()?;
    // /World/Cam authors only focalLength; the rest read back as `None`
    // (no schema registry to supply fallbacks).
    let c = Camera::get(&stage, sdf::path("/World/Cam")?)?.expect("Camera");
    assert_eq!(c.focal_length_attr().get()?, Some(sdf::Value::Float(50.0)));
    assert_eq!(c.horizontal_aperture_attr().get::<sdf::Value>()?, None);
    assert_eq!(c.projection_attr().get::<sdf::Value>()?, None);
    Ok(())
}

#[test]
fn orthographic_projection_token() -> Result<()> {
    let stage = open()?;
    let c = Camera::get(&stage, sdf::path("/World/OrthoCam")?)?.expect("Camera");
    assert_eq!(c.projection_attr().get()?, Some(sdf::Value::token("orthographic")));
    // `Projection` decodes the authored token.
    let tok = c.projection_attr().get::<String>()?;
    assert_eq!(
        tok.as_deref().and_then(Projection::from_token),
        Some(Projection::Orthographic)
    );
    Ok(())
}

#[test]
fn camera_projection_and_stereo_token_round_trip() {
    assert_eq!(Projection::Perspective.as_token(), "perspective");
    assert_eq!(Projection::from_token("orthographic"), Some(Projection::Orthographic));
    assert_eq!(Projection::from_token("bogus"), None);
    assert_eq!(StereoRole::Right.as_token(), "right");
    assert_eq!(StereoRole::from_token("mono"), Some(StereoRole::Mono));
}

#[test]
fn camera_get_returns_none_for_non_camera() -> Result<()> {
    let stage = open()?;
    assert!(Camera::get(&stage, sdf::path("/World/Shapes/Ball")?)?.is_none());
    Ok(())
}

// ── Mesh + GeomSubset ─────────────────────────────────────────────

#[test]
fn mesh_returns_topology() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    assert_eq!(array_len(&m.points_attr(), vec3f_len)?, 4);
    assert_eq!(m.face_vertex_counts_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
    assert_eq!(
        m.face_vertex_indices_attr().get()?,
        Some(sdf::Value::IntVec(vec![0, 1, 2, 3]))
    );
    Ok(())
}

#[test]
fn mesh_gprim_attrs_round_trip() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    assert_eq!(m.double_sided_attr().get()?, Some(sdf::Value::Bool(true)));
    assert_eq!(m.orientation_attr().get::<String>()?.as_deref(), Some("leftHanded"));
    assert_eq!(
        m.extent_attr().get()?,
        Some(sdf::Value::Vec3fVec(vec![
            openusd::gf::Vec3f { x: 0.0, y: 0.0, z: 0.0 },
            openusd::gf::Vec3f { x: 1.0, y: 1.0, z: 0.0 },
        ]))
    );
    Ok(())
}

#[test]
fn mesh_subdivision_attrs() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    assert_eq!(m.subdivision_scheme_attr().get::<String>()?.as_deref(), Some("none"));
    assert_eq!(
        m.interpolate_boundary_attr().get::<String>()?.as_deref(),
        Some("edgeAndCorner")
    );
    assert_eq!(m.corner_indices_attr().get()?, Some(sdf::Value::IntVec(vec![0, 2])));
    assert_eq!(
        m.corner_sharpnesses_attr().get()?,
        Some(sdf::Value::FloatVec(vec![10.0, 5.0]))
    );
    assert_eq!(
        m.crease_indices_attr().get()?,
        Some(sdf::Value::IntVec(vec![0, 1, 1, 2]))
    );
    assert_eq!(m.crease_lengths_attr().get()?, Some(sdf::Value::IntVec(vec![2, 2])));
    assert_eq!(
        m.crease_sharpnesses_attr().get()?,
        Some(sdf::Value::FloatVec(vec![3.0, 4.0]))
    );
    Ok(())
}

#[test]
fn mesh_normals_carry_interpolation() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    assert_eq!(array_len(&m.normals_attr(), vec3f_len)?, 4);
    assert_eq!(
        m.normals_attr().get_metadata::<String>("interpolation")?.as_deref(),
        Some("vertex")
    );
    Ok(())
}

#[test]
fn mesh_uvs_face_varying() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    // `primvars:st` has no dedicated accessor — it is reached through the
    // generic primvar namespace (UsdGeomPrimvarsAPI is not yet modeled).
    let st = m.attribute("primvars:st");
    assert_eq!(
        st.get::<sdf::Value>()?
            .and_then(|v| v.try_as_vec_2f_vec())
            .map(|v| v.len()),
        Some(4)
    );
    assert_eq!(
        st.get_metadata::<String>("interpolation")?.as_deref(),
        Some("faceVarying")
    );
    Ok(())
}

#[test]
fn mesh_display_color() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    assert_eq!(
        m.display_color_attr().get()?,
        Some(sdf::Value::Vec3fVec(vec![openusd::gf::Vec3f {
            x: 1.0,
            y: 0.0,
            z: 0.0
        }]))
    );
    assert_eq!(
        m.display_color_attr()
            .get_metadata::<String>("interpolation")?
            .as_deref(),
        Some("constant")
    );
    Ok(())
}

#[test]
fn mesh_velocities_pass_through() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    assert_eq!(array_len(&m.velocities_attr(), vec3f_len)?, 4);
    assert!(m.accelerations_attr().get::<sdf::Value>()?.is_none());
    Ok(())
}

#[test]
fn geom_subset_round_trip() -> Result<()> {
    let stage = open()?;
    let s = GeomSubset::get(&stage, sdf::path("/World/FancyMesh/Front")?)?.expect("GeomSubset");
    assert_eq!(s.element_type_attr().get::<String>()?.as_deref(), Some("face"));
    assert_eq!(s.family_name_attr().get::<String>()?.as_deref(), Some("materialBind"));
    assert_eq!(s.indices_attr().get()?, Some(sdf::Value::IntVec(vec![0])));
    Ok(())
}

#[test]
fn mesh_subdivision_scheme_token_round_trip() {
    assert_eq!(SubdivisionScheme::default(), SubdivisionScheme::CatmullClark);
    assert!(SubdivisionScheme::CatmullClark.is_subdivision());
    assert!(!SubdivisionScheme::None.is_subdivision());
    assert_eq!(SubdivisionScheme::from_token("loop"), Some(SubdivisionScheme::Loop));
    assert_eq!(SubdivisionScheme::from_token("bogus"), None);
    assert_eq!(InterpolateBoundary::default(), InterpolateBoundary::EdgeAndCorner);
}

#[test]
fn primvar_interpolation_token_round_trip() {
    for &(tok, mode) in &[
        ("constant", Interpolation::Constant),
        ("uniform", Interpolation::Uniform),
        ("varying", Interpolation::Varying),
        ("vertex", Interpolation::Vertex),
        ("faceVarying", Interpolation::FaceVarying),
    ] {
        assert_eq!(Interpolation::from_token(tok), Some(mode));
        assert_eq!(mode.as_token(), tok);
    }
}

#[test]
fn element_type_token_round_trip() {
    assert_eq!(ElementType::default(), ElementType::Face);
    assert_eq!(ElementType::from_token("point"), Some(ElementType::Point));
    assert_eq!(ElementType::Tetrahedron.as_token(), "tetrahedron");
}

// ── Curves / Patch / Points / TetMesh ─────────────────────────────

#[test]
fn basis_curves_topology_and_type() -> Result<()> {
    let stage = open()?;
    let c = BasisCurves::get(&stage, sdf::path("/World/Curves/Linear")?)?.expect("BasisCurves");
    assert_eq!(array_len(&c.points_attr(), vec3f_len)?, 4);
    assert_eq!(c.curve_vertex_counts_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
    assert_eq!(c.type_attr().get::<String>()?.as_deref(), Some("linear"));
    assert_eq!(c.wrap_attr().get::<String>()?.as_deref(), Some("nonperiodic"));
    assert_eq!(
        c.widths_attr()
            .get::<sdf::Value>()?
            .and_then(|v| v.try_as_float_vec())
            .map(|v| v.len()),
        Some(4)
    );
    // `basis` is unauthored — no registry fallback, so it reads back `None`.
    assert_eq!(c.basis_attr().get::<sdf::Value>()?, None);
    Ok(())
}

#[test]
fn nurbs_curves_order_and_weights() -> Result<()> {
    let stage = open()?;
    let c = NurbsCurves::get(&stage, sdf::path("/World/Curves/Smooth")?)?.expect("NurbsCurves");
    assert_eq!(c.order_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
    assert_eq!(
        c.knots_attr()
            .get::<sdf::Value>()?
            .and_then(|v| v.try_as_double_vec())
            .map(|v| v.len()),
        Some(8)
    );
    assert_eq!(
        c.point_weights_attr()
            .get::<sdf::Value>()?
            .and_then(|v| v.try_as_double_vec())
            .map(|v| v.len()),
        Some(4)
    );
    Ok(())
}

#[test]
fn nurbs_patch_grid() -> Result<()> {
    let stage = open()?;
    let p = NurbsPatch::get(&stage, sdf::path("/World/Curves/Sheet")?)?.expect("NurbsPatch");
    assert_eq!(p.u_vertex_count_attr().get()?, Some(sdf::Value::Int(4)));
    assert_eq!(p.v_vertex_count_attr().get()?, Some(sdf::Value::Int(4)));
    assert_eq!(array_len(&p.points_attr(), vec3f_len)?, 16);
    assert_eq!(p.u_order_attr().get()?, Some(sdf::Value::Int(4)));
    // uForm authored; vForm unauthored → reads back `None` (no fallback).
    assert_eq!(p.u_form_attr().get::<String>()?.as_deref(), Some("periodic"));
    assert_eq!(p.v_form_attr().get::<sdf::Value>()?, None);
    Ok(())
}

#[test]
fn patch_form_token_round_trip() {
    assert_eq!(PatchForm::default(), PatchForm::Open);
    assert_eq!(PatchForm::Open.as_token(), "open");
    assert_eq!(PatchForm::Closed.as_token(), "closed");
    assert_eq!(PatchForm::Periodic.as_token(), "periodic");
    assert_eq!(PatchForm::from_token("closed"), Some(PatchForm::Closed));
    assert_eq!(PatchForm::from_token("bogus"), None);
}

#[test]
fn hermite_curves_carry_tangents() -> Result<()> {
    let stage = open()?;
    let c = HermiteCurves::get(&stage, sdf::path("/World/Curves/Hairs")?)?.expect("HermiteCurves");
    assert_eq!(array_len(&c.points_attr(), vec3f_len)?, 4);
    assert_eq!(array_len(&c.tangents_attr(), vec3f_len)?, 4);
    assert_eq!(
        c.curve_vertex_counts_attr().get()?,
        Some(sdf::Value::IntVec(vec![2, 2]))
    );
    Ok(())
}

#[test]
fn points_with_ids_and_widths() -> Result<()> {
    let stage = open()?;
    let p = Points::get(&stage, sdf::path("/World/Curves/Cloud")?)?.expect("Points");
    assert_eq!(array_len(&p.points_attr(), vec3f_len)?, 3);
    assert_eq!(
        p.widths_attr().get()?,
        Some(sdf::Value::FloatVec(vec![0.05, 0.05, 0.05]))
    );
    assert_eq!(p.ids_attr().get()?, Some(sdf::Value::Int64Vec(vec![10, 20, 30])));
    Ok(())
}

#[test]
fn tet_mesh_indices() -> Result<()> {
    let stage = open()?;
    let t = TetMesh::get(&stage, sdf::path("/World/Curves/Soft")?)?.expect("TetMesh");
    assert_eq!(array_len(&t.points_attr(), vec3f_len)?, 5);
    // The fixture authors the flat `int[]` form; eight indices = two tets.
    assert_eq!(
        t.tet_vertex_indices_attr()
            .get::<sdf::Value>()?
            .and_then(|v| v.try_as_int_vec())
            .map(|v| v.len()),
        Some(8)
    );
    assert!(t.surface_face_vertex_indices_attr().get::<sdf::Value>()?.is_none());
    Ok(())
}

#[test]
fn curve_type_basis_wrap_token_round_trip() {
    use geom::{CurveBasis, CurveType, CurveWrap};
    assert_eq!(CurveType::default(), CurveType::Cubic);
    assert_eq!(CurveType::from_token("linear"), Some(CurveType::Linear));
    assert_eq!(CurveBasis::default(), CurveBasis::Bezier);
    assert_eq!(CurveBasis::from_token("catmullRom"), Some(CurveBasis::CatmullRom));
    assert_eq!(CurveWrap::default(), CurveWrap::Nonperiodic);
    assert_eq!(CurveWrap::from_token("pinned"), Some(CurveWrap::Pinned));
}

// ── PointInstancer ────────────────────────────────────────────────

#[test]
fn point_instancer_prototypes_and_arrays() -> Result<()> {
    let stage = open()?;
    let pi = PointInstancer::get(&stage, sdf::path("/World/InstancerScope/Stars")?)?.expect("PointInstancer");
    assert_eq!(
        pi.prototypes_rel().targets()?,
        vec![sdf::path("/World/InstancerScope/Proto")?]
    );
    assert_eq!(
        pi.proto_indices_attr().get()?,
        Some(sdf::Value::IntVec(vec![0, 0, 0, 0]))
    );
    assert_eq!(array_len(&pi.positions_attr(), vec3f_len)?, 4);
    let scales = pi
        .scales_attr()
        .get::<sdf::Value>()?
        .and_then(|v| v.try_as_vec_3f_vec())
        .expect("scales");
    assert_eq!(scales.len(), 4);
    assert_eq!(scales[1], openusd::gf::Vec3f { x: 2.0, y: 2.0, z: 2.0 });
    assert_eq!(
        pi.ids_attr().get()?,
        Some(sdf::Value::Int64Vec(vec![100, 200, 300, 400]))
    );
    assert_eq!(pi.invisible_ids_attr().get()?, Some(sdf::Value::Int64Vec(vec![300])));
    assert_eq!(array_len(&pi.velocities_attr(), vec3f_len)?, 4);
    // Unauthored attributes read back `None`.
    assert!(pi.orientations_attr().get::<sdf::Value>()?.is_none());
    assert!(pi.angular_velocities_attr().get::<sdf::Value>()?.is_none());
    Ok(())
}

#[test]
fn point_instancer_get_returns_none_for_non_instancer() -> Result<()> {
    let stage = open()?;
    assert!(PointInstancer::get(&stage, sdf::path("/World/Cam")?)?.is_none());
    Ok(())
}

#[test]
fn imageable_token_round_trip() {
    assert_eq!(Visibility::Inherited.as_token(), "inherited");
    assert_eq!(Visibility::Invisible.as_token(), "invisible");
    assert_eq!(Visibility::from_token("invisible"), Some(Visibility::Invisible));
    assert_eq!(Visibility::from_token("bogus"), None);

    assert_eq!(Purpose::Default.as_token(), "default");
    assert_eq!(Purpose::Render.as_token(), "render");
    assert_eq!(Purpose::from_token("guide"), Some(Purpose::Guide));
    assert_eq!(Purpose::from_token("bogus"), None);

    assert_eq!(geom::Orientation::RightHanded.as_token(), "rightHanded");
    assert_eq!(
        geom::Orientation::from_token("leftHanded"),
        Some(geom::Orientation::LeftHanded)
    );
}
