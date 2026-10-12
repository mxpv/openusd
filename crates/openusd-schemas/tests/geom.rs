//! Integration tests for the UsdGeom schema views, exercised against the
//! `usdGeom_scene.usda` fixture: the cross-cutting Imageable / Boundable
//! surface, the `Xformable` transform stack, and every concrete prim view.

use openusd::Result;
use openusd::gf::{Mat4d, Vec2f, Vec3d, Vec3f};
use openusd::sdf;
use openusd::tf::Token;
use openusd::usd::{Attribute, SchemaBase, Stage, TimeCode};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::{
    self, Axis, BasisCurves, BasisCurvesSchema, BoundableSchema, Camera, CameraSchema, Capsule, CapsuleSchema, Cone,
    ConeSchema, Cube, CubeSchema, CurvesSchema, Cylinder, CylinderSchema, ElementType, Gprim, GprimSchema,
    HermiteCurves, HermiteCurvesSchema, Imageable, ImageableExt, ImageableSchema, InterpolateBoundary, Interpolation,
    Mesh, MeshSchema, NurbsCurves, NurbsCurvesSchema, NurbsPatch, NurbsPatchSchema, PatchForm, Plane, PlaneSchema,
    PointBasedSchema, PointInstancer, PointInstancerSchema, Points, PointsSchema, PrimvarsAPI, Projection, Purpose,
    Scope, Sphere, SphereSchema, StereoRole, SubdivisionScheme, Subset, SubsetSchema, TetMesh, TetMeshSchema,
    Visibility, Xform, XformableExt, XformableSchema,
};

const FIXTURE: &str = "fixtures/usdGeom_scene.usda";

fn open() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)
}

fn xform(stage: &Stage, path: &str) -> Result<Xform> {
    Ok(Xform::get(stage, sdf::path(path)?)?.expect("Xform"))
}

/// The directly-authored `visibility` opinion, defaulting to `Inherited`
/// (mirrors the old `read_visibility` over a typed view).
fn direct_visibility(view: &impl ImageableSchema) -> Result<Visibility> {
    Ok(view
        .visibility_attr()
        .get::<Token>()?
        .as_deref()
        .and_then(Visibility::from_token)
        .unwrap_or_default())
}

/// The directly-authored `purpose` opinion, defaulting to `Default`.
fn direct_purpose(view: &impl ImageableSchema) -> Result<Purpose> {
    Ok(view
        .purpose_attr()
        .get::<Token>()?
        .as_deref()
        .and_then(Purpose::from_token)
        .unwrap_or_default())
}

/// Length of an authored array attribute, or 0 when unauthored.
fn array_len(attr: &Attribute, kind: impl Fn(sdf::Value) -> usize) -> Result<usize> {
    Ok(attr.get()?.map_or(0, kind))
}

fn vec3f_len(v: sdf::Value) -> usize {
    v.try_as_vec_3f_vec().map_or(0, |a| a.len())
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
    assert_eq!(child.compute_visibility(None)?, Visibility::Invisible);
    // Hero is not under any invisible ancestor.
    let hero = Mesh::get(&stage, sdf::path("/World/Geometry/Hero")?)?.expect("Mesh");
    assert_eq!(hero.compute_visibility(None)?, Visibility::Inherited);
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

// Abstract views: the class is no prim type, so the view reads a prim of
// whatever type under it.

#[test]
fn gprim_over_any_type() -> Result<()> {
    let stage = open()?;
    // Whatever type the prim carries, the view reads what every Gprim
    // shares — and, through the chain behind it, what every Imageable does.
    let mesh = Gprim::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Gprim");
    assert_eq!(mesh.orientation_attr().get::<Token>()?.as_deref(), Some("leftHanded"));
    let ball = Gprim::get(&stage, sdf::path("/World/Geometry/InvisibleBall")?)?.expect("Gprim");
    assert_eq!(direct_visibility(&ball)?, Visibility::Invisible);
    Ok(())
}

#[test]
fn abstract_get_gated() -> Result<()> {
    let stage = open()?;
    let cam = sdf::path("/World/Cam")?;
    // A Camera is an Imageable, and nothing under Gprim.
    assert!(Imageable::get(&stage, cam.clone())?.is_some());
    assert!(Gprim::get(&stage, cam)?.is_none());
    Ok(())
}

#[test]
fn from_prim_gated() -> Result<()> {
    let stage = open()?;
    // What a traversal has in hand is the prim, not its path.
    let prim = stage.prim(sdf::path("/World/FancyMesh")?)?;

    assert!(Mesh::from_prim(prim.clone())?.is_some());
    assert!(Camera::from_prim(prim)?.is_none());
    Ok(())
}

#[test]
fn abstract_view_takes_ext() -> Result<()> {
    let stage = open()?;
    let child = Imageable::get(&stage, sdf::path("/World/Hidden/HiddenChild")?)?.expect("Imageable");
    assert_eq!(child.compute_visibility(None)?, Visibility::Invisible);
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
fn xform_op_order_empty_when_unauthored() -> Result<()> {
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
fn unauthored_xform_is_identity() -> Result<(), SchemaError> {
    let stage = open()?;
    let m = xform(&stage, "/World")?.local_transform(None)?;
    assert_eq!(m, Mat4d::IDENTITY);
    Ok(())
}

#[test]
fn matrix_op_round_trips_to_authored_matrix() -> Result<(), SchemaError> {
    let stage = open()?;
    let m = xform(&stage, "/World/MatrixOp")?.local_transform(None)?;
    assert_eq!(m.0[12..15], [5.0, 6.0, 7.0]);
    Ok(())
}

#[test]
fn invert_prefix_inverts_the_op() -> Result<(), SchemaError> {
    let stage = open()?;
    // Authored translate (4, 0, 0), then !invert! it → translation row (-4, 0, 0).
    let m = xform(&stage, "/World/Inverted")?.local_transform(None)?;
    assert_eq!(m.0[12..15], [-4.0, 0.0, 0.0]);
    Ok(())
}

#[test]
fn rotate_xyz_matches_pixar_composition() -> Result<(), SchemaError> {
    // Pixar's `rotateXYZ` in `pxr/usd/usdGeom/xformOp.cpp` composes
    // as `xRot * yRot * zRot` (row-vector matrices, leftmost applies
    // first to v). Test rotateXYZ(0, 90°, 0) on +X: Ry(90°) takes
    // +X to -Z.
    let stage = open()?;
    let m = xform(&stage, "/World/EulerXYZ")?.local_transform(None)?;
    let p = m.transform_affine(Vec3d { x: 1.0, y: 0.0, z: 0.0 });
    assert!(p.x.abs() < 1e-5, "x: {}", p.x);
    assert!(p.y.abs() < 1e-5, "y: {}", p.y);
    assert!((p.z + 1.0).abs() < 1e-5, "z: {} (expected -1)", p.z);
    Ok(())
}

#[test]
fn trs_stack_composes_in_authored_order() -> Result<(), SchemaError> {
    let stage = open()?;
    // Order is translate → rotateY(90°) → scale(2,2,2). The *last*
    // op in xformOpOrder is most local — applied first to the point
    // — and the first op applies last. So a vertex at (1, 0, 0) on
    // this prim moves like:
    //   1. scale by 2: (1, 0, 0) → (2, 0, 0)
    //   2. rotate by 90° about Y: (2, 0, 0) → (0, 0, -2)
    //   3. translate by (1, 2, 3): (0, 0, -2) → (1, 2, 1)
    let m = xform(&stage, "/World/TRS")?.local_transform(None)?;
    let p = m.transform_affine(Vec3d { x: 1.0, y: 0.0, z: 0.0 });
    assert!((p.x - 1.0).abs() < 1e-4, "x: {}", p.x);
    assert!((p.y - 2.0).abs() < 1e-4, "y: {}", p.y);
    assert!((p.z - 1.0).abs() < 1e-4, "z: {}", p.z);
    Ok(())
}

#[test]
fn xform_double_precision() -> Result<(), SchemaError> {
    let stage = open()?;

    let translate = xform(&stage, "/World/DoubleTranslate")?.local_transform(None)?;
    assert_eq!(translate[12], 16_777_217.0);

    let scale = xform(&stage, "/World/DoubleScale")?.local_transform(None)?;
    assert_eq!(scale[0], 16_777_217.0);

    let scalar = xform(&stage, "/World/DoubleScalarOps")?.local_transform(None)?;
    assert_eq!(scalar[12], 16_777_217.0);
    assert_eq!(scalar[5], 16_777_217.0);

    let orient = xform(&stage, "/World/DoubleOrient")?.local_transform(None)?;
    assert!(orient[0].abs() < 1e-12, "x axis scale term: {}", orient[0]);

    Ok(())
}

// Metadata fields

/// The fields `usdGeom` registers read and write through the traits generated
/// for them, typed as they are declared; a stage's own falls back to the
/// declared default where no layer authors it.
#[test]
fn metadata_traits() -> Result<()> {
    use openusd_schemas::geom::{AttributeMetadata, StageMetadata};

    let stage = Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")?;
    assert_eq!(stage.meters_per_unit()?, Some(0.01));
    assert_eq!(stage.up_axis()?, Some(Token::new("Y")));

    let mesh = Mesh::define(&stage, "/Mesh")?;
    let normals = mesh.create_normals_attr()?;
    assert_eq!(
        normals.interpolation()?,
        None,
        "a property falls back to its definition only"
    );
    let normals = normals
        .set_interpolation(Token::new("faceVarying"))?
        .set_element_size(3)?;
    assert_eq!(normals.interpolation()?, Some(Token::new("faceVarying")));
    assert_eq!(normals.element_size()?, Some(3));
    Ok(())
}

// XformCache

/// The `testUsdGeomXformCache` scene: `/RootPrim` (Xform) over a `Scope`,
/// over `Foo`, `Foo/Bar` (which resets the stack) and `Foo/Bar/Baz`, plus
/// `Scope/Bar`. Every Xform carries one `transform` op of `step` by default,
/// and its square and cube at `1 + shift` and `2 + shift`.
fn xform_cache_stage(shift: f64) -> Result<Stage, SchemaError> {
    let stage = Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")?;
    Scope::define(&stage, "/RootPrim/Scope")?;
    let step = xform_step();
    for path in [
        "/RootPrim",
        "/RootPrim/Scope/Foo",
        "/RootPrim/Scope/Foo/Bar",
        "/RootPrim/Scope/Foo/Bar/Baz",
        "/RootPrim/Scope/Bar",
    ] {
        Xform::define(&stage, path)?.set_transform(step)?;
        stage
            .attribute(format!("{path}.xformOp:transform"))?
            .set_at(step * step, TimeCode::new(1.0 + shift))?
            .set_at(step * step * step, TimeCode::new(2.0 + shift))?;
    }
    xform(&stage, "/RootPrim/Scope/Foo/Bar")?.set_xform_op_order(["!resetXformStack!", "xformOp:transform"])?;
    Ok(stage)
}

fn xform_step() -> Mat4d {
    Mat4d::translation([10.0, 20.0, 30.0])
}

/// Checks every query of the C++ test against `stage`, whose transforms are
/// `x` at the cache's time.
fn verify_xform_cache(stage: &Stage, cache: &mut geom::XformCache, x: Mat4d) -> Result<(), SchemaError> {
    let prim = |path: &str| stage.prim(path);
    let (root, scope_foo, bar_under_foo, deepest, scope_bar) = (
        prim("/RootPrim")?,
        prim("/RootPrim/Scope/Foo")?,
        prim("/RootPrim/Scope/Foo/Bar")?,
        prim("/RootPrim/Scope/Foo/Bar/Baz")?,
        prim("/RootPrim/Scope/Bar")?,
    );
    let pseudo_root = prim("/")?;

    // The pseudo-root has no transform.
    assert_eq!(cache.local_to_world_transform(&pseudo_root)?, Mat4d::IDENTITY);
    assert!(!cache.transform_might_be_time_varying(&pseudo_root)?);
    assert!(!cache.resets_xform_stack(&pseudo_root)?);

    // The Scope passes `/RootPrim` through; `Foo/Bar` starts over.
    for (p, world, parent, resets) in [
        (&root, x, Mat4d::IDENTITY, false),
        (&scope_foo, x * x, x, false),
        (&bar_under_foo, x, x * x, true),
        (&deepest, x * x, x, false),
        (&scope_bar, x * x, x, false),
    ] {
        assert_eq!(cache.local_to_world_transform(p)?, world, "{}", p.path());
        assert_eq!(cache.parent_to_world_transform(p)?, parent, "{}", p.path());
        assert!(cache.transform_might_be_time_varying(p)?, "{}", p.path());
        assert_eq!(cache.resets_xform_stack(p)?, resets, "{}", p.path());
    }
    assert_eq!(cache.parent_to_world_transform(&pseudo_root)?, Mat4d::IDENTITY);

    assert_eq!(cache.relative_transform(&root, &pseudo_root)?, (x, false));
    assert_eq!(cache.relative_transform(&scope_foo, &root)?, (x, false));
    assert_eq!(cache.relative_transform(&bar_under_foo, &root)?, (x, true));
    assert_eq!(cache.relative_transform(&deepest, &root)?, (x * x, true));
    assert_eq!(cache.relative_transform(&scope_bar, &root)?, (x, false));
    Ok(())
}

/// A port of C++ `testUsdGeomXformCache`: one cache across times, after a
/// clear, and across two stages with the same paths.
#[test]
fn xform_cache_parity() -> Result<(), SchemaError> {
    let stage = xform_cache_stage(0.0)?;
    let step = xform_step();

    let mut cache = geom::XformCache::default();
    verify_xform_cache(&stage, &mut cache, step)?;

    cache.set_time(TimeCode::new(1.0));
    verify_xform_cache(&stage, &mut cache, step * step)?;

    let mut cache = geom::XformCache::new(TimeCode::new(2.0));
    verify_xform_cache(&stage, &mut cache, step * step * step)?;

    cache.clear();
    verify_xform_cache(&stage, &mut cache, step * step * step)?;

    cache.set_time(None);
    verify_xform_cache(&stage, &mut cache, step)?;

    // The same paths on a stage whose samples sit one frame later answer
    // for that stage.
    cache.set_time(TimeCode::new(2.0));
    verify_xform_cache(&stage, &mut cache, step * step * step)?;
    let shifted = xform_cache_stage(1.0)?;
    verify_xform_cache(&shifted, &mut cache, step * step)?;
    verify_xform_cache(&stage, &mut cache, step * step * step)?;
    Ok(())
}

/// The Imageable conveniences answer as a cache does.
#[test]
fn imageable_world_transform() -> Result<(), SchemaError> {
    let stage = xform_cache_stage(0.0)?;
    let step = xform_step();
    let baz = xform(&stage, "/RootPrim/Scope/Foo/Bar/Baz")?;
    assert_eq!(baz.local_to_world_transform(None)?, step * step);
    assert_eq!(baz.parent_to_world_transform(TimeCode::new(1.0))?, step * step);
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
fn unauthored_cube_size_falls_back() -> Result<()> {
    // An unauthored attribute reads back the fallback the schema declares,
    // which is what the registry resolves it through.
    let stage = open()?;
    let cube = Cube::get(&stage, sdf::path("/World/Shapes/DefaultCube")?)?.expect("Cube");
    assert_eq!(cube.size_attr().get()?, Some(sdf::Value::Double(2.0)));
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
fn cone_unauthored_axis_falls_back() -> Result<()> {
    let stage = open()?;
    let c = Cone::get(&stage, sdf::path("/World/Shapes/Pyramid")?)?.expect("Cone");
    assert_eq!(c.radius_attr().get()?, Some(sdf::Value::Double(1.5)));
    assert_eq!(c.height_attr().get()?, Some(sdf::Value::Double(4.0)));
    assert_eq!(c.axis_attr().get()?, Some(sdf::Value::token("Z")));
    Ok(())
}

#[test]
fn plane_dimensions_and_axis() -> Result<()> {
    let stage = open()?;
    let p = Plane::get(&stage, sdf::path("/World/Shapes/Ground")?)?.expect("Plane");
    assert_eq!(p.width_attr().get()?, Some(sdf::Value::Double(10.0)));
    assert_eq!(p.length_attr().get()?, Some(sdf::Value::Double(8.0)));
    assert_eq!(p.axis_attr().get()?, Some(sdf::Value::token("Y")));
    assert_eq!(p.double_sided_attr().get()?, Some(sdf::Value::Bool(true)));
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
fn camera_unauthored_attrs_fall_back() -> Result<()> {
    let stage = open()?;
    // /World/Cam authors only focalLength; the rest read back the fallbacks
    // `Camera` declares.
    let c = Camera::get(&stage, sdf::path("/World/Cam")?)?.expect("Camera");
    assert_eq!(c.focal_length_attr().get()?, Some(sdf::Value::Float(50.0)));
    assert_eq!(c.horizontal_aperture_attr().get()?, Some(sdf::Value::Float(20.955)));
    assert_eq!(c.projection_attr().get()?, Some(sdf::Value::token("perspective")));
    Ok(())
}

#[test]
fn orthographic_projection_token() -> Result<()> {
    let stage = open()?;
    let c = Camera::get(&stage, sdf::path("/World/OrthoCam")?)?.expect("Camera");
    assert_eq!(c.projection_attr().get()?, Some(sdf::Value::token("orthographic")));
    // `Projection` decodes the authored token.
    let tok = c.projection_attr().get::<Token>()?;
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

// ── Mesh + Subset ─────────────────────────────────────────────

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
    assert_eq!(m.orientation_attr().get::<Token>()?.as_deref(), Some("leftHanded"));
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
    assert_eq!(m.subdivision_scheme_attr().get::<Token>()?.as_deref(), Some("none"));
    assert_eq!(
        m.interpolate_boundary_attr().get::<Token>()?.as_deref(),
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
        m.normals_attr().metadata::<Token>("interpolation")?.as_deref(),
        Some("vertex")
    );
    Ok(())
}

#[test]
fn mesh_uvs_face_varying() -> Result<()> {
    let stage = open()?;
    let m = Mesh::get(&stage, sdf::path("/World/FancyMesh")?)?.expect("Mesh");
    // `primvars:st` is no schema property, so it has no accessor of its own.
    let st = m.attribute("primvars:st");
    assert_eq!(
        st.get::<sdf::Value>()?
            .and_then(|v| v.try_as_vec_2f_vec())
            .map(|v| v.len()),
        Some(4)
    );
    assert_eq!(st.metadata::<Token>("interpolation")?.as_deref(), Some("faceVarying"));
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
        m.display_color_attr().metadata::<Token>("interpolation")?.as_deref(),
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
    let s = Subset::get(&stage, sdf::path("/World/FancyMesh/Front")?)?.expect("Subset");
    assert_eq!(s.element_type_attr().get::<Token>()?.as_deref(), Some("face"));
    assert_eq!(s.family_name_attr().get::<Token>()?.as_deref(), Some("materialBind"));
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
    assert_eq!(c.type_attr().get::<Token>()?.as_deref(), Some("linear"));
    assert_eq!(c.wrap_attr().get::<Token>()?.as_deref(), Some("nonperiodic"));
    assert_eq!(
        c.widths_attr()
            .get::<sdf::Value>()?
            .and_then(|v| v.try_as_float_vec())
            .map(|v| v.len()),
        Some(4)
    );
    // `basis` is unauthored, so it reads back the schema's own fallback.
    assert_eq!(c.basis_attr().get()?, Some(sdf::Value::token("bezier")));
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
    // uForm is authored; vForm is not, and reads back the schema's fallback.
    assert_eq!(p.u_form_attr().get::<Token>()?.as_deref(), Some("periodic"));
    assert_eq!(p.v_form_attr().get()?, Some(sdf::Value::token("open")));
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

/// The purpose visibilities share one enum with no `Default`, since guide
/// falls back to `invisible` where proxy and render fall back to `inherited`;
/// a model's draw mode and card geometry each carry their own fallback.
#[test]
fn model_token_round_trip() {
    assert_eq!(geom::PurposeVisibility::Visible.as_token(), "visible");
    assert_eq!(
        geom::PurposeVisibility::from_token("inherited"),
        Some(geom::PurposeVisibility::Inherited)
    );
    assert_eq!(
        geom::PurposeVisibility::from_token("invisible"),
        Some(geom::PurposeVisibility::Invisible)
    );
    assert_eq!(geom::PurposeVisibility::from_token("bogus"), None);

    assert_eq!(geom::DrawMode::default(), geom::DrawMode::Inherited);
    assert_eq!(geom::DrawMode::Cards.as_token(), "cards");
    assert_eq!(geom::DrawMode::from_token("default"), Some(geom::DrawMode::Default));
    assert_eq!(geom::DrawMode::from_token("bogus"), None);

    assert_eq!(geom::CardGeometry::default(), geom::CardGeometry::Cross);
    assert_eq!(geom::CardGeometry::FromTexture.as_token(), "fromTexture");
    assert_eq!(geom::CardGeometry::from_token("box"), Some(geom::CardGeometry::Box));
    assert_eq!(geom::CardGeometry::from_token("bogus"), None);
}

/// An in-memory stage carrying the schema data, which is what makes a prim its
/// type and resolves the fallbacks its schema declares.
fn memory() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")
}

#[test]
fn camera_roundtrip() -> Result<()> {
    let stage = memory()?;
    let cam = Camera::define(&stage, "/Cam")?;
    cam.create_focal_length_attr()?.set(50.0_f32)?;
    cam.create_projection_attr()?
        .set(sdf::Value::Token("perspective".into()))?;
    cam.create_clipping_range_attr()?
        .set(sdf::Value::vec2f(0.1_f32, 1000.0))?;

    let cam = Camera::get(&stage, "/Cam")?.expect("Camera");
    assert_eq!(cam.focal_length_attr().get()?, Some(sdf::Value::Float(50.0)));
    assert_eq!(
        cam.projection_attr().get()?,
        Some(sdf::Value::Token("perspective".into()))
    );
    assert_eq!(
        cam.clipping_range_attr().get()?,
        Some(sdf::Value::vec2f(0.1_f32, 1000.0))
    );
    assert!(Camera::get(&stage, "/Cam")?.is_some());
    Ok(())
}

#[test]
fn basis_curves_roundtrip() -> Result<()> {
    let stage = memory()?;
    let c = BasisCurves::define(&stage, "/C")?;
    c.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
        [0.0_f32, 0.0, 0.0].into(),
        [1.0, 0.0, 0.0].into(),
    ]))?;
    c.create_curve_vertex_counts_attr()?.set(sdf::Value::IntVec(vec![2]))?;
    c.create_type_attr()?.set(sdf::Value::Token("linear".into()))?;
    c.create_widths_attr()?
        .set_metadata(geom::tokens::INTERPOLATION, sdf::Value::Token("vertex".into()))?
        .set(sdf::Value::FloatVec(vec![0.1, 0.1]))?;

    let c = BasisCurves::get(&stage, "/C")?.expect("BasisCurves");
    assert_eq!(c.curve_vertex_counts_attr().get()?, Some(sdf::Value::IntVec(vec![2])));
    assert_eq!(c.type_attr().get()?, Some(sdf::Value::Token("linear".into())));
    assert_eq!(
        c.widths_attr().metadata(geom::tokens::INTERPOLATION)?,
        Some(sdf::Value::Token("vertex".into()))
    );
    assert!(BasisCurves::get(&stage, "/Missing")?.is_none());
    Ok(())
}

#[test]
fn hermite_curves_tangents() -> Result<()> {
    let stage = memory()?;
    let c = HermiteCurves::define(&stage, "/H")?;
    c.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
        [0.0_f32, 0.0, 0.0].into(),
        [1.0, 0.0, 0.0].into(),
    ]))?;
    c.create_curve_vertex_counts_attr()?.set(sdf::Value::IntVec(vec![2]))?;
    c.create_tangents_attr()?.set(sdf::Value::Vec3fVec(vec![
        [1.0_f32, 0.0, 0.0].into(),
        [1.0, 0.0, 0.0].into(),
    ]))?;

    let c = HermiteCurves::get(&stage, "/H")?.expect("HermiteCurves");
    assert_eq!(
        c.tangents_attr()
            .get::<sdf::Value>()?
            .and_then(|v| v.try_as_vec_3f_vec())
            .map(|v| v.len()),
        Some(2)
    );
    Ok(())
}

#[test]
fn nurbs_curves_attrs() -> Result<()> {
    let stage = memory()?;
    let c = NurbsCurves::define(&stage, "/N")?;
    c.create_order_attr()?.set(vec![4])?;
    c.create_knots_attr()?
        .set(sdf::Value::DoubleVec(vec![0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 1.0]))?;
    c.create_point_weights_attr()?.set(vec![1.0_f64, 1.0, 1.0, 1.0])?;

    let c = NurbsCurves::get(&stage, "/N")?.expect("NurbsCurves");
    assert_eq!(c.order_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
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
fn xform_and_scope_are_pure_typed_prims() -> Result<()> {
    let stage = memory()?;
    Xform::define(&stage, "/Group")?;
    Scope::define(&stage, "/Stage")?;

    assert_eq!(stage.prim("/Group")?.type_name()?.as_deref(), Some("Xform"));
    assert_eq!(stage.prim("/Stage")?.type_name()?.as_deref(), Some("Scope"));
    assert!(Xform::get(&stage, "/Group")?.is_some());
    assert!(Scope::get(&stage, "/Stage")?.is_some());
    assert!(Xform::get(&stage, "/Stage")?.is_none());
    Ok(())
}

#[test]
fn point_instancer_roundtrip() -> Result<()> {
    let stage = memory()?;
    Cube::define(&stage, "/Proto/Marker")?
        .create_size_attr()?
        .set(0.1_f64)?;

    let pi = PointInstancer::define(&stage, "/Instances")?;
    pi.create_prototypes_rel()?.set_targets(["/Proto/Marker"])?;
    pi.create_proto_indices_attr()?.set(sdf::Value::IntVec(vec![0, 0, 0]))?;
    pi.create_positions_attr()?.set(sdf::Value::Vec3fVec(vec![
        [0.0_f32, 0.0, 0.0].into(),
        [1.0, 0.0, 0.0].into(),
        [2.0, 0.0, 0.0].into(),
    ]))?;
    pi.create_ids_attr()?.set(sdf::Value::Int64Vec(vec![100, 200, 300]))?;
    pi.create_invisible_ids_attr()?.set(sdf::Value::Int64Vec(vec![200]))?;

    let pi = PointInstancer::get(&stage, "/Instances")?.expect("PointInstancer");
    assert_eq!(pi.proto_indices_attr().get()?, Some(sdf::Value::IntVec(vec![0, 0, 0])));
    assert_eq!(pi.invisible_ids_attr().get()?, Some(sdf::Value::Int64Vec(vec![200])));
    assert_eq!(pi.prototypes_rel().targets()?, vec![sdf::path("/Proto/Marker")?]);
    // Inherited Boundable / Xformable accessors are available.
    assert_eq!(pi.extent_attr().get::<sdf::Value>()?, None);
    assert!(PointInstancer::get(&stage, "/Proto/Marker")?.is_none());
    Ok(())
}

#[test]
fn geom_subset_is_typed_not_imageable() -> Result<()> {
    let stage = memory()?;
    let s = Subset::define(&stage, "/M/RedFaces")?;
    s.create_element_type_attr()?.set(sdf::Value::Token("face".into()))?;
    s.create_family_name_attr()?
        .set(sdf::Value::Token("materialBind".into()))?;
    s.create_indices_attr()?.set(sdf::Value::IntVec(vec![0]))?;

    let s = Subset::get(&stage, "/M/RedFaces")?.expect("Subset");
    assert_eq!(s.element_type_attr().get()?, Some(sdf::Value::Token("face".into())));
    assert_eq!(s.indices_attr().get()?, Some(sdf::Value::IntVec(vec![0])));
    assert_eq!(Subset::KIND, openusd::usd::SchemaKind::ConcreteTyped);
    Ok(())
}

#[test]
fn mesh_topology_and_subdiv() -> Result<()> {
    let stage = memory()?;
    let m = Mesh::define(&stage, "/M")?;
    m.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
        [0.0_f32, 0.0, 0.0].into(),
        [1.0, 0.0, 0.0].into(),
        [1.0, 1.0, 0.0].into(),
        [0.0, 1.0, 0.0].into(),
    ]))?;
    m.create_face_vertex_counts_attr()?.set(sdf::Value::IntVec(vec![4]))?;
    m.create_face_vertex_indices_attr()?
        .set(sdf::Value::IntVec(vec![0, 1, 2, 3]))?;
    m.create_subdivision_scheme_attr()?
        .set(sdf::Value::Token("none".into()))?;
    m.create_orientation_attr()?
        .set(sdf::Value::Token("leftHanded".into()))?;
    m.create_display_color_attr()?
        .set(sdf::Value::Vec3fVec(vec![[1.0_f32, 0.0, 0.0].into()]))?;

    let m = Mesh::get(&stage, "/M")?.expect("Mesh");
    assert_eq!(m.face_vertex_counts_attr().get()?, Some(sdf::Value::IntVec(vec![4])));
    assert_eq!(
        m.face_vertex_indices_attr().get()?,
        Some(sdf::Value::IntVec(vec![0, 1, 2, 3]))
    );
    assert_eq!(
        m.subdivision_scheme_attr().get()?,
        Some(sdf::Value::Token("none".into()))
    );
    // Inherited Gprim / PointBased accessors are available on the handle.
    assert_eq!(
        m.orientation_attr().get()?,
        Some(sdf::Value::Token("leftHanded".into()))
    );
    assert_eq!(
        m.points_attr()
            .get::<sdf::Value>()?
            .and_then(|v| v.try_as_vec_3f_vec())
            .map(|v| v.len()),
        Some(4)
    );
    assert_eq!(
        m.display_color_attr().get()?,
        Some(sdf::Value::Vec3fVec(vec![[1.0_f32, 0.0, 0.0].into()]))
    );
    Ok(())
}

#[test]
fn points_widths_and_ids() -> Result<()> {
    let stage = memory()?;
    let p = Points::define(&stage, "/Cloud")?;
    p.create_points_attr()?.set(sdf::Value::Vec3fVec(vec![
        [0.0_f32, 0.0, 0.0].into(),
        [1.0, 0.0, 0.0].into(),
    ]))?;
    p.create_widths_attr()?.set(sdf::Value::FloatVec(vec![0.1, 0.1]))?;
    p.create_ids_attr()?.set(sdf::Value::Int64Vec(vec![10, 20]))?;

    let p = Points::get(&stage, "/Cloud")?.expect("Points");
    assert_eq!(p.widths_attr().get()?, Some(sdf::Value::FloatVec(vec![0.1, 0.1])));
    assert_eq!(p.ids_attr().get()?, Some(sdf::Value::Int64Vec(vec![10, 20])));
    Ok(())
}

#[test]
fn axial_shapes_roundtrip() -> Result<()> {
    let stage = memory()?;
    let cyl = Cylinder::define(&stage, "/Pipe")?;
    cyl.create_radius_attr()?.set(0.3_f64)?;
    cyl.create_height_attr()?.set(2.0_f64)?;
    cyl.create_axis_attr()?.set(sdf::Value::Token("X".into()))?;

    let cyl = Cylinder::get(&stage, "/Pipe")?.expect("Cylinder");
    assert_eq!(cyl.radius_attr().get()?, Some(sdf::Value::Double(0.3)));
    assert_eq!(cyl.axis_attr().get()?, Some(sdf::Value::Token("X".into())));

    Cone::define(&stage, "/Pyramid")?.create_height_attr()?.set(2.0_f64)?;
    assert!(Cone::get(&stage, "/Pyramid")?.is_some());
    Capsule::define(&stage, "/Pill")?.create_radius_attr()?.set(0.5_f64)?;
    assert!(Capsule::get(&stage, "/Pill")?.is_some());
    Ok(())
}

#[test]
fn cube_roundtrip() -> Result<()> {
    let stage = memory()?;
    Cube::define(&stage, "/Box")?.create_size_attr()?.set(0.5_f64)?;

    let cube = Cube::get(&stage, "/Box")?.expect("Cube");
    assert_eq!(cube.size_attr().get()?, Some(sdf::Value::Double(0.5)));
    assert!(Cube::get(&stage, "/Missing")?.is_none());
    Ok(())
}

#[test]
fn plane_roundtrip() -> Result<()> {
    let stage = memory()?;
    let plane = Plane::define(&stage, "/Ground")?;
    plane.create_width_attr()?.set(10.0_f64)?;
    plane.create_length_attr()?.set(20.0_f64)?;
    plane.create_axis_attr()?.set(sdf::Value::Token("Y".into()))?;
    plane.create_double_sided_attr()?.set(false)?;

    let plane = Plane::get(&stage, "/Ground")?.expect("Plane");
    assert_eq!(plane.width_attr().get()?, Some(sdf::Value::Double(10.0)));
    assert_eq!(plane.double_sided_attr().get()?, Some(sdf::Value::Bool(false)));
    Ok(())
}

#[test]
fn sphere_roundtrip_and_chain() -> Result<()> {
    let stage = memory()?;
    let sphere = Sphere::define(&stage, "/Ball")?;
    sphere.create_radius_attr()?.set(2.5_f64)?;
    // Inherited through the Gprim â†’ â€¦ â†’ Imageable chain.
    sphere.create_purpose_attr()?.set(sdf::Value::Token("render".into()))?;
    sphere.create_double_sided_attr()?.set(true)?;

    let sphere = Sphere::get(&stage, "/Ball")?.expect("Sphere");
    assert_eq!(sphere.radius_attr().get()?, Some(sdf::Value::Double(2.5)));
    assert_eq!(sphere.compute_purpose()?, Purpose::Render);
    assert_eq!(sphere.double_sided_attr().get()?, Some(sdf::Value::Bool(true)));
    assert_eq!(Sphere::KIND, openusd::usd::SchemaKind::ConcreteTyped);
    Ok(())
}

// Primvars, read from assets other tools authored.

/// A stage over an asset of the USD working group's collection.
fn vendor(asset: &str) -> Result<Stage> {
    let path = format!("{}vendor/usd-wg-assets/{asset}", env!("CARGO_WORKSPACE_DIR"));
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(&path)
}

fn primvars(stage: &Stage, path: &str) -> Result<PrimvarsAPI> {
    Ok(PrimvarsAPI::from_prim_unchecked(stage.prim(path)?))
}

/// Indexed face-varying UVs flatten to one coordinate per face vertex, each
/// the value its index names.
#[test]
fn mcusd_st_flattens() -> Result<(), SchemaError> {
    let stage = vendor("full_assets/McUsd/McUsd.usda")?;
    let mesh = Mesh::get(&stage, sdf::path("/McUsd/Geom/grass_block_top")?)?.expect("Mesh");
    let st = primvars(&stage, "/McUsd/Geom/grass_block_top")?.primvar("st")?;
    assert_eq!(st.interpolation()?, Interpolation::FaceVarying);
    assert!(st.is_indexed()?);

    let values = st.get_at::<Vec<Vec2f>>(None)?.expect("authored");
    let indices = st.indices(None)?.expect("authored");
    let flattened = st.flattened::<Vec<Vec2f>>(None)?.expect("flattened");
    assert_eq!(values.len(), 4);
    let face_vertices: i32 = mesh
        .face_vertex_counts_attr()
        .get::<Vec<i32>>()?
        .expect("authored")
        .iter()
        .sum();
    assert_eq!(flattened.len(), usize::try_from(face_vertices).expect("a count"));
    for (flat, index) in flattened.iter().zip(&indices) {
        assert_eq!(*flat, values[usize::try_from(*index).expect("an index")]);
    }
    Ok(())
}

/// Indices authored as `None` are blocked, so the primvar is not indexed and
/// flattens to its own values.
#[test]
fn teapot_indices_blocked() -> Result<(), SchemaError> {
    let stage = vendor("full_assets/Teapot/geo/UtahTeapot.usd")?;
    let teapot = primvars(&stage, "/UtahTeapot/Geometry")?;
    for name in ["rest", "st"] {
        let primvar = teapot.primvar(name)?;
        assert!(primvar.indices_attr().is_defined()?, "{name}");
        assert!(!primvar.is_indexed()?, "{name}");
        assert_eq!(
            primvar.flattened::<sdf::Value>(None)?,
            primvar.get_at::<sdf::Value>(None)?,
            "{name}"
        );
    }
    assert_eq!(teapot.primvar("st")?.interpolation()?, Interpolation::FaceVarying);
    assert_eq!(teapot.primvar("rest")?.interpolation()?, Interpolation::Vertex);
    Ok(())
}

/// Each interpolation reads back from the mesh that demonstrates it, with the
/// value count the mesh's topology gives it.
#[test]
fn interpolation_doc_asset() -> Result<(), SchemaError> {
    let stage = vendor("docs/PrimvarInterpolation/primvar_interpolation.usda")?;
    let expected = [
        ("constant", Interpolation::Constant, 1),
        ("uniform", Interpolation::Uniform, 2),
        ("varying", Interpolation::Varying, 6),
        ("vertex", Interpolation::Vertex, 6),
        ("faceVarying", Interpolation::FaceVarying, 8),
    ];
    for (name, interpolation, count) in expected {
        let mesh = primvars(&stage, &format!("/World/{name}"))?;
        let colors = mesh.primvars_with_authored_values()?;
        assert_eq!(colors.len(), 1, "{name}");
        let color = &colors[0];
        assert_eq!(color.primvar_name(), "displayColor", "{name}");
        assert_eq!(color.interpolation()?, interpolation, "{name}");
        assert!(!color.is_indexed()?, "{name}");
        let values = color.flattened::<Vec<Vec3f>>(None)?.expect("authored");
        assert_eq!(values.len(), count, "{name}");
    }
    Ok(())
}

/// `BBoxCache` against the fixtures of the C++ `testUsdGeomBBoxCache`.
mod bbox_cache {
    use std::collections::{BTreeSet, HashMap};

    use openusd::usd::{self, SchemaBase};
    use openusd::{gf, sdf};
    use openusd_schemas::SchemaError;
    use openusd_schemas::geom::{
        BBoxCache, Boundable, BoundableExt, Imageable, ImageableExt, ImageableSchema, ModelAPI, PointInstancer,
        PointInstancerSchema, Purpose, Sphere, Visibility, XformCache,
    };

    type Result<T = ()> = std::result::Result<T, SchemaError>;

    fn open(name: &str) -> Result<usd::Stage> {
        open_with(name, usd::InitialLoadSet::LoadAll)
    }

    fn open_with(name: &str, load: usd::InitialLoadSet) -> Result<usd::Stage> {
        Ok(usd::Stage::builder()
            .schema_registry(openusd_schemas::schema_registry())
            .load(load)
            .open(&format!("fixtures/bbox_cache/{name}"))?)
    }

    fn range(min: [f64; 3], max: [f64; 3]) -> gf::Range3d {
        gf::Range3d::new(min.into(), max.into())
    }

    fn close(a: gf::Vec3d, b: gf::Vec3d) -> bool {
        (a - b).length() < 1e-5
    }

    #[track_caller]
    fn assert_range(found: gf::Range3d, expected: gf::Range3d) {
        assert!(
            close(found.min(), expected.min()) && close(found.max(), expected.max()),
            "{found:?} is not {expected:?}"
        );
    }

    /// The world-aligned range around the boundable prims at and beneath
    /// `root`, each one's extent placed by its own local-to-world
    /// transform: what a cache bounds, computed with none. The walk leaves
    /// out what a cache leaves out, and reaches an instance's contents
    /// through its proxies.
    fn leaf_union(root: &usd::Prim, time: Option<usd::TimeCode>, purposes: &[Purpose]) -> Result<gf::Range3d> {
        let children = usd::PrimPredicate::new(
            usd::PrimStatus::ACTIVE | usd::PrimStatus::DEFINED,
            usd::PrimStatus::ABSTRACT,
        )
        .with_instance_proxies(true);
        let mut xforms = XformCache::new(time);
        let mut union = gf::Range3d::EMPTY;
        let mut stack = vec![root.clone()];
        while let Some(prim) = stack.pop() {
            if let Some(boundable) = Boundable::from_prim(prim.clone())? {
                let included = purposes.contains(&boundable.compute_purpose()?);
                if let Some(extent) = boundable.compute_extent(time)?.filter(|_| included) {
                    let bbox = gf::BBox3d::new(extent.into(), xforms.local_to_world_transform(&prim)?);
                    union = union.union(bbox.aligned_range());
                }
                continue;
            }
            for child in prim.filtered_children(children)? {
                let imageable = Imageable::from_prim(child.clone())?;
                if imageable.is_none() && child.is_a(usd::tokens::TYPED)? {
                    continue;
                }
                let invisible = match &imageable {
                    Some(imageable) => {
                        imageable.visibility_attr().get_at::<Visibility>(time)? == Some(Visibility::Invisible)
                    }
                    None => false,
                };
                if !invisible {
                    stack.push(child);
                }
            }
        }
        Ok(union)
    }

    /// The untransformed, local and world bounds of a component, at the
    /// default time and at a time its parent has moved by.
    #[test]
    fn bounds_three_spaces() -> Result {
        let stage = open("cubeSbdv.usda")?;
        let prim = stage.prim("/parent/primWithLocalXform")?;
        let mut cache = BBoxCache::new(None, [Purpose::Default]);

        for (time, world) in [(None, 0.5), (Some(usd::TimeCode::new(1.0)), 1.5)] {
            cache.set_time(time);
            let untransformed = cache.untransformed_bound(&prim)?;
            assert_eq!(untransformed.matrix(), gf::Mat4d::IDENTITY);
            assert_range(untransformed.range(), range([-1.5; 3], [-0.5; 3]));
            assert_range(cache.local_bound(&prim)?.aligned_range(), range([-0.5; 3], [0.5; 3]));

            let found = cache.world_bound(&prim)?;
            assert_eq!(found, cache.world_bound(&prim)?);
            assert_range(found.aligned_range(), range([world; 3], [world + 1.0; 3]));
            assert_range(found.aligned_range(), leaf_union(&prim, time, &[Purpose::Default])?);
        }
        Ok(())
    }

    /// An invisible prim is bounded when it is the prim asked for, and its
    /// own invisible child is still left out.
    #[test]
    fn invisible_queried_directly() -> Result {
        let stage = open("cubeSbdv.usda")?;
        let prim = stage.prim("/parent/primWithLocalXform/InvisibleChild")?;
        let mut cache = BBoxCache::new(None, [Purpose::Default]);
        let found = cache.world_bound(&prim)?.aligned_range();
        assert_range(found, range([7.5, 0.5, 0.5], [8.5, 1.5, 1.5]));
        assert_range(found, leaf_union(&prim, None, &[Purpose::Default])?);
        Ok(())
    }

    /// Each purpose has its own box, and several purposes combine theirs.
    /// Changing the purposes drops nothing.
    #[test]
    fn purposes_select_boxes() -> Result {
        let stage = open("cubeSbdv.usda")?;
        let prim = stage.prim("/parent/primWithLocalXform")?;
        let mut cache = BBoxCache::new(None, [Purpose::Default]);
        let boxes = [
            (Purpose::Guide, range([-2.5, -2.5, -3.5], [-1.5, -1.5, -2.5])),
            (Purpose::Render, range([-0.5, -2.5, -3.5], [0.5, -1.5, -2.5])),
            (Purpose::Proxy, range([1.5, -2.5, -3.5], [2.5, -1.5, -2.5])),
        ];
        for (purpose, expected) in boxes {
            cache.set_included_purposes([purpose]);
            assert_eq!(cache.included_purposes(), [purpose]);
            assert_range(cache.untransformed_bound(&prim)?.aligned_range(), expected);
            let world = cache.world_bound(&prim)?.aligned_range();
            assert_range(world, leaf_union(&prim, None, &[purpose])?);
        }

        let several = [Purpose::Default, Purpose::Proxy, Purpose::Render];
        cache.set_included_purposes(several);
        assert_range(
            cache.untransformed_bound(&prim)?.aligned_range(),
            range([-1.5, -2.5, -3.5], [2.5, -0.5, -0.5]),
        );
        assert_range(
            cache.world_bound(&prim)?.aligned_range(),
            leaf_union(&prim, None, &several)?,
        );

        cache.set_included_purposes([]);
        assert!(cache.world_bound(&prim)?.range().is_empty());
        Ok(())
    }

    /// With no component above them, rotated prims are unioned in world
    /// space, where the cache's range is the union of its leaves'.
    #[test]
    fn rotated_bounds() -> Result {
        let stage = open("cubeSbdv.usda")?;
        let mut cache = BBoxCache::new(None, [Purpose::Default]);
        let half = 0.5 * 2f64.sqrt();

        // A unit cube turned an eighth about X, then moved.
        let turned = stage.prim("/Rotated/Trans")?;
        let found = cache.world_bound(&turned)?.aligned_range();
        assert_range(found, range([3.5, -4.0 - half, -half], [4.5, -4.0 + half, half]));

        for path in ["/Rotated", "/Rotated/Rotate135AndTranslate/Rot45", "/Rotated/Rotate90"] {
            let prim = stage.prim(path)?;
            let found = cache.world_bound(&prim)?.aligned_range();
            assert_range(found, leaf_union(&prim, None, &[Purpose::Default])?);
        }
        Ok(())
    }

    /// An instance is bounded as the same prims are with no instancing.
    #[test]
    fn instanced_matches_plain() -> Result {
        let stage = open("cubeSbdv_instanced.usda")?;
        assert!(stage.prim("/instanced_parent")?.is_instance()?);
        for use_hint in [false, true] {
            let mut cache = BBoxCache::new(None, [Purpose::Default]).with_extents_hint(use_hint);
            for time in [None, Some(usd::TimeCode::new(1.0))] {
                cache.set_time(time);
                for name in ["parent", "Rotated"] {
                    let instanced = stage.prim(format!("/instanced_{name}").as_str())?;
                    let plain = stage.prim(format!("/uninstanced_{name}").as_str())?;
                    let found = cache.world_bound(&instanced)?.aligned_range();
                    assert!(!found.is_empty());
                    assert_range(found, cache.world_bound(&plain)?.aligned_range());
                    if !use_hint {
                        assert_range(found, leaf_union(&instanced, time, &[Purpose::Default])?);
                    }
                }
            }
        }
        Ok(())
    }

    /// The purpose an instance hands down reaches its prototype's prims,
    /// whichever of the two levels of instancing is in use.
    #[test]
    fn purpose_through_instances() -> Result {
        let default = gf::BBox3d::from(range([-1.5, -1.5, -1.5], [1.5, 1.5, 10.5]));
        let render = gf::BBox3d::from(range([-11.0, -1.5, -16.5], [1.5, 1.5, 10.5]));
        let stages = [
            ("disableAllInstancing.usda", 0),
            ("disableInnerInstancing.usda", 1),
            ("disableOuterInstancing.usda", 1),
            ("nestedInstanceTest.usda", 2),
        ];
        let mut default_cache = BBoxCache::new(None, [Purpose::Default]);
        let mut render_cache = BBoxCache::new(None, [Purpose::Default, Purpose::Render]);
        for (name, prototypes) in stages {
            let stage = open(name)?;
            let root = stage.prim("/Root")?;
            assert_eq!(default_cache.world_bound(&root)?, default, "{name}");
            assert_eq!(render_cache.world_bound(&root)?, render, "{name}");
            assert_eq!(stage.prototypes()?.len(), prototypes, "{name}");
        }
        Ok(())
    }

    /// A bound follows a child's animated visibility across times.
    #[test]
    fn visibility_change_invalidates() -> Result {
        let stage = open("animVis.usda")?;
        let root = stage.prim("/")?;
        let mut cache = BBoxCache::new(usd::TimeCode::new(0.0), [Purpose::Default]);
        for (time, empty) in [(0.0, true), (1.0, false), (2.0, true), (3.0, false)] {
            cache.set_time(usd::TimeCode::new(time));
            assert_eq!(cache.world_bound(&root)?.range().is_empty(), empty, "at {time}");
        }

        // With visibility ignored the prim is bounded at every time.
        let mut cache = BBoxCache::new(usd::TimeCode::new(0.0), [Purpose::Default])
            .with_extents_hint(true)
            .with_ignore_visibility(true);
        assert!(cache.ignores_visibility() && cache.uses_extents_hint());
        assert!(!cache.world_bound(&root)?.range().is_empty());
        Ok(())
    }

    /// Extents are the authored ones, or else computed from points and
    /// widths. Sizes that cannot bound a prim fail the query for it and for
    /// what holds it.
    #[test]
    fn computed_extents() -> Result {
        let stage = open("pointsAndCurves.usda")?;
        let mut cache = BBoxCache::new(usd::TimeCode::new(0.0), [Purpose::Default]);
        let mut bound =
            |path: &str| -> Result<gf::Range3d> { Ok(cache.untransformed_bound(&stage.prim(path)?)?.range()) };

        assert_eq!(
            bound("/ValidPrims/extentAuthored")?,
            range([-3.0, 0.0, -2.0], [1.0, 2.0, 1.0])
        );
        assert!(bound("/ValidPrims/empty")?.is_empty());
        assert!(bound("/ValidPrims/noGeometricDataAuthored")?.is_empty());
        assert_eq!(bound("/ValidPrims/bezierWExtent")?, range([-1.0; 3], [1.0; 3]));

        assert_eq!(
            bound("/WarningPrims/fourPointsWWidth")?,
            range([-5.5, -4.5, -6.5], [6.0, 5.0, 8.0])
        );
        assert_eq!(
            bound("/WarningPrims/pointsNoWidth")?,
            range([-3.0, -5.0, -3.0], [2.0, 1.0, 3.0])
        );
        assert_eq!(
            bound("/WarningPrims/zeroVolumeExtent")?,
            range([-6.0, 0.0, 3.0], [-6.0, 0.0, 3.0])
        );
        assert!(bound("/WarningPrims/emptyPointsData")?.is_empty());
        assert_range(
            bound("/WarningPrims/bezierWwidth")?,
            range([-1.1, -0.1, -1.1], [0.1, 0.1, 1.1]),
        );

        // An extent of one corner gives way to the computed one.
        assert_eq!(
            bound("/ErrorPrims/illAuthoredExtent")?,
            range([-2.0, -1.0, 0.0], [-2.0, -1.0, 0.0])
        );
        assert_eq!(bound("/ErrorPrims/illAuthoredSphere")?, range([-1.0; 3], [1.0; 3]));
        for path in ["/ErrorPrims/invalidNumWidthsAndPoints", "/ErrorPrims"] {
            let refused = bound(path);
            assert!(
                matches!(refused, Err(SchemaError::WidthCountMismatch { found: 2, expected: 3 })),
                "{refused:?}"
            );
        }
        // The failure leaves the cache answering the prims beside it.
        assert_eq!(bound("/ErrorPrims/illAuthoredSphere")?, range([-1.0; 3], [1.0; 3]));
        assert!(!bound("/ValidPrims")?.is_empty());
        Ok(())
    }

    /// Prims that are undefined, inactive or abstract bound nothing, asked
    /// for directly or as children, and neither does a prim that does not
    /// exist.
    #[test]
    fn undefined_inactive_abstract() -> Result {
        let stage = open("cubeSbdv.usda")?;
        let mut cache = BBoxCache::new(None, [Purpose::Default]);
        for path in ["/undefinedCube1", "/inactiveCube1", "/_class_UnitCube", "/Missing"] {
            let bound = cache.world_bound(&stage.prim(path)?)?;
            assert!(bound.range().is_empty(), "{path}");
        }
        assert_range(
            cache.world_bound(&stage.prim("/pCube1")?)?.aligned_range(),
            range([3.5, 4.5, 5.5], [4.5, 5.5, 6.5]),
        );
        Ok(())
    }

    /// Prims of no type are walked through to the imageable prims beneath
    /// them.
    #[test]
    fn untyped_ancestors_kept() -> Result {
        let stage = usd::Stage::builder()
            .schema_registry(openusd_schemas::schema_registry())
            .in_memory("anon.usda")?;
        let world = stage.define_prim("/World")?;
        stage.define_prim("/World/anim")?;
        stage.define_prim("/World/anim/char")?;
        Sphere::define(&stage, "/World/anim/char/sphere")?;

        let mut cache = BBoxCache::new(None, [Purpose::Default]).with_extents_hint(true);
        assert_range(
            cache.untransformed_bound(&world)?.aligned_range(),
            range([-1.0; 3], [1.0; 3]),
        );
        Ok(())
    }

    /// A bound relative to the parent is the prim's extent under its own
    /// local transform.
    #[test]
    fn relative_to_parent() -> Result {
        let stage = open("testUSD4957.usda")?;
        let (b, c) = (stage.prim("/A/B")?, stage.prim("/A/B/C")?);
        let mut cache = BBoxCache::new(None, [Purpose::Default, Purpose::Render]);
        let relative = cache.relative_bound(&c, &b)?;

        let extent = Boundable::from_prim_unchecked(c.clone())
            .compute_extent(None)?
            .expect("a sphere");
        let local = XformCache::default().local_transform(&c)?.0;
        assert_range(
            relative.aligned_range(),
            gf::BBox3d::new(extent.into(), local).aligned_range(),
        );
        assert_range(relative.aligned_range(), range([9.0; 3], [11.0; 3]));
        Ok(())
    }

    /// With the hint in use, a component is bounded by its hint, purpose by
    /// purpose, at the time the hint is sampled at too.
    #[test]
    fn hint_bounds_three_spaces() -> Result {
        let stage = open("cubeSbdv.usda")?;
        let prim = stage.prim("/parent/primWithLocalXform")?;
        let model = ModelAPI::from_prim_unchecked(prim.clone());
        let mut cache = BBoxCache::new(None, [Purpose::Default]).with_extents_hint(true);

        for (time, world) in [(None, 0.5), (Some(usd::TimeCode::new(1.0)), 1.5)] {
            cache.set_time(time);
            let hint = model.extents_hint_at(time)?.expect("a hint");
            assert_eq!(hint.len(), 4);
            for (purpose, extent) in Purpose::ORDERED.into_iter().zip(hint) {
                cache.set_included_purposes([purpose]);
                assert_eq!(
                    cache.untransformed_bound(&prim)?,
                    gf::BBox3d::from(gf::Range3d::from(extent))
                );
            }
            cache.set_included_purposes([Purpose::Default]);
            assert_range(
                cache.world_bound(&prim)?.aligned_range(),
                range([world; 3], [world + 1.0; 3]),
            );
        }

        // The prims beneath a hinted model are still bounded when asked for.
        let child = stage.prim("/parent/primWithLocalXform/Child")?;
        assert_range(cache.untransformed_bound(&child)?.range(), range([-0.5; 3], [0.5; 3]));
        Ok(())
    }

    /// A model whose payload is not loaded is bounded by its hint, and by
    /// nothing with the hint not in use.
    #[test]
    fn hint_bounds_unloaded() -> Result {
        let stage = open_with("unloadedCubeModel.usda", usd::InitialLoadSet::LoadNone)?;
        assert!(!stage.prim("/World/CubeModel")?.is_loaded()?);
        let root = stage.prim("/")?;
        let time = usd::TimeCode::new(0.0);

        let mut without = BBoxCache::new(time, [Purpose::Default]);
        assert!(without.world_bound(&root)?.range().is_empty());
        let mut with = BBoxCache::new(time, [Purpose::Default]).with_extents_hint(true);
        assert_range(with.world_bound(&root)?.aligned_range(), range([-1.0; 3], [1.0; 3]));

        // The override walk reaches the unloaded model too.
        let skip = BTreeSet::from([sdf::path("/World/Absent")?]);
        let world = stage.prim("/World")?;
        let found = with.untransformed_bound_with_overrides(&world, &skip, &HashMap::new())?;
        assert_range(found.aligned_range(), range([-1.0; 3], [1.0; 3]));
        Ok(())
    }

    /// A model bounded by its hint leaves nothing behind that a later query
    /// for a prim beneath it trips on.
    #[test]
    fn hint_then_descendant() -> Result {
        let stage = usd::Stage::builder()
            .schema_registry(openusd_schemas::schema_registry())
            .in_memory("anon.usda")?;
        let model = stage.define_typed_prim("/Model", "Xform")?.set_kind("component")?;
        stage.define_typed_prim("/Model/Geom", "Xform")?;
        let ball = Sphere::define(&stage, "/Model/Geom/ball")?;
        let hint = [gf::vec3f(-5.0, -5.0, -5.0), gf::vec3f(5.0, 5.0, 5.0)];
        ModelAPI::from_prim_unchecked(model.clone()).set_extents_hint(&[hint], None)?;

        let mut cache = BBoxCache::new(None, [Purpose::Default]).with_extents_hint(true);
        assert_eq!(cache.untransformed_bound(&model)?.range(), range([-5.0; 3], [5.0; 3]));
        assert_eq!(
            cache.untransformed_bound(ball.prim())?.range(),
            range([-1.0; 3], [1.0; 3])
        );
        Ok(())
    }

    /// The models of the vendor assets are bounded by the hints they author.
    #[test]
    fn hint_vendor_assets() -> Result {
        let assets = "../../vendor/usd-wg-assets/full_assets";
        for (file, path) in [
            ("Teapot/Teapot.usd", "/Teapot"),
            ("OpenChessSet/assets/King/King.usd", "/King"),
        ] {
            let stage = usd::Stage::builder()
                .schema_registry(openusd_schemas::schema_registry())
                .open(&format!("{assets}/{file}"))?;
            let prim = stage.prim(sdf::path(path)?)?;
            assert!(prim.is_model()?, "{path}");
            let hint = ModelAPI::from_prim_unchecked(prim.clone())
                .extents_hint_at(None)?
                .expect("a hint");
            let mut cache = BBoxCache::new(None, [Purpose::Default]).with_extents_hint(true);
            assert_eq!(
                cache.untransformed_bound(&prim)?,
                gf::BBox3d::from(gf::Range3d::from(hint[0])),
                "{path}"
            );
        }
        Ok(())
    }

    /// The pawns of the vendor chess set, one prototype placed eight times:
    /// each instance's bound is the prototype's, moved to where the
    /// instance is.
    #[test]
    fn chess_set_instances() -> Result {
        let stage = usd::Stage::builder()
            .schema_registry(openusd_schemas::schema_registry())
            .open("../../vendor/usd-wg-assets/full_assets/OpenChessSet/chess_set.usda")?;
        let pawns = PointInstancer::get(&stage, sdf::path("/ChessSet/Black/Pawns")?)?.expect("an instancer");
        let pawn = stage.prim("/ChessSet/Black/Pawns/Pawn")?;
        let positions = pawns.positions()?.expect("positions");
        let indices: Vec<usize> = (0..positions.len()).collect();
        assert_eq!(indices.len(), 8);

        let mut cache = BBoxCache::new(None, [Purpose::Default, Purpose::Render]);
        let prototype = cache.untransformed_bound(&pawn)?;
        assert!(!prototype.range().is_empty());

        // In the instancer's space an instance is its prototype, under the
        // prototype's own transform, moved by the instance's position.
        let mut xforms = XformCache::default();
        let own = cache.point_instance_untransformed_bounds(&pawns, &indices)?;
        for (found, position) in own.iter().zip(&positions) {
            let mut expected = prototype;
            expected.transform(xforms.local_transform(&pawn)?.0 * gf::Mat4d::translation(gf::Vec3d::from(*position)));
            assert_range(found.aligned_range(), expected.aligned_range());
        }

        // The other spaces place those boxes as they place the instancer.
        let world = cache.point_instance_world_bounds(&pawns, &indices)?;
        let local = cache.point_instance_local_bounds(&pawns, &indices)?;
        let board = stage.prim("/ChessSet")?;
        let relative = cache.point_instance_relative_bounds(&pawns, &indices, &board)?;
        let ctm = xforms.local_to_world_transform(pawns.prim())?;
        let to_board = ctm * xforms.local_to_world_transform(&board)?.inverse().expect("an inverse");
        for (index, own) in own.iter().enumerate() {
            let placed = |matrix: gf::Mat4d| {
                let mut bbox = *own;
                bbox.transform(matrix);
                bbox.aligned_range()
            };
            assert_range(world[index].aligned_range(), placed(ctm));
            assert_range(
                local[index].aligned_range(),
                placed(xforms.local_transform(pawns.prim())?.0),
            );
            assert_range(relative[index].aligned_range(), placed(to_board));
        }
        Ok(())
    }
}
