//! Integration tests for the UsdGeom module. This file grows as
//! more shape readers land in follow-up commits; today it covers the
//! cross-cutting Imageable / Boundable surface and the
//! `find_geom_prims` walker.

use anyhow::Result;
use openusd::math::{mat4_transform_point, IDENTITY_MAT4};
use openusd::schemas::geom::{
    self, compute_local_to_parent_transform, compute_purpose, compute_visibility, find_geom_prims, read_camera,
    read_capsule, read_cone, read_cube, read_cylinder, read_extent, read_kind, read_plane, read_proxy_prim,
    read_purpose, read_sphere, read_visibility, read_xform_op_order, resets_xform_stack, Axis, Projection, Purpose,
    StereoRole, Visibility,
};
use openusd::sdf;
use openusd::Stage;

const FIXTURE: &str = "fixtures/usdGeom_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

#[test]
fn defaults_when_visibility_unauthored() -> Result<()> {
    let stage = open()?;
    assert_eq!(
        read_visibility(&stage, &sdf::path("/World/Geometry/Hero")?)?,
        Visibility::Inherited
    );
    Ok(())
}

#[test]
fn reads_authored_visibility() -> Result<()> {
    let stage = open()?;
    assert_eq!(
        read_visibility(&stage, &sdf::path("/World/Geometry/InvisibleBall")?)?,
        Visibility::Invisible
    );
    Ok(())
}

#[test]
fn compute_visibility_inherits_invisible_from_ancestor() -> Result<()> {
    let stage = open()?;
    // HiddenChild has no authored visibility, but /World/Hidden is
    // invisible — so the composed visibility should be Invisible.
    assert_eq!(
        compute_visibility(&stage, &sdf::path("/World/Hidden/HiddenChild")?)?,
        Visibility::Invisible
    );
    // Hero is not under any invisible ancestor.
    assert_eq!(
        compute_visibility(&stage, &sdf::path("/World/Geometry/Hero")?)?,
        Visibility::Inherited
    );
    Ok(())
}

#[test]
fn reads_authored_purpose() -> Result<()> {
    let stage = open()?;
    assert_eq!(
        read_purpose(&stage, &sdf::path("/World/Geometry/Hero")?)?,
        Purpose::Render
    );
    assert_eq!(
        read_purpose(&stage, &sdf::path("/World/Geometry/HeroProxy")?)?,
        Purpose::Proxy
    );
    assert_eq!(
        read_purpose(&stage, &sdf::path("/World/Geometry/GuideCube")?)?,
        Purpose::Guide
    );
    Ok(())
}

#[test]
fn default_purpose_is_default() -> Result<()> {
    let stage = open()?;
    assert_eq!(read_purpose(&stage, &sdf::path("/World/Cam")?)?, Purpose::Default);
    Ok(())
}

#[test]
fn compute_purpose_walks_ancestors() -> Result<()> {
    let stage = open()?;
    // HeroProxy authors its own purpose — no inheritance needed.
    assert_eq!(
        compute_purpose(&stage, &sdf::path("/World/Geometry/HeroProxy")?)?,
        Purpose::Proxy
    );
    // Cam authors nothing → default fallback.
    assert_eq!(compute_purpose(&stage, &sdf::path("/World/Cam")?)?, Purpose::Default);
    Ok(())
}

#[test]
fn reads_extent_when_authored() -> Result<()> {
    let stage = open()?;
    let extent = read_extent(&stage, &sdf::path("/World/Geometry/Hero")?)?.expect("extent authored");
    assert_eq!(extent, [[-1.0, -1.0, -1.0], [1.0, 1.0, 1.0]]);
    Ok(())
}

#[test]
fn extent_unauthored_returns_none() -> Result<()> {
    let stage = open()?;
    assert!(read_extent(&stage, &sdf::path("/World/Cam")?)?.is_none());
    Ok(())
}

#[test]
fn reads_proxy_prim_rel() -> Result<()> {
    let stage = open()?;
    assert_eq!(
        read_proxy_prim(&stage, &sdf::path("/World/Geometry/Hero")?)?.as_deref(),
        Some("/World/Geometry/HeroProxy")
    );
    Ok(())
}

#[test]
fn reads_kind_metadata() -> Result<()> {
    let stage = open()?;
    assert_eq!(read_kind(&stage, &sdf::path("/World")?)?.as_deref(), Some("assembly"));
    assert_eq!(
        read_kind(&stage, &sdf::path("/World/Geometry/Hero")?)?.as_deref(),
        Some("component")
    );
    assert!(read_kind(&stage, &sdf::path("/World/Cam")?)?.is_none());
    Ok(())
}

#[test]
fn find_geom_prims_buckets_by_type() -> Result<()> {
    let stage = open()?;
    let prims = find_geom_prims(&stage)?;

    assert!(prims.xforms.contains(&"/World".to_string()));
    assert!(prims.xforms.contains(&"/World/Hidden".to_string()));
    assert!(prims.scopes.contains(&"/World/Geometry".to_string()));
    assert!(prims.scopes.contains(&"/World/Shapes".to_string()));
    assert!(prims.cameras.contains(&"/World/Cam".to_string()));
    assert!(prims.cameras.contains(&"/World/AuthoredCam".to_string()));
    assert!(prims.cameras.contains(&"/World/OrthoCam".to_string()));
    assert!(prims.meshes.contains(&"/World/Geometry/Hero".to_string()));
    assert!(prims.meshes.contains(&"/World/Geometry/HeroProxy".to_string()));
    assert!(prims.cubes.contains(&"/World/Geometry/GuideCube".to_string()));
    assert!(prims.cubes.contains(&"/World/Shapes/AuthoredCube".to_string()));
    assert!(prims.spheres.contains(&"/World/Geometry/InvisibleBall".to_string()));
    assert!(prims.spheres.contains(&"/World/Hidden/HiddenChild".to_string()));
    assert!(prims.spheres.contains(&"/World/Shapes/Ball".to_string()));
    assert!(prims.cylinders.contains(&"/World/Shapes/Pipe".to_string()));
    assert!(prims.capsules.contains(&"/World/Shapes/Pill".to_string()));
    assert!(prims.cones.contains(&"/World/Shapes/Pyramid".to_string()));
    assert!(prims.planes.contains(&"/World/Shapes/Ground".to_string()));

    // Imageables is the superset — every typed prim above lands there.
    for p in [
        "/World",
        "/World/Geometry",
        "/World/Geometry/Hero",
        "/World/Geometry/HeroProxy",
        "/World/Geometry/GuideCube",
        "/World/Geometry/InvisibleBall",
        "/World/Cam",
        "/World/Hidden",
        "/World/Hidden/HiddenChild",
    ] {
        assert!(prims.imageables.iter().any(|q| q == p), "missing {p} in imageables");
    }
    Ok(())
}

// ── Xformable / xformOpOrder ──────────────────────────────────────

#[test]
fn read_xform_op_order_returns_authored_stack() -> Result<()> {
    let stage = open()?;
    let order = read_xform_op_order(&stage, &sdf::path("/World/TRS")?)?.expect("authored");
    assert_eq!(order, vec!["xformOp:translate", "xformOp:rotateY", "xformOp:scale"]);
    Ok(())
}

#[test]
fn xform_op_order_none_when_unauthored() -> Result<()> {
    let stage = open()?;
    assert!(read_xform_op_order(&stage, &sdf::path("/World/Cam")?)?.is_none());
    Ok(())
}

#[test]
fn resets_xform_stack_detects_sentinel() -> Result<()> {
    let stage = open()?;
    assert!(resets_xform_stack(&stage, &sdf::path("/World/Detached")?)?);
    assert!(!resets_xform_stack(&stage, &sdf::path("/World/TRS")?)?);
    Ok(())
}

#[test]
fn unauthored_xform_is_identity() -> Result<()> {
    let stage = open()?;
    let m = compute_local_to_parent_transform(&stage, &sdf::path("/World/Cam")?, 0.0)?;
    assert_eq!(m, IDENTITY_MAT4);
    Ok(())
}

#[test]
fn matrix_op_round_trips_to_authored_matrix() -> Result<()> {
    let stage = open()?;
    let m = compute_local_to_parent_transform(&stage, &sdf::path("/World/MatrixOp")?, 0.0)?;
    assert_eq!(&m[12..15], &[5.0, 6.0, 7.0]);
    Ok(())
}

#[test]
fn invert_prefix_inverts_the_op() -> Result<()> {
    let stage = open()?;
    // Authored translate (4, 0, 0), then !invert! it → translation row (-4, 0, 0).
    let m = compute_local_to_parent_transform(&stage, &sdf::path("/World/Inverted")?, 0.0)?;
    assert_eq!(&m[12..15], &[-4.0, 0.0, 0.0]);
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
    let m = compute_local_to_parent_transform(&stage, &sdf::path("/World/TRS")?, 0.0)?;
    let p = mat4_transform_point(&m, [0.0, 0.0, 0.0]);
    assert!((p[0] - 6.0).abs() < 1e-4, "x: {}", p[0]);
    assert!((p[1] - 4.0).abs() < 1e-4, "y: {}", p[1]);
    assert!((p[2] + 2.0).abs() < 1e-4, "z: {}", p[2]);
    Ok(())
}

// ── Intrinsic shapes ──────────────────────────────────────────────

#[test]
fn read_cube_returns_authored_size() -> Result<()> {
    let stage = open()?;
    let cube = read_cube(&stage, &sdf::path("/World/Shapes/AuthoredCube")?)?.expect("Cube");
    assert_eq!(cube.size, 3.0);
    Ok(())
}

#[test]
fn unauthored_cube_falls_back_to_spec_default() -> Result<()> {
    let stage = open()?;
    let cube = read_cube(&stage, &sdf::path("/World/Shapes/DefaultCube")?)?.expect("Cube");
    assert_eq!(cube.size, 2.0);
    Ok(())
}

#[test]
fn read_cube_returns_none_for_non_cube() -> Result<()> {
    let stage = open()?;
    assert!(read_cube(&stage, &sdf::path("/World/Shapes/Ball")?)?.is_none());
    Ok(())
}

#[test]
fn read_sphere_returns_authored_radius() -> Result<()> {
    let stage = open()?;
    let s = read_sphere(&stage, &sdf::path("/World/Shapes/Ball")?)?.expect("Sphere");
    assert_eq!(s.radius, 4.5);
    Ok(())
}

#[test]
fn read_cylinder_with_y_axis() -> Result<()> {
    let stage = open()?;
    let c = read_cylinder(&stage, &sdf::path("/World/Shapes/Pipe")?)?.expect("Cylinder");
    assert_eq!(c.radius, 0.25);
    assert_eq!(c.height, 2.0);
    assert_eq!(c.axis, Axis::Y);
    Ok(())
}

#[test]
fn read_capsule_with_x_axis() -> Result<()> {
    let stage = open()?;
    let c = read_capsule(&stage, &sdf::path("/World/Shapes/Pill")?)?.expect("Capsule");
    assert_eq!(c.radius, 0.1);
    assert_eq!(c.height, 0.5);
    assert_eq!(c.axis, Axis::X);
    Ok(())
}

#[test]
fn read_cone_defaults_to_z_axis() -> Result<()> {
    let stage = open()?;
    let c = read_cone(&stage, &sdf::path("/World/Shapes/Pyramid")?)?.expect("Cone");
    assert_eq!(c.radius, 1.5);
    assert_eq!(c.height, 4.0);
    assert_eq!(c.axis, Axis::Z); // unauthored → spec default
    Ok(())
}

#[test]
fn read_plane_picks_up_dimensions_and_axis() -> Result<()> {
    let stage = open()?;
    let p = read_plane(&stage, &sdf::path("/World/Shapes/Ground")?)?.expect("Plane");
    assert_eq!(p.width, 10.0);
    assert_eq!(p.length, 8.0);
    assert_eq!(p.axis, Axis::Y);
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
fn read_camera_returns_authored_attrs() -> Result<()> {
    let stage = open()?;
    let c = read_camera(&stage, &sdf::path("/World/AuthoredCam")?)?.expect("Camera");
    assert_eq!(c.focal_length, 35.0);
    assert_eq!(c.horizontal_aperture, 36.0);
    assert_eq!(c.vertical_aperture, 24.0);
    assert_eq!(c.f_stop, 2.8);
    assert_eq!(c.focus_distance, 10.0);
    assert_eq!(c.projection, Projection::Perspective);
    assert_eq!(c.clipping_range, [0.1, 5000.0]);
    assert_eq!(c.shutter_open, -0.25);
    assert_eq!(c.shutter_close, 0.25);
    assert_eq!(c.exposure, 1.5);
    assert_eq!(c.stereo_role, StereoRole::Left);
    Ok(())
}

#[test]
fn unauthored_camera_falls_back_to_spec_defaults() -> Result<()> {
    let stage = open()?;
    // /World/Cam only authors focalLength.
    let c = read_camera(&stage, &sdf::path("/World/Cam")?)?.expect("Camera");
    assert_eq!(c.focal_length, 50.0);
    // Unauthored aperture / projection / stereoRole get Pixar's defaults.
    assert_eq!(c.horizontal_aperture, 20.955);
    assert_eq!(c.vertical_aperture, 15.2908);
    assert_eq!(c.projection, Projection::Perspective);
    assert_eq!(c.clipping_range, [1.0, 1_000_000.0]);
    assert_eq!(c.stereo_role, StereoRole::Mono);
    Ok(())
}

#[test]
fn orthographic_projection_token() -> Result<()> {
    let stage = open()?;
    let c = read_camera(&stage, &sdf::path("/World/OrthoCam")?)?.expect("Camera");
    assert_eq!(c.projection, Projection::Orthographic);
    Ok(())
}

#[test]
fn camera_fov_derives_from_aperture_and_focal_length() {
    // 35 mm focal length, 36 mm horizontal aperture → ~54.4° h-FOV.
    let c = openusd::schemas::geom::ReadCamera {
        focal_length: 35.0,
        horizontal_aperture: 36.0,
        vertical_aperture: 24.0,
        ..Default::default()
    };
    let h = c.horizontal_fov_rad().to_degrees();
    let v = c.vertical_fov_rad().to_degrees();
    assert!((h - 54.43).abs() < 0.05, "horizontal fov: {h}");
    assert!((v - 37.85).abs() < 0.05, "vertical fov: {v}");
    assert!((c.aspect_ratio() - 1.5).abs() < 1e-5);
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
fn read_camera_returns_none_for_non_camera() -> Result<()> {
    let stage = open()?;
    assert!(read_camera(&stage, &sdf::path("/World/Shapes/Ball")?)?.is_none());
    Ok(())
}

#[test]
fn token_round_trip() {
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
