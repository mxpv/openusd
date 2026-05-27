//! Integration tests for the [`openusd::schemas::lux`] reader.
//!
//! Exercises every concrete light prim plus the three applied APIs
//! (`ShapingAPI`, `ShadowAPI`, `LightListAPI`) against a fixture that
//! authors representative values for each.

use anyhow::Result;
use openusd::schemas::lux::{
    self, find_lux_prims, is_light_type, read_cylinder_light, read_disk_light, read_distant_light, read_dome_light,
    read_geometry_light, read_light, read_light_api, read_light_list, read_portal_light, read_rect_light, read_shadow,
    read_shaping, read_sphere_light, read_sphere_light_at, LightListCacheBehavior, ReadAnyLight, TextureFormat,
};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdLux_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

#[test]
fn finds_every_lux_prim_family() -> Result<()> {
    let stage = open()?;
    let prims = find_lux_prims(&stage)?;

    assert_eq!(prims.distant, vec!["/World/Sun".to_string()]);
    assert_eq!(prims.sphere, vec!["/World/Sphere".to_string()]);
    assert_eq!(prims.rect, vec!["/World/Rect".to_string()]);
    assert_eq!(prims.disk, vec!["/World/Disk".to_string()]);
    assert_eq!(prims.cylinder, vec!["/World/Tube".to_string()]);
    assert_eq!(prims.dome, vec!["/World/Dome".to_string()]);
    assert_eq!(prims.geometry, vec!["/World/MeshLight".to_string()]);
    assert_eq!(prims.portal, vec!["/World/Dome/Portal".to_string()]);

    assert!(prims.shaping.contains(&"/World/Rect".to_string()));
    assert!(prims.shadow.contains(&"/World/Rect".to_string()));
    assert!(prims.light_list.contains(&"/World".to_string()));
    Ok(())
}

#[test]
fn distant_light_overrides_intensity_default() -> Result<()> {
    let stage = open()?;
    let sun = read_distant_light(&stage, &sdf::path("/World/Sun")?)?.expect("DistantLight");
    assert_eq!(sun.common.path, "/World/Sun");
    assert!((sun.common.intensity - 12000.0).abs() < 1e-3);
    assert!((sun.common.exposure - 1.5).abs() < 1e-3);
    assert!((sun.angle_deg - 0.53).abs() < 1e-3);
    assert!(sun.common.enable_color_temperature);
    assert!((sun.common.color_temperature - 5500.0).abs() < 1e-3);
    Ok(())
}

#[test]
fn distant_light_unauthored_intensity_falls_back_to_50000() -> Result<()> {
    // Stand up a tiny in-memory stage with no authored intensity to
    // make sure the DistantLight-specific default override fires.
    let usda = r#"#usda 1.0
        def DistantLight "Bare" {}
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("bare.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let light = read_distant_light(&stage, &sdf::path("/Bare")?)?.expect("DistantLight");
    assert!((light.common.intensity - 50000.0).abs() < 1e-3);
    assert!((light.angle_deg - 0.53).abs() < 1e-3);
    Ok(())
}

#[test]
fn reads_sphere_light_with_treat_as_point() -> Result<()> {
    let stage = open()?;
    let light = read_sphere_light(&stage, &sdf::path("/World/Sphere")?)?.expect("SphereLight");
    assert!((light.radius - 0.25).abs() < 1e-3);
    assert!(light.treat_as_point);
    assert!((light.common.intensity - 800.0).abs() < 1e-3);
    Ok(())
}

#[test]
fn reads_rect_light_with_shaping_and_shadow_apis() -> Result<()> {
    let stage = open()?;
    let prim = sdf::path("/World/Rect")?;

    let rect = read_rect_light(&stage, &prim)?.expect("RectLight");
    assert!((rect.width - 2.0).abs() < 1e-3);
    assert!((rect.height - 1.0).abs() < 1e-3);
    assert_eq!(rect.texture_file.as_deref(), Some("./textures/softbox.exr"));

    let shaping = read_shaping(&stage, &prim)?.expect("ShapingAPI");
    assert!((shaping.cone_angle_deg - 45.0).abs() < 1e-3);
    assert!((shaping.cone_softness - 0.2).abs() < 1e-3);
    assert_eq!(shaping.ies_file.as_deref(), Some("./ies/profile.ies"));
    assert!(shaping.ies_normalize);

    let shadow = read_shadow(&stage, &prim)?.expect("ShadowAPI");
    assert!(shadow.enable);
    assert!((shadow.distance - 10.0).abs() < 1e-3);
    assert!((shadow.falloff - 2.0).abs() < 1e-3);
    Ok(())
}

#[test]
fn shaping_and_shadow_absent_on_non_applied_prims() -> Result<()> {
    let stage = open()?;
    let prim = sdf::path("/World/Sphere")?;
    assert!(read_shaping(&stage, &prim)?.is_none());
    assert!(read_shadow(&stage, &prim)?.is_none());
    Ok(())
}

#[test]
fn reads_disk_and_cylinder_lights() -> Result<()> {
    let stage = open()?;

    let disk = read_disk_light(&stage, &sdf::path("/World/Disk")?)?.expect("DiskLight");
    assert!((disk.radius - 0.75).abs() < 1e-3);

    let tube = read_cylinder_light(&stage, &sdf::path("/World/Tube")?)?.expect("CylinderLight");
    assert!((tube.length - 3.0).abs() < 1e-3);
    assert!((tube.radius - 0.05).abs() < 1e-3);
    assert!(tube.treat_as_line);
    Ok(())
}

#[test]
fn reads_dome_light_with_portals_and_format() -> Result<()> {
    let stage = open()?;
    let dome = read_dome_light(&stage, &sdf::path("/World/Dome")?)?.expect("DomeLight");
    assert_eq!(dome.texture_file.as_deref(), Some("./hdri/studio.hdr"));
    assert_eq!(dome.texture_format, TextureFormat::Latlong);
    assert!((dome.guide_radius - 50.0).abs() < 1e-3);
    assert_eq!(dome.portals, vec!["/World/Dome/Portal".to_string()]);
    Ok(())
}

#[test]
fn reads_portal_light_dimensions() -> Result<()> {
    let stage = open()?;
    let portal = read_portal_light(&stage, &sdf::path("/World/Dome/Portal")?)?.expect("PortalLight");
    assert!((portal.width - 1.2).abs() < 1e-3);
    assert!((portal.height - 2.4).abs() < 1e-3);
    Ok(())
}

#[test]
fn reads_geometry_light_target() -> Result<()> {
    let stage = open()?;
    let g = read_geometry_light(&stage, &sdf::path("/World/MeshLight")?)?.expect("GeometryLight");
    assert_eq!(g.geometry.as_deref(), Some("/World/Emitter"));
    Ok(())
}

#[test]
fn reads_light_list_api() -> Result<()> {
    let stage = open()?;
    let list = read_light_list(&stage, &sdf::path("/World")?)?.expect("LightListAPI");
    assert_eq!(list.cache_behavior, LightListCacheBehavior::ConsumeAndContinue);
    assert!(list.lights.contains(&"/World/Sun".to_string()));
    assert!(list.lights.contains(&"/World/Dome/Portal".to_string()));
    Ok(())
}

#[test]
fn dispatch_reader_returns_correct_variant() -> Result<()> {
    let stage = open()?;
    match read_light(&stage, &sdf::path("/World/Sun")?)? {
        Some(ReadAnyLight::Distant(_)) => {}
        other => panic!("expected Distant, got {other:?}"),
    }
    match read_light(&stage, &sdf::path("/World/Dome")?)? {
        Some(ReadAnyLight::Dome(_)) => {}
        other => panic!("expected Dome, got {other:?}"),
    }
    Ok(())
}

#[test]
fn dispatch_reader_skips_non_lights() -> Result<()> {
    let stage = open()?;
    assert!(read_light(&stage, &sdf::path("/World/Emitter")?)?.is_none());
    assert!(read_light(&stage, &sdf::path("/World")?)?.is_none());
    Ok(())
}

#[test]
fn is_light_type_matches_every_concrete_type() {
    let types = [
        "DistantLight",
        "SphereLight",
        "RectLight",
        "DiskLight",
        "CylinderLight",
        "DomeLight",
        "DomeLight_1",
        "GeometryLight",
        "PortalLight",
    ];
    for t in types {
        assert!(is_light_type(t), "{t} should be a light type");
    }
    assert!(!is_light_type("Mesh"));
    assert!(!is_light_type("Xform"));
}

#[test]
fn defaults_are_pixar_correct_for_unauthored_attrs() -> Result<()> {
    // A sphere light with only intensity authored — everything else
    // must fall back to Pixar's documented defaults.
    let usda = r#"#usda 1.0
        def SphereLight "Bulb" {
            float inputs:intensity = 1000
        }
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("bare_sphere.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let light = read_sphere_light(&stage, &sdf::path("/Bulb")?)?.expect("SphereLight");

    assert!((light.common.intensity - 1000.0).abs() < 1e-3);
    assert!((light.common.exposure - 0.0).abs() < 1e-6);
    assert!((light.common.diffuse - 1.0).abs() < 1e-6);
    assert!((light.common.specular - 1.0).abs() < 1e-6);
    assert!(!light.common.normalize);
    assert_eq!(light.common.color, [1.0, 1.0, 1.0]);
    assert!(!light.common.enable_color_temperature);
    assert!((light.common.color_temperature - 6500.0).abs() < 1e-3);
    assert!((light.radius - 0.5).abs() < 1e-6);
    assert!(!light.treat_as_point);
    Ok(())
}

#[test]
fn shaping_defaults_match_pixar() -> Result<()> {
    let usda = r#"#usda 1.0
        def RectLight "Plain" (
            prepend apiSchemas = ["ShapingAPI"]
        ) {}
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("plain_rect.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let s = lux::read_shaping(&stage, &sdf::path("/Plain")?)?.expect("ShapingAPI");

    assert!((s.focus - 0.0).abs() < 1e-6);
    assert_eq!(s.focus_tint, [0.0, 0.0, 0.0]);
    assert!((s.cone_angle_deg - 90.0).abs() < 1e-6);
    assert!((s.cone_softness - 0.0).abs() < 1e-6);
    assert!((s.ies_angle_scale - 0.0).abs() < 1e-6);
    assert!(!s.ies_normalize);
    Ok(())
}

#[test]
fn rect_light_unauthored_dimensions_fall_back_to_one() -> Result<()> {
    // Same contract as ReadRectLight::default().
    let usda = r#"#usda 1.0
        def RectLight "Plain" {}
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("plain_rect.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let light = lux::read_rect_light(&stage, &sdf::path("/Plain")?)?.expect("RectLight");

    let defaults = lux::ReadRectLight::default();
    assert!((defaults.width - 1.0).abs() < 1e-6);
    assert!((defaults.height - 1.0).abs() < 1e-6);
    assert!((light.width - 1.0).abs() < 1e-6);
    assert!((light.height - 1.0).abs() < 1e-6);
    assert!(light.texture_file.is_none());
    Ok(())
}

#[test]
fn portal_light_unauthored_dimensions_fall_back_to_one() -> Result<()> {
    let usda = r#"#usda 1.0
        def PortalLight "Plain" {}
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("plain_portal.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let light = lux::read_portal_light(&stage, &sdf::path("/Plain")?)?.expect("PortalLight");

    let defaults = lux::ReadPortalLight::default();
    assert!((defaults.width - 1.0).abs() < 1e-6);
    assert!((defaults.height - 1.0).abs() < 1e-6);
    assert!((light.width - 1.0).abs() < 1e-6);
    assert!((light.height - 1.0).abs() < 1e-6);
    Ok(())
}

#[test]
fn light_api_skips_non_light() -> Result<()> {
    // /World is an Xform with LightListAPI applied — neither a light
    // type nor LightAPI. read_light_api must return None rather than
    // fabricate a fully-defaulted ReadLight from an arbitrary prim.
    let stage = open()?;
    let outcome = read_light_api(&stage, &sdf::path("/World")?)?;
    assert!(outcome.is_none(), "expected None for non-light prim, got {outcome:?}");
    Ok(())
}

#[test]
fn light_api_via_concrete_type() -> Result<()> {
    // A bare SphereLight authors LightAPI implicitly via its typename.
    // read_light_api must see it and return populated defaults.
    let usda = r#"#usda 1.0
        def SphereLight "Bare" {}
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("bare.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let light = read_light_api(&stage, &sdf::path("/Bare")?)?.expect("LightAPI on SphereLight");
    assert_eq!(light.path, "/Bare");
    assert!((light.intensity - 1.0).abs() < 1e-6);
    Ok(())
}

#[test]
fn light_api_distant_default() -> Result<()> {
    let usda = r#"#usda 1.0
        def DistantLight "Bare" {}
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("bare_distant.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let light = read_light_api(&stage, &sdf::path("/Bare")?)?.expect("LightAPI on DistantLight");
    assert_eq!(light.path, "/Bare");
    assert!((light.intensity - 50000.0).abs() < 1e-3);
    Ok(())
}

#[test]
fn animated_intensity() -> Result<()> {
    // Light with only timeSamples authored (no default field).
    // read_sphere_light (default-time) must fall back to the spec
    // default — current Pixar Get(value) semantics. read_sphere_light_at
    // must interpolate the samples.
    let usda = r#"#usda 1.0
        def SphereLight "Flicker"
        {
            float inputs:intensity.timeSamples = {
                0: 100.0,
                10: 1000.0,
            }
        }
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("flicker.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;

    // Default-time read ignores timeSamples → LightAPI's 1.0 default.
    let still = read_sphere_light(&stage, &sdf::path("/Flicker")?)?.expect("SphereLight");
    assert!((still.common.intensity - 1.0).abs() < 1e-6);

    // At-time read picks the authored samples.
    let t0 = read_sphere_light_at(&stage, &sdf::path("/Flicker")?, 0.0)?.expect("SphereLight @ 0");
    assert!((t0.common.intensity - 100.0).abs() < 1e-3);
    let t10 = read_sphere_light_at(&stage, &sdf::path("/Flicker")?, 10.0)?.expect("SphereLight @ 10");
    assert!((t10.common.intensity - 1000.0).abs() < 1e-3);
    // Midpoint interpolates linearly (stage default).
    let t5 = read_sphere_light_at(&stage, &sdf::path("/Flicker")?, 5.0)?.expect("SphereLight @ 5");
    assert!((t5.common.intensity - 550.0).abs() < 1e-3);
    Ok(())
}

#[test]
fn emissive_mesh_bucket() -> Result<()> {
    let usda = r#"#usda 1.0
        def Mesh "Emissive" (
            prepend apiSchemas = ["LightAPI"]
        ) {}
        def Mesh "Plain" {}
        def SphereLight "Bulb" {}
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("emissive.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let prims = find_lux_prims(&stage)?;
    // Emissive mesh lands in the light_api bucket, NOT in `sphere`.
    assert_eq!(prims.light_api, vec!["/Emissive".to_string()]);
    // Concrete SphereLight stays in its own bucket (and does NOT
    // double-bucket into light_api).
    assert_eq!(prims.sphere, vec!["/Bulb".to_string()]);
    assert!(!prims.light_api.contains(&"/Bulb".to_string()));
    Ok(())
}

#[test]
fn light_api_via_applied_schema() -> Result<()> {
    // A Mesh with LightAPI prepended into apiSchemas is a valid
    // emissive surface — read_light_api must surface it as a light.
    let usda = r#"#usda 1.0
        def Mesh "EmissivePanel" (
            prepend apiSchemas = ["LightAPI"]
        ) {
            float inputs:intensity = 750
        }
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("emissive.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;
    let light = read_light_api(&stage, &sdf::path("/EmissivePanel")?)?.expect("LightAPI applied to Mesh");
    assert!((light.intensity - 750.0).abs() < 1e-3);
    Ok(())
}

#[test]
fn light_api_mesh_and_volume() -> Result<()> {
    let usda = r#"#usda 1.0
        def Mesh "Panel" (
            prepend apiSchemas = ["MeshLightAPI"]
        ) {
            float inputs:intensity = 321
        }

        def Volume "Fog" (
            prepend apiSchemas = ["VolumeLightAPI"]
        ) {
            float inputs:intensity = 123
        }
        "#;
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("mesh_volume_light_api.usda");
    std::fs::write(&path, usda)?;
    let stage = Stage::open(path.to_str().unwrap())?;

    let prims = find_lux_prims(&stage)?;
    assert!(prims.light_api.contains(&"/Panel".to_string()));
    assert!(prims.light_api.contains(&"/Fog".to_string()));

    let panel = read_light_api(&stage, &sdf::path("/Panel")?)?.expect("MeshLightAPI");
    assert!((panel.intensity - 321.0).abs() < 1e-3);

    let fog = read_light_api(&stage, &sdf::path("/Fog")?)?.expect("VolumeLightAPI");
    assert!((fog.intensity - 123.0).abs() < 1e-3);
    Ok(())
}
