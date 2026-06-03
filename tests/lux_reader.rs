//! Integration tests for the UsdLux schema views, exercised against the
//! `usdLux_scene.usda` fixture plus a few small in-memory stages: every
//! concrete light, the `Light` interface inputs, and the `ShapingAPI` /
//! `ShadowAPI` / `LightListAPI` / `LightAPI` applied schemas.

use anyhow::Result;
use openusd::schemas::lux::{
    CylinderLight, DiskLight, DistantLight, DomeLight, GeometryLight, Light, LightAPI, LightListAPI,
    LightListCacheBehavior, PortalLight, RectLight, ShadowAPI, ShapingAPI, SphereLight, TextureFormat,
};
use openusd::sdf;
use openusd::usd::Stage;

const FIXTURE: &str = "fixtures/usdLux_scene.usda";

fn open() -> Result<Stage> {
    Stage::open(FIXTURE)
}

/// Open an in-memory stage from `usda` source for the API / animation tests.
fn from_usda(usda: &str) -> Result<Stage> {
    let dir = tempfile::tempdir()?;
    let path = dir.path().join("scene.usda");
    std::fs::write(&path, usda)?;
    // Leak the tempdir so it outlives the stage; the process exits at test
    // end, so the OS reclaims it.
    std::mem::forget(dir);
    Stage::open(path.to_str().unwrap())
}

#[test]
fn distant_light_inputs_and_angle() -> Result<()> {
    let stage = open()?;
    let sun = DistantLight::get(&stage, sdf::path("/World/Sun")?)?.expect("DistantLight");
    // `get::<T>()` decodes straight to the Rust type instead of matching on
    // `sdf::Value`.
    assert_eq!(sun.intensity_attr().get::<f32>()?, Some(12000.0));
    assert_eq!(sun.exposure_attr().get::<f32>()?, Some(1.5));
    assert_eq!(sun.color_attr().get::<[f32; 3]>()?, Some([1.0, 0.95, 0.85]));
    assert_eq!(sun.enable_color_temperature_attr().get::<bool>()?, Some(true));
    assert_eq!(sun.color_temperature_attr().get::<f32>()?, Some(5500.0));
    // `get::<sdf::Value>()` still yields the raw value when that's wanted.
    assert_eq!(sun.angle_attr().get::<sdf::Value>()?, Some(sdf::Value::Float(0.53)));
    Ok(())
}

#[test]
fn distant_light_unauthored_intensity_is_none() -> Result<()> {
    // No schema registry yet, so DistantLight's documented 50000 fallback is
    // not synthesized — an unauthored input reads back `None`.
    let stage = from_usda("#usda 1.0\ndef DistantLight \"Bare\" {}\n")?;
    let bare = DistantLight::get(&stage, sdf::path("/Bare")?)?.expect("DistantLight");
    assert_eq!(bare.intensity_attr().get::<sdf::Value>()?, None);
    Ok(())
}

#[test]
fn sphere_light_radius_and_treat_as_point() -> Result<()> {
    let stage = open()?;
    let s = SphereLight::get(&stage, sdf::path("/World/Sphere")?)?.expect("SphereLight");
    assert_eq!(s.radius_attr().get()?, Some(sdf::Value::Float(0.25)));
    assert_eq!(s.treat_as_point_attr().get()?, Some(sdf::Value::Bool(true)));
    assert_eq!(s.intensity_attr().get()?, Some(sdf::Value::Float(800.0)));
    Ok(())
}

#[test]
fn rect_light_with_shaping_and_shadow() -> Result<()> {
    let stage = open()?;
    let prim = sdf::path("/World/Rect")?;

    let rect = RectLight::get(&stage, &prim)?.expect("RectLight");
    assert_eq!(rect.width_attr().get()?, Some(sdf::Value::Float(2.0)));
    assert_eq!(rect.height_attr().get()?, Some(sdf::Value::Float(1.0)));
    assert_eq!(
        rect.texture_file_attr().get()?,
        Some(sdf::Value::AssetPath("./textures/softbox.exr".into()))
    );

    let shaping = ShapingAPI::get(&stage, &prim)?.expect("ShapingAPI");
    assert_eq!(shaping.cone_angle_attr().get()?, Some(sdf::Value::Float(45.0)));
    assert_eq!(shaping.cone_softness_attr().get()?, Some(sdf::Value::Float(0.2)));
    assert_eq!(
        shaping.ies_file_attr().get()?,
        Some(sdf::Value::AssetPath("./ies/profile.ies".into()))
    );
    assert_eq!(shaping.ies_normalize_attr().get()?, Some(sdf::Value::Bool(true)));

    let shadow = ShadowAPI::get(&stage, &prim)?.expect("ShadowAPI");
    assert_eq!(shadow.enable_attr().get()?, Some(sdf::Value::Bool(true)));
    assert_eq!(shadow.distance_attr().get()?, Some(sdf::Value::Float(10.0)));
    assert_eq!(shadow.falloff_attr().get()?, Some(sdf::Value::Float(2.0)));
    Ok(())
}

#[test]
fn shaping_and_shadow_absent_on_non_applied_prims() -> Result<()> {
    let stage = open()?;
    let prim = sdf::path("/World/Sphere")?;
    assert!(ShapingAPI::get(&stage, &prim)?.is_none());
    assert!(ShadowAPI::get(&stage, &prim)?.is_none());
    Ok(())
}

#[test]
fn disk_and_cylinder_lights() -> Result<()> {
    let stage = open()?;

    let disk = DiskLight::get(&stage, sdf::path("/World/Disk")?)?.expect("DiskLight");
    assert_eq!(disk.radius_attr().get()?, Some(sdf::Value::Float(0.75)));

    let tube = CylinderLight::get(&stage, sdf::path("/World/Tube")?)?.expect("CylinderLight");
    assert_eq!(tube.length_attr().get()?, Some(sdf::Value::Float(3.0)));
    assert_eq!(tube.radius_attr().get()?, Some(sdf::Value::Float(0.05)));
    assert_eq!(tube.treat_as_line_attr().get()?, Some(sdf::Value::Bool(true)));
    Ok(())
}

#[test]
fn dome_light_texture_format_and_portals() -> Result<()> {
    let stage = open()?;
    let dome = DomeLight::get(&stage, sdf::path("/World/Dome")?)?.expect("DomeLight");
    assert_eq!(
        dome.texture_file_attr().get()?,
        Some(sdf::Value::AssetPath("./hdri/studio.hdr".into()))
    );
    assert_eq!(
        dome.texture_format_attr()
            .get::<String>()?
            .as_deref()
            .and_then(TextureFormat::from_token),
        Some(TextureFormat::Latlong)
    );
    assert_eq!(dome.guide_radius_attr().get()?, Some(sdf::Value::Float(50.0)));
    assert_eq!(
        dome.portals_rel().get_targets()?,
        vec![sdf::path("/World/Dome/Portal")?]
    );
    Ok(())
}

#[test]
fn portal_light_dimensions() -> Result<()> {
    let stage = open()?;
    let portal = PortalLight::get(&stage, sdf::path("/World/Dome/Portal")?)?.expect("PortalLight");
    assert_eq!(portal.width_attr().get()?, Some(sdf::Value::Float(1.2)));
    assert_eq!(portal.height_attr().get()?, Some(sdf::Value::Float(2.4)));
    Ok(())
}

#[test]
fn geometry_light_target() -> Result<()> {
    let stage = open()?;
    let g = GeometryLight::get(&stage, sdf::path("/World/MeshLight")?)?.expect("GeometryLight");
    assert_eq!(g.geometry_rel().get_targets()?, vec![sdf::path("/World/Emitter")?]);
    assert_eq!(g.intensity_attr().get()?, Some(sdf::Value::Float(200.0)));
    Ok(())
}

#[test]
fn get_rejects_wrong_type() -> Result<()> {
    let stage = open()?;
    // /World/Emitter is a Mesh, not a light.
    assert!(DistantLight::get(&stage, sdf::path("/World/Emitter")?)?.is_none());
    assert!(SphereLight::get(&stage, sdf::path("/World/Sun")?)?.is_none());
    Ok(())
}

#[test]
fn light_list_api() -> Result<()> {
    let stage = open()?;
    let list = LightListAPI::get(&stage, sdf::path("/World")?)?.expect("LightListAPI");
    assert_eq!(
        list.cache_behavior_attr()
            .get::<String>()?
            .as_deref()
            .and_then(LightListCacheBehavior::from_token),
        Some(LightListCacheBehavior::ConsumeAndContinue)
    );
    let lights = list.light_list_rel().get_targets()?;
    assert!(lights.contains(&sdf::path("/World/Sun")?));
    assert!(lights.contains(&sdf::path("/World/Dome/Portal")?));
    Ok(())
}

#[test]
fn light_api_skips_non_light() -> Result<()> {
    // /World is an Xform with LightListAPI applied — neither a light type nor
    // LightAPI. LightAPI::get must return None.
    let stage = open()?;
    assert!(LightAPI::get(&stage, sdf::path("/World")?)?.is_none());
    Ok(())
}

#[test]
fn light_api_via_applied_schema() -> Result<()> {
    // A Mesh with LightAPI prepended into apiSchemas is a valid emissive
    // surface — LightAPI::get must surface it.
    let stage = from_usda(
        "#usda 1.0\ndef Mesh \"Panel\" (\n  prepend apiSchemas = [\"LightAPI\"]\n) {\n  float inputs:intensity = 750\n}\n",
    )?;
    let light = LightAPI::get(&stage, sdf::path("/Panel")?)?.expect("LightAPI applied to Mesh");
    assert_eq!(light.intensity_attr().get()?, Some(sdf::Value::Float(750.0)));
    Ok(())
}

#[test]
fn light_api_mesh_and_volume() -> Result<()> {
    let stage = from_usda(concat!(
        "#usda 1.0\n",
        "def Mesh \"Panel\" (\n  prepend apiSchemas = [\"MeshLightAPI\"]\n) {\n  float inputs:intensity = 321\n}\n",
        "def Volume \"Fog\" (\n  prepend apiSchemas = [\"VolumeLightAPI\"]\n) {\n  float inputs:intensity = 123\n}\n",
    ))?;

    let panel = LightAPI::get(&stage, sdf::path("/Panel")?)?.expect("MeshLightAPI");
    assert_eq!(panel.intensity_attr().get()?, Some(sdf::Value::Float(321.0)));
    let fog = LightAPI::get(&stage, sdf::path("/Fog")?)?.expect("VolumeLightAPI");
    assert_eq!(fog.intensity_attr().get()?, Some(sdf::Value::Float(123.0)));
    Ok(())
}

#[test]
fn animated_intensity_via_get_at() -> Result<()> {
    let stage = from_usda(concat!(
        "#usda 1.0\n",
        "def SphereLight \"Flicker\" {\n",
        "  float inputs:intensity.timeSamples = {\n    0: 100.0,\n    10: 1000.0,\n  }\n",
        "}\n",
    ))?;
    let light = SphereLight::get(&stage, sdf::path("/Flicker")?)?.expect("SphereLight");
    // Default-time read ignores timeSamples → None (no authored default).
    assert_eq!(light.intensity_attr().get::<sdf::Value>()?, None);
    // At-time reads pick / interpolate the samples (stage default is linear).
    // The unsuffixed sample literals parse as `double`.
    assert_eq!(light.intensity_attr().get_at(0.0)?, Some(sdf::Value::Double(100.0)));
    assert_eq!(light.intensity_attr().get_at(10.0)?, Some(sdf::Value::Double(1000.0)));
    assert_eq!(light.intensity_attr().get_at(5.0)?, Some(sdf::Value::Double(550.0)));
    Ok(())
}

#[test]
fn token_round_trips() {
    assert_eq!(TextureFormat::default(), TextureFormat::Automatic);
    assert_eq!(TextureFormat::Latlong.as_token(), "latlong");
    assert_eq!(TextureFormat::from_token("angular"), Some(TextureFormat::Angular));
    assert_eq!(TextureFormat::from_token("bogus"), None);

    assert_eq!(
        LightListCacheBehavior::default(),
        LightListCacheBehavior::ConsumeAndContinue
    );
    assert_eq!(
        LightListCacheBehavior::from_token("ignore"),
        Some(LightListCacheBehavior::Ignore)
    );
}
