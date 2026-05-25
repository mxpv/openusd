//! Integration tests for the UsdGeom module. This file grows as
//! more shape readers land in follow-up commits; today it covers the
//! cross-cutting Imageable / Boundable surface and the
//! `find_geom_prims` walker.

use anyhow::Result;
use openusd::schemas::geom::{
    self, compute_purpose, compute_visibility, find_geom_prims, read_extent, read_kind, read_proxy_prim, read_purpose,
    read_visibility, Purpose, Visibility,
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
    assert_eq!(prims.scopes, vec!["/World/Geometry".to_string()]);
    assert_eq!(prims.cameras, vec!["/World/Cam".to_string()]);
    assert!(prims.meshes.contains(&"/World/Geometry/Hero".to_string()));
    assert!(prims.meshes.contains(&"/World/Geometry/HeroProxy".to_string()));
    assert_eq!(prims.cubes, vec!["/World/Geometry/GuideCube".to_string()]);
    assert!(prims.spheres.contains(&"/World/Geometry/InvisibleBall".to_string()));
    assert!(prims.spheres.contains(&"/World/Hidden/HiddenChild".to_string()));

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
