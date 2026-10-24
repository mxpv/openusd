//! Integration tests for the UsdLux schema views, exercised against the
//! `usdLux_scene.usda`, `usdLux_linking` and `usdLux_lightList` fixtures plus
//! a few small in-memory stages: every concrete light, the `Light` interface
//! inputs, the `ShapingAPI` / `ShadowAPI` / `LightListAPI` / `LightAPI`
//! applied schemas, light, shadow and filter linking, and light-list
//! discovery and its cache.

use std::collections::BTreeSet;
use std::ops::Deref;

use openusd::Result;
use openusd::sdf;
use openusd::tf;
use openusd::usd::{self, CollectionAPI, SchemaBase, Stage};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::{self, XformableExt, XformableSchema};
use openusd_schemas::lux::{
    BoundableLightBaseSchema, CylinderLight, CylinderLightSchema, DiskLight, DiskLightSchema, DistantLight,
    DistantLightSchema, DomeLight, DomeLight_1, DomeLight_1Schema, DomeLightSchema, GeometryLight, GeometryLightSchema,
    LightAPI, LightFilter, LightFilterExt, LightFilterSchema, LightList, LightListAPI, LightListCacheBehavior,
    LightListMode, ListAPI, NonboundableLightBaseSchema, PluginLight, PluginLightFilter, PortalLight,
    PortalLightSchema, RectLight, RectLightSchema, ShadowAPI, ShapingAPI, SphereLight, SphereLightSchema,
    TextureFormat,
};
use openusd_schemas::shade::{
    Connectable, ConnectableAPI, ImplementationSource, Input, NodeGraph, NodeGraphInterface, ProducerFilter, Shader,
};

mod common;
use common::from_usda;

const FIXTURE: &str = "fixtures/usdLux_scene.usda";

fn open() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open(FIXTURE)
}

#[test]
fn distant_light_inputs_and_angle() -> Result<()> {
    let stage = open()?;
    let sun = DistantLight::get(&stage, sdf::path("/World/Sun")?)?.expect("DistantLight");
    // `get::<T>()` decodes straight to the Rust type instead of matching on
    // `sdf::Value`.
    assert_eq!(sun.intensity()?, Some(12000.0));
    assert_eq!(sun.exposure()?, Some(1.5));
    assert_eq!(sun.color_attr().get::<[f32; 3]>()?, Some([1.0, 0.95, 0.85]));
    assert_eq!(sun.enable_color_temperature()?, Some(true));
    assert_eq!(sun.color_temperature()?, Some(5500.0));
    // `get::<sdf::Value>()` still yields the raw value when that's wanted.
    assert_eq!(sun.angle_attr().get::<sdf::Value>()?, Some(sdf::Value::Float(0.53)));
    Ok(())
}

#[test]
fn distant_light_unauthored_intensity_falls_back() -> Result<()> {
    // The registry carries the schema data, so an unauthored input reads back
    // the fallback the schema declares.
    let stage = from_usda("#usda 1.0\ndef DistantLight \"Bare\" {}\n")?;
    let bare = DistantLight::get(&stage, sdf::path("/Bare")?)?.expect("DistantLight");
    assert_eq!(bare.intensity_attr().get()?, Some(sdf::Value::Float(50000.0)));
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
    assert_eq!(shaping.shaping_cone_angle_attr().get()?, Some(sdf::Value::Float(45.0)));
    assert_eq!(
        shaping.shaping_cone_softness_attr().get()?,
        Some(sdf::Value::Float(0.2))
    );
    assert_eq!(
        shaping.shaping_ies_file_attr().get()?,
        Some(sdf::Value::AssetPath("./ies/profile.ies".into()))
    );
    assert_eq!(
        shaping.shaping_ies_normalize_attr().get()?,
        Some(sdf::Value::Bool(true))
    );

    let shadow = ShadowAPI::get(&stage, &prim)?.expect("ShadowAPI");
    assert_eq!(shadow.shadow_enable_attr().get()?, Some(sdf::Value::Bool(true)));
    assert_eq!(shadow.shadow_distance_attr().get()?, Some(sdf::Value::Float(10.0)));
    assert_eq!(shadow.shadow_falloff_attr().get()?, Some(sdf::Value::Float(2.0)));
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
            .get::<tf::Token>()?
            .as_deref()
            .and_then(TextureFormat::from_token),
        Some(TextureFormat::Latlong)
    );
    assert_eq!(dome.guide_radius_attr().get()?, Some(sdf::Value::Float(50.0)));
    assert_eq!(dome.portals_rel().targets()?, vec![sdf::path("/World/Dome/Portal")?]);
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
    assert_eq!(g.geometry_rel().targets()?, vec![sdf::path("/World/Emitter")?]);
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
        list.light_list_cache_behavior_attr()
            .get::<tf::Token>()?
            .as_deref()
            .and_then(LightListCacheBehavior::from_token),
        Some(LightListCacheBehavior::ConsumeAndContinue)
    );
    let lights = list.light_list_rel().targets()?;
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
    // A default-time read ignores timeSamples, so it answers the schema's
    // fallback rather than a sample.
    assert_eq!(light.intensity_attr().get()?, Some(sdf::Value::Float(1.0)));
    // At-time reads pick / interpolate the samples (stage default is linear).
    // The samples decode as `float`, the declared type.
    assert_eq!(
        light.intensity_attr().get_at(openusd::usd::TimeCode::new(0.0))?,
        Some(sdf::Value::Float(100.0))
    );
    assert_eq!(
        light.intensity_attr().get_at(openusd::usd::TimeCode::new(10.0))?,
        Some(sdf::Value::Float(1000.0))
    );
    assert_eq!(
        light.intensity_attr().get_at(openusd::usd::TimeCode::new(5.0))?,
        Some(sdf::Value::Float(550.0))
    );
    Ok(())
}

#[test]
fn token_round_trips() {
    assert_eq!(TextureFormat::default(), TextureFormat::Automatic);
    assert_eq!(TextureFormat::Latlong.as_token(), "latlong");
    assert_eq!(TextureFormat::from_token("angular"), Some(TextureFormat::Angular));
    assert_eq!(TextureFormat::from_token("bogus"), None);

    // The schema documents `ignore` as the fallback without declaring one, and
    // C++ `UsdLuxLightListAPI::_Traverse` consults the cache only for the two
    // consuming values, so everything else traverses.
    assert_eq!(LightListCacheBehavior::default(), LightListCacheBehavior::Ignore);
    assert_eq!(
        LightListCacheBehavior::from_token("ignore"),
        Some(LightListCacheBehavior::Ignore)
    );
}

/// An in-memory stage carrying the schema data, which is what makes a prim its
/// type and resolves the fallbacks its schema declares.
fn memory() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .in_memory("anon.usda")
}

#[test]
fn dome_light_and_v1() -> Result<()> {
    let stage = memory()?;
    let d = DomeLight::define(&stage, "/Dome")?;
    d.create_texture_format_attr()?
        .set(sdf::Value::Token("latlong".into()))?;
    d.create_portals_rel()?.set_targets(["/Dome/Portal"])?;
    assert_eq!(
        DomeLight::get(&stage, "/Dome")?
            .expect("DomeLight")
            .texture_format_attr()
            .get()?,
        Some(sdf::Value::Token("latlong".into()))
    );

    // `DomeLight_1` is a schema of its own, not a version of this one: it is
    // what carries `poleAxis`, and the unversioned view does not answer for it.
    let v1 = DomeLight_1::define(&stage, "/Dome1")?;
    v1.create_pole_axis_attr()?.set(sdf::Value::Token("Y".into()))?;
    assert_eq!(
        DomeLight_1::get(&stage, "/Dome1")?
            .expect("DomeLight_1")
            .pole_axis_attr()
            .get()?,
        Some(sdf::Value::Token("Y".into()))
    );
    assert!(DomeLight::get(&stage, "/Dome1")?.is_none(), "a version is its own type");
    Ok(())
}

#[test]
fn geometry_light_links_mesh() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/Emitter")?.set_type_name("Mesh")?;
    let g = GeometryLight::define(&stage, "/Light")?;
    g.create_geometry_rel()?.set_targets(["/Emitter"])?;

    let g = GeometryLight::get(&stage, "/Light")?.expect("GeometryLight");
    assert_eq!(g.geometry_rel().targets()?, vec![sdf::path("/Emitter")?]);
    Ok(())
}

/// `LightAPI` brings two built-in collections, both declared with
/// `includeRoot = 1`, so a light links to everything before anything is
/// authored (C++ `UsdLuxLightAPI::GetLightLinkCollectionAPI`).
#[test]
fn light_links_include_root() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/World/Geo")?.set_type_name("Mesh")?;
    let light = DistantLight::define(&stage, "/World/Sun")?;

    let api = light.light_api();
    for (name, linking) in [
        ("lightLink", api.light_link_collection()),
        ("shadowLink", api.shadow_link_collection()),
    ] {
        assert_eq!(linking.include_root()?, Some(true), "{name} includes the pseudo-root");
        assert!(
            linking.membership_query()?.is_included(&sdf::path("/World/Geo")?),
            "{name} links the geometry"
        );
    }
    Ok(())
}

#[test]
fn light_api_apply_and_get() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/Emitter")?.set_type_name("Mesh")?;
    let light = LightAPI::apply(&stage.prim("/Emitter")?)?;
    light.create_intensity_attr()?.set(1500.0_f32)?;

    assert!(stage.prim("/Emitter")?.api_schemas()?.iter().any(|s| s == "LightAPI"));
    let light = LightAPI::get(&stage, "/Emitter")?.expect("LightAPI");
    assert_eq!(light.intensity_attr().get()?, Some(sdf::Value::Float(1500.0)));
    assert_eq!(LightAPI::KIND, openusd::usd::SchemaKind::SingleApplyApi);
    Ok(())
}

#[test]
fn light_filter_is_typed_xformable() -> Result<()> {
    let stage = memory()?;
    LightFilter::define(&stage, "/Filter")?;
    let f = LightFilter::get(&stage, "/Filter")?.expect("LightFilter");
    // Inherited Xformable accessor is available on the handle.
    assert!(f.xform_op_order()?.is_none());
    assert!(LightFilter::get(&stage, "/Missing")?.is_none());
    Ok(())
}

#[test]
fn light_list_roundtrip() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/World")?.set_type_name("Xform")?;
    let list = LightListAPI::apply(&stage.prim("/World")?)?;
    list.create_light_list_rel()?.set_targets(["/World/Sun"])?;
    list.create_light_list_cache_behavior_attr()?
        .set(sdf::Value::Token("consumeAndContinue".into()))?;

    let list = LightListAPI::get(&stage, "/World")?.expect("LightListAPI");
    assert_eq!(list.light_list_rel().targets()?, vec![sdf::path("/World/Sun")?]);
    assert_eq!(
        list.light_list_cache_behavior_attr().get()?,
        Some(sdf::Value::Token("consumeAndContinue".into()))
    );
    Ok(())
}

#[test]
fn rect_light_texture_and_filters() -> Result<()> {
    let stage = memory()?;
    let r = RectLight::define(&stage, "/Rect")?;
    r.create_width_attr()?.set(2.0_f32)?;
    r.create_texture_file_attr()?
        .set(sdf::Value::AssetPath("./softbox.exr".into()))?;
    r.create_filters_rel()?.set_targets(["/Filter"])?;

    let r = RectLight::get(&stage, "/Rect")?.expect("RectLight");
    assert_eq!(r.width_attr().get()?, Some(sdf::Value::Float(2.0)));
    assert_eq!(r.filters_rel().targets()?, vec![sdf::path("/Filter")?]);
    Ok(())
}

#[test]
fn shaping_and_shadow_roundtrip() -> Result<()> {
    let stage = memory()?;
    stage.define_prim("/Spot")?.set_type_name("RectLight")?;
    ShapingAPI::apply(&stage.prim("/Spot")?)?
        .create_shaping_cone_angle_attr()?
        .set(45.0_f32)?;
    ShadowAPI::apply(&stage.prim("/Spot")?)?
        .create_shadow_distance_attr()?
        .set(10.0_f32)?;

    assert_eq!(
        ShapingAPI::get(&stage, "/Spot")?
            .expect("ShapingAPI")
            .shaping_cone_angle_attr()
            .get()?,
        Some(sdf::Value::Float(45.0))
    );
    assert_eq!(
        ShadowAPI::get(&stage, "/Spot")?
            .expect("ShadowAPI")
            .shadow_distance_attr()
            .get()?,
        Some(sdf::Value::Float(10.0))
    );
    Ok(())
}

#[test]
fn sphere_light_roundtrip() -> Result<()> {
    let stage = memory()?;
    let s = SphereLight::define(&stage, "/Bulb")?;
    s.create_radius_attr()?.set(0.25_f32)?;
    s.create_treat_as_point_attr()?.set(true)?;
    s.create_intensity_attr()?.set(800.0_f32)?;

    let s = SphereLight::get(&stage, "/Bulb")?.expect("SphereLight");
    assert_eq!(s.radius_attr().get()?, Some(sdf::Value::Float(0.25)));
    assert_eq!(s.treat_as_point_attr().get()?, Some(sdf::Value::Bool(true)));
    assert_eq!(s.intensity_attr().get()?, Some(sdf::Value::Float(800.0)));
    assert!(SphereLight::get(&stage, "/Missing")?.is_none());
    Ok(())
}

/// `testUsdLuxLinkingAPI/linking_example.usda`, which links lights and a
/// filter to the geometry under `/Geom`.
fn linking_stage() -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .open("fixtures/usdLux_linking/linking_example.usda")
}

/// Whether the collection includes the prim at `path`.
fn includes(collection: &CollectionAPI, path: &str) -> Result<bool> {
    Ok(collection.membership_query()?.is_included(&sdf::path(path)?))
}

/// `testUsdLuxLinkingAPI.py:test_LinkageQueries`.
#[test]
fn linkage_queries() -> Result<()> {
    let stage = linking_stage()?;
    #[rustfmt::skip]
    let cases = [
        ("/Lights/DefaultLinkage/include_all", "/Geom", true),
        ("/Lights/DefaultLinkage/include_all", "/Geom/a", true),
        ("/Lights/DefaultLinkage/include_all", "/Geom/a/sub_scope", true),
        ("/Lights/SimpleInclude/include_a", "/Geom", false),
        ("/Lights/SimpleInclude/include_a", "/Geom/a", true),
        ("/Lights/SimpleInclude/include_a", "/Geom/a/sub_scope", true),
        ("/Lights/SimpleInclude/include_a", "/Geom/b", false),
        ("/Lights/MultiInclude/include_ab", "/Geom", false),
        ("/Lights/MultiInclude/include_ab", "/Geom/a", true),
        ("/Lights/MultiInclude/include_ab", "/Geom/b", true),
        ("/Lights/SimpleExclude/exclude_a", "/Geom", true),
        ("/Lights/SimpleExclude/exclude_a", "/Geom/a", false),
        ("/Lights/SimpleExclude/exclude_a", "/Geom/a/sub_scope", false),
        ("/Lights/SimpleExclude/exclude_a", "/Geom/b", true),
        ("/Lights/FaceSetLinking/include_faceSet_example", "/", false),
        ("/Lights/FaceSetLinking/include_faceSet_example", "/Geom", false),
        ("/Lights/FaceSetLinking/include_faceSet_example", "/Geom/meshWithFaceSet", false),
        ("/Lights/FaceSetLinking/include_faceSet_example", "/Geom/meshWithFaceSet/faceSet", true),
    ];
    for (light, path, expected) in cases {
        let links = LightAPI::from_prim_unchecked(stage.prim(light)?).light_link_collection();
        assert_eq!(includes(&links, path)?, expected, "{light} links {path}");
    }
    Ok(())
}

/// `testUsdLuxLinkingAPI.py:test_LinkageAuthoring`.
#[test]
fn linkage_authoring() -> Result<()> {
    let stage = memory()?;
    geom::Scope::define(&stage, "/Geom")?;
    geom::Sphere::define(&stage, "/Geom/Sphere")?;
    geom::Scope::define(&stage, "/Lights")?;
    let light = SphereLight::define(&stage, "/Lights/light_1")?;
    let links = light.light_api().light_link_collection();

    // The schema links everything.
    assert!(includes(&links, "/Geom")? && includes(&links, "/Geom/Sphere")?);
    assert!(includes(&links, "/RandomOtherPath")?);

    links.exclude_path("/Geom")?;
    assert!(!includes(&links, "/Geom")? && !includes(&links, "/Geom/Sphere")?);
    assert!(includes(&links, "/RandomOtherPath")?);

    links.include_path("/Geom/Sphere")?;
    assert!(!includes(&links, "/Geom")?);
    assert!(includes(&links, "/Geom/Sphere")? && includes(&links, "/Geom/Sphere/Child")?);
    assert!(includes(&links, "/RandomOtherPath")?);
    Ok(())
}

/// `testUsdLuxLinkingAPI.py:test_FilterLinking`.
#[test]
fn filter_linking() -> Result<()> {
    let stage = linking_stage()?;
    let light = LightAPI::from_prim_unchecked(stage.prim("/Lights/FilterLinking/filter_exclude_a")?);
    let filters = light.filters_rel().forwarded_targets()?;
    assert_eq!(filters, [sdf::path("/Lights/FilterLinking/filter")?]);

    let filter = LightFilter::get(&stage, filters[0].clone())?.expect("LightFilter");
    assert_eq!(filter.path().as_str(), "/Lights/FilterLinking/filter");
    let links = filter.filter_link_collection();
    assert!(!includes(&links, "/Geom/a")?);
    assert!(includes(&links, "/Geom/b")?);
    Ok(())
}

/// A plugin light filter links like any filter, everything before anything
/// is authored.
#[test]
fn plugin_filter_linking() -> Result<()> {
    let stage = memory()?;
    let filter = PluginLightFilter::define(&stage, "/Filter")?;
    let links = filter.filter_link_collection();
    assert_eq!(links.include_root()?, Some(true));
    assert!(includes(&links, "/Anything")?);
    links.exclude_path("/Geom")?;
    assert!(!includes(&links, "/Geom/a")?);
    Ok(())
}

/// The shader-id queries a light and a light filter share, over the
/// universal attribute `universal`.
struct ShaderIds<'a> {
    attr_for: &'a dyn Fn(&str) -> Result<Option<usd::Attribute>>,
    builder_for: &'a dyn Fn(&str) -> usd::AttributeBuilder<'static>,
    id_for: &'a dyn Fn(&[&str]) -> Result<Option<tf::Token>>,
    universal: usd::Attribute,
}

/// `testUsdLuxLight.py:test_GetShaderId`'s `_TestShaderIDs`.
fn check_shader_ids(ids: ShaderIds<'_>) -> Result<()> {
    let name = ids.universal.name();
    let names = |context: &str| -> Result<Option<String>> {
        Ok((ids.attr_for)(context)?.map(|attribute| attribute.name().to_owned()))
    };
    let id = |contexts: &[&str]| -> Result<Option<String>> { Ok((ids.id_for)(contexts)?.map(|id| id.to_string())) };

    // The universal attribute exists through the schema; no other does yet.
    assert_eq!(names("")?.as_deref(), Some(name));
    assert_eq!(names("ri")?, None);
    assert_eq!(names("other")?, None);
    assert_eq!(id(&[])?, None);
    assert_eq!(id(&["other", "ri"])?, None);

    ids.universal.clone().set(sdf::Value::token("DefaultLight"))?;
    assert_eq!(names("ri")?, None);
    assert_eq!(id(&[])?.as_deref(), Some("DefaultLight"));
    assert_eq!(id(&["other", "ri"])?.as_deref(), Some("DefaultLight"));

    (ids.builder_for)("ri").set(sdf::Value::token("SphereLight")).build()?;
    assert_eq!(names("")?.as_deref(), Some(name));
    assert_eq!(names("ri")?, Some(format!("ri:{name}")));
    assert_eq!(names("other")?, None);
    assert_eq!(id(&[])?.as_deref(), Some("DefaultLight"));
    assert_eq!(id(&["other", "ri"])?.as_deref(), Some("SphereLight"));
    assert_eq!(id(&["ri"])?.as_deref(), Some("SphereLight"));
    assert_eq!(id(&["other"])?.as_deref(), Some("DefaultLight"));
    Ok(())
}

/// `testUsdLuxLight.py:test_GetShaderId`, over a `LightAPI` applied to an
/// untyped prim and over a `LightFilter`.
#[test]
fn shader_id_contexts() -> Result<()> {
    let stage = memory()?;
    let light = LightAPI::apply(&stage.define_prim("/PrimLight")?)?;
    check_shader_ids(ShaderIds {
        attr_for: &|context| light.shader_id_attr_for(context),
        builder_for: &|context| light.shader_id_attr_builder_for(context),
        id_for: &|contexts| light.shader_id_for(contexts),
        universal: light.shader_id_attr(),
    })?;

    let filter = LightFilter::define(&stage, "/PrimLightFilter")?;
    check_shader_ids(ShaderIds {
        attr_for: &|context| filter.shader_id_attr_for(context),
        builder_for: &|context| filter.shader_id_attr_builder_for(context),
        id_for: &|contexts| filter.shader_id_for(contexts),
        universal: filter.shader_id_attr(),
    })?;

    // A context attribute is a uniform token the schema does not declare.
    for other in [
        light.create_shader_id_attr_for("other")?,
        filter.create_shader_id_attr_for("other")?,
    ] {
        assert_eq!(other.type_name()?, Some(sdf::ValueTypeName::TOKEN));
        assert_eq!(other.variability()?, Some(sdf::Variability::Uniform));
        assert!(!other.is_custom()?);
    }
    Ok(())
}

/// `testUsdLuxLight.py:test_DomeLight_OrientToStageUpAxis`: a `Y`-up stage
/// needs no op, and a `Z`-up one a 90 degree turn about X.
#[test]
fn dome_orient_axis() -> Result<(), SchemaError> {
    let stage = memory()?;
    geom::set_stage_up_axis(&stage, geom::UpAxis::Y)?;
    let dome = DomeLight::define(&stage, "/dome")?;
    assert!(dome.ordered_xform_ops()?.0.is_empty());
    dome.orient_to_stage_up_axis()?;
    assert!(dome.ordered_xform_ops()?.0.is_empty());

    geom::set_stage_up_axis(&stage, geom::UpAxis::Z)?;
    dome.orient_to_stage_up_axis()?;
    let (ops, _) = dome.ordered_xform_ops()?;
    assert_eq!(ops.len(), 1);
    assert_eq!(ops[0].name(), "xformOp:rotateX:orientToStageUpAxis");
    assert_eq!(ops[0].kind(), Some(geom::XformOpKind::RotateX));
    assert_eq!(ops[0].attribute().get::<f32>()?, Some(90.0));
    Ok(())
}

/// A dome already turned is not turned again.
#[test]
fn dome_orient_idempotent() -> Result<(), SchemaError> {
    let stage = memory()?;
    geom::set_stage_up_axis(&stage, geom::UpAxis::Z)?;
    let dome = DomeLight::define(&stage, "/dome")?;
    dome.orient_to_stage_up_axis()?;
    dome.orient_to_stage_up_axis()?;
    assert_eq!(dome.ordered_xform_ops()?.0.len(), 1);
    Ok(())
}

/// The op already listed inverted counts as the turn, and one a layer
/// declares at double precision, unlisted, takes 90 as a double.
#[test]
fn dome_orient_existing() -> Result<(), SchemaError> {
    let stage = memory()?;
    geom::set_stage_up_axis(&stage, geom::UpAxis::Z)?;
    let name = "xformOp:rotateX:orientToStageUpAxis";

    let inverted = DomeLight::define(&stage, "/Inverted")?;
    stage.prim("/Inverted")?.create_attribute(name, "float")?;
    let inverted = inverted.set_xform_op_order([format!("!invert!{name}")])?;
    inverted.orient_to_stage_up_axis()?;
    assert_eq!(inverted.xform_op_order()?.map(|order| order.len()), Some(1));

    let double = DomeLight::define(&stage, "/Double")?;
    stage.prim("/Double")?.create_attribute(name, "double")?;
    double.orient_to_stage_up_axis()?;
    let (ops, _) = double.ordered_xform_ops()?;
    assert_eq!(ops.len(), 1);
    assert_eq!(ops[0].attribute().get::<f64>()?, Some(90.0));
    Ok(())
}

/// An `upAxis` naming no axis is an error, as is the op listed before a
/// `!resetXformStack!` the stack ignores.
#[test]
fn dome_orient_errors() -> Result<(), SchemaError> {
    let stage = memory()?;
    stage.set_stage_metadata("upAxis", sdf::Value::token("X"))?;
    let dome = DomeLight::define(&stage, "/dome")?;
    assert!(dome.orient_to_stage_up_axis().is_err());

    geom::set_stage_up_axis(&stage, geom::UpAxis::Z)?;
    let dome = dome.set_xform_op_order(["xformOp:rotateX:orientToStageUpAxis", "!resetXformStack!"])?;
    let result = dome.orient_to_stage_up_axis();
    assert!(matches!(result, Err(SchemaError::XformOpExists { .. })), "{result:?}");
    Ok(())
}

/// A stage over `root`, a file of `testUsdLuxLightListAPI`, with no payload
/// loaded.
fn light_list_stage(root: &str) -> Result<Stage> {
    Stage::builder()
        .schema_registry(openusd_schemas::schema_registry())
        .load(usd::InitialLoadSet::LoadNone)
        .open(&format!("fixtures/usdLux_lightList/{root}"))
}

/// The paths `list` computes in `mode`, as text.
fn light_names(list: &impl LightList, mode: LightListMode) -> Result<Vec<String>> {
    Ok(list
        .compute_light_list(mode)?
        .iter()
        .map(sdf::Path::to_string)
        .collect())
}

/// `testUsdLuxLightListAPI.py:_test`, over `stage`.
fn check_light_list(stage: &Stage) -> Result<()> {
    const SKY: &str = "/World/Lights/Sky_light";
    const TORCH_1: &str = "/World/Geo/torch_1/light";
    const TORCH_2: &str = "/World/Geo/torch_2/light";
    let list = LightListAPI::from_prim_unchecked(stage.prim("/World")?);
    let count = |mode| list.compute_light_list(mode).map(|lights| lights.len());

    // Unloaded, a walk finds the one light outside a payload, and the cache
    // `torch_2` publishes adds its light.
    assert!(list.light_list_rel().targets()?.is_empty());
    assert_eq!(light_names(&list, LightListMode::IgnoreCache)?, [SKY]);
    assert_eq!(light_names(&list, LightListMode::ConsultCache)?, [TORCH_2, SKY]);

    // Loaded, a walk finds every light. The cache still sees nothing below
    // the model hierarchy.
    stage.load("/", usd::LoadPolicy::WithDescendants)?;
    assert_eq!(light_names(&list, LightListMode::ConsultCache)?, [TORCH_2, SKY]);
    assert_eq!(light_names(&list, LightListMode::IgnoreCache)?, [TORCH_1, TORCH_2, SKY]);
    let all = list.compute_light_list(LightListMode::IgnoreCache)?;

    list.store_light_list(&all)?;
    assert_eq!(list.compute_light_list(LightListMode::ConsultCache)?, all);

    // A deactivated torch drops out of a walk but stays in the cache until
    // the cache is invalidated.
    stage.prim("/World/Geo/torch_1")?.set_active(false)?;
    assert_eq!(count(LightListMode::IgnoreCache)?, 2);
    assert_eq!(count(LightListMode::ConsultCache)?, 3);
    list.invalidate_light_list()?;
    assert_eq!(count(LightListMode::ConsultCache)?, 2);

    // A light filter counts, and an untyped prim counts once LightAPI
    // applies.
    LightFilter::define(stage, "/World/Lights/TestFilter")?;
    assert_eq!(count(LightListMode::IgnoreCache)?, 3);
    let prim = stage.define_prim("/World/Lights/PrimWithLightAPI")?;
    assert_eq!(count(LightListMode::IgnoreCache)?, 3);
    LightAPI::apply(&prim)?;
    assert_eq!(count(LightListMode::IgnoreCache)?, 4);
    Ok(())
}

#[test]
fn light_list_compute() -> Result<()> {
    check_light_list(&light_list_stage("root.usda")?)
}

#[test]
fn light_list_instanced() -> Result<()> {
    check_light_list(&light_list_stage("root_with_instances.usda")?)
}

/// A stored relative path is anchored at the prim, and an absolute one
/// outside its subtree is left out.
#[test]
fn light_list_relative() -> Result<()> {
    let stage = memory()?;
    let list = LightListAPI::apply(&stage.define_prim("/World")?)?;
    let lights = BTreeSet::from([sdf::path("Lights/Key")?, sdf::path("/Elsewhere/Light")?]);
    list.store_light_list(&lights)?;
    assert_eq!(list.light_list_rel().targets()?, [sdf::path("/World/Lights/Key")?]);
    assert_eq!(
        list.light_list_cache_behavior()?,
        Some(LightListCacheBehavior::ConsumeAndContinue)
    );
    Ok(())
}

/// `consumeAndHalt` takes the cache and skips the prim and its subtree.
#[test]
fn light_list_halt() -> Result<()> {
    let stage = memory()?;
    let list = LightListAPI::apply(&stage.define_prim("/World")?)?;
    SphereLight::define(&stage, "/World/Walked")?;
    list.store_light_list(&BTreeSet::from([sdf::path("/World/Cached")?]))?;
    list.light_list_cache_behavior_attr()
        .set(LightListCacheBehavior::ConsumeAndHalt)?;
    assert_eq!(light_names(&list, LightListMode::ConsultCache)?, ["/World/Cached"]);
    assert_eq!(light_names(&list, LightListMode::IgnoreCache)?, ["/World/Walked"]);

    // A halting cache below the root prunes only its own subtree, and a
    // filter of a derived type counts as a filter.
    let root = LightListAPI::from_prim_unchecked(stage.prim("/")?);
    stage.define_prim("/Group")?.set_kind("group")?;
    let model = stage.define_prim("/Group/Model")?.set_kind("component")?;
    SphereLight::define(&stage, "/Group/Model/Hidden")?;
    let cached = LightListAPI::apply(&model)?;
    cached.store_light_list(&BTreeSet::from([sdf::path("/Group/Model/Cached")?]))?;
    cached
        .light_list_cache_behavior_attr()
        .set(LightListCacheBehavior::ConsumeAndHalt)?;
    PluginLightFilter::define(&stage, "/Group/Filter")?;
    stage.prim("/Group/Filter")?.set_kind("component")?;
    assert_eq!(
        light_names(&root, LightListMode::ConsultCache)?,
        ["/Group/Filter", "/Group/Model/Cached"]
    );
    Ok(())
}

/// The deprecated `ListAPI` answers as `LightListAPI` does.
#[test]
fn list_api_deprecated() -> Result<()> {
    let stage = memory()?;
    let list = ListAPI::apply(&stage.define_prim("/World")?)?;
    SphereLight::define(&stage, "/World/Bulb")?;
    assert_eq!(light_names(&list, LightListMode::IgnoreCache)?, ["/World/Bulb"]);
    let lights = list.compute_light_list(LightListMode::IgnoreCache)?;
    list.store_light_list(&lights)?;
    assert_eq!(list.compute_light_list(LightListMode::ConsultCache)?, lights);
    list.invalidate_light_list()?;
    assert_eq!(list.light_list_cache_behavior()?.as_deref(), Some("ignore"));
    Ok(())
}

/// The paths of `attributes`.
fn paths<T: Deref<Target = usd::Attribute>>(attributes: &[T]) -> Vec<sdf::Path> {
    attributes.iter().map(|attribute| attribute.path().clone()).collect()
}

/// `testUsdLuxLight.py:test_BasicConnectableLights`.
#[test]
fn connectable_lights() -> Result<()> {
    let stage = memory()?;
    let rect = RectLight::define(&stage, "/RectLight")?;
    let light = rect.light_api();
    assert!(light.connectable_api()?.is_some());

    // The built-in inputs are listed, prefixed, and are the schema's own
    // attributes. None is authored.
    let built_in = [
        "color",
        "colorTemperature",
        "diffuse",
        "enableColorTemperature",
        "exposure",
        "height",
        "intensity",
        "normalize",
        "specular",
        "texture:file",
        "width",
    ];
    assert!(light.authored_inputs()?.is_empty());
    let inputs = light.inputs()?;
    let names: Vec<_> = inputs.iter().map(Input::base_name).collect();
    for name in built_in {
        assert!(names.contains(&name), "{name} is built in");
        assert_eq!(light.input(name).name(), format!("inputs:{name}"));
    }
    assert_eq!(light.input("color").path(), rect.color_attr().path());
    assert_eq!(light.input("texture:file").path(), rect.texture_file_attr().path());

    let light_input = light.create_input("newInput", "float")?;
    assert_eq!(paths(&light.authored_inputs()?), [light_input.path().clone()]);
    assert_eq!(light.input("newInput").path(), light_input.path());

    // A light declares no outputs.
    assert!(light.authored_outputs()?.is_empty());
    assert!(light.outputs()?.is_empty());
    let light_output = light.create_output("newOutput", "float")?;
    assert_eq!(paths(&light.authored_outputs()?), [light_output.path().clone()]);
    assert_eq!(paths(&light.outputs()?), [light_output.path().clone()]);

    // A light filter declares neither.
    let filter = LightFilter::define(&stage, "/LightFilter")?;
    assert!(filter.connectable_api()?.is_some());
    assert!(filter.authored_inputs()?.is_empty());
    let filter_input = filter.create_input("newInput", "float")?;
    assert_eq!(paths(&filter.authored_inputs()?), [filter_input.path().clone()]);
    assert!(filter.outputs()?.is_empty());
    let filter_output = filter.create_output("newOutput", "float")?;
    assert_eq!(paths(&filter.outputs()?), [filter_output.path().clone()]);

    // Sources under the light and under the filter.
    let light_graph = NodeGraph::define(&stage, "/RectLight/Prim")?.create_output("graphOut", "float")?;
    let filter_graph = NodeGraph::define(&stage, "/LightFilter/Prim")?.create_output("graphOut", "float")?;

    // A light's outputs connect, and its inputs connect across scopes.
    assert!(light_output.can_connect(&light_graph)?);
    assert!(light_output.can_connect(&filter_graph)?);
    assert!(light_input.can_connect(&light_output)?);
    assert!(light_input.can_connect(&light_graph)?);
    assert!(light_input.can_connect(&filter_graph)?);

    // A filter's outputs connect to nothing, and its inputs across scopes.
    assert!(!filter_output.can_connect(&light_graph)?);
    assert!(!filter_output.can_connect(&filter_graph)?);
    assert!(filter_input.can_connect(&filter_output)?);
    assert!(filter_input.can_connect(&filter_graph)?);
    assert!(filter_input.can_connect(&light_graph)?);

    // ShapingAPI and ShadowAPI inputs on a light connect as the light's do.
    let shaping = ShapingAPI::apply(light.prim())?;
    assert!(shaping.connectable_api()?.is_some());
    let shadow = ShadowAPI::apply(light.prim())?;
    assert!(shadow.connectable_api()?.is_some());
    for (input, attribute) in [
        (shaping.input("shaping:cone:angle"), shaping.shaping_cone_angle_attr()),
        (shaping.input("shaping:focus"), shaping.shaping_focus_attr()),
        (shadow.input("shadow:color"), shadow.shadow_color_attr()),
        (shadow.input("shadow:distance"), shadow.shadow_distance_attr()),
    ] {
        assert_eq!(input.path(), attribute.path());
    }
    for input in [shaping.input("shaping:focus"), shadow.input("shadow:color")] {
        assert!(input.can_connect(&light_output)?);
        assert!(input.can_connect(&light_graph)?);
        assert!(input.can_connect(&filter_graph)?);
    }
    Ok(())
}

/// `testUsdLuxLight.py:test_UsdLux_HasConnectableAPI`, and the type checks
/// `test_BasicConnectableLights` opens with.
#[test]
fn light_has_connectable() -> Result<()> {
    let stage = memory()?;
    let connectable = |schema: &str| ConnectableAPI::has_connectable_api(stage.schema_registry(), &schema.into());
    for schema in ["LightAPI", "LightFilter", "RectLight", "PluginLightFilter"] {
        assert!(connectable(schema), "{schema}");
    }
    assert!(!connectable("ShadowAPI"));
    Ok(())
}

/// ShadowAPI and ShapingAPI give a prim whose type is not connectable no
/// behavior (the end of `test_BasicConnectableLights`).
#[test]
fn shadow_api_unconnectable() -> Result<()> {
    let stage = memory()?;
    let sphere = stage.define_prim("/Sphere")?.set_type_name("Sphere")?;
    assert!(ShadowAPI::apply(&sphere)?.connectable_api()?.is_none());
    assert!(ShapingAPI::apply(&sphere)?.connectable_api()?.is_none());
    Ok(())
}

/// The shade walks see a light's behavior. A value routed out through a
/// light's output resolves to the shader inside it, the light being a
/// container. A light's input consumes the interface input of the graph it
/// sits in, the light being connectable.
#[test]
fn light_container_sources() -> Result<(), SchemaError> {
    let stage = memory()?;
    let rig = RectLight::define(&stage, "/Rig")?.light_api();
    let inner = Shader::define(&stage, "/Rig/Tex")?.create_output("out", "float")?;
    let routed = rig.create_output("out", "float")?.connect_to(&inner)?;
    let consumer = Shader::define(&stage, "/Consumer")?
        .create_input("in", "float")?
        .connect_to(&routed)?;
    let producing = consumer.value_producing_attributes(ProducerFilter::Any)?;
    let producing: Vec<_> = producing.iter().map(|attribute| attribute.path().clone()).collect();
    assert_eq!(producing, [inner.path().clone()]);

    let graph = NodeGraph::define(&stage, "/Graph")?;
    let gain = graph.create_input("gain", "float")?;
    let bulb = SphereLight::define(&stage, "/Graph/Bulb")?.light_api();
    let intensity = bulb.input("intensity").connect_to(&gain)?;
    let consumers = graph.interface_input_consumers(false)?;
    let consumers = consumers.consumers(&gain).expect("gain is an interface input");
    assert_eq!(paths(consumers), [intensity.path().clone()]);
    Ok(())
}

/// A plugin light's and a plugin filter's `NodeDefAPI` read and write the
/// shader they stand for.
#[test]
fn plugin_light_node_def() -> Result<()> {
    let stage = memory()?;
    let light = PluginLight::define(&stage, "/Light")?.node_def();
    light.set_shader_id("MyLight")?;
    assert_eq!(light.shader_id()?.as_deref(), Some("MyLight"));
    assert_eq!(light.implementation()?, ImplementationSource::Id);

    light.set_source_asset("./light.osl", "osl")?;
    assert_eq!(light.implementation()?, ImplementationSource::SourceAsset);
    assert_eq!(
        light.source_asset("osl")?.expect("OSL asset").authored_path,
        "./light.osl"
    );
    assert_eq!(light.shader_id()?, None);

    let filter = PluginLightFilter::define(&stage, "/Filter")?.node_def();
    filter.set_shader_id("MyFilter")?;
    assert_eq!(filter.shader_id()?.as_deref(), Some("MyFilter"));
    Ok(())
}
