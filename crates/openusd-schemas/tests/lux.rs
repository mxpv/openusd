//! Integration tests for the UsdLux schema views, exercised against the
//! `usdLux_scene.usda` and `usdLux_linking` fixtures plus a few small
//! in-memory stages: every concrete light, the `Light` interface inputs, the
//! `ShapingAPI` / `ShadowAPI` / `LightListAPI` / `LightAPI` applied schemas,
//! and light, shadow and filter linking.

use openusd::Result;
use openusd::sdf;
use openusd::tf;
use openusd::usd::{self, CollectionAPI, SchemaBase, Stage};
use openusd_schemas::SchemaError;
use openusd_schemas::geom::{self, XformableExt, XformableSchema};
use openusd_schemas::lux::{
    BoundableLightBaseSchema, CylinderLight, CylinderLightSchema, DiskLight, DiskLightSchema, DistantLight,
    DistantLightSchema, DomeLight, DomeLight_1, DomeLight_1Schema, DomeLightSchema, GeometryLight, GeometryLightSchema,
    LightAPI, LightFilter, LightFilterExt, LightFilterSchema, LightListAPI, LightListCacheBehavior,
    NonboundableLightBaseSchema, PluginLightFilter, PortalLight, PortalLightSchema, RectLight, RectLightSchema,
    ShadowAPI, ShapingAPI, SphereLight, SphereLightSchema, TextureFormat,
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
