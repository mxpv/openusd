//! Color-space resolution over composed stages: AOUSD core spec §14.4.3,
//! and C++ `testUsdColorSpaceAPIPy.py`.

use std::fs;

use openusd::gf::{self, color_space_names as names};
use openusd::usd;
use openusd::{sdf, tf, vt};

fn stage() -> usd::Stage {
    usd::Stage::builder()
        .in_memory("anon.usda")
        .expect("an in-memory stage")
}

/// Apply `ColorSpaceAPI` to the prim at `path`, assigning `name` where given.
fn assign(stage: &usd::Stage, path: &str, name: Option<&str>) -> usd::Prim {
    let prim = stage.override_prim(path).expect("a prim");
    let api = usd::ColorSpaceAPI::apply(&prim).expect("applies");
    if let Some(name) = name {
        api.color_space_name_attr_builder()
            .set(vt::Value::token(name))
            .build()
            .expect("authors");
    }
    prim
}

/// A `color3f` attribute named `color` on `prim`.
fn color_attr(prim: &usd::Prim) -> usd::Attribute {
    prim.create_attribute("color", "color3f").expect("an attribute")
}

/// Define the color space `name` on `prim` as the instance `instance`.
fn define(prim: &usd::Prim, instance: &str, name: &str) -> usd::ColorSpaceDefinitionAPI {
    let definition = usd::ColorSpaceDefinitionAPI::apply(prim, instance).expect("applies");
    definition
        .name_attr_builder()
        .set(vt::Value::token(name))
        .build()
        .expect("authors");
    definition
}

/// Define the color space `name` on `prim` as the instance `instance`, with
/// the primaries of the built-in `like` and the gamma `gamma`.
fn define_like(prim: &usd::Prim, instance: &str, name: &str, like: &str, gamma: f32) {
    let primaries = gf::ColorSpace::new(like).primaries_and_white_point();
    define(prim, instance, name)
        .create_attrs_with_chroma(primaries, gamma, 0.0)
        .expect("authors");
}

fn name_of(prim: &usd::Prim, cache: &mut usd::ColorSpaceCache) -> tf::Token {
    usd::ColorSpaceAPI::compute_name(prim, Some(cache))
        .expect("resolves")
        .unwrap_or_default()
}

fn attr_name_of(attr: &usd::Attribute, cache: &mut usd::ColorSpaceCache) -> tf::Token {
    usd::ColorSpaceAPI::compute_attribute_name(attr, Some(cache))
        .expect("resolves")
        .unwrap_or_default()
}

fn cached(cache: &usd::ColorSpaceCache, stage: &usd::Stage, path: &str) -> Option<String> {
    let path = sdf::Path::new(path).expect("a path");
    cache.get(stage, &path).map(|name| name.as_str().to_owned())
}

/// `testUsdColorSpaceAPIPy.py:test_ColorSpaceAPI`, the hierarchy half: a name
/// inherits down the hierarchy, a nearer assignment wins, and each computed
/// name is cached at the prim asked about.
#[test]
fn inherits_down_hierarchy() {
    let stage = stage();
    let mut cache = usd::ColorSpaceCache::default();

    let root = assign(&stage, "/rec2020", Some(names::LINEAR_REC2020));
    assert!(gf::ColorSpace::is_valid(names::LINEAR_REC2020));
    let api = usd::ColorSpaceAPI::from_prim(root.clone())
        .expect("a read")
        .expect("applied");
    assert_eq!(
        api.color_space_name().expect("a read").expect("authored"),
        names::LINEAR_REC2020
    );
    assert_eq!(name_of(&root, &mut cache), names::LINEAR_REC2020);
    assert_eq!(
        attr_name_of(&api.color_space_name_attr(), &mut cache),
        names::LINEAR_REC2020
    );
    assert_eq!(
        cached(&cache, &stage, "/rec2020").as_deref(),
        Some(names::LINEAR_REC2020)
    );
    assert_eq!(attr_name_of(&color_attr(&root), &mut cache), names::LINEAR_REC2020);

    let child = assign(&stage, "/rec2020/linSRGB", Some(names::LINEAR_REC709));
    assert_eq!(name_of(&child, &mut cache), names::LINEAR_REC709);
    assert_eq!(
        cached(&cache, &stage, "/rec2020/linSRGB").as_deref(),
        Some(names::LINEAR_REC709)
    );
    assert_eq!(attr_name_of(&color_attr(&child), &mut cache), names::LINEAR_REC709);

    let grandchild = stage.override_prim("/rec2020/linSRGB/noColorSpace").expect("a prim");
    assert_eq!(name_of(&grandchild, &mut cache), names::LINEAR_REC709);
    assert_eq!(
        cached(&cache, &stage, "/rec2020/linSRGB/noColorSpace").as_deref(),
        Some(names::LINEAR_REC709)
    );
    assert_eq!(attr_name_of(&color_attr(&grandchild), &mut cache), names::LINEAR_REC709);

    // A hierarchy with no assignment at its root resolves to none there.
    let root2 = stage.override_prim("/noColorSpace").expect("a prim");
    assert_eq!(name_of(&root2, &mut cache), "");
    assert_eq!(cached(&cache, &stage, "/noColorSpace").as_deref(), Some(""));
    assert_eq!(attr_name_of(&color_attr(&root2), &mut cache), "");
    let child2 = assign(&stage, "/noColorSpace/linSRGB", Some(names::LINEAR_REC709));
    assert_eq!(name_of(&child2, &mut cache), names::LINEAR_REC709);
    assert_eq!(attr_name_of(&color_attr(&child2), &mut cache), names::LINEAR_REC709);
    let grandchild2 = assign(&stage, "/noColorSpace/linSRGB/noColorSpace", None);
    assert_eq!(name_of(&grandchild2, &mut cache), names::LINEAR_REC709);
    assert_eq!(
        attr_name_of(&color_attr(&grandchild2), &mut cache),
        names::LINEAR_REC709
    );

    for prim in [&root, &child, &grandchild] {
        usd::ColorSpaceAPI::can_apply(prim).expect("applies");
    }
    let found = usd::ColorSpaceAPI::get(&stage, "/rec2020")
        .expect("a read")
        .expect("applied");
    assert_eq!(found.path(), root.path());
}

/// `testUsdColorSpaceAPIPy.py:test_ColorSpaceAPI`, the definition half: names
/// defined on an ancestor resolve, an attribute's own name wins, and the
/// definition's attributes give the space.
#[test]
fn definitions_resolve() {
    let stage = stage();
    let mut cache = usd::ColorSpaceCache::default();
    let (rec2020, aces) = ("testRec2020", "testACESCg");
    let def_prim = stage.override_prim("/colorSpaceDef").expect("a prim");
    define(&def_prim, rec2020, rec2020);
    let aces_def = define(&def_prim, aces, aces);

    let prim = assign(&stage, "/colorSpaceDef/noCS/defPrim", Some(aces));
    let attr = color_attr(&prim).set_color_space(rec2020).expect("authors");
    assert_eq!(attr_name_of(&attr, &mut cache), rec2020);
    let no_cs = stage.override_prim("/colorSpaceDef/noCS").expect("a prim");
    assert_eq!(name_of(&no_cs, &mut cache), "");

    let child = stage
        .override_prim("/colorSpaceDef/noCS/defPrim/childDefPrim")
        .expect("a prim");
    assert_eq!(name_of(&child, &mut cache), aces);
    let child_attr = color_attr(&child);
    assert_eq!(attr_name_of(&child_attr, &mut cache), aces);
    let child_attr = child_attr.set_color_space(rec2020).expect("authors");
    assert_eq!(attr_name_of(&child_attr, &mut cache), rec2020);
    assert_eq!(name_of(&child, &mut cache), aces);

    // The definition's fallbacks describe an identity transform.
    let space = usd::ColorSpaceAPI::compute(&child, Some(&mut cache)).expect("resolves");
    assert!(space.is_equivalent(&gf::ColorSpace::new(aces)));

    let acescg = gf::ColorSpace::new(names::LINEAR_AP1);
    let [red, green, blue, white] = acescg.primaries_and_white_point();
    for builder in [
        aces_def.red_chroma_attr_builder().set(red),
        aces_def.green_chroma_attr_builder().set(green),
        aces_def.blue_chroma_attr_builder().set(blue),
        aces_def.white_point_attr_builder().set(white),
    ] {
        builder.build().expect("authors");
    }
    assert!(aces_def.color_space().expect("a read").is_equivalent(&acescg));
    let space = usd::ColorSpaceAPI::compute(&child, Some(&mut cache)).expect("resolves");
    assert!(space.is_equivalent(&acescg));
    assert_eq!(space.name(), aces);
}

/// AOUSD core spec §14.4.3: Material1 overrides Root, Material2's
/// `colorSpace:name` is ignored without `usd::ColorSpaceAPI`, and Material3's
/// attribute names its own.
#[test]
fn spec_inheritance_example() {
    let stage = usd::Stage::open("fixtures/color_space_inheritance.usda").expect("opens");
    let resolve = |path: &str| {
        let attr = stage.attribute(path).expect("an attribute");
        usd::ColorSpaceAPI::compute_attribute_name(&attr, None)
            .expect("resolves")
            .unwrap_or_default()
    };
    assert_eq!(resolve("/Root/Material1.inputs:diffuseColor"), names::SRGB_P3_D65);
    assert_eq!(resolve("/Root/Material2.inputs:diffuseColor"), names::LINEAR_REC709);
    assert_eq!(resolve("/Root/Material3.inputs:diffuseColor"), names::SRGB_REC709);
    let root = stage.prim("/Root").expect("a prim");
    assert_eq!(
        usd::ColorSpaceAPI::compute_name(&root, None)
            .expect("resolves")
            .as_deref(),
        Some(names::LINEAR_REC709)
    );
}

/// A prim assigning a name nothing defines resolves to no name, even under
/// an ancestor that assigns a valid one, while an attribute's own unknown
/// name comes back as it is.
#[test]
fn unknown_names() {
    let stage = stage();
    assign(&stage, "/Outer", Some(names::LINEAR_AP1));
    let bogus = assign(&stage, "/Outer/Bogus", Some("not_a_space"));
    let mut cache = usd::ColorSpaceCache::default();
    assert_eq!(
        usd::ColorSpaceAPI::compute_name(&bogus, Some(&mut cache)).expect("resolves"),
        None
    );
    assert_eq!(
        cached(&cache, &stage, "/Outer/Bogus"),
        None,
        "an unknown name is not cached"
    );
    assert_eq!(
        usd::ColorSpaceAPI::compute_attribute_name(&color_attr(&bogus), None).expect("resolves"),
        None
    );

    let prim = assign(&stage, "/Valid", Some(names::LINEAR_AP1));
    let attr = color_attr(&prim).set_color_space("not_a_space").expect("authors");
    assert_eq!(
        usd::ColorSpaceAPI::compute_attribute_name(&attr, None)
            .expect("resolves")
            .as_deref(),
        Some("not_a_space")
    );
    assert!(!usd::ColorSpaceAPI::is_valid_name(&prim, "not_a_space").expect("a read"));
    let space = usd::ColorSpaceAPI::compute_attribute(&attr, None).expect("resolves");
    assert_eq!(space.name(), "");
    assert!(space.is_equivalent(&gf::ColorSpace::new(names::DATA)));
}

/// A definition reusing a built-in's name is passed over, and the nearest
/// definition of a name wins.
#[test]
fn definition_precedence() {
    let stage = stage();
    let a = stage.override_prim("/A").expect("a prim");
    define_like(&a, "fake709", names::LINEAR_REC709, names::LINEAR_AP1, 2.2);
    define_like(&a, "house", "house", names::LINEAR_REC709, 1.0);
    let b = stage.override_prim("/A/B").expect("a prim");
    define_like(&b, "house", "house", names::LINEAR_REC709, 2.2);

    let builtin = assign(&stage, "/A/Builtin", Some(names::LINEAR_REC709));
    let space = usd::ColorSpaceAPI::compute(&builtin, None).expect("resolves");
    assert_eq!(space, gf::ColorSpace::new(names::LINEAR_REC709));

    let near = assign(&stage, "/A/B/C", Some("house"));
    let far = assign(&stage, "/A/D", Some("house"));
    let near = usd::ColorSpaceAPI::compute(&near, None).expect("resolves");
    let far = usd::ColorSpaceAPI::compute(&far, None).expect("resolves");
    assert_eq!((near.name().as_str(), near.gamma()), ("house", 2.2));
    assert_eq!((far.name().as_str(), far.gamma()), ("house", 1.0));
    assert!(usd::ColorSpaceAPI::is_valid_name(&b, "house").expect("a read"));
    let outside = stage.override_prim("/Outside").expect("a prim");
    assert!(!usd::ColorSpaceAPI::is_valid_name(&outside, "house").expect("a read"));
}

/// One cache serves several stages, each its own answer at a shared path.
#[test]
fn cache_per_stage() {
    let (first, second) = (stage(), stage());
    let a = assign(&first, "/Mesh", Some(names::LINEAR_AP1));
    let b = assign(&second, "/Mesh", Some(names::SRGB_REC709));
    let mut cache = usd::ColorSpaceCache::default();
    assert_eq!(name_of(&a, &mut cache), names::LINEAR_AP1);
    assert_eq!(name_of(&b, &mut cache), names::SRGB_REC709);
    assert_eq!(name_of(&a, &mut cache), names::LINEAR_AP1);
    assert_eq!(cached(&cache, &first, "/Mesh").as_deref(), Some(names::LINEAR_AP1));
    assert_eq!(cached(&cache, &second, "/Mesh").as_deref(), Some(names::SRGB_REC709));
}

/// A cache keeps what it computed across edits, as its contract states; a
/// new cache sees the edit.
#[test]
fn cache_after_edits() {
    let stage = stage();
    let prim = assign(&stage, "/P", Some(names::LINEAR_REC709));
    let mut old = usd::ColorSpaceCache::default();
    assert_eq!(name_of(&prim, &mut old), names::LINEAR_REC709);
    usd::ColorSpaceAPI::from_prim_unchecked(prim.clone())
        .color_space_name_attr()
        .set(vt::Value::token(names::LINEAR_AP1))
        .expect("authors");
    assert_eq!(name_of(&prim, &mut old), names::LINEAR_REC709);
    assert_eq!(name_of(&prim, &mut usd::ColorSpaceCache::default()), names::LINEAR_AP1);

    let leaf = stage.override_prim("/Q/R").expect("a prim");
    let mut old = usd::ColorSpaceCache::default();
    assert_eq!(name_of(&leaf, &mut old), "");
    assign(&stage, "/Q", Some(names::LINEAR_REC2020));
    assert_eq!(name_of(&leaf, &mut old), "");
    assert_eq!(
        name_of(&leaf, &mut usd::ColorSpaceCache::default()),
        names::LINEAR_REC2020
    );
}

/// An unassigned attribute resolves to the identity sentinel, which converts
/// otherwise than the spec's default, Linear Rec.709, does.
#[test]
fn unassigned_not_default() {
    let stage = stage();
    let attr = color_attr(&stage.override_prim("/U").expect("a prim"));
    assert_eq!(
        usd::ColorSpaceAPI::compute_attribute_name(&attr, None).expect("resolves"),
        None
    );
    let space = usd::ColorSpaceAPI::compute_attribute(&attr, None).expect("resolves");
    assert_eq!(space.name(), "");

    let ap0 = gf::ColorSpace::new(names::LINEAR_AP0);
    let rgb = [0.5, 0.25, 0.125];
    let through_sentinel = gf::Color::new(rgb, space).to_space(ap0.clone()).rgb();
    let default = gf::ColorSpace::new(names::LINEAR_REC709);
    let through_default = gf::Color::new(rgb, default).to_space(ap0);
    let expected = gf::Color::new(
        [0.337_736, 0.260_346, 0.145_521],
        gf::ColorSpace::new(names::LINEAR_AP0),
    );
    assert!(through_default.is_close(&expected, 1e-5));
    assert!(!through_default.is_close(&gf::Color::new(through_sentinel, expected.color_space().clone()), 1e-3));
}

/// A row-vector matrix authors primaries that rebuild it.
#[test]
fn definition_from_matrix() {
    let stage = stage();
    let prim = stage.override_prim("/M").expect("a prim");
    let definition = usd::ColorSpaceDefinitionAPI::apply(&prim, "byMatrix").expect("applies");
    let m = gf::Mat3d::from([
        [0.4124, 0.2126, 0.0193],
        [0.3576, 0.7152, 0.1192],
        [0.1805, 0.0722, 0.9505],
    ]);
    definition.create_attrs_with_matrix(m, 2.4, 0.055).expect("authors");
    assert_eq!(definition.gamma().expect("a read"), Some(2.4));
    assert_eq!(definition.linear_bias().expect("a read"), Some(0.055));
    let space = definition.color_space().expect("a read");
    assert_eq!(space.name(), "byMatrix");
    assert!(space.rgb_to_xyz().is_close(m, 1e-4), "{:?}", space.rgb_to_xyz());
}

/// The text reader types `colorConfiguration` as an asset and
/// `colorManagementSystem` as a token. The stage resolves the configuration
/// against the layer that authors it, and reports the session layer's opinion
/// over the root layer's.
#[test]
fn color_configuration_metadata() {
    let dir = tempfile::tempdir().expect("a temp dir");
    let root = dir.path().join("root.usda");
    let session = dir.path().join("session.usda");
    let root_text = "#usda 1.0\n(\n    colorConfiguration = @./config.ocio@\n    \
                     colorManagementSystem = \"OpenColorIO\"\n)\n";
    fs::write(&root, root_text).expect("writes");
    fs::write(dir.path().join("config.ocio"), "").expect("writes");
    fs::write(&session, "#usda 1.0\n(\n    colorManagementSystem = \"ACES\"\n)\n").expect("writes");
    let (root, session) = (root.to_str().expect("a path"), session.to_str().expect("a path"));

    let stage = usd::Stage::open(root).expect("opens");
    {
        let handle = stage.root_layer();
        let layer = handle.try_borrow().expect("a layer");
        let config = layer.color_configuration().expect("authored");
        assert_eq!(config, "./config.ocio");
        assert_eq!(config.resolved_path(), None);
        assert_eq!(layer.color_management_system().expect("authored"), "OpenColorIO");
    }
    let config = stage.color_configuration().expect("authored");
    assert_eq!(config, "./config.ocio");
    let resolved = config.resolved_path().expect("resolved against the root layer");
    assert!(resolved.ends_with("config.ocio"), "{resolved}");
    let cms = stage.color_management_system().expect("authored");
    assert_eq!(cms, "OpenColorIO");

    let with_session = usd::Stage::builder().session_layer(session).open(root).expect("opens");
    let cms = with_session.color_management_system().expect("authored");
    assert_eq!(cms, "ACES");
}

/// The builder's fallbacks answer where no layer authors a non-empty value,
/// and an authored one wins over them.
#[test]
fn color_config_fallbacks() {
    let stage = usd::Stage::builder()
        .color_configuration_fallback("site.ocio")
        .color_management_system_fallback("OpenColorIO")
        // An empty fallback leaves the one before it, as in C++.
        .color_management_system_fallback("")
        .in_memory("anon.usda")
        .expect("an in-memory stage");
    assert_eq!(stage.color_configuration().expect("a fallback"), "site.ocio");
    let cms = stage.color_management_system().expect("a fallback");
    assert_eq!(cms, "OpenColorIO");
    let (config, cms) = stage.color_config_fallbacks();
    assert_eq!(config.expect("set"), "site.ocio");
    assert_eq!(cms.expect("set"), "OpenColorIO");

    stage.set_color_configuration("shot.ocio").expect("authors");
    stage.set_color_management_system("ACES").expect("authors");
    assert_eq!(stage.color_configuration().expect("authored"), "shot.ocio");
    assert_eq!(stage.color_management_system().expect("authored"), "ACES");
    assert!(
        stage
            .root_layer()
            .try_borrow()
            .expect("a layer")
            .has_color_configuration()
    );

    // An empty authored name defers to the fallback, as in C++.
    stage.set_color_management_system("").expect("authors");
    let cms = stage.color_management_system().expect("a fallback");
    assert_eq!(cms, "OpenColorIO");

    let bare = self::stage();
    assert_eq!(bare.color_configuration(), None);
    assert_eq!(bare.color_config_fallbacks(), (None, None));
}

/// A layer sets, reports, writes and clears both fields.
#[test]
fn layer_color_configuration() {
    let mut layer = sdf::Layer::new_anonymous("color.usda");
    assert!(!layer.has_color_configuration() && !layer.has_color_management_system());
    layer
        .edit(|edit| {
            edit.set_color_configuration("config.ocio")?;
            edit.set_color_management_system("OpenColorIO")
        })
        .expect("authors");
    assert_eq!(layer.color_configuration().expect("authored"), "config.ocio");
    assert!(layer.has_color_management_system());
    let text = layer.export_to_string().expect("writes");
    assert!(text.contains("colorConfiguration = @config.ocio@"), "{text}");
    assert!(text.contains("colorManagementSystem = \"OpenColorIO\""), "{text}");
    layer
        .edit(|edit| {
            edit.clear_color_configuration()?;
            edit.clear_color_management_system()
        })
        .expect("clears");
    assert!(!layer.has_color_configuration() && !layer.has_color_management_system());
}

/// An attribute's own empty `colorSpace`, or one that is not a token,
/// assigns no color space, and its prim's is not consulted (C++ returns the
/// attribute's own as it is).
#[test]
fn attribute_own_edge_cases() {
    let stage = stage();
    let prim = assign(&stage, "/P", Some(names::LINEAR_AP1));
    let empty = color_attr(&prim).set_color_space("").expect("authors");
    assert_eq!(empty.color_space().expect("a read").as_deref(), Some(""));
    assert_eq!(
        usd::ColorSpaceAPI::compute_attribute_name(&empty, None).expect("resolves"),
        None
    );

    let odd = prim.create_attribute("odd", "color3f").expect("an attribute");
    let root = stage.root_layer().identifier().to_owned();
    stage
        .edit_layer(&root, |edit| {
            let mut spec = edit.attribute_mut(odd.path().clone())?.expect("a spec");
            spec.set(sdf::FieldKey::ColorSpace.as_str(), vt::Value::Int(3));
            Ok(())
        })
        .expect("authors");
    assert_eq!(odd.color_space().expect("a read"), None);
    assert_eq!(
        usd::ColorSpaceAPI::compute_attribute_name(&odd, None).expect("resolves"),
        None
    );
}

/// A prim the stage does not hold resolves to no color space, even under a
/// prim that assigns one, as C++ stops at an invalid prim.
#[test]
fn invalid_prim_none() {
    let stage = stage();
    assign(&stage, "/P", Some(names::LINEAR_AP1));
    let missing = stage.prim("/P/Missing").expect("a handle");
    assert!(!missing.is_valid().expect("a read"));
    assert_eq!(
        usd::ColorSpaceAPI::compute_name(&missing, None).expect("resolves"),
        None
    );
}
