//! UsdLux schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdLux` class hierarchy. UsdLux lights are UsdGeom prims, so these views
//! build on the [`geom`](crate::geom) chain: every light is a
//! [`geom::Imageable`](crate::geom::Imageable) /
//! [`geom::Xformable`](crate::geom::Xformable) prim, and area lights
//! are additionally [`geom::Boundable`](crate::geom::Boundable).
//!
//! ```text
//! geom::Xformable
//!  ├ LightFilter                         (typed; modulates referencing lights)
//!  └ NonboundableLight  (= Xformable + Light)
//!     ├ DistantLight / GeometryLight
//!     └ DomeLight                        (also covers the DomeLight_1 typeName)
//! geom::Boundable
//!  └ BoundableLight     (= Boundable + Light)
//!     └ SphereLight / DiskLight / RectLight / CylinderLight / PortalLight
//! ```
//!
//! [`LightAPI`] is the `UsdLuxLightAPI` attribute interface every light exposes
//! (intensity / exposure / colour / temperature / filters). It is implemented
//! by every concrete light and by the standalone [`LightAPI`] applied-schema
//! view, which makes an arbitrary prim (a `Mesh`, `Volume`, …) emissive.
//! [`ShapingAPI`], [`ShadowAPI`], and [`LightListAPI`] are the other applied
//! schemas. [`LightAPI::light_link_collection`] and
//! [`LightAPI::shadow_link_collection`] are the geometry a light illuminates
//! and is shadowed by, and [`LightFilterExt::filter_link_collection`] the
//! geometry a filter applies to. [`LightAPI::shader_id_for`] and
//! [`LightFilterExt::shader_id_for`] name the shader each render context
//! draws a light or a filter with. [`DomeLight::orient_to_stage_up_axis`]
//! turns a dome's texture to a `Z`-up stage. [`blackbody_rgb`] is the color
//! a light's color temperature stands for. [`LightList`] finds the lights
//! below a prim and keeps them as a cache on it.
//!
//! Lights and light filters are shading nodes: [`LightAPI`], [`ShapingAPI`],
//! [`ShadowAPI`], [`LightFilter`] and [`PluginLightFilter`] are
//! [`shade::Connectable`](crate::shade::Connectable), and a prim with
//! `LightAPI` or of a `LightFilter` type is a container whose inputs connect
//! across scopes, without encapsulation.
//!
//! # Example
//!
//! ```
//! // A light's own accessors live on its `<Class>Schema` trait; the ones
//! // every light shares come from the light interface it derives through.
//! use openusd_schemas::lux::{self, BoundableLightBaseSchema, SphereLightSchema};
//! use openusd::usd;
//!
//! let stage = usd::Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda").unwrap();
//!
//! let bulb = lux::SphereLight::define(&stage, "/World/Bulb").unwrap();
//! bulb.create_radius_attr().unwrap().set(0.25_f32).unwrap();
//! // `intensity` is the shared light interface, not SphereLight's own.
//! bulb.create_intensity_attr().unwrap().set(800.0_f32).unwrap();
//!
//! assert_eq!(bulb.radius_attr().get::<f32>().unwrap(), Some(0.25));
//! ```
//!
//! # Conventions
//!
//! Property accessors mirror the C++ `Get*Attr` / `Create*Attr` pair: a
//! `foo_attr()` returns an [`openusd::usd::Attribute`] handle whose `get()`
//! yields the authored value, or the fallback the schema declares when
//! nothing is authored (see [`openusd::usd::SchemaRegistry`]), and `create_foo_attr()` authors
//! the attribute with its schema-declared type / variability. Applied-API
//! views (`LightAPI`, `ShapingAPI`, …) gate their `get` on the prim's composed
//! `apiSchemas` and `apply` it through
//! [`openusd::usd::Prim::add_applied_schema`].
//!
//! Token-valued attributes (`texture:format`, `poleAxis`,
//! `lightList:cacheBehavior`) decode through the enums generated with the
//! views, via `from_token` / `as_token`.

openusd::include_schema!("usdLux");

mod blackbody;
mod connectable;
mod dome;
mod light;
mod light_list;

pub use blackbody::blackbody_rgb;
pub(crate) use connectable::register_behaviors;
pub use light::LightFilterExt;
pub use light_list::{LightList, LightListMode};

use openusd::{gf, usd};

use crate::SchemaError;
use crate::geom::{Axis, Cylinder, Extent, ExtentContext, ExtentRegistry, Plane, Sphere};

impl Default for LightListCacheBehavior {
    /// `ignore`: the cache is not consulted and lights are discovered by
    /// traversal.
    ///
    /// The schema documents this as the fallback without declaring one, so the
    /// generator has nothing to take a `Default` from and it is written here.
    /// C++ `UsdLuxLightListAPI::_Traverse` consults the cache only for
    /// `consumeAndHalt` and `consumeAndContinue`, so every other value —
    /// including an unauthored one — traverses.
    fn default() -> Self {
        Self::Ignore
    }
}

/// Add the extent function of each light that has a shape (C++ registers
/// one from each light's own file). A light's extent is the box around the
/// shape that emits, centered on its origin.
pub(crate) fn register_extents(registry: &mut ExtentRegistry) {
    registry
        .register(tokens::SPHERE_LIGHT, sphere_light)
        .register(tokens::DISK_LIGHT, disk_light)
        .register(tokens::CYLINDER_LIGHT, cylinder_light)
        .register(tokens::RECT_LIGHT, rect_light)
        .register(tokens::PORTAL_LIGHT, portal_light);
}

/// A sphere of the light's radius.
fn sphere_light(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
    _context: &ExtentContext,
) -> Result<Option<Extent>, SchemaError> {
    let radius = SphereLight::from_prim_unchecked(prim.clone()).radius_at(time)?;
    Ok(radius.map(|radius| Sphere::extent_from(radius.into(), transform)))
}

/// A disk of the light's radius in the XY plane: a cylinder of no height
/// on Z.
fn disk_light(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
    _context: &ExtentContext,
) -> Result<Option<Extent>, SchemaError> {
    let radius = DiskLight::from_prim_unchecked(prim.clone()).radius_at(time)?;
    Ok(radius.map(|radius| Cylinder::extent_from(0.0, radius.into(), Axis::Z, transform)))
}

/// A cylinder of the light's radius and length along X.
fn cylinder_light(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
    _context: &ExtentContext,
) -> Result<Option<Extent>, SchemaError> {
    let light = CylinderLight::from_prim_unchecked(prim.clone());
    let sizes = light.length_at(time)?.zip(light.radius_at(time)?);
    Ok(sizes.map(|(length, radius)| Cylinder::extent_from(length.into(), radius.into(), Axis::X, transform)))
}

/// A rectangle of the light's width and height in the XY plane.
fn rect_light(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
    _context: &ExtentContext,
) -> Result<Option<Extent>, SchemaError> {
    let light = RectLight::from_prim_unchecked(prim.clone());
    let sizes = light.width_at(time)?.zip(light.height_at(time)?);
    Ok(sizes.map(|(width, height)| Plane::extent_from(width.into(), height.into(), Axis::Z, transform)))
}

/// A rectangle of the portal's width and height in the XY plane.
fn portal_light(
    prim: &usd::Prim,
    time: Option<usd::TimeCode>,
    transform: Option<gf::Mat4d>,
    _context: &ExtentContext,
) -> Result<Option<Extent>, SchemaError> {
    let light = PortalLight::from_prim_unchecked(prim.clone());
    let sizes = light.width_at(time)?.zip(light.height_at(time)?);
    Ok(sizes.map(|(width, height)| Plane::extent_from(width.into(), height.into(), Axis::Z, transform)))
}

#[cfg(test)]
mod tests {
    use openusd::gf;

    use super::{CylinderLight, DiskLight, PortalLight, RectLight, SphereLight, tokens};
    use crate::SchemaError;
    use crate::geom::BoundableExt;

    /// Each shaped light is bounded by its shape (C++ `testUsdLuxLight`
    /// `test_BasicLights` extents).
    #[test]
    fn light_extents() -> Result<(), SchemaError> {
        let stage = crate::tests::stage("anon.usda")?;
        let extent = |x: f32, y: f32, z: f32| Some([gf::vec3f(-x, -y, -z), gf::vec3f(x, y, z)]);

        let sphere = SphereLight::define(&stage, "/Sphere")?;
        sphere.attribute(tokens::INPUTS_RADIUS).set(2.0f32)?;
        assert_eq!(sphere.compute_extent(None)?, extent(2.0, 2.0, 2.0));

        let disk = DiskLight::define(&stage, "/Disk")?;
        disk.attribute(tokens::INPUTS_RADIUS).set(2.0f32)?;
        assert_eq!(disk.compute_extent(None)?, extent(2.0, 2.0, 0.0));

        let cylinder = CylinderLight::define(&stage, "/Cylinder")?;
        cylinder.attribute(tokens::INPUTS_RADIUS).set(2.0f32)?;
        cylinder.attribute(tokens::INPUTS_LENGTH).set(6.0f32)?;
        assert_eq!(cylinder.compute_extent(None)?, extent(3.0, 2.0, 2.0));

        let rect = RectLight::define(&stage, "/Rect")?;
        rect.attribute(tokens::INPUTS_WIDTH).set(4.0f32)?;
        rect.attribute(tokens::INPUTS_HEIGHT).set(2.0f32)?;
        assert_eq!(rect.compute_extent(None)?, extent(2.0, 1.0, 0.0));
        let turned = gf::Mat4d::rotation_z(90f64.to_radians());
        let [low, high] = rect.shape_extent(None, turned)?.expect("a rect light has a shape");
        assert!((high - gf::vec3f(1.0, 2.0, 0.0)).length() < 1e-5 && (low + high).length() < 1e-5);

        // A portal takes the fallback width and height, one each.
        let portal = PortalLight::define(&stage, "/Portal")?;
        assert_eq!(portal.compute_extent(None)?, extent(0.5, 0.5, 0.0));
        Ok(())
    }
}
