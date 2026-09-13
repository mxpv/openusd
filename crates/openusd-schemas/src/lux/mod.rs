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
//! schemas.
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
