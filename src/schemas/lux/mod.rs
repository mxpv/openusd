//! UsdLux schema views.
//!
//! Typed value-views over a composed [`crate::Stage`], mirroring Pixar's
//! `UsdLux` class hierarchy. UsdLux lights are UsdGeom prims, so these views
//! build on the [`geom`](crate::schemas::geom) trait chain: every light is a
//! [`geom::Imageable`](crate::schemas::geom::Imageable) /
//! [`geom::Xformable`](crate::schemas::geom::Xformable) prim, and area lights
//! are additionally [`geom::Boundable`](crate::schemas::geom::Boundable).
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
//! [`Light`] is the `UsdLuxLightAPI` attribute interface every light exposes
//! (intensity / exposure / colour / temperature / filters). It is implemented
//! by every concrete light and by the standalone [`LightAPI`] applied-schema
//! view, which makes an arbitrary prim (a `Mesh`, `Volume`, …) emissive.
//! [`ShapingAPI`], [`ShadowAPI`], and [`LightListAPI`] are the other applied
//! schemas.
//!
//! # Conventions
//!
//! Property accessors mirror the C++ `Get*Attr` / `Create*Attr` pair: a
//! `foo_attr()` returns an [`crate::usd::Attribute`] handle whose `get()`
//! yields the authored value (or `None` — there is no schema registry yet to
//! supply fallbacks, so e.g. `DistantLight`'s documented 50000 intensity is
//! not synthesized), and `create_foo_attr()` authors the attribute with its
//! schema-declared type / variability. Applied-API views (`LightAPI`,
//! `ShapingAPI`, …) gate their `get` on the prim's composed `apiSchemas` and
//! `apply` it through [`crate::usd::Prim::add_applied_schema`].
//!
//! Token-valued attributes (`texture:format`, `poleAxis`,
//! `lightList:cacheBehavior`) decode through the enums at the end of this
//! module via `from_token` / `as_token`.

pub mod tokens;

mod schema;
mod traits;

pub use schema::{
    CylinderLight, DiskLight, DistantLight, DomeLight, GeometryLight, LightAPI, LightFilter, LightListAPI, PortalLight,
    RectLight, ShadowAPI, ShapingAPI, SphereLight,
};
pub use traits::{BoundableLight, Light, NonboundableLight};

use anyhow::Result;

use crate::sdf;
use crate::usd::{Attribute, Prim, Stage};

use tokens::*;

// The typed / applied-API `get` gates, applying an API schema, and the
// attribute-authoring shorthands the `create_*` accessors build on. Private to
// the module so the `lights` / `traits` submodules reach them via `super::`.

/// Resolve `path` to a [`Prim`] handle only when its `typeName` matches
/// `type_name` — the gate behind a concrete light's `get`.
fn get_typed(stage: &Stage, path: impl Into<sdf::Path>, type_name: &str) -> Result<Option<Prim>> {
    let path = path.into();
    if stage.type_name(&path)?.as_deref() != Some(type_name) {
        return Ok(None);
    }
    Ok(Some(stage.prim_at_path(path)))
}

/// Resolve `path` to a [`Prim`] handle only when its `typeName` is one of
/// `type_names` — the gate behind a view (like `DomeLight`) that covers more
/// than one schema typeName.
fn get_typed_any(stage: &Stage, path: impl Into<sdf::Path>, type_names: &[&str]) -> Result<Option<Prim>> {
    let path = path.into();
    match stage.type_name(&path)? {
        Some(t) if type_names.contains(&t.as_str()) => Ok(Some(stage.prim_at_path(path))),
        _ => Ok(None),
    }
}

/// Resolve `path` to a [`Prim`] handle only when it carries one of `apis` in
/// its composed `apiSchemas` — the gate behind an applied-API view's `get`.
fn get_with_api(stage: &Stage, path: impl Into<sdf::Path>, apis: &[&str]) -> Result<Option<Prim>> {
    let path = path.into();
    let applied = stage.api_schemas(&path)?;
    if apis.iter().any(|a| applied.iter().any(|s| s == a)) {
        Ok(Some(stage.prim_at_path(path)))
    } else {
        Ok(None)
    }
}

/// Open the prim at `path` as `over` and add `api` to its `apiSchemas` — the
/// shared body of every applied-API view's `apply`.
fn apply_api(stage: &Stage, path: impl Into<sdf::Path>, api: &str) -> Result<Prim> {
    Ok(stage.override_prim(path)?.add_applied_schema(api)?)
}

/// Author a varying attribute named `name` of `type_name` with
/// `custom = false`, returning its handle.
fn create(prim: &Prim, name: &str, type_name: &str) -> Result<Attribute> {
    Ok(prim.create_attribute(name, type_name)?.set_custom(false)?)
}

/// Author a `uniform token` attribute named `name` with `custom = false`.
fn create_uniform_token(prim: &Prim, name: &str) -> Result<Attribute> {
    Ok(create(prim, name, "token")?.set_variability(sdf::Variability::Uniform)?)
}

/// Implement the schema-trait chain for a concrete `struct $ty(Prim)` light
/// newtype. Every arm hand-writes the one `SchemaBase` method (`prim`) and
/// adds the empty membership impls for the chain it names; all trait paths are
/// fully qualified, so the call site only needs the macro in scope.
///
/// - `xformable` is a typed [`geom::Xformable`](crate::schemas::geom::Xformable)
///   prim that is not a light (e.g. `LightFilter`).
/// - `nonboundable_light` adds [`Light`] + [`NonboundableLight`]
///   (`DistantLight`, `DomeLight`, `GeometryLight`).
/// - `boundable_light` adds [`geom::Boundable`](crate::schemas::geom::Boundable)
///   + [`Light`] + [`BoundableLight`] (the area lights).
/// - `applied_api` is a single-apply API-schema view (`LightAPI`, `ShapingAPI`,
///   `ShadowAPI`, `LightListAPI`) — just the `SchemaBase` impl with
///   `KIND = SingleApplyApi`, no chain memberships.
macro_rules! impl_lux_schema {
    (@base $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
        impl $crate::schemas::geom::Imageable for $ty {}
        impl $crate::schemas::geom::Xformable for $ty {}
    };
    (xformable $ty:ident) => {
        impl_lux_schema!(@base $ty);
    };
    (nonboundable_light $ty:ident) => {
        impl_lux_schema!(@base $ty);
        impl $crate::schemas::lux::Light for $ty {}
        impl $crate::schemas::lux::NonboundableLight for $ty {}
    };
    (boundable_light $ty:ident) => {
        impl_lux_schema!(@base $ty);
        impl $crate::schemas::geom::Boundable for $ty {}
        impl $crate::schemas::lux::Light for $ty {}
        impl $crate::schemas::lux::BoundableLight for $ty {}
    };
    (applied_api $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::SingleApplyApi;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
    };
}

pub(crate) use impl_lux_schema;

// Token-valued attribute enums. Each decodes one `allowedTokens` attribute via
// `from_token` / `as_token`, with the Pixar default as its `Default`. The
// views expose the raw `Attribute` handles; pass the handle's token through
// these to classify it.

/// `UsdLuxDomeLight.inputs:texture:format` token values.
///
/// Per Pixar's schema the default is [`TextureFormat::Automatic`] — the
/// renderer picks based on the image aspect ratio.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TextureFormat {
    #[default]
    Automatic,
    Latlong,
    MirroredBall,
    Angular,
    CubeMapVerticalCross,
}

impl TextureFormat {
    pub fn as_token(self) -> &'static str {
        match self {
            TextureFormat::Automatic => TEXTURE_FORMAT_AUTOMATIC,
            TextureFormat::Latlong => TEXTURE_FORMAT_LATLONG,
            TextureFormat::MirroredBall => TEXTURE_FORMAT_MIRRORED_BALL,
            TextureFormat::Angular => TEXTURE_FORMAT_ANGULAR,
            TextureFormat::CubeMapVerticalCross => TEXTURE_FORMAT_CUBE_MAP_VERTICAL_CROSS,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            TEXTURE_FORMAT_AUTOMATIC => TextureFormat::Automatic,
            TEXTURE_FORMAT_LATLONG => TextureFormat::Latlong,
            TEXTURE_FORMAT_MIRRORED_BALL => TextureFormat::MirroredBall,
            TEXTURE_FORMAT_ANGULAR => TextureFormat::Angular,
            TEXTURE_FORMAT_CUBE_MAP_VERTICAL_CROSS => TextureFormat::CubeMapVerticalCross,
            _ => return None,
        })
    }
}

/// `UsdLuxDomeLight_1.poleAxis` token values.
///
/// Selects which axis points to the dome's "north pole" — i.e. which axis the
/// texture wraps around. Pixar's spec default is [`PoleAxis::SceneUp`], which
/// defers to the stage's `upAxis` metadata. Only meaningful on `DomeLight_1`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PoleAxis {
    #[default]
    SceneUp,
    Y,
    Z,
}

impl PoleAxis {
    pub fn as_token(self) -> &'static str {
        match self {
            PoleAxis::SceneUp => POLE_AXIS_SCENE_UP,
            PoleAxis::Y => POLE_AXIS_Y,
            PoleAxis::Z => POLE_AXIS_Z,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            POLE_AXIS_SCENE_UP => PoleAxis::SceneUp,
            POLE_AXIS_Y => PoleAxis::Y,
            POLE_AXIS_Z => PoleAxis::Z,
            _ => return None,
        })
    }
}

/// `UsdLuxLightListAPI.lightList:cacheBehavior` token values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LightListCacheBehavior {
    /// Use the cached `lightList` rel and also continue traversing children
    /// for any additional lights. Spec default.
    #[default]
    ConsumeAndContinue,
    /// Use the cached `lightList` only; don't recurse into children.
    ConsumeAndHalt,
    /// Ignore the cache and traverse normally.
    Ignore,
}

impl LightListCacheBehavior {
    pub fn as_token(self) -> &'static str {
        match self {
            LightListCacheBehavior::ConsumeAndContinue => CACHE_BEHAVIOR_CONSUME_AND_CONTINUE,
            LightListCacheBehavior::ConsumeAndHalt => CACHE_BEHAVIOR_CONSUME_AND_HALT,
            LightListCacheBehavior::Ignore => CACHE_BEHAVIOR_IGNORE,
        }
    }

    pub fn from_token(s: &str) -> Option<Self> {
        Some(match s {
            CACHE_BEHAVIOR_CONSUME_AND_CONTINUE => LightListCacheBehavior::ConsumeAndContinue,
            CACHE_BEHAVIOR_CONSUME_AND_HALT => LightListCacheBehavior::ConsumeAndHalt,
            CACHE_BEHAVIOR_IGNORE => LightListCacheBehavior::Ignore,
            _ => return None,
        })
    }
}
