//! UsdRender schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdRender` family — the description of *what* to render and *how* the
//! output is framed and split into channels.
//!
//! ```text
//! SchemaBase
//!  ├ SettingsBase  (interface; shared camera + framing attrs)
//!  │  ├ Settings    (typed; top-level config + products)
//!  │  └ Product     (typed; one output artifact, overrides the base)
//!  ├ Var            (typed; one output channel / AOV)
//!  ├ Pass           (typed; a node in a multi-pass graph)
//! ```
//!
//! [`SettingsBase`] carries the camera + image-framing attributes shared
//! by [`Settings`] and [`Product`]. The centrepiece is the computed
//! *render spec* ([`render_spec`]): a `Settings` prim, its
//! products, vars, and camera are flattened into a self-contained,
//! fallback-resolved [`RenderSpec`] (product attributes
//! overriding settings, the aspect-ratio conform policy applied, vars
//! de-duplicated). That computation reads through these views and is the
//! spec-faithful crux of the family.
//!
//! # Example
//!
//! ```
//! use openusd::gf;
//! use openusd::sdf;
//! use openusd_schemas::render::{self, ProductSchema, SettingsBaseSchema, SettingsSchema};
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda").unwrap();
//!
//! // A product renders through a camera, its own or the settings'.
//! openusd_schemas::geom::Camera::define(&stage, "/World/Camera").unwrap();
//!
//! let settings = render::Settings::define(&stage, "/Render/Settings").unwrap();
//! settings.create_resolution_attr().unwrap().set(gf::vec2i(1920, 1080)).unwrap();
//! settings.create_camera_rel().unwrap().add_target("/World/Camera").unwrap();
//! settings.create_products_rel().unwrap().add_target("/Render/Products/beauty").unwrap();
//!
//! render::Product::define(&stage, "/Render/Products/beauty").unwrap()
//!     .create_product_name_attr().unwrap()
//!     .set(sdf::Value::token("beauty.exr")).unwrap();
//!
//! let spec = render::render_spec(&stage, &"/Render/Settings".parse().unwrap(), &[]).unwrap()
//!     .expect("RenderSpec");
//! assert_eq!(spec.products.len(), 1);
//! ```

openusd::include_schema!("usdRender");

pub mod spec;

mod compute;
mod conform;
mod pass;
mod settings;

pub use compute::{namespaced_settings, namespaced_settings_in, render_spec, render_spec_in};
pub use conform::{ConformedAperture, conform_aperture};
pub use spec::{RenderSpec, SpecDiagnostic};
