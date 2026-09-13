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
//! *render spec* ([`compute_render_spec`]): a `Settings` prim, its
//! products, vars, and camera are flattened into a self-contained,
//! fallback-resolved [`RenderSpec`](spec::RenderSpec) (product attributes
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
//! let settings = render::Settings::define(&stage, "/Render/Settings").unwrap();
//! settings.create_resolution_attr().unwrap().set(gf::vec2i(1920, 1080)).unwrap();
//! settings.create_products_rel().unwrap().add_target("/Render/Products/beauty").unwrap();
//!
//! render::Product::define(&stage, "/Render/Products/beauty").unwrap()
//!     .create_product_name_attr().unwrap()
//!     .set(sdf::Value::token("beauty.exr")).unwrap();
//!
//! let spec = render::compute_render_spec(&stage, &"/Render/Settings".parse().unwrap(), &[]).unwrap()
//!     .expect("RenderSpec");
//! assert_eq!(spec.products.len(), 1);
//! ```

openusd::include_schema!("usdRender");

pub mod spec;

mod compute;
mod conform;
mod settings;

pub use compute::{compute_namespaced_settings, compute_render_spec};
pub use conform::{ConformedAperture, apply_aspect_ratio_policy};

// The collections a `RenderPass` carries, each an instance name of
// `UsdCollectionAPI` rather than a property of the pass.
pub const COLLECTION_CAMERA_VISIBILITY: &str = "cameraVisibility";
pub const COLLECTION_PRUNE: &str = "prune";
pub const COLLECTION_MATTE: &str = "matte";
