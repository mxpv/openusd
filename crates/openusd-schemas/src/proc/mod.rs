//! UsdProc schema views.
//!
//! Typed value-views over a composed [`openusd::usd::Stage`], mirroring Pixar's
//! `UsdProc` family. The one concrete schema is [`GenerativeProcedural`]
//! (C++ `UsdProcGenerativeProcedural`) — a prim whose children are generated
//! at runtime by a named procedural system. It is a
//! [`geom::Boundable`](crate::geom::Boundable) prim (its transform /
//! extent / visibility come from the UsdGeom layer, and its input parameters
//! live in the `primvars:` namespace); this module adds the procedural-specific
//! `proceduralSystem` attribute.
//!
//! # Example
//!
//! ```
//! // A view's own accessors live on its `<Class>Schema` trait.
//! use openusd_schemas::proc::{GenerativeProcedural, GenerativeProceduralSchema};
//! use openusd::sdf;
//! use openusd::usd::Stage;
//!
//! // The registry is what makes the prim a `GenerativeProcedural`.
//! let stage = Stage::builder()
//!     .schema_registry(openusd_schemas::schema_registry())
//!     .in_memory("scene.usda")
//!     .unwrap();
//!
//! let proc = GenerativeProcedural::define(&stage, "/World/Scatter").unwrap();
//! proc.create_procedural_system_attr().unwrap().set(sdf::Value::Token("Houdini".into())).unwrap();
//!
//! // Read it back through a typed view.
//! let proc = GenerativeProcedural::get(&stage, "/World/Scatter").unwrap().expect("GenerativeProcedural");
//! assert_eq!(
//!     proc.procedural_system_attr().get::<sdf::Value>().unwrap(),
//!     Some(sdf::Value::Token("Houdini".into()))
//! );
//! ```

openusd::include_schema!("usdProc");
