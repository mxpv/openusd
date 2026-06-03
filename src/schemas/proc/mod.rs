//! UsdProc schema views.
//!
//! Typed value-views over a composed [`crate::usd::Stage`], mirroring Pixar's
//! `UsdProc` family. The one concrete schema is [`GenerativeProcedural`]
//! (C++ `UsdProcGenerativeProcedural`) — a prim whose children are generated
//! at runtime by a named procedural system. It is a
//! [`geom::Boundable`](crate::schemas::geom::Boundable) prim (its transform /
//! extent / visibility come from the UsdGeom layer, and its input parameters
//! live in the `primvars:` namespace); this module adds the procedural-specific
//! `proceduralSystem` attribute.
//!
//! # Example
//!
//! ```
//! use openusd::schemas::proc::GenerativeProcedural;
//! use openusd::sdf;
//! use openusd::usd::Stage;
//!
//! let stage = Stage::builder().in_memory("scene.usda").unwrap();
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

pub mod tokens;

mod schema;

pub use schema::GenerativeProcedural;

/// Implement the schema-trait chain for a concrete `struct $ty(Prim)` proc
/// newtype. All trait paths are fully qualified, so the call site only needs
/// the macro in scope.
///
/// - `boundable` is a [`geom::Boundable`](crate::schemas::geom::Boundable) prim
///   (`GenerativeProcedural`).
macro_rules! impl_proc_schema {
    (boundable $ty:ident) => {
        impl $crate::usd::SchemaBase for $ty {
            const KIND: $crate::usd::SchemaKind = $crate::usd::SchemaKind::ConcreteTyped;

            fn prim(&self) -> &$crate::usd::Prim {
                &self.0
            }
        }
        impl $crate::schemas::geom::Imageable for $ty {}
        impl $crate::schemas::geom::Xformable for $ty {}
        impl $crate::schemas::geom::Boundable for $ty {}
    };
}

pub(crate) use impl_proc_schema;
