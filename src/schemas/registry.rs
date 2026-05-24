//! Schema registry — placeholder for the future Rust analogue of
//! Pixar's `UsdSchemaRegistry`.
//!
//! The C++ registry maps schema type tokens (e.g. `"Mesh"`,
//! `"PhysicsRigidBodyAPI"`) to schema definitions: their fallback
//! property values, allowed token sets, applied-API flags, and
//! aliases. Once openusd-rs gains enough domain schemas to make a
//! shared lookup useful, this is where that registry will live.
//!
//! Today the per-schema readers in [`super::physics`] and
//! [`super::skel`] keep their own token constants and validation
//! logic in-module — the registry layer doesn't need to exist yet,
//! and would just be empty plumbing. The module exists as a clear
//! signpost so future contributions know where to grow.
