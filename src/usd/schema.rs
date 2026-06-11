//! Schema view-type foundation.
//!
//! [`SchemaBase`] is the root of the schema-view hierarchy (C++
//! `UsdSchemaBase`). Every schema — typed (IsA) or applied (API) — is a
//! lightweight value-type view over a single [`Prim`] and implements this
//! trait, directly or through an intermediate schema trait (`Imageable`,
//! `Xformable`, …). Domain schemas in [`crate::schemas`] build their typed
//! property accessors on top of [`SchemaBase::prim`].

use crate::sdf;

use super::{Prim, Stage};

/// How a schema relates to its prim (C++ `UsdSchemaKind`).
///
/// Each concrete schema declares its kind as [`SchemaBase::KIND`]; the
/// classification queries on [`SchemaBase`] derive from it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SchemaKind {
    /// Abstract base that is never instantiated and is not `UsdTyped`
    /// (e.g. `SchemaBase` itself, or `Imageable`).
    AbstractBase,
    /// Abstract typed schema — a non-instantiable `IsA` base (e.g.
    /// `Boundable`).
    AbstractTyped,
    /// Concrete typed schema — an instantiable prim type whose `typeName`
    /// names it (e.g. `Sphere`, `GenerativeProcedural`).
    ConcreteTyped,
    /// API schema that is not applied to a prim's `apiSchemas` list.
    NonAppliedApi,
    /// Single-apply API schema (applied once, no instance name).
    SingleApplyApi,
    /// Multiple-apply API schema (applied per instance name).
    MultipleApplyApi,
}

/// Common surface shared by every schema view type (C++ `UsdSchemaBase`).
///
/// A schema wraps a [`Prim`] and exposes that prim's opinions through typed
/// accessors. This trait carries the part every schema shares — the
/// underlying prim, the handles derived from it, and the schema's
/// classification — so intermediate schema traits and concrete schemas can
/// build their accessors on one foundation.
///
/// A schema is constructed by wrapping a [`Prim`] (each concrete schema is a
/// `struct Foo(Prim)` newtype). Wrapping is unchecked, mirroring the C++
/// `UsdSchemaBase(prim)` constructor; a type-gated constructor (the analog of
/// C++ `UsdSchema::Get`) belongs on each concrete schema.
///
/// The registry-backed members of C++ `UsdSchemaBase`
/// (`GetSchemaClassPrimDefinition`, `GetSchemaAttributeNames`) are omitted
/// until the schema registry ([`crate::schemas::registry`]) exists.
pub trait SchemaBase {
    /// This schema's kind (C++ `UsdSchemaBase::schemaKind` /
    /// `GetSchemaKind`). Read it at the type level (`Sphere::KIND`) or
    /// generically (`S::KIND`); the classification queries below derive from
    /// it. Required, with no default: a concrete view's kind is almost never
    /// `AbstractBase`, so every schema declares its own.
    const KIND: SchemaKind;

    /// The prim this schema is a view of (C++ `UsdSchemaBase::GetPrim`). The
    /// one method each schema implements; everything else derives from it.
    fn prim(&self) -> &Prim;

    /// Composed namespace path of the prim (C++ `UsdSchemaBase::GetPath`).
    fn path(&self) -> &sdf::Path {
        self.prim().path()
    }

    /// The stage the prim is anchored to.
    fn stage(&self) -> &Stage {
        self.prim().stage()
    }

    /// Whether this is an instantiable prim type (C++ `IsConcrete`).
    fn is_concrete(&self) -> bool {
        matches!(Self::KIND, SchemaKind::ConcreteTyped)
    }

    /// Whether this schema is an `IsA` (typed) schema (C++ `IsTyped`).
    fn is_typed(&self) -> bool {
        matches!(Self::KIND, SchemaKind::AbstractTyped | SchemaKind::ConcreteTyped)
    }

    /// Whether this schema is an API schema (C++ `IsAPISchema`).
    fn is_api_schema(&self) -> bool {
        matches!(
            Self::KIND,
            SchemaKind::NonAppliedApi | SchemaKind::SingleApplyApi | SchemaKind::MultipleApplyApi
        )
    }

    /// Whether this is an applied API schema (C++ `IsAppliedAPISchema`).
    fn is_applied_api_schema(&self) -> bool {
        matches!(Self::KIND, SchemaKind::SingleApplyApi | SchemaKind::MultipleApplyApi)
    }

    /// Whether this is a multiple-apply API schema
    /// (C++ `IsMultipleApplyAPISchema`).
    fn is_multiple_apply_api_schema(&self) -> bool {
        matches!(Self::KIND, SchemaKind::MultipleApplyApi)
    }
}

/// Every schema unwraps to its underlying [`Prim`], so `Prim::from(schema)`
/// and `let prim: Prim = schema.into()` work uniformly. The prim is cloned
/// out — a cheap `Rc` bump on the stage plus a path clone.
impl<T: SchemaBase> From<T> for Prim {
    fn from(schema: T) -> Self {
        schema.prim().clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::usd::Stage;

    /// A minimal concrete schema used to exercise the trait's provided methods.
    struct Marker(Prim);

    impl SchemaBase for Marker {
        const KIND: SchemaKind = SchemaKind::ConcreteTyped;

        fn prim(&self) -> &Prim {
            &self.0
        }
    }

    #[test]
    fn base_accessors() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let prim = stage.define_prim("/World")?;

        let schema = Marker(prim);
        assert_eq!(schema.path().as_str(), "/World");
        // `stage()` resolves through the prim's own shared handle.
        assert_eq!(schema.stage().prim(schema.path()).type_name()?, None);
        Ok(())
    }

    #[test]
    fn into_prim_via_from() -> anyhow::Result<()> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        let schema = Marker(stage.define_prim("/World")?);

        let prim: Prim = schema.into();
        assert_eq!(prim.path().as_str(), "/World");
        Ok(())
    }

    #[test]
    fn classification() {
        assert_eq!(Marker::KIND, SchemaKind::ConcreteTyped);
        let stage = Stage::builder().in_memory("anon.usda").unwrap();
        let schema = Marker(stage.define_prim("/World").unwrap());
        assert!(schema.is_concrete());
        assert!(schema.is_typed());
        assert!(!schema.is_api_schema());
        assert!(!schema.is_applied_api_schema());
        assert!(!schema.is_multiple_apply_api_schema());
    }
}
