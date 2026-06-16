//! Namespace-aware spec copying, the Rust port of C++ `SdfCopySpec`
//! (`pxr/usd/sdf/copyUtils.h`).
//!
//! The recursion walks only the namespace-children fields this backend
//! materializes as separate specs — `primChildren`, `propertyChildren`, and the
//! variant scaffolding (`variantSetChildren` / `variantChildren`). Relationship
//! targets and attribute connections live as list-op fields, not child specs, so
//! their paths are remapped as values rather than recursed into. An internal
//! (same-layer) reference or payload has its prim path remapped too; an external
//! one carries its prim path in the *referenced* layer's namespace and is left
//! untouched.

use crate::sdf;
use crate::tf;

/// Recursively copy the spec at `src_path` (and its namespace descendants) from
/// `src` into `dst` rooted at `dst_path`, re-rooting every embedded namespace
/// path — relationship `targetPaths`, attribute `connectionPaths`,
/// `inheritPaths`, `specializes`, `layerRelocates` — from `src_path` to
/// `dst_path`, along with the child names.
///
/// A replacement: a prim or property subtree already at `dst_path` is erased
/// first (via [`remove_spec`](super::spec::remove_spec)), so the destination
/// ends up an exact copy of the source subtree. A `dst_path` that names a
/// variant, variant set, or the pseudo-root is not erasable, so the copy
/// overlays onto it rather than replacing — pre-existing descendants there
/// survive. Returns `Ok(true)` when a source spec existed (and was copied),
/// `Ok(false)` when `src_path` has no spec — nothing is authored in that case.
///
/// Mirrors the four-argument C++ `SdfCopySpec`. Spec kinds with no separate
/// storage in this backend (relationship targets, connections) are reached
/// through their owning property's list-op fields, not as children.
///
/// `src` and `dst` are distinct backends (`&dyn` vs `&mut dyn`), so an in-place
/// move within a single layer cannot pass it as both; use
/// [`copy_spec_within`] for that.
pub fn copy_spec(
    src: &dyn sdf::AbstractData,
    src_path: &sdf::Path,
    dst: &mut dyn sdf::AbstractData,
    dst_path: &sdf::Path,
) -> Result<bool, sdf::AuthoringError> {
    // Copy nothing — and so erase nothing — unless the source actually holds a
    // copyable spec. A missing or non-materialized source (connection, mapper,
    // …) that reached the erase first would clear the destination and still
    // report success despite copying nothing.
    match src.spec_type(src_path) {
        Some(spec_type) if is_copyable(spec_type) => {}
        _ => return Ok(false),
    }
    // Replacement semantics: clear any existing destination subtree first.
    sdf::spec::remove_spec(dst, dst_path)?;
    copy_spec_with(
        src,
        src_path,
        dst,
        dst_path,
        |args| should_copy_value(args, src_path, dst_path),
        should_copy_children,
    )?;
    Ok(true)
}

/// Copy the spec subtree at `src_path` to `dst_path` within a single backend,
/// re-rooting every embedded namespace path from `src_path` to `dst_path`
/// exactly as [`copy_spec`] does across two backends.
///
/// This is the same-layer form reparent / rename need: [`copy_spec`] takes a
/// `&dyn` source and a `&mut dyn` destination and cannot alias one backend, so
/// the source subtree is snapshotted into a scratch [`Data`](crate::sdf::Data)
/// and copied back. Like [`copy_spec`], the destination subtree is erased first
/// (replacement semantics) and a missing source authors nothing, returning
/// `Ok(false)`.
///
/// This copies; it does not remove the source. A move is `copy_spec_within`
/// followed by [`remove_spec`](super::spec::remove_spec) on `src_path`.
pub fn copy_spec_within(
    data: &mut dyn sdf::AbstractData,
    src_path: &sdf::Path,
    dst_path: &sdf::Path,
) -> Result<bool, sdf::AuthoringError> {
    // Snapshot the source subtree verbatim (src_root == dst_root, so no
    // remapping), then copy the snapshot to `dst_path` — that second copy does
    // the re-rooting and erases any existing destination subtree.
    let mut scratch = sdf::Data::new();
    if !copy_spec(data, src_path, &mut scratch, src_path)? {
        return Ok(false);
    }
    copy_spec(&scratch, src_path, data, dst_path)?;
    Ok(true)
}

/// [`copy_spec`] with caller-supplied policies that can prune fields, prune or
/// rename children, or substitute transformed values — the seam that flatten,
/// namespace editing, and rename (all designed downstream consumers) need.
/// Mirrors the C++ `SdfCopySpec` overload taking `SdfShouldCopyValue` /
/// `SdfShouldCopyChildren` callbacks.
///
/// `should_copy_value` is consulted once per non-children field and returns a
/// [`CopyValue`] (copy as-is, skip, or replace with a transformed value);
/// `should_copy_children` is consulted once per namespace-children field and
/// returns a [`CopyChildren`] (recurse all, skip, or recurse a renamed subset).
/// The structural children fields (`primChildren` / `propertyChildren` /
/// `variantSetChildren` / `variantChildren`) are never offered to
/// `should_copy_value` — the recursion rebuilds them through the typed spec
/// constructors. Unlike [`copy_spec`], this does not erase the destination
/// first.
///
/// NOTE: The destination spec is (re)constructed through the typed constructors,
/// so a property's construction fields (`variability`, `custom`, an attribute's
/// `typeName`) follow the source: `CopyValue::Skip` declines to copy a source
/// field, it does not preserve a pre-existing destination opinion. Overlaying
/// onto an existing spec therefore resets those fields to the source's; field-
/// level merge onto a live destination is not a mode this offers.
pub fn copy_spec_with<V, C>(
    src: &dyn sdf::AbstractData,
    src_path: &sdf::Path,
    dst: &mut dyn sdf::AbstractData,
    dst_path: &sdf::Path,
    should_copy_value: V,
    should_copy_children: C,
) -> Result<(), sdf::AuthoringError>
where
    V: FnMut(CopyValueArgs<'_>) -> CopyValue,
    C: FnMut(CopyChildrenArgs<'_>) -> CopyChildren,
{
    CopyOp {
        src,
        dst,
        value_policy: should_copy_value,
        children_policy: should_copy_children,
    }
    .copy_into(src_path, dst_path)
}

/// The default value policy, a direct callback: copy every field, rewriting any
/// path that falls under `src_root` to sit under `dst_root` instead. A field
/// with no embedded paths is copied as-is ([`CopyValue::Copy`]) without a clone.
///
/// Exposed so a wrapping policy can defer to it — e.g. drop one field, then call
/// this for the rest.
pub fn should_copy_value(args: CopyValueArgs, src_root: &sdf::Path, dst_root: &sdf::Path) -> CopyValue {
    if args.value.has_embedded_paths() {
        CopyValue::Replace(
            args.value
                .remap_paths(|path| path.replace_prefix(src_root, dst_root).unwrap_or_else(|| path.clone())),
        )
    } else {
        CopyValue::Copy
    }
}

/// The default children policy, a direct callback: recurse into every child
/// under its own name. A pure root remap re-roots child *paths* through the
/// recursion, so the child *names* are unchanged.
pub fn should_copy_children(_args: CopyChildrenArgs) -> CopyChildren {
    CopyChildren::All
}

/// What [`copy_spec_with`] does with one field offered to the value policy.
pub enum CopyValue {
    /// Copy the source value unchanged.
    Copy,
    /// Do not copy this field.
    Skip,
    /// Copy this transformed value (path-remapped, …) in place of the source.
    Replace(sdf::Value),
}

/// What [`copy_spec_with`] does with one namespace-children field.
pub enum CopyChildren {
    /// Recurse into every child under its own name.
    All,
    /// Do not recurse into this children field.
    Skip,
    /// Recurse into these `(source name, destination name)` children, in order.
    Map(Vec<(tf::Token, tf::Token)>),
}

/// Inputs handed to the value policy for one field, mirroring the arguments C++
/// passes to `SdfShouldCopyValue`. The source value is borrowed for the
/// callback to read or transform on demand.
pub struct CopyValueArgs<'a> {
    /// Spec type of the spec being copied.
    pub spec_type: sdf::SpecType,
    /// Name of the field offered for copying.
    pub field: &'a str,
    /// The authored source value.
    pub value: &'a sdf::Value,
    /// Path of the spec in the source.
    pub src_path: &'a sdf::Path,
    /// Path the spec is being copied to in the destination.
    pub dst_path: &'a sdf::Path,
}

/// Inputs handed to the children policy for one namespace-children field,
/// mirroring the arguments C++ passes to `SdfShouldCopyChildren`.
pub struct CopyChildrenArgs<'a> {
    /// Which namespace-children field is being recursed.
    pub children_field: sdf::ChildrenKey,
    /// The authored source child names, in order.
    pub children: &'a [tf::Token],
    /// Path of the parent spec in the source.
    pub src_path: &'a sdf::Path,
    /// Path of the parent spec in the destination.
    pub dst_path: &'a sdf::Path,
}

/// The recursive worker behind [`copy_spec_with`]. Holds the source and
/// destination plus the two policies, so the recursion threads only the
/// `(src_path, dst_path)` pair and the generic policy types `V` / `C` stay fixed
/// — one monomorphized copy per [`copy_spec_with`] call, no dynamic dispatch.
struct CopyOp<'a, V, C> {
    src: &'a dyn sdf::AbstractData,
    dst: &'a mut dyn sdf::AbstractData,
    value_policy: V,
    children_policy: C,
}

impl<V, C> CopyOp<'_, V, C>
where
    V: FnMut(CopyValueArgs<'_>) -> CopyValue,
    C: FnMut(CopyChildrenArgs<'_>) -> CopyChildren,
{
    /// Copy the spec at `src_path` (and its namespace descendants) to `dst_path`.
    fn copy_into(&mut self, src_path: &sdf::Path, dst_path: &sdf::Path) -> Result<(), sdf::AuthoringError> {
        let Some(spec_type) = self.src.spec_type(src_path) else {
            return Ok(());
        };
        if !is_copyable(spec_type) {
            return Ok(());
        }
        create_dst_spec(self.dst, dst_path, spec_type)?;

        let fields = self.src.list_fields(src_path).unwrap_or_default();
        let mut authored_type_name = false;
        for field in &fields {
            if is_children_field(field) {
                continue;
            }
            let Some(value) = self.src.try_field(src_path, field)? else {
                continue;
            };
            let args = CopyValueArgs {
                spec_type,
                field,
                value: &value,
                src_path,
                dst_path,
            };
            let authored = match (self.value_policy)(args) {
                CopyValue::Skip => false,
                CopyValue::Copy => {
                    self.dst.set_field(dst_path, field, value.into_owned());
                    true
                }
                CopyValue::Replace(value) => {
                    self.dst.set_field(dst_path, field, value);
                    true
                }
            };
            authored_type_name |= authored && field == sdf::FieldKey::TypeName.as_str();
        }

        // The attribute constructor stamps a placeholder `typeName`; drop it
        // unless the policy actually authored one, so the copy never leaves the
        // empty placeholder behind (a source `typeName` the policy skipped, or a
        // source that authored none at all).
        if spec_type == sdf::SpecType::Attribute && !authored_type_name {
            self.dst.erase_field(dst_path, sdf::FieldKey::TypeName.as_str());
        }

        for &key in child_fields(spec_type) {
            let names = read_child_names(self.src, src_path, key)?;
            if names.is_empty() {
                continue;
            }
            let args = CopyChildrenArgs {
                children_field: key,
                children: &names,
                src_path,
                dst_path,
            };
            match (self.children_policy)(args) {
                CopyChildren::Skip => {}
                CopyChildren::All => {
                    for name in &names {
                        self.copy_child(src_path, dst_path, key, name, name)?;
                    }
                }
                CopyChildren::Map(mapping) => {
                    for (src_name, dst_name) in &mapping {
                        self.copy_child(src_path, dst_path, key, src_name, dst_name)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Copy one child: join the source and destination names onto their parents
    /// through `key`, then recurse.
    fn copy_child(
        &mut self,
        src_path: &sdf::Path,
        dst_path: &sdf::Path,
        key: sdf::ChildrenKey,
        src_name: &str,
        dst_name: &str,
    ) -> Result<(), sdf::AuthoringError> {
        let child_src = join_child(src_path, key, src_name)?;
        let child_dst = join_child(dst_path, key, dst_name)?;
        self.copy_into(&child_src, &child_dst)
    }
}

/// Ensure a spec of `spec_type` exists at `path` and author `fields` on it.
///
/// An upsert: a spec already present with the matching kind keeps its state
/// and only the given fields are written, so unrelated opinions survive.
/// Otherwise the spec is created, with missing ancestors and variant
/// scaffolding materialized as by [`copy_spec_with`].
///
/// An attribute spec requires a `typeName` (as C++ `SdfAttributeSpec::New`
/// does — the text format cannot express an attribute without one), so
/// creating one is rejected with [`InvalidPath`](sdf::AuthoringError::InvalidPath)
/// unless `fields` authors it; writing onto an existing attribute has its
/// `typeName` already.
///
/// Spec kinds with no own storage (targets, connections, mappers, expressions)
/// cannot be authored and are rejected with
/// [`InvalidPath`](sdf::AuthoringError::InvalidPath).
pub(crate) fn author_spec<'a>(
    dst: &mut dyn sdf::AbstractData,
    path: &sdf::Path,
    spec_type: sdf::SpecType,
    fields: impl IntoIterator<Item = (&'a str, sdf::Value)>,
) -> Result<(), sdf::AuthoringError> {
    if !is_copyable(spec_type) {
        return Err(sdf::AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "spec kind has no own storage to author",
        });
    }
    let exists = dst.spec_type(path) == Some(spec_type);
    if !exists {
        create_dst_spec(dst, path, spec_type)?;
    }
    let mut authored_type_name = false;
    for (field, value) in fields {
        authored_type_name |= field == sdf::FieldKey::TypeName.as_str();
        dst.set_field(path, field, value);
    }
    if !exists && spec_type == sdf::SpecType::Attribute && !authored_type_name {
        return Err(sdf::AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "an attribute spec cannot be authored without a typeName",
        });
    }
    Ok(())
}

/// Whether a spec of `spec_type` has its own storage in this backend and is
/// therefore a copy target. The non-copyable kinds (targets, connections,
/// mappers, expressions) live as list-op fields on their owning property.
///
/// Exhaustive over [`sdf::SpecType`] so adding a spec kind is a compile error
/// here rather than a silent "not copyable".
fn is_copyable(spec_type: sdf::SpecType) -> bool {
    match spec_type {
        sdf::SpecType::Prim
        | sdf::SpecType::Attribute
        | sdf::SpecType::Relationship
        | sdf::SpecType::Variant
        | sdf::SpecType::VariantSet
        | sdf::SpecType::PseudoRoot => true,
        sdf::SpecType::Unknown
        | sdf::SpecType::Connection
        | sdf::SpecType::Expression
        | sdf::SpecType::Mapper
        | sdf::SpecType::MapperArg
        | sdf::SpecType::RelationshipTarget => false,
    }
}

/// Create the destination spec at `dst_path` for a source spec of `spec_type`.
/// Attribute / relationship go through the typed constructors; the pseudo-root
/// already exists.
///
/// Prim and variant specs copy onto each other, as in C++ `SdfCopySpec`: both
/// hold the same prim-level fields, so the chain builder derives the spec kind
/// to create from the shape of `dst_path` itself — a prim spec copied to a
/// variant-selection `dst_path` materializes the variant chain, and vice
/// versa.
///
/// The match is exhaustive over [`sdf::SpecType`] so that adding a spec kind is a
/// compile error here rather than a silent no-op.
fn create_dst_spec(
    dst: &mut dyn sdf::AbstractData,
    dst_path: &sdf::Path,
    spec_type: sdf::SpecType,
) -> Result<(), sdf::AuthoringError> {
    match spec_type {
        sdf::SpecType::Prim | sdf::SpecType::Variant => sdf::spec::ensure_prim_chain(dst, dst_path)?,
        sdf::SpecType::Attribute => {
            sdf::AttributeSpecMut::new(dst, dst_path.clone(), "", sdf::Variability::Varying, false)?;
        }
        sdf::SpecType::Relationship => {
            sdf::RelationshipSpecMut::new(dst, dst_path.clone(), sdf::Variability::Varying, false)?;
        }
        sdf::SpecType::VariantSet => sdf::spec::ensure_variant_set(dst, dst_path)?,
        sdf::SpecType::PseudoRoot => {}
        sdf::SpecType::Unknown
        | sdf::SpecType::Connection
        | sdf::SpecType::Expression
        | sdf::SpecType::Mapper
        | sdf::SpecType::MapperArg
        | sdf::SpecType::RelationshipTarget => {
            // The `is_copyable` guard in `copy_spec_into` keeps these out.
            debug_assert!(false, "create_dst_spec called for non-materialized {spec_type}");
        }
    }
    Ok(())
}

/// The namespace-children fields to recurse into for a spec of `spec_type`, the
/// single source of truth for child traversal. A variant set holds variants;
/// prims, variants, and the pseudo-root hold prim / property / variant-set
/// children.
///
/// Exhaustive over [`sdf::SpecType`] so adding a spec kind is a compile error
/// here rather than silently recursing into no children.
fn child_fields(spec_type: sdf::SpecType) -> &'static [sdf::ChildrenKey] {
    use sdf::ChildrenKey::{PrimChildren, PropertyChildren, VariantChildren, VariantSetChildren};
    match spec_type {
        sdf::SpecType::Prim | sdf::SpecType::Variant => &[PrimChildren, PropertyChildren, VariantSetChildren],
        sdf::SpecType::VariantSet => &[VariantChildren],
        sdf::SpecType::PseudoRoot => &[PrimChildren],
        sdf::SpecType::Attribute
        | sdf::SpecType::Relationship
        | sdf::SpecType::Unknown
        | sdf::SpecType::Connection
        | sdf::SpecType::Expression
        | sdf::SpecType::Mapper
        | sdf::SpecType::MapperArg
        | sdf::SpecType::RelationshipTarget => &[],
    }
}

/// Join a child `name` onto `parent` for the given children field, producing the
/// child spec's path. A variant set attaches as `{name=}` to its prim; a variant
/// attaches as `{set=name}` to its prim, recovering the set from the variant-set
/// `parent`.
fn join_child(parent: &sdf::Path, key: sdf::ChildrenKey, name: &str) -> Result<sdf::Path, sdf::AuthoringError> {
    let invalid = || sdf::AuthoringError::InvalidPath {
        path: parent.clone(),
        reason: "child name is not a valid path component",
    };
    match key {
        sdf::ChildrenKey::PrimChildren => parent.append_path(name).map_err(|_| invalid()),
        sdf::ChildrenKey::PropertyChildren => parent.append_property(name).map_err(|_| invalid()),
        sdf::ChildrenKey::VariantSetChildren => Ok(parent.append_variant_selection(name, "")),
        sdf::ChildrenKey::VariantChildren => {
            let prim = parent.parent().ok_or_else(invalid)?;
            let set = parent.variant_set_name().ok_or_else(invalid)?;
            Ok(prim.append_variant_selection(set, name))
        }
        _ => Err(invalid()),
    }
}

/// Read a namespace-children field as its authored child-name list, or an empty
/// list when the field is absent or not a `TokenVec`.
fn read_child_names(
    src: &dyn sdf::AbstractData,
    path: &sdf::Path,
    key: sdf::ChildrenKey,
) -> Result<Vec<tf::Token>, sdf::AuthoringError> {
    let Some(value) = src.try_field(path, key.as_str())? else {
        return Ok(Vec::new());
    };
    Ok(match value.into_owned() {
        sdf::Value::TokenVec(names) => names,
        _ => Vec::new(),
    })
}

/// `true` for the structural children fields the recursion rebuilds, so the
/// value policy never sees them. Also the crate's shared test for "is this
/// field child-name bookkeeping rather than an authored opinion".
pub(crate) fn is_children_field(field: &str) -> bool {
    field == sdf::ChildrenKey::PrimChildren.as_str()
        || field == sdf::ChildrenKey::PropertyChildren.as_str()
        || field == sdf::ChildrenKey::VariantSetChildren.as_str()
        || field == sdf::ChildrenKey::VariantChildren.as_str()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::{path, AbstractData, Data, FieldKey, PathListOp, SpecType, Value};

    /// Author a prim subtree with an attribute and a relationship into a fresh
    /// `Data`, returning it. Shape:
    /// `/A` (Xform) → `/A/Child` (Mesh), `/A.rel` -> [`/A/Child`, `/Outside`],
    /// `/A.attr` connected to `/A/Child.attr`, inherits `[/A/Class]`.
    fn sample() -> Data {
        let mut data = Data::new();
        sdf::PrimSpecMut::new(&mut data, path("/A").unwrap(), sdf::Specifier::Def, "Xform").unwrap();
        sdf::PrimSpecMut::new(&mut data, path("/A/Child").unwrap(), sdf::Specifier::Def, "Mesh").unwrap();
        sdf::RelationshipSpecMut::new(&mut data, path("/A.rel").unwrap(), sdf::Variability::Varying, false).unwrap();
        data.set_field(
            &path("/A.rel").unwrap(),
            FieldKey::TargetPaths.as_str(),
            Value::PathListOp(PathListOp::explicit([
                path("/A/Child").unwrap(),
                path("/Outside").unwrap(),
            ])),
        );
        sdf::AttributeSpecMut::new(
            &mut data,
            path("/A.attr").unwrap(),
            "float",
            sdf::Variability::Varying,
            false,
        )
        .unwrap();
        data.set_field(
            &path("/A.attr").unwrap(),
            FieldKey::ConnectionPaths.as_str(),
            Value::PathListOp(PathListOp::explicit([path("/A/Child.attr").unwrap()])),
        );
        data.set_field(
            &path("/A").unwrap(),
            FieldKey::InheritPaths.as_str(),
            Value::PathListOp(PathListOp::explicit([path("/A/Class").unwrap()])),
        );
        data
    }

    fn targets(data: &dyn AbstractData, prop: &str, field: FieldKey) -> Vec<String> {
        data.try_field(&path(prop).unwrap(), field.as_str())
            .unwrap()
            .unwrap()
            .into_owned()
            .try_as_path_list_op()
            .unwrap()
            .explicit_items
            .iter()
            .map(|p| p.as_str().to_owned())
            .collect()
    }

    #[test]
    fn copy_subtree_reroots() {
        let src = sample();
        let mut dst = Data::new();
        assert!(copy_spec(&src, &path("/A").unwrap(), &mut dst, &path("/B").unwrap()).unwrap());

        assert_eq!(dst.spec_type(&path("/B").unwrap()), Some(SpecType::Prim));
        assert_eq!(dst.spec_type(&path("/B/Child").unwrap()), Some(SpecType::Prim));
        assert_eq!(dst.spec_type(&path("/B.attr").unwrap()), Some(SpecType::Attribute));
        assert_eq!(dst.spec_type(&path("/B.rel").unwrap()), Some(SpecType::Relationship));
        // Child registered on the copied parent.
        let children = dst
            .try_field(&path("/B").unwrap(), sdf::ChildrenKey::PrimChildren.as_str())
            .unwrap()
            .unwrap()
            .into_owned()
            .try_as_token_vec()
            .unwrap();
        assert!(children.iter().any(|t| t == "Child"));
    }

    #[test]
    fn copy_reroots_paths() {
        let src = sample();
        let mut dst = Data::new();
        copy_spec(&src, &path("/A").unwrap(), &mut dst, &path("/B").unwrap()).unwrap();

        // In-subtree targets re-root; the out-of-subtree target is untouched.
        assert_eq!(
            targets(&dst, "/B.rel", FieldKey::TargetPaths),
            vec!["/B/Child", "/Outside"]
        );
        assert_eq!(
            targets(&dst, "/B.attr", FieldKey::ConnectionPaths),
            vec!["/B/Child.attr"]
        );
        assert_eq!(targets(&dst, "/B", FieldKey::InheritPaths), vec!["/B/Class"]);
    }

    #[test]
    fn copy_missing_source_is_noop() {
        let src = Data::new();
        let mut dst = Data::new();
        assert!(!copy_spec(&src, &path("/Nope").unwrap(), &mut dst, &path("/B").unwrap()).unwrap());
        assert_eq!(dst.spec_type(&path("/B").unwrap()), None);
    }

    #[test]
    fn copy_replaces_destination() {
        let src = sample();
        let mut dst = Data::new();
        // A stale child at the destination must not survive the replacement copy.
        sdf::PrimSpecMut::new(&mut dst, path("/B").unwrap(), sdf::Specifier::Def, "Scope").unwrap();
        sdf::PrimSpecMut::new(&mut dst, path("/B/Stale").unwrap(), sdf::Specifier::Def, "Mesh").unwrap();

        copy_spec(&src, &path("/A").unwrap(), &mut dst, &path("/B").unwrap()).unwrap();

        assert_eq!(dst.spec_type(&path("/B/Stale").unwrap()), None);
        assert_eq!(dst.spec_type(&path("/B/Child").unwrap()), Some(SpecType::Prim));
        let type_name = dst
            .try_field(&path("/B").unwrap(), FieldKey::TypeName.as_str())
            .unwrap()
            .unwrap()
            .into_owned()
            .try_as_token()
            .unwrap();
        assert_eq!(type_name.as_str(), "Xform");
    }

    #[test]
    fn copy_with_prunes() {
        let src = sample();
        let mut dst = Data::new();
        // Drop the relationship's targets; copy everything else through the
        // default remap. Prune the `Child` prim.
        let value_policy = |args: CopyValueArgs| {
            if args.field == FieldKey::TargetPaths.as_str() {
                CopyValue::Skip
            } else {
                should_copy_value(args, &path("/A").unwrap(), &path("/B").unwrap())
            }
        };
        let children_policy = |args: CopyChildrenArgs| {
            CopyChildren::Map(
                args.children
                    .iter()
                    .filter(|n| *n != "Child")
                    .map(|n| (n.clone(), n.clone()))
                    .collect(),
            )
        };
        copy_spec_with(
            &src,
            &path("/A").unwrap(),
            &mut dst,
            &path("/B").unwrap(),
            value_policy,
            children_policy,
        )
        .unwrap();

        assert_eq!(dst.spec_type(&path("/B/Child").unwrap()), None);
        assert!(dst
            .try_field(&path("/B.rel").unwrap(), FieldKey::TargetPaths.as_str())
            .unwrap()
            .is_none());
    }

    #[test]
    fn copy_noncopyable_source_preserves_dst() {
        // A source spec of a non-materialized kind copies nothing, so it must
        // leave the destination untouched and report `false`.
        let mut src = Data::new();
        src.create_spec(path("/X").unwrap(), SpecType::Connection);
        let mut dst = Data::new();
        sdf::PrimSpecMut::new(&mut dst, path("/B").unwrap(), sdf::Specifier::Def, "Scope").unwrap();

        assert!(!copy_spec(&src, &path("/X").unwrap(), &mut dst, &path("/B").unwrap()).unwrap());
        assert_eq!(dst.spec_type(&path("/B").unwrap()), Some(SpecType::Prim));
    }

    #[test]
    fn copy_with_skipped_type_name() {
        // A policy that skips an authored typeName must not leave the attribute
        // constructor's empty-string placeholder behind.
        let src = sample();
        let mut dst = Data::new();
        let value_policy = |args: CopyValueArgs| {
            if args.field == FieldKey::TypeName.as_str() {
                CopyValue::Skip
            } else {
                CopyValue::Copy
            }
        };
        copy_spec_with(
            &src,
            &path("/A.attr").unwrap(),
            &mut dst,
            &path("/B.attr").unwrap(),
            value_policy,
            should_copy_children,
        )
        .unwrap();

        assert_eq!(dst.spec_type(&path("/B.attr").unwrap()), Some(SpecType::Attribute));
        assert!(dst
            .try_field(&path("/B.attr").unwrap(), FieldKey::TypeName.as_str())
            .unwrap()
            .is_none());
    }

    #[test]
    fn copy_into_variant() {
        let src = sample();
        let mut dst = Data::new();
        // Land the copy under a variant selection; the scaffolding must appear.
        copy_spec(&src, &path("/A").unwrap(), &mut dst, &path("/V{set=sel}Model").unwrap()).unwrap();

        assert_eq!(dst.spec_type(&path("/V").unwrap()), Some(SpecType::Prim));
        assert_eq!(dst.spec_type(&path("/V{set=}").unwrap()), Some(SpecType::VariantSet));
        assert_eq!(dst.spec_type(&path("/V{set=sel}").unwrap()), Some(SpecType::Variant));
        assert_eq!(dst.spec_type(&path("/V{set=sel}Model").unwrap()), Some(SpecType::Prim));
        assert_eq!(
            dst.spec_type(&path("/V{set=sel}Model/Child").unwrap()),
            Some(SpecType::Prim)
        );
        // A target inside the copied subtree re-roots under the variant path.
        assert_eq!(
            targets(&dst, "/V{set=sel}Model.rel", FieldKey::TargetPaths),
            vec!["/V{set=sel}Model/Child", "/Outside"]
        );
    }

    #[test]
    fn copy_remaps_internal_reference() {
        let mut src = Data::new();
        sdf::PrimSpecMut::new(&mut src, path("/A").unwrap(), sdf::Specifier::Def, "").unwrap();
        src.set_field(
            &path("/A").unwrap(),
            FieldKey::References.as_str(),
            Value::ReferenceListOp(sdf::ReferenceListOp::prepended([
                sdf::Reference {
                    prim_path: path("/A/Inner").unwrap(),
                    ..Default::default()
                },
                sdf::Reference {
                    asset_path: "other.usda".into(),
                    prim_path: path("/A/Ext").unwrap(),
                    ..Default::default()
                },
                sdf::Reference::default(),
            ])),
        );

        let mut dst = Data::new();
        copy_spec(&src, &path("/A").unwrap(), &mut dst, &path("/B").unwrap()).unwrap();

        // The internal (same-layer) reference re-roots; the external one keeps
        // its prim path in the referenced layer's namespace, and the empty
        // defaultPrim selector stays empty.
        let references = dst
            .try_field(&path("/B").unwrap(), FieldKey::References.as_str())
            .unwrap()
            .unwrap()
            .into_owned()
            .try_as_reference_list_op()
            .unwrap();
        assert_eq!(references.prepended_items[0].prim_path.as_str(), "/B/Inner");
        assert_eq!(references.prepended_items[1].prim_path.as_str(), "/A/Ext");
        assert!(references.prepended_items[2].prim_path.is_empty());
    }

    #[test]
    fn copy_prim_onto_variant() {
        // A prim spec copies onto a variant-selection destination: the variant
        // chain materializes and the prim's fields land on the variant spec.
        let src = sample();
        let mut dst = Data::new();
        copy_spec(&src, &path("/A").unwrap(), &mut dst, &path("/V{set=sel}").unwrap()).unwrap();

        assert_eq!(dst.spec_type(&path("/V{set=}").unwrap()), Some(SpecType::VariantSet));
        assert_eq!(dst.spec_type(&path("/V{set=sel}").unwrap()), Some(SpecType::Variant));
        assert_eq!(dst.spec_type(&path("/V{set=sel}Child").unwrap()), Some(SpecType::Prim));
        let type_name = dst
            .try_field(&path("/V{set=sel}").unwrap(), FieldKey::TypeName.as_str())
            .unwrap()
            .unwrap()
            .into_owned()
            .try_as_token()
            .unwrap();
        assert_eq!(type_name.as_str(), "Xform");
    }

    #[test]
    fn within_moves_subtree() {
        let mut data = sample();
        assert!(copy_spec_within(&mut data, &path("/A").unwrap(), &path("/B").unwrap()).unwrap());

        assert_eq!(data.spec_type(&path("/B").unwrap()), Some(SpecType::Prim));
        assert_eq!(data.spec_type(&path("/B/Child").unwrap()), Some(SpecType::Prim));
        assert_eq!(data.spec_type(&path("/B.attr").unwrap()), Some(SpecType::Attribute));
        // A copy, not a move: the source survives until the caller removes it.
        assert_eq!(data.spec_type(&path("/A").unwrap()), Some(SpecType::Prim));
    }

    #[test]
    fn within_reroots_paths() {
        let mut data = sample();
        copy_spec_within(&mut data, &path("/A").unwrap(), &path("/B").unwrap()).unwrap();

        // In-subtree targets re-root; the out-of-subtree target is untouched.
        assert_eq!(
            targets(&data, "/B.rel", FieldKey::TargetPaths),
            vec!["/B/Child", "/Outside"]
        );
        assert_eq!(
            targets(&data, "/B.attr", FieldKey::ConnectionPaths),
            vec!["/B/Child.attr"]
        );
        assert_eq!(targets(&data, "/B", FieldKey::InheritPaths), vec!["/B/Class"]);
    }

    #[test]
    fn within_missing_source_noop() {
        let mut data = Data::new();
        assert!(!copy_spec_within(&mut data, &path("/Nope").unwrap(), &path("/B").unwrap()).unwrap());
        assert_eq!(data.spec_type(&path("/B").unwrap()), None);
    }

    #[test]
    fn copy_source_variant() {
        // A source prim carrying a variant set copies its variant contents.
        let mut src = Data::new();
        sdf::PrimSpecMut::new(&mut src, path("/A").unwrap(), sdf::Specifier::Def, "Xform").unwrap();
        sdf::PrimSpecMut::over(&mut src, path("/A{look=red}Inside").unwrap()).unwrap();

        let mut dst = Data::new();
        copy_spec(&src, &path("/A").unwrap(), &mut dst, &path("/B").unwrap()).unwrap();

        assert_eq!(dst.spec_type(&path("/B{look=}").unwrap()), Some(SpecType::VariantSet));
        assert_eq!(dst.spec_type(&path("/B{look=red}").unwrap()), Some(SpecType::Variant));
        assert_eq!(
            dst.spec_type(&path("/B{look=red}Inside").unwrap()),
            Some(SpecType::Prim)
        );
    }
}
