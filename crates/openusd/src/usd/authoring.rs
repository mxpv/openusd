//! The shared machinery behind stage-tier property authoring: where a spec
//! comes from when the edit target holds none, which fields the generic
//! metadata calls may not touch, and the closures that edit a typed spec.
//!
//! Creating or editing a property on the edit target follows C++
//! `UsdStage::_CreatePropertySpecForEditing` in two phases. The read phase,
//! [`plan_property_spec`], runs before any transaction and is the only place
//! composition is consulted: it resolves an [`EnsurePlan`] in C++ precedence
//! order — the edit target's own spec, the schema declaration, the strongest
//! authored spec of any kind, then the caller's fallback. The write phase,
//! [`apply_plan`], runs inside the single transaction and only rechecks the
//! local spec and stamps the resolved declaration. Splitting them keeps
//! composed queries out of the transaction closure, which holds the layer
//! graph mutably, and lets a caller stamp the spec and perform its own
//! mutation as one atomic edit.

use std::sync::Arc;

use crate::{pcp, sdf, tf};

use super::{Attribute, PrimTypeInfo, Relationship, SpecSite, Stage, StageAuthoringError};

/// A property kind, as the authoring operations below work on it: what its
/// specs are, and how one is opened for editing.
///
/// Implemented on the stage-tier handles, so an operation names the thing being
/// authored: `author::<Attribute>`.
pub(super) trait PropertySpecKind {
    /// What a spec of this kind answers to, for the checks that a path holds
    /// the kind the caller meant.
    const KIND: sdf::SpecType;

    /// A mutable view of one, borrowed from the layer that holds it.
    type View<'a>;

    /// Opens the spec at `path`, or `None` where the layer holds none.
    fn view(data: &mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self::View<'_>>;
}

impl PropertySpecKind for Attribute {
    const KIND: sdf::SpecType = sdf::SpecType::Attribute;

    type View<'a> = sdf::AttributeSpecMut<'a>;

    fn view(data: &mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self::View<'_>> {
        sdf::AttributeSpecMut::get(data, path)
    }
}

impl PropertySpecKind for Relationship {
    const KIND: sdf::SpecType = sdf::SpecType::Relationship;

    type View<'a> = sdf::RelationshipSpecMut<'a>;

    fn view(data: &mut dyn sdf::AbstractData, path: sdf::Path) -> Option<Self::View<'_>> {
        sdf::RelationshipSpecMut::get(data, path)
    }
}

/// Stamps the spec `path` needs on the edit target and runs `edit` on it, as
/// one transaction.
///
/// The phase order lives here: the read that resolves where the spec comes
/// from, then the transaction that stamps it and mutates it. A caller supplies
/// the mutation alone, typed to the spec its kind opens.
pub(super) fn author<P: PropertySpecKind>(
    stage: &Stage,
    path: &sdf::Path,
    edit: impl FnOnce(&mut P::View<'_>) -> Result<(), StageAuthoringError>,
) -> Result<(), StageAuthoringError> {
    let plan = plan_property_spec(stage, path, P::KIND, None)?;
    stage
        .with_target_layer_at(path, |layer, spec_path| {
            apply_plan(layer.data_mut(), &spec_path, P::KIND, &plan)?;
            edit_spec(layer.data_mut(), spec_path, P::KIND, P::view, edit)
        })
        .map(|_| ())
}

/// What a property spec stamped on the edit target declares: the fields C++
/// `_StampNewPropertySpec` copies from the declaration it found.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum PropertyDeclaration {
    Attribute {
        type_name: sdf::ValueTypeName,
        variability: sdf::Variability,
        custom: bool,
    },
    Relationship {
        variability: sdf::Variability,
        custom: bool,
    },
}

impl PropertyDeclaration {
    pub fn kind(&self) -> sdf::SpecType {
        match self {
            Self::Attribute { .. } => sdf::SpecType::Attribute,
            Self::Relationship { .. } => sdf::SpecType::Relationship,
        }
    }
}

/// The read phase's answer for a property about to be authored.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum EnsurePlan {
    /// The edit target already holds a spec of the wanted kind, which is left
    /// as it is.
    Existing,
    /// The edit target holds no spec; this declaration is stamped first.
    Stamp(PropertyDeclaration),
}

impl EnsurePlan {
    /// The value type this plan would declare an attribute with, or `None`
    /// when it stamps nothing — a target that already holds the spec says
    /// nothing about the type — or stamps a relationship.
    pub fn attribute_type(&self) -> Option<&sdf::ValueTypeName> {
        match self {
            Self::Stamp(PropertyDeclaration::Attribute { type_name, .. }) => Some(type_name),
            // A target that already holds the spec says nothing about its
            // type, and a relationship plan never reaches a value write.
            Self::Existing | Self::Stamp(PropertyDeclaration::Relationship { .. }) => None,
        }
    }
}

/// The read phase of authoring the property at `path` as a `kind` spec.
///
/// In C++ precedence order: a spec of that kind already on the edit target is
/// [`EnsurePlan::Existing`]; otherwise the schema declaration, then the
/// strongest authored spec of any kind, supplies the declaration to stamp; only
/// when nothing declares the property does `fallback` apply (`None` for an
/// edit, the supplied declaration for a creation). A declaration of the other
/// kind found at any of those sources is
/// [`SpecKindMismatch`](StageAuthoringError::SpecKindMismatch), never skipped
/// in favour of a weaker one. A declaration taken from a layer is read with
/// the fallible readers, so a malformed strongest spec is an error; the
/// fallback is checked only when it is stamped.
pub(super) fn plan_property_spec(
    stage: &Stage,
    path: &sdf::Path,
    kind: sdf::SpecType,
    fallback: Option<PropertyDeclaration>,
) -> Result<EnsurePlan, StageAuthoringError> {
    if let Some(found) = stage.local_spec_type(path)? {
        return if found == kind {
            Ok(EnsurePlan::Existing)
        } else {
            Err(kind_mismatch(path, kind, found))
        };
    }
    let Some((info, name)) = schema_definition(stage, path)? else {
        return Err(sdf::AuthoringError::InvalidPath {
            path: path.clone(),
            reason: "property authoring needs a property path",
        }
        .into());
    };

    if let Some(property) = info.prim_definition().property(&name) {
        let found = property.spec_type();
        if found != kind {
            return Err(kind_mismatch(path, kind, found));
        }
        let declaration = if kind == sdf::SpecType::Attribute {
            PropertyDeclaration::Attribute {
                type_name: property
                    .type_name_token()
                    .map(sdf::ValueTypeName::from)
                    .ok_or(sdf::ValueTypeError::Empty)?,
                variability: property.variability(),
                custom: false,
            }
        } else {
            PropertyDeclaration::Relationship {
                variability: property.variability(),
                custom: false,
            }
        };
        return Ok(EnsurePlan::Stamp(declaration));
    }

    let strongest = stage
        .masked(path, |graph, cache| cache.property_stack(graph, path, None))?
        .into_iter()
        .next();
    if let Some(site) = strongest {
        let declaration = declaration_at(stage, &site, kind)?;
        if declaration.kind() != kind {
            return Err(kind_mismatch(path, kind, declaration.kind()));
        }
        return Ok(EnsurePlan::Stamp(declaration));
    }

    fallback.map(EnsurePlan::Stamp).ok_or_else(|| missing_spec(path, kind))
}

/// The write phase: inside the transaction, recheck the edit target's spec
/// at `path` and stamp the plan's declaration when it holds none.
pub(super) fn apply_plan(
    data: &mut dyn sdf::AbstractData,
    path: &sdf::Path,
    kind: sdf::SpecType,
    plan: &EnsurePlan,
) -> Result<(), StageAuthoringError> {
    match data.spec_type(path) {
        Some(found) if found == kind => Ok(()),
        Some(found) => Err(kind_mismatch(path, kind, found)),
        None => match plan {
            EnsurePlan::Existing => Err(missing_spec(path, kind)),
            EnsurePlan::Stamp(declaration) => stamp(data, path, declaration),
        },
    }
}

/// The schema of the prim the property at `path` hangs off, with the
/// property's own name: the pair every schema-declaration lookup starts from
/// (C++ `UsdStage::_GetSchemaProperty`). `None` when `path` is not a property
/// path.
pub(super) fn schema_definition(
    stage: &Stage,
    path: &sdf::Path,
) -> Result<Option<(Arc<PrimTypeInfo>, tf::Token)>, pcp::QueryError> {
    let Some((prim, name)) = path.split_property() else {
        return Ok(None);
    };
    Ok(Some((stage.prim_type_info_composed(prim)?, tf::Token::from(name))))
}

/// Run `f` on the `kind` spec at `path` on the edit-target layer, or return
/// [`sdf::AuthoringError::InvalidPath`] when no such spec exists. `get` is the
/// spec view's constructor (e.g. `sdf::PrimSpecMut::get`). The shared body of
/// the `usd`-tier authoring closures.
pub(super) fn edit_spec<'a, S>(
    data: &'a mut dyn sdf::AbstractData,
    path: sdf::Path,
    kind: sdf::SpecType,
    get: impl FnOnce(&'a mut dyn sdf::AbstractData, sdf::Path) -> Option<S>,
    f: impl FnOnce(&mut S) -> Result<(), StageAuthoringError>,
) -> Result<(), StageAuthoringError> {
    match get(data, path.clone()) {
        Some(mut spec) => f(&mut spec),
        None => Err(missing_spec(&path, kind)),
    }
}

/// The non-creating counterpart of [`edit_spec`]: run `f` on the `kind` spec
/// at `path` when the edit-target layer holds one, do nothing when it holds
/// none, and report a spec of the other kind. The clear operations use it, so
/// removing an opinion never stamps a spec to remove it from.
pub(super) fn edit_existing_spec<'a, S>(
    data: &'a mut dyn sdf::AbstractData,
    path: sdf::Path,
    kind: sdf::SpecType,
    get: impl FnOnce(&'a mut dyn sdf::AbstractData, sdf::Path) -> Option<S>,
    f: impl FnOnce(&mut S) -> Result<(), StageAuthoringError>,
) -> Result<(), StageAuthoringError> {
    match data.spec_type(&path) {
        None => Ok(()),
        Some(found) if found == kind => {
            let mut spec = get(data, path).expect("the kind was checked");
            f(&mut spec)
        }
        Some(found) => Err(kind_mismatch(&path, kind, found)),
    }
}

/// Rejects `key` when a `kind` spec authors it only through a dedicated,
/// validated setter, so the generic metadata calls cannot bypass the
/// invariants those setters keep. This is this crate's authoring
/// restriction, not a fact about the field: C++ `_IsPrivateFieldKey` is a
/// read-side classifier of value, arc and clip fields that does not police
/// `SetMetadata`, and a state only the raw field reaches — a whole-field
/// `timeSamples` block, an empty sample map — is authored on the layer
/// through [`sdf::Layer::edit`].
// TODO: the reserved fields belong in a per-spec-type field definition, the
// counterpart of C++ `SdfSchema::SpecDefinition`, which would also own the
// required-field knowledge `usda::parser::KNOWN_PROPS` keeps. Until then a
// prim's `typeName`, `active`, `hidden`, `kind` and `instanceable` have
// dedicated setters but stay reachable here, since gating them needs the
// matching clear operations first; `spline` joins the attribute list once
// splines are authored.
pub(super) fn check_reserved(kind: sdf::SpecType, key: &'static str) -> Result<(), StageAuthoringError> {
    let reserved: &[sdf::FieldKey] = match kind {
        sdf::SpecType::Attribute => &[
            sdf::FieldKey::Default,
            sdf::FieldKey::TimeSamples,
            sdf::FieldKey::TypeName,
            sdf::FieldKey::ConnectionPaths,
            sdf::FieldKey::Variability,
            sdf::FieldKey::Custom,
        ],
        sdf::SpecType::Relationship => &[
            sdf::FieldKey::TargetPaths,
            sdf::FieldKey::Variability,
            sdf::FieldKey::Custom,
        ],
        _ => &[],
    };
    if reserved.iter().any(|field| field.as_str() == key) {
        return Err(StageAuthoringError::ReservedField { field: key });
    }
    Ok(())
}

/// The declaration the spec at `site` carries, read from that layer with the
/// fallible readers; `wanted` names the kind being authored for the error
/// when the site holds none.
fn declaration_at(
    stage: &Stage,
    site: &SpecSite,
    wanted: sdf::SpecType,
) -> Result<PropertyDeclaration, StageAuthoringError> {
    let layer = stage
        .layer(&site.layer)
        .ok_or_else(|| StageAuthoringError::LayerNotFound {
            layer: site.layer.clone(),
        })?;
    declaration_of(layer.data(), &site.path, wanted)
}

/// The declaration a layer's property spec at `path` carries. An attribute
/// without a `typeName` is [`sdf::ValueTypeError::Empty`], a field holding
/// the wrong variant [`sdf::SpecError::FieldType`], and a decode failure a
/// [`sdf::DataError`]: a malformed declaration is never silently repaired.
fn declaration_of(
    data: &dyn sdf::AbstractData,
    path: &sdf::Path,
    wanted: sdf::SpecType,
) -> Result<PropertyDeclaration, StageAuthoringError> {
    match data.spec_type(path) {
        Some(sdf::SpecType::Attribute) => {
            let spec = sdf::AttributeSpecRef::get(data, path.clone()).expect("the kind was checked");
            Ok(PropertyDeclaration::Attribute {
                type_name: spec.declared_type()?.ok_or(sdf::ValueTypeError::Empty)?,
                variability: spec
                    .typed_field(sdf::FieldKey::Variability, "Variability")?
                    .unwrap_or_default(),
                custom: spec.typed_field(sdf::FieldKey::Custom, "Bool")?.unwrap_or(false),
            })
        }
        Some(sdf::SpecType::Relationship) => {
            let spec = sdf::RelationshipSpecRef::get(data, path.clone()).expect("the kind was checked");
            Ok(PropertyDeclaration::Relationship {
                variability: spec
                    .typed_field(sdf::FieldKey::Variability, "Variability")?
                    .unwrap_or_default(),
                custom: spec.typed_field(sdf::FieldKey::Custom, "Bool")?.unwrap_or(false),
            })
        }
        Some(found) => Err(kind_mismatch(path, wanted, found)),
        None => Err(missing_spec(path, wanted)),
    }
}

fn stamp(
    data: &mut dyn sdf::AbstractData,
    path: &sdf::Path,
    declaration: &PropertyDeclaration,
) -> Result<(), StageAuthoringError> {
    match declaration {
        PropertyDeclaration::Attribute {
            type_name,
            variability,
            custom,
        } => {
            sdf::AttributeSpec::new(data, path.clone(), type_name.clone(), *variability, *custom)?;
        }
        PropertyDeclaration::Relationship { variability, custom } => {
            sdf::RelationshipSpec::new(data, path.clone(), *variability, *custom)?;
        }
    }
    Ok(())
}

fn kind_mismatch(path: &sdf::Path, expected: sdf::SpecType, found: sdf::SpecType) -> StageAuthoringError {
    StageAuthoringError::SpecKindMismatch {
        path: path.clone(),
        expected,
        found,
    }
}

/// The error for a `kind` spec the edit target was expected to hold at
/// `path` and does not.
pub(super) fn missing_spec(path: &sdf::Path, kind: sdf::SpecType) -> StageAuthoringError {
    let reason = match kind {
        sdf::SpecType::Prim => "no prim spec at path on the edit target layer",
        sdf::SpecType::Attribute => "no attribute spec at path on the edit target layer",
        sdf::SpecType::Relationship => "no relationship spec at path on the edit target layer",
        _ => "no spec at path on the edit target layer",
    };
    sdf::AuthoringError::InvalidPath {
        path: path.clone(),
        reason,
    }
    .into()
}
