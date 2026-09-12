//! Stage-composed relationship handle — a value-type wrapper around
//! `(stage, path)` that mirrors C++ `UsdRelationship`.
//!
//! Like [`Prim`], the handle is freely [`Clone`], holds no borrow on the
//! composition cache, and re-acquires state from the [`Stage`] per call. Its
//! fluent setters take `self` by value and return `Self`, so writes chain in a
//! single statement that ends with the final handle bound.

use super::{Prim, SpecSite, Stage, StageAuthoringError, StageEdit, authoring};
use crate::Result;
use crate::{pcp, sdf};

/// A relationship to author, and everything it is authored with.
///
/// The relationship counterpart of [`AttributeBuilder`](super::AttributeBuilder):
/// creating the relationship, declaring it and giving it targets are one edit
/// of the target layer, and nothing reaches the stage until
/// [`build`](Self::build). A relationship carries no type and is always
/// uniform, so [`custom`](Self::custom) is all there is to declare about one.
///
/// A builder from [`Prim`] or [`Stage`] commits on its own; one from a
/// [`PrimEdit`](super::PrimEdit) or a [`StageEdit`](super::StageEdit) joins
/// that transaction instead.
#[derive(Debug)]
pub struct RelationshipBuilder<'a> {
    /// The stage and the property path to author at, or what naming them — or
    /// naming a target — hit. The failure is carried so the setters need not
    /// answer for it.
    site: Result<(Stage, sdf::Path), StageAuthoringError>,
    custom: bool,
    /// The targets to author in the same edit.
    targets: Option<Vec<sdf::Path>>,
    /// The transaction to join, where the builder came from one.
    batch: Option<&'a StageEdit>,
}

impl<'a> RelationshipBuilder<'a> {
    /// A relationship at `site`, declared as C++ declares one a caller says
    /// nothing more about.
    pub(super) fn new(site: Result<(Stage, sdf::Path), StageAuthoringError>) -> Self {
        RelationshipBuilder {
            site,
            custom: true,
            targets: None,
            batch: None,
        }
    }

    /// The same relationship, authored as part of `batch` rather than on its
    /// own.
    pub(super) fn in_batch(mut self, batch: &'a StageEdit) -> Self {
        self.batch = Some(batch);
        self
    }

    /// Whether the relationship is the caller's own rather than a schema's
    /// (C++ `custom`). A schema's property is not.
    pub fn custom(mut self, custom: bool) -> Self {
        self.custom = custom;
        self
    }

    /// The target list to author with it: [`Relationship::set_targets`] as
    /// part of the creating edit rather than an edit after it.
    pub fn set_targets(mut self, targets: impl IntoIterator<Item: sdf::IntoPath>) -> Self {
        match targets
            .into_iter()
            .map(sdf::try_into_path)
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(targets) => self.targets = Some(targets),
            Err(err) => self.site = Err(err.into()),
        }
        self
    }

    /// Authors the relationship and hands back the handle that reads and
    /// edits it, as one edit of the target layer.
    ///
    /// A builder that came from a [`PrimEdit`](super::PrimEdit) or a
    /// [`StageEdit`](super::StageEdit) is queued into that transaction instead,
    /// and the handle reads nothing until the transaction commits.
    pub fn build(mut self) -> Result<Relationship, StageAuthoringError> {
        let batch = self.batch.take();
        if let Some(batch) = batch {
            batch.holds_target()?;
        }
        let planned = self.plan()?;
        let (stage, path) = match batch {
            Some(batch) => batch.queue(planned)?,
            None => planned.commit()?,
        };
        Ok(Relationship::new(&stage, path))
    }

    /// Resolves everything the write depends on against composed state, so all
    /// the transaction has left to do is stamp the spec and write.
    fn plan(self) -> Result<authoring::PlannedProperty, StageAuthoringError> {
        let (stage, path) = self.site?;
        let declaration = authoring::PropertyDeclaration::Relationship {
            variability: sdf::Variability::Uniform,
            custom: self.custom,
        };
        let ensure = authoring::plan_property_spec(&stage, &path, sdf::SpecType::Relationship, Some(declaration))?;
        Ok(authoring::PlannedProperty::new(
            stage,
            path,
            authoring::PropertyWrite::Relationship {
                ensure,
                targets: self.targets,
            },
        ))
    }
}

/// Stage-composed relationship handle. Mirrors C++ `UsdRelationship`.
///
/// Returned by [`Stage::create_relationship`] / [`Prim::create_relationship`],
/// which declare it as C++ generic property authoring does — `custom = true`,
/// and a relationship is always uniform — or by a [`RelationshipBuilder`]
/// where it is declared as something else. The fluent setters below edit a
/// relationship that already exists.
#[derive(Clone, Debug)]
pub struct Relationship {
    stage: Stage,
    path: sdf::Path,
}

impl Relationship {
    pub(super) fn new(stage: &Stage, path: sdf::Path) -> Self {
        Self {
            stage: stage.clone(),
            path,
        }
    }

    /// Composed namespace path of the relationship.
    pub fn path(&self) -> &sdf::Path {
        &self.path
    }

    /// The stage this handle is anchored to.
    pub fn stage(&self) -> &Stage {
        &self.stage
    }

    /// Handle to the owning prim.
    pub fn prim(&self) -> Prim {
        Prim::new(&self.stage, self.path.prim_path())
    }

    /// Set the relationship's `variability` field. Always authors an
    /// explicit opinion (see [`Attribute::set_variability`] for rationale).
    ///
    /// [`Attribute::set_variability`]: crate::usd::Attribute::set_variability
    pub fn set_variability(self, v: sdf::Variability) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| {
            spec.set(sdf::FieldKey::Variability.as_str(), sdf::Value::Variability(v));
            Ok(())
        })
    }

    /// Set the relationship's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for rationale).
    ///
    /// [`Attribute::set_variability`]: crate::usd::Attribute::set_variability
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(|spec| {
            spec.set(sdf::FieldKey::Custom.as_str(), sdf::Value::Bool(custom));
            Ok(())
        })
    }

    /// `true` when this relationship is composed as `custom`. Mirrors C++
    /// `UsdProperty::IsCustom`; an unauthored `custom` field resolves to
    /// `false`.
    pub fn is_custom(&self) -> Result<bool> {
        // A property a schema declares is never custom — that is what `custom`
        // means — so an authored opinion on one is ignored, exactly as for an
        // attribute (C++ `UsdStage::_GetPropCustomImpl` covers both).
        if self.schema_declared()? {
            return Ok(false);
        }
        Ok(self
            .stage
            .field::<bool>(&self.path, sdf::FieldKey::Custom)?
            .unwrap_or(false))
    }

    /// Whether a schema of the owning prim declares this relationship.
    fn schema_declared(&self) -> Result<bool, pcp::QueryError> {
        let Some((info, name)) = authoring::schema_definition(&self.stage, &self.path)? else {
            return Ok(false);
        };
        Ok(info
            .prim_definition()
            .property(&name)
            .is_some_and(|property| property.spec_type() == sdf::SpecType::Relationship))
    }

    /// Append a target path. No-op if already present.
    pub fn add_target(self, target: impl sdf::IntoPath) -> Result<Self, StageAuthoringError> {
        let target = sdf::try_into_path(target)?;
        self.edit(|spec| Ok(spec.add_target(target)?))
    }

    /// Replace the entire target list.
    pub fn set_targets(self, targets: impl IntoIterator<Item: sdf::IntoPath>) -> Result<Self, StageAuthoringError> {
        let targets: Vec<sdf::Path> = targets.into_iter().map(sdf::try_into_path).collect::<Result<_, _>>()?;
        self.edit(|spec| Ok(spec.set_target_paths(targets)?))
    }

    /// Author a generic metadata field on the relationship spec.
    /// Sibling of [`Attribute::set_metadata`]; used for relationship
    /// metadata the dedicated setters don't cover, e.g. UsdShade's
    /// `bindMaterialAs` binding-strength token on a `material:binding`
    /// relationship.
    ///
    /// `key` is `&'static str` so the change-tracking layer can record
    /// it without copying — pass a `pub const` token, not a runtime
    /// string.
    ///
    /// `value` is in stage time, so any `timecode` it holds is mapped into the
    /// edit target's own time frame (C++ `_StageValueToFieldXf`).
    ///
    /// [`Attribute::set_metadata`]: crate::usd::Attribute::set_metadata
    pub fn set_metadata(self, key: &'static str, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        authoring::check_reserved(sdf::SpecType::Relationship, key)?;
        let value = self.stage.map_to_spec_value(&self.path, value);
        self.edit(|spec| {
            spec.set(key, value);
            Ok(())
        })
    }

    /// Erase the local `targetPaths` opinion on the edit target (C++
    /// `UsdRelationship::ClearTargets` without removing the spec): the targets
    /// weaker layers author compose again, unlike after `set_targets([])`,
    /// which authors an explicit empty list that blocks them. A target
    /// holding no spec is left alone; an attribute at the path is an error.
    pub fn clear_targets(self) -> Result<Self, StageAuthoringError> {
        authoring::edit_existing::<Self>(&self.stage, &self.path, |spec| {
            spec.erase(sdf::FieldKey::TargetPaths.as_str());
            Ok(())
        })?;
        Ok(self)
    }

    /// Remove a target path. Returns `Ok(true)` if it was present. Takes
    /// `&self` rather than consuming — `remove_target` returns a `bool` (not
    /// `Self`), so it doesn't fit the chain pattern. Skips cache invalidation
    /// when the target wasn't authored (no mutation occurred).
    pub fn remove_target(&self, target: impl sdf::IntoPath) -> Result<bool, StageAuthoringError> {
        let target = sdf::try_into_path(target)?;
        let mut removed = false;
        authoring::author::<Self>(&self.stage, &self.path, |spec| {
            removed = spec.remove_target(&target);
            Ok(())
        })?;
        Ok(removed)
    }

    /// `true` when any target opinion is authored — including an
    /// explicit-empty list op (`rel r = []`), the canonical way to block
    /// weaker-layer targets. Mirrors C++ `UsdRelationship::HasAuthoredTargets`.
    pub fn has_authored_targets(&self) -> Result<bool> {
        Ok(self
            .stage
            .field::<sdf::Value>(&self.path, sdf::FieldKey::TargetPaths)?
            .is_some())
    }

    /// Composed raw `targetPaths`, with list-op edits folded across every
    /// contributing layer (prepend / append / add / delete). These are the raw
    /// targets (spec 12.4); target forwarding is not applied — see
    /// [`Self::forwarded_targets`]. Returns an empty vec for a non-property
    /// path, an unauthored relationship, or an owning prim outside the
    /// population mask. Mirrors C++ `UsdRelationship::GetTargets`.
    pub fn targets(&self) -> Result<Vec<sdf::Path>> {
        Ok(self
            .stage
            .masked(&self.path, |g, cache| cache.relationship_targets(g, &self.path))?)
    }

    /// Composes this relationship's target paths together with the paths its
    /// list-op deletes, returned as `(targets, deleted)` (C++
    /// `PcpBuildFilteredTargetIndex` and its `deletedPaths` out-param). The
    /// targets match [`Relationship::targets`]; both are empty when the
    /// owning prim is outside the population mask.
    pub fn compute_targets(&self) -> Result<(Vec<sdf::Path>, Vec<sdf::Path>)> {
        Ok(self.stage.masked(&self.path, |g, cache| {
            cache.compute_relationship_target_paths(g, &self.path)
        })?)
    }

    /// Composed forwarded targets: a target that resolves to another
    /// relationship is replaced, recursively, by that relationship's forwarded
    /// targets; every other target is kept as-is, including prim paths,
    /// attribute paths, and dangling paths (spec 12.4). Cycles are broken and
    /// duplicates collapse. Forwarding honors the population mask — a target
    /// relationship on a prim outside the working set is not followed, while a
    /// directly-reached terminal outside the mask is still returned, matching
    /// raw [`Self::targets`]. Mirrors C++
    /// `UsdRelationship::GetForwardedTargets`.
    pub fn forwarded_targets(&self) -> Result<Vec<sdf::Path>> {
        Ok(self.stage.masked(&self.path, |g, cache| {
            cache.forwarded_relationship_targets(g, &self.path)
        })?)
    }

    /// Every spec that authors an opinion for this relationship, strongest
    /// first, each with the cumulative layer offset that reaches it. Mirrors
    /// C++ `UsdProperty::GetPropertyStack`.
    ///
    /// Takes no time, unlike
    /// [`Attribute::property_stack_at`](super::Attribute::property_stack_at):
    /// only value clips make a stack time-dependent, and they source attributes.
    pub fn property_stack(&self) -> Result<Vec<SpecSite>> {
        self.stage.property_stack(&self.path, None)
    }

    /// Borrow the relationship spec at `self.path` on the edit target's
    /// layer, apply `f`, and return `self` for chaining. The layer records
    /// whatever fields `f` writes, setting `CHANGE_RELATIONSHIP_TARGETS` when
    /// the write touches `targetPaths`. That flag is what routes the edit to
    /// `pcp::Changes::effects_of`'s property branch, which drops the affected prims'
    /// memoized resolved targets (the owner and each dependent that reads the
    /// site through an arc) so the next query recomposes them.
    /// Returns `InvalidPath` if nothing declares the relationship at all.
    fn edit<F>(self, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::RelationshipSpecMut<'_>) -> Result<(), StageAuthoringError>,
    {
        authoring::author::<Self>(&self.stage, &self.path, f)?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::Result;
    use crate::sdf;
    use crate::usd::Stage;

    fn stage() -> Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    #[test]
    fn relationship_chain() -> Result<()> {
        let stage = stage()?;
        let mesh = stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        stage.define_prim("/World/Material")?.set_type_name("Material")?;
        stage.define_prim("/World/Material2")?.set_type_name("Material")?;
        let binding = mesh
            .create_relationship("material:binding")?
            .add_target(sdf::Path::new("/World/Material")?)?
            .add_target(sdf::Path::new("/World/Material2")?)?;
        assert!(binding.remove_target(&sdf::Path::new("/World/Material2")?)?);
        assert_eq!(stage.spec_type(binding.path())?, Some(sdf::SpecType::Relationship));
        assert_eq!(
            stage.field::<sdf::Value>(binding.path(), sdf::FieldKey::Custom)?,
            Some(sdf::Value::Bool(true)),
        );
        Ok(())
    }

    #[test]
    fn relationship_targets() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/World/Material")?.set_type_name("Material")?;
        stage.define_prim("/World/Material2")?.set_type_name("Material")?;
        let mesh = stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;

        let binding = mesh
            .create_relationship("material:binding")?
            .add_target(sdf::Path::new("/World/Material")?)?
            .add_target(sdf::Path::new("/World/Material2")?)?;
        assert!(binding.has_authored_targets()?);
        assert_eq!(
            binding.targets()?,
            vec![sdf::Path::new("/World/Material")?, sdf::Path::new("/World/Material2")?]
        );

        // Removing a target updates the composed list.
        assert!(binding.remove_target(&sdf::Path::new("/World/Material2")?)?);
        assert_eq!(binding.targets()?, vec![sdf::Path::new("/World/Material")?]);
        Ok(())
    }

    #[test]
    fn relationship_targets_unauthored() -> Result<()> {
        let stage = stage()?;
        let rel = stage
            .define_prim("/World/Mesh")?
            .set_type_name("Mesh")?
            .create_relationship("material:binding")?;
        assert!(!rel.has_authored_targets()?);
        assert!(rel.targets()?.is_empty());
        Ok(())
    }

    /// Spec 12.4 example: `/foo.myRel` targets a prim and a relationship; the
    /// relationship forwards to two prims. Forwarding flattens the chain to
    /// only prim/attribute paths, while the raw targets keep the relationship.
    #[test]
    fn forwarded_targets_spec_example() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/foo")?;
        stage.define_prim("/foo/bar")?;
        stage.define_prim("/foo/foobar")?;
        stage.define_prim("/foo/foobar/barbaz")?;
        stage
            .define_prim("/baz")?
            .create_relationship("bazrel")?
            .set_targets([sdf::path("/foo/foobar")?, sdf::path("/foo/foobar/barbaz")?])?;
        let my_rel = stage
            .define_prim("/foo")?
            .create_relationship("myRel")?
            .set_targets([sdf::path("/foo/bar")?, sdf::path("/baz.bazrel")?])?;

        assert_eq!(
            my_rel.forwarded_targets()?,
            vec![
                sdf::path("/foo/bar")?,
                sdf::path("/foo/foobar")?,
                sdf::path("/foo/foobar/barbaz")?,
            ]
        );
        assert_eq!(
            my_rel.targets()?,
            vec![sdf::path("/foo/bar")?, sdf::path("/baz.bazrel")?]
        );
        Ok(())
    }

    /// Forwarding follows a multi-hop relationship chain to its terminal prim.
    #[test]
    fn forwarded_targets_multi_hop() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let p = stage.define_prim("/P")?;
        p.create_relationship("c")?.set_targets(["/Geom"])?;
        p.create_relationship("b")?.set_targets(["/P.c"])?;
        let a = p.create_relationship("a")?.set_targets(["/P.b"])?;

        assert_eq!(a.forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// A deep relationship chain forwards without overflowing the call stack
    /// (the iterative walk must finish where recursion would abort).
    #[test]
    fn forwarded_targets_deep_chain() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let host = stage.define_prim("/Host")?;
        const N: usize = 4_000;
        // r0 -> r1 -> ... -> r{N-1} -> /Geom, all relationships on one prim.
        let r0 = host.create_relationship("r0")?.set_targets(["/Host.r1"])?;
        for i in 1..N - 1 {
            host.create_relationship(format!("r{i}"))?
                .set_targets([sdf::path(format!("/Host.r{}", i + 1))?])?;
        }
        host.create_relationship(format!("r{}", N - 1))?
            .set_targets(["/Geom"])?;

        assert_eq!(r0.forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// Forwarding picks up a relationship authored AFTER a target was first
    /// queried: the earlier query must not cache a stale "not a relationship"
    /// verdict for the target path.
    #[test]
    fn forwarded_targets_after_target_authored() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let p = stage.define_prim("/P")?;
        let a = p.create_relationship("a")?.set_targets(["/P.b"])?;

        // /P.b is not a relationship yet -> a forwards to the raw path /P.b.
        assert_eq!(a.forwarded_targets()?, vec![sdf::path("/P.b")?]);

        // Author /P.b as a relationship; forwarding must now follow it.
        p.create_relationship("b")?.set_targets(["/Geom"])?;
        assert_eq!(a.forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// A target that does not resolve to a relationship is kept as-is, even
    /// when it has no spec at all (dangling path), matching C++ which forwards
    /// only through live relationships.
    #[test]
    fn forwarded_targets_keeps_dangling() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let a = stage
            .define_prim("/P")?
            .create_relationship("a")?
            .set_targets([sdf::path("/Geom")?, sdf::path("/Nowhere.rel")?])?;

        assert_eq!(
            a.forwarded_targets()?,
            vec![sdf::path("/Geom")?, sdf::path("/Nowhere.rel")?]
        );
        Ok(())
    }

    /// Terminals reachable through multiple relationship paths collapse to a
    /// single first-occurrence entry.
    #[test]
    fn forwarded_targets_dedup() -> Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let p = stage.define_prim("/P")?;
        p.create_relationship("b")?.set_targets(["/Geom"])?;
        let a = p
            .create_relationship("a")?
            .set_targets([sdf::path("/Geom")?, sdf::path("/P.b")?])?;

        // /Geom is reached directly and again via /P.b; it appears once.
        assert_eq!(a.forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// A pure relationship cycle forwards to no terminal targets without
    /// hanging.
    #[test]
    fn forwarded_targets_cycle() -> Result<()> {
        let stage = stage()?;
        let p = stage.define_prim("/P")?;
        let a = p.create_relationship("a")?.set_targets(["/P.b"])?;
        p.create_relationship("b")?.set_targets(["/P.a"])?;

        assert!(a.forwarded_targets()?.is_empty());
        Ok(())
    }
}
