//! Stage-composed relationship handle — a value-type wrapper around
//! `(stage, path)` that mirrors C++ `UsdRelationship`.
//!
//! Like [`Prim`], the handle is freely [`Clone`], holds no borrow on the
//! composition cache, and re-acquires state from the [`Stage`] per call. Its
//! fluent setters take `self` by value and return `Self`, so writes chain in a
//! single statement that ends with the final handle bound.

use super::{Prim, Stage, StageAuthoringError};
use crate::sdf;

/// Stage-composed relationship handle. Mirrors C++ `UsdRelationship`.
///
/// Returned by [`Stage::create_relationship`] / [`Prim::create_relationship`]
/// with defaults `variability = Varying`, `custom = true`, matching C++
/// generic property authoring. Override via the fluent setters below.
#[derive(Clone)]
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
        self.edit(&[sdf::FieldKey::Variability], false, |spec| {
            spec.add(sdf::FieldKey::Variability, sdf::Value::Variability(v))
        })
    }

    /// Set the relationship's `custom` flag. Always authors an explicit
    /// opinion (see [`Attribute::set_variability`] for rationale).
    ///
    /// [`Attribute::set_variability`]: crate::usd::Attribute::set_variability
    pub fn set_custom(self, custom: bool) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::Custom], false, |spec| {
            spec.add(sdf::FieldKey::Custom, sdf::Value::Bool(custom))
        })
    }

    /// `true` when this relationship is composed as `custom`. Mirrors C++
    /// `UsdProperty::IsCustom`; an unauthored `custom` field resolves to
    /// `false`.
    pub fn is_custom(&self) -> anyhow::Result<bool> {
        Ok(self
            .stage
            .field::<bool>(&self.path, sdf::FieldKey::Custom)?
            .unwrap_or(false))
    }

    /// Append a target path. No-op if already present.
    pub fn add_target(self, target: sdf::Path) -> Result<Self, StageAuthoringError> {
        self.edit(&[sdf::FieldKey::TargetPaths], true, |spec| spec.add_target(target))
    }

    /// Replace the entire target list.
    pub fn set_targets<I: IntoIterator<Item = sdf::Path>>(self, targets: I) -> Result<Self, StageAuthoringError> {
        let targets: Vec<sdf::Path> = targets.into_iter().collect();
        self.edit(&[sdf::FieldKey::TargetPaths], true, |spec| {
            spec.set_target_paths(targets)
        })
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
    /// [`Attribute::set_metadata`]: crate::usd::Attribute::set_metadata
    pub fn set_metadata(self, key: &'static str, value: impl Into<sdf::Value>) -> Result<Self, StageAuthoringError> {
        let value = value.into();
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_relationship_mut()) {
                Some(mut spec) => {
                    spec.add(key, value);
                    let mut cl = sdf::ChangeList::new();
                    cl.entry_mut(&path).info_changed.insert(key);
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no relationship spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
    }

    /// Remove a target path. Returns `Ok(true)` if it was present. Takes
    /// `&self` rather than consuming — `remove_target` returns a `bool` (not
    /// `Self`), so it doesn't fit the chain pattern. Skips cache invalidation
    /// when the target wasn't authored (no mutation occurred).
    pub fn remove_target(&self, target: &sdf::Path) -> Result<bool, StageAuthoringError> {
        let target = target.clone();
        let mut removed = false;
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_relationship_mut()) {
                Some(mut spec) => {
                    removed = spec.remove_target(&target);
                    let mut cl = sdf::ChangeList::new();
                    if removed {
                        let entry = cl.entry_mut(&path);
                        entry.flags |= sdf::ChangeFlags::CHANGE_RELATIONSHIP_TARGETS;
                        entry.info_changed.insert(sdf::FieldKey::TargetPaths.as_str());
                    }
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no relationship spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(removed)
    }

    /// `true` when any target opinion is authored — including an
    /// explicit-empty list op (`rel r = []`), the canonical way to block
    /// weaker-layer targets. Mirrors C++ `UsdRelationship::HasAuthoredTargets`.
    pub fn has_authored_targets(&self) -> anyhow::Result<bool> {
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
    pub fn targets(&self) -> anyhow::Result<Vec<sdf::Path>> {
        self.stage
            .masked(&self.path, |g, cache| cache.relationship_targets(g, &self.path))
    }

    /// Composes this relationship's target paths together with the paths its
    /// list-op deletes, returned as `(targets, deleted)` (C++
    /// `PcpBuildFilteredTargetIndex` and its `deletedPaths` out-param). The
    /// targets match [`Relationship::targets`]; both are empty when the
    /// owning prim is outside the population mask.
    pub fn compute_targets(&self) -> anyhow::Result<(Vec<sdf::Path>, Vec<sdf::Path>)> {
        self.stage.masked(&self.path, |g, cache| {
            cache.compute_relationship_target_paths(g, &self.path)
        })
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
    pub fn forwarded_targets(&self) -> anyhow::Result<Vec<sdf::Path>> {
        let mask = self.stage.mask();
        self.stage.masked(&self.path, |g, cache| {
            cache.forwarded_relationship_targets(g, &self.path, &|p| mask.includes(p))
        })
    }

    /// Returns the property stack: each `(layer identifier, spec path)` site
    /// that authors a spec for this relationship, strongest first. Mirrors C++
    /// `UsdProperty::GetPropertyStack`.
    pub fn property_stack(&self) -> anyhow::Result<Vec<(String, sdf::Path)>> {
        self.stage.with_cache(|g, c| c.property_stack(g, &self.path))
    }

    /// Borrow the relationship spec at `self.path` on the edit target's
    /// layer, apply `f`, and return `self` for chaining. `fields` names the
    /// authored metadata keys; `targets_changed` sets the target-list flag
    /// in the change list. See [`Prim::edit`] for the `ReadOnly` vs
    /// `InvalidPath` discrimination.
    //
    // The change-list entry is recorded at the relationship's property
    // path, which `pcp::Changes::did_change` currently skips (no consumer
    // for relationship-target invalidation). Flag and `info_changed`
    // opinions are still emitted here so the producer side is in place
    // when a consumer lands.
    //
    // TODO: wire the consumer. When `IndexCache` starts memoizing per-attribute
    // composed values or per-relationship resolved-target lists:
    //   1. Add a `classify_property_entry` branch in `pcp/change.rs`
    //      mirroring `classify_prim_entry`, gated on
    //      `path.is_property_path()`. Inspect
    //      `entry.flags & CHANGE_RELATIONSHIP_TARGETS` and the
    //      `TargetPaths` / `ConnectionPaths` keys in `info_changed`.
    //   2. Decide tier: relationship/connection target list changes
    //      are conceptually tier-3 (spec-stack refresh) — they don't
    //      reshape the prim graph but they do invalidate composed
    //      target resolution. Insert the owning prim path into
    //      `did_change_specs` (or a new `did_change_targets` set keyed
    //      by property path).
    //   3. Extend `Changes::apply` to consume the new set by either
    //      dropping the owner's resolved-target cache or refreshing it
    //      in place. The current `did_change_specs` field is already
    //      reserved for this; right now the entry is dropped on the
    //      floor (see CacheChanges docs).
    //   4. Remove the `targets_changed` parameter from `edit` and the
    //      flag emission here if the classifier ends up not needing
    //      either signal (e.g. it can infer everything from
    //      `info_changed[TargetPaths]`). Until then both stay for
    //      forward-compat.
    fn edit<F>(self, fields: &[sdf::FieldKey], targets_changed: bool, f: F) -> Result<Self, StageAuthoringError>
    where
        F: FnOnce(&mut sdf::RelationshipSpecMut<'_>),
    {
        let info_changed: Vec<&'static str> = fields.iter().map(sdf::FieldKey::as_str).collect();
        self.stage.with_target_layer_at(&self.path, |layer, path| {
            let data = layer.writable_data_mut()?;
            match data.spec_mut(&path).and_then(|s| s.as_relationship_mut()) {
                Some(mut spec) => {
                    f(&mut spec);
                    let mut cl = sdf::ChangeList::new();
                    let entry = cl.entry_mut(&path);
                    if targets_changed {
                        entry.flags |= sdf::ChangeFlags::CHANGE_RELATIONSHIP_TARGETS;
                    }
                    for name in &info_changed {
                        entry.info_changed.insert(name);
                    }
                    Ok(cl)
                }
                None => Err(sdf::AuthoringError::InvalidPath {
                    path: path.clone(),
                    reason: "no relationship spec at path on the edit target layer",
                }),
            }
        })?;
        Ok(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::sdf;
    use crate::usd::Stage;

    fn stage() -> anyhow::Result<Stage> {
        Stage::builder().in_memory("anon.usda")
    }

    #[test]
    fn relationship_chain() -> anyhow::Result<()> {
        let stage = stage()?;
        let mesh = stage.define_prim("/World/Mesh")?.set_type_name("Mesh")?;
        stage.define_prim("/World/Material")?.set_type_name("Material")?;
        stage.define_prim("/World/Material2")?.set_type_name("Material")?;
        let binding = mesh
            .create_relationship("material:binding")?
            .set_variability(sdf::Variability::Uniform)?
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
    fn relationship_targets() -> anyhow::Result<()> {
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
    fn relationship_targets_unauthored() -> anyhow::Result<()> {
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
    fn forwarded_targets_spec_example() -> anyhow::Result<()> {
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
    fn forwarded_targets_multi_hop() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let p = stage.define_prim("/P")?;
        p.create_relationship("c")?.set_targets([sdf::path("/Geom")?])?;
        p.create_relationship("b")?.set_targets([sdf::path("/P.c")?])?;
        let a = p.create_relationship("a")?.set_targets([sdf::path("/P.b")?])?;

        assert_eq!(a.forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// A deep relationship chain forwards without overflowing the call stack
    /// (the iterative walk must finish where recursion would abort).
    #[test]
    fn forwarded_targets_deep_chain() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let host = stage.define_prim("/Host")?;
        const N: usize = 4_000;
        // r0 -> r1 -> ... -> r{N-1} -> /Geom, all relationships on one prim.
        let r0 = host.create_relationship("r0")?.set_targets([sdf::path("/Host.r1")?])?;
        for i in 1..N - 1 {
            host.create_relationship(format!("r{i}"))?
                .set_targets([sdf::path(format!("/Host.r{}", i + 1))?])?;
        }
        host.create_relationship(format!("r{}", N - 1))?
            .set_targets([sdf::path("/Geom")?])?;

        assert_eq!(r0.forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// Forwarding picks up a relationship authored AFTER a target was first
    /// queried: the earlier query must not cache a stale "not a relationship"
    /// verdict for the target path.
    #[test]
    fn forwarded_targets_after_target_authored() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let p = stage.define_prim("/P")?;
        let a = p.create_relationship("a")?.set_targets([sdf::path("/P.b")?])?;

        // /P.b is not a relationship yet -> a forwards to the raw path /P.b.
        assert_eq!(a.forwarded_targets()?, vec![sdf::path("/P.b")?]);

        // Author /P.b as a relationship; forwarding must now follow it.
        p.create_relationship("b")?.set_targets([sdf::path("/Geom")?])?;
        assert_eq!(a.forwarded_targets()?, vec![sdf::path("/Geom")?]);
        Ok(())
    }

    /// A target that does not resolve to a relationship is kept as-is, even
    /// when it has no spec at all (dangling path), matching C++ which forwards
    /// only through live relationships.
    #[test]
    fn forwarded_targets_keeps_dangling() -> anyhow::Result<()> {
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
    fn forwarded_targets_dedup() -> anyhow::Result<()> {
        let stage = stage()?;
        stage.define_prim("/Geom")?;
        let p = stage.define_prim("/P")?;
        p.create_relationship("b")?.set_targets([sdf::path("/Geom")?])?;
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
    fn forwarded_targets_cycle() -> anyhow::Result<()> {
        let stage = stage()?;
        let p = stage.define_prim("/P")?;
        let a = p.create_relationship("a")?.set_targets([sdf::path("/P.b")?])?;
        p.create_relationship("b")?.set_targets([sdf::path("/P.a")?])?;

        assert!(a.forwarded_targets()?.is_empty());
        Ok(())
    }
}
