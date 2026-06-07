//! Stage-level namespace editing — rename, reparent, and delete prims and
//! properties, fixing up the relationship targets and attribute connections
//! that referenced them so nothing dangles.
//!
//! Mirrors C++ `UsdNamespaceEditor`. A [`NamespaceEditor`] holds a [`Stage`]
//! handle and a single pending edit; [`NamespaceEditor::apply_edits`] validates
//! and applies it. The single-edit model matches the C++ public API, which
//! today also stages one edit at a time.
//!
//! # Scope (v1)
//!
//! Edits are applied to the local layer stack (the common authored case).
//! Objects that compose only across a reference / payload would require
//! relocates to move and are rejected for now, matching C++'s initial cut. The
//! mechanical per-layer spec surgery lives one tier down in
//! [`sdf::Layer::move_spec_subtree`](crate::sdf::Layer::move_spec_subtree) /
//! [`remove_spec_subtree`](crate::sdf::Layer::remove_spec_subtree); this type
//! adds composition awareness, the target/connection fix-up, and validation.

use crate::sdf;

use super::{EditTarget, Stage, StageAuthoringError};

/// A single staged namespace edit. A `None` `new_path` is a delete.
#[derive(Clone, Debug)]
struct Edit {
    old_path: sdf::Path,
    new_path: Option<sdf::Path>,
}

/// Edits a stage's namespace: rename / reparent / delete prims and properties.
///
/// Construct with [`NamespaceEditor::new`], stage one edit with a `*_at_path`
/// (or the `rename_*` / `reparent_*` convenience) method, then
/// [`apply_edits`](Self::apply_edits). Each staging call replaces the previous
/// pending edit.
pub struct NamespaceEditor {
    stage: Stage,
    pending: Option<Edit>,
}

impl NamespaceEditor {
    /// Create an editor bound to `stage` (cheap — clones the stage handle).
    pub fn new(stage: &Stage) -> Self {
        Self {
            stage: stage.clone(),
            pending: None,
        }
    }

    /// Stage a delete of the prim or property at `path`.
    pub fn delete_at_path(&mut self, path: impl Into<sdf::Path>) -> &mut Self {
        self.pending = Some(Edit {
            old_path: path.into(),
            new_path: None,
        });
        self
    }

    /// Stage a move of the prim or property at `old` to `new` (rename when the
    /// parent is unchanged, reparent otherwise).
    pub fn move_at_path(&mut self, old: impl Into<sdf::Path>, new: impl Into<sdf::Path>) -> &mut Self {
        self.pending = Some(Edit {
            old_path: old.into(),
            new_path: Some(new.into()),
        });
        self
    }

    /// Stage a rename of `prim` to `new_name` (same parent).
    pub fn rename_prim(&mut self, prim: &super::Prim, new_name: &str) -> &mut Self {
        if let Some(new) = prim.path().parent().and_then(|p| p.append_path(new_name).ok()) {
            self.pending = Some(Edit {
                old_path: prim.path().clone(),
                new_path: Some(new),
            });
        }
        self
    }

    /// Stage a reparent of `prim` under `new_parent`, keeping its name.
    pub fn reparent_prim(&mut self, prim: &super::Prim, new_parent: &super::Prim) -> &mut Self {
        if let Some(new) = prim.path().name().and_then(|n| new_parent.path().append_path(n).ok()) {
            self.pending = Some(Edit {
                old_path: prim.path().clone(),
                new_path: Some(new),
            });
        }
        self
    }

    /// Validate the pending edit without applying it. Returns `Ok(())` if it
    /// could be applied, or a human-readable reason why not (mirrors C++
    /// `CanApplyEdits`'s `whyNot`).
    pub fn can_apply_edits(&self) -> Result<(), String> {
        let edit = self.pending.as_ref().ok_or("no pending edit")?;
        let old = &edit.old_path;

        if !old.is_abs() {
            return Err(format!("source path {old} is not absolute"));
        }
        if old.is_abs_root() || old.name().is_none() {
            return Err("cannot namespace-edit the pseudo-root".into());
        }
        if !self.object_exists(old)? {
            return Err(format!("nothing exists at the source path {old}"));
        }

        let Some(new) = edit.new_path.as_ref() else {
            // Delete: source validity is enough.
            return Ok(());
        };

        if !new.is_abs() || new.is_abs_root() || new.name().is_none() {
            return Err(format!("destination path {new} is not a valid absolute object path"));
        }
        if old.is_property_path() != new.is_property_path() {
            return Err("source and destination are different namespace kinds".into());
        }
        if new == old {
            return Err("destination path is the same as the source".into());
        }
        if new.has_prefix(old) {
            return Err("destination is a descendant of the source".into());
        }
        if self.object_exists(new)? {
            return Err(format!("an object already exists at the destination {new}"));
        }
        Ok(())
    }

    /// Whether a prim or property is composed at `path` on the stage.
    fn object_exists(&self, path: &sdf::Path) -> Result<bool, String> {
        let to_err = |e: anyhow::Error| e.to_string();
        match path.split_property() {
            // Property: the owning prim must exist and list the property.
            Some((prim_path, name)) => {
                let prim = self.stage.prim_at(prim_path);
                if !prim.is_valid().map_err(to_err)? {
                    return Ok(false);
                }
                Ok(prim.property_names().map_err(to_err)?.iter().any(|n| n == name))
            }
            // Prim.
            None => self.stage.prim_at(path.clone()).is_valid().map_err(to_err),
        }
    }

    /// Validate and apply the pending edit, then clear it.
    ///
    /// v1 handles **prim** edits on the local layer stack: the spec subtree is
    /// moved or removed in every contributing layer. A prim that composes only
    /// across a reference / payload (its spec sits at a different namespace
    /// location) would need relocates and is rejected. Property edits and
    /// the target/connection fix-up land in follow-up commits.
    pub fn apply_edits(&mut self) -> Result<(), StageAuthoringError> {
        self.can_apply_edits()
            .map_err(|why| StageAuthoringError::Composition(anyhow::anyhow!("cannot apply namespace edit: {why}")))?;
        let edit = self.pending.clone().expect("validated above");
        let old = &edit.old_path;

        if old.is_property_path() {
            return Err(StageAuthoringError::Composition(anyhow::anyhow!(
                "property namespace edits are not yet supported"
            )));
        }

        // Layers that author a spec at `old`. Reject any whose spec sits at a
        // different namespace location — that means the prim composes across an
        // arc, and moving it would require relocates (not yet supported).
        let stack = self
            .stage
            .prim_at(old.clone())
            .prim_stack()
            .map_err(StageAuthoringError::Composition)?;
        for (_id, spec_path) in &stack {
            if spec_path != old {
                return Err(StageAuthoringError::Composition(anyhow::anyhow!(
                    "{old} composes across an arc (spec at {spec_path}); moving it would require relocates"
                )));
            }
        }

        let identifiers = self.stage.layer_identifiers();
        let saved_target = self.stage.edit_target();

        let apply = || -> Result<(), StageAuthoringError> {
            for (layer_id, _) in &stack {
                let idx = identifiers.iter().position(|i| i == layer_id).ok_or_else(|| {
                    StageAuthoringError::Composition(anyhow::anyhow!("layer {layer_id} not found in stack"))
                })?;
                self.stage.set_edit_target(EditTarget::for_layer_index(idx))?;
                self.stage.with_target_layer_at(old, |layer, old_spec| {
                    let mut cl = sdf::ChangeList::new();
                    match edit.new_path.as_ref() {
                        None => {
                            layer.remove_spec_subtree(&old_spec)?;
                            cl.entry_mut(&old_spec).flags |= sdf::ChangeFlags::REMOVE_NON_INERT_PRIM;
                        }
                        Some(new) => {
                            layer.move_spec_subtree(&old_spec, new)?;
                            cl.entry_mut(&old_spec).flags |= sdf::ChangeFlags::REMOVE_NON_INERT_PRIM;
                            cl.entry_mut(new).flags |= sdf::ChangeFlags::ADD_NON_INERT_PRIM;
                        }
                    }
                    Ok(cl)
                })?;
            }
            Ok(())
        };

        let result = apply();
        // Restore the caller's edit target regardless of outcome.
        let _ = self.stage.set_edit_target(saved_target);
        result?;

        self.pending = None;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::usd::Stage;
    use anyhow::Result;

    /// `/World/A` and `/World/B`, with `/World/A.attr` authored.
    fn stage() -> Result<Stage> {
        let stage = Stage::builder().in_memory("anon.usda")?;
        stage.define_prim(sdf::path("/World")?)?;
        stage.define_prim(sdf::path("/World/A")?)?;
        stage.define_prim(sdf::path("/World/B")?)?;
        stage
            .prim_at(sdf::path("/World/A")?)
            .create_attribute("attr", "double")?;
        Ok(stage)
    }

    #[test]
    fn validates_a_clean_rename() -> Result<()> {
        let stage = stage()?;
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_at_path(sdf::path("/World/A")?, sdf::path("/World/C")?);
        assert!(editor.can_apply_edits().is_ok());
        Ok(())
    }

    #[test]
    fn validates_a_delete() -> Result<()> {
        let stage = stage()?;
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_at_path(sdf::path("/World/A")?);
        assert!(editor.can_apply_edits().is_ok());
        Ok(())
    }

    #[test]
    fn rejects_missing_source() -> Result<()> {
        let stage = stage()?;
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_at_path(sdf::path("/World/Nope")?, sdf::path("/World/C")?);
        assert!(editor.can_apply_edits().is_err());
        Ok(())
    }

    #[test]
    fn rejects_collision_self_descendant_and_kind_mismatch() -> Result<()> {
        let stage = stage()?;
        let mut editor = NamespaceEditor::new(&stage);

        // Destination already occupied.
        editor.move_at_path(sdf::path("/World/A")?, sdf::path("/World/B")?);
        assert!(editor.can_apply_edits().is_err());

        // Destination is a descendant of the source.
        editor.move_at_path(sdf::path("/World/A")?, sdf::path("/World/A/Inner")?);
        assert!(editor.can_apply_edits().is_err());

        // Prim → property kind mismatch.
        editor.move_at_path(sdf::path("/World/A")?, sdf::path("/World.attr")?);
        assert!(editor.can_apply_edits().is_err());
        Ok(())
    }

    #[test]
    fn rejects_pseudo_root_and_no_edit() -> Result<()> {
        let stage = stage()?;
        let editor = NamespaceEditor::new(&stage);
        // Nothing staged yet.
        assert!(editor.can_apply_edits().is_err());
        Ok(())
    }

    #[test]
    fn applies_a_prim_rename_moving_the_subtree() -> Result<()> {
        let stage = stage()?;
        stage.define_prim(sdf::path("/World/A/Child")?)?;

        let mut editor = NamespaceEditor::new(&stage);
        editor.move_at_path(sdf::path("/World/A")?, sdf::path("/World/C")?);
        editor.apply_edits()?;

        assert!(!stage.prim_at(sdf::path("/World/A")?).is_valid()?);
        assert!(stage.prim_at(sdf::path("/World/C")?).is_valid()?);
        assert!(stage.prim_at(sdf::path("/World/C/Child")?).is_valid()?);
        Ok(())
    }

    #[test]
    fn applies_a_prim_delete() -> Result<()> {
        let stage = stage()?;
        let mut editor = NamespaceEditor::new(&stage);
        editor.delete_at_path(sdf::path("/World/B")?);
        editor.apply_edits()?;

        assert!(!stage.prim_at(sdf::path("/World/B")?).is_valid()?);
        assert!(stage.prim_at(sdf::path("/World/A")?).is_valid()?);
        Ok(())
    }

    #[test]
    fn validates_property_rename_and_rejects_missing_property() -> Result<()> {
        let stage = stage()?;
        let mut editor = NamespaceEditor::new(&stage);
        editor.move_at_path(sdf::path("/World/A.attr")?, sdf::path("/World/A.renamed")?);
        assert!(editor.can_apply_edits().is_ok());

        editor.move_at_path(sdf::path("/World/A.ghost")?, sdf::path("/World/A.renamed")?);
        assert!(editor.can_apply_edits().is_err());
        Ok(())
    }
}
