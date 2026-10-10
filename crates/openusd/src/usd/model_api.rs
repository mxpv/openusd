//! Kind queries on the model view (C++ `UsdModelAPI`).
//!
//! [`ModelAPI`] reads and writes a prim's `kind`, and asks whether the prim is
//! a model or a group, through the [`Prim`](super::Prim) it derefs to. What
//! this module adds is [`ModelAPI::is_kind`], the one query that takes the
//! kind to compare against.

use crate::Result;

use super::ModelAPI;

/// Whether [`ModelAPI::is_kind`] holds a model kind to the model hierarchy
/// (C++ `UsdModelAPI::KindValidation`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum KindValidation {
    /// Compare the prim's kind with the kind asked about, wherever the prim
    /// sits (C++ `KindValidationNone`).
    None,
    /// A prim is of a model kind only when it is a model, so one whose
    /// ancestors break the model hierarchy is of none (C++
    /// `KindValidationModelHierarchy`).
    #[default]
    ModelHierarchy,
}

impl ModelAPI {
    /// Whether the prim's `kind` is `base` or derives from it, by the stage's
    /// [`kind::Registry`](crate::kind::Registry) (C++ `UsdModelAPI::IsKind`).
    ///
    /// Under [`KindValidation::ModelHierarchy`] a `base` that is a model kind
    /// is answered `false` for a prim that is not a model. A `base` outside
    /// the model kinds, such as `subcomponent`, is compared the same way
    /// under either validation.
    ///
    /// ```
    /// use openusd::usd::{KindValidation, ModelAPI, Stage};
    ///
    /// let stage = Stage::builder().in_memory("root.usda")?;
    /// stage.define_prim("/Set")?.set_kind("assembly")?;
    /// let set = ModelAPI::from_prim_unchecked(stage.prim("/Set")?);
    /// assert!(set.is_kind("group", KindValidation::ModelHierarchy)?);
    /// # Ok::<(), openusd::Error>(())
    /// ```
    pub fn is_kind(&self, base: &str, validation: KindValidation) -> Result<bool> {
        let kinds = self.stage().schema_registry().kinds();
        if !self.kind()?.is_some_and(|kind| kinds.is_a(&kind, base)) {
            return Ok(false);
        }
        // Asked last: whether the prim is a model takes a walk up its
        // ancestors, and most prims are not of the kind asked about.
        Ok(validation == KindValidation::None || !kinds.is_model(base) || self.is_model()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::kind;
    use crate::usd::{SchemaFamily, SchemaRegistry, Stage};

    use KindValidation::{ModelHierarchy, None as Unvalidated};

    fn model(stage: &Stage, path: &str) -> Result<ModelAPI> {
        Ok(ModelAPI::from_prim_unchecked(stage.prim(path)?))
    }

    /// The cases of C++ `testUsdModel.py`.
    #[test]
    fn is_kind_validation() -> Result<()> {
        let stage = Stage::builder().in_memory("model.usda")?;
        stage.define_prim("/Parent")?;
        stage.define_prim("/Parent/Child")?.set_kind("component")?;

        // A component under a non-model is of its kind only unvalidated.
        let child = model(&stage, "/Parent/Child")?;
        assert!(!child.is_model()?);
        assert!(!child.is_kind("component", ModelHierarchy)?);
        assert!(!child.is_kind("model", ModelHierarchy)?);
        assert!(child.is_kind("component", Unvalidated)?);
        assert!(child.is_kind("model", Unvalidated)?);

        // Under an assembly it is a model, and of its kind either way.
        stage.prim("/Parent")?.set_kind("assembly")?;
        assert!(child.is_model()?);
        assert!(child.is_kind("component", ModelHierarchy)?);
        assert!(child.is_kind("model", ModelHierarchy)?);
        let parent = model(&stage, "/Parent")?;
        assert!(parent.is_kind("group", ModelHierarchy)?);
        assert!(!parent.is_kind("component", Unvalidated)?);

        // A component holds no models.
        stage.define_prim("/Parent/Child/Inner")?.set_kind("component")?;
        let inner = model(&stage, "/Parent/Child/Inner")?;
        assert!(!inner.is_model()?);
        assert!(!inner.is_kind("component", ModelHierarchy)?);
        assert!(inner.is_kind("component", Unvalidated)?);

        // A subcomponent is never a model, and the hierarchy does not gate it.
        stage.define_prim("/Parent/Child/Part")?.set_kind("subcomponent")?;
        let part = model(&stage, "/Parent/Child/Part")?;
        assert!(!part.is_model()?);
        assert!(part.is_kind("subcomponent", ModelHierarchy)?);
        assert!(part.is_kind("subcomponent", Unvalidated)?);
        assert!(!part.is_kind("model", Unvalidated)?);

        // A prim authoring no kind is of none.
        let bare = model(&stage, "/Parent/Child/Bare")?;
        assert!(!bare.is_kind("model", Unvalidated)?);
        Ok(())
    }

    #[test]
    fn is_kind_declared() -> Result<()> {
        static SITE: &SchemaFamily<'_> = &SchemaFamily::new("site", &[]).kinds(kind::tests::SITE);
        let stage = Stage::builder()
            .schema_registry(SchemaRegistry::builder().register(SITE).build()?)
            .in_memory("declared.usda")?;
        stage.define_prim("/Show")?.set_kind("chargroup")?;
        stage.define_prim("/Show/Hero")?.set_kind("prop")?;
        stage.define_prim("/Loose")?;
        stage.define_prim("/Loose/Hero")?.set_kind("prop")?;

        let show = model(&stage, "/Show")?;
        assert!(show.is_kind("assembly", ModelHierarchy)? && show.is_kind("group", ModelHierarchy)?);
        assert!(show.is_kind("chargroup", ModelHierarchy)?);

        let hero = model(&stage, "/Show/Hero")?;
        assert!(hero.is_kind("component", ModelHierarchy)? && hero.is_kind("prop", ModelHierarchy)?);
        assert!(!hero.is_kind("chargroup", Unvalidated)?);

        let loose = model(&stage, "/Loose/Hero")?;
        assert!(!loose.is_kind("prop", ModelHierarchy)?);
        assert!(loose.is_kind("prop", Unvalidated)?);
        Ok(())
    }
}
