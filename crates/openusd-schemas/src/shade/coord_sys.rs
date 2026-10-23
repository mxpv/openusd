//! The `CoordSysAPI` view (C++ `UsdShadeCoordSysAPI`).
//!
//! A coordinate system is the local space of an Xformable prim. An applied
//! instance `CoordSysAPI:<name>` names it for the prim the instance is applied
//! to and that prim's descendants, through the single-target relationship
//! `coordSys:<name>:binding`; a descendant binds the same name again to
//! override it. [`CoordSysBinding`] reads one such relationship, and
//! [`CoordSysAPI::resolve_bindings`] walks a prim and its ancestors for the
//! bindings in force at the prim, over a [`CoordSysCache`] resolutions share.
//!
//! Only the applied form is read. C++ also reads bare `coordSys:<name>`
//! relationships under its deprecated non-applied mode.

use std::collections::HashMap;

use openusd::Result;
use openusd::sdf;
use openusd::tf;
use openusd::usd::{Prim, Relationship, SchemaBase, Stage};

use super::CoordSysAPI;

impl CoordSysAPI {
    /// The binding this instance makes on its prim, read from its binding
    /// relationship whether or not the instance is applied (C++
    /// `GetLocalBinding`). `None` where the relationship targets nothing.
    pub fn local_binding(&self) -> Result<Option<CoordSysBinding>> {
        CoordSysBinding::new(self.name().clone(), self.binding_rel())
    }

    /// The bindings the instances applied to `prim` make, in applied order,
    /// skipping an instance whose relationship targets nothing (C++
    /// `GetLocalBindingsForPrim`). Empty where the schema is not applied.
    pub fn local_bindings(prim: &Prim) -> Result<Vec<CoordSysBinding>> {
        Self::all(prim)?
            .iter()
            .filter_map(|instance| instance.local_binding().transpose())
            .collect()
    }

    /// The bindings in force at `prim`: its own, then each ancestor's for the
    /// names no nearer prim binds (C++ `FindBindingsWithInheritanceForPrim`).
    /// An instance whose relationship targets nothing binds nothing. An
    /// ancestor's binding of its name stays in force.
    ///
    /// `cache` keeps the answer at every prim the walk passes. A resolution
    /// over a subtree then reads each prim's bindings once; hand one cache to
    /// every resolution over it.
    pub fn resolve_bindings(prim: &Prim, cache: &mut CoordSysCache) -> Result<Vec<CoordSysBinding>> {
        let stage = prim.stage();
        let resolved = cache.stages.entry(stage.clone()).or_default();
        let chain: Vec<Prim> = prim.ancestors().collect();
        let cached = chain.iter().position(|prim| resolved.contains_key(prim.path()));
        let mut bindings = cached.map_or_else(Vec::new, |nearest| resolved[chain[nearest].path()].clone());
        for prim in chain[..cached.unwrap_or(chain.len())].iter().rev() {
            let local = Self::local_bindings(prim)?;
            bindings.retain(|inherited| !local.iter().any(|binding| binding.name == inherited.name));
            bindings.splice(..0, local);
            resolved.insert(prim.path().clone(), bindings.clone());
        }
        Ok(bindings)
    }

    /// The binding of this instance's name in force at its prim: the one the
    /// nearest of the prim and its ancestors makes, where the instance is
    /// applied there and its relationship targets something (C++
    /// `FindBindingWithInheritance`). Each call walks afresh;
    /// [`resolve_bindings`](Self::resolve_bindings) answers every name over
    /// a cache.
    pub fn resolve_binding(&self) -> Result<Option<CoordSysBinding>> {
        for prim in self.prim().ancestors() {
            if let Some(instance) = Self::from_prim(&prim, self.name())?
                && let Some(binding) = instance.local_binding()?
            {
                return Ok(Some(binding));
            }
        }
        Ok(None)
    }

    /// Author the binding relationship with `coord_sys` as its one target
    /// (C++ `Bind`).
    pub fn bind(&self, coord_sys: impl sdf::IntoPath) -> Result<&Self> {
        self.binding_rel_builder().set_targets([coord_sys]).build()?;
        Ok(self)
    }

    /// Erase the edit target's opinion on the binding relationship's targets,
    /// keeping the spec (C++ `ClearBinding` without `removeSpec`). The targets
    /// weaker layers author compose again.
    pub fn clear_binding(&self) -> Result<&Self> {
        self.binding_rel().clear_targets()?;
        Ok(self)
    }

    /// Remove the binding relationship's spec from the edit target's layer
    /// (C++ `ClearBinding` with `removeSpec`): `true` where the layer held
    /// one.
    pub fn remove_binding(&self) -> Result<bool> {
        Ok(self.stage().remove_property(self.binding_rel().path())?)
    }

    /// Block the binding with an explicit empty target list on the edit
    /// target, which hides the targets weaker layers author (C++
    /// `BlockBinding`). A binding an ancestor makes of the name stays in
    /// force, since resolution skips an instance that targets nothing.
    pub fn block_binding(&self) -> Result<&Self> {
        self.binding_rel_builder().block_targets().build()?;
        Ok(self)
    }
}

/// A named coordinate system bound at a prim: the name, the prim at
/// `coord_sys_path` whose local space it designates, and the relationship
/// that binds them (C++ `UsdShadeCoordSysAPI::Binding`).
///
/// The name is the instance name, which addresses the view that made the
/// binding: `CoordSysAPI::from_prim(prim, binding.name())`. C++ carries the
/// relationship name less its `coordSys` prefix, `<name>:binding`, which
/// [`rel`](Self::rel) still names in full.
#[derive(Clone)]
pub struct CoordSysBinding {
    name: tf::Token,
    rel: Relationship,
    coord_sys_path: sdf::Path,
}

impl CoordSysBinding {
    /// Read `rel` as the binding of `name`: `Some` with its first forwarded
    /// target, whatever follows it.
    fn new(name: tf::Token, rel: Relationship) -> Result<Option<Self>> {
        Ok(rel.forwarded_targets()?.into_iter().next().map(|coord_sys_path| Self {
            name,
            rel,
            coord_sys_path,
        }))
    }

    /// The coordinate system's name, the instance name of the binding.
    pub fn name(&self) -> &tf::Token {
        &self.name
    }

    /// The binding relationship, `coordSys:<name>:binding` (C++
    /// `bindingRelPath`).
    pub fn rel(&self) -> &Relationship {
        &self.rel
    }

    /// The path of the prim whose local space the name designates, which the
    /// stage may hold no prim at, or one of another type (C++
    /// `coordSysPrimPath`).
    pub fn coord_sys_path(&self) -> &sdf::Path {
        &self.coord_sys_path
    }
}

/// What coordinate-system resolutions share: the bindings in force at each
/// prim a resolution has passed, kept per stage instance.
///
/// Over a subtree, resolutions pass the same ancestors; one cache handed to
/// each [`resolve_bindings`](CoordSysAPI::resolve_bindings) reads each prim's
/// own bindings once and lays them over its parent's answer. Nothing evicts an
/// entry: start a new cache after editing bindings. The C++ library resolves
/// without a cache; usdImaging's `UsdImaging_CoordSysBindingCache` memoizes
/// the same per-prim answer, in ancestor-first order and without a binding
/// whose target prim is missing.
#[derive(Default)]
pub struct CoordSysCache {
    /// Entries are keyed by path, which stages share. Each stage has its own.
    stages: HashMap<Stage, sdf::PathMap<Vec<CoordSysBinding>>>,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The scene of the C++ `testUsdShadeCoordSysAPI` test.
    const SCENE: &str = r#"#usda 1.0
(
    defaultPrim = "World"
)

def Xform "World" (
    prepend apiSchemas = ["CoordSysAPI:worldSpace"]
)
{
    rel coordSys:worldSpace:binding = </World/Space>

    def Xform "Model" (
        prepend apiSchemas = ["CoordSysAPI:instanceSpace", "CoordSysAPI:modelSpace", "CoordSysAPI:paintSpace", "CoordSysAPI:worldSpace"]
    )
    {
        rel coordSys:instanceSpace:binding = </World/Model>
        rel coordSys:modelSpace:binding = </World/Model/Geom>
        rel coordSys:paintSpace:binding = </World/Model/Place3dTexture>
        rel coordSys:worldSpace:binding

        def Xform "Place3dTexture"
        {
        }

        def Xform "Geom"
        {
            def Cube "Box"
            {
            }
        }
    }

    def Xform "Space"
    {
    }
}
"#;

    const WORLD_SPACE: (&str, &str, &str) = ("worldSpace", "/World.coordSys:worldSpace:binding", "/World/Space");
    const MODEL_SPACES: [(&str, &str, &str); 3] = [
        (
            "instanceSpace",
            "/World/Model.coordSys:instanceSpace:binding",
            "/World/Model",
        ),
        (
            "modelSpace",
            "/World/Model.coordSys:modelSpace:binding",
            "/World/Model/Geom",
        ),
        (
            "paintSpace",
            "/World/Model.coordSys:paintSpace:binding",
            "/World/Model/Place3dTexture",
        ),
    ];

    /// The name, binding relationship path, and coordinate system path of
    /// `binding`.
    fn triple(binding: &CoordSysBinding) -> (&str, &str, &str) {
        (
            binding.name().as_str(),
            binding.rel().path().as_str(),
            binding.coord_sys_path().as_str(),
        )
    }

    /// [`triple`] of each of `bindings`.
    fn summary(bindings: &[CoordSysBinding]) -> Vec<(&str, &str, &str)> {
        bindings.iter().map(triple).collect()
    }

    /// The bindings in force at `path`, resolved over a cache of their own.
    fn resolved(stage: &Stage, path: &str) -> Result<Vec<CoordSysBinding>> {
        CoordSysAPI::resolve_bindings(&stage.prim(path)?, &mut CoordSysCache::default())
    }

    #[test]
    fn local_bindings() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(SCENE)?;
        let world = stage.prim("/World")?;
        let model = stage.prim("/World/Model")?;
        let world_space = CoordSysAPI::from_prim(&world, "worldSpace")?.expect("applied");
        assert_eq!(triple(&world_space.local_binding()?.expect("bound")), WORLD_SPACE);
        let model_world_space = CoordSysAPI::from_prim(&model, "worldSpace")?.expect("applied");
        assert!(model_world_space.local_binding()?.is_none(), "targets nothing");

        assert_eq!(summary(&CoordSysAPI::local_bindings(&model)?), MODEL_SPACES);
        assert!(CoordSysAPI::local_bindings(&stage.prim("/World/Model/Geom")?)?.is_empty());
        Ok(())
    }

    /// A relationship authored without the schema applied reads as the
    /// binding of its own instance view, and counts for nothing else.
    #[test]
    fn unapplied_binding() -> Result<()> {
        let stage = crate::tests::stage("anon.usda")?;
        let p = stage.define_prim("/P")?;
        p.author_relationship_targets("coordSys:x:binding", ["/P"])?;
        stage.define_prim("/P/C")?;
        let x = CoordSysAPI::from_prim_unchecked(p.clone(), "x");
        assert!(x.local_binding()?.is_some());
        assert!(CoordSysAPI::local_bindings(&p)?.is_empty());
        assert!(x.resolve_binding()?.is_none());
        assert!(resolved(&stage, "/P/C")?.is_empty());
        Ok(())
    }

    #[test]
    fn inherited_bindings() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(SCENE)?;
        assert_eq!(summary(&resolved(&stage, "/World")?), [WORLD_SPACE]);
        let expected = [MODEL_SPACES.as_slice(), &[WORLD_SPACE]].concat();
        for path in ["/World/Model", "/World/Model/Geom", "/World/Model/Geom/Box"] {
            assert_eq!(summary(&resolved(&stage, path)?), expected, "{path}");
        }

        // Model applies worldSpace without a target. World's binding of the
        // name is the one in force there.
        let model_world_space = CoordSysAPI::from_prim_unchecked(stage.prim("/World/Model")?, "worldSpace");
        assert_eq!(
            triple(&model_world_space.resolve_binding()?.expect("inherited")),
            WORLD_SPACE
        );
        let box_paint_space = CoordSysAPI::from_prim_unchecked(stage.prim("/World/Model/Geom/Box")?, "paintSpace");
        assert_eq!(
            triple(&box_paint_space.resolve_binding()?.expect("inherited")),
            MODEL_SPACES[2]
        );
        assert!(
            CoordSysAPI::from_prim_unchecked(stage.prim("/World")?, "paintSpace")
                .resolve_binding()?
                .is_none()
        );
        Ok(())
    }

    /// A descendant binding a name again overrides the ancestor's binding of
    /// it, for itself and its descendants.
    #[test]
    fn nearer_binding_overrides() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(SCENE)?;
        CoordSysAPI::apply(&stage.prim("/World/Model/Geom")?, "paintSpace")?.bind("/World/Space")?;
        let geom_paint_space = (
            "paintSpace",
            "/World/Model/Geom.coordSys:paintSpace:binding",
            "/World/Space",
        );
        assert_eq!(
            summary(&resolved(&stage, "/World/Model/Geom/Box")?),
            [geom_paint_space, MODEL_SPACES[0], MODEL_SPACES[1], WORLD_SPACE]
        );
        let box_paint_space = CoordSysAPI::from_prim_unchecked(stage.prim("/World/Model/Geom/Box")?, "paintSpace");
        assert_eq!(
            triple(&box_paint_space.resolve_binding()?.expect("bound")),
            geom_paint_space
        );
        assert_eq!(
            summary(&resolved(&stage, "/World/Model")?).len(),
            4,
            "Model keeps its own"
        );
        Ok(())
    }

    /// Blocking hides the binding a weaker layer authors; clearing lets it
    /// compose again.
    #[test]
    fn block_hides_weaker_layer() -> Result<()> {
        let (_dir, stage) = crate::tests::layered(&[(
            "weak.usda",
            r#"
def Xform "P" (prepend apiSchemas = ["CoordSysAPI:x"]) {
    rel coordSys:x:binding = </P>
}
"#,
        )])?;
        let x = CoordSysAPI::from_prim(&stage.prim("/P")?, "x")?.expect("applied");
        assert!(x.local_binding()?.is_some());
        x.block_binding()?;
        assert!(x.local_binding()?.is_none());
        x.clear_binding()?;
        assert!(
            x.local_binding()?.is_some(),
            "the weaker layer's binding composes again"
        );
        assert!(x.remove_binding()?, "the root layer's spec, emptied, is still there");
        assert!(x.local_binding()?.is_some(), "the weaker layer's spec is not");
        Ok(())
    }

    /// A cache answers from the prims it has passed: a subtree resolved after
    /// an ancestor reuses the ancestor's entry, edits since included.
    #[test]
    fn cache_shares_ancestors() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(SCENE)?;
        let mut cache = CoordSysCache::default();
        let model = stage.prim("/World/Model")?;
        let at_model = CoordSysAPI::resolve_bindings(&model, &mut cache)?;
        assert_eq!(summary(&at_model).len(), 4);

        CoordSysAPI::from_prim(&stage.prim("/World")?, "worldSpace")?
            .expect("applied")
            .block_binding()?;
        let at_box = CoordSysAPI::resolve_bindings(&stage.prim("/World/Model/Geom/Box")?, &mut cache)?;
        assert_eq!(summary(&at_box), summary(&at_model), "served from Model's entry");
        assert_eq!(
            summary(&resolved(&stage, "/World/Model/Geom/Box")?),
            MODEL_SPACES,
            "a new cache sees the block"
        );
        Ok(())
    }

    #[test]
    fn bind_clear_remove_block() -> Result<()> {
        let (_dir, stage) = crate::tests::from_usda(SCENE)?;
        let world = stage.prim("/World")?;
        let model_space = CoordSysAPI::apply(&world, "modelSpace")?;
        model_space.bind("/World/Model/Geom")?;
        assert_eq!(
            triple(&model_space.local_binding()?.expect("bound")),
            ("modelSpace", "/World.coordSys:modelSpace:binding", "/World/Model/Geom")
        );
        assert!(model_space.remove_binding()?);
        assert!(!model_space.remove_binding()?, "nothing left to remove");
        assert!(model_space.local_binding()?.is_none());

        model_space.bind("/World/Model/Geom")?;
        model_space.clear_binding()?;
        assert!(model_space.local_binding()?.is_none());

        let model = stage.prim("/World/Model")?;
        CoordSysAPI::from_prim(&model, "instanceSpace")?
            .expect("applied")
            .block_binding()?;
        assert_eq!(summary(&CoordSysAPI::local_bindings(&model)?), MODEL_SPACES[1..]);

        // Blocking a nearer instance leaves the ancestor's binding in force.
        let geom_paint_space = CoordSysAPI::apply(&stage.prim("/World/Model/Geom")?, "paintSpace")?;
        geom_paint_space.block_binding()?;
        let box_paint_space = CoordSysAPI::from_prim_unchecked(stage.prim("/World/Model/Geom/Box")?, "paintSpace");
        assert_eq!(
            triple(&box_paint_space.resolve_binding()?.expect("inherited")),
            MODEL_SPACES[2]
        );
        assert!(summary(&resolved(&stage, "/World/Model/Geom/Box")?).contains(&MODEL_SPACES[2]));
        Ok(())
    }
}
