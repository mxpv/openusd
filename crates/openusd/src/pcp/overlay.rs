//! Prim opinions composed before they are written.
//!
//! An authoring batch plans every write before any of them reaches a layer,
//! so it cannot read back what it has queued the way C++ does, where each
//! authoring call recomposes before the next one reads. An [`Overlay`]
//! carries the queued prim opinions, keyed by the site they will be written
//! at, and [`IndexCache::compose_planned`] answers what the stage holds at a
//! path with them substituted. The rules are composition's own: the opinions
//! are walked in strength order through the prim's existing index and folded
//! by the same specifier rule ([`compose_specifier`]) and strongest-opinion
//! rule a read applies, and the population is the stage's own, a mask and the
//! populated ancestors.
//!
//! The overlay substitutes opinions. It does not rebuild an index. A first
//! spec at a culled node with no arcs below it only adds that node's opinions,
//! which the walk reads at the node's place; a first spec at a culled node
//! that has arcs below it, or at one the index erased, un-culls an arc whose
//! subtree only a rebuild composes (C++ `PcpChanges::DidChangeSpecs`), and the
//! query reports the result unknown.

use std::collections::HashMap;

use crate::sdf::schema::FieldKey;
use crate::sdf::{self, Path, Specifier};
use crate::tf;
use crate::vt::Value;

use super::prim_graph::{ArcType, Node};
use super::prim_index::PrimIndex;
use super::prim_resolve::compose_specifier;
use super::{IndexCache, LayerGraph, LayerId, QueryError};

/// Pending prim opinions, keyed by the site — a layer and the spec path in
/// it — they are to be written at.
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct Overlay {
    sites: HashMap<LayerId, sdf::PathMap<SiteFields>>,
}

/// What an [`Overlay`] writes at one site.
#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct SiteFields {
    /// Whether the site gains a prim spec it does not hold yet.
    pub(crate) creates_spec: bool,
    /// The `specifier` written there, in place of the layer's.
    pub(crate) specifier: Option<Specifier>,
    /// The `typeName` written there, in place of the layer's; an empty token
    /// erases the layer's, as [`PrimSpecMut::set_type_name`] does, so the site
    /// holds no opinion.
    ///
    /// [`PrimSpecMut::set_type_name`]: crate::sdf::PrimSpecMut::set_type_name
    pub(crate) type_name: Option<tf::Token>,
}

/// A prim's composed existence, definedness, type and activation: the fields
/// an authoring decision about the prim reads.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct PrimFields {
    /// Whether a contributing site holds a spec for the prim.
    pub(crate) has_spec: bool,
    /// Whether the composed specifier is `def` or `class`.
    pub(crate) defining: bool,
    /// The composed `typeName`, `None` where no site authors one or the
    /// query did not ask for it.
    pub(crate) type_name: Option<tf::Token>,
    /// The composed `active`.
    pub(crate) active: bool,
}

/// What [`IndexCache::compose_planned`] finds at a path.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Planned {
    /// The population reaches the path, and the prim there composes to these
    /// fields; `has_spec` is `false` where nothing composes there.
    Reached(PrimFields),
    /// The population mask hides the path, or an ancestor is not populated.
    Unreached,
    /// A spec the overlay creates un-culls an arc whose subtree only a
    /// rebuild composes, in an index the answer reads.
    Unknown,
}

/// The opinions [`PrimIndex::overlaid`] found for a prim.
struct OverlaidOpinions {
    has_spec: bool,
    specifiers: Vec<(Specifier, ArcType)>,
    type_name: Option<tf::Token>,
}

impl Overlay {
    /// Whether the overlay writes nothing.
    pub(crate) fn is_empty(&self) -> bool {
        self.sites.is_empty()
    }

    /// The fields written at `path` in `layer`, if any.
    pub(crate) fn get(&self, layer: LayerId, path: &Path) -> Option<&SiteFields> {
        self.sites.get(&layer)?.get(path)
    }

    /// The fields written at `path` in `layer`, created empty when the overlay
    /// writes nothing there yet.
    pub(crate) fn entry(&mut self, layer: LayerId, path: Path) -> &mut SiteFields {
        self.sites.entry(layer).or_default().entry(path).or_default()
    }

    /// Whether `layer` holds a spec at `path` once the overlay is written:
    /// the layer has one, or the overlay creates one.
    pub(crate) fn holds_spec(&self, graph: &LayerGraph, layer: LayerId, path: &Path) -> bool {
        graph.layer(layer).data().has_spec(path) || self.creates_spec(layer, path)
    }

    /// Whether the overlay creates a spec at `path` in `layer`.
    fn creates_spec(&self, layer: LayerId, path: &Path) -> bool {
        self.get(layer, path).is_some_and(|fields| fields.creates_spec)
    }
}

impl PrimIndex {
    /// Whether a spec `overlay` creates un-culls an arc of this index whose
    /// subtree only a rebuild composes: one at a culled node that is not
    /// [`revivable`], or at a culled node the index erased.
    fn revived_by(&self, graph: &LayerGraph, overlay: &Overlay) -> bool {
        let created = |stack, path: &Path| {
            graph
                .layer_stack(stack)
                .iter()
                .any(|&(layer, _)| overlay.creates_spec(layer, path))
        };
        self.all_nodes()
            .any(|node| node.is_culled() && !revivable(node) && created(node.layer_stack_id(), node.path()))
            || self
                .culled_dependencies()
                .iter()
                .any(|culled| created(culled.layer_stack, &culled.site))
    }

    /// The prim's `specifier` and `typeName` opinions, strongest first, with
    /// `overlay`'s substituted at the sites it writes and a site counted where
    /// it creates a spec; `None` where the overlay revives an arc only a
    /// rebuild composes.
    ///
    /// Walks the retained nodes in strength order and each node's layer stack
    /// in order: the walk of the spec stack, extended to the layers that hold
    /// no spec yet but will, a culled node among them once the overlay gives
    /// it its first spec. A `specifier` block stops the specifier's opinions,
    /// as [`resolve_field`](PrimIndex::resolve_field) does, and a `typeName`
    /// block withholds every weaker `typeName`.
    // TODO(perf): every layer of every node is probed; the spec stack already
    // lists the ones holding a spec, so only the overlay's own sites need
    // inserting into it.
    fn overlaid(&self, graph: &LayerGraph, overlay: &Overlay) -> Result<Option<OverlaidOpinions>, QueryError> {
        if self.revived_by(graph, overlay) {
            return Ok(None);
        }
        let mut found = OverlaidOpinions {
            has_spec: false,
            specifiers: Vec::new(),
            type_name: None,
        };
        let mut specifier_blocked = false;
        let mut type_name_settled = false;
        for node in self.all_nodes() {
            // A culled node contributes only as an empty arc target the
            // overlay gives its first spec. One a relocation elided keeps its
            // opinions masked, as the committed walk has it.
            if node.is_culled() && !revivable(node) {
                continue;
            }
            let path = node.path();
            for &(layer, _) in graph.layer_stack(node.layer_stack_id()).iter() {
                if !overlay.holds_spec(graph, layer, path) {
                    continue;
                }
                found.has_spec = true;
                let fields = overlay.get(layer, path);
                let data = graph.layer(layer).data();
                if !specifier_blocked {
                    match fields.and_then(|fields| fields.specifier) {
                        Some(specifier) => found.specifiers.push((specifier, node.arc())),
                        None => match data.try_field(path, FieldKey::Specifier.as_str())?.as_deref() {
                            Some(Value::Specifier(specifier)) => found.specifiers.push((*specifier, node.arc())),
                            Some(Value::ValueBlock) => specifier_blocked = true,
                            _ => {}
                        },
                    }
                }
                if !type_name_settled {
                    let opinion = match fields.and_then(|fields| fields.type_name.as_ref()) {
                        Some(erased) if erased.as_str().is_empty() => None,
                        Some(type_name) => Some(Some(type_name.clone())),
                        None => data
                            .try_field(path, FieldKey::TypeName.as_str())?
                            .map(|value| value.into_owned().try_as_token()),
                    };
                    if let Some(type_name) = opinion {
                        // A block withholds every weaker opinion.
                        found.type_name = type_name;
                        type_name_settled = true;
                    }
                }
            }
        }
        Ok(Some(found))
    }
}

impl IndexCache {
    /// What the stage holds at `path` with `overlay`'s opinions written: the
    /// prim's composed fields where its population reaches it, the mask
    /// including the path and every ancestor populated (C++
    /// `UsdStage::GetPrimAtPath`). The composed `typeName` is read only where
    /// `with_type` asks for it.
    ///
    /// With an empty overlay this is the committed answer, read from the
    /// memoized population and prim status
    /// ([`population_reaches`](Self::population_reaches),
    /// [`own_status`](Self::own_status)).
    pub(crate) fn compose_planned(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        overlay: &Overlay,
        with_type: bool,
    ) -> Result<Planned, QueryError> {
        if overlay.is_empty() {
            if !self.population_reaches(graph, path)? {
                return Ok(Planned::Unreached);
            }
            let own = self.own_status(graph, path)?;
            let type_name = match with_type {
                true => self
                    .resolve_field(graph, path, FieldKey::TypeName.as_str())?
                    .and_then(Value::try_as_token),
                false => None,
            };
            return Ok(Planned::Reached(PrimFields {
                has_spec: own.is_some(),
                defining: own.is_some_and(|own| own.defining),
                type_name,
                active: own.is_none_or(|own| own.active),
            }));
        }
        if !self.mask_includes(path) {
            return Ok(Planned::Unreached);
        }
        // TODO(perf): each ancestor's composition checks its own ancestors for
        // a revived arc again, and an index the overlay reaches no site of is
        // walked where its memoized status would answer; one walk down the path
        // could check each index once.
        let mut ancestors: Vec<Path> = path.strict_ancestors_below_root().collect();
        ancestors.reverse();
        for ancestor in &ancestors {
            match self.compose_prim_fields(graph, ancestor, overlay)? {
                None => return Ok(Planned::Unknown),
                Some(fields) if !(fields.has_spec && fields.active) => return Ok(Planned::Unreached),
                Some(_) => {}
            }
        }
        Ok(self
            .compose_prim_fields(graph, path, overlay)?
            .map_or(Planned::Unknown, Planned::Reached))
    }

    /// The composed [`PrimFields`] of the prim at `path`, with `overlay`'s
    /// opinions written, population aside.
    ///
    /// `None` where the answer needs an index the overlay cannot predict: a
    /// spec it creates revives an arc in the prim's index or an ancestor's
    /// that only rebuilding that index composes.
    fn compose_prim_fields(
        &mut self,
        graph: &LayerGraph,
        path: &Path,
        overlay: &Overlay,
    ) -> Result<Option<PrimFields>, QueryError> {
        let path = self.effective_path(graph, path)?;
        for ancestor in path.strict_ancestors_below_root() {
            self.ensure_index(graph, &ancestor)?;
            if self.cached(&ancestor).revived_by(graph, overlay) {
                return Ok(None);
            }
        }
        self.ensure_index(graph, &path)?;
        let Some(found) = self.cached(&path).overlaid(graph, overlay)? else {
            return Ok(None);
        };
        // A prototype root is `def` whatever its source says, as the
        // committed read has it.
        let defining = self.is_prototype(&path)
            || matches!(
                compose_specifier(&found.specifiers),
                Some(Specifier::Def | Specifier::Class)
            );
        Ok(Some(PrimFields {
            has_spec: found.has_spec,
            defining,
            type_name: found.type_name,
            active: self.active_at(graph, &path)?,
        }))
    }
}

/// Whether a culled `node` is an empty arc target whose first spec only adds
/// that spec's opinions at the node's place: it holds no spec, no relocation
/// restricted it, and no node sits below it for a rebuild to graft.
fn revivable(node: Node<'_>) -> bool {
    !node.has_specs() && node.restriction_depth() == 0 && node.children().next().is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Result;
    use crate::usd::Stage;
    use crate::usd::stage::tests::scene;

    /// What `stage` holds at `path` under `overlay`.
    fn planned(stage: &Stage, path: &str, overlay: &Overlay) -> Result<Planned> {
        let path = Path::new(path)?;
        Ok(stage.with_cache(|graph, cache| cache.compose_planned(graph, &path, overlay, true))?)
    }

    /// The fields of a prim the population reaches.
    fn reached(stage: &Stage, path: &str, overlay: &Overlay) -> Result<PrimFields> {
        match planned(stage, path, overlay)? {
            Planned::Reached(fields) => Ok(fields),
            other => panic!("{path} is {other:?}"),
        }
    }

    /// An overlay writing `fields` at `path` in the stage's root layer.
    fn written(stage: &Stage, path: &str, fields: SiteFields) -> Result<Overlay> {
        let root = stage.edit_target().layer_identifier().to_string();
        let layer = stage.layers().id_of(&root).expect("the root layer is in the stage");
        let mut overlay = Overlay::default();
        *overlay.entry(layer, Path::new(path)?) = fields;
        Ok(overlay)
    }

    fn token(text: &str) -> Option<tf::Token> {
        Some(tf::Token::from(text))
    }

    /// The overlay's own walk answers what the memoized committed reads do
    /// for prims its sites do not reach.
    #[test]
    fn walk_matches_committed() -> Result<()> {
        let root = "def Xform \"A\"\n{\n    def \"C\"\n    {\n    }\n}\nover \"B\"\n{\n}\ndef \"Off\" (\n    active = false\n)\n{\n    def \"Child\"\n    {\n    }\n}\n";
        let (_dir, stage) = scene(&[("root.usda", root)])?;
        let empty = Overlay::default();
        let elsewhere = written(&stage, "/Elsewhere", SiteFields::default())?;

        for path in ["/A", "/A/C", "/B", "/Missing", "/Off", "/Off/Child"] {
            assert_eq!(
                planned(&stage, path, &empty)?,
                planned(&stage, path, &elsewhere)?,
                "{path}"
            );
        }
        let a = reached(&stage, "/A", &empty)?;
        assert!(a.has_spec && a.defining && a.active);
        assert_eq!(a.type_name, token("Xform"));
        assert!(!reached(&stage, "/B", &empty)?.defining);
        assert!(!reached(&stage, "/Missing", &empty)?.has_spec);
        assert_eq!(planned(&stage, "/Off/Child", &empty)?, Planned::Unreached);
        Ok(())
    }

    /// A field the overlay writes replaces the layer's, and one it leaves
    /// keeps the committed opinion.
    #[test]
    fn substitutes_written_fields() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "over Xform \"A\"\n{\n}\n")])?;
        let overlay = written(
            &stage,
            "/A",
            SiteFields {
                specifier: Some(Specifier::Def),
                ..SiteFields::default()
            },
        )?;

        let a = reached(&stage, "/A", &overlay)?;
        assert!(a.defining);
        assert_eq!(a.type_name, token("Xform"));
        Ok(())
    }

    /// A site the overlay creates a spec at counts as one.
    #[test]
    fn created_spec_exists() -> Result<()> {
        let (_dir, stage) = scene(&[("root.usda", "")])?;
        let overlay = written(
            &stage,
            "/New",
            SiteFields {
                creates_spec: true,
                specifier: Some(Specifier::Def),
                type_name: token("Scope"),
            },
        )?;

        let created = reached(&stage, "/New", &overlay)?;
        assert!(created.has_spec && created.defining);
        assert_eq!(created.type_name, token("Scope"));
        Ok(())
    }

    /// An opinion one prim's site receives reaches every prim that composes
    /// the site: a prim referencing it reads the written type.
    #[test]
    fn reaches_referencing_prim() -> Result<()> {
        let root = "def Scope \"Source\"\n{\n}\ndef \"Instance\" (\n    references = </Source>\n)\n{\n}\n";
        let (_dir, stage) = scene(&[("root.usda", root)])?;
        let overlay = written(
            &stage,
            "/Source",
            SiteFields {
                type_name: token("Cube"),
                ..SiteFields::default()
            },
        )?;

        assert_eq!(reached(&stage, "/Instance", &overlay)?.type_name, token("Cube"));
        Ok(())
    }

    /// A spec inside an unselected variant composes nowhere.
    #[test]
    fn unselected_variant_ignored() -> Result<()> {
        let root = "def Xform \"A\" (\n    variantSets = \"set\"\n)\n{\n    variantSet \"set\" = {\n        \"off\" {\n        }\n    }\n}\n";
        let (_dir, stage) = scene(&[("root.usda", root)])?;
        let overlay = written(
            &stage,
            "/A{set=off}",
            SiteFields {
                creates_spec: true,
                specifier: Some(Specifier::Def),
                type_name: token("Scope"),
            },
        )?;

        assert_eq!(reached(&stage, "/A", &overlay)?.type_name, token("Xform"));
        Ok(())
    }

    /// A first spec at an empty reference target adds the target's opinions
    /// where the culled node sits, as the committed spec then composes. A
    /// first spec at a site the index erased, the selected variant's site of a
    /// prim no layer holds yet, has no place in the index to read it at: only a
    /// rebuild composes it, for the prim and everything below it.
    #[test]
    fn culled_target_revival() -> Result<()> {
        let root = "def \"Instance\" (\n    references = </Target>\n)\n{\n}\n";
        let (_dir, stage) = scene(&[("root.usda", root)])?;
        let overlay = written(
            &stage,
            "/Target",
            SiteFields {
                creates_spec: true,
                specifier: Some(Specifier::Def),
                type_name: token("Scope"),
            },
        )?;
        assert_eq!(reached(&stage, "/Instance", &overlay)?.type_name, token("Scope"));
        stage.define_typed_prim("/Target", "Scope")?;
        assert_eq!(stage.prim("/Instance")?.type_name()?.as_deref(), Some("Scope"));

        let (_dir, stage) = scene(&[(
            "root.usda",
            "def \"A\" (\n    variants = {\n        string set = \"on\"\n    }\n    prepend variantSets = \"set\"\n)\n{\n    variantSet \"set\" = {\n        \"on\" {\n        }\n    }\n}\n",
        )])?;
        let overlay = written(
            &stage,
            "/A{set=on}X",
            SiteFields {
                creates_spec: true,
                specifier: Some(Specifier::Def),
                ..SiteFields::default()
            },
        )?;
        assert_eq!(planned(&stage, "/A/X", &overlay)?, Planned::Unknown);
        assert_eq!(planned(&stage, "/A/X/Y", &overlay)?, Planned::Unknown);
        Ok(())
    }
}
