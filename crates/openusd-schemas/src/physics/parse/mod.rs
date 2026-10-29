//! The physics parser (C++ `parseUtils.h`, `UsdPhysicsLoadStageFromPrimRange`):
//! [`parse`] walks the prims under the include paths, classifies each by
//! schema type and applied API schemas, builds a [`desc`] descriptor per
//! physics object, resolves the relations between them (collider to body,
//! joint to body, articulation to its links) and reports them all in a
//! [`Parsed`].
//!
//! C++ hands the descriptors to a callback, one call per kind, and its Python
//! binding turns that into a dictionary keyed by kind. [`Parsed`] is that
//! dictionary with the kinds as fields, in the order C++ reports them. Each
//! list is in traversal order, the include paths in the order given and each
//! a pre-order walk. Where C++ orders differently, by a path-ordered map or
//! by reporting shapes and joints kind by kind, the field docs say so.

use openusd::sdf::{Path, PathSet};
use openusd::tf;
use openusd::usd::{self, PrimPredicate};
use openusd::{gf, vt};

use super::tokens::{
    PHYSICS_ARTICULATION_ROOT_API, PHYSICS_COLLISION_API, PHYSICS_COLLISION_GROUP, PHYSICS_DISTANCE_JOINT,
    PHYSICS_FIXED_JOINT, PHYSICS_JOINT, PHYSICS_MATERIAL_API, PHYSICS_PRISMATIC_JOINT, PHYSICS_REVOLUTE_JOINT,
    PHYSICS_RIGID_BODY_API, PHYSICS_SCENE, PHYSICS_SPHERICAL_JOINT,
};
use super::{FilteredPairsAPI, desc};
use crate::SchemaError;
use crate::geom::{self, XformCache};

mod articulation;
mod body;
mod joint;
mod scene;
mod shape;

use joint::JointType;

/// What [`parse`] walks and reports (the arguments of C++
/// `UsdPhysicsLoadStageFromPrimRange` after the stage and the callback).
#[derive(Debug, Clone, Default)]
pub struct ParseOptions {
    /// The roots of the walk, each the start of a `UsdPrimRange` that
    /// traverses instance proxies. A prim under two of them is visited once;
    /// C++ visits it once per path, and its path-keyed maps then keep one of
    /// the two descriptors. Empty is [`SchemaError::EmptyIncludePaths`].
    pub include: Vec<Path>,
    /// Prims whose subtree the walk prunes, by exact path.
    pub exclude: Vec<Path>,
    /// The caller's own shape, joint and instancer types.
    pub custom: CustomTokens,
    /// `None` reports every object. `Some(owners)` keeps the scenes among
    /// `owners`, and, where `owners` is not empty, the bodies, colliders,
    /// joints and articulations they own: a body or a static collider is
    /// owned when one of its `physics:simulationOwner` targets is among
    /// `owners`, or when it names none and `owners` holds the empty path; a
    /// collider of a body when the body is kept; a joint when each of its
    /// bodies is missing or kept; an articulation when every body of it is
    /// kept. `Some(vec![])` therefore drops every scene and filters nothing
    /// else, as the C++ pointer argument does.
    pub simulation_owners: Option<Vec<Path>>,
}

/// The caller's own physics types (C++ `UsdPhysicsCustomTokens`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CustomTokens {
    /// Type names of `PhysicsJoint` prims reported as
    /// [`desc::JointKind::Custom`].
    pub joints: Vec<tf::Token>,
    /// Applied API schema names or type names of colliders reported as
    /// [`desc::Geometry::Custom`].
    pub shapes: Vec<tf::Token>,
    /// Type names of instancer prims whose subtree the walk prunes, as it
    /// does a `PointInstancer`'s; their prototypes are parsed separately.
    pub instancers: Vec<tf::Token>,
}

/// What [`parse`] found, one list per kind in the order C++ reports them.
#[derive(Debug, Clone, PartialEq)]
pub struct Parsed {
    /// The scenes, in traversal order.
    pub scenes: Vec<desc::Scene>,
    /// The groups after merging: one per `mergeGroupName`, in the order the
    /// C++ merge loop leaves them (see [`desc::CollisionGroup`]).
    pub collision_groups: Vec<desc::CollisionGroup>,
    /// The physics materials, in traversal order.
    pub materials: Vec<desc::Material>,
    /// The colliders, in traversal order; C++ reports them kind by kind, in
    /// the order of [`desc::Geometry`]'s variants.
    pub shapes: Vec<desc::Shape>,
    /// The articulations, in traversal order.
    pub articulations: Vec<desc::Articulation>,
    /// The bodies, in traversal order.
    pub rigid_bodies: Vec<desc::RigidBody>,
    /// The joints, in traversal order; C++ reports them kind by kind, in the
    /// order of [`desc::JointKind`]'s variants.
    pub joints: Vec<desc::Joint>,
    /// What the walk found and did not report.
    pub diagnostics: Vec<ParseDiagnostic>,
}

/// A prim the walk found and does not report, and why. C++ warns about the
/// first and reports the others with `isValid` false.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseDiagnostic {
    /// `PhysicsCollisionAPI` on a prim that is no supported gprim and no
    /// custom shape.
    UnknownShape(Path),
    /// A `Points` collider whose `widths` is absent or blocked.
    PointsWithoutWidths(Path),
    /// A `Points` collider whose `widths` and `points` counts differ.
    PointsWidthCount { path: Path, points: usize, widths: usize },
    /// An articulation for which no root was found.
    ArticulationWithoutRoot(Path),
}

/// The physics objects under `options.include` on `stage` (C++
/// `UsdPhysicsLoadStageFromPrimRange`).
///
/// A prim is classified by type and applied API schemas, built-ins included:
/// a `PhysicsScene`, a `PhysicsCollisionGroup`, a `PhysicsMaterialAPI` prim,
/// a `PhysicsJoint` of some kind, and otherwise a collider
/// (`PhysicsCollisionAPI`), a body (`PhysicsRigidBodyAPI`) or both; a joint
/// or any other prim with `PhysicsArticulationRootAPI` is also an
/// articulation. The walk prunes under a prim in `options.exclude`, under a
/// `PointInstancer` and under a custom instancer type, after classifying the
/// prim itself.
pub fn parse(stage: &usd::Stage, options: &ParseOptions) -> Result<Parsed, SchemaError> {
    if options.include.is_empty() {
        return Err(SchemaError::EmptyIncludePaths);
    }
    let mut parser = Parser {
        stage,
        xform: XformCache::new(None),
        diagnostics: Vec::new(),
    };
    let found = parser.classify(options)?;

    // TODO(rayon): every descriptor below depends on its own prim alone, the
    // collision groups and articulations on the maps built before them; C++
    // parses each kind in parallel batches of ten prims. The transform cache
    // would then be one per thread.
    let scenes = found
        .scenes
        .iter()
        .map(|prim| parser.scene(prim))
        .collect::<Result<Vec<_>, _>>()?;
    let (collision_groups, group_sets) = parser.collision_groups(&found.groups)?;
    let materials = found
        .materials
        .iter()
        .map(scene::material)
        .collect::<Result<Vec<_>, _>>()?;
    let joints = found
        .joints
        .iter()
        .map(|(prim, kind)| parser.joint(prim, *kind))
        .collect::<Result<Vec<_>, _>>()?;
    let mut shapes = parser.shapes(&found.colliders, &options.custom.shapes)?;
    let (mut rigid_bodies, frames): (Vec<_>, Vec<_>) = found
        .bodies
        .iter()
        .map(|prim| parser.rigid_body(prim))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .unzip();
    parser.attach_collisions(&mut shapes, &mut rigid_bodies, &frames, &group_sets)?;
    let articulations = parser.articulations(&found.articulations, &rigid_bodies, &joints)?;

    let mut parsed = Parsed {
        scenes,
        collision_groups,
        materials,
        shapes,
        articulations,
        rigid_bodies,
        joints,
        diagnostics: parser.diagnostics,
    };
    if let Some(owners) = &options.simulation_owners {
        filter_owners(owners, &mut parsed);
    }
    Ok(parsed)
}

/// One parse: the stage, the transform cache every descriptor's transform
/// comes from, and what was found and not reported.
struct Parser<'a> {
    stage: &'a usd::Stage,
    xform: XformCache,
    diagnostics: Vec<ParseDiagnostic>,
}

/// The prims the walk classified, per kind, in traversal order.
#[derive(Default)]
struct Classified {
    scenes: Vec<usd::Prim>,
    groups: Vec<usd::Prim>,
    materials: Vec<usd::Prim>,
    joints: Vec<(usd::Prim, JointType)>,
    colliders: Vec<usd::Prim>,
    bodies: Vec<usd::Prim>,
    articulations: Vec<usd::Prim>,
}

/// Which of the four API schemas the classifier cares about a prim carries
/// (C++ `_SchemaAPIFlag`).
#[derive(Default)]
struct ApiFlags {
    articulation: bool,
    collision: bool,
    body: bool,
    material: bool,
}

impl ApiFlags {
    /// The flags of `schemas`, a prim's applied API schemas. The material
    /// flag is set only while no other flag is, as in C++. A prim that
    /// carries `PhysicsMaterialAPI` beside another of the four is therefore
    /// a material only where the material name comes first.
    fn of(schemas: &[tf::Token]) -> Self {
        let mut flags = Self::default();
        for schema in schemas {
            if schema == PHYSICS_ARTICULATION_ROOT_API {
                flags.articulation = true;
            }
            if schema == PHYSICS_COLLISION_API {
                flags.collision = true;
            }
            if schema == PHYSICS_RIGID_BODY_API {
                flags.body = true;
            }
            if !flags.any() && schema == PHYSICS_MATERIAL_API {
                flags.material = true;
            }
        }
        flags
    }

    fn any(&self) -> bool {
        self.articulation || self.collision || self.body || self.material
    }
}

impl Parser<'_> {
    /// The walk and classification of the entry point.
    fn classify(&mut self, options: &ParseOptions) -> Result<Classified, SchemaError> {
        let exclude: PathSet = options.exclude.iter().cloned().collect();
        // Only a second include path can reach a prim again.
        let mut visited = (options.include.len() > 1).then(PathSet::default);
        let mut found = Classified::default();
        for include in &options.include {
            let mut walk = self
                .stage
                .prim(include.clone())?
                .filtered_subtree(PrimPredicate::DEFAULT_PROXIES)?;
            while let Some(prim) = walk.next() {
                let prim = prim?;
                if exclude.contains(prim.path())
                    || visited.as_mut().is_some_and(|seen| !seen.insert(prim.path().clone()))
                {
                    walk.prune_children();
                    continue;
                }
                // TODO(perf): `api_schemas`, `type_name` and each `is_a` below
                // resolve the prim's type info again, and `SchemaRegistry::is_a`
                // allocates per call. One `PrimTypeInfo` per prim, carried into
                // the per-kind parsers with its applied-schema list (which every
                // `from_prim` recomputes), and an allocation-free `is_a` would
                // serve every prim of the walk.
                let flags = ApiFlags::of(&prim.api_schemas()?);
                let type_name = prim.type_name()?;
                let is_type = |name: &tf::Token| type_name.as_ref() == Some(name);
                if prim.is_a(geom::tokens::POINT_INSTANCER)? || options.custom.instancers.iter().any(is_type) {
                    walk.prune_children();
                }
                if prim.is_a(PHYSICS_SCENE)? {
                    found.scenes.push(prim);
                } else if prim.is_a(PHYSICS_COLLISION_GROUP)? {
                    found.groups.push(prim);
                } else if flags.material {
                    found.materials.push(prim);
                } else if prim.is_a(PHYSICS_JOINT)? {
                    let kind = if prim.is_a(PHYSICS_FIXED_JOINT)? {
                        JointType::Fixed
                    } else if prim.is_a(PHYSICS_REVOLUTE_JOINT)? {
                        JointType::Revolute
                    } else if prim.is_a(PHYSICS_PRISMATIC_JOINT)? {
                        JointType::Prismatic
                    } else if prim.is_a(PHYSICS_SPHERICAL_JOINT)? {
                        JointType::Spherical
                    } else if prim.is_a(PHYSICS_DISTANCE_JOINT)? {
                        JointType::Distance
                    } else if options.custom.joints.iter().any(is_type) {
                        JointType::Custom
                    } else {
                        JointType::D6
                    };
                    if flags.articulation {
                        found.articulations.push(prim.clone());
                    }
                    found.joints.push((prim, kind));
                } else {
                    if flags.collision {
                        found.colliders.push(prim.clone());
                    }
                    if flags.body {
                        found.bodies.push(prim.clone());
                    }
                    if flags.articulation {
                        found.articulations.push(prim);
                    }
                }
            }
        }
        Ok(found)
    }

    /// `prim`'s world scale at the default time (C++
    /// `GfTransform(ComputeLocalToWorldTransform()).GetScale()`).
    fn world_scale(&mut self, prim: &usd::Prim) -> Result<gf::Vec3d, SchemaError> {
        Ok(self
            .xform
            .local_to_world_transform(prim)?
            .factor(gf::Mat4d::FACTOR_EPSILON)
            .scale)
    }
}

/// What `owners` keeps of `parsed` (the entry point's scene filter and the
/// C++ `_Check*SimulationOwner` filters), in place and in order.
fn filter_owners(owners: &[Path], parsed: &mut Parsed) {
    parsed.scenes.retain(|scene| owners.contains(&scene.path));
    if owners.is_empty() {
        return;
    }
    let default_owner = owners.iter().any(Path::is_empty);
    let owned =
        |named: &[Path]| (named.is_empty() && default_owner) || named.iter().any(|owner| owners.contains(owner));
    parsed.rigid_bodies.retain(|body| owned(&body.simulation_owners));
    let kept: PathSet = parsed.rigid_bodies.iter().map(|body| body.path.clone()).collect();
    parsed.shapes.retain(|shape| match &shape.rigid_body {
        Some(body) => kept.contains(body),
        None => owned(&shape.simulation_owners),
    });
    parsed.joints.retain(|joint| {
        [&joint.body0, &joint.body1]
            .into_iter()
            .flatten()
            .all(|body| kept.contains(body))
    });
    parsed
        .articulations
        .retain(|articulation| articulation.bodies.iter().flatten().all(|body| kept.contains(body)));
}

/// The value `attribute` resolves to. Every attribute read this way declares
/// a fallback; no value at all is a defect in the schema data.
fn read<T>(attribute: &usd::Attribute) -> Result<T, SchemaError>
where
    T: vt::FromValue,
    T::Error: Into<openusd::Error>,
{
    attribute.get::<T>()?.ok_or_else(|| SchemaError::NoValue {
        attribute: attribute.path().clone(),
    })
}

/// What `attribute`'s token names under `parse`, and `default` for any other
/// token, as C++ compares a `TfToken` against the ones it knows and keeps its
/// default otherwise.
fn token_or<T>(
    attribute: &usd::Attribute,
    parse: impl FnOnce(tf::Token) -> Option<T>,
    default: T,
) -> Result<T, SchemaError> {
    let token: tf::Token = read(attribute)?;
    Ok(parse(token).unwrap_or(default))
}

/// The `physics:filteredPairs` targets of `prim`, where it carries
/// `PhysicsFilteredPairsAPI` (C++ `_ParseFilteredPairs`).
fn filtered_pairs(prim: &usd::Prim) -> Result<Vec<Path>, SchemaError> {
    Ok(match FilteredPairsAPI::from_prim(prim.clone())? {
        Some(api) => api.filtered_pairs_rel().targets()?,
        None => Vec::new(),
    })
}
