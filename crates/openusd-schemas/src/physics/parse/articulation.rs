//! Articulations (C++ `_ParseArticulationDesc` and `_FinalizeArticulations`
//! with its link graph).
//!
//! An articulation's links are the bodies joined to each other by enabled
//! joints. From the prim the API is on, or the body a one-bodied joint there
//! names, every body underneath that is not yet a link starts a link map,
//! filled by following the joints. Where the API prim is neither a body nor
//! such a joint, each link map chooses a root: the link of largest weight, a
//! joint to the world where there is one, else the top of a nested chain or
//! the center of the graph.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use openusd::sdf::{Path, PathSet};
use openusd::usd::{self, PrimPredicate};

use super::{ParseDiagnostic, Parser, filtered_pairs};
use crate::SchemaError;
use crate::physics::desc;

/// A body in an articulation's link graph (C++ `ArticulationLink`).
#[derive(Debug, Default)]
struct Link {
    /// The bodies its joints reach, `None` for the world.
    children: Vec<Option<Path>>,
    /// Its joint to the world, where it has one.
    root_joint: Option<Path>,
    /// How much it wants to be the root: 100 per child link, 1000 per joint
    /// left out of the articulation, 100000 per joint to the world.
    weight: u32,
    /// Its row in the distance matrix, the order it joined the map in.
    index: usize,
    /// Whether one of its joints holds it to the world.
    has_fixed_joint: bool,
    /// Its joints, in joint path order.
    joints: Vec<Path>,
}

/// The links reached from one body, by path (C++ `ArticulationLinkMap`).
type LinkMap = BTreeMap<Path, Link>;

/// The enabled joints of each enabled body, in joint path order (C++
/// `BodyJointMap`, filled from the path-ordered joint map).
type BodyJoints<'a> = HashMap<&'a Path, Vec<&'a desc::Joint>>;

impl Parser<'_> {
    /// The articulations among `prims`, leaving out and recording those with
    /// no root (C++ `_ParseArticulationDesc`, `_FinalizeArticulations`).
    pub(super) fn articulations(
        &mut self,
        prims: &[usd::Prim],
        bodies: &[desc::RigidBody],
        joints: &[desc::Joint],
    ) -> Result<Vec<desc::Articulation>, SchemaError> {
        let body_map: HashMap<&Path, &desc::RigidBody> = bodies.iter().map(|body| (&body.path, body)).collect();
        // Iterated in path order, as C++ iterates its `std::map`; the order
        // reaches each body's joint list and so the link graph.
        let joint_map: BTreeMap<&Path, &desc::Joint> = joints.iter().map(|joint| (&joint.path, joint)).collect();
        let mut body_joints = BodyJoints::new();
        for joint in joint_map.values().filter(|joint| joint.enabled) {
            for body in [&joint.body0, &joint.body1].into_iter().flatten() {
                if body_map.get(body).is_some_and(|body| body.enabled) {
                    body_joints.entry(body).or_default().push(joint);
                }
            }
        }

        // TODO(rayon): each articulation reads the shared maps only; C++
        // finalizes them in parallel.
        let mut articulations = Vec::with_capacity(prims.len());
        for prim in prims {
            let mut articulation = desc::Articulation {
                path: prim.path().clone(),
                roots: Vec::new(),
                filtered_collisions: filtered_pairs(prim)?,
                joints: Vec::new(),
                bodies: Vec::new(),
            };
            self.finalize(&mut articulation, &body_map, &joint_map, &body_joints)?;
            if articulation.roots.is_empty() {
                self.diagnostics
                    .push(ParseDiagnostic::ArticulationWithoutRoot(articulation.path));
            } else {
                articulations.push(articulation);
            }
        }
        Ok(articulations)
    }

    /// `articulation`'s roots, joints and bodies (the per-articulation body of
    /// C++ `_FinalizeArticulations`).
    fn finalize(
        &self,
        articulation: &mut desc::Articulation,
        body_map: &HashMap<&Path, &desc::RigidBody>,
        joint_map: &BTreeMap<&Path, &desc::Joint>,
        body_joints: &BodyJoints<'_>,
    ) -> Result<(), SchemaError> {
        // The API on a body roots it there; on a joint with a body missing it
        // roots at the joint and the search starts at the body present.
        let mut base = Some(articulation.path.clone());
        if body_map.contains_key(&articulation.path) {
            articulation.roots.push(articulation.path.clone());
        } else if let Some(joint) = joint_map.get(&articulation.path)
            && (joint.body0.is_none() || joint.body1.is_none())
        {
            articulation.roots.push(articulation.path.clone());
            base = if joint.body0.is_none() {
                joint.body1.clone()
            } else {
                joint.body0.clone()
            };
        }
        let Some(base) = base else {
            return Ok(());
        };
        let base = self.stage.prim(base)?;
        if !base.is_valid()? {
            return Ok(());
        }

        let mut link_maps: Vec<(Path, LinkMap)> = Vec::new();
        let mut linked = PathSet::default();
        let mut order: Vec<Path> = Vec::new();
        let mut walk = base.filtered_subtree(PrimPredicate::DEFAULT_PROXIES)?;
        while let Some(prim) = walk.next() {
            let prim = prim?;
            if linked.contains(prim.path()) {
                walk.prune_children();
                continue;
            }
            if body_map.contains_key(prim.path()) {
                let mut links = LinkMap::new();
                traverse(prim.path(), &mut links, body_joints, &mut order);
                linked.extend(links.keys().cloned());
                link_maps.push((prim.path().clone(), links));
            }
        }

        // C++ decides once, before its loop, whether to choose roots, and then
        // chooses one per link map.
        let choose_roots = articulation.roots.is_empty();
        let mut joints = BTreeSet::new();
        let mut bodies = BTreeSet::new();
        for (first, links) in &link_maps {
            if choose_roots {
                let mut root: Option<Path> = None;
                let mut largest = 0;
                let mut has_fixed_joint = false;
                for (path, link) in links {
                    has_fixed_joint |= link.has_fixed_joint;
                    let candidate = link.root_joint.clone().unwrap_or_else(|| path.clone());
                    if link.weight > largest {
                        largest = link.weight;
                        root = Some(candidate);
                    } else if link.weight == largest {
                        root = earlier(&order, root, candidate);
                    }
                }
                if !has_fixed_joint {
                    root = nested_top(first, links).or_else(|| center_of_graph(links, &order));
                }
                articulation.roots.extend(root);
            }
            for link in links.values() {
                joints.extend(link.joints.iter().cloned());
                bodies.extend(link.children.iter().cloned());
            }
        }
        articulation.joints = joints.into_iter().collect();
        articulation.bodies = bodies.into_iter().collect();
        Ok(())
    }
}

/// The link graph from `path`, following its joints (C++
/// `_TraverseHierarchy`). A body with no joints is visited and recorded in
/// `order` but gets no link.
fn traverse(path: &Path, links: &mut LinkMap, body_joints: &BodyJoints<'_>, order: &mut Vec<Path>) {
    if links.contains_key(path) {
        return;
    }
    order.push(path.clone());
    let Some(joints) = body_joints.get(path) else {
        return;
    };
    // The link is in the map before its children are followed, which is what
    // stops a cycle.
    let mut link = Link {
        index: links.len(),
        ..Link::default()
    };
    links.insert(path.clone(), Link::default());
    for joint in joints {
        link.joints.push(joint.path.clone());
        let linked = |body: &Option<Path>| body.as_ref().is_some_and(|body| body_joints.contains_key(body));
        if !linked(&joint.body0) || !linked(&joint.body1) {
            if joint.exclude_from_articulation {
                link.weight += 1000;
            } else {
                link.weight += 100_000;
                link.root_joint = Some(joint.path.clone());
                link.has_fixed_joint = true;
            }
            link.children.push(None);
        } else {
            let other = if joint.body0.as_ref() == Some(path) {
                joint.body1.clone()
            } else {
                joint.body0.clone()
            };
            link.children.push(other.clone());
            if joint.exclude_from_articulation {
                link.weight += 1000;
            } else {
                link.weight += 100;
                if let Some(other) = &other {
                    traverse(other, links, body_joints, order);
                }
            }
        }
    }
    links.insert(path.clone(), link);
}

/// Of two tied candidates, the one `order` lists first (the C++ tie-break
/// over `articulationLinkOrderVector`).
fn earlier(order: &[Path], current: Option<Path>, candidate: Path) -> Option<Path> {
    for path in order {
        if Some(path) == current.as_ref() {
            break;
        }
        if *path == candidate {
            return Some(candidate);
        }
    }
    current
}

/// `top` where every link is at or under it, the first body of a chain nested
/// in namespace (C++ `_IsNestedArticulation`).
fn nested_top(top: &Path, links: &LinkMap) -> Option<Path> {
    links.keys().all(|link| link.has_prefix(top)).then(|| top.clone())
}

/// The link whose longest path to another link is shortest, ties going to
/// more children and then to the earlier in `order` (C++
/// `_GetCenterOfGraph`).
fn center_of_graph(links: &LinkMap, order: &[Path]) -> Option<Path> {
    let n = links.len();
    let mut distances = vec![-1_i32; n * n];
    for link in links.values() {
        mark_distances(link, links, link.index, 0, &mut distances);
    }
    let mut shortest = i32::MAX;
    let mut children = 0;
    let mut center: Option<Path> = None;
    for (path, link) in links {
        let longest = (0..n).map(|i| distances[link.index + i * n]).fold(0, i32::max);
        if longest < shortest {
            shortest = longest;
            children = link.children.len();
            center = Some(path.clone());
        } else if longest == shortest {
            if children < link.children.len() {
                children = link.children.len();
                center = Some(path.clone());
            } else if children == link.children.len() {
                center = earlier(order, center, path.clone());
            }
        }
    }
    center
}

/// The distance from the link at row `start` to `link` and, through its
/// children, to every link reached (C++ `_TraverseChilds`).
fn mark_distances(link: &Link, links: &LinkMap, start: usize, distance: i32, distances: &mut [i32]) {
    let n = links.len();
    distances[start + link.index * n] = distance;
    for child in link.children.iter().flatten() {
        if let Some(child) = links.get(child)
            && distances[start + child.index * n] < 0
        {
            mark_distances(child, links, start, distance + 1, distances);
        }
    }
}
