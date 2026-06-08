//! Scene-graph instancing: shared prototypes for `instanceable` prims (spec
//! 11.3.3).
//!
//! Instances with the same [`InstanceKey`] — the arc-introduced opinions that
//! define their subtree, independent of stage path — share one composed
//! prototype. [`PrototypeRegistry`] owns that mapping (an [`IndexCache`] holds
//! one as a field); the composition-coupled glue stays on `IndexCache` because
//! it needs the composed indices, and every descendant-serving query enters
//! through [`IndexCache::effective_path`], which redirects a non-canonical
//! instance's subtree into its canonical instance so identical instances are
//! composed only once.

use std::collections::HashMap;

use anyhow::Result;

use crate::sdf::schema::FieldKey;
use crate::sdf::{Path, Value};

use super::index_cache::IndexCache;
use super::layer_graph::LayerGraph;
use super::prim_index::PrimIndex;
use super::LayerId;

/// The shared-prototype registry (spec 11.3.3): maps each instancing key to its
/// prototype and tracks the instances that share it. Owns no composition state
/// — the [`IndexCache`] computes an [`InstanceKey`] from a composed index and
/// hands it to [`register`](Self::register); the registry only dedups by key,
/// mints `/__Prototype_N` identities, and answers prototype/instance queries.
#[derive(Default)]
pub(super) struct PrototypeRegistry {
    /// Prototypes keyed by their `/__Prototype_N` root path. Path-keyed so the
    /// common query direction (path to prototype) is a single lookup.
    by_root: HashMap<Path, Prototype>,
    /// Maps an instancing key to its prototype root, the lookup direction used
    /// only when registering an instance to dedup against an existing key.
    by_key: HashMap<InstanceKey, Path>,
    /// Counter for minting `/__Prototype_N` identities in registration order.
    /// Stays monotonic across [`clear`](Self::clear) so a `/__Prototype_N`
    /// identity is never reused for a different composition within a session.
    count: usize,
}

/// A shared prototype for a set of instances with the same [`InstanceKey`]
/// (spec 11.3.3). Its composition is backed by the canonical instance, exposed
/// under a synthetic `/__Prototype_N` path. The instance-namespace opinions are
/// suppressed where they would leak into shared content: an instance's child
/// names and every descendant compose only from the shared subtree (the
/// instanceable arc and below, plus implied classes), with the local root and
/// the ancestral references above the instanceable arc inerted (see
/// [`PrimIndex::instance_local_nodes`] and [`PrimIndex::mark_instance_local_inert`]).
///
/// TODO(instancing): instancing is functionally correct for stage-level
/// instance and descendant queries (the composition goldens pass byte-exact),
/// but three gaps remain before it reaches full C++ `Pcp`/`UsdStage` parity:
///
/// 1. Alias-backed prototype root. The prototype is the canonical instance,
///    not a separately composed namespace, so a query on the prototype *root*
///    itself (`/__Prototype_N`, no tail) reflects the canonical instance's
///    root — which keeps that instance's allowed root property overrides (spec
///    11.3.3 permits overriding property values at an instance root). A faithful
///    `/__Prototype_N` composed as its own root would drop those overrides too.
///    The descendant suppression here only fixes child names and the subtree
///    (the spec's "overrides on descendants are ignored" rule); the prototype
///    *root* override leak is the part `effective_path`'s aliasing cannot reach.
///    The goldens compose the namespace prims, not the prototype root, so they
///    do not exercise it.
/// 2. Relationship-target / connection-target remap into the prototype is gated
///    on §12.4 target resolution and not done for the prototype namespace.
/// 3. Distinct prototypes compose independent subtrees and could be built in
///    parallel (see the `TODO(rayon)` on [`IndexCache::canonical_instance`]);
///    today they are composed serially on the `&mut self` path.
///
/// Closing (1) — materializing `/__Prototype_N` as an independently composed
/// root — is the structural change that would also make (2) natural, since the
/// prototype would then be a real prim index to resolve targets against rather
/// than an alias.
struct Prototype {
    /// Registration order (the `N` in `/__Prototype_N`). Kept so prototypes can
    /// be returned in mint order without parsing the path.
    index: usize,
    /// Instance whose composed subtree backs this prototype.
    canonical: Path,
    /// Every instance sharing this prototype.
    instances: Vec<Path>,
}

/// Identity of an instance prim's shared composition (spec 11.3.3): the
/// arc-introduced opinions that determine its subtree, independent of the
/// instance's own stage path. Instances with equal keys share a prototype.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct InstanceKey(Vec<InstanceArc>);

/// One arc contribution in an [`InstanceKey`]. Floats are stored as bit
/// patterns so the key is `Hash`/`Eq`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct InstanceArc {
    arc: u8,
    layer: LayerId,
    path: String,
    offset_bits: u64,
    scale_bits: u64,
}

impl PrototypeRegistry {
    /// Registers `instance` against its prototype: dedups by `key`, recording
    /// the instance the first time a key is seen and minting `/__Prototype_N`.
    /// Returns the `(canonical instance, prototype path)` pair.
    fn register(&mut self, key: InstanceKey, instance: &Path) -> (Path, Path) {
        if let Some(root) = self.by_key.get(&key) {
            let root = root.clone();
            let prototype = self.by_root.get_mut(&root).expect("key index points to a prototype");
            if !prototype.instances.contains(instance) {
                prototype.instances.push(instance.clone());
            }
            return (prototype.canonical.clone(), root);
        }

        let index = self.count;
        let path = Path::new(&format!("/__Prototype_{index}")).expect("synthetic prototype path is valid");
        self.count += 1;
        self.by_key.insert(key, path.clone());
        self.by_root.insert(
            path.clone(),
            Prototype {
                index,
                canonical: instance.clone(),
                instances: vec![instance.clone()],
            },
        );
        (instance.clone(), path)
    }

    /// The canonical instance backing the prototype at `prototype`, or `None`
    /// for an unknown path.
    fn canonical_of(&self, prototype: &Path) -> Option<Path> {
        self.by_root.get(prototype).map(|p| p.canonical.clone())
    }

    /// The instances sharing the prototype at `prototype` (a `/__Prototype_N`
    /// path), sorted by namespace path so the result does not depend on the
    /// order instances were queried. Empty for unknown paths.
    fn instances_of(&self, prototype: &Path) -> Vec<Path> {
        let mut instances = self
            .by_root
            .get(prototype)
            .map(|prototype| prototype.instances.clone())
            .unwrap_or_default();
        instances.sort();
        instances
    }

    /// The registered `/__Prototype_N` roots, in registration order.
    fn roots(&self) -> Vec<Path> {
        let mut roots: Vec<(&Path, &Prototype)> = self.by_root.iter().collect();
        roots.sort_by_key(|(_, prototype)| prototype.index);
        roots.into_iter().map(|(root, _)| root.clone()).collect()
    }

    /// Whether `path` is a registered `/__Prototype_N` root.
    fn is_root(&self, path: &Path) -> bool {
        self.by_root.contains_key(path)
    }

    /// Whether `path` lies within a prototype's namespace — i.e. it has a
    /// `/__Prototype_N` ancestor (spec 11.3.3).
    fn is_in_prototype(&self, path: &Path) -> bool {
        self.enclosing_root(path.parent()).is_some()
    }

    /// Walks the chain from `start` toward the root and returns the nearest
    /// `/__Prototype_N` root on it, or `None`. Passing the queried prim starts
    /// the walk inclusively; passing its parent excludes the prim itself.
    fn enclosing_root(&self, start: Option<Path>) -> Option<Path> {
        let mut node = start;
        while let Some(current) = node {
            if self.by_root.contains_key(&current) {
                return Some(current);
            }
            node = current.parent();
        }
        None
    }

    /// Drops every prototype so stale instance-to-prototype mappings do not
    /// survive a composition change; the registry is rebuilt lazily on the next
    /// instancing query. `count` stays monotonic (see its doc).
    fn clear(&mut self) {
        self.by_root.clear();
        self.by_key.clear();
    }
}

/// Computes the instancing key for an already-built instance index: the
/// arc-introduced (shared) opinions that define the prototype subtree,
/// independent of the instance's own stage path (spec 11.3.3).
/// `instance_depth` is the instance prim's own namespace depth, used to
/// partition shared from instance-local nodes
/// ([`PrimIndex::instance_local_nodes`]).
///
/// TODO: variant selections are captured only implicitly via variant
/// nodes' paths; fold the resolved selection set in explicitly if a case
/// surfaces where that is insufficient.
fn instance_key(index: &PrimIndex, instance_depth: u16) -> InstanceKey {
    let local = index.instance_local_nodes(instance_depth);
    let arcs = index
        .nodes_with_ids()
        .filter(|(id, node)| !local[id.idx()] && !node.is_culled())
        .map(|(_, node)| {
            let offset = node.map_to_root.time_offset();
            InstanceArc {
                arc: node.arc as u8,
                layer: node.layer_id(),
                path: node.path.to_string(),
                offset_bits: offset.offset.to_bits(),
                scale_bits: offset.scale.to_bits(),
            }
        })
        .collect();
    InstanceKey(arcs)
}

impl IndexCache {
    /// Clears the shared-prototype registry (spec 11.3.3) so stale
    /// instance-to-prototype mappings do not survive a composition change.
    ///
    /// TODO: this drops the whole registry on any invalidation; a targeted
    /// invalidation that removes only the prototypes whose instances changed
    /// would avoid recomputing unaffected keys.
    pub(crate) fn invalidate_prototypes(&mut self) {
        self.prototypes.clear();
    }

    /// Returns `true` if `path` resolves as an instance prim (spec 11.3.3):
    /// the strongest `instanceable` opinion is `true` and the prim has at
    /// least one composition arc. Reads the index directly (not through
    /// [`Self::resolve_field`]) so it is safe to call from path redirection.
    pub(crate) fn is_instance(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_abs_root() {
            return Ok(false);
        }
        self.ensure_index(graph, path)?;
        let index = &self.indices[path];
        if !index.has_composition_arc() {
            return Ok(false);
        }
        Ok(matches!(
            index.resolve_field(FieldKey::Instanceable.as_str(), graph, None)?,
            Some(Value::Bool(true))
        ))
    }

    /// Returns the canonical instance whose composed subtree is shared by
    /// every instance with `instance`'s instancing key. The first instance
    /// registered for a key becomes canonical; later instances with the same
    /// key reuse its subtree, so it is composed only once (spec 11.3.3).
    //
    // TODO(rayon): distinct prototypes (distinct instancing keys) compose
    // independent subtrees, so the canonical instances can be composed in
    // parallel. The `Indexer` already takes only `&` references; this needs
    // the cache to build indices off the `&mut self` path first (e.g. compose
    // into per-prototype results, then insert), and the shared `LayerGraph`
    // handed to workers as `&`/`Arc`.
    fn canonical_instance(&mut self, graph: &LayerGraph, instance: &Path) -> Result<Path> {
        Ok(self.register_prototype(graph, instance)?.0)
    }

    /// Composes `instance` and registers it against its prototype, returning the
    /// `(canonical instance, prototype path)` pair. Composing the index here
    /// (and computing its [`InstanceKey`]) is the cache's job; the dedup is the
    /// [`PrototypeRegistry`]'s.
    fn register_prototype(&mut self, graph: &LayerGraph, instance: &Path) -> Result<(Path, Path)> {
        self.ensure_index(graph, instance)?;
        let key = instance_key(&self.indices[instance], instance.prim_element_count() as u16);
        Ok(self.prototypes.register(key, instance))
    }

    /// Returns the synthetic prototype path (`/__Prototype_N`) shared by
    /// `instance`, registering it on first use. `None` when `instance` is not
    /// an instance prim (spec 11.3.3).
    pub(crate) fn prototype_of(&mut self, graph: &LayerGraph, instance: &Path) -> Result<Option<Path>> {
        if !self.is_instance(graph, instance)? {
            return Ok(None);
        }
        Ok(Some(self.register_prototype(graph, instance)?.1))
    }

    /// The instances sharing the prototype at `prototype` (a `/__Prototype_N`
    /// path), sorted by namespace path. Empty for unknown paths.
    pub(crate) fn instances_of(&self, prototype: &Path) -> Vec<Path> {
        self.prototypes.instances_of(prototype)
    }

    /// The registered `/__Prototype_N` roots, in registration order.
    pub(crate) fn prototypes(&self) -> Vec<Path> {
        self.prototypes.roots()
    }

    /// Returns `true` if `path` is a `/__Prototype_N` root.
    pub(crate) fn is_prototype(&self, path: &Path) -> bool {
        self.prototypes.is_root(path)
    }

    /// Returns `true` if `path` lies within a prototype's namespace — i.e. it
    /// has a `/__Prototype_N` ancestor (spec 11.3.3).
    pub(crate) fn is_in_prototype(&self, path: &Path) -> bool {
        self.prototypes.is_in_prototype(path)
    }

    /// Maps a prim path to the path that actually composes it. A descendant of
    /// a non-canonical instance is redirected into the canonical instance's
    /// subtree, so identical instances share one composition (spec 11.3.3).
    /// Other paths pass through unchanged.
    ///
    /// Nested instances work without special handling: the walk redirects to
    /// the nearest enclosing instance, so a nested instance resolves to its own
    /// shared prototype.
    fn redirect_prim(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Path> {
        match self.redirect_anchor(graph, prim)? {
            Some((origin, canonical)) => Ok(prim.replace_prefix(&origin, &canonical).unwrap_or_else(|| prim.clone())),
            None => Ok(prim.clone()),
        }
    }

    /// If `prim` lies within a shared prototype's namespace, returns the
    /// `(origin, canonical)` prefixes that map between the queried namespace
    /// and the composed one: a `/__Prototype_N` root or a non-canonical
    /// instance prim (`origin`) and the canonical instance backing it
    /// (`canonical`). Returns `None` when `prim` composes in place.
    pub(super) fn redirect_anchor(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Option<(Path, Path)>> {
        // A `/__Prototype_N[/tail]` query maps into the canonical instance's
        // subtree, so the synthetic prototype namespace is addressable.
        if let Some(root) = self.prototypes.enclosing_root(Some(prim.clone())) {
            let canonical = self
                .prototypes
                .canonical_of(&root)
                .expect("enclosing root is a registered prototype");
            return Ok(Some((root, canonical)));
        }

        let mut ancestor = prim.parent();
        while let Some(current) = ancestor {
            if current.is_abs_root() {
                break;
            }
            if self.is_instance(graph, &current)? {
                let canonical = self.canonical_instance(graph, &current)?;
                if canonical != current {
                    return Ok(Some((current, canonical)));
                }
                // Nearest instance is canonical: compose this subtree in place.
                break;
            }
            ancestor = current.parent();
        }
        Ok(None)
    }

    /// Redirects `path` (prim or property) through [`Self::redirect_prim`],
    /// preserving any property suffix. Applied at every descendant-serving
    /// query entry point so non-canonical instance subtrees are never built.
    //
    // TODO(perf): every call walks the path's ancestors to find an enclosing
    // instance. The result is stable until the prototype registry is
    // invalidated, so it could be memoized per prim path and cleared alongside
    // `invalidate_prototypes`.
    pub(super) fn effective_path(&mut self, graph: &LayerGraph, path: &Path) -> Result<Path> {
        let prim = path.prim_path();
        let redirected = self.redirect_prim(graph, &prim)?;
        if redirected == prim {
            return Ok(path.clone());
        }
        // Re-anchor any property suffix onto the redirected prim; for a prim
        // path this is the redirected prim itself.
        Ok(path.replace_prefix(&prim, &redirected).unwrap_or(redirected))
    }
}
