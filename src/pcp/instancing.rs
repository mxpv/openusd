//! Scene-graph instancing: shared prototypes for `instanceable` prims (spec
//! 11.3.3).
//!
//! Instances with the same [`InstanceKey`] — the arc-introduced opinions that
//! define their subtree, independent of stage path — share one composed
//! prototype. [`PrototypeRegistry`] owns that mapping (an [`IndexCache`] holds
//! one as a field); the composition-coupled glue stays on `IndexCache` because
//! it needs the composed indices, and every descendant-serving query enters
//! through [`IndexCache::effective_path`], which redirects an instance proxy's
//! subtree into the canonical instance's in-place composition so identical
//! instances are composed only once. The prototype *root* itself is materialized
//! as an independent `/__Prototype_N` index so its shared content is addressable
//! without the canonical instance's root-level overrides leaking in.

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
/// (spec 11.3.3). The prototype *root* is composed as an independent
/// `/__Prototype_N` index, built from the canonical instance's shared subtree —
/// the instanceable arc, its descendants, and the implied classes — with the
/// instance-local opinions (the local root override and the ancestral references
/// above the instanceable arc) inerted (see
/// [`PrimIndex::mark_instance_local_inert`]) and the namespace re-anchored onto
/// the prototype root (see [`PrimIndex::rebase_root`]). Its descendants and the
/// instance proxies of every sharing instance are served from the canonical
/// instance's in-place composition through [`IndexCache::redirect_anchor`], so
/// identical instances compose once. Materializing the root is what keeps a
/// query on `/__Prototype_N` itself free of the canonical instance's root-level
/// overrides (spec 11.3.3 permits overriding property values at an instance
/// root).
struct Prototype {
    /// Registration order (the `N` in `/__Prototype_N`). Kept so prototypes can
    /// be returned in mint order without parsing the path.
    index: usize,
    /// Instance whose composed subtree seeds this prototype's materialization.
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
    /// Returns the canonical instance, the prototype path, and whether this call
    /// minted a new prototype (so the caller knows to materialize its index).
    fn register(&mut self, key: InstanceKey, instance: &Path) -> (Path, Path, bool) {
        if let Some(root) = self.by_key.get(&key) {
            let root = root.clone();
            let prototype = self.by_root.get_mut(&root).expect("key index points to a prototype");
            if !prototype.instances.contains(instance) {
                prototype.instances.push(instance.clone());
            }
            return (prototype.canonical.clone(), root, false);
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
        (instance.clone(), path, true)
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
    /// Clears the shared-prototype registry (spec 11.3.3) and evicts every
    /// materialized `/__Prototype_N` index so stale instance-to-prototype
    /// mappings do not survive a composition change. Prototypes are recomposed
    /// lazily on the next instancing query.
    ///
    /// TODO: this drops the whole registry on any invalidation; a targeted
    /// invalidation that removes only the prototypes whose instances changed
    /// would avoid recomputing unaffected keys.
    pub(crate) fn invalidate_prototypes(&mut self) {
        // Only the prototype root is cached — its descendants and the instance
        // proxies of every sharing instance are served from the canonical
        // instance (see [`Self::redirect_anchor`]), so the cache holds nothing
        // under `/__Prototype_N`. A single `drop_index` per root therefore
        // suffices and avoids a full-cache subtree scan per prototype.
        for root in self.prototypes.roots() {
            self.drop_index(&root);
        }
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

    /// Composes `instance`, registers it against its prototype, and materializes
    /// the prototype's index on first use, returning the `(canonical instance,
    /// prototype path)` pair. The first instance registered for a key becomes
    /// canonical and seeds the prototype; later instances with the same key reuse
    /// the already-materialized prototype, so its subtree is composed only once
    /// (spec 11.3.3). Composing the index here (and computing its [`InstanceKey`])
    /// is the cache's job; the dedup is the [`PrototypeRegistry`]'s.
    fn register_prototype(&mut self, graph: &LayerGraph, instance: &Path) -> Result<(Path, Path)> {
        self.ensure_index(graph, instance)?;
        let key = instance_key(&self.indices[instance], instance.prim_element_count() as u16);
        let (canonical, prototype, minted) = self.prototypes.register(key, instance);
        // Materialize the prototype's index only when this call minted it. Keying
        // off the registry's signal (not `indices.contains_key`) means a stale
        // index cached at the synthetic path — e.g. from an earlier query on the
        // deterministic `/__Prototype_N` before any instance composed — is
        // overwritten with the real composition rather than mistaken for it.
        if minted {
            self.materialize_prototype(graph, &canonical, &prototype);
        }
        Ok((canonical, prototype))
    }

    /// Builds and caches the composed index for a freshly minted prototype root
    /// (`/__Prototype_N`) from the canonical instance's shared subtree (spec
    /// 11.3.3). The clone of the canonical index has its instance-local nodes
    /// inerted at the instance root's own depth, so only the instanceable arc,
    /// its descendants, and the implied classes contribute — the local root
    /// override and the ancestral references above the instanceable arc drop out
    /// — and its namespace is re-anchored onto the prototype root.
    ///
    /// The prototype root's child context is seeded as a namespace root with
    /// `instance_depth` cleared (it is not itself an instance — its `instanceable`
    /// opinion is inert), so a descendant built by deepening this graph composes
    /// as prototype content rather than instance-suppressed. Ordinary queries
    /// still serve descendants from the canonical instance via
    /// [`Self::redirect_anchor`], so the prototype graph is rarely deepened, but
    /// the seeded context keeps that path correct rather than silently empty.
    //
    // TODO(rayon): distinct prototypes (distinct instancing keys) compose
    // independent subtrees, so they can be materialized in parallel. The
    // `Indexer` already takes only `&` references; this needs the cache to build
    // off the `&mut self` path first (compose into per-prototype results, then
    // insert) and the shared `LayerGraph` handed to workers as `&`/`Arc`.
    fn materialize_prototype(&mut self, graph: &LayerGraph, canonical: &Path, prototype: &Path) {
        let mut index = self.indices[canonical].clone();
        index.mark_instance_local_inert(canonical.prim_element_count() as u16);
        // Re-anchor the seeding instance's composed namespace onto the prototype
        // root so the root's own target translation lands in the prototype
        // namespace, not the canonical instance's.
        index.rebase_root(canonical, prototype);

        let mut context = index.context_for_children(graph, &self.root_parent_context());
        context.instance_depth = None;
        self.cache_index(graph, prototype, index, context);
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

    /// Returns `true` if `path` is an instance proxy — a descendant of an
    /// instance prim, in the instance's own namespace, standing in for a prim in
    /// the shared prototype (spec 11.3.3). A prim inside a `/__Prototype_N`
    /// namespace is in a prototype, not a proxy, so it returns `false`.
    ///
    /// A proxy stands in for a real prim in the shared prototype, so a path under
    /// an instance that composes to no prim (e.g. a misspelled child) is not a
    /// proxy — mirroring the existence check on [`Self::is_instance`] /
    /// `Prim::is_valid`.
    ///
    /// Limitation: a prim under a *nested* instance that itself lives inside a
    /// prototype namespace (`/__Prototype_N/.../NestedInstance/child`) is
    /// reported as in-prototype rather than as a proxy. Modeling those requires
    /// composing each prototype subtree independently, which is the broader
    /// descendant-aliasing gap tracked in the [`pcp`](super) module docs; proxies
    /// in the ordinary instance namespace are unaffected.
    pub(crate) fn is_instance_proxy(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_abs_root() || self.is_prototype(path) || self.is_in_prototype(path) {
            return Ok(false);
        }
        if self.enclosing_instance(graph, path)?.is_none() {
            return Ok(false);
        }
        self.has_spec(graph, path)
    }

    /// Returns the prim in the shared prototype an instance proxy stands in for:
    /// a proxy `instance/tail` maps to `/__Prototype_N/tail` (spec 11.3.3).
    /// `None` when `path` is not an instance proxy (including a path under an
    /// instance that composes to no prim).
    pub(crate) fn prim_in_prototype(&mut self, graph: &LayerGraph, path: &Path) -> Result<Option<Path>> {
        if !self.is_instance_proxy(graph, path)? {
            return Ok(None);
        }
        let instance = self
            .enclosing_instance(graph, path)?
            .expect("an instance proxy has an enclosing instance");
        let (_canonical, prototype) = self.register_prototype(graph, &instance)?;
        Ok(path.replace_prefix(&instance, &prototype))
    }

    /// Returns the nearest strict ancestor of `path` that resolves as an
    /// instance prim (spec 11.3.3), or `None` when `path` is not inside an
    /// instance.
    fn enclosing_instance(&mut self, graph: &LayerGraph, path: &Path) -> Result<Option<Path>> {
        let mut ancestor = path.parent();
        while let Some(current) = ancestor {
            if current.is_abs_root() {
                break;
            }
            if self.is_instance(graph, &current)? {
                return Ok(Some(current));
            }
            ancestor = current.parent();
        }
        Ok(None)
    }

    /// Maps a prim path to the path that actually composes it. An instance
    /// proxy — a descendant of an instance prim — and a prototype descendant are
    /// redirected into the canonical instance's in-place composition, so
    /// identical instances share one subtree (spec 11.3.3). Other paths — the
    /// canonical instance's own subtree, the materialized prototype root, and
    /// non-instanced prims — pass through unchanged.
    fn redirect_prim(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Path> {
        match self.redirect_anchor(graph, prim)? {
            Some((origin, canonical)) => Ok(prim.replace_prefix(&origin, &canonical).unwrap_or_else(|| prim.clone())),
            None => Ok(prim.clone()),
        }
    }

    /// Returns the `(origin, canonical)` prefixes that map `prim`'s queried
    /// namespace onto the canonical instance's in-place composition, or `None`
    /// when `prim` composes in place (spec 11.3.3). The shared subtree of a set
    /// of identical instances is composed once, under the canonical instance:
    ///
    /// - A descendant inside a prototype's namespace (`/__Prototype_N/tail`)
    ///   maps to the canonical instance backing that prototype. The prototype
    ///   *root* itself (`/__Prototype_N`, no tail) composes in place from its
    ///   materialized index, so its root-level overrides do not leak.
    /// - An instance proxy (a descendant of a non-canonical instance) maps to
    ///   the canonical instance. The canonical instance's own subtree, and every
    ///   non-instanced prim, compose in place.
    ///
    /// Nested instances need no special handling: the walk stops at the nearest
    /// enclosing instance, so a nested instance proxy resolves against its own
    /// canonical instance.
    pub(super) fn redirect_anchor(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Option<(Path, Path)>> {
        // Inside a prototype's namespace, the root composes in place from its
        // materialized index; a descendant aliases to the canonical instance.
        if let Some(root) = self.prototypes.enclosing_root(Some(prim.clone())) {
            if *prim == root {
                return Ok(None);
            }
            let canonical = self
                .prototypes
                .canonical_of(&root)
                .expect("enclosing root is a registered prototype");
            return Ok(Some((root, canonical)));
        }

        // An instance proxy maps to the canonical instance backing its nearest
        // enclosing instance; the canonical instance's own subtree composes in
        // place (it is the canonical of its own prototype).
        if let Some(instance) = self.enclosing_instance(graph, prim)? {
            let (canonical, _prototype) = self.register_prototype(graph, &instance)?;
            if canonical != instance {
                return Ok(Some((instance, canonical)));
            }
        }
        Ok(None)
    }

    /// Redirects `path` (prim or property) through [`Self::redirect_prim`],
    /// preserving any property suffix. Applied at every descendant-serving
    /// query entry point so an instance proxy's subtree is served from the
    /// shared prototype rather than recomposed per instance.
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
