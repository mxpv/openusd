//! Scene-graph instancing: shared prototypes for `instanceable` prims (spec
//! 11.3.3).
//!
//! Instances with the same [`InstanceKey`] — the arc-introduced opinions that
//! define their subtree, independent of stage path — share one composed
//! prototype. [`PrototypeRegistry`] owns that mapping (an [`IndexCache`] holds
//! one as a field); the composition-coupled glue stays on `IndexCache` because
//! it needs the composed indices. The prototype *namespace* is the single
//! composition of a set of identical instances and composes in place: the root
//! from its materialized `/__Prototype_N` index, a descendant by deepening that
//! graph. Every descendant-serving query enters through
//! [`IndexCache::effective_path`], which redirects an instance proxy `/A/tail`
//! onto `/__Prototype_N/tail` so identical instances are composed only once,
//! while an instance root composes in place (it may override property values).
//! Materializing the root independently keeps its shared content addressable
//! without the seeding instance's root-level overrides leaking in.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};

use anyhow::Result;

use crate::sdf;
use crate::sdf::schema::FieldKey;
use crate::sdf::{Path, PathElement, Value};
use crate::tf::Token;

use super::LayerId;
use super::index_cache::IndexCache;
use super::layer_graph::LayerGraph;
use super::load_rules::LoadRules;
use super::population_mask::PopulationMask;
use super::prim_graph::ArcType;
use super::prim_index::PrimIndex;
use super::prim_indexer::ExprVarDeps;

/// The shared-prototype registry (spec 11.3.3): maps each instancing key to its
/// prototype and tracks the instances that share it. Owns no composition state
/// — the [`IndexCache`] computes an [`InstanceKey`] from a composed index and
/// hands it to [`register`](Self::register); the registry only dedups by key,
/// mints `/__Prototype_N` identities, and answers prototype/instance queries.
#[derive(Default)]
pub(super) struct PrototypeRegistry {
    /// Prototypes keyed by their `/__Prototype_N` root path. A namespace-aware
    /// table so the common query direction (path to prototype) is a single
    /// lookup, while change invalidation can fan a touched path up to an
    /// enclosing root and down to nested roots without scanning every entry.
    by_root: sdf::PathTable<Prototype>,
    /// Reverse index from each instance's composed path to its `/__Prototype_N`
    /// root, so a changed path resolves to the prototypes whose instances it
    /// touches via bounded ancestor/subtree lookups rather than a full scan. A
    /// nested instance is keyed by its prim inside the enclosing prototype, so
    /// those lookups reach it through that prototype's namespace.
    by_instance: sdf::PathTable<Path>,
    /// Maps an instancing key to its prototype root, the lookup direction used
    /// only when registering an instance to dedup against an existing key.
    by_key: HashMap<InstanceKey, Path>,
    /// Counter for minting `/__Prototype_N` identities in registration order.
    /// Never rewound — [`remove_affected`](Self::remove_affected) leaves it
    /// alone — so a `/__Prototype_N` identity is never reused for a different
    /// composition within a session.
    count: usize,
}

/// A shared prototype for a set of instances with the same [`InstanceKey`]
/// (spec 11.3.3). The prototype *root* is composed as an independent
/// `/__Prototype_N` index, built from the canonical instance's shared subtree —
/// the instanceable arc, its descendants, and the implied classes — with the
/// instance-local opinions (the local root override and the ancestral references
/// above the instanceable arc) inerted (see
/// [`PrimIndex::mark_instance_local_inert`]) and the namespace re-anchored onto
/// the prototype root (see [`PrimIndex::rebase_root`]). Its descendants compose
/// in place by deepening that graph, and every sharing instance's proxies
/// redirect onto the prototype namespace through [`IndexCache::redirect_anchor`],
/// so identical instances compose once. Materializing the root is what keeps a
/// query on `/__Prototype_N` itself free of the seeding instance's root-level
/// overrides (spec 11.3.3 permits overriding property values at an instance
/// root).
pub(super) struct Prototype {
    /// Registration order (the `N` in `/__Prototype_N`). Kept so prototypes can
    /// be returned in mint order without parsing the path.
    index: usize,
    /// Every instance sharing this prototype, by composed path — so a nested
    /// instance appears once, as its prim inside the enclosing prototype,
    /// however many proxies stand for it. The first is the canonical instance,
    /// whose composed subtree seeded the materialization.
    instances: Vec<Path>,
    /// The canonical instance's load rules, re-rooted onto the path it composes
    /// at (`LoadRules::make_relative_to`), so a `/__Prototype_N` descendant
    /// build resolves its own payload-inclusion decision against the
    /// instance's authored rules (see `IndexCache::scoped_load_rules`). For a
    /// nested instance that path lies inside the enclosing prototype, so the
    /// rules are already that prototype's relative table.
    pub(super) relative_load_rules: LoadRules,
    /// The canonical instance's population mask, re-rooted onto the path it
    /// composes at (`PopulationMask::make_relative_to`), so a query inside this
    /// prototype's namespace resolves against the mask in the instance
    /// namespace its author wrote it in (see `IndexCache::scoped_mask`). Every
    /// instance sharing this prototype has the same one, because it is part of
    /// the [`InstanceKey`].
    pub(super) relative_mask: PopulationMask,
}

/// Identity of an instance prim's shared composition (spec 11.3.3): the
/// arc-introduced opinions that determine its subtree, independent of the
/// instance's own stage path. Instances with equal keys share a prototype.
///
/// Variant selections are folded in explicitly via [`selections`](Self::selections)
/// rather than left implicit in the arc paths: each arc's path has its variant
/// selections stripped (so two instances of the same reference produce the same
/// arc path regardless of which variant they pick) and the resolved selection
/// set is carried as a separate, path-independent list. Without the explicit
/// list, two instances of one reference that differ only by a variant selection
/// would collide once the selection is stripped from the path.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct InstanceKey {
    arcs: Vec<InstanceArc>,
    /// The resolved `(variant set, selection)` pairs, in composition order.
    selections: Vec<(String, String)>,
    /// The instance's load rules, re-rooted onto its own path
    /// (`LoadRules::make_relative_to`). Two otherwise-identical instances
    /// with different load rules mint separate prototypes (C++
    /// `Usd_InstanceKey`), since a shared prototype's descendants must
    /// resolve one consistent payload-inclusion decision.
    load_rules: LoadRules,
    /// The instance's population mask, re-rooted onto its own path
    /// (`PopulationMask::make_relative_to`). Two otherwise-identical instances
    /// the mask exposes differently mint separate prototypes (C++
    /// `Usd_InstanceKey`), since a shared prototype composes one subtree and
    /// that subtree is filtered by the mask.
    ///
    /// C++ also folds each instance's value-clip definitions into the key; this
    /// port does not, so the key is not yet fully `Usd_InstanceKey`-equivalent.
    mask: PopulationMask,
}

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
    /// Registers an instance against its prototype: dedups by `key`, recording
    /// the instance the first time a key is seen and minting `/__Prototype_N`.
    /// Returns the prototype path and whether this call minted it (so the caller
    /// knows to materialize its index, seeding from the `composed` that minted
    /// it — the prototype's canonical instance). `key.load_rules` and
    /// `key.mask` are stored as the prototype's relative load rules and mask
    /// only on the minting call — a cache hit's existing entry is already
    /// guaranteed identical, since both were part of the matched key.
    ///
    /// `composed` is the path whose index composes the instance
    /// ([`IndexCache::effective_path`]), which is the instance's identity here:
    /// every proxy standing for one nested instance shares a single entry, in
    /// the enclosing prototype's namespace.
    fn register(&mut self, key: InstanceKey, composed: &Path) -> (Path, bool) {
        if let Some(root) = self.by_key.get(&key) {
            let root = root.clone();
            // The reverse index answers "already registered here?" in one lookup,
            // and the two are written together below.
            if self.by_instance.get(composed) != Some(&root) {
                let prototype = self.by_root.get_mut(&root).expect("key index points to a prototype");
                prototype.instances.push(composed.clone());
                self.by_instance.insert(composed.clone(), root.clone());
            }
            return (root, false);
        }

        let index = self.count;
        let path = Path::new(&format!("/{PROTOTYPE_PREFIX}{index}")).expect("synthetic prototype path is valid");
        self.count += 1;
        let relative_load_rules = key.load_rules.clone();
        let relative_mask = key.mask.clone();
        self.by_key.insert(key, path.clone());
        self.by_root.insert(
            path.clone(),
            Prototype {
                index,
                instances: vec![composed.clone()],
                relative_load_rules,
                relative_mask,
            },
        );
        self.by_instance.insert(composed.clone(), path.clone());
        (path, true)
    }

    /// The prototype registered at `prototype`, holding the canonical
    /// instance's load rules and population mask re-rooted onto the path it
    /// composes at. `None` for an unknown path.
    fn get(&self, prototype: &Path) -> Option<&Prototype> {
        self.by_root.get(prototype)
    }

    /// The canonical instance backing the prototype at `prototype` — the first
    /// registered, which seeded its materialization — or `None` for an unknown
    /// path. Used by registry tests to assert a prototype's presence; production
    /// composition reaches the prototype directly through
    /// [`register`](Self::register)'s return.
    #[cfg(test)]
    fn canonical_of(&self, prototype: &Path) -> Option<Path> {
        self.by_root.get(prototype).and_then(|p| p.instances.first().cloned())
    }

    /// The instances sharing the prototype at `prototype` (a `/__Prototype_N`
    /// path), by composed path and sorted by namespace path, so neither the
    /// membership nor the order depends on how the instances were queried
    /// ([`register`](Self::register)). Empty for unknown paths.
    fn instances_of(&self, prototype: &Path) -> Vec<Path> {
        let mut instances = self
            .by_root
            .get(prototype)
            .map_or_else(Vec::new, |p| p.instances.clone());
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

    /// Returns the nearest registered `/__Prototype_N` root at or above `path`,
    /// inclusive of `path` itself, or `None` when it is outside every
    /// registered prototype namespace.
    fn enclosing_root(&self, path: &Path) -> Option<Path> {
        self.by_root.nearest_ancestor(path).map(|(root, _)| root.clone())
    }

    /// Removes every prototype the change set could have invalidated, returning
    /// the dropped `/__Prototype_N` roots so the cache can evict their indices.
    /// A prototype is affected when a changed prim path lies on the ancestor
    /// chain of one of its instances (the instance's `instanceable` opinion,
    /// arcs, or shared content may have changed) or of its prototype root.
    /// Unaffected prototypes keep their instance-to-prototype mapping and
    /// materialized index, so a localized edit no longer forces every key to be
    /// recomputed (spec 11.3.3).
    ///
    /// `count` stays monotonic (see its doc), so a re-registered instance mints
    /// a fresh identity rather than reusing a removed prototype's number.
    ///
    /// Each changed path resolves to the prototypes it could affect through
    /// bounded lookups: the [`by_root`](Self::by_root) entries nested with it
    /// (an enclosing root above, or `/__Prototype_N` roots below) and, via the
    /// [`by_instance`](Self::by_instance) reverse index, the prototypes whose
    /// instances it is nested with. The cost scales with the change set and the
    /// touched subtrees, not the total prototype count.
    ///
    /// A nested instance is registered inside its enclosing prototype's
    /// namespace, so an affected root is itself a path to sweep: each newly
    /// affected root rejoins the worklist and a whole nesting chain drops
    /// together. A root is enqueued only on its first insertion into `affected`,
    /// which both terminates the sweep and puts its scan count at the change set
    /// plus the affected roots. The closure is computed in full before anything
    /// is removed, since the table entries are the edges to the deeper
    /// prototypes.
    fn remove_affected(&mut self, changed: &[Path]) -> Vec<Path> {
        let mut affected: HashSet<Path> = HashSet::new();
        let mut worklist: Vec<&Path> = changed.iter().collect();
        while let Some(p) = worklist.pop() {
            let roots = self.by_root.ancestors(p).chain(self.by_root.subtree(p));
            let instances = self.by_instance.ancestors(p).chain(self.by_instance.subtree(p));
            let touched = roots.map(|(root, _)| root).chain(instances.map(|(_, root)| root));
            for root in touched {
                if !affected.contains(root) {
                    affected.insert(root.clone());
                    worklist.push(root);
                }
            }
        }
        for root in &affected {
            if let Some(prototype) = self.by_root.remove(root) {
                for instance in &prototype.instances {
                    self.by_instance.remove(instance);
                }
            }
        }
        self.by_key.retain(|_, root| !affected.contains(root));
        // Sorted so a cascade returns its roots in a stable order, whatever the
        // hash set's iteration happens to be.
        let mut dropped: Vec<Path> = affected.into_iter().collect();
        dropped.sort();
        dropped
    }
}

/// The reserved name every synthetic prototype root starts with. The mint
/// ([`PrototypeRegistry::register`]) writes it and
/// [`is_prototype_namespace`] recognizes it, so the spelling has one owner.
const PROTOTYPE_PREFIX: &str = "__Prototype_";

/// Whether `path` lies in the reserved prototype namespace *syntactically* — it
/// is a synthetic root or a descendant of one — whether or not any prototype is
/// registered there (C++ `Usd_InstanceCache::IsPathInPrototype`).
///
/// This is the predicate for namespace *policy*, which must not depend on how
/// much has been composed: a load rule naming `/__Prototype_9` is meaningless
/// before that root exists just as much as after. Whether a live prototype
/// stands at a path is [`IndexCache::is_prototype`]; whether a path is inside
/// one is [`IndexCache::is_in_prototype`].
pub(crate) fn is_prototype_namespace(path: &Path) -> bool {
    path.is_abs()
        && path
            .root_prim_name()
            .is_some_and(|name| name.starts_with(PROTOTYPE_PREFIX))
}

/// Computes the instancing key for an already-built instance index: the
/// arc-introduced (shared) opinions that define the prototype subtree,
/// independent of the instance's own stage path (spec 11.3.3).
/// `instance_depth` is the instance prim's own namespace depth, used to
/// partition shared from instance-local nodes
/// ([`PrimIndex::instance_local_nodes`]).
///
/// Each contributing arc's path is stripped of variant selections, and the
/// resolved selection set is folded into the key explicitly (see
/// [`InstanceKey`]), so two instances of one reference share a prototype iff
/// their variant selections also match. `load_rules` and `mask` are the
/// instance's load rules and population mask, already re-rooted onto its own
/// path (`LoadRules::make_relative_to`, `PopulationMask::make_relative_to`), so
/// two instances also only share a prototype when their load state and their
/// exposure agree.
fn instance_key(index: &PrimIndex, instance_depth: u16, load_rules: LoadRules, mask: PopulationMask) -> InstanceKey {
    let local = index.instance_local_nodes(instance_depth, instance_depth);
    let mut arcs = Vec::new();
    let mut selections = Vec::new();
    for (id, node) in index.nodes_with_ids() {
        if local[id.idx()] || node.is_culled() {
            continue;
        }
        if node.arc == ArcType::Variant
            && let Some(PathElement::Variant { set, selection }) = node.path.last_element()
        {
            selections.push((set.to_string(), selection.to_string()));
        }
        let offset = node.map_to_root.time_offset();
        arcs.push(InstanceArc {
            arc: node.arc as u8,
            layer: node.layer_id(),
            path: node.path.strip_all_variant_selections().to_string(),
            offset_bits: offset.offset.to_bits(),
            scale_bits: offset.scale.to_bits(),
        });
    }
    InstanceKey {
        arcs,
        selections,
        load_rules,
        mask,
    }
}

impl IndexCache {
    /// Evicts only the prototypes a prim-level change touches (spec 11.3.3):
    /// every prototype whose instance subtree or prototype namespace lies on the
    /// ancestor chain of one of the `changed` prim paths is removed from the
    /// registry and has its materialized `/__Prototype_N` index dropped.
    /// Unaffected prototypes keep their mapping and index, so a localized edit
    /// does not recompute every key.
    ///
    /// Pure analysis over the change list (no composition), so it stays
    /// rayon-friendly: see [`PrototypeRegistry::remove_affected`]. A layer-stack
    /// edit instead drops the affected prototypes through
    /// [`Self::invalidate_layers`].
    ///
    /// Returns the roots it retired, sorted. A caller reporting what an edit
    /// invalidated must name them in their own right: the retirement cascades
    /// through a worklist, so a nested root goes without any `changed` path
    /// covering it, and a `/__Prototype_N` root stands in its own namespace where
    /// no instance path could subsume it.
    pub(crate) fn invalidate_prototypes(&mut self, changed: &[Path]) -> Vec<Path> {
        // A prototype's whole namespace composes in place now (the root from its
        // materialized index, descendants by deepening it; see
        // [`Self::redirect_anchor`]), so each affected root's entire subtree must
        // be dropped, not just the root spec.
        //
        // TODO(perf): `drop_index_subtree` is an O(n) cache scan per affected
        // root; batching the affected roots into one prefix-filtered pass (or an
        // `SdfPathTable`-like trie) would bound it by the change set. A change
        // reaching a nested instance drops its whole prototype chain, so the
        // per-root cost is paid once per level.
        // The dropped roots owned redirections and eligibility answers of their
        // own, so those memos go with them.
        self.clear_population_memos();
        let retired = self.prototypes.remove_affected(changed);
        for root in &retired {
            self.drop_index_subtree(root);
        }
        retired
    }

    /// Whether the stage's population admits `path` — the mask exposes it, it
    /// exists, and it and every ancestor are active. C++'s `_NameChildrenPred`
    /// gate, which decides both whether to descend past a prim and whether its
    /// index may register as an instance.
    ///
    /// This is eligibility for population traversal and instance registration,
    /// **not** prim existence: an inactive prim still exists and still composes,
    /// and C++ instantiates it too — what it suppresses is that prim's
    /// descendants and its instance registration. So the only two callers are
    /// [`Self::is_instance`] and the stage's discovery walk; it must never gate
    /// [`Self::has_spec`], `Prim::is_valid`, or any ordinary read.
    ///
    /// The steps are ordered so nothing below an excluded or inactive ancestor
    /// is ever composed or loaded: the mask test is pure, the parent is settled
    /// before the prim itself, and only then does `path` compose.
    ///
    /// Memoized in `populated_prims`, which makes the recursion O(1) amortized
    /// rather than an ancestor walk per query — the ancestors settle first, so
    /// each is a hit by the time a deeper query asks. As in
    /// [`Self::effective_path`], a result reached while a build demanded a
    /// not-yet-loaded layer is provisional and left unmemoized, and a path in an
    /// unregistered synthetic prototype namespace is never memoized at all,
    /// since registering that prototype changes the answer without an edit.
    ///
    /// Terminates because every step moves to a strictly shorter path: the
    /// parent recursion by construction, and the existence check only through
    /// [`Self::enclosing_instance`], which walks strict ancestors (see
    /// [`Self::is_instance`]).
    pub(crate) fn is_populated(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_abs_root() {
            return Ok(true);
        }
        if let Some(hit) = self.populated_prims.get(path) {
            return Ok(*hit);
        }
        let pending_before = self.pending_loads.len();
        let parent = path.parent().expect("a non-root path has a parent");
        // Short-circuiting is what orders the steps: the mask test composes
        // nothing, and neither the prim nor its own `active` is reached until
        // its parent is settled. The redirect is resolved once and both reads
        // take it, rather than each finding it again.
        let populated = self.mask_includes(path) && self.is_populated(graph, &parent)? && {
            let composed = self.effective_path(graph, path)?;
            self.has_spec_at(graph, &composed)? && self.active_at(graph, &composed)?
        };
        if !self.provisional(path, pending_before) {
            self.populated_prims.insert(path.clone(), populated);
        }
        Ok(populated)
    }

    /// Whether an answer just computed for `path` may change with no edit to
    /// notice, and so must not be memoized. Two ways it can, and every memo in
    /// this cache has to respect both:
    ///
    /// - The work demanded a layer that was not yet loaded (`pending_loads`
    ///   grew since `pending_before`), so it read the empty-on-miss index; the
    ///   stage's load loop recomputes it once the layer is in.
    /// - It names an unregistered synthetic prototype namespace, where minting
    ///   the root turns "composes nothing" into shared content
    ///   ([`Self::in_unregistered_prototype`]).
    pub(super) fn provisional(&self, path: &Path, pending_before: usize) -> bool {
        self.pending_loads.len() != pending_before || self.in_unregistered_prototype(path)
    }

    /// Whether `path` sits in the reserved prototype namespace with no
    /// prototype registered there — a path that composes to nothing today and
    /// to shared content once some instance mints its root.
    pub(super) fn in_unregistered_prototype(&self, path: &Path) -> bool {
        is_prototype_namespace(path) && self.prototype_root_of(path).is_none()
    }

    /// Returns `true` if `path` resolves as an instance prim (spec 11.3.3):
    /// the strongest `instanceable` opinion is `true` and the prim has at
    /// least one composition arc.
    ///
    /// A `/__Prototype_N` root is never an instance, whatever its composed
    /// `instanceable` opinion says. The opinion is routinely `true` there: an
    /// asset commonly authors `instanceable = true` on the very prim its
    /// referencing layer targets, so the opinion arrives on the instanceable arc
    /// itself and is shared content the prototype must keep. It describes the
    /// instances that share this prototype, not the prototype, which stands
    /// outside the instance namespace as the single composition those instances
    /// redirect onto. Exempting the root here is also what lets
    /// [`Self::redirect_anchor`] compose plain prototype content in place: were
    /// the root an instance, its own descendants would redirect back through it.
    /// A *nested* instance inside a prototype namespace is not a prototype root,
    /// so it still resolves as an instance and mints its own prototype.
    ///
    /// Reads `instanceable` off the index that actually composes `path` — for an
    /// instance proxy that is the shared `/__Prototype_N` index, reached through
    /// [`Self::effective_path`], not a throwaway per-instance copy. So checking
    /// instance-ness while walking a deep proxy subtree (every ancestor is tested
    /// by [`Self::enclosing_instance`]) composes the shared subtree once instead
    /// of a literal index per instance. `effective_path` re-enters `is_instance`
    /// on a strict ancestor to find the enclosing instance, but each step moves
    /// to a shorter path and bottoms out at the root, so the recursion
    /// terminates.
    pub(crate) fn is_instance(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_abs_root() || self.is_prototype(path) {
            return Ok(false);
        }
        // The stage populates no prim the mask excludes or an inactive ancestor
        // buries, and C++ composes the instance flag only for the prims it
        // populated — so nothing else can register a prototype either.
        if !self.is_populated(graph, path)? {
            return Ok(false);
        }
        let composed = self.effective_path(graph, path)?;
        self.ensure_index(graph, &composed)?;
        let index = self.cached(&composed);
        if !index.has_composition_arc() {
            return Ok(false);
        }
        Ok(matches!(
            index.resolve_field(FieldKey::Instanceable.as_str(), graph, None)?,
            Some(Value::Bool(true))
        ))
    }

    /// Composes `instance`'s shared subtree, registers it against its prototype,
    /// and materializes the prototype's index on first use, returning the
    /// prototype path. The first instance registered for a key becomes canonical
    /// and seeds the prototype; later instances with the same key reuse the
    /// already-materialized prototype, so its subtree is composed only once
    /// (spec 11.3.3). Composing the index here (and computing its
    /// [`InstanceKey`]) is the cache's job; the dedup is the
    /// [`PrototypeRegistry`]'s.
    fn register_prototype(&mut self, graph: &LayerGraph, instance: &Path) -> Result<Path> {
        // A nested instance can itself be an instance proxy. Its shared
        // composition lives at the corresponding prim inside the enclosing
        // prototype, so that is the index defining the nested prototype's key
        // and materialized root, and the identity it registers under.
        let composed = self.effective_path(graph, instance)?;
        self.ensure_index(graph, &composed)?;
        // Load rules are authored against the stage namespace, so they scope at
        // the path the instance composes at; `scoped_load_rules` translates a
        // path inside a prototype onto that prototype's stored relative rules.
        let relative_load_rules = {
            let (rules, relative_instance) = self.scoped_load_rules(&composed);
            rules.make_relative_to(&relative_instance)
        };
        // The mask scopes the same way and for the same reason: it names stage
        // paths, so a nested instance resolves it through the enclosing
        // prototype's stored relative mask.
        let relative_mask = {
            let (mask, relative_instance) = self.scoped_mask(&composed);
            mask.make_relative_to(&relative_instance)
        };
        let key = instance_key(
            self.cached(&composed),
            composed.prim_element_count() as u16,
            relative_load_rules,
            relative_mask,
        );
        let (prototype, minted) = self.prototypes.register(key, &composed);
        // Materialize the prototype's index only when this call minted it: the
        // minting registration made `composed` this prototype's canonical
        // instance, so its index is the one the prototype materializes from.
        // The namespace it fills is empty, since an unregistered synthetic path
        // composes and memoizes nothing (`IndexCache::in_unregistered_prototype`).
        if minted {
            self.materialize_prototype(graph, &composed, &prototype);
        }
        Ok(prototype)
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
    /// `instance_depth` cleared — a prototype root is not an instance (see
    /// [`Self::is_instance`]) — so a descendant built by deepening this graph
    /// composes as prototype content rather than instance-suppressed. Every
    /// instance proxy redirects onto this namespace through
    /// [`Self::redirect_anchor`], so the prototype subtree is the one place a set
    /// of identical instances' descendants compose.
    //
    // TODO(rayon): distinct prototypes (distinct instancing keys) compose
    // independent subtrees, so they can be materialized in parallel. The
    // `Indexer` already takes only `&` references; this needs the cache to build
    // off the `&mut self` path first (compose into per-prototype results, then
    // insert) and the shared `LayerGraph` handed to workers as `&`/`Arc`.
    fn materialize_prototype(&mut self, graph: &LayerGraph, canonical: &Path, prototype: &Path) {
        let mut index = self.cached(canonical).clone();
        let depth = canonical.prim_element_count() as u16;
        index.mark_instance_local_inert(depth, depth);
        // Re-anchor the seeding instance's composed namespace onto the prototype
        // root so the root's own target translation lands in the prototype
        // namespace, not the canonical instance's.
        index.rebase_root(canonical, prototype);

        let (mut context, _) = index.context_for_children(graph, &self.root_parent_context());
        context.instance_depth = None;

        self.cache_index(graph, prototype, index, context, Vec::new(), ExprVarDeps::default());
    }

    /// Returns the synthetic prototype path (`/__Prototype_N`) shared by
    /// `instance`, registering it on first use. `None` when `instance` is not
    /// an instance prim (spec 11.3.3).
    pub(crate) fn prototype_of(&mut self, graph: &LayerGraph, instance: &Path) -> Result<Option<Path>> {
        if !self.is_instance(graph, instance)? {
            return Ok(None);
        }
        Ok(Some(self.register_prototype(graph, instance)?))
    }

    /// The instances sharing the prototype at `prototype` (a `/__Prototype_N`
    /// path), sorted by namespace path. Each is the path whose index composes
    /// that instance, so a nested instance is reported once, as its prim inside
    /// the enclosing prototype. Empty for unknown paths.
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

    /// Returns `true` if `path` is inside a registered prototype's namespace —
    /// the `/__Prototype_N` root itself or any descendant of it (spec 11.3.3).
    ///
    /// Inclusive of the root, as in C++, where `UsdPrim::IsPrototype()` is
    /// defined as `IsInPrototype() && GetPath().IsRootPrimPath()`. It asserts
    /// only namespace membership: a path under a registered root that composes
    /// to no prim still answers `true` here, so a caller reporting prim state
    /// (`Prim::is_in_prototype`) checks existence itself.
    pub(crate) fn is_in_prototype(&self, path: &Path) -> bool {
        self.prototypes.enclosing_root(path).is_some()
    }

    /// Returns the registered `/__Prototype_N` root enclosing `path` (inclusive
    /// of `path` when it is itself a root), or `None` when `path` is outside
    /// every registered prototype namespace (spec 11.3.3). The lookup that
    /// scopes load rules and the population mask onto a prototype's stored,
    /// instance-relative tables.
    pub(crate) fn prototype_root_of(&self, path: &Path) -> Option<Path> {
        // Every registered root is `/__Prototype_N`, so a path the syntactic
        // test rejects can match nothing — and skipping the walk keeps this off
        // the cost of every ordinary query, which reaches it through
        // [`Self::scoped_mask`] and `scoped_load_rules`.
        if is_prototype_namespace(path) {
            self.prototypes.enclosing_root(path)
        } else {
            None
        }
    }

    /// The stage-namespace policy governing `path`, and `path` translated into
    /// its coordinate space.
    ///
    /// Load rules and the population mask are both authored against stage
    /// paths, while a `/__Prototype_N` descendant composes at a synthetic path
    /// no author could have written — so each prototype stores its canonical
    /// instance's table, and a path inside one resolves against that with the
    /// synthetic root replaced by the absolute root. Outside a prototype
    /// namespace `global` and `path` pass through untouched. Nesting needs no
    /// walk: a nested prototype's stored tables were themselves derived from
    /// its enclosing prototype's when it was minted.
    pub(super) fn scoped<'a, T>(
        &'a self,
        path: &'a Path,
        global: &'a T,
        stored: impl FnOnce(&'a Prototype) -> &'a T,
    ) -> (&'a T, Cow<'a, Path>) {
        let Some(root) = self.prototype_root_of(path) else {
            return (global, Cow::Borrowed(path));
        };
        let relative = path
            .replace_prefix(&root, &Path::abs_root())
            .unwrap_or_else(Path::abs_root);
        let prototype = self
            .prototypes
            .get(&root)
            .expect("a registered prototype root has stored tables");
        (stored(prototype), Cow::Owned(relative))
    }

    /// The population mask governing `path`, in `path`'s scope — see
    /// [`Self::scoped`].
    pub(super) fn scoped_mask<'a>(&'a self, path: &'a Path) -> (&'a PopulationMask, Cow<'a, Path>) {
        self.scoped(path, &self.population_mask, |p| &p.relative_mask)
    }

    /// Whether the stage's population exposes `path` (the mask test C++ makes
    /// in `_ComposeChildren`). Prototype content resolves through
    /// [`Self::scoped_mask`], so the question is always asked in the instance
    /// namespace the mask names — where C++ asks it of the prototype's source
    /// prim index path, which is the same place.
    ///
    /// A pure registry read: it composes nothing and takes `&self`, so a caller
    /// already holding the cache can use it.
    pub(crate) fn mask_includes(&self, path: &Path) -> bool {
        let (mask, relative) = self.scoped_mask(path);
        mask.includes(&relative)
    }

    /// The stage's population mask, as opened.
    pub(crate) fn population_mask(&self) -> &PopulationMask {
        &self.population_mask
    }

    /// Filters a composed child-name list to the prims the population mask
    /// exposes (C++ `_ComposeChildren`).
    ///
    /// A `parent` whose whole subtree the mask includes admits every child
    /// without a per-name test — C++'s short-circuit, and the one an
    /// all-inclusive mask takes too, since it holds the absolute root. `parent`
    /// is scoped once, so a prototype's children are tested in the instance
    /// namespace the mask names.
    pub(crate) fn filter_child_names(&self, parent: &Path, children: Vec<Token>) -> Vec<Token> {
        let (mask, relative) = self.scoped_mask(parent);
        if mask.includes_subtree(&relative) {
            return children;
        }
        children
            .into_iter()
            .filter(|name| {
                relative
                    .append_path(name.as_str())
                    .is_ok_and(|child| mask.includes(&child))
            })
            .collect()
    }

    /// Returns `true` if `path` is an instance proxy — a strict descendant of an
    /// instance prim standing in for a prim in that instance's shared prototype
    /// (spec 11.3.3). This holds both in the ordinary instance namespace
    /// (`/A/child`) and inside a prototype namespace under a *nested* instance
    /// (`/__Prototype_N/.../NestedInstance/child`): each has an enclosing
    /// instance. Prototype content not under a nested instance has no enclosing
    /// instance (a prototype root is never one; see [`Self::is_instance`]), so it
    /// is in a prototype, not a proxy.
    ///
    /// A proxy stands in for a real prim in the shared prototype, so a path under
    /// an instance that composes to no prim (e.g. a misspelled child) is not a
    /// proxy — mirroring the existence check on [`Self::is_instance`] /
    /// `Prim::is_valid`.
    pub(crate) fn is_instance_proxy(&mut self, graph: &LayerGraph, path: &Path) -> Result<bool> {
        if path.is_abs_root() || self.is_prototype(path) {
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
        let prototype = self.register_prototype(graph, &instance)?;
        Ok(path.replace_prefix(&instance, &prototype))
    }

    /// Returns the nearest strict ancestor of `path` that resolves as an
    /// instance prim (spec 11.3.3), or `None` when `path` is not inside an
    /// instance.
    //
    // TODO(perf): each [`is_instance`](Self::is_instance) here itself redirects
    // through `effective_path`, which walks back up via this function — so a cold
    // first query on a depth-d path is O(d²) (cheap path/hashmap ops, no extra
    // composition). The `redirected_prims` memo collapses it to O(d) once the
    // ancestors are warm, which a top-down traversal keeps it; a dedicated
    // `is_instance` memo would remove the cold-cache factor entirely.
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

    /// Maps a prim path to the path that actually composes it. An instance proxy
    /// — a strict descendant of an instance prim — is redirected into the shared
    /// prototype's namespace, so identical instances share one composed subtree
    /// (spec 11.3.3). Other paths — the prototype namespace itself, an instance
    /// root, and non-instanced prims — pass through unchanged.
    fn redirect_prim(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Path> {
        match self.redirect_anchor(graph, prim)? {
            Some((origin, target)) => Ok(prim.replace_prefix(&origin, &target).unwrap_or_else(|| prim.clone())),
            None => Ok(prim.clone()),
        }
    }

    /// Returns the `(origin, target)` prefixes that map `prim`'s queried
    /// namespace onto the shared prototype's composition, or `None` when `prim`
    /// composes in place (spec 11.3.3).
    ///
    /// `prim` redirects onto the nearest enclosing instance's prototype, so
    /// identical instances share one composed subtree. This is uniform across
    /// namespaces: an ordinary instance proxy (`/A/tail` → `/__Prototype_N/tail`,
    /// including the canonical instance's own descendants) and a nested instance
    /// proxy *inside* a prototype (`/__Prototype_0/Nested/tail`, where `Nested`
    /// is itself an instance → the nested prototype) both map onto the prototype
    /// they stand in for.
    ///
    /// A prim with no enclosing instance composes in place: an instance *root*
    /// (spec 11.3.3 lets it override property values), the prototype root and its
    /// plain content (a prototype root is never an instance, so never an enclosing
    /// one; see [`Self::is_instance`] — the shared subtree lives there, composed by
    /// deepening the materialized index), and every non-instanced prim.
    pub(super) fn redirect_anchor(&mut self, graph: &LayerGraph, prim: &Path) -> Result<Option<(Path, Path)>> {
        if let Some(instance) = self.enclosing_instance(graph, prim)? {
            let prototype = self.register_prototype(graph, &instance)?;
            return Ok(Some((instance, prototype)));
        }
        Ok(None)
    }

    /// Redirects `path` (prim or property) through [`Self::redirect_prim`],
    /// preserving any property suffix. Applied at every descendant-serving
    /// query entry point so an instance proxy's subtree is served from the
    /// shared prototype rather than recomposed per instance.
    ///
    /// The prim-level redirection is memoized in `redirected_prims` (including
    /// the identity result for a non-redirected prim, the common case), so the
    /// ancestor walk that finds an enclosing instance runs once per prim path
    /// rather than once per query; the memo is cleared whenever the prototype
    /// registry is invalidated.
    pub(super) fn effective_path(&mut self, graph: &LayerGraph, path: &Path) -> Result<Path> {
        let prim = path.prim_path();
        let redirected = if let Some(hit) = self.redirected_prims.get(&prim) {
            hit.clone()
        } else {
            let pending_before = self.pending_loads.len();
            let redirected = self.redirect_prim(graph, &prim)?;
            if !self.provisional(&prim, pending_before) {
                self.redirected_prims.insert(prim.clone(), redirected.clone());
            }
            redirected
        };
        if redirected == prim {
            return Ok(path.clone());
        }
        // Re-anchor any property suffix onto the redirected prim; for a prim
        // path this is the redirected prim itself.
        Ok(path.replace_prefix(&prim, &redirected).unwrap_or(redirected))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(s: &str) -> Path {
        Path::new(s).expect("valid test path")
    }

    /// A key whose identity is a single tagged selection, enough to drive the
    /// registry's dedup without composing a real index.
    fn key(tag: &str) -> InstanceKey {
        InstanceKey {
            arcs: Vec::new(),
            selections: vec![(tag.to_string(), tag.to_string())],
            load_rules: LoadRules::default(),
            mask: PopulationMask::all(),
        }
    }

    /// `remove_affected` drops only the prototypes whose instances or root the
    /// change set touches, leaving the rest mapped, and re-registration mints a
    /// fresh identity for a dropped prototype.
    #[test]
    fn remove_affected_targets_touched() {
        let mut reg = PrototypeRegistry::default();
        // /A and /B share one prototype; /C has its own.
        let (p0, minted0) = reg.register(key("p"), &path("/A"));
        reg.register(key("p"), &path("/B"));
        let (p1, minted1) = reg.register(key("q"), &path("/C"));
        assert!(minted0 && minted1);
        assert_ne!(p0, p1);

        // A change under /C touches only its prototype.
        let dropped = reg.remove_affected(&[path("/C/Child")]);
        assert_eq!(dropped, vec![p1.clone()]);
        assert_eq!(reg.canonical_of(&p0), Some(path("/A")));
        assert!(reg.canonical_of(&p1).is_none());

        // Re-registering /C mints a fresh identity (count stays monotonic).
        let (p1b, minted) = reg.register(key("q"), &path("/C"));
        assert!(minted);
        assert_ne!(p1b, p1);
    }

    /// A nested prototype registers inside its enclosing prototype's namespace,
    /// so a change at the outermost instance drops the whole dependent chain.
    #[test]
    fn remove_affected_cascades() {
        let mut reg = PrototypeRegistry::default();
        let (p0, _) = reg.register(key("outer"), &path("/A"));
        let (p1, _) = reg.register(key("mid"), &path(&format!("{p0}/Inner")));
        let (p2, _) = reg.register(key("inner"), &path(&format!("{p1}/Nested")));

        let dropped = reg.remove_affected(&[path("/A")]);
        for root in [&p0, &p1, &p2] {
            assert!(dropped.contains(root), "{root} must be dropped");
            assert!(reg.canonical_of(root).is_none(), "{root} must be unmapped");
        }
    }

    /// An unrelated change leaves every prototype mapping intact.
    #[test]
    fn remove_affected_keeps_unrelated() {
        let mut reg = PrototypeRegistry::default();
        let (p0, _) = reg.register(key("p"), &path("/A"));
        let (p1, _) = reg.register(key("q"), &path("/C"));

        assert!(reg.remove_affected(&[path("/Extra")]).is_empty());
        assert!(reg.canonical_of(&p0).is_some());
        assert!(reg.canonical_of(&p1).is_some());
    }

    /// A change at an instance's ancestor (or the prototype root itself) is on
    /// the chain, so it invalidates the prototype.
    #[test]
    fn remove_affected_ancestor_and_root() {
        let mut reg = PrototypeRegistry::default();
        let (p0, _) = reg.register(key("p"), &path("/Group/A"));

        // The prototype root itself is on the chain.
        assert_eq!(reg.remove_affected(std::slice::from_ref(&p0)), vec![p0.clone()]);

        // Re-register, then touch an ancestor of the instance.
        let (p0b, _) = reg.register(key("p"), &path("/Group/A"));
        assert_eq!(reg.remove_affected(&[path("/Group")]), vec![p0b]);
    }
}
