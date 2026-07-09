//! Per-path payload-inclusion policy for runtime `Load`/`Unload` control.
//!
//! [`LoadRules`] decides, for any stage path, whether a payload arc authored
//! there is expanded during composition — independent of whether the arc's
//! target layer happens to be loaded yet (see [`crate::pcp`]'s lazy-loading
//! machinery for that separate question). It is the Rust port of C++
//! `UsdStageLoadRules`. [`IndexCache`] owns the live table directly and
//! queries it in place: unlike C++, where `Usd` and `Pcp` are separate
//! libraries and so need a predicate/callback boundary, this composition
//! engine can just hold the table as a plain field.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::mem;
use std::ops::Bound;

use crate::sdf::Path;

use super::index_cache::IndexCache;
#[cfg(test)]
use super::VariantFallbackMap;

/// A payload-inclusion policy authored at one path (C++
/// `UsdStageLoadRules::Rule`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Rule {
    /// Include this path's payload and, transitively, every descendant
    /// payload.
    All,
    /// Include this path's payload only. A descendant with no rule of its
    /// own is excluded — only a deeper explicit `All`/`Only` entry reopens
    /// it (see [`LoadRules::effective_rule`]'s lookahead step).
    Only,
    /// Exclude this path's payload and everything beneath it.
    None,
}

/// Per-path payload-inclusion table (C++ `UsdStageLoadRules`).
///
/// No entry anywhere means every path resolves to [`Rule::All`] — the
/// load-everything state a stage starts in unless
/// [`InitialLoadSet::LoadNone`](crate::usd::InitialLoadSet) seeds a root
/// [`Rule::None`] instead. Assumes prim-only paths throughout (no property or
/// variant-selection segments); the `usd`-facing boundary normalizes a
/// caller's path before it ever reaches this type.
///
/// Backed by a `BTreeMap`, which derives `Hash`/`Eq` directly — needed since
/// this type becomes part of an instancing key (see `pcp::instancing`).
/// `Path`'s derived `Ord` sorts a prim-only path's descendants contiguously
/// between it and its next sibling (`/` sorts below every valid prim-name
/// character), so `BTreeMap::range` gives correct, cheap prefix-bounded scans
/// for the subtree operations below.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct LoadRules {
    rules: BTreeMap<Path, Rule>,
}

impl LoadRules {
    /// A table with no authored rules, so every path resolves to
    /// [`Rule::All`] (load everything). Named for symmetry with
    /// [`none`](Self::none); equivalent to [`Default::default`].
    pub fn all() -> Self {
        Self::default()
    }

    /// A table with a single root rule excluding every payload.
    pub fn none() -> Self {
        let mut rules = BTreeMap::new();
        rules.insert(Path::abs_root(), Rule::None);
        Self { rules }
    }

    /// `true` if no rules are authored (every path resolves to
    /// [`Rule::All`]).
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// The authored `(path, rule)` pairs, in path order.
    pub fn rules(&self) -> Vec<(Path, Rule)> {
        self.rules.iter().map(|(p, r)| (p.clone(), *r)).collect()
    }

    /// Replaces every authored rule with `rules`.
    pub fn set_rules(&mut self, rules: impl IntoIterator<Item = (Path, Rule)>) {
        self.rules = rules.into_iter().collect();
    }

    /// Sets `path`'s rule directly, replacing any existing entry at exactly
    /// that path without touching its subtree. A no-op when the table
    /// already has exactly `(path, rule)`.
    pub fn add_rule(&mut self, path: Path, rule: Rule) {
        if self.rules.get(&path) == Some(&rule) {
            return;
        }
        self.rules.insert(path, rule);
    }

    /// Includes `path`'s payload and, transitively, every descendant payload
    /// (C++ `UsdLoadWithDescendants`). A no-op when `path` already resolves
    /// to [`Rule::All`] with no existing entries in its own subtree to clear.
    pub fn load_with_descendants(&mut self, path: Path) {
        self.set_subtree_rule(path, Rule::All);
    }

    /// Includes `path`'s payload only, excluding every descendant that has
    /// no rule of its own (C++ `UsdLoadWithoutDescendants`). A no-op when
    /// `path` already resolves to [`Rule::Only`] with no existing entries in
    /// its own subtree to clear.
    pub fn load_without_descendants(&mut self, path: Path) {
        self.set_subtree_rule(path, Rule::Only);
    }

    /// Excludes `path`'s payload and everything beneath it (C++
    /// `UsdStageLoadRules::Unload`). A no-op when `path` already resolves to
    /// [`Rule::None`] with no existing entries in its own subtree to clear.
    pub fn unload(&mut self, path: Path) {
        self.set_subtree_rule(path, Rule::None);
    }

    /// The shared body of [`load_with_descendants`](Self::load_with_descendants)/
    /// [`load_without_descendants`](Self::load_without_descendants)/
    /// [`unload`](Self::unload): skip entirely when `path` already resolves to
    /// `rule` and has no entries in its own subtree to clear, so a redundant
    /// call leaves the table untouched — this is what lets
    /// `IndexCache::set_load_rules` detect a no-op edit for free by diffing
    /// the raw table before and after. Otherwise clears `path`'s subtree
    /// range and inserts one entry; descendant rules are always fully
    /// overwritten, never merged, matching C++.
    fn set_subtree_rule(&mut self, path: Path, rule: Rule) {
        if self.effective_rule(&path) == rule && !self.has_subtree_entries(&path) {
            return;
        }
        self.clear_subtree(&path);
        self.rules.insert(path, rule);
    }

    /// The entries at or under `path`, in path order — the contiguous
    /// `BTreeMap` range every subtree query below shares. Borrows `path`
    /// directly as the range's start bound.
    fn subtree<'a>(&'a self, path: &'a Path) -> impl Iterator<Item = (&'a Path, &'a Rule)> {
        self.rules
            .range((Bound::Included(path), Bound::Unbounded))
            .take_while(move |(p, _)| p.has_prefix(path))
    }

    /// `true` if any entry lies strictly beneath `path`.
    fn has_subtree_entries(&self, path: &Path) -> bool {
        self.subtree(path).any(|(p, _)| p != path)
    }

    /// Removes every entry in `path`'s subtree, including `path` itself.
    fn clear_subtree(&mut self, path: &Path) {
        let doomed: Vec<Path> = self.subtree(path).map(|(p, _)| p.clone()).collect();
        for p in doomed {
            self.rules.remove(&p);
        }
    }

    /// The effective payload-inclusion rule at `path` (C++
    /// `UsdStageLoadRules::GetEffectiveRuleForPath`):
    ///
    /// 1. No ancestor-or-self entry ⇒ [`Rule::All`].
    /// 2. The nearest ancestor-or-self entry is [`Rule::All`] ⇒ [`Rule::All`].
    /// 3. That entry is `path` itself and is [`Rule::Only`] ⇒ [`Rule::Only`].
    /// 4. Otherwise the nearest entry is a strict ancestor with
    ///    [`Rule::Only`]/[`Rule::None`]: `path` is [`Rule::Only`] if a
    ///    descendant of `path` resolves [`Rule::All`]/[`Rule::Only`] before any
    ///    other explicit descendant entry shadows it (`path` is "on the way"
    ///    to a loaded descendant), else [`Rule::None`].
    ///
    /// This is what lets `Load`-ing a deep descendant implicitly reopen every
    /// ancestor between it and the nearest governing rule, even one with its
    /// own explicit `None`.
    pub fn effective_rule(&self, path: &Path) -> Rule {
        let Some((prefix_path, prefix_rule)) = self.nearest_prefix_entry(path) else {
            return Rule::All;
        };
        if prefix_rule == Rule::All {
            return Rule::All;
        }
        if prefix_path == *path && prefix_rule == Rule::Only {
            return Rule::Only;
        }
        if self.has_loaded_descendant(path) {
            Rule::Only
        } else {
            Rule::None
        }
    }

    /// `true` when `path`'s own payload is included —
    /// `effective_rule(path) != Rule::None`.
    pub fn is_loaded(&self, path: &Path) -> bool {
        self.effective_rule(path) != Rule::None
    }

    /// The nearest authored entry that is `path` itself or a strict ancestor
    /// of it — a self entry always outranks an ancestor's — or `None` when no
    /// such entry exists. Walks `path`'s own ancestor chain outward (self
    /// first), doing a point lookup at each step, since only that chain can
    /// ever match.
    fn nearest_prefix_entry(&self, path: &Path) -> Option<(Path, Rule)> {
        path.ancestors().find_map(|p| self.rules.get(&p).map(|&r| (p, r)))
    }

    /// The raw entry authored exactly at `path`, if any — distinct from
    /// [`effective_rule`](Self::effective_rule), which also considers
    /// ancestors and descendants.
    fn own_rule(&self, path: &Path) -> Option<Rule> {
        self.rules.get(path).copied()
    }

    /// `true` if a strict descendant of `path` resolves [`Rule::All`]/
    /// [`Rule::Only`] before any other explicit descendant entry shadows it —
    /// step 4 of [`effective_rule`](Self::effective_rule). Walks `path`'s
    /// descendant entries in path order, skipping past an entry's own
    /// descendants once it has been inspected, so an intervening explicit
    /// rule shadows whatever is beneath it.
    fn has_loaded_descendant(&self, path: &Path) -> bool {
        let descendants: Vec<(&Path, &Rule)> = self.subtree(path).filter(|(p, _)| *p != path).collect();
        let mut i = 0;
        while i < descendants.len() {
            let (cur_path, cur_rule) = descendants[i];
            if matches!(cur_rule, Rule::All | Rule::Only) {
                return true;
            }
            i += 1;
            while i < descendants.len() && descendants[i].0.has_prefix(cur_path) {
                i += 1;
            }
        }
        false
    }

    /// Removes every rule whose removal would not change
    /// [`effective_rule`](Self::effective_rule) at any currently authored
    /// path — including a root [`Rule::All`], which is always redundant (the
    /// implicit default). Processes candidates deepest-first, so a removal
    /// already accounts for whatever a shallower entry's own lookahead
    /// (step 4) sees through it.
    ///
    /// Verifies safety empirically, recomputing every authored path's
    /// effective rule after each tentative removal, because an authored
    /// entry's raw rule can differ from its own effective rule (an authored
    /// [`Rule::None`] shadowing a loaded descendant still resolves to
    /// [`Rule::Only`]), and a removal can change a shallower ancestor's
    /// decision through that same lookahead, not just the removed entry's
    /// own path. Rule tables are small (authored entries, not one per prim),
    /// so this stays cheap.
    // TODO(perf): O(candidates² · effective_rule cost) — every candidate's
    // removal re-verifies the whole `expected` set. Called on every
    // `IndexCache::set_load_rules` and every `make_relative_to` (so once per
    // instance registration); scoping the re-verification to entries near
    // each candidate, rather than the full table, would help if a profile
    // ever shows a stage with many authored rules paying for this.
    pub fn minimize(&mut self) {
        let mut candidates: Vec<Path> = self.rules.keys().cloned().collect();
        candidates.sort_by_key(|p| std::cmp::Reverse(p.prim_element_count()));
        let expected: Vec<(Path, Rule)> = candidates.iter().map(|p| (p.clone(), self.effective_rule(p))).collect();
        for candidate in candidates {
            let rule = self.rules[&candidate];
            self.rules.remove(&candidate);
            let safe = expected.iter().all(|(p, r)| self.effective_rule(p) == *r);
            if !safe {
                self.rules.insert(candidate, rule);
            }
        }
    }

    /// Re-roots this table at `path`: `path`'s own effective rule becomes the
    /// new table's root rule, and every rule authored under `path` is
    /// translated relative to it. Ports C++ `Usd_InstanceKey`'s
    /// `_MakeLoadRulesRelativeTo`, used to fold an instance's load state into
    /// its prototype-sharing key (`pcp::instancing`) so two otherwise-identical
    /// instances with different load rules mint separate prototypes.
    pub(crate) fn make_relative_to(&self, path: &Path) -> LoadRules {
        let mut rules = BTreeMap::new();
        rules.insert(Path::abs_root(), self.effective_rule(path));
        for (p, r) in &self.rules {
            if p == path {
                continue;
            }
            if let Some(relative) = p.replace_prefix(path, &Path::abs_root()) {
                rules.insert(relative, *r);
            }
        }
        let mut result = LoadRules { rules };
        result.minimize();
        result
    }
}

/// Every path whose raw entry differs between `before` and `after` — added,
/// removed, or changed value. The touched set
/// [`IndexCache::set_load_rules`] uses to bound invalidation.
fn diff_entries(before: &LoadRules, after: &LoadRules) -> Vec<Path> {
    let mut touched: Vec<Path> = Vec::new();
    for (p, r) in &before.rules {
        if after.rules.get(p) != Some(r) {
            touched.push(p.clone());
        }
    }
    for (p, r) in &after.rules {
        if before.rules.get(p) != Some(r) {
            touched.push(p.clone());
        }
    }
    touched.sort();
    touched.dedup();
    touched
}

impl IndexCache {
    /// The stage's current load rules.
    pub(crate) fn load_rules(&self) -> &LoadRules {
        &self.load_rules
    }

    /// `true` if `path`'s own payload is included — resolved through
    /// [`scoped_load_rules`](Self::scoped_load_rules), so a path inside a
    /// `/__Prototype_N` namespace is decided against that prototype's stored
    /// relative rules (translated onto the synthetic path), not the global
    /// table, which never carries prototype-rooted entries. Used both by
    /// composition (`IndexCache::build_index`, deciding whether to expand
    /// the site currently being composed) and by external queries
    /// (`Prim::is_loaded`, which may address a prototype's own namespace
    /// directly, e.g. through `Prim::prototype`).
    pub(crate) fn is_loaded(&self, path: &Path) -> bool {
        let (rules, relative) = self.scoped_load_rules(path);
        rules.is_loaded(&relative)
    }

    /// Installs `rules` wholesale, drops exactly the cached indices whose
    /// composition could have changed, and returns those paths — empty when
    /// the edit is a genuine no-op (`rules` resolves identically to the table
    /// it replaced).
    ///
    /// Any entry rooted inside a `/__Prototype_N` namespace is dropped first:
    /// load rules are always authored in real-namespace terms (a prototype's
    /// own relative rules live separately, on its `Prototype` entry — see
    /// [`is_loaded`](Self::is_loaded)), and this is the
    /// single choke point every mutation passes through — `usd::Stage`'s
    /// `load`/`unload`/`load_and_unload` already normalize their target
    /// before reaching here, but a caller-supplied `set_load_rules` table
    /// has no other gate.
    ///
    /// `rules` is minimized before it is stored or compared, so the stored
    /// table is always canonical: a caller-supplied table that is textually
    /// different but semantically identical (e.g. an explicit
    /// `(abs_root, Rule::All)` entry replacing the equivalent empty default)
    /// diffs as no change. This also means [`load_rules`](Self::load_rules)
    /// always reads back a canonical table regardless of how the caller
    /// built its input.
    ///
    /// Diffing the two (now both canonical) tables' raw entries — added,
    /// removed, or changed value — is what makes a redundant edit free:
    /// [`LoadRules`]'s own mutators already skip a no-op edit before it ever
    /// reaches here, so a repeated `load`/`unload` call costs nothing, and
    /// installing a caller-supplied table that resolves identically to the
    /// current one now costs nothing either. For each touched path,
    /// [`drop_index_subtree`](Self::drop_index_subtree) covers every
    /// descendant whose effective rule could change because an entry inside
    /// that subtree moved; walking its strict ancestors while their current
    /// effective rule is not [`Rule::All`] covers every ancestor
    /// [`LoadRules::effective_rule`]'s descendant lookahead could also
    /// affect — an ancestor already at [`Rule::All`] is provably unaffected
    /// by anything below it, since that conclusion never consults
    /// descendants.
    pub(crate) fn set_load_rules(&mut self, mut rules: LoadRules) -> Vec<Path> {
        let real: Vec<(Path, Rule)> = rules
            .rules()
            .into_iter()
            .filter(|(p, _)| !self.is_prototype(p) && !self.is_in_prototype(p))
            .collect();
        rules.set_rules(real);
        rules.minimize();
        let before = mem::replace(&mut self.load_rules, rules);
        let touched = diff_entries(&before, &self.load_rules);
        if touched.is_empty() {
            return Vec::new();
        }
        self.bump_revision();
        let victims = self.load_rule_victims(&touched);
        self.drop_index_victims(&victims);
        victims
    }

    /// The cached indices [`set_load_rules`](Self::set_load_rules) must drop
    /// for a change touching `touched` — see that method's doc for the
    /// downward/upward reasoning.
    fn load_rule_victims(&self, touched: &[Path]) -> Vec<Path> {
        let mut victims: Vec<Path> = Vec::new();
        for p in touched {
            victims.push(p.clone());
            for ancestor in p.strict_ancestors() {
                if ancestor.is_abs_root() {
                    break;
                }
                let rule = self.load_rules.effective_rule(&ancestor);
                if rule == Rule::All {
                    break;
                }
                // A self-authored `Only` is an equally terminal case: step 3
                // of `effective_rule` returns it directly, without ever
                // consulting descendants, exactly like step 1/2's `All`. An
                // `Only` reached instead through a deeper entry's lookahead
                // (step 4/5) is not terminal — it depends on what's below —
                // so this checks the raw entry, not just the resolved rule.
                if rule == Rule::Only && self.load_rules.own_rule(&ancestor) == Some(Rule::Only) {
                    break;
                }
                victims.push(ancestor);
            }
        }
        victims.sort();
        victims.dedup();
        victims
    }

    /// The load rules governing `path`, and `path` translated into their
    /// coordinate space: the global table with `path` unchanged outside any
    /// prototype's namespace, or a prototype's stored relative load rules
    /// with `path` translated relative to the prototype's root when `path`
    /// lies inside one — since a `/__Prototype_N/child` build composes at
    /// that literal synthetic path (see the `pcp::instancing` module doc),
    /// not the real instance path the rule was authored against.
    ///
    /// Borrows `path` outside a prototype's namespace — the common case,
    /// hit once per composed prim.
    pub(super) fn scoped_load_rules<'a>(&'a self, path: &'a Path) -> (&'a LoadRules, Cow<'a, Path>) {
        match self.prototype_root_of(path) {
            Some(root) => {
                let relative = path
                    .replace_prefix(&root, &Path::abs_root())
                    .unwrap_or_else(Path::abs_root);
                let rules = self
                    .relative_load_rules_of(&root)
                    .expect("a registered prototype root has stored relative load rules");
                (rules, Cow::Owned(relative))
            }
            None => (&self.load_rules, Cow::Borrowed(path)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> Path {
        Path::new(s).expect("valid test path")
    }

    #[test]
    fn empty_table_is_all() {
        let rules = LoadRules::all();
        assert_eq!(rules.effective_rule(&p("/A/B")), Rule::All);
        assert!(rules.is_loaded(&p("/A/B")));
    }

    #[test]
    fn none_excludes_everything() {
        let rules = LoadRules::none();
        assert_eq!(rules.effective_rule(&p("/A")), Rule::None);
        assert!(!rules.is_loaded(&p("/A")));
    }

    #[test]
    fn self_only_excludes_plain_descendants() {
        let mut rules = LoadRules::all();
        rules.load_without_descendants(p("/A"));
        assert_eq!(rules.effective_rule(&p("/A")), Rule::Only);
        assert_eq!(
            rules.effective_rule(&p("/A/B")),
            Rule::None,
            "without-descendants excludes a plain descendant with no override of its own"
        );
    }

    #[test]
    fn ancestor_all_cascades() {
        let mut rules = LoadRules::all();
        rules.load_with_descendants(p("/A"));
        assert_eq!(rules.effective_rule(&p("/A/B/C")), Rule::All);
    }

    #[test]
    fn unload_excludes_descendants() {
        let mut rules = LoadRules::all();
        rules.unload(p("/A"));
        assert_eq!(rules.effective_rule(&p("/A/B")), Rule::None);
    }

    #[test]
    fn loaded_descendant_reopens_ancestor() {
        let mut rules = LoadRules::all();
        rules.unload(p("/A"));
        rules.load_with_descendants(p("/A/B"));
        assert_eq!(
            rules.effective_rule(&p("/A")),
            Rule::Only,
            "on the way to a loaded descendant"
        );
        assert_eq!(rules.effective_rule(&p("/A/B")), Rule::All);
        assert_eq!(
            rules.effective_rule(&p("/A/C")),
            Rule::None,
            "an unrelated sibling stays excluded"
        );
    }

    #[test]
    fn explicit_entry_shadows_deeper_one() {
        // /A/B/C is All, but /A/B's own explicit None entry shadows it from
        // /A's lookahead scan (which stops at the first entry it finds,
        // /A/B, without looking past it) -- /A stays fully excluded even
        // though a loaded prim exists two levels down. /A/B's own query
        // still resolves via its own (unshadowed) lookahead to C.
        let mut rules = LoadRules::all();
        rules.add_rule(p("/A"), Rule::None);
        rules.add_rule(p("/A/B"), Rule::None);
        rules.add_rule(p("/A/B/C"), Rule::All);
        assert_eq!(rules.effective_rule(&p("/A")), Rule::None);
        assert_eq!(rules.effective_rule(&p("/A/B")), Rule::Only);
        assert_eq!(rules.effective_rule(&p("/A/B/C")), Rule::All);
    }

    #[test]
    fn add_rule_overrides_ancestor_either_direction() {
        let mut rules = LoadRules::all();
        rules.load_with_descendants(p("/World"));
        rules.add_rule(p("/World/Heavy"), Rule::Only);
        assert_eq!(
            rules.effective_rule(&p("/World/Light")),
            Rule::All,
            "unaffected sibling inherits All"
        );
        assert_eq!(
            rules.effective_rule(&p("/World/Heavy")),
            Rule::Only,
            "explicit override wins over All"
        );
        assert_eq!(
            rules.effective_rule(&p("/World/Heavy/Child")),
            Rule::None,
            "Heavy's own Only excludes its plain descendants, regardless of World's All"
        );
    }

    #[test]
    fn load_with_descendants_noop_on_default() {
        let mut rules = LoadRules::all();
        rules.load_with_descendants(p("/A"));
        assert!(
            rules.is_empty(),
            "already All by default, nothing authored beneath -- no entry needed"
        );
    }

    #[test]
    fn unload_noop_when_already_excluded() {
        let mut rules = LoadRules::none();
        let before = rules.clone();
        rules.unload(p("/A"));
        assert_eq!(rules, before, "the whole stage is already excluded");
    }

    #[test]
    fn load_with_descendants_clears_conflicting_subtree() {
        let mut rules = LoadRules::all();
        rules.unload(p("/A/B"));
        rules.load_with_descendants(p("/A"));
        assert_eq!(
            rules.rules(),
            vec![(p("/A"), Rule::All)],
            "the nested override is cleared, not merged"
        );
    }

    #[test]
    fn minimize_drops_redundant_root() {
        let mut rules = LoadRules::all();
        rules.add_rule(p("/"), Rule::All);
        rules.minimize();
        assert!(rules.is_empty());
    }

    #[test]
    fn minimize_drops_redundant_nested() {
        let mut rules = LoadRules::all();
        rules.add_rule(p("/A"), Rule::None);
        rules.add_rule(p("/A/B"), Rule::None);
        rules.minimize();
        assert_eq!(
            rules.rules(),
            vec![(p("/A"), Rule::None)],
            "the nested duplicate is dropped"
        );
    }

    /// A naive "drop an entry if it textually matches its nearest kept
    /// ancestor's rule" reduction is unsound here: `/A/B`'s own `None` looks
    /// redundant against `/A`'s `None`, but removing it would expose
    /// `/A/B/C`'s `All` to `/A`'s own lookahead, changing
    /// `effective_rule(/A)` from `None` to `Only`. `minimize` must keep every
    /// entry whose removal would change any authored path's effective rule.
    #[test]
    fn minimize_keeps_shadowing_entries() {
        let mut rules = LoadRules::all();
        rules.add_rule(p("/A"), Rule::None);
        rules.add_rule(p("/A/B"), Rule::None);
        rules.add_rule(p("/A/B/C"), Rule::All);
        let before = rules.clone();
        rules.minimize();
        for path in [p("/A"), p("/A/B"), p("/A/B/C"), p("/A/B/D")] {
            assert_eq!(
                rules.effective_rule(&path),
                before.effective_rule(&path),
                "minimize must not change the effective rule at {path}"
            );
        }
    }

    #[test]
    fn make_relative_to_preserves_effective_rules() {
        let mut rules = LoadRules::all();
        rules.unload(p("/World"));
        rules.load_with_descendants(p("/World/Inst/Heavy"));
        let relative = rules.make_relative_to(&p("/World/Inst"));
        assert_eq!(
            relative.effective_rule(&p("/")),
            Rule::Only,
            "the instance root is on the way to Heavy"
        );
        assert_eq!(relative.effective_rule(&p("/Heavy")), Rule::All);
        assert_eq!(relative.effective_rule(&p("/Sibling")), Rule::None);
    }

    #[test]
    fn set_load_rules_reports_bounded_victims() {
        let mut cache = IndexCache::new(VariantFallbackMap::new(), LoadRules::all(), Vec::new());
        let mut rules = cache.load_rules().clone();
        rules.unload(p("/A"));
        assert_eq!(cache.set_load_rules(rules), vec![p("/A")]);
    }

    #[test]
    fn set_load_rules_noop_reports_nothing() {
        let mut cache = IndexCache::new(VariantFallbackMap::new(), LoadRules::all(), Vec::new());
        let rules = cache.load_rules().clone();
        assert!(cache.set_load_rules(rules).is_empty());
    }

    /// A caller-supplied table that is textually different but semantically
    /// identical to the current one -- an explicit `(abs_root, Rule::All)`
    /// entry standing in for the equivalent empty default -- must not read as
    /// a change: `set_load_rules` minimizes the incoming table before
    /// diffing, so this reports no victims.
    #[test]
    fn set_load_rules_noop_on_equivalent_table() {
        let mut cache = IndexCache::new(VariantFallbackMap::new(), LoadRules::all(), Vec::new());
        let mut explicit_all = LoadRules::all();
        explicit_all.add_rule(p("/"), Rule::All);
        assert!(cache.set_load_rules(explicit_all).is_empty());
        assert!(cache.load_rules().is_empty(), "the stored table stays canonical");
    }

    #[test]
    fn set_load_rules_stops_ancestor_walk_at_all() {
        let mut cache = IndexCache::new(VariantFallbackMap::new(), LoadRules::all(), Vec::new());
        let mut rules = cache.load_rules().clone();
        rules.load_with_descendants(p("/World"));
        cache.set_load_rules(rules.clone());
        rules.unload(p("/World/Deep/Nested"));
        let victims = cache.set_load_rules(rules);
        assert_eq!(
            victims,
            vec![p("/World/Deep/Nested")],
            "an ancestor already at All is unaffected by a change below it"
        );
    }

    /// A self-authored `Only` ancestor (reached via `effective_rule`'s step 3,
    /// which never consults descendants) is just as invariant to a change
    /// below it as an `All` ancestor is, so the walk must stop there too: it
    /// must not appear as a victim (or, via `invalidate_prototypes`, evict
    /// an unrelated prototype sharing its subtree) for an edit elsewhere.
    #[test]
    fn set_load_rules_stops_ancestor_walk_at_self_only() {
        let mut cache = IndexCache::new(VariantFallbackMap::new(), LoadRules::all(), Vec::new());
        let mut rules = cache.load_rules().clone();
        rules.load_without_descendants(p("/World"));
        cache.set_load_rules(rules.clone());
        rules.load_with_descendants(p("/World/A/Deep"));
        let victims = cache.set_load_rules(rules);
        assert_eq!(
            victims,
            vec![p("/World/A"), p("/World/A/Deep")],
            "/World's own self-authored Only is unaffected by a change under an unrelated child"
        );
    }
}
