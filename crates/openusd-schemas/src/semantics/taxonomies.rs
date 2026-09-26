//! The taxonomies a prim is labelled under, which this family spells as the
//! instance names of an applied schema.

use std::collections::BTreeSet;

use openusd::Result;
use openusd::tf::Token;
use openusd::usd::Prim;

use super::LabelsAPI;

impl LabelsAPI {
    /// The taxonomies `prim` itself carries labels under: the instance name of
    /// every application of this schema on it (C++
    /// `UsdSemanticsLabelsAPI::GetDirectTaxonomies`).
    pub fn direct_taxonomies(prim: &Prim) -> Result<Vec<Token>> {
        Ok(Self::get_all(prim)?.into_iter().map(|labels| labels.name).collect())
    }

    /// Every taxonomy in reach of `prim`: the ones it carries labels under and
    /// the ones its ancestors do, deduplicated and sorted (C++
    /// `UsdSemanticsLabelsAPI::ComputeInheritedTaxonomies`).
    ///
    /// A taxonomy an ancestor is labelled under reaches `prim` because labels
    /// inherit down namespace, so this is the set of taxonomies worth asking
    /// `prim` about — not the labels it answers with, which are each
    /// taxonomy's own.
    pub fn inherited_taxonomies(prim: &Prim) -> Result<Vec<Token>> {
        let stage = prim.stage();
        let mut taxonomies = BTreeSet::new();
        // TODO(rayon): each hop is an independent composed `apiSchemas` query
        // over `&stage`, so every ancestor could resolve at once and merge its
        // names in. Each hop also builds a `LabelsAPI` view per instance only
        // to read the name off it, which an instance-name query on `usd::Prim`
        // would answer without the views.
        for path in prim.path().ancestors_below_root() {
            taxonomies.extend(Self::direct_taxonomies(&stage.prim(path)?)?);
        }
        Ok(taxonomies.into_iter().collect())
    }
}
