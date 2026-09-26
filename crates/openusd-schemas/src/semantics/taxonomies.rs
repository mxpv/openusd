//! The taxonomies a prim is labelled under, which this family spells as the
//! instance names of an applied schema.

use std::collections::BTreeSet;

use openusd::Result;
use openusd::tf;
use openusd::usd::Prim;

use super::{LabelsAPI, tokens};

impl LabelsAPI {
    /// The taxonomies `prim` itself carries labels under: the instance name of
    /// every application of this schema on it (C++
    /// `UsdSemanticsLabelsAPI::GetDirectTaxonomies`).
    pub fn direct_taxonomies(prim: &Prim) -> Result<Vec<tf::Token>> {
        prim.api_schema_instance_names(tokens::SEMANTICS_LABELS_API)
    }

    /// Every taxonomy in reach of `prim`: the ones it carries labels under and
    /// the ones its ancestors do, deduplicated and sorted (C++
    /// `UsdSemanticsLabelsAPI::ComputeInheritedTaxonomies`).
    ///
    /// A taxonomy an ancestor is labelled under reaches `prim` because labels
    /// inherit down namespace, so this is the set of taxonomies worth asking
    /// `prim` about — not the labels it answers with, which are each
    /// taxonomy's own.
    pub fn inherited_taxonomies(prim: &Prim) -> Result<Vec<tf::Token>> {
        let stage = prim.stage();
        let mut taxonomies: BTreeSet<tf::Token> = Self::direct_taxonomies(prim)?.into_iter().collect();
        // TODO(rayon): each hop is an independent composed `apiSchemas` query
        // over `&stage`, so every ancestor could resolve at once and merge its
        // names in.
        for path in prim.path().strict_ancestors_below_root() {
            taxonomies.extend(Self::direct_taxonomies(&stage.prim(path)?)?);
        }
        Ok(taxonomies.into_iter().collect())
    }
}
