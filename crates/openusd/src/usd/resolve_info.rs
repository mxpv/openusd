//! Where value resolution found an attribute's answer (C++ `UsdResolveInfo`).

use crate::pcp;
use crate::usd::SpecSite;

/// The kind of source an attribute's resolved value came from (C++
/// `UsdResolveInfoSource`).
///
/// These are the sources this crate resolves from. Upstream additionally has a
/// spline source, which arrives with spline support.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ResolveInfoSource {
    /// No value at all.
    #[default]
    None,
    /// The attribute's schema supplied a fallback.
    Fallback,
    /// An authored `default` opinion.
    Default,
    /// An authored `timeSamples` opinion.
    TimeSamples,
    /// A value-clip set that owns the attribute.
    ValueClips,
}

/// Where value resolution found an attribute's answer — the resolved *location*
/// of its value rather than the value itself (C++ `UsdResolveInfo`).
///
/// Obtained from [`Attribute::resolve_info`](super::Attribute::resolve_info) and
/// [`resolve_info_at`](super::Attribute::resolve_info_at). Meant for debugging
/// and introspection: a value read should go through
/// [`Attribute::get`](super::Attribute::get), which is what actually applies the
/// schema fallback and asset resolution this only describes.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct ResolveInfo {
    pub(super) source: ResolveInfoSource,
    pub(super) node: Option<pcp::ResolveNode>,
    pub(super) spec: Option<SpecSite>,
    pub(super) weaker: Vec<ResolveInfo>,
    /// Whether the value composes over a source that varies with time, where
    /// the chain does not say so itself — what a query that named no time
    /// learns by reading past a composing source.
    pub(super) composes_over_varying: bool,
    pub(super) value_is_blocked: bool,
    /// Whether any layer authored a value opinion, including one that withholds
    /// a value. Wider than both `source` and `value_is_blocked`: a blocked
    /// `timeSamples` field is an authored opinion that neither records, and so
    /// is a `timeSamples` opinion a default-time query resolved past.
    pub(super) has_authored_opinion: bool,
}

impl ResolveInfo {
    /// The kind of source that answered.
    pub fn source(&self) -> ResolveInfoSource {
        self.source
    }

    /// The composition node that supplied the opinion, or `None` when the answer
    /// came from a schema fallback or from nothing at all.
    ///
    /// This is an owned record rather than a live handle: a `ResolveInfo`
    /// outlives the composition index it was resolved from, and that index's
    /// node handles are reused after a recompose.
    ///
    /// For a [`ValueClips`](ResolveInfoSource::ValueClips) source this is the
    /// node that introduced the winning clip set, which is where value
    /// resolution consulted it.
    pub fn node(&self) -> Option<&pcp::ResolveNode> {
        self.node.as_ref()
    }

    /// The spec a property stack lists for the source that answered, or `None`
    /// where nothing authored one — a schema fallback, no source at all, or a
    /// value clip reached without a time, which selects none.
    ///
    /// The layer, the path inside it, and the cumulative offset that reaches
    /// it (C++ splits these across `GetLayer`, `GetPrimPathInLayerStack` and
    /// `GetLayerToStageOffset`).
    ///
    /// For the source that answered, this is the site
    /// [`Attribute::property_stack`](super::Attribute::property_stack) lists
    /// for it. A link in [`weaker_sources`](Self::weaker_sources) names the
    /// spec its own source answered from, which the stack can leave out: the
    /// stack admits a spec only where its kind agrees with the property's, and
    /// value resolution asks no such question of an opinion it composes.
    ///
    /// For a value clip the site is the layer the stack names at that time,
    /// which is not always the layer the value was read from: a gap filled
    /// under `interpolateMissingClipValues` names the manifest while the
    /// samples came from the clips around it.
    pub fn spec_site(&self) -> Option<&SpecSite> {
        self.spec.as_ref()
    }

    /// The weaker sources that composed into the resolved value, strongest
    /// first (C++ walks the same chain through `GetNextWeakerInfo`).
    ///
    /// Empty unless the value composes across sources rather than being won
    /// outright: a path expression whose `%_` draws on weaker opinions, or a
    /// dictionary merged over weaker dictionaries. A dense value answers alone.
    ///
    /// A link can come from any tier the walk reaches — a weaker layer's
    /// `default` or `timeSamples`, a value clip — and the last can be the
    /// schema fallback, where the authored sources ran out before the
    /// composition closed. Each names the node and spec it answered from, as
    /// [`source`](Self::source) does, except the fallback, which was authored
    /// in no layer and names neither. None chains further: the whole chain is
    /// here.
    ///
    /// A proximal [`resolve_info`](super::Attribute::resolve_info) reports
    /// none: it answers which source would answer, not what went into a value.
    pub fn weaker_sources(&self) -> &[ResolveInfo] {
        &self.weaker
    }

    /// Whether an opinion blocked the value
    /// ([`Attribute::block`](super::Attribute::block)).
    ///
    /// A blocked attribute still reads back its schema fallback (spec §12.3.6),
    /// so this reports the block that `source` alone cannot.
    pub fn value_is_blocked(&self) -> bool {
        self.value_is_blocked
    }

    /// Whether a layer authored a value that survives composition.
    ///
    /// A block is *not* an authored value; use
    /// [`has_authored_value_opinion`](Self::has_authored_value_opinion) to count
    /// one.
    pub fn has_authored_value(&self) -> bool {
        matches!(
            self.source,
            ResolveInfoSource::Default | ResolveInfoSource::TimeSamples | ResolveInfoSource::ValueClips
        )
    }

    /// Whether a layer authored any value opinion at all, *including* one that
    /// withholds a value — a blocked `default`, or a blocked `timeSamples`
    /// field — and one the query resolved past.
    pub fn has_authored_value_opinion(&self) -> bool {
        self.has_authored_opinion
    }

    /// Whether the source that answered can vary over time.
    ///
    /// Deliberately more conservative than
    /// [`Attribute::value_might_be_time_varying`](super::Attribute::value_might_be_time_varying),
    /// which has the attribute's own sample count to consult: a `timeSamples`
    /// source reports `true` even holding a single sample.
    ///
    /// A `default` source reports `true` where a source it composed over can
    /// vary: the value is only as constant as everything that went into it, so
    /// this walks the whole chain (C++ recurses through `GetNextWeakerInfo`).
    ///
    /// A proximal [`resolve_info`](super::Attribute::resolve_info) builds no
    /// chain to walk, and still answers: the walk reads past a composing
    /// source to learn whether one it draws on varies, which is the question
    /// this asks (C++ keeps the same answer in
    /// `_defaultCanComposeOverWeakerTimeVaryingSources`).
    pub fn value_source_might_be_time_varying(&self) -> bool {
        let varies = |info: &ResolveInfo| {
            matches!(
                info.source,
                ResolveInfoSource::TimeSamples | ResolveInfoSource::ValueClips
            )
        };
        self.composes_over_varying || varies(self) || self.weaker.iter().any(varies)
    }
}
