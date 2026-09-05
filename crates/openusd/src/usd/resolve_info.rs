//! Where value resolution found an attribute's answer (C++ `UsdResolveInfo`).

use crate::pcp;

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
    /// A `default` source reports `false`. That holds because a `default` here
    /// never composes over a weaker time-varying source; were cross-source
    /// composition added, this would have to recurse through the weaker sources
    /// the way C++ does.
    pub fn value_source_might_be_time_varying(&self) -> bool {
        matches!(
            self.source,
            ResolveInfoSource::TimeSamples | ResolveInfoSource::ValueClips
        )
    }
}
