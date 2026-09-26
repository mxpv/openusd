//! Reading labels under one taxonomy across a stage's namespace.

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::ops::RangeInclusive;

use openusd::Result;
use openusd::sdf;
use openusd::tf;
use openusd::usd::{Prim, TimeCode};

use super::LabelsAPI;
use crate::SchemaError;

/// The labels prims carry under one taxonomy at one time
/// (C++ `UsdSemanticsLabelsQuery`).
///
/// What a prim is labelled is what it carries itself together with what its
/// ancestors carry, since labels inherit down namespace: a prim under a
/// labelled ancestor answers with that label whether or not [`LabelsAPI`] is
/// applied to it.
///
/// Each prim is read once and remembered, so a subtree costs one read per prim.
/// Nothing invalidates what is remembered: discard the query when the stage
/// changes. Every prim asked about has to come from the one stage, since a prim
/// is remembered by its path alone.
#[derive(Debug)]
pub struct LabelsQuery {
    taxonomy: tf::Token,
    time: QueryTime,
    /// What each prim asked about carries, or `None` for a prim the schema is
    /// not applied to, so that asking again about either answers from here.
    labels: RefCell<HashMap<sdf::Path, Option<BTreeSet<tf::Token>>>>,
}

/// The time a [`LabelsQuery`] reads labels at.
#[derive(Debug, Clone, PartialEq)]
pub enum QueryTime {
    /// One time code, or the default value where `None`.
    At(Option<TimeCode>),
    /// Every time sample in a closed interval, together with the value held at
    /// its start.
    Over(RangeInclusive<f64>),
}

impl LabelsQuery {
    /// A query for `taxonomy` at one time code, or at the default value where
    /// `time` is `None`.
    pub fn at(taxonomy: impl Into<tf::Token>, time: impl Into<Option<TimeCode>>) -> Result<Self, SchemaError> {
        LabelsQuery::new(taxonomy.into(), QueryTime::At(time.into()))
    }

    /// A query for `taxonomy` over a closed interval, answering with every
    /// label carried at any time sample in it.
    ///
    /// The interval's start is read as well, so a value held there from an
    /// earlier sample counts as much as the samples inside it.
    ///
    /// A start of negative infinity reaches the earliest sample authored. C++
    /// reaches it for positive infinity too, since `GfInterval::IsMinFinite`
    /// rejects both, where a start above every sample holds the last one here.
    pub fn over(taxonomy: impl Into<tf::Token>, interval: RangeInclusive<f64>) -> Result<Self, SchemaError> {
        if interval.is_empty() {
            return Err(SchemaError::EmptyInterval);
        }
        LabelsQuery::new(taxonomy.into(), QueryTime::Over(interval))
    }

    /// The taxonomy this query reads labels under.
    pub fn taxonomy(&self) -> &tf::Token {
        &self.taxonomy
    }

    /// The time this query reads labels at.
    pub fn time(&self) -> &QueryTime {
        &self.time
    }

    /// The labels authored on `prim` itself under this taxonomy, sorted and
    /// deduplicated (C++ `ComputeUniqueDirectLabels`).
    ///
    /// Empty where the schema is not applied to `prim` under this taxonomy,
    /// which is what gives a label authored there its meaning.
    pub fn direct_labels(&self, prim: &Prim) -> Result<Vec<tf::Token>> {
        self.populate(prim)?;
        let cached = self.labels.borrow();
        Ok(cached
            .get(prim.path())
            .and_then(Option::as_ref)
            .into_iter()
            .flatten()
            .cloned()
            .collect())
    }

    /// Every label in reach of `prim`: the ones it carries and the ones its
    /// ancestors carry, sorted and deduplicated (C++
    /// `ComputeUniqueInheritedLabels`).
    pub fn inherited_labels(&self, prim: &Prim) -> Result<Vec<tf::Token>> {
        let mut unique = BTreeSet::new();
        self.visit_inherited(prim, |labels| unique.extend(labels.iter().cloned()))?;
        Ok(unique.into_iter().collect())
    }

    /// Whether `prim` itself is labelled `label` under this taxonomy
    /// (C++ `HasDirectLabel`).
    pub fn has_direct_label(&self, prim: &Prim, label: &tf::Token) -> Result<bool> {
        self.populate(prim)?;
        let cached = self.labels.borrow();
        Ok(cached
            .get(prim.path())
            .and_then(Option::as_ref)
            .is_some_and(|labels| labels.contains(label)))
    }

    /// Whether `prim` or any ancestor is labelled `label` under this taxonomy
    /// (C++ `HasInheritedLabel`).
    pub fn has_inherited_label(&self, prim: &Prim, label: &tf::Token) -> Result<bool> {
        let mut found = false;
        self.visit_inherited(prim, |labels| found |= labels.contains(label))?;
        Ok(found)
    }

    /// A query for `taxonomy`, which has to name something for an application
    /// of the schema to be found under it.
    fn new(taxonomy: tf::Token, time: QueryTime) -> Result<Self, SchemaError> {
        if taxonomy.is_empty() {
            return Err(SchemaError::EmptyTaxonomy);
        }
        Ok(LabelsQuery {
            taxonomy,
            time,
            labels: RefCell::default(),
        })
    }

    /// Reads `prim` and each of its ancestors, handing what each carries to
    /// `visit`.
    ///
    /// Every ancestor is read, so every answer below `prim` is in hand
    /// afterwards.
    ///
    /// TODO(rayon): each hop is an independent schema lookup and value read
    /// over `&stage`, so the ancestors could resolve at once — which needs the
    /// remembered labels behind a map several hops can write to.
    fn visit_inherited(&self, prim: &Prim, mut visit: impl FnMut(&BTreeSet<tf::Token>)) -> Result<()> {
        let stage = prim.stage();
        for path in prim.path().ancestors_below_root() {
            let ancestor = stage.prim(path)?;
            self.populate(&ancestor)?;
            if let Some(labels) = self.labels.borrow().get(ancestor.path()).and_then(Option::as_ref) {
                visit(labels);
            }
        }
        Ok(())
    }

    /// Reads and remembers what `prim` carries, a prim the schema is not
    /// applied to included.
    fn populate(&self, prim: &Prim) -> Result<()> {
        if self.labels.borrow().contains_key(prim.path()) {
            return Ok(());
        }
        let labels = match LabelsAPI::get_instance(prim, &self.taxonomy)? {
            Some(view) => Some(self.read(&view)?),
            None => None,
        };
        self.labels.borrow_mut().insert(prim.path().clone(), labels);
        Ok(())
    }

    /// The labels `view` holds at this query's time.
    fn read(&self, view: &LabelsAPI) -> Result<BTreeSet<tf::Token>> {
        let labels = view.labels_attr();
        match &self.time {
            QueryTime::At(time) => Ok(labels
                .get_at::<Vec<tf::Token>>(*time)?
                .unwrap_or_default()
                .into_iter()
                .collect()),
            QueryTime::Over(interval) => {
                // TODO: which times carry the values in effect across an
                // interval is a value-resolution concept `usd::Attribute`
                // should answer beside `time_samples_in_interval`, along with
                // the trailing bracketing sample that an interpolating value
                // type needs and a held one does not.
                let mut times = labels.time_samples_in_interval(interval.clone())?;

                // A value is held from the sample before it, so the interval's
                // start carries one as much as the samples inside it do. A
                // start below every sample reaches the earliest one authored,
                // and an attribute with no samples at all answers there with
                // its default or its schema fallback.
                let start = match interval.start() == &f64::NEG_INFINITY {
                    true => TimeCode::EARLIEST.value(),
                    false => *interval.start(),
                };
                if times.first() != Some(&start) {
                    times.push(start);
                }

                // One value source, resolved once for the whole sweep.
                let query = labels.query();
                let mut unique = BTreeSet::new();
                for time in times {
                    unique.extend(query.get_at::<Vec<tf::Token>>(TimeCode::new(time))?.unwrap_or_default());
                }
                Ok(unique)
            }
        }
    }
}
