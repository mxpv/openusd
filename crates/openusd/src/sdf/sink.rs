//! The generic sink registry shared by every change-sink tier.
//!
//! [`Set`] is the add / remove / iterate machinery behind both the
//! layer-tier [`LayerSink`](super::LayerSink)s and the stage-tier sinks, keyed
//! by an [`Id`] that is tagged with the sink kind so an id minted for one
//! registry cannot remove a sink in another.

use std::fmt;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};

/// A sink's rejection of a staged edit, returned from a sink's pre-commit hook
/// to abort and roll the edit back. Shared across the sink tiers.
#[derive(Debug, thiserror::Error)]
#[error("edit rejected by sink: {0}")]
pub struct Error(pub String);

impl Error {
    /// A rejection carrying a human-readable reason.
    pub fn new(reason: impl Into<String>) -> Self {
        Error(reason.into())
    }
}

/// A process-unique identifier for a sink installed in a [`Set`], returned
/// by [`Set::add`] and passed to [`Set::remove`].
///
/// Tagged by the sink kind `K` (the registry's trait-object type), so a
/// `Id<dyn LayerSink>` and an `Id<dyn StageSink>` are distinct types: an
/// id from one tier cannot be passed to the other's `remove`.
pub struct Id<K: ?Sized> {
    raw: u64,
    _kind: PhantomData<fn() -> K>,
}

impl<K: ?Sized> Id<K> {
    /// A fresh id, unique among the ids minted for kind `K`.
    fn next() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        Id {
            raw: NEXT.fetch_add(1, Ordering::Relaxed),
            _kind: PhantomData,
        }
    }
}

// `PhantomData<fn() -> K>` keeps `Id` `Copy`/`Send`/`Sync` regardless of `K`,
// but the standard derives would add a spurious `K: Trait` bound, so the marker
// traits are implemented by hand.
impl<K: ?Sized> Clone for Id<K> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<K: ?Sized> Copy for Id<K> {}
impl<K: ?Sized> PartialEq for Id<K> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}
impl<K: ?Sized> Eq for Id<K> {}
impl<K: ?Sized> fmt::Debug for Id<K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Id").field(&self.raw).finish()
    }
}

/// An ordered set of installed sinks keyed by an [`Id`] — the add / remove /
/// iterate machinery shared by the layer-tier and stage-tier sink registries.
/// Generic over the (unsized) sink trait object type `T`, so the same logic
/// backs both `Set<dyn LayerSink>` and the stage's sink list.
///
/// Mutation takes `&mut self`; each tier supplies its own interior mutability
/// where it installs sinks through a shared handle (the stage wraps this in a
/// `RefCell`, a layer owns it directly behind `&mut Layer`).
pub struct Set<T: ?Sized> {
    sinks: Vec<(Id<T>, Box<T>)>,
}

impl<T: ?Sized> Default for Set<T> {
    fn default() -> Self {
        Self { sinks: Vec::new() }
    }
}

impl<T: ?Sized> Set<T> {
    /// Install `sink` and return its [`Id`].
    pub fn add(&mut self, sink: Box<T>) -> Id<T> {
        let id = Id::next();
        self.sinks.push((id, sink));
        id
    }

    /// Remove the sink with `id`; a no-op if already gone.
    pub fn remove(&mut self, id: Id<T>) {
        self.sinks.retain(|(sid, _)| *sid != id);
    }

    /// Whether no sink is installed — each tier's no-sink fast path.
    pub fn is_empty(&self) -> bool {
        self.sinks.is_empty()
    }

    /// Iterate the installed sinks in installation order.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.sinks.iter().map(|(_, s)| &**s)
    }
}
