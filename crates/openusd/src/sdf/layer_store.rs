//! The layers a [`LayerRegistry`](super::LayerRegistry) holds, and the
//! [`LayerHandle`]s that share them (C++ `Sdf_LayerRegistry` and
//! `SdfLayerRefPtr`).
//!
//! A [`LayerStore`] is an arena of layers behind one `RefCell`, indexed by
//! identifier and by real path. Each layer sits in a slot named by a
//! [`SlotKey`]: its index and the epoch it was filled in. A handle keeps its
//! slot alive. Once the last handle to a slot drops, the slot is freed at the
//! next [`sweep`](LayerStore::sweep) and its epoch moves on. A key kept from
//! before never names the layer the slot holds next.
//!
//! Each slot holds its layer behind an `Rc`, which a [`LayerGuard`] shares to
//! lend that one layer without holding the arena borrowed.

use std::cell::{BorrowMutError, Cell, Ref, RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr;
use std::rc::{Rc, Weak};
use std::slice;
use std::thread;

use crate::ar;

use super::commit::{Committed, Dispatch, Subscriber, TxnContext};
use super::layer::{Due, Reload};
use super::{
    AuthoringError, DataError, EditError, ExportError, Layer, LayerEdit, LayerRegistry, LayerSink, LayerSinkId,
    Listing, PackageFiles, ReadListing, TargetLayer, dry_run_layers, edit_layers, held_packages, sink,
};

/// A failure to read, edit or add a layer of a
/// [`LayerRegistry`](super::LayerRegistry).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LayerError {
    /// The layer or its registry was in use, so nothing was read or staged:
    /// the access was made from inside an edit or a save on the registry (a
    /// file format or resolver a save runs), a change (an edit, a save, a
    /// sink, a layer added) was asked for from a resolver or file format a
    /// reload runs or a resolver a stage calls as it reads the registry's
    /// layers, or a [`LayerGuard`] or live query holds the layer it would
    /// change.
    #[error("the layer or its registry is in use by a borrow or an edit")]
    Busy,

    /// A layer with this identifier is already open in the registry, which
    /// holds one layer per identifier.
    #[error("a layer with identifier {identifier} is already open in this registry")]
    Duplicate {
        /// The identifier both layers carry.
        identifier: String,
    },

    /// One edit named the same layer twice.
    #[error("layer {identifier} is named twice in one edit")]
    Repeated {
        /// The layer's identifier.
        identifier: String,
    },

    /// One edit named a layer another registry holds.
    #[error("layer {identifier} belongs to another registry")]
    Foreign {
        /// The layer's identifier.
        identifier: String,
    },

    /// A reload found the layer's asset at another location than it was read
    /// from, which the layer cannot move to.
    #[error("layer {identifier} now resolves to {resolved}, and a reload cannot move it")]
    Moved {
        /// The layer's identifier.
        identifier: String,
        /// Where the identifier resolves now.
        resolved: String,
    },

    /// The edit itself failed; nothing was committed.
    #[error(transparent)]
    Edit(#[from] EditError),

    /// A field a query read could not be decoded.
    #[error(transparent)]
    Data(#[from] DataError),

    /// Writing the layer out through its handle failed: a
    /// [`save`](LayerHandle::save), an [`export`](LayerHandle::export) or an
    /// [`export_to_string`](LayerHandle::export_to_string).
    #[error(transparent)]
    Export(#[from] ExportError),
}

/// A layer a [`LayerRegistry`](super::LayerRegistry) declined to hold, handed
/// back with the reason so nothing it holds is lost.
#[derive(Debug, thiserror::Error)]
#[error("cannot hold layer {}", layer.identifier())]
pub struct AdoptError {
    /// Why the registry declined it.
    #[source]
    pub error: LayerError,
    /// The layer, as it was given.
    pub layer: Box<Layer>,
}

/// The reason a layer was declined, without the layer.
impl From<AdoptError> for LayerError {
    fn from(error: AdoptError) -> Self {
        error.error
    }
}

/// A sink's veto fails the edit, as it does a [`Layer::edit`].
impl From<sink::Error> for LayerError {
    fn from(error: sink::Error) -> Self {
        Self::Edit(error.into())
    }
}

/// An authoring failure fails the edit, as it does a [`Layer::edit`].
impl From<AuthoringError> for LayerError {
    fn from(error: AuthoringError) -> Self {
        Self::Edit(error.into())
    }
}

/// The layers a registry holds and the bookkeeping their handles share.
#[derive(Default)]
pub(crate) struct LayerStore {
    /// The slots, borrowed whole by every edit and every
    /// [`StoreRead`], and briefly to add, find or lend a layer.
    slots: RefCell<Slots>,
    /// Slots whose last handle has dropped, waiting for a
    /// [`sweep`](Self::sweep) to free them. Pushed by a handle's drop, which
    /// never borrows [`slots`](Self::slots).
    dead: RefCell<Vec<SlotKey>>,
    /// Subscriptions that ended while [`slots`](Self::slots) was borrowed,
    /// applied by the next mutable borrow.
    unsubscribed: RefCell<Vec<(SlotKey, sink::Id<dyn Subscriber>)>>,
    /// The `after_commit` notifications of the registry's edits, in commit
    /// order.
    dispatch: Dispatch,
    /// How many [`SweepHold`]s are live. While any is, a sweep frees
    /// nothing.
    holds: Cell<usize>,
}

/// The slot arena and its indexes.
#[derive(Default)]
struct Slots {
    /// Every slot ever filled, live or free.
    slots: Vec<Slot>,
    /// Indexes of free slots, reused before the arena grows.
    free: Vec<u32>,
    /// Live slots by layer identifier.
    by_identifier: HashMap<String, u32>,
    /// Live slots by the real path of a layer read from an asset.
    by_real_path: HashMap<String, u32>,
    /// What each package a live layer was read from holds, by package path,
    /// a nested package by its own packaged path. A package is held while
    /// any live layer lies in it.
    packages: HashMap<String, HeldPackage>,
}

/// A package's listing and the slots of the layers that hold it.
pub(crate) struct HeldPackage {
    /// What the package holds, `None` while no listing of it has succeeded.
    files: Option<Rc<PackageFiles>>,
    /// The filled slots whose layers hold the package, live or awaiting a
    /// sweep.
    layers: Vec<u32>,
}

/// The packages a layer holds, each with its listing where one was read
/// ([`held_packages`]).
pub(crate) type PackageListings = Vec<(String, Option<Rc<PackageFiles>>)>;

/// One arena slot: the epoch it is in, and its layer while it is filled.
#[derive(Default)]
struct Slot {
    /// Advanced each time the slot is freed.
    epoch: u32,
    /// The layer and what the store keeps beside it, while the slot is filled.
    entry: Option<Entry>,
}

/// A filled slot's layer and what the store keeps beside it.
///
/// The layer sits behind an `Rc` whose strong count is its borrow flag: each
/// [`LayerGuard`] and each running live query holds a clone, and an edit takes
/// the layer through [`Rc::get_mut`], which fails while either lives. Three
/// rules keep that sound:
///
/// - the `Rc` is set when the slot fills and taken when it frees, never
///   replaced;
/// - the layer's content changes only through `Rc::get_mut`: a guard never
///   sees it change;
/// - no `Weak<Layer>` exists: `Rc::get_mut` fails only while a guard lives
///   or a live query runs, each of which holds a clone.
struct Entry {
    /// The layer, shared with each live [`LayerGuard`] and each running live
    /// query, and changed only through `Rc::get_mut`.
    layer: Rc<Layer>,
    /// The crate-internal observers subscribed to the layer, prepared ahead of
    /// each commit and committed with it (see [`edit_layers`]). Kept beside
    /// the layer so a subscription comes and goes while the layer is
    /// borrowed.
    subscribers: sink::Set<dyn Subscriber>,
    /// The token every handle to the layer shares.
    token: Weak<SlotToken>,
    /// The packages the layer holds ([`held_packages`]).
    packages: Vec<String>,
}

/// Names one filling of one arena slot: a key from before the slot was freed
/// never matches what the slot holds next.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct SlotKey {
    /// The slot's position in the arena.
    index: u32,
    /// The epoch the slot was in when filled.
    epoch: u32,
}

/// The token every handle to one slot shares: the slot lives while it does.
struct SlotToken {
    /// The slot it keeps alive.
    key: SlotKey,
    /// The layer's identifier, which never changes while the layer is held.
    identifier: String,
    /// The location anchoring the layer's relative asset paths, which is
    /// fixed with its identifier (see [`Layer::anchor_location`]).
    anchor: Option<ar::ResolvedPath>,
    /// The store, told of the token's end so a sweep can free the slot.
    store: Weak<LayerStore>,
}

impl Drop for SlotToken {
    fn drop(&mut self) {
        if let Some(store) = self.store.upgrade() {
            store.dead.borrow_mut().push(self.key);
        }
    }
}

/// A shared reference to one layer a [`LayerRegistry`](super::LayerRegistry)
/// holds (C++ `SdfLayerRefPtr`). Cloning it shares the layer: an edit through
/// any clone is seen through every other, and the layer stays open while any
/// clone exists.
///
/// A handle keeps its registry's store alive, and with it every layer the
/// registry holds. A sink on a layer that captures a handle into the same
/// registry therefore holds the store in a cycle that never frees, as a C++
/// layer holding its own `SdfLayerRefPtr` would. Such a sink captures what it
/// needs from the layer instead.
///
/// # Borrowing
///
/// A handle holds no borrow; each of its reads borrows the layer for its own
/// duration.
///
/// [`try_borrow`](Self::try_borrow) lends one layer across several reads.
/// While the [`LayerGuard`] it returns lives, that layer cannot change: an
/// edit, a save, a reload, or a sink added or removed on it fails with
/// [`LayerError::Busy`], having staged nothing. A layer's sinks are part of
/// the [`Layer`] (see [`Layer::add_sink`]): changing them changes the layer.
/// The registry's other layers stay free to borrow, edit and add.
///
/// An edit borrows the registry's layers whole. Inside an edit's closure, and
/// in a sink's [`before_commit`](LayerSink::before_commit) that it runs, every
/// other read or write of the registry's layers fails with `Busy`, a live
/// query or one on an unrelated layer included. What names a layer or a
/// spec without reading it (an identifier, a path, `Debug`) still answers. An
/// [`after_commit`](LayerSink::after_commit) runs once the edit's borrow is
/// released.
///
/// | Held                       | add a layer | borrow a layer | edit the borrowed layer | edit another layer |
/// |----------------------------|-------------|----------------|-------------------------|--------------------|
/// | a [`LayerGuard`]           | yes         | yes            | `Busy`                  | yes                |
/// | an edit's closure          | `Busy`      | `Busy`         | (it is the edit)        | `Busy`             |
/// | a stage reading the layers | `Busy`      | yes            | `Busy`                  | `Busy`             |
#[derive(Clone)]
pub struct LayerHandle {
    /// The slot's token, declared first so it drops while the store is still
    /// held and can record the slot as dead.
    token: Rc<SlotToken>,
    /// The store the slot lives in, kept alive by every handle into it.
    store: Rc<LayerStore>,
}

impl LayerHandle {
    /// The layer's identifier.
    pub fn identifier(&self) -> &str {
        &self.token.identifier
    }

    /// The location that anchors the relative asset paths the layer authors
    /// (see [`Layer::anchor_location`]).
    pub(crate) fn anchor_location(&self) -> Option<&ar::ResolvedPath> {
        self.token.anchor.as_ref()
    }

    /// Where the layer was read from (see [`Layer::resolved_path`]), `None`
    /// for an anonymous layer. Fixed with the identifier, so it reads no
    /// content and never fails.
    pub fn resolved_path(&self) -> Option<&str> {
        self.token.anchor.as_deref().and_then(|path| path.to_str())
    }

    /// Whether the layer is anonymous (see [`Layer::is_anonymous`]). Reads
    /// the identifier only, so it never fails.
    pub fn is_anonymous(&self) -> bool {
        Layer::is_anonymous_identifier(self.identifier())
    }

    /// Run `f` on the layer, borrowed for the call alone: the layer's `Rc`
    /// is held while `f` runs, so an edit of the layer fails with `Busy` until
    /// it returns. Fails with [`LayerError::Busy`] inside an edit or a save
    /// on the registry.
    pub(crate) fn read<R>(&self, f: impl FnOnce(&Layer) -> R) -> Result<R, LayerError> {
        Ok(f(&*self.shared()?))
    }

    /// The layer's own `Rc`, cloned under a brief borrow of the slots. Fails
    /// with [`LayerError::Busy`] inside an edit of the registry.
    fn shared(&self) -> Result<Rc<Layer>, LayerError> {
        let slots = self.store.slots.try_borrow().map_err(|_| LayerError::Busy)?;
        let entry = slots.entry(self.token.key).expect("a handle keeps its slot filled");
        Ok(Rc::clone(&entry.layer))
    }

    /// Borrow the layer until the returned [`LayerGuard`] drops (see the
    /// borrowing rules above). Fails with [`LayerError::Busy`] from inside an
    /// edit or a save on the same registry.
    pub fn try_borrow(&self) -> Result<LayerGuard, LayerError> {
        Ok(LayerGuard {
            layer: self.shared()?,
            _handle: self.clone(),
        })
    }

    /// [`try_borrow`](Self::try_borrow), panicking from inside an edit or a
    /// save on the same registry, as `RefCell::borrow` panics while the cell
    /// is mutably borrowed.
    #[track_caller]
    pub fn borrow(&self) -> LayerGuard {
        self.try_borrow()
            .expect("the layer is borrowed outside an edit or a save of its registry")
    }

    /// Author a batch of edits on the layer as one atomic transaction (see
    /// [`Layer::edit`]), visible through every handle to it. Returns whether
    /// the edit produced a composition change.
    ///
    /// The closure runs with the registry borrowed: it cannot read or edit
    /// through another handle of the same registry. An edit fails with
    /// [`LayerError::Busy`], having staged nothing, while the layer is
    /// borrowed, and from inside another edit on the registry, or from a
    /// resolver a stage calls while it reads the registry's layers. The edit is
    /// attributed to no stage: a stage holding the layer sees it as an edit
    /// made elsewhere. The layer's sinks see it in commit order, after the
    /// edits committed before it.
    pub fn edit(&self, f: impl FnOnce(&mut LayerEdit<'_>) -> Result<(), AuthoringError>) -> Result<bool, LayerError> {
        self.store.edit(&[self], TxnContext::new(None), |edits| {
            f(&mut edits[0]).map_err(LayerError::from)
        })
    }

    /// Save the layer to the file its identifier names (see [`Layer::save`]).
    /// Fails with [`LayerError::Busy`] while the layer is borrowed, and from
    /// inside an edit on the same registry, or from a resolver a stage calls
    /// while it reads the registry's layers.
    pub fn save(&self) -> Result<(), LayerError> {
        self.with_layer_mut(Layer::save)?.map_err(LayerError::from)
    }

    /// Reload the layer from its asset (see [`Layer::reload`]), returning
    /// whether it did. Like an [`edit`](Self::edit) through a handle, the
    /// reload is attributed to no stage: every stage holding the layer
    /// recomposes what it reads from it, and drops the undo steps touching it.
    /// Fails with [`LayerError::Busy`] while the layer is borrowed, and from
    /// inside an edit on the same registry, or from a resolver a stage calls
    /// while it reads the registry's layers.
    pub fn reload(&self, force: bool) -> crate::Result<bool> {
        Self::reload_all(slice::from_ref(self), force)
    }

    /// Reload each of `handles`, layers of one registry, as
    /// [`reload`](Self::reload) does, in one transaction (C++
    /// `SdfLayer::ReloadLayers`), so a stage holding several of them
    /// recomposes once, returning whether any reloaded. A layer named twice
    /// reloads once.
    ///
    /// A package whose listing changed brings every live layer in it into
    /// the batch, reloaded when its asset changed, and the layers holding a
    /// package in common reload as one group, together with the packages'
    /// listings. Every group is tried: one with a layer whose asset cannot
    /// be read is left as it is whole, while a layer whose identifier no
    /// longer resolves is left as it is alone, and the first failure is
    /// returned once the rest have reloaded. A layer in no package is a group
    /// of its own.
    ///
    /// A borrowed layer the reload would leave as it is (no unsaved edits, and
    /// its asset unchanged unless `force`) does not stop the batch.
    ///
    /// Fails, with nothing reloaded, with [`LayerError::Busy`] when a layer the
    /// batch would change is borrowed or when called from inside an edit on the
    /// registry, or from a resolver a stage calls while it reads the registry's
    /// layers, and with [`LayerError::Foreign`] for layers of two registries.
    /// Both are found before any asset's content is read. A layer borrowed
    /// while the assets are read fails the commit with `Busy` after the reads.
    pub fn reload_all(handles: &[LayerHandle], force: bool) -> crate::Result<bool> {
        let Some(first) = handles.first() else {
            return Ok(false);
        };
        if let Some(foreign) = handles.iter().find(|handle| !Rc::ptr_eq(&handle.store, &first.store)) {
            return Err(LayerError::Foreign {
                identifier: foreign.identifier().to_owned(),
            }
            .into());
        }
        let store = &first.store;
        // No layer is freed until the reload has committed and delivered: a
        // freed layer's sinks drop, and a drop running user code could edit a
        // target between its reload being computed and committed.
        let _hold = store.hold();
        let mut seen = HashSet::new();
        let unique: Vec<&LayerHandle> = handles
            .iter()
            .filter(|handle| seen.insert(Rc::as_ptr(&handle.token)))
            .collect();
        store.ensure_writable()?;
        let _scope = ar::CacheScope::begin();
        let mut failed = Vec::new();
        // Each reload is computed against its layer's content as it is now. No
        // layer may change from here to the commit: every read below keeps
        // each edit of the registry out, one a resolver makes included, and
        // no user code runs between them.
        let mut members = Vec::new();
        // Whether the packages were listed anew, which a batch with nothing
        // to read leaves alone.
        let mut listed = false;
        // The packages whose listings changed.
        let mut changed = HashSet::new();
        {
            let read = store.read()?;
            for handle in &unique {
                let layer = read.layer(handle);
                if let Some(resolver) = layer.resolver() {
                    LayerRegistry::forget_packages(resolver.as_ref(), layer.real_path());
                }
            }
            for handle in unique {
                let step = match read.layer(handle).reload_due(force) {
                    Ok(due) => due.map(Step::Due),
                    Err(error) => {
                        failed.push((members.len(), error));
                        None
                    }
                };
                members.push(Member {
                    asked: true,
                    handle: handle.clone(),
                    held: read.held_by(handle).to_vec(),
                    packages: Vec::new(),
                    step,
                    package_changed: false,
                });
            }
            let resolver = members
                .iter()
                .find_map(|member| read.layer(&member.handle).resolver().cloned());
            if let Some(resolver) = resolver.filter(|_| members.iter().any(|member| member.step.is_some())) {
                listed = true;
                let mut listing = ReadListing::new(resolver.as_ref(), None);
                for member in &mut members {
                    member.packages = held_packages(read.layer(&member.handle).real_path(), &mut listing);
                }
                // A package whose listing changed, a nested one included,
                // brings every live layer in it into the batch, so none keeps
                // content its package no longer matches.
                let outermost: HashSet<String> = members
                    .iter()
                    .flat_map(|member| {
                        member
                            .held
                            .iter()
                            .chain(member.packages.iter().map(|(package, _)| package))
                    })
                    .map(|package| outermost_package(package))
                    .collect();
                changed = read
                    .packages_within(&outermost)
                    .into_iter()
                    .chain(
                        members
                            .iter()
                            .flat_map(|member| member.packages.iter().map(|(package, _)| package.clone())),
                    )
                    .filter(|package| {
                        let held = read.package(package).and_then(HeldPackage::files);
                        held.map(|held| &**held) != listing.files(package).as_deref()
                    })
                    .collect();
                let batch: HashSet<SlotKey> = members.iter().map(|member| member.handle.token.key).collect();
                for token in read.holders(&changed) {
                    if batch.contains(&token.key) {
                        continue;
                    }
                    let handle = LayerHandle {
                        token,
                        store: Rc::clone(store),
                    };
                    let layer = read.layer(&handle);
                    // A layer brought in reloads when its asset changed. One
                    // with unsaved edits keeps them, and one whose asset no
                    // longer resolves where it was read stays as it is:
                    // neither was asked for, so neither stops the batch.
                    let step = (!layer.is_dirty())
                        .then(|| layer.reload_due(false).ok().flatten().map(Step::Due))
                        .flatten();
                    members.push(Member {
                        asked: false,
                        held: read.held_by(&handle).to_vec(),
                        packages: held_packages(layer.real_path(), &mut listing),
                        handle,
                        step,
                        package_changed: false,
                    });
                }
            }
        }
        let mut groups = Groups::default();
        for member in &mut members {
            let packages = member
                .held
                .iter()
                .chain(member.packages.iter().map(|(package, _)| package));
            member.package_changed = packages.clone().any(|package| changed.contains(package));
            groups.join(packages);
        }
        // A layer whose identifier no longer resolves is left as it is
        // alone. Any other failure to tell whether a layer reloads, a moved
        // asset among them, leaves its group whole.
        for (member, error) in &failed {
            if !matches!(error, crate::Error::UnresolvedAsset(_)) {
                groups.fail(*member);
            }
        }
        // The first failure in the order the batch names the layers, whichever
        // check found it.
        let first = |failed: Vec<(usize, crate::Error)>| {
            failed
                .into_iter()
                .min_by_key(|&(member, _)| member)
                .map(|(_, error)| error)
        };
        // A layer brought in that is borrowed stays as it is, unless its
        // package changed: a layer the report of that cannot reach would
        // anchor against listings it no longer matches, so its group stays as
        // it was. A batch that would change a borrowed layer it was asked for
        // fails here, before any asset's content is read.
        for (at, member) in members.iter_mut().enumerate() {
            // A layer asked for is checked with the batch below.
            let edited = member.step.is_some() || member.package_changed;
            if !member.asked && edited && store.ensure_editable(&[&member.handle]).is_err() {
                member.step = None;
                if member.package_changed {
                    groups.fail(at);
                    failed.push((at, LayerError::Busy.into()));
                }
            }
        }
        let changing: Vec<&LayerHandle> = members
            .iter()
            .enumerate()
            .filter(|(at, member)| (member.step.is_some() || member.package_changed) && !groups.failed(*at))
            .map(|(_, member)| &member.handle)
            .collect();
        store.ensure_editable(&changing)?;
        {
            let read = store.read()?;
            // TODO(rayon): each layer's read and diff is independent of the
            // others'.
            for (at, member) in members.iter_mut().enumerate() {
                let Some(Step::Due(due)) = member.step.take().filter(|_| !groups.failed(at)) else {
                    continue;
                };
                match read.layer(&member.handle).read_due(due) {
                    Ok(reload) => member.step = Some(Step::Read(reload)),
                    Err(error) => {
                        groups.fail(at);
                        failed.push((at, error));
                    }
                }
            }
        }
        // A group a failure dropped keeps its content and its listings whole.
        let mut targets = Vec::new();
        let mut contents = Vec::new();
        let mut relisted = Vec::new();
        for (at, member) in members.iter_mut().enumerate() {
            if groups.failed(at) {
                continue;
            }
            let reload = if let Some(Step::Read(reload)) = member.step.take() {
                Some(reload)
            } else {
                None
            };
            // A layer of a package whose listing changed reports the change,
            // whether or not its own content changed.
            if reload.is_some() || member.package_changed {
                targets.push(&member.handle);
                contents.push((reload, member.package_changed));
            }
            if listed && (!member.held.is_empty() || !member.packages.is_empty()) {
                relisted.push((member.handle.token.key, mem::take(&mut member.packages)));
            }
        }
        let failed = first(failed);
        if targets.is_empty() {
            return failed.map_or(Ok(false), Err);
        }
        // A sink offered the commit, and an observer of it, find the packages
        // listed anew; a commit that fails leaves them as they were.
        let mut restore = Relisted {
            store,
            previous: Some(store.relist(relisted)),
        };
        let committed = store.commit(&targets, TxnContext::new(None), |edits| {
            for (edit, (reload, package_changed)) in edits.iter_mut().zip(contents) {
                if let Some(reload) = reload {
                    edit.reload(reload);
                }
                if package_changed {
                    edit.package_changed();
                }
            }
            Ok::<_, LayerError>(())
        });
        let committed = committed?;
        restore.previous = None;
        store.deliver(committed);
        failed.map_or(Ok(true), Err)
    }

    /// Install a [`LayerSink`] on the layer (see [`Layer::add_sink`]). Fails
    /// with [`LayerError::Busy`] while the layer is borrowed, and from inside
    /// an edit on the same registry, or from a resolver a stage calls while it
    /// reads the registry's layers.
    pub fn add_sink<S: LayerSink + 'static>(&self, sink: S) -> Result<LayerSinkId, LayerError> {
        self.with_layer_mut(|layer| layer.add_sink(sink))
    }

    /// Remove the sink with `id` (see [`Layer::remove_sink`]). Fails with
    /// [`LayerError::Busy`] while the layer is borrowed, and from inside an
    /// edit on the same registry, or from a resolver a stage calls while it
    /// reads the registry's layers.
    pub fn remove_sink(&self, id: LayerSinkId) -> Result<(), LayerError> {
        self.with_layer_mut(|layer| layer.remove_sink(id))
    }

    /// Subscribe `subscriber` to the layer's commits, until the returned
    /// [`Subscription`] drops.
    pub(crate) fn subscribe(&self, subscriber: Rc<dyn Subscriber>) -> Result<Subscription, LayerError> {
        let id = self.with_entry_mut(|entry| entry.subscribers.add(subscriber))?;
        Ok(Subscription {
            store: Rc::downgrade(&self.store),
            key: self.token.key,
            id,
        })
    }

    /// Run `f` on the layer with the registry borrowed mutably. Fails with
    /// [`LayerError::Busy`] while the layer is borrowed, and from inside a
    /// composition read or an edit on the same registry.
    fn with_layer_mut<R>(&self, f: impl FnOnce(&mut Layer) -> R) -> Result<R, LayerError> {
        self.with_entry_mut(|entry| Rc::get_mut(&mut entry.layer).map(f))?
            .ok_or(LayerError::Busy)
    }

    /// Run `f` on the layer's slot entry with the registry borrowed mutably,
    /// then free the slots whose last handle dropped meanwhile. Fails with
    /// [`LayerError::Busy`] from inside a composition read or an edit on the
    /// same registry.
    fn with_entry_mut<R>(&self, f: impl FnOnce(&mut Entry) -> R) -> Result<R, LayerError> {
        let result = {
            let mut slots = self.store.slots_mut().map_err(|_| LayerError::Busy)?;
            f(slots.entry_mut(self.token.key).expect("a handle keeps its slot filled"))
        };
        self.store.sweep_dead();
        Ok(result)
    }
}

/// Two handles are equal when they share one layer.
impl PartialEq for LayerHandle {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.token, &other.token)
    }
}

impl Eq for LayerHandle {}

/// Hashes the layer's identity, as [`PartialEq`] compares it.
impl Hash for LayerHandle {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.token).hash(state);
    }
}

impl fmt::Debug for LayerHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("LayerHandle").field(&self.token.identifier).finish()
    }
}

/// A borrow of one layer a [`LayerRegistry`](super::LayerRegistry) holds, from
/// [`LayerHandle::try_borrow`] or [`LayerHandle::borrow`]. It derefs to the
/// [`Layer`].
///
/// While it lives, the layer cannot change: an edit, a save, a reload, or a
/// sink added or removed on it fails with [`LayerError::Busy`]. The rest of
/// the registry is unaffected (see the borrowing rules on [`LayerHandle`]).
/// Like a handle, it keeps the layer open.
#[must_use = "the layer is borrowed only while the guard lives"]
pub struct LayerGuard {
    /// The layer, declared first so the guard gives up its count on it before
    /// the handle's drop can mark the slot dead. The sweep that frees the slot
    /// then finds the layer's `Rc` unique.
    layer: Rc<Layer>,
    /// Keeps the layer open while it is borrowed.
    _handle: LayerHandle,
}

impl Deref for LayerGuard {
    type Target = Layer;

    fn deref(&self) -> &Layer {
        &self.layer
    }
}

impl fmt::Debug for LayerGuard {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.layer, f)
    }
}

/// A [`Subscriber`]'s subscription to one layer, ended when this drops.
pub(crate) struct Subscription {
    /// The store the layer lives in.
    store: Weak<LayerStore>,
    /// The layer's slot, so an ended subscription never reaches a slot
    /// refilled since.
    key: SlotKey,
    /// The subscriber's id on the layer.
    id: sink::Id<dyn Subscriber>,
}

impl Drop for Subscription {
    fn drop(&mut self) {
        let Some(store) = self.store.upgrade() else {
            return;
        };
        match store.slots.try_borrow_mut() {
            Ok(mut slots) => {
                if let Some(entry) = slots.entry_mut(self.key) {
                    entry.subscribers.remove(self.id);
                }
            }
            Err(_) => store.unsubscribed.borrow_mut().push((self.key, self.id)),
        }
    }
}

/// A shared borrow of a store's layers, through which a caller holding
/// several handles reads them all under one borrow. Dropped, it releases the
/// borrow and frees the slots whose last handle dropped while it was held,
/// unless a [`SweepHold`] is live, whose last release frees them.
pub(crate) struct StoreRead<'a> {
    /// The borrow, `None` only while the read drops.
    slots: Option<Ref<'a, Slots>>,
    /// The store the borrow is of.
    store: &'a LayerStore,
}

impl StoreRead<'_> {
    /// The layer `handle` names. The handle belongs to this store.
    pub(crate) fn layer(&self, handle: &LayerHandle) -> &Layer {
        &self
            .slots
            .as_ref()
            .expect("a read holds its borrow until it drops")
            .entry(handle.token.key)
            .expect("a handle keeps its slot filled in its own store")
            .layer
    }

    /// The live layer whose identifier is `identifier`, or, with `real_path`,
    /// the one read from that location.
    pub(crate) fn find(&self, identifier: &str, real_path: Option<&str>) -> Option<&Layer> {
        let slots = self.slots.as_ref().expect("a read holds its borrow until it drops");
        let entry = slots.slots[slots.find(identifier, real_path)? as usize]
            .entry
            .as_ref()?;
        Some(&entry.layer)
    }

    /// The packages the layer `handle` names holds ([`held_packages`]).
    pub(crate) fn held_by(&self, handle: &LayerHandle) -> &[String] {
        &self
            .slots
            .as_ref()
            .expect("a read holds its borrow until it drops")
            .entry(handle.token.key)
            .expect("a handle keeps its slot filled in its own store")
            .packages
    }

    /// Every package the store holds that is one of `outermost` or lies in
    /// one of them.
    fn packages_within(&self, outermost: &HashSet<String>) -> Vec<String> {
        let slots = self.slots.as_ref().expect("a read holds its borrow until it drops");
        slots
            .packages
            .keys()
            .filter(|package| outermost.contains(&outermost_package(package)))
            .cloned()
            .collect()
    }

    /// The token of each live layer that holds one of `packages`.
    fn holders(&self, packages: &HashSet<String>) -> Vec<Rc<SlotToken>> {
        let slots = self.slots.as_ref().expect("a read holds its borrow until it drops");
        let mut seen = HashSet::new();
        packages
            .iter()
            .filter_map(|package| slots.packages.get(package))
            .flat_map(|held| &held.layers)
            .filter(|&&index| seen.insert(index))
            .filter_map(|&index| slots.slots[index as usize].entry.as_ref()?.token.upgrade())
            .collect()
    }

    /// The package `package`, while a live layer holds it.
    pub(crate) fn package(&self, package: &str) -> Option<&HeldPackage> {
        self.slots
            .as_ref()
            .expect("a read holds its borrow until it drops")
            .package(package)
    }
}

impl Drop for StoreRead<'_> {
    fn drop(&mut self) {
        self.slots.take();
        // As at a hold's release, a panic unwinding frees nothing: a freed
        // layer's sink that panicked too would abort. The next sweep frees it.
        if !thread::panicking() {
            self.store.sweep_dead();
        }
    }
}

impl LayerStore {
    /// Borrow the layers for reading. Fails with [`LayerError::Busy`] while
    /// an edit holds them.
    pub(crate) fn read(&self) -> Result<StoreRead<'_>, LayerError> {
        let slots = self.slots.try_borrow().map_err(|_| LayerError::Busy)?;
        Ok(StoreRead {
            slots: Some(slots),
            store: self,
        })
    }

    /// A handle to the live layer whose identifier is `identifier`, or, with
    /// `real_path`, the one read from that location.
    pub(crate) fn find(
        self: &Rc<Self>,
        identifier: &str,
        real_path: Option<&str>,
    ) -> Result<Option<LayerHandle>, LayerError> {
        let slots = self.slots.try_borrow().map_err(|_| LayerError::Busy)?;
        Ok(slots
            .find(identifier, real_path)
            .and_then(|index| self.live(&slots, index)))
    }

    /// Hold `layer`, committing any edit it has staged without notifying its
    /// sinks, and return a handle to it. Fails, handing the layer back, with
    /// [`LayerError::Busy`] while the store is borrowed and with
    /// [`LayerError::Duplicate`] when a live layer already carries its
    /// identifier or, for a layer read from an asset, its real path.
    ///
    /// `packages` names each package the layer lies in, with its files where
    /// they were listed. The store holds each package while a live layer lies
    /// in it; a package already held keeps the listing it has.
    pub(crate) fn insert(
        self: &Rc<Self>,
        mut layer: Layer,
        packages: PackageListings,
    ) -> Result<LayerHandle, AdoptError> {
        self.sweep();
        let Ok(mut slots) = self.slots_mut() else {
            return Err(AdoptError {
                error: LayerError::Busy,
                layer: Box::new(layer),
            });
        };
        let real_path = (!layer.is_anonymous()).then(|| layer.real_path().to_owned());
        let taken = |index: Option<&u32>| index.is_some_and(|&index| self.live(&slots, index).is_some());
        if taken(slots.by_identifier.get(layer.identifier()))
            || real_path
                .as_ref()
                .is_some_and(|path| taken(slots.by_real_path.get(path)))
        {
            let identifier = layer.identifier().to_owned();
            return Err(AdoptError {
                error: LayerError::Duplicate { identifier },
                layer: Box::new(layer),
            });
        }
        layer.discard_changes();
        let index = slots.free.pop().unwrap_or_else(|| {
            slots.slots.push(Slot::default());
            u32::try_from(slots.slots.len() - 1).expect("fewer than u32::MAX layers")
        });
        let slot = &mut slots.slots[index as usize];
        let key = SlotKey {
            index,
            epoch: slot.epoch,
        };
        let token = Rc::new(SlotToken {
            key,
            identifier: layer.identifier().to_owned(),
            anchor: layer.anchor_location(),
            store: Rc::downgrade(self),
        });
        let mut held = Vec::new();
        for (package, files) in packages {
            slots.hold_package(package.clone(), files, index, false);
            held.push(package);
        }
        slots.slots[index as usize].entry = Some(Entry {
            layer: Rc::new(layer),
            subscribers: sink::Set::default(),
            token: Rc::downgrade(&token),
            packages: held,
        });
        slots.by_identifier.insert(token.identifier.clone(), index);
        if let Some(real_path) = real_path {
            slots.by_real_path.insert(real_path, index);
        }
        Ok(LayerHandle {
            token,
            store: Rc::clone(self),
        })
    }

    /// Fails with [`LayerError::Busy`] while a composition read or an edit
    /// holds the store, so a caller about to add a layer can tell before doing
    /// the work of reading it.
    pub(crate) fn ensure_writable(&self) -> Result<(), LayerError> {
        self.slots.try_borrow_mut().map(drop).map_err(|_| LayerError::Busy)
    }

    /// Fails as an edit of the layers `handles` name would fail now (see
    /// [`edit`](Self::edit)), running nothing. A caller about to do the work
    /// an edit commits checks this first.
    fn ensure_editable(&self, handles: &[&LayerHandle]) -> Result<(), LayerError> {
        self.with_layers(handles, |_| Ok(()))
    }

    /// Have each reloaded layer `relisted` names hold the packages listed
    /// beside it, in place of those it held (see [`held_packages`]),
    /// returning what each held before, which restores it.
    fn relist(&self, relisted: Vec<(SlotKey, PackageListings)>) -> Vec<(SlotKey, PackageListings)> {
        let Ok(mut slots) = self.slots_mut() else {
            return Vec::new();
        };
        // Every layer's listings are taken before any changes: layers holding
        // one package share its listing.
        let previous = relisted
            .iter()
            .map(|&(key, _)| {
                let held = slots.entry(key).map(|entry| entry.packages.clone()).unwrap_or_default();
                let listings = held
                    .into_iter()
                    .map(|package| {
                        let files = slots.packages.get(&package).and_then(|held| held.files.clone());
                        (package, files)
                    })
                    .collect();
                (key, listings)
            })
            .collect();
        for (key, packages) in relisted {
            slots.relist(key, packages);
        }
        previous
    }

    /// Hold the store's sweeps until the returned guard drops (see
    /// [`SweepHold`]).
    pub(crate) fn hold(&self) -> SweepHold<'_> {
        self.holds.set(self.holds.get() + 1);
        SweepHold(self)
    }

    /// [`sweep`](Self::sweep) when a handle dropped while the store was
    /// borrowed left a slot to free. A no-op under an enclosing borrow or a
    /// live hold, whose release sweeps.
    fn sweep_dead(&self) {
        if !self.dead.borrow().is_empty() {
            self.sweep();
        }
    }

    /// Free every slot whose last handle has dropped, and apply the
    /// subscriptions that ended while the store was borrowed. A no-op while
    /// the store is borrowed or a [`SweepHold`] lives; the next sweep frees
    /// what this one skipped.
    pub(crate) fn sweep(&self) {
        if self.holds.get() > 0 {
            return;
        }
        let Ok(mut slots) = self.slots_mut() else {
            return;
        };
        let dead = mem::take(&mut *self.dead.borrow_mut());
        // The freed layers drop once the borrow is released, so nothing their
        // drop reaches finds the store borrowed.
        let freed: Vec<Entry> = dead.into_iter().filter_map(|key| slots.free_slot(key)).collect();
        drop(slots);
        drop(freed);
    }

    /// Run `f` over the layers `handles` name, in order, as one atomic
    /// transaction `txn`, then deliver the sinks' notifications through the
    /// registry's queue. Fails, having staged nothing, with
    /// [`LayerError::Busy`] when the store is already borrowed or a
    /// [`LayerGuard`] or live query borrows one of the layers, and with
    /// [`LayerError::Foreign`] or [`LayerError::Repeated`] for a handle of
    /// another registry or one named twice.
    pub(crate) fn edit<E: From<sink::Error> + From<LayerError>>(
        &self,
        handles: &[&LayerHandle],
        txn: TxnContext,
        f: impl FnOnce(&mut [LayerEdit<'_>]) -> Result<(), E>,
    ) -> Result<bool, E> {
        Ok(self.deliver(self.commit(handles, txn, f)?))
    }

    /// The commit half of [`edit`](Self::edit): the transaction lands, and
    /// its notifications wait for [`deliver`](Self::deliver).
    pub(crate) fn commit<E: From<sink::Error> + From<LayerError>>(
        &self,
        handles: &[&LayerHandle],
        txn: TxnContext,
        f: impl FnOnce(&mut [LayerEdit<'_>]) -> Result<(), E>,
    ) -> Result<Committed, E> {
        self.with_layers(handles, |targets| edit_layers(targets, txn, f))
    }

    /// Deliver `committed`'s notifications through the store's queue, after
    /// those queued ahead of them, and return whether it changed anything.
    pub(crate) fn deliver(&self, committed: Committed) -> bool {
        // A sink can drop a layer's last handle; the layer is freed once the
        // notifications are delivered, not inside a later sink's callback.
        let _hold = self.hold();
        committed.dispatch_via(&self.dispatch)
    }

    /// Stage `f` over the layers `handles` name to check it applies, then
    /// discard it, firing nothing ([`dry_run_layers`]). Fails as
    /// [`edit`](Self::edit) does.
    pub(crate) fn dry_run<E: From<LayerError>>(
        &self,
        handles: &[&LayerHandle],
        f: impl FnOnce(&mut [LayerEdit<'_>]) -> Result<(), E>,
    ) -> Result<(), E> {
        self.with_layers(handles, |targets| dry_run_layers(targets, f))
    }

    /// Run `f` over the layers `handles` name, in order, each with its
    /// subscribers, with the slots borrowed mutably. Fails, having run
    /// nothing, with [`LayerError::Busy`] when the store is already borrowed
    /// or a [`LayerGuard`] or live query borrows any of the layers, and with
    /// [`LayerError::Foreign`] or [`LayerError::Repeated`] for a handle of
    /// another registry or one named twice.
    fn with_layers<R, E: From<LayerError>>(
        &self,
        handles: &[&LayerHandle],
        f: impl FnOnce(&mut [TargetLayer<'_>]) -> Result<R, E>,
    ) -> Result<R, E> {
        for (position, handle) in handles.iter().enumerate() {
            let identifier = || handle.identifier().to_owned();
            if !ptr::eq(&*handle.store, self) {
                return Err(LayerError::Foreign {
                    identifier: identifier(),
                }
                .into());
            }
            if handles[..position].contains(handle) {
                return Err(LayerError::Repeated {
                    identifier: identifier(),
                }
                .into());
            }
        }
        let result = 'edit: {
            let Ok(mut slots) = self.slots_mut() else {
                break 'edit Err(LayerError::Busy.into());
            };
            // A single layer, the common edit, takes its slot directly, without
            // the scan that pairs several keys with their slots.
            if let [handle] = handles {
                match slots.target(handle.token.key) {
                    Some(target) => f(&mut [target]),
                    None => Err(LayerError::Busy.into()),
                }
            } else {
                let keys: Vec<SlotKey> = handles.iter().map(|handle| handle.token.key).collect();
                match slots.targets(&keys) {
                    Some(mut targets) => f(&mut targets),
                    None => Err(LayerError::Busy.into()),
                }
            }
        };
        self.sweep_dead();
        result
    }

    /// Borrow the slots mutably, first applying the subscriptions that ended
    /// while they were borrowed.
    fn slots_mut(&self) -> Result<RefMut<'_, Slots>, BorrowMutError> {
        let mut slots = self.slots.try_borrow_mut()?;
        for (key, id) in mem::take(&mut *self.unsubscribed.borrow_mut()) {
            if let Some(entry) = slots.entry_mut(key) {
                entry.subscribers.remove(id);
            }
        }
        Ok(slots)
    }

    /// A handle to the slot at `index`, while a handle still holds it.
    fn live(self: &Rc<Self>, slots: &Slots, index: u32) -> Option<LayerHandle> {
        let entry = slots.slots[index as usize].entry.as_ref()?;
        Some(LayerHandle {
            token: entry.token.upgrade()?,
            store: Rc::clone(self),
        })
    }
}

impl Slots {
    /// The package `package`, while a live layer holds it.
    fn package(&self, package: &str) -> Option<&HeldPackage> {
        let held = self.packages.get(package)?;
        let live = held.layers.iter().any(|&index| {
            self.slots[index as usize]
                .entry
                .as_ref()
                .is_some_and(|entry| entry.token.strong_count() > 0)
        });
        live.then_some(held)
    }

    /// Record that the layer in slot `index` holds `package`, listed as
    /// `files`, a failed listing included. The listing replaces the one held
    /// when `fresh`, read anew from the package, and where no live layer
    /// holds the package, whose listing may predate a change. A live
    /// package keeps its listing otherwise: the root chains its layers hold
    /// were read from it.
    fn hold_package(&mut self, package: String, files: Option<Rc<PackageFiles>>, index: u32, fresh: bool) {
        let replace = fresh || self.package(&package).is_none();
        let held = self.packages.entry(package).or_insert(HeldPackage {
            files: None,
            layers: Vec::new(),
        });
        if replace {
            held.files = files;
        }
        // Only a relist can find the slot holding the package already.
        if !(fresh && held.layers.contains(&index)) {
            held.layers.push(index);
        }
    }

    /// Record that the layer in slot `index` no longer holds `package`,
    /// dropping a package no layer holds.
    fn release_package(&mut self, package: &str, index: u32) {
        if let Some(held) = self.packages.get_mut(package) {
            held.layers.retain(|&layer| layer != index);
            if held.layers.is_empty() {
                self.packages.remove(package);
            }
        }
    }

    /// Have the layer in slot `key` hold `packages`, each read anew, in place
    /// of those it holds.
    fn relist(&mut self, key: SlotKey, packages: PackageListings) {
        let Some(entry) = self.entry_mut(key) else {
            return;
        };
        let old = mem::replace(
            &mut entry.packages,
            packages.iter().map(|(package, _)| package.clone()).collect(),
        );
        for package in &old {
            if !packages.iter().any(|(held, _)| held == package) {
                self.release_package(package, key.index);
            }
        }
        for (package, files) in packages {
            self.hold_package(package, files, key.index, true);
        }
    }

    /// The slot of the live layer whose identifier is `identifier`, or, with
    /// `real_path`, of the one read from that location.
    fn find(&self, identifier: &str, real_path: Option<&str>) -> Option<u32> {
        let live = |index: Option<&u32>| {
            let &index = index?;
            let entry = self.slots[index as usize].entry.as_ref()?;
            (entry.token.strong_count() > 0).then_some(index)
        };
        live(self.by_identifier.get(identifier)).or_else(|| live(self.by_real_path.get(real_path?)))
    }

    /// The entry in the slot `key` names, while it holds the filling `key`
    /// came from.
    fn entry(&self, key: SlotKey) -> Option<&Entry> {
        let slot = self
            .slots
            .get(key.index as usize)
            .filter(|slot| slot.epoch == key.epoch)?;
        slot.entry.as_ref()
    }

    /// [`entry`](Self::entry), mutably.
    fn entry_mut(&mut self, key: SlotKey) -> Option<&mut Entry> {
        let slot = self
            .slots
            .get_mut(key.index as usize)
            .filter(|slot| slot.epoch == key.epoch)?;
        slot.entry.as_mut()
    }

    /// The layer the live slot `key` names, beside its subscribers, or `None`
    /// while a [`LayerGuard`] or live query borrows it.
    fn target(&mut self, key: SlotKey) -> Option<TargetLayer<'_>> {
        let entry = self.entry_mut(key).expect("a handle keeps its slot filled");
        entry.target()
    }

    /// [`target`](Self::target) for each of `keys`, in `keys` order, or `None`
    /// when a [`LayerGuard`] or live query borrows any of them. `keys` are
    /// distinct live slots, as every handle's key is.
    fn targets(&mut self, keys: &[SlotKey]) -> Option<Vec<TargetLayer<'_>>> {
        // TODO(perf): pairing keys with slots scans the whole arena; walking
        // the slots in key-index order would visit only the named ones.
        let position: HashMap<u32, usize> = keys.iter().enumerate().map(|(at, key)| (key.index, at)).collect();
        let mut found: Vec<(usize, &mut Entry)> = self
            .slots
            .iter_mut()
            .enumerate()
            .filter_map(|(index, slot)| {
                let at = *position.get(&u32::try_from(index).ok()?)?;
                (slot.epoch == keys[at].epoch).then_some(())?;
                slot.entry.as_mut().map(|entry| (at, entry))
            })
            .collect();
        found.sort_by_key(|&(at, _)| at);
        found.into_iter().map(|(_, entry)| entry.target()).collect()
    }

    /// Free the slot `key` names when no handle holds it, returning its entry
    /// for the caller to drop.
    fn free_slot(&mut self, key: SlotKey) -> Option<Entry> {
        let slot = self
            .slots
            .get_mut(key.index as usize)
            .filter(|slot| slot.epoch == key.epoch)?;
        if slot.entry.as_ref().is_some_and(|entry| entry.token.strong_count() > 0) {
            return None;
        }
        let entry = slot.entry.take()?;
        // Every guard holds a handle: a slot no handle holds has no guard.
        debug_assert_eq!(Rc::strong_count(&entry.layer), 1, "no guard outlives the handles");
        slot.epoch = slot.epoch.wrapping_add(1);
        self.free.push(key.index);
        let unindex = |map: &mut HashMap<String, u32>, name: &str| {
            if map.get(name) == Some(&key.index) {
                map.remove(name);
            }
        };
        unindex(&mut self.by_identifier, entry.layer.identifier());
        unindex(&mut self.by_real_path, entry.layer.real_path());
        for package in &entry.packages {
            self.release_package(package, key.index);
        }
        Some(entry)
    }
}

impl HeldPackage {
    /// What the package holds, or `None` where no listing of it succeeded:
    /// a package that cannot be opened.
    pub(crate) fn files(&self) -> Option<&Rc<PackageFiles>> {
        self.files.as_ref()
    }
}

impl Entry {
    /// The layer as an edit takes it, beside its subscribers, or `None` while
    /// a [`LayerGuard`] or a live query borrows it.
    fn target(&mut self) -> Option<TargetLayer<'_>> {
        Some(TargetLayer {
            layer: Rc::get_mut(&mut self.layer)?,
            subscribers: &self.subscribers,
        })
    }
}

/// A hold on a [`LayerStore`]'s sweeps: while it lives, no slot is freed,
/// so no layer drops (and no sink of one runs) under a borrow its holder
/// keeps. Dropping the last hold frees what the holds kept.
///
/// While a panic unwinds, the last release frees nothing, so no sink's drop
/// runs during the unwind; the next sweep frees what it kept.
#[must_use = "a hold protects nothing once dropped"]
pub(crate) struct SweepHold<'a>(&'a LayerStore);

impl Drop for SweepHold<'_> {
    fn drop(&mut self) {
        let holds = self.0.holds.get() - 1;
        self.0.holds.set(holds);
        if holds == 0 && !thread::panicking() {
            self.0.sweep_dead();
        }
    }
}

/// A `RefCell` whose every borrow holds a store's sweeps
/// ([`SweepHold`]) for as long as it lives, so no layer of the store is
/// freed, and no sink of one runs, while the cell is borrowed.
pub(crate) struct HeldCell<T> {
    /// The value.
    cell: RefCell<T>,
    /// The store whose sweeps the borrows hold.
    store: Rc<LayerStore>,
}

impl<T> HeldCell<T> {
    /// A cell holding `value`, whose borrows hold `store`'s sweeps.
    pub(crate) fn new(value: T, store: Rc<LayerStore>) -> Self {
        Self {
            cell: RefCell::new(value),
            store,
        }
    }

    /// Borrow the value, holding the store's sweeps. Panics while it is
    /// mutably borrowed, as [`RefCell::borrow`] does.
    #[track_caller]
    pub(crate) fn borrow(&self) -> Held<'_, T> {
        let hold = self.store.hold();
        Held {
            value: self.cell.borrow(),
            _hold: hold,
        }
    }

    /// Borrow the value mutably, holding the store's sweeps. Panics while it
    /// is borrowed, as [`RefCell::borrow_mut`] does.
    #[track_caller]
    pub(crate) fn borrow_mut(&self) -> HeldMut<'_, T> {
        let hold = self.store.hold();
        HeldMut {
            value: self.cell.borrow_mut(),
            _hold: hold,
        }
    }

    /// Whether the value is borrowed, shared or mutably.
    pub(crate) fn is_borrowed(&self) -> bool {
        self.cell.try_borrow_mut().is_err()
    }

    /// Whether the value is borrowed mutably.
    pub(crate) fn is_borrowed_mut(&self) -> bool {
        self.cell.try_borrow().is_err()
    }
}

/// A shared borrow of a [`HeldCell`].
pub(crate) struct Held<'a, T: ?Sized> {
    /// The borrow, declared first so it is released before the hold.
    value: Ref<'a, T>,
    /// The hold on the store's sweeps.
    _hold: SweepHold<'a>,
}

impl<'a, T: ?Sized> Held<'a, T> {
    /// A borrow of the part of the value `f` picks, keeping the hold
    /// ([`Ref::map`]).
    pub(crate) fn map<U: ?Sized>(this: Self, f: impl FnOnce(&T) -> &U) -> Held<'a, U> {
        Held {
            value: Ref::map(this.value, f),
            _hold: this._hold,
        }
    }
}

impl<T: ?Sized> Deref for Held<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.value
    }
}

/// A mutable borrow of a [`HeldCell`].
pub(crate) struct HeldMut<'a, T: ?Sized> {
    /// The borrow, declared first so it is released before the hold.
    value: RefMut<'a, T>,
    /// The hold on the store's sweeps.
    _hold: SweepHold<'a>,
}

impl<T: ?Sized> Deref for HeldMut<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.value
    }
}

impl<T: ?Sized> DerefMut for HeldMut<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

/// Package listings a reload installed ahead of its commit, restored when
/// it drops unless the commit landed: a veto, a borrow conflict, or a panic
/// in a sink leaves the listings as they were.
struct Relisted<'a> {
    store: &'a LayerStore,
    /// What the layers held before, until the commit lands.
    previous: Option<Vec<(SlotKey, PackageListings)>>,
}

impl Drop for Relisted<'_> {
    fn drop(&mut self) {
        if let Some(previous) = self.previous.take() {
            self.store.relist(previous);
        }
    }
}

/// One layer of a reload batch.
struct Member {
    /// Whether the layer was asked for, rather than brought in by a package
    /// that changed.
    asked: bool,
    /// The layer.
    handle: LayerHandle,
    /// The packages it holds now.
    held: Vec<String>,
    /// The packages it holds after the reload, with their listings
    /// ([`held_packages`]), when the batch lists them.
    packages: PackageListings,
    /// How far its reload has come, `None` when it does not reload.
    step: Option<Step>,
    /// Whether a package it holds changed what it holds, which the reload
    /// reports to it ([`ChangeList::did_change_package`](super::ChangeList::did_change_package)).
    package_changed: bool,
}

/// How far a reload batch's layer has come.
enum Step {
    /// Its reload is due, its asset not yet read.
    Due(Due),
    /// Its asset is read, the reload ready to commit.
    Read(Reload),
}

/// The groups a reload batch's layers fall in: layers that hold a package in
/// common reload together, all or none, as do the packages they hold.
#[derive(Default)]
struct Groups {
    /// Each member's parent in the union-find forest.
    parents: Vec<usize>,
    /// The first member found holding each package.
    holder: HashMap<String, usize>,
    /// The roots of the groups a failure dropped.
    failed: HashSet<usize>,
}

impl Groups {
    /// Adds the next member, holding `packages`, to the group of each member
    /// holding one of them.
    fn join<'a>(&mut self, packages: impl IntoIterator<Item = &'a String>) {
        let member = self.parents.len();
        self.parents.push(member);
        for package in packages {
            match self.holder.get(package) {
                Some(&other) => {
                    let (a, b) = (self.of(member), self.of(other));
                    self.parents[a] = b;
                }
                None => {
                    self.holder.insert(package.clone(), member);
                }
            }
        }
    }

    /// The group of `member`.
    fn of(&self, mut member: usize) -> usize {
        while self.parents[member] != member {
            member = self.parents[member];
        }
        member
    }

    /// Drops the group of `member`. Every member has joined by then.
    fn fail(&mut self, member: usize) {
        self.failed.insert(self.of(member));
    }

    /// Whether a failure dropped the group of `member`.
    fn failed(&self, member: usize) -> bool {
        self.failed.contains(&self.of(member))
    }
}

/// The outermost package of `package`, itself when it lies in none.
fn outermost_package(package: &str) -> String {
    ar::enclosing_packages(package)
        .into_iter()
        .next()
        .unwrap_or_else(|| package.to_owned())
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::sdf::commit::{CommitRecord, EditorId, Footprint, PendingCommit, Prepared, TxnId};
    use crate::sdf::layer_registry::tests::{HookResolver, counting_registry};
    use crate::{ar, sdf, vt};

    use std::cell::Cell;
    use std::fs;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::path::Path as FsPath;

    /// The footprint and origin of each commit a [`Footprints`] subscriber saw.
    type Seen = Rc<RefCell<Vec<(Footprint, Option<EditorId>)>>>;

    /// What a test observer saw, in order.
    type Log = Rc<RefCell<Vec<String>>>;

    /// A handle a test hook reaches, emptied at the test's end so the hook's
    /// registry does not keep itself alive.
    type HandleCell = Rc<RefCell<Option<LayerHandle>>>;

    /// A subscriber that logs each transaction's commit or abort, with the
    /// `documentation` of `/P` its prepare saw in the pre-edit base.
    struct Watch {
        log: Log,
        /// Panic after building the capture, so its drop is the abort.
        panic: bool,
    }

    /// One transaction's capture: the transaction it was prepared for and the
    /// pre-edit value it saw.
    struct Capture {
        log: Log,
        txn: TxnId,
        before: String,
        committed: bool,
    }

    impl Subscriber for Watch {
        fn prepare(&self, commit: &PendingCommit<'_>) -> Option<Box<dyn Prepared>> {
            let before = commit
                .change
                .base
                .try_field(&sdf::path("/P").unwrap(), "documentation")
                .unwrap()
                .map_or_else(String::new, |value| value.try_as_string_ref().unwrap().clone());
            let capture = Capture {
                log: Rc::clone(&self.log),
                txn: commit.txn.id,
                before,
                committed: false,
            };
            assert!(!self.panic, "a subscriber that panics in prepare");
            Some(Box::new(capture))
        }
    }

    impl Prepared for Capture {
        fn commit(mut self: Box<Self>, record: &CommitRecord) -> Option<Rc<dyn sdf::LayerSink>> {
            assert_eq!(record.txn, self.txn, "committed with its own transaction's record");
            self.log.borrow_mut().push(format!("commit {}", self.before));
            self.committed = true;
            None
        }
    }

    impl Drop for Capture {
        fn drop(&mut self) {
            if !self.committed {
                self.log.borrow_mut().push(format!("abort {}", self.before));
            }
        }
    }

    /// A subscriber that keeps each commit's footprint and origin.
    struct Footprints(Seen);

    /// The capture of a [`Footprints`] subscriber.
    struct Keep(Seen);

    impl Subscriber for Footprints {
        fn prepare(&self, _commit: &PendingCommit<'_>) -> Option<Box<dyn Prepared>> {
            Some(Box::new(Keep(Rc::clone(&self.0))))
        }
    }

    impl Prepared for Keep {
        fn commit(self: Box<Self>, record: &CommitRecord) -> Option<Rc<dyn sdf::LayerSink>> {
            self.0.borrow_mut().push(((*record.footprint).clone(), record.origin));
            None
        }
    }

    /// A sink that vetoes every edit.
    struct Veto;

    impl sdf::LayerSink for Veto {
        fn before_commit(&self, _change: &sdf::PendingLayerChange<'_>) -> Result<(), sink::Error> {
            Err(sink::Error::new("vetoed"))
        }
    }

    /// What `f` returns when run from inside an edit of `handle`'s layer,
    /// where the registry's layers are borrowed whole.
    pub(crate) fn inside_edit<R>(handle: &LayerHandle, f: impl FnOnce() -> R) -> R {
        let mut result = None;
        handle
            .edit(|_| {
                result = Some(f());
                Ok(())
            })
            .expect("an edit of the layer runs");
        result.expect("the edit ran its closure")
    }

    /// An anonymous layer holding the prim `/P`.
    fn layer_with_prim(tag: &str) -> Layer {
        let mut layer = Layer::new_anonymous(tag);
        layer
            .edit(|edit| {
                sdf::PrimSpec::new(edit.data_mut(), "/P", sdf::Specifier::Def, "Xform")?;
                Ok(())
            })
            .unwrap();
        layer
    }

    /// Set `/P`'s `documentation` to `text` through `handle`.
    fn document(handle: &LayerHandle, text: &str) -> Result<bool, LayerError> {
        handle.edit(|edit| {
            let path = sdf::path("/P")?;
            edit.data_mut()
                .set_field(&path, "documentation", vt::Value::String(text.into()));
            Ok(())
        })
    }

    /// `/P`'s `documentation` as `handle` reads it.
    fn documentation(handle: &LayerHandle) -> Option<String> {
        let layer = handle.borrow();
        let value = layer
            .data()
            .try_field(&sdf::path("/P").unwrap(), "documentation")
            .unwrap()?;
        Some(value.try_as_string_ref().unwrap().clone())
    }

    /// Opening a file twice through one registry reads it once and hands out
    /// one shared layer: an edit through either handle is seen through both.
    #[test]
    fn find_or_open_shares() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("shared.usda");
        fs::write(&path, "#usda 1.0\n\ndef Xform \"P\"\n{\n}\n")?;
        let (registry, opens) = counting_registry();

        let first = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        let second = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        assert_eq!(opens.get(), 1, "the second open finds the first");
        assert_eq!(first, second);
        assert_eq!(registry.find(&path.to_string_lossy())?, Some(first.clone()));

        document(&first, "shared")?;
        assert_eq!(documentation(&second).as_deref(), Some("shared"));
        Ok(())
    }

    /// A layer named twice in one batch reloads once, reading its file once.
    #[test]
    fn reload_all_dedups() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("shared.usda");
        fs::write(&path, "#usda 1.0\n")?;
        let (registry, opens) = counting_registry();
        let handle = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        sdf::layer::tests::append(&path, "def \"P\" {}\n")?;
        assert!(LayerHandle::reload_all(&[handle.clone(), handle.clone()], false)?);
        assert_eq!(opens.get(), 2, "one open, one reload");
        assert!(handle.prim("/P")?.is_some());
        Ok(())
    }

    /// A batch naming layers of two registries reloads none of them, though
    /// only one has changed.
    #[test]
    fn reload_all_foreign() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("changed.usda");
        fs::write(&path, "#usda 1.0\n")?;
        let registry = sdf::LayerRegistry::default();
        let changed = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        let elsewhere = sdf::LayerRegistry::default()
            .adopt(layer_with_prim("b.usda"))
            .expect("adopts");
        sdf::layer::tests::append(&path, "def \"P\" {}\n")?;
        let reloaded = LayerHandle::reload_all(&[changed.clone(), elsewhere], false);
        assert!(
            matches!(reloaded, Err(crate::Error::Layer(LayerError::Foreign { .. }))),
            "{reloaded:?}"
        );
        assert!(changed.prim("/P")?.is_none());
        Ok(())
    }

    /// Opening a layer from inside an edit fails with `Busy` before reading
    /// the file.
    #[test]
    fn open_inside_edit_busy() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("later.usda");
        fs::write(&path, "#usda 1.0\n")?;
        let (registry, opens) = counting_registry();
        let held = registry.adopt(layer_with_prim("held.usda")).unwrap();

        let inner = inside_edit(&held, || registry.find_or_open(&path.to_string_lossy()));
        assert!(matches!(inner, Err(crate::Error::Layer(LayerError::Busy))));
        assert_eq!(opens.get(), 0, "nothing was read");
        Ok(())
    }

    /// A layer whose resolver is a clone of the registry that holds it is
    /// freed once its handles and the registry drop: the registry refers to its
    /// layers weakly, so the layer keeping the registry does not keep itself.
    #[test]
    fn registry_resolver_no_cycle() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("own.usda");
        fs::write(&path, "#usda 1.0\n")?;
        let registry = sdf::LayerRegistry::default();
        let mut layer = Layer::open_with(registry.clone(), path.to_string_lossy())?;
        let marker = Rc::new(());
        let held = Rc::clone(&marker);
        layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            let _ = &held;
        });
        let handle = registry.adopt(layer).unwrap();

        drop(handle);
        drop(registry);
        assert_eq!(Rc::strong_count(&marker), 1, "the layer was freed with its store");
        Ok(())
    }

    /// Once the last handle into a registry drops, its layers are freed with
    /// the store, and the registry holds the next layer in a fresh one.
    #[test]
    fn store_restarts_empty() {
        let registry = sdf::LayerRegistry::default();
        let layer = layer_with_prim("first.usda");
        let identifier = layer.identifier().to_owned();
        drop(registry.adopt(layer).unwrap());
        assert_eq!(registry.find(&identifier).unwrap(), None);
        let again = registry.adopt(Layer::new_in_memory(identifier.clone())).unwrap();
        assert_eq!(registry.find(&identifier).unwrap(), Some(again));
    }

    /// A layer found through a search path keeps the bare path as its
    /// identifier; opening the file it resolved to by its own path finds that
    /// layer through its real path.
    #[test]
    fn find_by_real_path() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let lib = dir.path().canonicalize()?;
        fs::write(lib.join("lib.usda"), "#usda 1.0\n")?;
        let registry = sdf::LayerRegistry::new(Box::new(ar::DefaultResolver::with_search_paths([&lib])));

        let searched = registry.find_or_open("lib.usda")?.expect("found on the search path");
        assert_eq!(searched.identifier(), "lib.usda");
        let direct = registry
            .find_or_open(&lib.join("lib.usda").to_string_lossy())?
            .expect("resolves");
        assert_eq!(direct, searched, "one layer, found by the file it was read from");
        Ok(())
    }

    /// One edit refuses a layer named twice or held by another registry,
    /// staging nothing.
    #[test]
    fn edit_refuses_handles() {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with_prim("a.usda")).unwrap();
        let elsewhere = sdf::LayerRegistry::default().adopt(layer_with_prim("b.usda")).unwrap();
        let edit = |handles: &[&LayerHandle]| {
            a.store
                .edit(handles, TxnContext::new(None), |_| Ok::<(), LayerError>(()))
        };
        assert!(matches!(edit(&[&a, &a]), Err(LayerError::Repeated { .. })));
        assert!(matches!(edit(&[&a, &elsewhere]), Err(LayerError::Foreign { .. })));
        let dry_run = |handles: &[&LayerHandle]| a.store.dry_run(handles, |_| Ok::<(), LayerError>(()));
        assert!(matches!(dry_run(&[&a, &a]), Err(LayerError::Repeated { .. })));
        assert!(matches!(dry_run(&[&a, &elsewhere]), Err(LayerError::Foreign { .. })));
    }

    /// A layer stays held until its last handle drops and a sweep runs; the
    /// sweep frees it.
    #[test]
    fn sweep_frees_layer() {
        let registry = sdf::LayerRegistry::default();
        // Another layer's handle keeps the store, so only the sweep frees.
        let _keep = registry.adopt(layer_with_prim("kept.usda")).unwrap();
        let mut layer = layer_with_prim("freed.usda");
        // A sink owning a marker: the marker's count drops when the layer does.
        let marker = Rc::new(());
        let held = Rc::clone(&marker);
        layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            let _ = &held;
        });
        let identifier = layer.identifier().to_owned();
        let handle = registry.adopt(layer).unwrap();
        let clone = handle.clone();

        drop(handle);
        registry.sweep();
        assert_eq!(Rc::strong_count(&marker), 2, "a clone still holds the layer");
        drop(clone);
        assert_eq!(Rc::strong_count(&marker), 2, "held until a sweep");
        registry.sweep();
        assert_eq!(Rc::strong_count(&marker), 1, "the sweep freed the layer");
        assert_eq!(registry.find(&identifier).unwrap(), None);
    }

    /// A hold keeps every sweep from freeing a layer, and releasing the last
    /// hold frees it.
    #[test]
    fn hold_defers_sweep() {
        let registry = sdf::LayerRegistry::default();
        let kept = registry.adopt(layer_with_prim("kept.usda")).unwrap();
        let mut layer = layer_with_prim("freed.usda");
        let marker = Rc::new(());
        let held = Rc::clone(&marker);
        layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            let _ = &held;
        });
        let handle = registry.adopt(layer).unwrap();
        let store = Rc::clone(&kept.store);
        let hold = store.hold();
        let nested = store.hold();
        drop(handle);
        registry.sweep();
        drop(store.read().unwrap());
        assert_eq!(Rc::strong_count(&marker), 2, "a hold defers every sweep");
        drop(nested);
        registry.sweep();
        assert_eq!(Rc::strong_count(&marker), 2, "an outer hold still defers it");
        drop(hold);
        assert_eq!(Rc::strong_count(&marker), 1, "the last release frees it");
    }

    /// A read a panic unwinds through frees nothing; the next sweep frees
    /// what it would have.
    #[test]
    fn unwind_defers_sweep() {
        let registry = sdf::LayerRegistry::default();
        let kept = registry.adopt(layer_with_prim("kept.usda")).unwrap();
        let mut layer = layer_with_prim("freed.usda");
        let marker = Rc::new(());
        let held = Rc::clone(&marker);
        layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            let _ = &held;
        });
        let handle = registry.adopt(layer).unwrap();
        let store = Rc::clone(&kept.store);
        let unwound = catch_unwind(AssertUnwindSafe(|| {
            let _read = store.read().unwrap();
            drop(handle);
            panic!("unwinding through a read");
        }));
        assert!(unwound.is_err());
        assert_eq!(Rc::strong_count(&marker), 2, "the unwinding read freed nothing");
        registry.sweep();
        assert_eq!(Rc::strong_count(&marker), 1, "the next sweep frees it");
    }

    /// A slot refilled after a sweep is a new filling: a key from before
    /// names nothing, and a subscription kept from before ends nothing of the
    /// new layer's.
    #[test]
    fn stale_key_misses() {
        let registry = sdf::LayerRegistry::default();
        // Another layer's handle keeps the store, so the freed slot is reused.
        let _keep = registry.adopt(layer_with_prim("kept.usda")).unwrap();
        let old = registry.adopt(layer_with_prim("old.usda")).unwrap();
        let stale = old.subscribe(Rc::new(Footprints(Rc::default()))).unwrap();
        let old_key = old.token.key;
        drop(old);
        registry.sweep();

        let new = registry.adopt(layer_with_prim("new.usda")).unwrap();
        assert_eq!(new.token.key.index, old_key.index, "the slot is reused");
        assert!(new.store.slots.borrow_mut().entry_mut(old_key).is_none());

        let seen = Rc::default();
        let _live = new.subscribe(Rc::new(Footprints(Rc::clone(&seen)))).unwrap();
        drop(stale);
        document(&new, "after").unwrap();
        assert_eq!(
            seen.borrow().len(),
            1,
            "the new layer's subscriber still sees its edits"
        );
    }

    /// An adopted layer can be found; a second layer with its identifier is
    /// refused.
    #[test]
    fn adopt_finds_and_refuses() {
        let registry = sdf::LayerRegistry::default();
        let layer = layer_with_prim("adopted.usda");
        let identifier = layer.identifier().to_owned();
        let handle = registry.adopt(layer).unwrap();
        assert_eq!(registry.find(&identifier).unwrap().as_ref(), Some(&handle));

        let refused = registry
            .adopt(Layer::new_in_memory(identifier.clone()))
            .expect_err("the identifier is taken");
        assert!(matches!(
            &refused.error,
            LayerError::Duplicate { identifier: duplicate } if *duplicate == identifier
        ));
        assert_eq!(refused.layer.identifier(), identifier, "the layer comes back");

        // Once no handle holds the first layer, the identifier is free again.
        drop(handle);
        assert!(registry.adopt(Layer::new_in_memory(identifier)).is_ok());
    }

    /// An access nested in an edit is refused with `Busy`, never a panic,
    /// and leaves the outer edit to finish.
    #[test]
    fn nested_access_busy() {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with_prim("a.usda")).unwrap();
        let b = registry.adopt(layer_with_prim("b.usda")).unwrap();

        let mut inner = None;
        a.edit(|edit| {
            inner = Some(document(&b, "inside an edit"));
            let path = sdf::path("/P")?;
            edit.data_mut()
                .set_field(&path, "documentation", vt::Value::String("outer".into()));
            Ok(())
        })
        .unwrap();
        assert!(matches!(inner, Some(Err(LayerError::Busy))));
        assert_eq!(documentation(&b), None, "the refused edit staged nothing");
        assert_eq!(documentation(&a).as_deref(), Some("outer"), "the outer edit committed");
    }

    /// A footprint names each field set or erased on a spec that existed, and
    /// each spec created or erased. A record carries its transaction's origin.
    #[test]
    fn footprint_fields_specs() {
        let registry = sdf::LayerRegistry::default();
        let mut layer = layer_with_prim("footprint.usda");
        layer
            .edit(|edit| {
                let path = sdf::path("/P")?;
                edit.data_mut()
                    .set_field(&path, "documentation", vt::Value::String("old".into()));
                sdf::PrimSpec::new(edit.data_mut(), "/Q", sdf::Specifier::Def, "Xform")?;
                Ok(())
            })
            .unwrap();
        let handle = registry.adopt(layer).unwrap();
        let seen = Rc::default();
        let _subscription = handle.subscribe(Rc::new(Footprints(Rc::clone(&seen)))).unwrap();

        handle
            .edit(|edit| {
                let path = sdf::path("/P")?;
                edit.data_mut()
                    .set_field(&path, "comment", vt::Value::String("new".into()));
                edit.data_mut().erase_field(&path, "documentation");
                Ok(())
            })
            .unwrap();
        let editor = EditorId::next();
        handle
            .store
            .edit(&[&handle], TxnContext::new(Some(editor)), |edits| {
                sdf::PrimSpec::new(edits[0].data_mut(), "/R", sdf::Specifier::Def, "Xform")?;
                let q = sdf::path("/Q").map_err(sdf::AuthoringError::from)?;
                edits[0].remove_spec(&q)?;
                Ok::<(), LayerError>(())
            })
            .unwrap();

        let seen = seen.borrow();
        let p = sdf::path("/P").unwrap();
        assert_eq!(
            seen[0].0.fields,
            [(p.clone(), "comment".to_owned()), (p, "documentation".to_owned())]
        );
        assert!(seen[0].0.specs.is_empty());
        assert_eq!(seen[0].1, None, "a raw handle edit is attributed to no editor");
        assert!(seen[1].0.specs.contains(&sdf::path("/Q").unwrap()));
        assert!(seen[1].0.specs.contains(&sdf::path("/R").unwrap()));
        assert_eq!(seen[1].1, Some(editor));
    }

    /// A veto from any layer's sink rolls the group back before any
    /// subscriber is prepared.
    #[test]
    fn veto_skips_prepare() {
        let registry = sdf::LayerRegistry::default();
        let mut vetoing = layer_with_prim("vetoing.usda");
        vetoing.add_sink(Veto);
        let watched = registry.adopt(layer_with_prim("watched.usda")).unwrap();
        let vetoing = registry.adopt(vetoing).unwrap();
        let log = Log::default();
        let _subscription = watched
            .subscribe(Rc::new(Watch {
                log: Rc::clone(&log),
                panic: false,
            }))
            .unwrap();

        let result = watched
            .store
            .edit(&[&watched, &vetoing], TxnContext::new(None), |edits| {
                for edit in edits.iter_mut() {
                    let path = sdf::path("/P").map_err(sdf::AuthoringError::from)?;
                    edit.data_mut()
                        .set_field(&path, "documentation", vt::Value::String("vetoed".into()));
                }
                Ok::<(), LayerError>(())
            });
        assert!(matches!(result, Err(LayerError::Edit(EditError::Rejected(_)))));
        assert!(log.borrow().is_empty(), "no subscriber was prepared");
        assert_eq!(documentation(&watched), None);
    }

    /// A panic in a later subscriber's prepare aborts the transaction: the
    /// earlier subscriber's capture and the panicking one's own both drop
    /// uncommitted, and the layer keeps its pre-edit data.
    #[test]
    fn prepare_panic_aborts() {
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with_prim("aborted.usda")).unwrap();
        let log = Log::default();
        let _first = handle
            .subscribe(Rc::new(Watch {
                log: Rc::clone(&log),
                panic: false,
            }))
            .unwrap();
        let _second = handle
            .subscribe(Rc::new(Watch {
                log: Rc::clone(&log),
                panic: true,
            }))
            .unwrap();

        let panicked = catch_unwind(AssertUnwindSafe(|| document(&handle, "lost")));
        assert!(panicked.is_err());
        assert_eq!(*log.borrow(), ["abort ", "abort "]);
        assert_eq!(documentation(&handle), None, "the edit rolled back");
    }

    /// An edit made from a sink's `after_commit` is a transaction of its own:
    /// each is prepared against its own pre-edit data and committed with its
    /// own record, and a later sink sees both in commit order.
    #[test]
    fn reentrant_edit_ordered() {
        let registry = sdf::LayerRegistry::default();
        let mut layer = layer_with_prim("reentrant.usda");
        let echo: HandleCell = Rc::default();
        {
            // Installed first, so it edits while the outer notification is still
            // being delivered to the sink after it.
            let echo = Rc::clone(&echo);
            let done = Cell::new(false);
            layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
                if !done.replace(true) {
                    let handle = echo.borrow().clone().expect("set before the first edit");
                    document(&handle, "second").expect("a sink may edit once the registry is free");
                }
            });
        }
        let events = Log::default();
        {
            let events = Rc::clone(&events);
            let echo = Rc::clone(&echo);
            layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
                let handle = echo.borrow().clone().expect("set before the first edit");
                events.borrow_mut().push(documentation(&handle).unwrap_or_default());
            });
        }
        let handle = registry.adopt(layer).unwrap();
        echo.replace(Some(handle.clone()));
        let log = Log::default();
        let _subscription = handle
            .subscribe(Rc::new(Watch {
                log: Rc::clone(&log),
                panic: false,
            }))
            .unwrap();

        document(&handle, "first").unwrap();
        assert_eq!(*log.borrow(), ["commit ", "commit first"]);
        assert_eq!(
            *events.borrow(),
            ["second", "second"],
            "the later sink saw both, after the nested edit"
        );
        assert_eq!(documentation(&handle).as_deref(), Some("second"));
        // The sinks hold a handle into their own registry; break the cycle.
        echo.replace(None);
    }

    /// A subscription dropped while the registry is borrowed ends at the next
    /// borrow that edits.
    #[test]
    fn unsubscribe_deferred() {
        let registry = sdf::LayerRegistry::default();
        let handle = registry.adopt(layer_with_prim("deferred.usda")).unwrap();
        let log = Log::default();
        let subscription = handle
            .subscribe(Rc::new(Watch {
                log: Rc::clone(&log),
                panic: false,
            }))
            .unwrap();

        inside_edit(&handle, move || drop(subscription));
        assert_eq!(handle.store.unsubscribed.borrow().len(), 1, "deferred");
        document(&handle, "unwatched").unwrap();
        assert!(log.borrow().is_empty(), "the next edit applied it first");
        assert!(handle.store.unsubscribed.borrow().is_empty());
    }

    /// A panicking `after_commit` loses only its own notification: the rest
    /// stay queued, in order, for the next dispatch.
    #[test]
    fn dispatch_panic_keeps_queue() {
        let registry = sdf::LayerRegistry::default();
        let mut layer = layer_with_prim("panicking.usda");
        let panics = Rc::new(Cell::new(true));
        {
            let panics = Rc::clone(&panics);
            layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
                assert!(!panics.replace(false), "the first notification panics");
            });
        }
        let events = Rc::new(Cell::new(0));
        {
            let events = Rc::clone(&events);
            layer.add_sink(move |_: &str, _: &sdf::ChangeList| events.set(events.get() + 1));
        }
        let handle = registry.adopt(layer).unwrap();

        let panicked = catch_unwind(AssertUnwindSafe(|| document(&handle, "first")));
        assert!(panicked.is_err());
        assert_eq!(events.get(), 0, "the second sink's notification is still queued");
        assert_eq!(documentation(&handle).as_deref(), Some("first"), "the data landed");

        document(&handle, "second").unwrap();
        assert_eq!(events.get(), 2, "the queued notification ran, then the new one");
    }

    /// Open `a.usda` and `b.usda` in `dir`, each written as `initial`, through
    /// `registry`, then append `appended` to both files, so a reload has
    /// something to read.
    fn stale_pair(
        registry: &sdf::LayerRegistry,
        dir: &FsPath,
        initial: &str,
        appended: &str,
    ) -> crate::Result<Vec<LayerHandle>> {
        let mut handles = Vec::new();
        for name in ["a.usda", "b.usda"] {
            let path = dir.join(name);
            fs::write(&path, initial)?;
            handles.push(registry.find_or_open(&path.to_string_lossy())?.expect("resolves"));
            sdf::layer::tests::append(&path, appended)?;
        }
        Ok(handles)
    }

    /// A guard lends its one layer: the registry still adds layers and edits
    /// the others, while an edit of the borrowed layer is `Busy`, stages
    /// nothing, and runs none of its sinks.
    #[test]
    fn guard_lends_one_layer() {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with_prim("a.usda")).unwrap();
        let b = registry.adopt(layer_with_prim("b.usda")).unwrap();
        let heard = Rc::new(Cell::new(0));
        let count = Rc::clone(&heard);
        a.add_sink(move |_: &str, _: &sdf::ChangeList| count.set(count.get() + 1))
            .unwrap();

        let guard = a.try_borrow().unwrap();
        let c = registry.adopt(layer_with_prim("c.usda"));
        assert!(c.is_ok(), "a layer joins while another is borrowed");
        assert!(document(&b, "b").unwrap());
        assert!(matches!(document(&a, "a"), Err(LayerError::Busy)));
        assert!(guard.prim("/P").unwrap().is_some(), "the guard reads its layer");
        drop(guard);

        assert_eq!(documentation(&a), None, "the refused edit staged nothing");
        assert_eq!(heard.get(), 0, "the refused edit ran no sink");
        assert!(document(&a, "a").unwrap(), "the edit lands once the guard drops");
        assert_eq!(heard.get(), 1);
    }

    /// An edit naming a borrowed layer fails as a whole wherever the layer
    /// sits in the batch: the other layers keep their content, and none of
    /// their subscribers is prepared.
    #[test]
    fn guard_fails_whole_batch() {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with_prim("a.usda")).unwrap();
        let b = registry.adopt(layer_with_prim("b.usda")).unwrap();
        let seen: Seen = Rc::default();
        let _subscription = b.subscribe(Rc::new(Footprints(Rc::clone(&seen)))).unwrap();
        let guard = a.borrow();

        for batch in [[&a, &b], [&b, &a]] {
            let edited = a.store.edit(&batch, TxnContext::new(None), |edits| {
                for edit in edits.iter_mut() {
                    let path = sdf::path("/P").unwrap();
                    edit.data_mut()
                        .set_field(&path, "documentation", vt::Value::String("batch".into()));
                }
                Ok::<_, LayerError>(())
            });
            assert!(matches!(edited, Err(LayerError::Busy)), "{edited:?}");
        }
        drop(guard);
        assert_eq!(documentation(&b), None, "the other layer is unchanged");
        assert!(seen.borrow().is_empty(), "no subscriber was prepared");
    }

    /// A guard keeps its layer open after the layer's last handle drops. The
    /// layer is freed at the first sweep after the guard drops, and not while a
    /// hold lasts.
    #[test]
    fn guard_keeps_layer_open() {
        let registry = sdf::LayerRegistry::default();
        let mut layer = layer_with_prim("freed.usda");
        let marker = Rc::new(());
        let held = Rc::clone(&marker);
        layer.add_sink(move |_: &str, _: &sdf::ChangeList| {
            let _ = &held;
        });
        let identifier = layer.identifier().to_owned();
        let handle = registry.adopt(layer).unwrap();
        let guard = handle.borrow();

        drop(handle);
        registry.sweep();
        assert_eq!(Rc::strong_count(&marker), 2, "the guard keeps the layer");
        assert!(registry.find(&identifier).unwrap().is_some(), "and its slot");

        let store = registry.store();
        let hold = store.hold();
        drop(guard);
        registry.sweep();
        assert_eq!(Rc::strong_count(&marker), 2, "the hold defers the free");
        drop(hold);
        assert_eq!(Rc::strong_count(&marker), 1, "the hold's release frees the layer");
        assert_eq!(registry.find(&identifier).unwrap(), None);
    }

    /// Inside an edit, borrowing any layer of the registry is `Busy`: the
    /// edited one and an unrelated one alike.
    #[test]
    fn borrow_inside_edit_busy() {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with_prim("a.usda")).unwrap();
        let b = registry.adopt(layer_with_prim("b.usda")).unwrap();
        let mut inner = Vec::new();
        a.edit(|_| {
            inner.push(a.try_borrow().map(drop));
            inner.push(b.try_borrow().map(drop));
            Ok(())
        })
        .unwrap();
        assert!(
            inner.iter().all(|result| matches!(result, Err(LayerError::Busy))),
            "{inner:?}"
        );
    }

    /// Saving a borrowed layer, or changing its sinks, is `Busy`.
    #[test]
    fn guard_blocks_save() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("saved.usda");
        fs::write(&path, "#usda 1.0\n\ndef \"P\"\n{\n}\n")?;
        let registry = sdf::LayerRegistry::default();
        let handle = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        document(&handle, "unsaved")?;

        let guard = handle.borrow();
        assert!(matches!(handle.save(), Err(LayerError::Busy)));
        let added = handle.add_sink(|_: &str, _: &sdf::ChangeList| {});
        assert!(matches!(added, Err(LayerError::Busy)));
        drop(guard);
        handle.save()?;
        assert!(fs::read_to_string(&path)?.contains("unsaved"));
        Ok(())
    }

    /// A subscription joins and leaves a borrowed layer. A layer with a
    /// subscriber and no sink still hands each commit's record on.
    #[test]
    fn subscribe_while_borrowed() {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with_prim("a.usda")).unwrap();
        let seen: Seen = Rc::default();
        let gone: Seen = Rc::default();

        let guard = a.borrow();
        let _subscription = a.subscribe(Rc::new(Footprints(Rc::clone(&seen)))).unwrap();
        let ended = a.subscribe(Rc::new(Footprints(Rc::clone(&gone)))).unwrap();
        drop(ended);
        drop(guard);

        document(&a, "seen").unwrap();
        assert_eq!(seen.borrow().len(), 1, "the subscriber had the record");
        assert!(gone.borrow().is_empty(), "the ended subscription had nothing");
    }

    /// A batch reload naming a borrowed layer fails before any file is read,
    /// and reloads none of the layers.
    #[test]
    fn reload_borrowed_busy() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let (registry, opens) = counting_registry();
        let handles = stale_pair(&registry, dir.path(), "#usda 1.0\n", "def \"P\" {}\n")?;
        let opened = opens.get();

        let guard = handles[1].borrow();
        let reloaded = LayerHandle::reload_all(&handles, false);
        assert!(
            matches!(reloaded, Err(crate::Error::Layer(LayerError::Busy))),
            "{reloaded:?}"
        );
        assert_eq!(opens.get(), opened, "no file was read");
        drop(guard);
        assert!(handles[0].borrow().prim("/P")?.is_none(), "nothing was reloaded");
        Ok(())
    }

    /// A borrowed layer whose file is unchanged does not stop a batch reload:
    /// it is left as it is, and the batch's other layers reload.
    #[test]
    fn reload_skips_borrowed_unchanged() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let registry = sdf::LayerRegistry::default();
        let handles = stale_pair(&registry, dir.path(), "#usda 1.0\n", "def \"P\" {}\n")?;
        let unchanged = dir.path().join("c.usda");
        fs::write(&unchanged, "#usda 1.0\n")?;
        let c = registry.find_or_open(&unchanged.to_string_lossy())?.expect("resolves");

        let guard = c.borrow();
        assert!(LayerHandle::reload_all(
            &[handles[0].clone(), c.clone(), handles[1].clone()],
            false
        )?);
        drop(guard);
        for handle in &handles {
            assert!(
                handle.borrow().prim("/P")?.is_some(),
                "{} reloaded",
                handle.identifier()
            );
        }
        Ok(())
    }

    /// A batch whose layers fail at different checks reports the failure of
    /// the layer it names first: a parse error found reading the first layer
    /// beats the second layer's failure to resolve.
    #[test]
    fn reload_first_failure() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let registry = sdf::LayerRegistry::default();
        let handles = stale_pair(
            &registry,
            dir.path(),
            "#usda 1.0
",
            "def \"P\" {}
",
        )?;
        sdf::layer::tests::rewrite(
            &dir.path().join("a.usda"),
            "#usda 1.0
def (
",
        )?;
        fs::remove_file(dir.path().join("b.usda"))?;

        let reloaded = LayerHandle::reload_all(&handles, false);
        assert!(reloaded.is_err(), "{reloaded:?}");
        assert!(
            !matches!(reloaded, Err(crate::Error::UnresolvedAsset(_))),
            "{reloaded:?}"
        );
        Ok(())
    }

    /// A batch reload keeps every edit of the registry out while it reads the
    /// files: an edit a resolver tries while reading one target is `Busy`, and
    /// another target reloads to its file as it was computed.
    #[test]
    fn reload_refuses_resolver_edit() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let target: HandleCell = Rc::default();
        let armed = Rc::new(Cell::new(false));
        let tried = Rc::new(RefCell::new(None));
        let resolver = {
            let (target, armed, tried) = (Rc::clone(&target), Rc::clone(&armed), Rc::clone(&tried));
            HookResolver::new(move |resolved| {
                let reading_b = resolved.to_str().is_some_and(|path| path.ends_with("b.usda"));
                if armed.get() && reading_b {
                    let a = target.borrow().clone().expect("the target is set");
                    tried.replace(Some(document(&a, "from the resolver")));
                }
            })
        };
        let registry = sdf::LayerRegistry::new(Box::new(resolver));
        let handles = stale_pair(&registry, dir.path(), "#usda 1.0\ndef \"P\" {}\n", "def \"Q\" {}\n")?;
        target.replace(Some(handles[0].clone()));

        armed.set(true);
        assert!(LayerHandle::reload_all(&handles, false)?);
        let tried = tried.take().expect("the resolver ran");
        assert!(matches!(tried, Err(LayerError::Busy)), "{tried:?}");
        assert!(handles[0].borrow().prim("/Q")?.is_some(), "a reloaded");
        assert_eq!(documentation(&handles[0]), None, "a matches its file");
        target.take();
        Ok(())
    }

    /// Ends a test's hook-held handle with an edit of another layer when it
    /// drops, as a sink's destructor running user code would.
    struct EditOnDrop(HandleCell);

    impl Drop for EditOnDrop {
        fn drop(&mut self) {
            if let Some(handle) = self.0.take() {
                document(&handle, "from a drop").unwrap();
            }
        }
    }

    /// A layer whose last handle drops while a batch reload reads its files is
    /// freed only once the reload has committed and delivered: a drop that
    /// edits a target then lands after the reload, as its own transaction.
    #[test]
    fn reload_defers_freeing() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let doomed: HandleCell = Rc::default();
        let armed = Rc::new(Cell::new(false));
        let resolver = {
            let (doomed, armed) = (Rc::clone(&doomed), Rc::clone(&armed));
            HookResolver::new(move |resolved| {
                if armed.get() && resolved.to_str().is_some_and(|path| path.ends_with("b.usda")) {
                    doomed.take();
                }
            })
        };
        let registry = sdf::LayerRegistry::new(Box::new(resolver));
        let handles = stale_pair(&registry, dir.path(), "#usda 1.0\ndef \"P\" {}\n", "def \"Q\" {}\n")?;
        let log: Log = Rc::default();
        let record = Rc::clone(&log);
        handles[0]
            .add_sink(move |_: &str, changes: &sdf::ChangeList| {
                let kind = if changes.did_reload_content() { "reload" } else { "edit" };
                record.borrow_mut().push(kind.to_owned());
            })
            .unwrap();
        // C's only sink edits A when it drops, which is when C is freed.
        let mut c = layer_with_prim("c.usda");
        let on_drop = EditOnDrop(Rc::new(RefCell::new(Some(handles[0].clone()))));
        c.add_sink(move |_: &str, _: &sdf::ChangeList| {
            let _ = &on_drop;
        });
        doomed.replace(Some(registry.adopt(c).unwrap()));

        armed.set(true);
        assert!(LayerHandle::reload_all(&handles, false)?);
        assert!(doomed.borrow().is_none(), "the resolver dropped c's handle");
        assert_eq!(*log.borrow(), ["reload", "edit"], "the drop's edit follows the reload");
        assert!(handles[0].borrow().prim("/Q")?.is_some(), "a reloaded");
        assert_eq!(documentation(&handles[0]).as_deref(), Some("from a drop"));
        Ok(())
    }
}
