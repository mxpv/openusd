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

use std::cell::{BorrowMutError, RefCell, RefMut};
use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::ptr;
use std::rc::{Rc, Weak};

use super::commit::{Dispatch, Subscriber, TxnContext};
use super::{AuthoringError, EditError, Layer, LayerEdit, edit_layers, sink};

/// A failure to read, edit or add a layer of a
/// [`LayerRegistry`](super::LayerRegistry).
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum LayerError {
    /// The registry was already borrowed — the access was made from inside a
    /// read or an edit on the same registry — so nothing was read or staged.
    #[error("the layer registry is in use by another read or edit")]
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

    /// The edit itself failed; nothing was committed.
    #[error(transparent)]
    Edit(#[from] EditError),
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
    /// The layers, borrowed whole by every read and edit.
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
}

/// One arena slot: the epoch it is in, and its layer while it is filled.
#[derive(Default)]
struct Slot {
    /// Advanced each time the slot is freed.
    epoch: u32,
    /// The layer, with the token every handle to it shares.
    entry: Option<(Layer, Weak<SlotToken>)>,
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
/// A registry's layers are borrowed whole, not one at a time: a
/// [`read`](Self::read) shares them and an [`edit`](Self::edit) takes them
/// mutably. A nested access therefore conflicts even across two different
/// layers — `a.read(|_| b.edit(..))` — and every borrow is fallible: a read or
/// an edit that meets a held borrow is [`LayerError::Busy`], having read or
/// staged nothing. User code runs under a borrow only in the closure given to
/// `read` or `edit` and in a sink's
/// [`before_commit`](super::LayerSink::before_commit); an
/// [`after_commit`](super::LayerSink::after_commit) runs once the borrow is
/// released.
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

    /// Run `f` on the layer. The closure runs with the registry shared: it can
    /// read through other handles but not edit through any. Fails with
    /// [`LayerError::Busy`] when called from inside an edit on the same
    /// registry.
    pub fn read<R>(&self, f: impl FnOnce(&Layer) -> R) -> Result<R, LayerError> {
        let slots = self.store.slots.try_borrow().map_err(|_| LayerError::Busy)?;
        let layer = slots.get(self.token.key).expect("a handle keeps its slot filled");
        Ok(f(layer))
    }

    /// Author a batch of edits on the layer as one atomic transaction (see
    /// [`Layer::edit`]), visible through every handle to it. Returns whether
    /// the edit produced a composition change.
    ///
    /// The closure runs with the registry borrowed: it cannot read or edit
    /// through another handle of the same registry. An edit made from inside
    /// a read or another edit on the registry fails with
    /// [`LayerError::Busy`], having staged nothing. The edit is attributed to
    /// no stage: a stage holding the layer sees it as an edit made elsewhere.
    /// The layer's sinks see it in commit order, after the edits committed
    /// before it.
    pub fn edit(&self, f: impl FnOnce(&mut LayerEdit<'_>) -> Result<(), AuthoringError>) -> Result<bool, LayerError> {
        self.store.edit(&[self], TxnContext::new(None), |edits| {
            f(&mut edits[0]).map_err(LayerError::from)
        })
    }

    /// Subscribe `subscriber` to the layer's commits, until the returned
    /// [`Subscription`] drops.
    #[cfg_attr(not(test), expect(dead_code, reason = "only the tests subscribe"))]
    pub(crate) fn subscribe(&self, subscriber: Rc<dyn Subscriber>) -> Result<Subscription, LayerError> {
        let mut slots = self.store.slots_mut().map_err(|_| LayerError::Busy)?;
        let layer = slots.get_mut(self.token.key).expect("a handle keeps its slot filled");
        Ok(Subscription {
            store: Rc::downgrade(&self.store),
            key: self.token.key,
            id: layer.subscribe(subscriber),
        })
    }
}

/// Two handles are equal when they share one layer.
impl PartialEq for LayerHandle {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.token, &other.token)
    }
}

impl Eq for LayerHandle {}

impl fmt::Debug for LayerHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("LayerHandle").field(&self.token.identifier).finish()
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
                if let Some(layer) = slots.get_mut(self.key) {
                    layer.unsubscribe(self.id);
                }
            }
            Err(_) => store.unsubscribed.borrow_mut().push((self.key, self.id)),
        }
    }
}

impl LayerStore {
    /// A handle to the live layer whose identifier is `identifier`, or, with
    /// `real_path`, the one read from that location.
    pub(crate) fn find(
        self: &Rc<Self>,
        identifier: &str,
        real_path: Option<&str>,
    ) -> Result<Option<LayerHandle>, LayerError> {
        let slots = self.slots.try_borrow().map_err(|_| LayerError::Busy)?;
        let live = |index: Option<&u32>| index.and_then(|&index| self.live(&slots, index));
        Ok(live(slots.by_identifier.get(identifier)).or_else(|| live(slots.by_real_path.get(real_path?))))
    }

    /// Hold `layer`, committing any edit it has staged without notifying its
    /// sinks, and return a handle to it. Fails, handing the layer back, with
    /// [`LayerError::Busy`] while the store is borrowed and with
    /// [`LayerError::Duplicate`] when a live layer already carries its
    /// identifier or, for a layer read from an asset, its real path.
    pub(crate) fn insert(self: &Rc<Self>, mut layer: Layer) -> Result<LayerHandle, AdoptError> {
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
            store: Rc::downgrade(self),
        });
        slot.entry = Some((layer, Rc::downgrade(&token)));
        slots.by_identifier.insert(token.identifier.clone(), index);
        if let Some(real_path) = real_path {
            slots.by_real_path.insert(real_path, index);
        }
        Ok(LayerHandle {
            token,
            store: Rc::clone(self),
        })
    }

    /// Fails with [`LayerError::Busy`] while a read or an edit holds the store,
    /// so a caller about to add a layer can tell before doing the work of
    /// reading it.
    pub(crate) fn ensure_writable(&self) -> Result<(), LayerError> {
        self.slots.try_borrow_mut().map(drop).map_err(|_| LayerError::Busy)
    }

    /// Free every slot whose last handle has dropped, and apply the
    /// subscriptions that ended while the store was borrowed. A no-op while
    /// the store is borrowed; the next sweep frees what this one skipped.
    pub(crate) fn sweep(&self) {
        let Ok(mut slots) = self.slots_mut() else {
            return;
        };
        let dead = mem::take(&mut *self.dead.borrow_mut());
        // The freed layers drop once the borrow is released, so nothing their
        // drop reaches finds the store borrowed.
        let freed: Vec<Layer> = dead.into_iter().filter_map(|key| slots.free_slot(key)).collect();
        drop(slots);
        drop(freed);
    }

    /// Run `f` over the layers `handles` name, in order, as one atomic
    /// transaction `txn`, then deliver the sinks' notifications through the
    /// registry's queue. Fails, having staged nothing, with
    /// [`LayerError::Busy`] when the store is already borrowed, and with
    /// [`LayerError::Foreign`] or [`LayerError::Repeated`] for a handle of
    /// another registry or one named twice.
    pub(crate) fn edit<E: From<sink::Error> + From<LayerError>>(
        &self,
        handles: &[&LayerHandle],
        txn: TxnContext,
        f: impl FnOnce(&mut [LayerEdit<'_>]) -> Result<(), E>,
    ) -> Result<bool, E> {
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
        let committed = {
            let mut slots = self.slots_mut().map_err(|_| LayerError::Busy)?;
            let keys: Vec<SlotKey> = handles.iter().map(|handle| handle.token.key).collect();
            let mut layers = slots.layers_mut(&keys);
            edit_layers(&mut layers, txn, f)?
        };
        Ok(committed.dispatch_via(&self.dispatch))
    }

    /// Borrow the slots mutably, first applying the subscriptions that ended
    /// while they were borrowed.
    fn slots_mut(&self) -> Result<RefMut<'_, Slots>, BorrowMutError> {
        let mut slots = self.slots.try_borrow_mut()?;
        for (key, id) in mem::take(&mut *self.unsubscribed.borrow_mut()) {
            if let Some(layer) = slots.get_mut(key) {
                layer.unsubscribe(id);
            }
        }
        Ok(slots)
    }

    /// A handle to the slot at `index`, while a handle still holds it.
    fn live(self: &Rc<Self>, slots: &Slots, index: u32) -> Option<LayerHandle> {
        let (_, token) = slots.slots[index as usize].entry.as_ref()?;
        Some(LayerHandle {
            token: token.upgrade()?,
            store: Rc::clone(self),
        })
    }
}

impl Slots {
    /// The layer in the slot `key` names, while it holds the filling `key`
    /// came from.
    fn get(&self, key: SlotKey) -> Option<&Layer> {
        let slot = self
            .slots
            .get(key.index as usize)
            .filter(|slot| slot.epoch == key.epoch)?;
        slot.entry.as_ref().map(|(layer, _)| layer)
    }

    /// [`get`](Self::get), mutably.
    fn get_mut(&mut self, key: SlotKey) -> Option<&mut Layer> {
        let slot = self
            .slots
            .get_mut(key.index as usize)
            .filter(|slot| slot.epoch == key.epoch)?;
        slot.entry.as_mut().map(|(layer, _)| layer)
    }

    /// The layers `keys` name, in `keys` order: distinct live slots, as every
    /// handle's key is.
    fn layers_mut(&mut self, keys: &[SlotKey]) -> Vec<&mut Layer> {
        if let [key] = keys {
            return self.get_mut(*key).into_iter().collect();
        }
        let position: HashMap<u32, usize> = keys.iter().enumerate().map(|(at, key)| (key.index, at)).collect();
        let mut layers: Vec<(usize, &mut Layer)> = self
            .slots
            .iter_mut()
            .enumerate()
            .filter_map(|(index, slot)| {
                let at = *position.get(&u32::try_from(index).ok()?)?;
                (slot.epoch == keys[at].epoch).then_some(())?;
                slot.entry.as_mut().map(|(layer, _)| (at, layer))
            })
            .collect();
        layers.sort_by_key(|&(at, _)| at);
        layers.into_iter().map(|(_, layer)| layer).collect()
    }

    /// Free the slot `key` names when no handle holds it, returning its layer
    /// for the caller to drop.
    fn free_slot(&mut self, key: SlotKey) -> Option<Layer> {
        let slot = self
            .slots
            .get_mut(key.index as usize)
            .filter(|slot| slot.epoch == key.epoch)?;
        if slot.entry.as_ref().is_some_and(|(_, token)| token.strong_count() > 0) {
            return None;
        }
        let (layer, _) = slot.entry.take()?;
        slot.epoch = slot.epoch.wrapping_add(1);
        self.free.push(key.index);
        let unindex = |map: &mut HashMap<String, u32>, name: &str| {
            if map.get(name) == Some(&key.index) {
                map.remove(name);
            }
        };
        unindex(&mut self.by_identifier, layer.identifier());
        unindex(&mut self.by_real_path, layer.real_path());
        Some(layer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sdf::commit::{CommitRecord, EditorId, Footprint, PendingCommit, Prepared, TxnId};
    use crate::{ar, sdf, vt};

    use std::cell::Cell;
    use std::fs;
    use std::io;
    use std::panic::{AssertUnwindSafe, catch_unwind};

    /// The footprint and origin of each commit a [`Footprints`] subscriber saw.
    type Seen = Rc<RefCell<Vec<(Footprint, Option<EditorId>)>>>;

    /// What a test observer saw, in order.
    type Log = Rc<RefCell<Vec<String>>>;

    /// A filesystem resolver that counts the assets it opens.
    struct Counting {
        inner: ar::DefaultResolver,
        opens: Rc<Cell<usize>>,
    }

    impl ar::Resolver for Counting {
        fn create_identifier(&self, asset_path: &str, anchor: Option<&ar::ResolvedPath>) -> String {
            self.inner.create_identifier(asset_path, anchor)
        }

        fn resolve(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
            self.inner.resolve(asset_path)
        }

        fn resolve_for_new_asset(&self, asset_path: &str) -> Option<ar::ResolvedPath> {
            self.inner.resolve_for_new_asset(asset_path)
        }

        fn open_asset(&self, resolved_path: &ar::ResolvedPath) -> io::Result<Box<dyn ar::Asset>> {
            self.opens.set(self.opens.get() + 1);
            self.inner.open_asset(resolved_path)
        }
    }

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
        fn commit(mut self: Box<Self>, record: &CommitRecord) {
            assert_eq!(record.txn, self.txn, "committed with its own transaction's record");
            self.log.borrow_mut().push(format!("commit {}", self.before));
            self.committed = true;
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
        fn commit(self: Box<Self>, record: &CommitRecord) {
            self.0.borrow_mut().push((record.footprint.clone(), record.origin));
        }
    }

    /// A sink that vetoes every edit.
    struct Veto;

    impl sdf::LayerSink for Veto {
        fn before_commit(&self, _change: &sdf::PendingLayerChange<'_>) -> Result<(), sink::Error> {
            Err(sink::Error::new("vetoed"))
        }
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
        handle
            .read(|layer| {
                let value = layer
                    .data()
                    .try_field(&sdf::path("/P").unwrap(), "documentation")
                    .unwrap()?;
                Some(value.try_as_string_ref().unwrap().clone())
            })
            .unwrap()
    }

    /// Opening a file twice through one registry reads it once and hands out
    /// one shared layer: an edit through either handle is seen through both.
    #[test]
    fn find_or_open_shares() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("shared.usda");
        fs::write(&path, "#usda 1.0\n\ndef Xform \"P\"\n{\n}\n")?;
        let opens = Rc::new(Cell::new(0));
        let registry = sdf::LayerRegistry::new(Box::new(Counting {
            inner: ar::DefaultResolver::new(),
            opens: Rc::clone(&opens),
        }));

        let first = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        let second = registry.find_or_open(&path.to_string_lossy())?.expect("resolves");
        assert_eq!(opens.get(), 1, "the second open finds the first");
        assert_eq!(first, second);
        assert_eq!(registry.find(&path.to_string_lossy())?, Some(first.clone()));

        document(&first, "shared")?;
        assert_eq!(documentation(&second).as_deref(), Some("shared"));
        Ok(())
    }

    /// Opening a layer from inside a read fails with `Busy` before reading
    /// the file.
    #[test]
    fn open_inside_read_busy() -> crate::Result<()> {
        let dir = tempfile::tempdir()?;
        let path = dir.path().join("later.usda");
        fs::write(&path, "#usda 1.0\n")?;
        let opens = Rc::new(Cell::new(0));
        let registry = sdf::LayerRegistry::new(Box::new(Counting {
            inner: ar::DefaultResolver::new(),
            opens: Rc::clone(&opens),
        }));
        let held = registry.adopt(layer_with_prim("held.usda")).unwrap();

        let inner = held.read(|_| registry.find_or_open(&path.to_string_lossy()))?;
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
        assert!(new.store.slots.borrow_mut().get_mut(old_key).is_none());

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

    /// A nested access is refused with `Busy` either way round, never a panic,
    /// and leaves the outer access to finish.
    #[test]
    fn nested_access_busy() {
        let registry = sdf::LayerRegistry::default();
        let a = registry.adopt(layer_with_prim("a.usda")).unwrap();
        let b = registry.adopt(layer_with_prim("b.usda")).unwrap();

        let inner = a.read(|_| document(&b, "inside a read")).unwrap();
        assert!(matches!(inner, Err(LayerError::Busy)));
        assert_eq!(documentation(&b), None, "the refused edit staged nothing");

        let clone = a.clone();
        let mut inner = None;
        a.edit(|edit| {
            inner = Some(clone.read(|_| ()));
            let path = sdf::path("/P")?;
            edit.data_mut()
                .set_field(&path, "documentation", vt::Value::String("outer".into()));
            Ok(())
        })
        .unwrap();
        assert!(matches!(inner, Some(Err(LayerError::Busy))));
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
        let echo: Rc<RefCell<Option<LayerHandle>>> = Rc::default();
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

        handle.read(move |_| drop(subscription)).unwrap();
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
}
