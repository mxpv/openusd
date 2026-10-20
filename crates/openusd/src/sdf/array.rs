//! Numeric arrays with owned or shared immutable storage.

use std::fmt;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::slice;
use std::sync::Arc;
use std::vec;

use bytemuck::{Pod, try_cast_slice};

use crate::ar;

/// A numeric array with copy-on-write storage (C++ `VtArray`).
///
/// Clones share their elements. Mutation copies storage shared with another
/// array or backed by immutable bytes. A uniquely owned vector moves out
/// without copying. Arrays retain their bytes independently of their layer.
#[derive(Clone)]
pub struct Array<T: Pod> {
    storage: Option<Arc<Storage<T>>>,
}

#[derive(Clone)]
enum Storage<T: Pod> {
    Owned(Vec<T>),
    Shared(View<T>),
}

#[derive(Clone)]
struct View<T: Pod> {
    bytes: ar::SharedBuffer,
    element: PhantomData<T>,
}

impl<T: Pod> Array<T> {
    /// An empty owned array.
    pub fn new() -> Self {
        Self::default()
    }

    /// Shares `bytes` when their length and alignment admit whole `T` elements.
    /// The bytes must use the host's element representation.
    pub fn from_shared(bytes: ar::SharedBuffer) -> Option<Self> {
        try_cast_slice::<u8, T>(&bytes).ok()?;
        if bytes.is_empty() {
            return Some(Self::new());
        }
        Some(Self {
            storage: Some(Arc::new(Storage::Shared(View {
                bytes,
                element: PhantomData,
            }))),
        })
    }

    /// Whether the elements borrow shared backing bytes.
    pub fn is_shared(&self) -> bool {
        matches!(self.storage.as_deref(), Some(Storage::Shared(_)))
    }

    /// Moves out a unique owned vector, copying shared elements when necessary.
    pub fn into_vec(self) -> Vec<T> {
        match self.storage.map(Arc::unwrap_or_clone) {
            None => Vec::new(),
            Some(Storage::Owned(values)) => values,
            Some(Storage::Shared(view)) => view.elements().to_vec(),
        }
    }

    /// Borrows all elements.
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Mutably borrows all elements, copying shared storage first.
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.make_mut()
    }

    /// Obtains the owned vector, copying shared storage first.
    pub fn make_mut(&mut self) -> &mut Vec<T> {
        let storage = Arc::make_mut(self.storage.get_or_insert_with(|| Arc::new(Storage::Owned(Vec::new()))));
        if let Storage::Shared(view) = storage {
            *storage = Storage::Owned(view.elements().to_vec());
        }
        let Storage::Owned(values) = storage else {
            unreachable!()
        };
        values
    }
}

impl<T: Pod> View<T> {
    fn elements(&self) -> &[T] {
        try_cast_slice(&self.bytes).expect("shared array validated at construction")
    }
}

impl<T: Pod> Default for Array<T> {
    fn default() -> Self {
        Self { storage: None }
    }
}

impl<T: Pod> From<Vec<T>> for Array<T> {
    fn from(values: Vec<T>) -> Self {
        Self {
            storage: (!values.is_empty()).then(|| Arc::new(Storage::Owned(values))),
        }
    }
}

impl<T: Pod> From<Array<T>> for Vec<T> {
    fn from(values: Array<T>) -> Self {
        values.into_vec()
    }
}

impl<T: Pod> FromIterator<T> for Array<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Vec::from_iter(iter).into()
    }
}

impl<T: Pod> Deref for Array<T> {
    type Target = [T];
    fn deref(&self) -> &[T] {
        match self.storage.as_deref() {
            None => &[],
            Some(Storage::Owned(values)) => values,
            Some(Storage::Shared(view)) => view.elements(),
        }
    }
}

impl<T: Pod> DerefMut for Array<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.make_mut()
    }
}

impl<T: Pod> AsRef<[T]> for Array<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T: Pod + fmt::Debug> fmt::Debug for Array<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_slice().fmt(f)
    }
}

impl<T: Pod + PartialEq> PartialEq for Array<T> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Pod + Eq> Eq for Array<T> {}

impl<T: Pod + PartialEq, const N: usize> PartialEq<[T; N]> for Array<T> {
    fn eq(&self, other: &[T; N]) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Pod + PartialEq> PartialEq<Vec<T>> for Array<T> {
    fn eq(&self, other: &Vec<T>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Pod + PartialEq> PartialEq<Array<T>> for Vec<T> {
    fn eq(&self, other: &Array<T>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T: Pod> IntoIterator for Array<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.into_vec().into_iter()
    }
}

impl<'a, T: Pod> IntoIterator for &'a Array<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T: Pod> IntoIterator for &'a mut Array<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

#[cfg(feature = "serde")]
impl<T: Pod + serde::Serialize> serde::Serialize for Array<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_slice().serialize(serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn owned_clone_detaches() {
        let values = vec![1u32, 2, 3];
        let pointer = values.as_ptr();
        let original = Array::from(values);
        let mut clone = original.clone();
        assert_eq!(original.as_ptr(), pointer);
        assert_eq!(clone.as_ptr(), pointer);
        clone[1] = 20;
        assert_ne!(clone.as_ptr(), pointer);
        assert_eq!(original.as_slice(), &[1, 2, 3]);
        assert_eq!(clone.as_slice(), &[1, 20, 3]);
        let values = original.into_vec();
        assert_eq!(values.as_ptr(), pointer);
    }

    #[test]
    fn shared_clone_detaches() {
        let bytes = ar::SharedBuffer::new(vec![1u8, 2, 3, 4]);
        let pointer = bytes.as_ptr();
        let original = Array::<u8>::from_shared(bytes).unwrap();
        let mut clone = original.clone();
        assert!(original.is_shared());
        assert_eq!(original.as_ptr(), pointer);
        assert_eq!(clone.as_ptr(), pointer);
        clone.make_mut().push(5);
        assert!(!clone.is_shared());
        assert_eq!(clone.as_slice(), &[1, 2, 3, 4, 5]);
        assert_eq!(original.as_slice(), &[1, 2, 3, 4]);
        drop(original);
        assert_eq!(clone.into_vec(), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn shared_alignment_checked() {
        static WORDS: [u32; 2] = [1, 2];
        let bytes = ar::SharedBuffer::new(bytemuck::cast_slice(&WORDS));
        assert!(Array::<u32>::from_shared(bytes.clone()).is_some());
        assert!(Array::<u32>::from_shared(bytes.slice(1..5).unwrap()).is_none());
        assert!(Array::<u32>::from_shared(bytes.slice(0..3).unwrap()).is_none());
        assert!(
            Array::<u32>::from_shared(bytes.slice(0..0).unwrap())
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn owned_extraction_detaches() {
        let original = Array::from(vec![1i32, 2, 3]);
        let mut values = original.clone().into_vec();
        values[0] = 10;
        assert_eq!(original.as_slice(), &[1, 2, 3]);
        let mut empty = Array::<i32>::new();
        empty.make_mut().push(5);
        assert_eq!(empty.as_slice(), &[5]);
    }
}
