//! A vector with custom index types.
//!
//! This data-structure is mostly meant to be used with the index types defined
//! with [ids::generate_index_type]: by using custom index types, we
//! leverage the type checker to prevent us from mixing them.
//!
//! Note that this data structure is implemented by using persistent vectors.
//! This makes the clone operation almost a no-op.

use index_vec::{Idx, IndexVec};
use serde::{Serialize, Serializer};
use std::iter::{FromIterator, IntoIterator};

pub use std::collections::hash_map::Iter as IterAll;
pub use std::collections::hash_map::IterMut as IterAllMut;

/// Indexed vector
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Vector<I, T>
where
    I: Idx,
{
    pub vector: IndexVec<I, T>,
}

impl<I, T> Vector<I, T>
where
    I: Idx,
{
    pub fn new() -> Self {
        Vector {
            vector: IndexVec::new(),
        }
    }

    pub fn get(&self, i: I) -> Option<&T> {
        self.vector.get(i)
    }

    pub fn insert(&mut self, i: I, x: T) {
        self.vector.insert(i, x);
    }

    pub fn is_empty(&self) -> bool {
        self.vector.is_empty()
    }

    pub fn len(&self) -> usize {
        self.vector.len()
    }

    pub fn push_back(&mut self, x: T) {
        self.vector.push(x);
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.vector.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.vector.iter_mut()
    }

    pub fn iter_indexed_values(&self) -> impl Iterator<Item = (I, &T)> {
        self.vector.iter_enumerated()
    }

    pub fn iter_indices(&self) -> impl Iterator<Item = I> {
        self.vector.indices()
    }
}

impl<I: Idx, T: Clone> Default for Vector<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, I, T> IntoIterator for &'a Vector<I, T>
where
    I: Idx,
{
    type Item = &'a T;
    type IntoIter = <&'a IndexVec<I, T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> <&'a IndexVec<I, T> as IntoIterator>::IntoIter {
        (&self.vector).into_iter()
    }
}

impl<I, T> IntoIterator for Vector<I, T>
where
    I: Idx,
{
    type Item = T;
    type IntoIter = <IndexVec<I, T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> <IndexVec<I, T> as IntoIterator>::IntoIter {
        self.vector.into_iter()
    }
}

impl<I, T> FromIterator<T> for Vector<I, T>
where
    I: Idx,
{
    #[inline]
    fn from_iter<It: IntoIterator<Item = T>>(iter: It) -> Vector<I, T> {
        Vector {
            vector: IndexVec::from_iter(iter),
        }
    }
}

impl<I, T> From<Vec<T>> for Vector<I, T>
where
    I: Idx,
{
    fn from(v: Vec<T>) -> Self {
        Vector {
            vector: IndexVec::from(v),
        }
    }
}

impl<I: Idx, T: Serialize> Serialize for Vector<I, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.vector.serialize(serializer)
    }
}
