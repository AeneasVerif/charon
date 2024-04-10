//! A vector with custom index types.
//!
//! This data-structure is mostly meant to be used with the index types defined
//! with [ids::generate_index_type]: by using custom index types, we
//! leverage the type checker to prevent us from mixing them.
//!
//! Note that this data structure is implemented by using persistent vectors.
//! This makes the clone operation almost a no-op.

use index_vec::{Idx, IdxSliceIndex, IndexVec};
use serde::{Serialize, Serializer};
use std::{
    iter::{FromIterator, IntoIterator},
    ops::{Index, IndexMut},
};

/// Indexed vector
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Vector<I, T>
where
    I: Idx,
{
    vector: IndexVec<I, T>,
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

    pub fn is_empty(&self) -> bool {
        self.vector.is_empty()
    }

    pub fn len(&self) -> usize {
        self.vector.len()
    }

    pub fn next_id(&self) -> I {
        self.vector.next_idx()
    }

    pub fn push(&mut self, x: T) -> I {
        self.vector.push(x)
    }

    pub fn push_with(&mut self, f: impl FnOnce(I) -> T) -> I {
        self.push(f(self.next_id()))
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

impl<I: Idx, T> Default for Vector<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I, R, T> Index<R> for Vector<I, T>
where
    I: Idx,
    R: IdxSliceIndex<I, T>,
{
    type Output = R::Output;
    fn index(&self, index: R) -> &Self::Output {
        &self.vector[index]
    }
}

impl<I, R, T> IndexMut<R> for Vector<I, T>
where
    I: Idx,
    R: IdxSliceIndex<I, T>,
{
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        &mut self.vector[index]
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
