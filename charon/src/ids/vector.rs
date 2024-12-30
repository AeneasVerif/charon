//! A vector with custom index types.
//!
//! This data-structure is mostly meant to be used with the index types defined
//! with [ids::generate_index_type]: by using custom index types, we
//! leverage the type checker to prevent us from mixing them.
//!
//! Note that this data structure is implemented by using persistent vectors.
//! This makes the clone operation almost a no-op.

use index_vec::{Idx, IdxSliceIndex, IndexVec};
use serde::{Deserialize, Serialize, Serializer};
use std::{
    iter::{FromIterator, IntoIterator},
    ops::{ControlFlow, Deref, Index, IndexMut},
};

use derive_generic_visitor::*;

/// Indexed vector.
/// To prevent accidental id reuse, the vector supports reserving a slot to be filled later.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Vector<I, T>
where
    I: Idx,
{
    vector: IndexVec<I, Option<T>>,
    /// The number of non-`None` elements.
    real_len: usize,
}

impl<I: std::fmt::Debug, T: std::fmt::Debug> std::fmt::Debug for Vector<I, T>
where
    I: Idx,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <IndexVec<_, _> as std::fmt::Debug>::fmt(&self.vector, f)
    }
}

pub struct ReservedSlot<I: Idx>(I);

impl<I, T> Vector<I, T>
where
    I: Idx,
{
    pub fn new() -> Self {
        Vector {
            vector: IndexVec::new(),
            real_len: 0,
        }
    }

    pub fn get(&self, i: I) -> Option<&T> {
        self.vector.get(i).map(Option::as_ref).flatten()
    }

    pub fn get_mut(&mut self, i: I) -> Option<&mut T> {
        self.vector.get_mut(i).map(Option::as_mut).flatten()
    }

    pub fn is_empty(&self) -> bool {
        self.real_len == 0
    }

    pub fn len(&self) -> usize {
        self.real_len
    }

    /// Gets the value of the next available id. Avoid if possible; use `reserve_slot` instead.
    pub fn next_id(&self) -> I {
        self.vector.next_idx()
    }

    /// Reserve a spot in the vector.
    pub fn reserve_slot(&mut self) -> I {
        // Push a `None` to ensure we don't reuse the id.
        self.vector.push(None)
    }

    /// Fill the reserved slot.
    pub fn set_slot(&mut self, id: I, x: T) {
        assert!(self.vector[id].is_none());
        self.vector[id] = Some(x);
        self.real_len += 1;
    }

    /// Remove the value from this slot.
    pub fn remove(&mut self, id: I) -> Option<T> {
        if self.vector[id].is_some() {
            self.real_len -= 1;
        }
        std::mem::replace(&mut self.vector[id], None)
    }

    pub fn push(&mut self, x: T) -> I {
        self.real_len += 1;
        self.vector.push(Some(x))
    }

    pub fn push_with(&mut self, f: impl FnOnce(I) -> T) -> I {
        let id = self.reserve_slot();
        let x = f(id);
        self.set_slot(id, x);
        id
    }

    pub fn push_all<It>(&mut self, it: It) -> impl Iterator<Item = I> + use<'_, I, T, It>
    where
        It: Iterator<Item = T>,
    {
        it.map(move |x| self.push(x))
    }

    pub fn extend<It>(&mut self, it: It)
    where
        It: Iterator<Item = T>,
    {
        self.push_all(it).for_each(|_| ())
    }

    /// Map each entry to a new one, keeping the same ids.
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> Vector<I, U> {
        Vector {
            vector: self
                .vector
                .into_iter()
                .map(|x_opt| x_opt.map(&mut f))
                .collect(),
            real_len: self.real_len,
        }
    }

    /// Map each entry to a new one, keeping the same ids.
    pub fn map_ref<'a, U>(&'a self, mut f: impl FnMut(&'a T) -> U) -> Vector<I, U> {
        Vector {
            vector: self
                .vector
                .iter()
                .map(|x_opt| x_opt.as_ref().map(&mut f))
                .collect(),
            real_len: self.real_len,
        }
    }

    /// Map each entry to a new one, keeping the same ids.
    pub fn map_ref_mut<'a, U>(&'a mut self, mut f: impl FnMut(&'a mut T) -> U) -> Vector<I, U> {
        Vector {
            vector: self
                .vector
                .iter_mut()
                .map(|x_opt| x_opt.as_mut().map(&mut f))
                .collect(),
            real_len: self.real_len,
        }
    }

    /// Map each entry to a new one, keeping the same ids.
    pub fn map_ref_indexed<'a, U>(&'a self, mut f: impl FnMut(I, &'a T) -> U) -> Vector<I, U> {
        Vector {
            vector: self
                .vector
                .iter_enumerated()
                .map(|(i, x_opt)| x_opt.as_ref().map(|x| f(i, x)))
                .collect(),
            real_len: self.real_len,
        }
    }

    /// Iter over the nonempty slots.
    pub fn iter(&self) -> impl Iterator<Item = &T> + DoubleEndedIterator + Clone {
        self.vector.iter().filter_map(|opt| opt.as_ref())
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> + DoubleEndedIterator {
        self.vector.iter_mut().filter_map(|opt| opt.as_mut())
    }

    pub fn iter_indexed(&self) -> impl Iterator<Item = (I, &T)> {
        self.vector
            .iter_enumerated()
            .flat_map(|(i, opt)| Some((i, opt.as_ref()?)))
    }

    pub fn into_iter_indexed(self) -> impl Iterator<Item = (I, T)> {
        self.vector
            .into_iter_enumerated()
            .flat_map(|(i, opt)| Some((i, opt?)))
    }

    pub fn iter_indexed_values(&self) -> impl Iterator<Item = (I, &T)> {
        self.iter_indexed()
    }

    pub fn into_iter_indexed_values(self) -> impl Iterator<Item = (I, T)> {
        self.into_iter_indexed()
    }

    /// Iterate over all slots, even empty ones.
    pub fn iter_all_slots(&self) -> impl Iterator<Item = &Option<T>> {
        self.vector.iter()
    }

    pub fn iter_indexed_all_slots(&self) -> impl Iterator<Item = (I, &Option<T>)> {
        self.vector.iter_enumerated()
    }

    pub fn iter_indices(&self) -> impl Iterator<Item = I> + '_ {
        // Reuse `iter_indexed` to filter only the filled indices.
        self.iter_indexed().map(|(id, _)| id)
    }

    /// Like `Vec::split_off`.
    pub fn split_off(&mut self, at: usize) -> Self {
        let mut ret = Self {
            vector: self.vector.split_off(I::from_usize(at)),
            real_len: 0,
        };
        self.real_len = self.iter().count();
        ret.real_len = ret.iter().count();
        ret
    }
}

impl<I: Idx, T> Default for Vector<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: Idx> Deref for ReservedSlot<I> {
    type Target = I;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<I, R, T> Index<R> for Vector<I, T>
where
    I: Idx,
    R: IdxSliceIndex<I, Option<T>, Output = Option<T>>,
{
    type Output = T;
    fn index(&self, index: R) -> &Self::Output {
        self.vector[index].as_ref().unwrap()
    }
}

impl<I, R, T> IndexMut<R> for Vector<I, T>
where
    I: Idx,
    R: IdxSliceIndex<I, Option<T>, Output = Option<T>>,
{
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        self.vector[index].as_mut().unwrap()
    }
}

impl<'a, I, T> IntoIterator for &'a Vector<I, T>
where
    I: Idx,
{
    type Item = &'a T;
    type IntoIter = impl Iterator<Item = &'a T>;

    fn into_iter(self) -> Self::IntoIter {
        self.vector.iter().flat_map(|opt| opt.as_ref())
    }
}

impl<'a, I, T> IntoIterator for &'a mut Vector<I, T>
where
    I: Idx,
{
    type Item = &'a mut T;
    type IntoIter = impl Iterator<Item = &'a mut T>;

    fn into_iter(self) -> Self::IntoIter {
        self.vector.iter_mut().flat_map(|opt| opt.as_mut())
    }
}

impl<I, T> IntoIterator for Vector<I, T>
where
    I: Idx,
{
    type Item = T;
    type IntoIter = impl Iterator<Item = T>;

    fn into_iter(self) -> Self::IntoIter {
        self.vector.into_iter().flat_map(|opt| opt)
    }
}

// FIXME: this impl is a footgun
impl<I, T> FromIterator<T> for Vector<I, T>
where
    I: Idx,
{
    #[inline]
    fn from_iter<It: IntoIterator<Item = T>>(iter: It) -> Vector<I, T> {
        let mut real_len = 0;
        let vector = IndexVec::from_iter(iter.into_iter().inspect(|_| real_len += 1).map(Some));
        Vector { vector, real_len }
    }
}

// FIXME: this impl is a footgun
impl<I, T> From<Vec<T>> for Vector<I, T>
where
    I: Idx,
{
    fn from(v: Vec<T>) -> Self {
        v.into_iter().collect()
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

impl<'de, I: Idx, T: Deserialize<'de>> Deserialize<'de> for Vector<I, T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let mut ret = Self {
            vector: Deserialize::deserialize(deserializer)?,
            real_len: 0,
        };
        ret.real_len = ret.iter().count();
        Ok(ret)
    }
}

impl<'s, I: Idx, T, V: Visit<'s, T>> Drive<'s, V> for Vector<I, T> {
    fn drive_inner(&'s self, v: &mut V) -> ControlFlow<V::Break> {
        for x in self {
            v.visit(x)?;
        }
        Continue(())
    }
}
impl<'s, I: Idx, T, V: VisitMut<'s, T>> DriveMut<'s, V> for Vector<I, T> {
    fn drive_inner_mut(&'s mut self, v: &mut V) -> ControlFlow<V::Break> {
        for x in self {
            v.visit(x)?;
        }
        Continue(())
    }
}
