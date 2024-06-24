//! A vector with custom index types.
//!
//! This data-structure is mostly meant to be used with the index types defined
//! with [ids::generate_index_type]: by using custom index types, we
//! leverage the type checker to prevent us from mixing them.
//!
//! Note that this data structure is implemented by using persistent vectors.
//! This makes the clone operation almost a no-op.

use derive_visitor::{Drive, DriveMut, Event, Visitor, VisitorMut};
use index_vec::{Idx, IdxSliceIndex, IndexVec};
use serde::{Deserialize, Serialize, Serializer};
use std::{
    iter::{FromIterator, IntoIterator},
    ops::{Deref, Index, IndexMut},
};

/// Indexed vector.
/// To prevent accidental id reuse, the vector supports reserving a slot to be filled later.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Vector<I, T>
where
    I: Idx,
{
    vector: IndexVec<I, Option<T>>,
}

pub struct ReservedSlot<I: Idx>(I);

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
        self.vector.get(i).map(Option::as_ref).flatten()
    }

    pub fn get_mut(&mut self, i: I) -> Option<&mut T> {
        self.vector.get_mut(i).map(Option::as_mut).flatten()
    }

    pub fn is_empty(&self) -> bool {
        self.vector.is_empty()
    }

    pub fn len(&self) -> usize {
        self.vector.len()
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
    }

    /// Remove the value from this slot.
    pub fn remove(&mut self, id: I) {
        self.vector[id] = None
    }

    pub fn push(&mut self, x: T) -> I {
        self.vector.push(Some(x))
    }

    pub fn push_with(&mut self, f: impl FnOnce(I) -> T) -> I {
        let id = self.reserve_slot();
        let x = f(id);
        self.set_slot(id, x);
        id
    }

    /// Iter over the nonempty slots.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.vector.iter().flat_map(|opt| opt.as_ref())
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.vector.iter_mut().flat_map(|opt| opt.as_mut())
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

    pub fn iter_indices(&self) -> impl Iterator<Item = I> {
        self.vector.indices()
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
        Vector {
            vector: IndexVec::from_iter(iter.into_iter().map(Some)),
        }
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
        Ok(Self {
            vector: Deserialize::deserialize(deserializer)?,
        })
    }
}

impl<I: Idx, T: Drive> Drive for Vector<I, T> {
    fn drive<V: Visitor>(&self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        for x in self {
            x.drive(visitor);
        }
        visitor.visit(self, Event::Exit);
    }
}
impl<I: Idx, T: DriveMut> DriveMut for Vector<I, T> {
    fn drive_mut<V: VisitorMut>(&mut self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        for x in &mut *self {
            x.drive_mut(visitor);
        }
        visitor.visit(self, Event::Exit);
    }
}
