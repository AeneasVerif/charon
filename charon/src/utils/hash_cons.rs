use derive_generic_visitor::{Drive, DriveMut, DriveTwo, Visit, VisitMut, VisitTwo};
use std::hash::Hash;
use std::ops::{ControlFlow, Deref};
use std::sync::Arc;

use crate::utils::hash_by_addr::HashByAddr;
use crate::utils::type_map::Mappable;

/// Hash-consed data structure: a reference-counted wrapper that guarantees that two equal
/// value will be stored at the same address. This makes it possible to use the pointer address
/// as a hash value.
// Warning: a `derive` should not introduce a way to create a new `HashConsed` value without
// going through the interning table.
#[derive(PartialEq, Eq, Hash)]
pub struct HashConsed<T>(HashByAddr<Arc<T>>);

impl<T> Clone for HashConsed<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T> HashConsed<T> {
    pub fn inner(&self) -> &T {
        self.0.0.as_ref()
    }
}

impl<T: PartialOrd> PartialOrd for HashConsed<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.inner().partial_cmp(other.inner())
    }
}

impl<T: Ord> Ord for HashConsed<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner().cmp(other.inner())
    }
}

pub trait HashConsable: Hash + PartialEq + Eq + Clone + Mappable {}
impl<T> HashConsable for T where T: Hash + PartialEq + Eq + Clone + Mappable {}

// Private module that contains the static we'll use as interning map. A value of type
// `HashCons` MUST NOT be created in any other way than this table, else hashing and euqality
// on it will be broken. Note that this likely means that if a crate uses charon both as a
// direct dependency and as a dylib, then the static will be duplicated, causing hashing and
// equality on `HashCons` to be broken.
mod intern_table {
    use rustc_hash::FxBuildHasher;
    use std::borrow::Borrow;
    use std::sync::{Arc, LazyLock, RwLock};

    use super::{HashConsable, HashConsed};
    use crate::utils::hash_by_addr::HashByAddr;
    use crate::utils::type_map::{Mappable, Mapper, TypeMap};

    type SeqHashSet<T> = indexmap::IndexSet<T, FxBuildHasher>;

    // This is a static mutable `SeqHashSet<Arc<T>>` that records for each `T` value a unique
    // `Arc<T>` that contains the same value. Values inside the set are hashed/compared
    // as is normal for `T`.
    // Once we've gotten an `Arc` out of the set however, we're sure that "T-equality"
    // implies address-equality, hence the `HashByAddr` wrapper preserves correct equality
    // and hashing behavior.
    struct InternMapper;
    impl Mapper for InternMapper {
        type Value<T: Mappable> = SeqHashSet<Arc<T>>;
    }
    static INTERNED: LazyLock<RwLock<TypeMap<InternMapper>>> = LazyLock::new(Default::default);

    // The excessive generality is to make it work for both `U = T` and `U = Arc<T>`.
    pub fn intern<T: HashConsable, U>(inner: U) -> HashConsed<T>
    where
        Arc<T>: Borrow<U>,
        U: Into<Arc<T>> + std::hash::Hash,
        U: indexmap::Equivalent<Arc<T>>,
    {
        // Fast read-only check.
        let arc = if let read_guard = INTERNED.read().unwrap()
            && let Some(set) = read_guard.get::<T>()
            && let Some(arc) = set.get(&inner)
        {
            arc.clone()
        } else {
            // Concurrent access is possible right here, so we have to check everything again.
            let mut write_guard = INTERNED.write().unwrap();
            let set: &mut SeqHashSet<Arc<T>> = write_guard.or_default::<T>();
            if let Some(arc) = set.get(&inner) {
                arc.clone()
            } else {
                let arc: Arc<T> = inner.into();
                set.insert(arc.clone());
                arc
            }
        };
        HashConsed(HashByAddr(arc))
    }

    /// Mutate the contents in-place if possible.
    pub fn mutate_in_place<T: HashConsable, R, F: FnOnce(&mut T) -> R>(
        x: &mut HashConsed<T>,
        f: F,
    ) -> Result<R, F> {
        let arc = &mut x.0.0;
        // Every value has at least two pointers: the current value and the one stored in the
        // global map. If there are exactly two, we may mutate directly by discarding the one in
        // the global map temporarily.
        if Arc::strong_count(arc) != 2 {
            return Err(f);
        }
        {
            // Take the write guard just long enough to drop the other `Arc` to this value.
            let mut write_guard = INTERNED.write().unwrap();
            // Check the count again, it could have changed concurrently.
            if Arc::strong_count(arc) != 2 {
                return Err(f);
            }
            if let Some(other_arc) = write_guard.or_default::<T>().swap_take(&*arc) {
                drop(other_arc);
            } else {
                // Nothing was removed, early return.
                return Err(f);
            }
            // The Arc was removed from the map; `x` is invalid as interning the same value would
            // result in a different pointer. NO MORE EARLY RETURN until we fix that.
        }
        // If we are still the sole owner, we can now mutate in-place.
        let ret = match Arc::get_mut(arc) {
            Some(val) => Ok(f(val)),
            None => Err(f),
        };
        // Re-establish the interning invariant. If the same value was added to the map in the
        // meantime, we'll get a pointer to that.
        *x = HashConsed::from_arc(arc.clone());
        ret
    }
}

impl<T> HashConsed<T>
where
    T: HashConsable,
{
    /// Deduplicate the values by hashing them. This deduplication is crucial for the hashing
    /// function to be correct. This is the only function allowed to create `Self` values.
    pub fn new(inner: T) -> Self {
        intern_table::intern(inner)
    }
    /// Rarely used: in case we already have an `Arc`, may avoid an allocation.
    pub fn from_arc(inner: Arc<T>) -> Self {
        intern_table::intern(inner)
    }

    /// Clones if needed to get mutable access to the inner value.
    pub fn with_inner_mut<R>(&mut self, f: impl FnOnce(&mut T) -> R) -> R {
        match intern_table::mutate_in_place(self, f) {
            Ok(r) => r,
            Err(f) => {
                // The value is behind a shared `Arc`, we clone it in order to mutate it.
                let mut value = self.inner().clone();
                let ret = f(&mut value);
                // Re-intern the new value.
                *self = Self::new(value);
                ret
            }
        }
    }
}

impl<T> Deref for HashConsed<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        self.inner()
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for HashConsed<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Hide the `HashByAddr` wrapper.
        f.debug_tuple("HashConsed").field(self.inner()).finish()
    }
}

impl<'s, T, V: Visit<'s, T>> Drive<'s, V> for HashConsed<T> {
    fn drive_inner(&'s self, v: &mut V) -> ControlFlow<V::Break> {
        v.visit(self.inner())
    }
}
impl<'s, T, V: VisitTwo<'s, T>> DriveTwo<'s, V> for HashConsed<T> {
    fn drive_two_inner(&'s self, other: &'s Self, v: &mut V) -> ControlFlow<V::Break> {
        v.visit(self.inner(), other.inner())
    }
}
/// Note: this explores the inner value mutably by cloning and re-hashing afterwards.
impl<'s, T, V> DriveMut<'s, V> for HashConsed<T>
where
    T: HashConsable,
    V: for<'a> VisitMut<'a, T>,
{
    fn drive_inner_mut(&'s mut self, v: &mut V) -> ControlFlow<V::Break> {
        self.with_inner_mut(|inner| v.visit(inner))
    }
}

/// `HashCons` values are deduplicated in the serialized output: see [`crate::utils::dedup`].
mod serialize {
    use serde::{Deserialize, Serialize};
    use serde_state::{DeserializeState, SerializeState};

    use super::{HashConsable, HashConsed};
    use crate::utils::dedup::*;

    impl<T> Serialize for HashConsed<T>
    where
        T: Serialize + HashConsable,
    {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            SerDedup::Untagged(self.inner()).serialize(serializer)
        }
    }
    /// Options for the state are `()` to serialize values normally and `DedupSerializer`
    /// to deduplicate identical values in the serialized output.
    impl<T, State> SerializeState<State> for HashConsed<T>
    where
        T: SerializeState<State> + HashConsable,
        State: DedupSerializerState,
    {
        fn serialize_state<S>(&self, state: &State, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            serialize_dedup(self, self.inner(), state, serializer)
        }
    }

    impl<'de, T> Deserialize<'de> for HashConsed<T>
    where
        T: Deserialize<'de> + HashConsable,
    {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            use serde::de::Error;
            let repr: SerDedup<T> = SerDedup::deserialize(deserializer)?;
            match repr {
                SerDedup::Value { .. } | SerDedup::Deduplicated { .. } => {
                    Err(D::Error::custom(stateless_deserialize_error::<T>()))
                }
                SerDedup::Untagged(val) => Ok(HashConsed::new(val)),
            }
        }
    }
    impl<'de, T, State> DeserializeState<'de, State> for HashConsed<T>
    where
        T: DeserializeState<'de, State> + HashConsable,
        State: DedupSerializerState,
    {
        fn deserialize_state<D>(state: &State, deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            deserialize_dedup(state, deserializer, HashConsed::new)
        }
    }
}

#[test]
fn test_hash_cons() {
    let x = HashConsed::new(42u32);
    let y = HashConsed::new(42u32);
    assert_eq!(x, y);
    // Test a serialization round-trip.
    let z = serde_json::from_value(serde_json::to_value(x.clone()).unwrap()).unwrap();
    assert_eq!(x, z);
}

#[test]
fn test_hash_cons_concurrent() {
    use itertools::Itertools;
    let handles = (0..10)
        .map(|_| std::thread::spawn(|| std::hint::black_box(HashConsed::new(42u32))))
        .collect_vec();
    let values = handles.into_iter().map(|h| h.join().unwrap()).collect_vec();
    assert!(values.iter().all_equal())
}

#[test]
fn test_hash_cons_dedup() {
    use crate::utils::dedup::DedupSerializer;
    use serde_state::{DeserializeState, SerializeState};
    type Ty = HashConsed<TyKind>;
    #[derive(Debug, Clone, PartialEq, Eq, Hash, SerializeState, DeserializeState)]
    #[serde_state(state = DedupSerializer)]
    enum TyKind {
        Bool,
        Pair(Ty, Ty),
    }

    // Build a value with some redundancy.
    let bool1 = HashConsed::new(TyKind::Bool);
    let bool2 = HashConsed::new(TyKind::Bool);
    let pair = HashConsed::new(TyKind::Pair(bool1.clone(), bool2));
    let triple = HashConsed::new(TyKind::Pair(bool1, pair));

    let state = DedupSerializer::default();
    let json_val = triple
        .serialize_state(&state, serde_json::value::Serializer)
        .unwrap();
    let state = DedupSerializer::default();
    let round_tripped = Ty::deserialize_state(&state, json_val).unwrap();

    assert_eq!(triple, round_tripped);
}
