/// This module provides a notion of table, identifiers and nodes. A
/// `Node<T>` is a `Arc<T>` bundled with a unique identifier such that
/// there exists an entry in a table for that identifier.
///
/// The type `WithTable<T>` bundles a table with a value of type
/// `T`. That value of type `T` may hold an arbitrary number of
/// `Node<_>`s. In the context of a `WithTable<T>`, the type `Node<_>`
/// serializes and deserializes using a table as a state. In this
/// case, serializing a `Node<U>` produces only an identifier, without
/// any data of type `U`. Deserializing a `Node<U>` under a
/// `WithTable<T>` will recover `U` data from the table held by
/// `WithTable`.
///
/// Serde is not designed for stateful (de)serialization. There is no
/// way of deriving `serde::de::DeserializeSeed` systematically. This
/// module thus makes use of global state to achieve serialization and
/// deserialization. This modules provides an API that hides this
/// global state.
use crate::prelude::*;
use std::{
    hash::Hash,
    sync::{Arc, LazyLock, Mutex, MutexGuard, atomic::Ordering},
};

/// Unique IDs in a ID table.
#[derive_group(Serializers)]
#[derive(Default, Clone, Copy, Debug, JsonSchema, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[serde(transparent)]
pub struct Id {
    id: u32,
}

/// A session providing fresh IDs for ID table.
#[derive(Default, Debug)]
pub struct Session {
    table: Table,
}

impl Session {
    pub fn table(&self) -> &Table {
        &self.table
    }
}

/// The different types of values one can store in an ID table.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub enum Value {
    Ty(Arc<TyKind>),
    DefId(Arc<DefIdContents>),
    ItemRef(Arc<ItemRefContents>),
}

/// A table is a map from IDs to `Value`s. When serialized, we
/// represent a table as a *sorted* vector. Indeed, the values stored
/// in the table might reference each other, without cycle, so the
/// order matters.
#[derive(Default, Debug, Clone, Deserialize, Serialize)]
#[serde(into = "serde_repr::SortedIdValuePairs")]
#[serde(from = "serde_repr::SortedIdValuePairs")]
pub struct Table(HeterogeneousMap<Id, Value>);

mod heterogeneous_map {
    //! This module provides an heterogenous map that can store types
    //! that implement the trait `SupportedType`.

    use std::collections::HashMap;
    use std::hash::Hash;
    #[derive(Clone, Debug)]
    /// An heterogenous map is a map from `Key` to `Value`. It provide
    /// the methods `insert` and `get` for any type `T` that
    /// implements `SupportedType<Value>`.
    pub struct HeterogeneousMap<Key, Value>(HashMap<Key, Value>);

    impl<Id, Value> Default for HeterogeneousMap<Id, Value> {
        fn default() -> Self {
            Self(HashMap::default())
        }
    }

    impl<Key: Hash + Eq + PartialEq, Value> HeterogeneousMap<Key, Value> {
        pub(super) fn insert_raw_value(&mut self, key: Key, value: Value) {
            self.0.insert(key, value);
        }
        pub(super) fn from_iter(it: impl Iterator<Item = (Key, Value)>) -> Self {
            Self(HashMap::from_iter(it))
        }
        pub(super) fn into_iter(self) -> impl Iterator<Item = (Key, Value)> {
            self.0.into_iter()
        }
    }
}
use heterogeneous_map::*;

/// Wrapper for a type `T` that creates a bundle containing both a ID
/// table and a value `T`. That value may contains `Node` values
/// inside it. Serializing `WithTable<T>` will serialize IDs only,
/// skipping values. Deserialization of a `WithTable<T>` will
/// automatically use the table and IDs to reconstruct skipped values.
#[derive(Debug)]
pub struct WithTable<T> {
    table: Table,
    value: T,
}

/// The state used for deserialization: a table.
static DESERIALIZATION_STATE: LazyLock<Mutex<Table>> =
    LazyLock::new(|| Mutex::new(Table::default()));
static DESERIALIZATION_STATE_LOCK: LazyLock<Mutex<()>> = LazyLock::new(|| Mutex::new(()));

/// The mode of serialization: should `Node<T>` ship values of type `T` or not?
static SERIALIZATION_MODE_USE_IDS: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

fn serialize_use_id() -> bool {
    SERIALIZATION_MODE_USE_IDS.load(Ordering::Relaxed)
}

impl<T> WithTable<T> {
    /// Runs `f` with a `WithTable<T>` created out of `map` and
    /// `value`. Any serialization of values of type `Node<_>` will
    /// skip the field `value`.
    pub fn run<R>(map: Table, value: T, f: impl FnOnce(&Self) -> R) -> R {
        if serialize_use_id() {
            panic!(
                "CACHE_MAP_LOCK: only one WithTable serialization can occur at a time (nesting is forbidden)"
            )
        }
        SERIALIZATION_MODE_USE_IDS.store(true, Ordering::Relaxed);
        let result = f(&Self { table: map, value });
        SERIALIZATION_MODE_USE_IDS.store(false, Ordering::Relaxed);
        result
    }
    pub fn destruct(self) -> (T, Table) {
        let Self { value, table: map } = self;
        (value, map)
    }
}

impl<T: Serialize> Serialize for WithTable<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut ts = serializer.serialize_tuple_struct("WithTable", 2)?;
        use serde::ser::SerializeTupleStruct;
        ts.serialize_field(&self.table)?;
        ts.serialize_field(&self.value)?;
        ts.end()
    }
}

/// The deserializer of `WithTable<T>` is special. We first decode the
/// table in order: each `(Id, Value)` pair of the table populates the
/// global table state found in `DESERIALIZATION_STATE`. Only then we
/// can decode the value itself, knowing `DESERIALIZATION_STATE` is
/// complete.
impl<'de, T: Deserialize<'de>> serde::Deserialize<'de> for WithTable<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let _lock: MutexGuard<_> = DESERIALIZATION_STATE_LOCK.try_lock().expect("CACHE_MAP_LOCK: only one WithTable deserialization can occur at a time (nesting is forbidden)");
        use serde_repr::WithTableRepr;
        let previous = std::mem::take(&mut *DESERIALIZATION_STATE.lock().unwrap());
        let with_table_repr = WithTableRepr::deserialize(deserializer);
        *DESERIALIZATION_STATE.lock().unwrap() = previous;
        let WithTableRepr(table, value) = with_table_repr?;
        Ok(Self { table, value })
    }
}

/// Defines representations for various types when serializing or/and
/// deserializing via serde
mod serde_repr {
    use super::*;

    #[derive(Serialize)]
    pub(super) struct Pair(Id, Value);
    pub(super) type SortedIdValuePairs = Vec<Pair>;

    #[derive(Serialize, Deserialize)]
    pub(super) struct WithTableRepr<T>(pub(super) Table, pub(super) T);

    impl<'de> serde::Deserialize<'de> for Pair {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            let (id, v) = <(Id, Value)>::deserialize(deserializer)?;
            DESERIALIZATION_STATE
                .lock()
                .unwrap()
                .0
                .insert_raw_value(id.clone(), v.clone());
            Ok(Pair(id, v))
        }
    }

    impl Into<SortedIdValuePairs> for Table {
        fn into(self) -> SortedIdValuePairs {
            let mut vec: Vec<_> = self.0.into_iter().map(|(x, y)| Pair(x, y)).collect();
            vec.sort_by_key(|o| o.0.clone());
            vec
        }
    }

    impl From<SortedIdValuePairs> for Table {
        fn from(t: SortedIdValuePairs) -> Self {
            Self(HeterogeneousMap::from_iter(
                t.into_iter().map(|Pair(x, y)| (x, y)),
            ))
        }
    }
}

pub mod type_map {
    use std::{
        any::{Any, TypeId},
        collections::HashMap,
        marker::PhantomData,
    };

    pub trait Mappable = Any + Send + Sync;

    pub trait Mapper {
        type Value<T: Mappable>: Mappable;
    }

    /// A map that maps types to values in a generic manner: we store for each type `T` a value of
    /// type `M::Value<T>`.
    pub struct TypeMap<M> {
        data: HashMap<TypeId, Box<dyn Mappable>>,
        phantom: PhantomData<M>,
    }

    impl<M: Mapper> TypeMap<M> {
        pub fn get<T: Mappable>(&self) -> Option<&M::Value<T>> {
            self.data
                .get(&TypeId::of::<T>())
                // We must be careful to not accidentally cast the box itself as `dyn Any`.
                .map(|val: &Box<dyn Mappable>| &**val)
                .and_then(|val: &dyn Mappable| (val as &dyn Any).downcast_ref())
        }

        pub fn get_mut<T: Mappable>(&mut self) -> Option<&mut M::Value<T>> {
            self.data
                .get_mut(&TypeId::of::<T>())
                // We must be careful to not accidentally cast the box itself as `dyn Any`.
                .map(|val: &mut Box<dyn Mappable>| &mut **val)
                .and_then(|val: &mut dyn Mappable| (val as &mut dyn Any).downcast_mut())
        }

        pub fn insert<T: Mappable>(&mut self, val: M::Value<T>) -> Option<Box<M::Value<T>>> {
            self.data
                .insert(TypeId::of::<T>(), Box::new(val))
                .and_then(|val: Box<dyn Mappable>| (val as Box<dyn Any>).downcast().ok())
        }
    }

    impl<M> Default for TypeMap<M> {
        fn default() -> Self {
            Self {
                data: Default::default(),
                phantom: Default::default(),
            }
        }
    }
}

pub mod hash_consing {
    use super::hash_by_addr::HashByAddr;
    use super::type_map::{Mappable, Mapper, TypeMap};
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};
    use std::collections::HashSet;
    use std::hash::Hash;
    use std::ops::Deref;
    use std::sync::{Arc, LazyLock, RwLock};

    /// Hash-consed data structure: a reference-counted wrapper that guarantees that two equal
    /// value will be stored at the same address. This makes it possible to use the pointer address
    /// as a hash value.
    #[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, JsonSchema)]
    pub struct HashConsed<T>(HashByAddr<Arc<T>>);

    impl<T> HashConsed<T> {
        pub fn inner(&self) -> &T {
            self.0.0.as_ref()
        }
    }

    impl<T> HashConsed<T>
    where
        T: Hash + PartialEq + Eq + Mappable,
    {
        pub fn new(inner: T) -> Self {
            Self::intern(inner)
        }

        /// Clones if needed to get mutable access to the inner value.
        pub fn with_inner_mut<R>(&mut self, f: impl FnOnce(&mut T) -> R) -> R
        where
            T: Clone,
        {
            // The value is behind a shared `Arc`, we clone it in order to mutate it.
            let mut value = self.inner().clone();
            let ret = f(&mut value);
            // Re-intern the new value.
            *self = Self::intern(value);
            ret
        }

        /// Deduplicate the values by hashing them. This deduplication is crucial for the hashing
        /// function to be correct. This is the only function allowed to create `Self` values.
        fn intern(inner: T) -> Self {
            struct InternMapper;
            impl Mapper for InternMapper {
                type Value<T: Mappable> = HashSet<Arc<T>>;
            }
            // This is a static mutable `HashSet<Arc<T>>` that records for each `T` value a unique
            // `Arc<T>` that contains the same value. Values inside the set are hashed/compared
            // as is normal for `T`.
            // Once we've gotten an `Arc` out of the set however, we're sure that "T-equality"
            // implies address-equality, hence the `HashByAddr` wrapper preserves correct equality
            // and hashing behavior.
            static INTERNED: LazyLock<RwLock<TypeMap<InternMapper>>> =
                LazyLock::new(|| Default::default());

            if INTERNED.read().unwrap().get::<T>().is_none() {
                INTERNED.write().unwrap().insert::<T>(HashSet::default());
            }
            let read_guard = INTERNED.read().unwrap();
            let arc = if let Some(arc) = (*read_guard).get::<T>().unwrap().get(&inner) {
                arc.clone()
            } else {
                drop(read_guard);
                let arc: Arc<T> = Arc::new(inner);
                INTERNED
                    .write()
                    .unwrap()
                    .get_mut::<T>()
                    .unwrap()
                    .insert(arc.clone());
                arc
            };
            Self(HashByAddr(arc))
        }
    }

    impl<T> Clone for HashConsed<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
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

    /// Manual impl to make sure we re-establish sharing!
    impl<'de, T> Deserialize<'de> for HashConsed<T>
    where
        T: Hash + PartialEq + Eq + Clone + Mappable,
        T: Deserialize<'de>,
    {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            let x: T = T::deserialize(deserializer)?;
            Ok(Self::new(x))
        }
    }

    #[test]
    fn test_hash_cons() {
        let x = HashConsed::new(42u32);
        let y = HashConsed::new(42u32);
        assert_eq!(x, y);
        let z = serde_json::from_value(serde_json::to_value(x.clone()).unwrap()).unwrap();
        assert_eq!(x, z);
    }
}

pub mod hash_by_addr {
    use schemars::JsonSchema;
    use serde::{Deserialize, Serialize};
    use std::{
        hash::{Hash, Hasher},
        ops::Deref,
    };

    /// A wrapper around a smart pointer that hashes and compares the contents by the address of
    /// the pointee.
    #[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
    pub struct HashByAddr<T>(pub T);

    impl<T: Deref> HashByAddr<T> {
        pub fn addr(&self) -> *const T::Target {
            self.0.deref()
        }
    }

    impl<T: Deref> Eq for HashByAddr<T> {}
    impl<T: Deref> PartialEq for HashByAddr<T> {
        fn eq(&self, other: &Self) -> bool {
            std::ptr::addr_eq(self.addr(), other.addr())
        }
    }

    impl<T: Deref> Hash for HashByAddr<T> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.addr().hash(state);
        }
    }

    // Delegate `Ord` impls to the derefed value.
    impl<T: Deref<Target: PartialOrd>> PartialOrd for HashByAddr<T> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            self.0.partial_cmp(&other.0)
        }
    }
    impl<T: Deref<Target: Ord>> Ord for HashByAddr<T> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.0.cmp(&other.0)
        }
    }
}
