use derive_generic_visitor::{Drive, DriveMut, Visit, VisitMut};
use serde::{Deserialize, Serialize};
use std::hash::Hash;
use std::ops::{ControlFlow, Deref};
use std::sync::Arc;

use crate::common::hash_by_addr::HashByAddr;
use crate::common::type_map::Mappable;

/// Hash-consed data structure: a reference-counted wrapper that guarantees that two equal
/// value will be stored at the same address. This makes it possible to use the pointer address
/// as a hash value.
// Warning: a `derive` should not introduce a way to create a new `HashConsed` value without
// going through the interning table.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct HashConsed<T>(HashByAddr<Arc<T>>);

impl<T> HashConsed<T> {
    pub fn inner(&self) -> &T {
        self.0.0.as_ref()
    }
}

pub trait HashConsable = Hash + PartialEq + Eq + Clone + Mappable;

/// Unique id identifying a hashconsed value amongst those with the same type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HashConsId(usize);

// Private module that contains the static we'll use as interning map. A value of type
// `HashCons` MUST NOT be created in any other way than this table, else hashing and euqality
// on it will be broken. Note that this likely means that if a crate uses charon both as a
// direct dependency and as a dylib, then the static will be duplicated, causing hashing and
// equality on `HashCons` to be broken.
mod intern_table {
    use indexmap::IndexSet;
    use std::sync::{Arc, LazyLock, RwLock};

    use super::{HashConsId, HashConsable, HashConsed};
    use crate::common::hash_by_addr::HashByAddr;
    use crate::common::type_map::{Mappable, Mapper, TypeMap};

    // This is a static mutable `IndexSet<Arc<T>>` that records for each `T` value a unique
    // `Arc<T>` that contains the same value. Values inside the set are hashed/compared
    // as is normal for `T`.
    // Once we've gotten an `Arc` out of the set however, we're sure that "T-equality"
    // implies address-equality, hence the `HashByAddr` wrapper preserves correct equality
    // and hashing behavior.
    struct InternMapper;
    impl Mapper for InternMapper {
        type Value<T: Mappable> = IndexSet<Arc<T>>;
    }
    static INTERNED: LazyLock<RwLock<TypeMap<InternMapper>>> = LazyLock::new(|| Default::default());

    pub fn intern<T: HashConsable>(inner: T) -> HashConsed<T> {
        if INTERNED.read().unwrap().get::<T>().is_none() {
            INTERNED.write().unwrap().insert::<T>(IndexSet::default());
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
        HashConsed(HashByAddr(arc))
    }

    /// Identify this value uniquely amongst values of its type. The id depends on insertion
    /// order into the interning table which makes them in principle deterministic.
    pub fn id<T: HashConsable>(x: &HashConsed<T>) -> HashConsId {
        // `HashConsed` can only be constructed via `intern`, so we know this value exists in
        // the table.
        HashConsId(
            (*INTERNED.read().unwrap())
                .get::<T>()
                .unwrap()
                .get_index_of(&x.0.0)
                .unwrap(),
        )
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

    /// Clones if needed to get mutable access to the inner value.
    pub fn with_inner_mut<R>(&mut self, f: impl FnOnce(&mut T) -> R) -> R {
        // The value is behind a shared `Arc`, we clone it in order to mutate it.
        let mut value = self.inner().clone();
        let ret = f(&mut value);
        // Re-intern the new value.
        *self = Self::new(value);
        ret
    }

    pub fn id(&self) -> HashConsId {
        intern_table::id(self)
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

/// `HashCons` supports serializing each value to a unique id in order to serialize
/// highly-shared values without explosion.
///
/// Note that the deduplication scheme is highly order-dependent: we serialize the real value
/// the first time it comes up, and use ids only subsequent times. This relies on the fact that
/// `derive(Serialize, Deserialize)` traverse the value in the same order.
pub use serialize::with_dedup_serialization;
mod serialize {
    use indexmap::IndexMap;
    use serde::{Deserialize, Serialize};
    use std::any::type_name;
    use std::collections::HashSet;
    use std::sync::{LazyLock, RwLock};

    use super::{HashConsId, HashConsable, HashConsed};
    use crate::common::type_map::{Mappable, Mapper, TypeMap};

    // If `Some`, we will deduplicate the serialized values. We use the contained sets to track
    // whether we've already serialized each value.
    struct SerializeTableMapper;
    impl Mapper for SerializeTableMapper {
        type Value<T: Mappable> = HashSet<HashConsId>;
    }
    static SERIALIZE_TO_IDS: LazyLock<RwLock<Option<TypeMap<SerializeTableMapper>>>> =
        LazyLock::new(|| RwLock::new(None));

    // During deserialization we record the already-deserialized values. If we don't find a
    // value deserialization errors.
    struct DeserializeTableMapper;
    impl Mapper for DeserializeTableMapper {
        type Value<T: Mappable> = IndexMap<HashConsId, HashConsed<T>>;
    }
    static DESERIALIZATION_SIDE_TABLE: LazyLock<RwLock<TypeMap<DeserializeTableMapper>>> =
        LazyLock::new(|| RwLock::new(TypeMap::default()));

    /// Enable the deduplication of `HashConsed` values in serialization output for the
    /// duraciton of the call to the provided function.
    pub fn with_dedup_serialization<R>(f: impl FnOnce() -> R) -> R {
        *SERIALIZE_TO_IDS.write().unwrap() = Some(TypeMap::default());
        let out = f();
        *SERIALIZE_TO_IDS.write().unwrap() = None;
        out
    }

    /// A dummy enum used when serializing/deserializing a `HashConsed<T>` in the deduplicated
    /// case.
    #[derive(Serialize, Deserialize)]
    #[serde(untagged)]
    enum SerRepr<T> {
        /// A value represented normally, accompanied by its id. This is emitted the first time
        /// we serialize a given value: subsequent times will use `SerRepr::Deduplicate`
        /// instead.
        HashConsedValue { hash_cons_id: HashConsId, value: T },
        /// A value represented by its id. The actual value must have been emitted as a
        /// `SerRepr::Value` with that same id earlier.
        Deduplicated { hash_cons_id: HashConsId },
        /// A plain value without an id.
        PlainValue(T),
    }

    impl<T> Serialize for HashConsed<T>
    where
        T: Serialize + HashConsable,
    {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            // This `unwrap` is about lock poisoning; we ignore that.
            let guard = SERIALIZE_TO_IDS.read().unwrap();
            if guard.is_some() {
                drop(guard);
                let hash_cons_id = self.id();
                let repr: SerRepr<T> = {
                    // This `unwrap` is about lock poisoning; we ignore that.
                    let mut type_map_lock = SERIALIZE_TO_IDS.write().unwrap();
                    // This `unwrap` is ok because of `is_some` above.
                    let type_map: &mut TypeMap<_> = type_map_lock.as_mut().unwrap();
                    if type_map.or_default::<T>().insert(hash_cons_id) {
                        SerRepr::HashConsedValue {
                            hash_cons_id,
                            value: self.inner().clone(),
                        }
                    } else {
                        SerRepr::Deduplicated { hash_cons_id }
                    }
                };
                // Careful to drop the locks before calling back into `serialize`.
                repr.serialize(serializer)
            } else {
                self.inner().serialize(serializer)
            }
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
            // Because of `serde(untagged)`, this can handle both a direct value and the
            // deduplicated cases.
            let repr: SerRepr<T> = SerRepr::deserialize(deserializer)?;
            Ok(match repr {
                SerRepr::HashConsedValue {
                    hash_cons_id,
                    value,
                } => {
                    let val = HashConsed::new(value);
                    // This `unwrap` is about lock poisoning; we ignore that.
                    DESERIALIZATION_SIDE_TABLE
                        .write()
                        .unwrap()
                        .or_default::<T>()
                        .insert(hash_cons_id, val.clone());
                    val
                }
                SerRepr::Deduplicated { hash_cons_id } => DESERIALIZATION_SIDE_TABLE
                    .read()
                    .unwrap()
                    .get::<T>()
                    .and_then(|map| map.get(&hash_cons_id))
                    .cloned()
                    .ok_or_else(|| {
                        let msg = format!(
                            "can't deserialize deduplicated value of type {};\
                                    possibly serialization and deserialization aren't \
                                    happening in the same order",
                            type_name::<T>()
                        );
                        D::Error::custom(msg)
                    })?,
                SerRepr::PlainValue(val) => HashConsed::new(val),
            })
        }
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

#[test]
fn test_hash_cons_dedup() {
    let x = HashConsed::new(42u32);
    let y = HashConsed::new(42u32);
    let val = (x.clone(), x.clone(), y);
    let (a, b, c): (HashConsed<u32>, HashConsed<u32>, HashConsed<u32>) =
        serde_json::from_value(serde_json::to_value(val).unwrap()).unwrap();
    assert_eq!(a, x);
    assert_eq!(b, x);
    assert_eq!(c, x);
}
