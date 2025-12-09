use itertools::Itertools;

pub static TAB_INCR: &str = "    ";

/// Custom function to pretty-print elements from an iterator
/// The output format is:
/// ```text
/// [
///   elem_0,
///   ...
///   elem_n
/// ]
/// ```
pub fn pretty_display_list<T>(
    t_to_string: impl Fn(T) -> String,
    it: impl IntoIterator<Item = T>,
) -> String {
    let mut elems = it
        .into_iter()
        .map(t_to_string)
        .map(|x| format!("  {},\n", x))
        .peekable();
    if elems.peek().is_none() {
        "[]".to_owned()
    } else {
        format!("[\n{}]", elems.format(""))
    }
}

/// Implement `From` and `TryFrom` to wrap/unwrap enum variants with a single payload.
#[macro_export]
macro_rules! impl_from_enum {
    ($enum:ident::$variant:ident($ty:ty)) => {
        impl From<$ty> for $enum {
            fn from(x: $ty) -> Self {
                $enum::$variant(x)
            }
        }
        impl TryFrom<$enum> for $ty {
            type Error = ();
            fn try_from(e: $enum) -> Result<Self, Self::Error> {
                match e {
                    $enum::$variant(x) => Ok(x),
                    _ => Err(()),
                }
            }
        }
    };
}

/// Yield `None` then infinitely many `Some(x)`.
pub fn repeat_except_first<T: Clone>(x: T) -> impl Iterator<Item = Option<T>> {
    [None].into_iter().chain(std::iter::repeat(Some(x)))
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

        pub fn or_insert_with<T: Mappable>(
            &mut self,
            f: impl FnOnce() -> M::Value<T>,
        ) -> &mut M::Value<T> {
            if self.get::<T>().is_none() {
                self.insert(f());
            }
            self.get_mut::<T>().unwrap()
        }
        pub fn or_default<T: Mappable>(&mut self) -> &mut M::Value<T>
        where
            M::Value<T>: Default,
        {
            self.or_insert_with(|| Default::default())
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

pub mod hash_by_addr {
    use serde::{Deserialize, Serialize};
    use std::{
        hash::{Hash, Hasher},
        ops::Deref,
    };

    /// A wrapper around a smart pointer that hashes and compares the contents by the address of
    /// the pointee.
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct HashByAddr<T>(pub T);

    impl<T: Deref> HashByAddr<T> {
        fn addr(&self) -> *const T::Target {
            self.0.deref()
        }
    }

    impl<T: Eq + Deref> Eq for HashByAddr<T> {}

    impl<T: PartialEq + Deref> PartialEq for HashByAddr<T> {
        fn eq(&self, other: &Self) -> bool {
            std::ptr::addr_eq(self.addr(), other.addr())
        }
    }

    impl<T: Hash + Deref> Hash for HashByAddr<T> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.addr().hash(state);
        }
    }
}

pub mod serialize_map_to_array {
    use core::{fmt, marker::PhantomData};
    use std::{
        collections::hash_map::RandomState,
        hash::{BuildHasher, Hash},
    };

    use indexmap::IndexMap;
    use serde::{
        Deserialize, Deserializer, Serialize,
        de::{SeqAccess, Visitor},
        ser::Serializer,
    };
    use serde_state::{DeserializeState, SerializeState};

    #[derive(Serialize, Deserialize, SerializeState, DeserializeState)]
    struct KeyValue<K, V> {
        key: K,
        value: V,
    }

    /// A converter between an `IndexMap` and a sequence of named key-value pairs.
    pub struct IndexMapToArray<K, V, U = RandomState>(PhantomData<(K, V, U)>);

    impl<K, V, U> IndexMapToArray<K, V, U> {
        /// Serializes the given `map` to an array of named key-values.
        pub fn serialize<'a, S>(
            map: &'a IndexMap<K, V, U>,
            serializer: S,
        ) -> Result<S::Ok, S::Error>
        where
            K: Serialize,
            V: Serialize,
            S: Serializer,
        {
            serializer.collect_seq(map.into_iter().map(|(key, value)| KeyValue { key, value }))
        }
        pub fn serialize_state<'a, S, State: ?Sized>(
            map: &'a IndexMap<K, V, U>,
            state: &State,
            serializer: S,
        ) -> Result<S::Ok, S::Error>
        where
            K: SerializeState<State>,
            V: SerializeState<State>,
            S: Serializer,
        {
            serializer.collect_seq(
                map.into_iter().map(|(key, value)| {
                    serde_state::WithState::new(KeyValue { key, value }, state)
                }),
            )
        }

        /// Deserializes from an array of named key-values.
        pub fn deserialize<'de, D>(deserializer: D) -> Result<IndexMap<K, V, U>, D::Error>
        where
            K: Deserialize<'de> + Eq + Hash,
            V: Deserialize<'de>,
            U: BuildHasher + Default,
            D: Deserializer<'de>,
        {
            struct IndexMapToArrayVisitor<K, V, U>(PhantomData<(K, V, U)>);

            impl<'de, K, V, U> Visitor<'de> for IndexMapToArrayVisitor<K, V, U>
            where
                K: Deserialize<'de> + Eq + Hash,
                V: Deserialize<'de>,
                U: BuildHasher + Default,
            {
                type Value = IndexMap<K, V, U>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str("a list of key-value objects")
                }

                fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                    let mut map = IndexMap::<K, V, U>::default();
                    while let Some(entry) = seq.next_element::<KeyValue<K, V>>()? {
                        map.insert(entry.key, entry.value);
                    }
                    Ok(map)
                }
            }
            let map =
                deserializer.deserialize_seq(IndexMapToArrayVisitor::<K, V, U>(PhantomData))?;
            Ok(map.into())
        }
        /// Deserializes from an array of named key-values.
        pub fn deserialize_state<'de, D, State>(
            state: &State,
            deserializer: D,
        ) -> Result<IndexMap<K, V, U>, D::Error>
        where
            K: DeserializeState<'de, State> + Eq + Hash,
            V: DeserializeState<'de, State>,
            U: BuildHasher + Default,
            D: Deserializer<'de>,
        {
            struct IndexMapToArrayVisitor<'a, State, K, V, U>(&'a State, PhantomData<(K, V, U)>);

            impl<'de, State, K, V, U> Visitor<'de> for IndexMapToArrayVisitor<'_, State, K, V, U>
            where
                K: DeserializeState<'de, State> + Eq + Hash,
                V: DeserializeState<'de, State>,
                U: BuildHasher + Default,
            {
                type Value = IndexMap<K, V, U>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str("a list of key-value objects")
                }

                fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
                    let mut map = IndexMap::default();
                    let seed =
                        serde_state::__private::wrap_deserialize_seed::<KeyValue<K, V>, _>(self.0);
                    while let Some(entry) = seq.next_element_seed(seed)? {
                        map.insert(entry.key, entry.value);
                    }
                    Ok(map)
                }
            }
            let map = deserializer
                .deserialize_seq(IndexMapToArrayVisitor::<_, K, V, U>(state, PhantomData))?;
            Ok(map.into())
        }
    }
}

// This is the amount of bytes that need to be left on the stack before increasing the size. It
// must be at least as large as the stack required by any code that does not call
// `ensure_sufficient_stack`.
const RED_ZONE: usize = 100 * 1024; // 100k

// Only the first stack that is pushed, grows exponentially (2^n * STACK_PER_RECURSION) from then
// on. Values taken from rustc.
const STACK_PER_RECURSION: usize = 1024 * 1024; // 1MB

/// Grows the stack on demand to prevent stack overflow. Call this in strategic locations to "break
/// up" recursive calls. E.g. most statement visitors can benefit from this.
#[inline]
pub fn ensure_sufficient_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(RED_ZONE, STACK_PER_RECURSION, f)
}

/// Returns the values of the command-line options that match `find_arg`. The options are built-in
/// to be of the form `--arg=value` or `--arg value`.
pub fn arg_values<'a, T: AsRef<str>>(
    args: &'a [T],
    needle: &'a str,
) -> impl Iterator<Item = &'a str> {
    struct ArgFilter<'a, T> {
        args: std::slice::Iter<'a, T>,
        needle: &'a str,
    }
    impl<'a, T: AsRef<str>> Iterator for ArgFilter<'a, T> {
        type Item = &'a str;
        fn next(&mut self) -> Option<Self::Item> {
            while let Some(arg) = self.args.next() {
                let mut split_arg = arg.as_ref().splitn(2, '=');
                if split_arg.next() == Some(self.needle) {
                    return match split_arg.next() {
                        // `--arg=value` form
                        arg @ Some(_) => arg,
                        // `--arg value` form
                        None => self.args.next().map(|x| x.as_ref()),
                    };
                }
            }
            None
        }
    }
    ArgFilter {
        args: args.iter(),
        needle,
    }
}

pub fn arg_value<'a, T: AsRef<str>>(args: &'a [T], needle: &'a str) -> Option<&'a str> {
    arg_values(args, needle).next()
}
