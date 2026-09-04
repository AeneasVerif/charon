//! Deduplication of repeated values in the serialized output.
//!
//! Note that the deduplication scheme is order-dependent: it relies on the fact that
//! serialization and deserialization traverse the value in the same order.

use indexmap::IndexMap as SeqHashMap;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use serde_state::{DeserializeState, SerializeState};
use std::any::type_name;
use std::cell::RefCell;
use std::hash::Hash;

use crate::utils::type_map::{Mappable, Mapper, TypeMap};

/// Identifies a deduplicated value amongst the values of its type within a single serialized
/// output. Ids are allocated in the order in which we serialize the values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DedupId(u32);

/// A value that we deduplicate in the serialized output. We identify values by equality, hence
/// the bounds.
pub trait Dedup: Mappable + Clone + Eq + Hash {}
impl<T> Dedup for T where T: Mappable + Clone + Eq + Hash {}

/// The state threaded through (de)serialization to deduplicate values. Use `()` to serialize
/// values normally and [`DedupSerializer`] to deduplicate them.
pub trait DedupSerializerState: Sized {
    /// Record that we're serializing this value. Returns `None` if we're not deduplicating
    /// values, `Some(Ok(id))` the first time we meet a given value (it must then be serialized
    /// in full), and `Some(Err(id))` afterwards (only the id must be serialized).
    fn record_serialized<T: Dedup>(&self, value: &T) -> Option<Result<DedupId, DedupId>>;
    /// Record that we deserialized the value with this id.
    fn record_deserialized<T: Dedup>(&self, id: DedupId, value: T);
    /// Find the previously-deserialized value with that id.
    fn get_deserialized<T: Dedup>(&self, id: DedupId) -> Option<T>;
}

/// Don't deduplicate anything.
impl DedupSerializerState for () {
    fn record_serialized<T: Dedup>(&self, _value: &T) -> Option<Result<DedupId, DedupId>> {
        None
    }
    fn record_deserialized<T: Dedup>(&self, _id: DedupId, _value: T) {}
    fn get_deserialized<T: Dedup>(&self, _id: DedupId) -> Option<T> {
        None
    }
}

struct SerializeTableMapper;
impl Mapper for SerializeTableMapper {
    type Value<T: Mappable> = FxHashMap<T, DedupId>;
}
struct DeserializeTableMapper;
impl Mapper for DeserializeTableMapper {
    type Value<T: Mappable> = SeqHashMap<DedupId, T>;
}

/// Deduplicate the values of each type, in one table per type.
#[derive(Default)]
pub struct DedupSerializer {
    // Table used for serialization: the values we've already emitted, with the id we gave them.
    ser: RefCell<TypeMap<SerializeTableMapper>>,
    // Table used for deserialization: the values we've read so far, by id.
    de: RefCell<TypeMap<DeserializeTableMapper>>,
}

impl DedupSerializerState for DedupSerializer {
    fn record_serialized<T: Dedup>(&self, value: &T) -> Option<Result<DedupId, DedupId>> {
        let mut ser = self.ser.borrow_mut();
        let table = ser.or_default::<T>();
        Some(match table.get(value) {
            Some(&id) => Err(id),
            None => {
                let id = DedupId(table.len() as u32);
                table.insert(value.clone(), id);
                Ok(id)
            }
        })
    }
    fn record_deserialized<T: Dedup>(&self, id: DedupId, value: T) {
        self.de.borrow_mut().or_default::<T>().insert(id, value);
    }
    fn get_deserialized<T: Dedup>(&self, id: DedupId) -> Option<T> {
        self.de
            .borrow()
            .get::<T>()
            .and_then(|table| table.get(&id))
            .cloned()
    }
}

/// How we represent a deduplicated value in the serialized output. `T` is the serialized form of
/// the value.
#[derive(Serialize, Deserialize, SerializeState, DeserializeState)]
#[serde_state(state_implements = DedupSerializerState)]
pub enum SerDedup<T> {
    /// A value represented normally, accompanied by its id. This is emitted the first time we
    /// serialize a given value: subsequent times will use `SerDedup::Deduplicated` instead.
    Value(#[serde_state(stateless)] DedupId, T),
    /// A value represented by its id. The actual value must have been emitted as a
    /// `SerDedup::Value` with that same id earlier.
    #[serde_state(stateless)]
    Deduplicated(DedupId),
    /// A plain value without an id, emitted when we're not deduplicating.
    Untagged(T),
}

/// Serialize `value`, deduplicating it if the state says so. `repr` is the serialized form of
/// `value`, only used the first time we meet it.
pub fn serialize_dedup<T, R, State, S>(
    value: &T,
    repr: R,
    state: &State,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    T: Dedup,
    R: SerializeState<State>,
    State: DedupSerializerState,
    S: serde::Serializer,
{
    let repr = match state.record_serialized(value) {
        Some(Ok(id)) => SerDedup::Value(id, repr),
        Some(Err(id)) => SerDedup::Deduplicated(id),
        None => SerDedup::Untagged(repr),
    };
    repr.serialize_state(state, serializer)
}

/// Deserialize a value that may have been deduplicated. `build` reconstructs the value from its
/// serialized form.
pub fn deserialize_dedup<'de, T, R, State, D>(
    state: &State,
    deserializer: D,
    build: impl FnOnce(R) -> T,
) -> Result<T, D::Error>
where
    T: Dedup,
    R: DeserializeState<'de, State>,
    State: DedupSerializerState,
    D: serde::Deserializer<'de>,
{
    use serde::de::Error;
    Ok(
        match SerDedup::<R>::deserialize_state(state, deserializer)? {
            SerDedup::Value(id, repr) => {
                let value = build(repr);
                state.record_deserialized(id, value.clone());
                value
            }
            SerDedup::Deduplicated(id) => state.get_deserialized(id).ok_or_else(|| {
                let msg = format!(
                    "can't deserialize deduplicated value of type {}; \
                were you careful with managing the deduplication state?",
                    type_name::<T>()
                );
                D::Error::custom(msg)
            })?,
            SerDedup::Untagged(repr) => build(repr),
        },
    )
}

/// The error we report when a deduplicated value is deserialized with serde's stateless
/// `Deserialize` impl, which can't resolve the ids.
pub fn stateless_deserialize_error<T>() -> String {
    format!(
        "trying to deserialize a deduplicated value using serde's `{ty}::deserialize` method. \
        This won't work, use serde_state's \
        `{ty}::deserialize_state(&DedupSerializer::default(), _)` instead",
        ty = type_name::<T>(),
    )
}
