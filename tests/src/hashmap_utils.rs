#![allow(dead_code)]

use crate::hashmap::*;

/// Serialize a hash map - we don't have traits, so we fix the type of the
/// values (this is not the interesting part anyway)
pub(crate) fn serialize_to_disk(_hm: HashMap<u64>) {
    unimplemented!();
}
/// Deserialize a hash map - we don't have traits, so we fix the type of the
/// values (this is not the interesting part anyway)
pub(crate) fn deserialize_from_disk() -> HashMap<u64> {
    unimplemented!();
}
