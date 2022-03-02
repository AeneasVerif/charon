mod hashmap;
mod hashmap_utils;

use crate::hashmap::*;
use crate::hashmap_utils::*;

#[allow(dead_code)]
fn insert_on_disk(key: Key, value: u64) {
    // Deserialize
    let mut hm = deserialize_from_disk();
    // Update
    hm.insert(key, value);
    // Serialize
    serialize_to_disk(hm);
}

#[allow(dead_code)]
fn main() {}
