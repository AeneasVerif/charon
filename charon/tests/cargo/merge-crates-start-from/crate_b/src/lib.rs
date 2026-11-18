pub fn entry() -> u32 {
    crate_a::used()
}

/// Not reachable from the start-from items.
pub fn not_started_from() -> u32 {
    crate_a::unused()
}

pub struct Thing;

/// Started from by a pattern whose implemented type is in `crate_b`.
impl crate_a::Describe for Thing {
    fn describe(&self) -> u32 {
        1
    }
}
