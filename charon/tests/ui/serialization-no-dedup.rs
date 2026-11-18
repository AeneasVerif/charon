//@ no-default-options
//@ charon-args=--no-dedup-serialized-ast

// Exercise JSON and Postcard round-trips without deduplication.
pub fn repeated_types(x: (u32, u32)) -> (u32, u32) {
    x
}
