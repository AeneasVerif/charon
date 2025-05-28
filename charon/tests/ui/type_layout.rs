/// Will have size=12 and alignment = 4
struct StaticSize {
    x: u32,
    y: u32,
    z: u32
}

/// Will not have a statically determinable layout.
struct DynamicSize<T> {
    t: T,
    x: usize
}