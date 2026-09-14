//@ charon-args=--monomorphize
enum Never {}

enum MyResult<T, E> {
    Ok(T),
    Err(E),
}

// This gives an enum with a single variant that doesn't have `VariantId` 0, which caused a crash.
fn use_result(_: MyResult<Never, u8>) {}

// This gives an enum with no inhabited variants.
fn use_uninhabited_result(_: MyResult<Never, Never>) {}
