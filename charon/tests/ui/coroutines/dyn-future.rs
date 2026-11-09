//@ revisions=poly,mono
//@ charon-args=--mir elaborated --include core::future::future::Future
//@[mono] charon-args=--monomorphize
use std::future::Future;
use std::pin::Pin;

// We don't support the vtables of coroutines yet; this used to panic.
fn boxed() -> Pin<Box<dyn Future<Output = u32>>> {
    Box::pin(async { 1 })
}
