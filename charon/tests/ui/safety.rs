//@ revisions=built,promoted,elaborated,optimized
//@[built] charon-args=--mir built
//@[promoted] charon-args=--mir promoted
//@[elaborated] charon-args=--mir elaborated
//@[optimized] charon-args=--mir optimized
//@ rustc-args=--target x86_64-unknown-linux-gnu
//@ charon-args=--print-safety --opaque test_crate::Opaque --exclude test_crate::excluded
//@ charon-args=--exclude test_crate::ExcludedUnsafeTrait
#![feature(
    core_intrinsics,
    stmt_expr_attributes,
    effective_target_features,
    negative_impls,
    dropck_eyepatch
)]

struct S;
unsafe trait UnsafeTrait {}
trait SafeTrait {}
unsafe impl UnsafeTrait for S {}
impl SafeTrait for S {}
impl !Send for S {}
unsafe trait ExcludedUnsafeTrait {}
unsafe impl ExcludedUnsafeTrait for S {}
struct MayDangle<T>(T);
unsafe impl<#[may_dangle] T> Drop for MayDangle<T> {
    fn drop(&mut self) {}
}
unsafe fn unsafe_fn() {}

unsafe extern "C" {
    fn extern_fn();
    static EXTERN_STATIC: u32;
    safe fn safe_extern_fn();
    safe static SAFE_EXTERN_STATIC: u32;
}

#[unsafe(no_mangle)]
fn no_mangle() {}
#[unsafe(export_name = "exported")]
fn export_name() {}
#[unsafe(link_section = ".text.custom")]
fn link_section() {}
#[unsafe(naked)]
extern "C" fn naked() {
    core::arch::naked_asm!("ret")
}
#[unsafe(force_target_feature(enable = "avx"))]
fn force_target_feature() {}

fn safe_fn() {}

static mut COUNTER: usize = 0;
#[derive(Clone, Copy)]
union Foo {
    one: u64,
    two: [u32; 2],
}
union Bar {
    foo: Foo,
}
unsafe fn dangerous() {}
trait Trait {
    unsafe fn unsafe_method();
    fn safe_method();
}
trait DynTrait {
    unsafe fn unsafe_method(&self);
    fn safe_method(&self);
}

fn unsafe_deref_raw_ptr(x: *const u32) -> u32 {
    unsafe { *x }
}
fn unsafe_call_fn() {
    unsafe { dangerous() }
}
fn unsafe_call_method<T: Trait>() {
    unsafe { T::unsafe_method() }
}
fn unsafe_call_fn_ptr(f: unsafe fn()) {
    unsafe { f() }
}
fn unsafe_read_mutable_static() -> usize {
    unsafe { COUNTER }
}
fn unsafe_write_mutable_static() {
    unsafe { COUNTER = 1 }
}
fn unsafe_read_extern_static() -> u32 {
    unsafe { EXTERN_STATIC }
}
static mut PAIR: (u32, u32) = (0, 0);
fn unsafe_raw_borrow_of_mutable_static_field() -> *const u32 {
    unsafe { &raw const PAIR.0 }
}
static mut PTR: *const u32 = std::ptr::null();
fn unsafe_raw_borrow_through_mutable_static() -> *const u32 {
    unsafe { &raw const *PTR }
}
fn unsafe_read_union_field(foo: Foo) -> u64 {
    unsafe { foo.one }
}
fn unsafe_asm() {
    unsafe { core::arch::asm!("nop") }
}
fn unsafe_call_unsafe_dyn_method(s: &dyn DynTrait) {
    unsafe { s.unsafe_method() }
}
fn unsafe_raw_borrow_of_indexed_union_field(foo: Foo) -> *const u32 {
    unsafe { &raw const foo.two[0] }
}
static mut STATIC_FOO: Foo = Foo { one: 0 };
fn unsafe_raw_borrow_of_mutable_static_union_field() -> *const u64 {
    unsafe { &raw const STATIC_FOO.one }
}

// These intrinsics get lowered to MIR operations in the optimized MIR.
fn unsafe_builtins(x: u32, p: *const u32, s: &[u32], i: usize) {
    use std::intrinsics;
    unsafe {
        let _: i32 = intrinsics::transmute(x);
        let _: &u32 = intrinsics::slice_get_unchecked(s, i);
        let _ = intrinsics::unchecked_add(x, 1);
        let _ = intrinsics::offset(p, 1isize);
    }
}

fn safe_raw_ptrs(x: u32) -> (*const u32, *mut usize) {
    (&raw const x, &raw mut COUNTER)
}
fn safe_call(f: fn()) {
    f();
    safe_raw_ptrs(0);
}
fn safe_call_method<T: Trait>() {
    T::safe_method();
}
fn safe_build_union() -> Foo {
    Foo { one: 0 }
}
fn safe_write_union_field(mut foo: Foo) {
    foo.one = 1;
}
fn safe_write_nested_union_field(mut bar: Bar) {
    bar.foo.one = 1;
}
fn safe_read_safe_extern_static() -> u32 {
    SAFE_EXTERN_STATIC
}
fn safe_raw_borrow_of_extern_static() -> *const u32 {
    &raw const EXTERN_STATIC
}
fn safe_raw_borrow_of_deref(p: *const u32) -> *const u32 {
    &raw const *p
}
fn safe_raw_borrow_of_union_field(mut foo: Foo) -> (*const u64, *mut [u32; 2]) {
    (&raw const foo.one, &raw mut foo.two)
}
fn safe_raw_borrow_of_nested_union_field(bar: &Bar) -> *const u64 {
    &raw const bar.foo.one
}
#[unsafe(naked)]
extern "C" fn safe_naked_asm() {
    core::arch::naked_asm!("ret")
}
fn safe_call_dyn_method(s: &dyn DynTrait) {
    s.safe_method()
}
fn safe_drop_dyn(_s: Box<dyn DynTrait>) {}

// Target features.
#[target_feature(enable = "avx")]
fn with_feature() {}
#[target_feature(enable = "avx")]
unsafe fn with_feature_unsafe() {}
fn unsafe_call_target_feature_fn() {
    unsafe { with_feature() }
}
#[target_feature(enable = "avx")]
fn safe_call_target_feature_fn_with_feature() {
    with_feature()
}
#[target_feature(enable = "avx2")]
fn safe_call_target_feature_fn_with_implied_feature() {
    with_feature()
}
#[target_feature(enable = "avx")]
fn safe_call_target_feature_fn_in_closure() {
    (|| with_feature())()
}
#[target_feature(enable = "avx")]
fn safe_call_target_feature_fn_in_inline_closure() {
    (#[inline(always)]
    || with_feature())()
}
#[target_feature(enable = "avx")]
fn unsafe_call_unsafe_target_feature_fn() {
    unsafe { with_feature_unsafe() }
}
#[unsafe(force_target_feature(enable = "avx"))]
fn with_forced_feature() {}
fn unsafe_call_forced_target_feature_fn() {
    unsafe { with_forced_feature() }
}
#[target_feature(enable = "avx")]
fn safe_call_forced_target_feature_fn_with_feature() {
    with_forced_feature()
}

// When some information is missing, we can't tell whether an operation is unsafe.
union Opaque {
    one: u64,
    two: [u32; 2],
}
fn unknown_read_opaque_field(u: Opaque) -> u64 {
    unsafe { u.one }
}
unsafe fn excluded() {}
fn unknown_call_excluded() {
    unsafe { excluded() }
}
