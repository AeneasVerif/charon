//@ no-check-output
#![feature(never_type)]

use std::num::NonZero;

struct SimpleStruct {
    x: u32,
    y: u32,
    z: u32,
}

struct GenericStruct<T> {
    a: usize,
    b: T,
}

struct UnsizedStruct {
    x: usize,
    y: [usize],
}

struct UnsizedDyn {
    x: u8,
    y: dyn std::fmt::Debug,
}

struct NestedUnsized {
    x: u16,
    y: UnsizedStruct,
}

#[repr(packed(2))]
struct PackedUnsized {
    x: u8,
    y: [u32],
}

enum SimpleEnum {
    Var1,
    Other,
}

enum SimpleAdt {
    EmptyVar,
    StructVar { x: usize, y: usize },
    TupleVar(u32, u32),
}

enum NicheAdt {
    None,
    Some(NonZero<u32>),
}

enum NicheAdtSigned {
    None,
    Some(NonZero<i32>),
}

enum NicheAdtChar {
    None,
    Some(char),
}

struct IsAZST;

struct GenericWithKnownLayout<T> {
    x: usize,
    y: Box<T>,
}

// Rust reorders the fields to save space.
struct Reordered {
    x: u8,
    y: u32,
    z: u8,
}

// `repr(C)` prevents reordering the fields.
#[repr(C)]
struct NotReordered {
    x: u8,
    y: u32,
    z: u8,
}

#[repr(packed)]
struct Packed {
    x: u8,
    y: u32,
    z: u8,
}

enum UninhabitedVariant {
    A(!),
    B(u32),
}

enum UninhabitedVariant2 {
    A(!, u32),
    B(u32),
}

enum UninhabitedVariantWithFields {
    Bar,
    Baz { x: u32, y: !, z: u32 },
}

struct Uninhabited(!);

enum DiscriminantInNicheOfField<'a, T> {
    None,
    Some((usize, &'a T)),
}

union MaybeUninitInt {
    x: u32,
    y: (),
}

union PackIntsUnion {
    x: (u32, u32),
    y: u64,
}

enum NonZeroNiche {
    A(char),
    B,
    C,
}

#[repr(i32)]
enum ArbitraryDiscriminants {
    A(String) = 12,
    B(u32) = 43,
    C = 123456,
}

#[repr(i8)]
enum MyOrder {
    Less = -1,
    Equal = 0,
    Greater = 1,
}

enum WithNicheAndUninhabited {
    First,
    Second(!),
    Third(NonZero<u32>),
}

enum GenericUnsized<'a, T: ?Sized> {
    First,
    Second(&'a T),
}

enum GenericButFixedSize<'a, T: Sized> {
    First,
    Second(&'a T),
}

#[repr(u128)]
enum MaxBitsDiscr {
    First = 42,
    Second = 18446744073709551615,
}

type SingleVariantButNonZero = Result<!, ()>;

type NonAdtAlias<T> = T;

type Tuple = (u32, u32);

type Usize = usize;

type Str = str;

type Ref<'a> = &'a mut u32;

// See https://github.com/AeneasVerif/charon/issues/1046 : reading 3 is UB
enum HasInvalidDiscr {
    Var1,       // variant 0, tag 2
    Var2(bool), // variant 1, untagged (valid values are 0=false and 1=true)
    Var3,       // variant 2, tag 4
}

// Signed tag: the niche is -2, and the valid range -2..=1 wraps around in bits
// (0xFE..=0x01). Values outside -2..=1 are invalid.
enum NicheInSignedRepr {
    A(MyOrder),
    B,
}

// Has a niche at offset 8
#[repr(C)]
struct BigWithChar {
    a: u64,
    c: char,
}

// The uninhabited variant `A` still gets a reserved niche value (0x110000), which must
// not be attributed to the untagged variant `C`!
enum UninhabitedAtNicheEdge {
    A(u32, !),
    B,
    C(BigWithChar),
}

// The untagged variant is uninhabited: reading any non-niche value is UB.
enum UninhabitedUntagged {
    A(char, !),
    B,
}
