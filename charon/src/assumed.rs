//! This file contains information about the assumed functions/types/traits definitions
//!
//! **IMPORTANT**:
//! When checking whether names are equal to one of the reference names below,
//! we ignore the disambiguators (see [crate::names] and [crate::names_utils]).
// TODO: rename to "primitive"
#![allow(dead_code)]

use crate::names::*;
use crate::types;
use crate::ullbc_ast;
use macros::EnumIsA;

/// Ignore the builtin/auto traits like [core::marker::Sized] or [core::marker::Sync].
pub const IGNORE_BUILTIN_MARKER_TRAITS: bool = true;

// Ignored traits (includes marker traits, and others)
pub static SIZED_NAME: [&str; 3] = ["core", "marker", "Sized"];
pub static SYNC_NAME: [&str; 3] = ["core", "marker", "SYNC"];
pub static SEND_NAME: [&str; 3] = ["core", "marker", "SEND"];
pub static UNPIN_NAME: [&str; 3] = ["core", "marker", "UNPIN"];
pub static ALLOC_ALLOCATOR: [&str; 3] = ["core", "alloc", "Allocator"];
pub static IGNORED_TRAITS_NAMES: [&[&str]; 5] = [
    &SIZED_NAME,
    &SYNC_NAME,
    &SEND_NAME,
    &UNPIN_NAME,
    &ALLOC_ALLOCATOR,
];

// Assumed types
pub static BOX_NAME: [&str; 3] = ["alloc", "boxed", "Box"];
pub static VEC_NAME: [&str; 3] = ["alloc", "vec", "Vec"];
pub static OPTION_NAME: [&str; 3] = ["core", "option", "Option"];
pub static RANGE_NAME: [&str; 4] = ["core", "ops", "range", "Range"];

pub static OPTION_NONE_VARIANT_ID: types::VariantId::Id = types::VariantId::ZERO;
pub static OPTION_SOME_VARIANT_ID: types::VariantId::Id = types::VariantId::ONE;

//
// Assumed functions/traits
//
pub static PANIC_NAME: [&str; 3] = ["core", "panicking", "panic"];
pub static BEGIN_PANIC_NAME: [&str; 3] = ["std", "panicking", "begin_panic"];
pub static REPLACE_NAME: [&str; 3] = ["core", "mem", "replace"];

// Boxes
pub static BOX_NEW_NAME: [&str; 4] = ["alloc", "boxed", "Box", "new"];
// This is a trait: for now we assume it is only used on boxes
pub static DEREF_DEREF_NAME: [&str; 5] = ["core", "ops", "deref", "Deref", "deref"];
// This is a trait: for now we assume it is only used on boxes
pub static DEREF_DEREF_MUT_NAME: [&str; 5] = ["core", "ops", "deref", "DerefMut", "deref_mut"];
pub static BOX_FREE_NAME: [&str; 3] = ["alloc", "alloc", "box_free"];

// Index traits
pub static INDEX_NAME: [&str; 5] = ["core", "ops", "index", "Index", "index"];
pub static INDEX_MUT_NAME: [&str; 5] = ["core", "ops", "index", "IndexMut", "index_mut"];

// Slices
pub static SLICE_LEN_NAME: [&str; 4] = ["core", "slice", "[T]", "len"]; // TODO: fix the `[T]` name element

// Vectors
pub static VEC_NEW_NAME: [&str; 4] = ["alloc", "vec", "Vec", "new"];
pub static VEC_PUSH_NAME: [&str; 4] = ["alloc", "vec", "Vec", "push"];
pub static VEC_INSERT_NAME: [&str; 4] = ["alloc", "vec", "Vec", "insert"];
pub static VEC_LEN_NAME: [&str; 4] = ["alloc", "vec", "Vec", "len"];

// Pointers
pub static PTR_UNIQUE_NAME: [&str; 3] = ["core", "ptr", "Unique"];
pub static PTR_NON_NULL_NAME: [&str; 3] = ["core", "ptr", "NonNull"];

// We ignore this trait, which is automatically added for some type parameters
// when defining a new type.
pub static MARKER_SIZED_NAME: [&str; 3] = ["core", "marker", "Sized"];

/// We redefine identifiers for assumed functions here, instead of reusing the
/// identifiers from [ullbc_ast], because:
/// - some of the functions (the panic functions) will actually not be translated
///   to functions: there are thus missing identifiers.
/// - some of the ids here are actually traits, that we disambiguate later
/// TODO: merge with the other enum?
#[derive(EnumIsA)]
enum FunId {
    /// `core::panicking::panic`
    Panic,
    /// `std::panicking::begin_panic`
    BeginPanic,
    Replace,
    BoxNew,
    BoxDeref,
    BoxDerefMut,
    BoxFree,
    /// `index` function of the `Index` trait
    Index,
    /// `index_mut` function of the `IndexMut` trait
    IndexMut,
    SliceLen,
    VecNew,
    VecPush,
    VecInsert,
    VecLen,
}

pub fn is_marker_trait(name: &Name) -> bool {
    for n in IGNORED_TRAITS_NAMES {
        if name.equals_ref_name(n) {
            return true;
        }
    }
    false
}

pub fn get_type_id_from_name(name: &TypeName) -> Option<types::AssumedTy> {
    if name.equals_ref_name(&BOX_NAME) {
        Option::Some(types::AssumedTy::Box)
    } else if name.equals_ref_name(&RANGE_NAME) {
        Option::Some(types::AssumedTy::Range)
    } else if name.equals_ref_name(&VEC_NAME) {
        Option::Some(types::AssumedTy::Vec)
    } else if name.equals_ref_name(&OPTION_NAME) {
        Option::Some(types::AssumedTy::Option)
    } else if name.equals_ref_name(&PTR_UNIQUE_NAME) {
        Option::Some(types::AssumedTy::PtrUnique)
    } else if name.equals_ref_name(&PTR_NON_NULL_NAME) {
        Option::Some(types::AssumedTy::PtrNonNull)
    } else {
        Option::None
    }
}

pub fn get_name_from_type_id(id: types::AssumedTy) -> Vec<String> {
    use types::AssumedTy;
    match id {
        AssumedTy::Box => BOX_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::Range => RANGE_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::Vec => VEC_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::Option => OPTION_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::PtrUnique => PTR_UNIQUE_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::PtrNonNull => PTR_NON_NULL_NAME.iter().map(|s| s.to_string()).collect(),
        AssumedTy::Str => vec!["Str".to_string()],
        AssumedTy::Array => vec!["Array".to_string()],
        AssumedTy::Slice => vec!["Slice".to_string()],
    }
}

fn get_fun_id_from_name_full(name: &FunName) -> Option<FunId> {
    if name.equals_ref_name(&PANIC_NAME) {
        Option::Some(FunId::Panic)
    } else if name.equals_ref_name(&BEGIN_PANIC_NAME) {
        Option::Some(FunId::BeginPanic)
    } else if name.equals_ref_name(&REPLACE_NAME) {
        Option::Some(FunId::Replace)
    } else if name.equals_ref_name(&BOX_NEW_NAME) {
        Option::Some(FunId::BoxNew)
    } else if name.equals_ref_name(&DEREF_DEREF_NAME) {
        Option::Some(FunId::BoxDeref)
    } else if name.equals_ref_name(&DEREF_DEREF_MUT_NAME) {
        Option::Some(FunId::BoxDerefMut)
    } else if name.equals_ref_name(&BOX_FREE_NAME) {
        Option::Some(FunId::BoxFree)
    } else if name.equals_ref_name(&VEC_NEW_NAME) {
        Option::Some(FunId::VecNew)
    } else if name.equals_ref_name(&VEC_PUSH_NAME) {
        Option::Some(FunId::VecPush)
    } else if name.equals_ref_name(&VEC_INSERT_NAME) {
        Option::Some(FunId::VecInsert)
    } else if name.equals_ref_name(&VEC_LEN_NAME) {
        Option::Some(FunId::VecLen)
    } else if name.equals_ref_name(&INDEX_NAME) {
        Option::Some(FunId::Index)
    } else if name.equals_ref_name(&INDEX_MUT_NAME) {
        Option::Some(FunId::IndexMut)
    } else if name.equals_ref_name(&SLICE_LEN_NAME) {
        Option::Some(FunId::SliceLen)
    } else {
        Option::None
    }
}

pub fn get_fun_id_from_name(
    name: &FunName,
    type_args: &Vec<types::ETy>,
) -> Option<ullbc_ast::AssumedFunId> {
    match get_fun_id_from_name_full(name) {
        Option::Some(id) => {
            let id = match id {
                FunId::Panic | FunId::BeginPanic => unreachable!(),
                FunId::Replace => ullbc_ast::AssumedFunId::Replace,
                FunId::BoxNew => ullbc_ast::AssumedFunId::BoxNew,
                FunId::BoxDeref => ullbc_ast::AssumedFunId::BoxDeref,
                FunId::BoxDerefMut => ullbc_ast::AssumedFunId::BoxDerefMut,
                FunId::BoxFree => ullbc_ast::AssumedFunId::BoxFree,
                FunId::VecNew => ullbc_ast::AssumedFunId::VecNew,
                FunId::VecPush => ullbc_ast::AssumedFunId::VecPush,
                FunId::VecInsert => ullbc_ast::AssumedFunId::VecInsert,
                FunId::VecLen => ullbc_ast::AssumedFunId::VecLen,
                FunId::SliceLen => ullbc_ast::AssumedFunId::SliceLen,
                FunId::Index | FunId::IndexMut => {
                    assert!(type_args.len() == 1);
                    use types::*;

                    // Indexing into an array (pointer arithmetic + dereference) is represented in MIR
                    // by an Offset projector followed by a Deref operation.
                    //
                    // Here, we see the Index trait on arrays, which does NOT mean indexing into an
                    // array (like above). Instead, it refers to a particular implementation that
                    // demands that the index be a Range<usize>, and that returns a Slice. See:
                    // - https://doc.rust-lang.org/src/core/array/mod.rs.html#340
                    // - https://doc.rust-lang.org/src/core/slice/index.rs.html#11
                    // - https://doc.rust-lang.org/src/core/slice/index.rs.html#350
                    match type_args[0] {
                        Ty::Adt(TypeId::Assumed(aty), ..) => {
                            // TODO: figure out whether indexing into a slice
                            // (i.e. bounds-check, pointer arithmetic, dereference) also
                            // appears as an implementation of the Index trait or as a
                            // primitive operation like array indexing.
                            match aty {
                                types::AssumedTy::Vec => {
                                    if id.is_index() {
                                        ullbc_ast::AssumedFunId::VecIndex
                                    } else {
                                        // mut case
                                        ullbc_ast::AssumedFunId::VecIndexMut
                                    }
                                }
                                types::AssumedTy::Array => {
                                    if id.is_index() {
                                        ullbc_ast::AssumedFunId::ArraySubsliceShared
                                    } else {
                                        // mut case
                                        ullbc_ast::AssumedFunId::ArraySubsliceMut
                                    }
                                }
                                types::AssumedTy::Slice => {
                                    if id.is_index() {
                                        ullbc_ast::AssumedFunId::SliceSubsliceShared
                                    } else {
                                        // mut case
                                        ullbc_ast::AssumedFunId::SliceSubsliceMut
                                    }
                                }
                                _ => unimplemented!("ty: {:?}", aty),
                            }
                        }
                        _ => unimplemented!(),
                    }
                }
            };
            Option::Some(id)
        }
        Option::None => Option::None,
    }
}

/// When translating from MIR to ULLBC, we ignore some type parameters for some
/// assumed types.
/// For instance, many types like box or vec are parameterized (in MIR) by an allocator
/// (`std::alloc::Allocator`): we ignore it.
pub fn type_to_used_params(name: &TypeName) -> Option<Vec<bool>> {
    trace!("{}", name);
    match get_type_id_from_name(name) {
        Option::None => Option::None,
        Option::Some(id) => {
            use types::AssumedTy;
            let id = match id {
                AssumedTy::Box => {
                    vec![true, false]
                }
                AssumedTy::Vec => {
                    vec![true, false]
                }
                AssumedTy::Option => {
                    vec![true]
                }
                AssumedTy::PtrUnique | AssumedTy::PtrNonNull => {
                    vec![true]
                }
                AssumedTy::Str => {
                    vec![]
                }
                AssumedTy::Range => {
                    vec![true]
                }
                AssumedTy::Array | AssumedTy::Slice => vec![true],
            };
            Option::Some(id)
        }
    }
}

pub struct FunInfo {
    pub used_type_params: Vec<bool>,
    // TODO: rename. "value_args"?
    pub used_args: Vec<bool>,
}

/// See the comments for [type_to_used_params]
pub fn function_to_info(name: &FunName) -> Option<FunInfo> {
    trace!("{}", name);
    match get_fun_id_from_name_full(name) {
        Option::None => Option::None,
        Option::Some(id) => {
            let info = match id {
                FunId::Panic => FunInfo {
                    used_type_params: vec![],
                    used_args: vec![true],
                },
                FunId::BeginPanic => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true],
                },
                FunId::Replace => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true, true],
                },
                FunId::BoxNew => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true],
                },
                FunId::BoxDeref => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true],
                },
                FunId::BoxDerefMut => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true],
                },
                FunId::BoxFree => FunInfo {
                    used_type_params: vec![true, false],
                    used_args: vec![true, false],
                },
                FunId::VecNew => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![],
                },
                FunId::VecPush => FunInfo {
                    used_type_params: vec![true, false],
                    used_args: vec![true, true],
                },
                FunId::VecInsert => FunInfo {
                    used_type_params: vec![true, false],
                    used_args: vec![true, true, true],
                },
                FunId::VecLen => FunInfo {
                    used_type_params: vec![true, false],
                    used_args: vec![true],
                },
                FunId::SliceLen => FunInfo {
                    used_type_params: vec![true],
                    used_args: vec![true],
                },
                FunId::Index => FunInfo {
                    // The second type parameter is for the index type (`usize` for vectors)
                    used_type_params: vec![true, false],
                    used_args: vec![true, true],
                },
                FunId::IndexMut => FunInfo {
                    // The second type parameter is for the index type (`usize` for vectors)
                    used_type_params: vec![true, false],
                    used_args: vec![true, true],
                },
            };
            Option::Some(info)
        }
    }
}
