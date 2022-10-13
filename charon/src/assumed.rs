//! This file contains information about the assumed functions/types/traits definitions
//! TODO: rename to "primitive"
//!
//! **IMPORTANT**:
//! When checking whether names are equal to one of the reference names below,
//! we ignore the disambiguators (see [names] and [names_utils]).
#![allow(dead_code)]

use crate::ullbc_ast;
use crate::names::*;
use crate::types;

// Assumed types
pub static BOX_NAME: [&str; 3] = ["alloc", "boxed", "Box"];
pub static VEC_NAME: [&str; 3] = ["alloc", "vec", "Vec"];
pub static OPTION_NAME: [&str; 3] = ["core", "option", "Option"];

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

// Vectors
pub static VEC_NEW_NAME: [&str; 4] = ["alloc", "vec", "Vec", "new"];
pub static VEC_PUSH_NAME: [&str; 4] = ["alloc", "vec", "Vec", "push"];
pub static VEC_INSERT_NAME: [&str; 4] = ["alloc", "vec", "Vec", "insert"];
pub static VEC_LEN_NAME: [&str; 4] = ["alloc", "vec", "Vec", "len"];
// This is a trait: for now we assume it is only used on vectors
pub static INDEX_NAME: [&str; 5] = ["core", "ops", "index", "Index", "index"];
// This is a trait: for now we assume it is only used on vectors
pub static INDEX_MUT_NAME: [&str; 5] = ["core", "ops", "index", "IndexMut", "index_mut"];

// We ignore this trait, which is implicitly given to all the type parameters
pub static MARKER_SIZED_NAME: [&str; 3] = ["core", "marker", "Sized"];

/// We redefine identifiers for assumed functions here, instead of reusing the
/// identifiers from [ullbc_ast], because some of the functions (the panic functions)
/// will actually not be translated to functions: there are thus missing identifiers.
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
    VecNew,
    VecPush,
    VecInsert,
    VecLen,
    VecIndex,
    VecIndexMut,
}

pub fn get_type_id_from_name(name: &TypeName) -> Option<types::AssumedTy> {
    if name.equals_ref_name(&BOX_NAME) {
        Option::Some(types::AssumedTy::Box)
    } else if name.equals_ref_name(&VEC_NAME) {
        Option::Some(types::AssumedTy::Vec)
    } else if name.equals_ref_name(&OPTION_NAME) {
        Option::Some(types::AssumedTy::Option)
    } else {
        Option::None
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
        Option::Some(FunId::VecIndex)
    } else if name.equals_ref_name(&INDEX_MUT_NAME) {
        Option::Some(FunId::VecIndexMut)
    } else {
        Option::None
    }
}

pub fn get_fun_id_from_name(name: &FunName) -> Option<ullbc_ast::AssumedFunId> {
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
                FunId::VecIndex => ullbc_ast::AssumedFunId::VecIndex,
                FunId::VecIndexMut => ullbc_ast::AssumedFunId::VecIndexMut,
            };
            Option::Some(id)
        }
        Option::None => Option::None,
    }
}

/// We ignore some type parameters, for some assumed types.
/// For instance, many types like box or vec are parameterized by an allocator
/// (`std::alloc::Allocator`): we ignore it, because it is not useful to reason
/// about the functional behaviour.
pub fn type_to_used_params(name: &TypeName) -> Option<Vec<bool>> {
    trace!("{}", name);
    match get_type_id_from_name(name) {
        Option::None => Option::None,
        Option::Some(id) => {
            let id = match id {
                types::AssumedTy::Box => {
                    vec![true, false]
                }
                types::AssumedTy::Vec => {
                    vec![true, false]
                }
                types::AssumedTy::Option => {
                    vec![true]
                }
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
                FunId::VecIndex => FunInfo {
                    // The second type parameter is for the index type (`usize` for vectors)
                    used_type_params: vec![true, false],
                    used_args: vec![true, true],
                },
                FunId::VecIndexMut => FunInfo {
                    // The second type parameter is for the index type (`usize` for vectors)
                    used_type_params: vec![true, false],
                    used_args: vec![true, true],
                },
            };
            Option::Some(info)
        }
    }
}
