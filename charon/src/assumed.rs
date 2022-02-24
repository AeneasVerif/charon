//! This file contains information about the assumed functions/types/traits definitions
#![allow(dead_code)]

use crate::im_ast;
use crate::names::Name;
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

/// We redefine identifiers for assumed functions here, instead of reusing the
/// identifiers from [im_ast], because some of the functions (the panic functions)
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

pub fn get_type_id_from_name(name: &Name) -> types::AssumedTy {
    if name.equals_ref_name(&BOX_NAME) {
        types::AssumedTy::Box
    } else if name.equals_ref_name(&VEC_NAME) {
        types::AssumedTy::Vec
    } else if name.equals_ref_name(&OPTION_NAME) {
        types::AssumedTy::Option
    } else {
        error!("Unsupported non-local type: {}", name);
        panic!("Unsupported non-local type: {}", name)
    }
}

fn get_fun_id_from_name_full(name: &Name) -> FunId {
    if name.equals_ref_name(&PANIC_NAME) {
        FunId::Panic
    } else if name.equals_ref_name(&BEGIN_PANIC_NAME) {
        FunId::BeginPanic
    } else if name.equals_ref_name(&REPLACE_NAME) {
        FunId::Replace
    } else if name.equals_ref_name(&BOX_NEW_NAME) {
        FunId::BoxNew
    } else if name.equals_ref_name(&DEREF_DEREF_NAME) {
        FunId::BoxDeref
    } else if name.equals_ref_name(&DEREF_DEREF_MUT_NAME) {
        FunId::BoxDerefMut
    } else if name.equals_ref_name(&BOX_FREE_NAME) {
        FunId::BoxFree
    } else if name.equals_ref_name(&VEC_NEW_NAME) {
        FunId::VecNew
    } else if name.equals_ref_name(&VEC_PUSH_NAME) {
        FunId::VecPush
    } else if name.equals_ref_name(&VEC_INSERT_NAME) {
        FunId::VecInsert
    } else if name.equals_ref_name(&VEC_LEN_NAME) {
        FunId::VecLen
    } else if name.equals_ref_name(&INDEX_NAME) {
        FunId::VecIndex
    } else if name.equals_ref_name(&INDEX_MUT_NAME) {
        FunId::VecIndexMut
    } else {
        error!("Unsupported non-local function: {}", name);
        panic!("Unsupported non-local function: {}", name)
    }
}

pub fn get_fun_id_from_name(name: &Name) -> im_ast::AssumedFunId {
    match get_fun_id_from_name_full(name) {
        FunId::Panic | FunId::BeginPanic => unreachable!(),
        FunId::Replace => im_ast::AssumedFunId::Replace,
        FunId::BoxNew => im_ast::AssumedFunId::BoxNew,
        FunId::BoxDeref => im_ast::AssumedFunId::BoxDeref,
        FunId::BoxDerefMut => im_ast::AssumedFunId::BoxDerefMut,
        FunId::BoxFree => im_ast::AssumedFunId::BoxFree,
        FunId::VecNew => im_ast::AssumedFunId::VecNew,
        FunId::VecPush => im_ast::AssumedFunId::VecPush,
        FunId::VecInsert => im_ast::AssumedFunId::VecInsert,
        FunId::VecLen => im_ast::AssumedFunId::VecLen,
        FunId::VecIndex => im_ast::AssumedFunId::VecIndex,
        FunId::VecIndexMut => im_ast::AssumedFunId::VecIndexMut,
    }
}

/// We ignore some type parameters, for some assumed types.
/// For instance, many types like box or vec are parameterized by an allocator
/// (`std::alloc::Allocator`): we ignore it, because it is not useful to reason
/// about the functional behaviour.
pub fn type_to_used_params(name: &Name) -> Vec<bool> {
    trace!("{}", name);
    match get_type_id_from_name(name) {
        types::AssumedTy::Box => {
            vec![true, false]
        }
        types::AssumedTy::Vec => {
            vec![true, false]
        }
        types::AssumedTy::Option => {
            vec![true]
        }
    }
}

pub struct FunInfo {
    pub used_type_params: Vec<bool>,
    pub used_args: Vec<bool>,
}

/// See the comments for [type_to_used_params]
pub fn function_to_info(name: &Name) -> FunInfo {
    trace!("{}", name);
    match get_fun_id_from_name_full(name) {
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
    }
}
