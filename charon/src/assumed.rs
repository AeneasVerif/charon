//! This file contains information about the assumed functions/types/traits definitions
#![allow(dead_code)]

use crate::types;
use crate::vars::Name;

// Assumed types
pub static BOX_NAME: [&str; 3] = ["alloc", "boxed", "Box"];
pub static VEC_NAME: [&str; 3] = ["alloc", "vec", "Vec"];

// Assumed functions/traits
pub static PANIC_NAME: [&str; 3] = ["core", "panicking", "panic"];
pub static BEGIN_PANIC_NAME: [&str; 3] = ["std", "panicking", "begin_panic"];
pub static BOX_NEW_NAME: [&str; 4] = ["alloc", "boxed", "Box", "new"];
// This is a trait: for now we assume it is only used on boxes
pub static DEREF_DEREF_NAME: [&str; 5] = ["core", "ops", "deref", "Deref", "deref"];
// This is a trait: for now we assume it is only used on boxes
pub static DEREF_DEREF_MUT_NAME: [&str; 5] = ["core", "ops", "deref", "DerefMut", "deref_mut"];
pub static BOX_FREE_NAME: [&str; 3] = ["alloc", "alloc", "box_free"];

/// We ignore some type parameters, for some assumed types.
/// For instance, many types like box or vec are parameterized by an allocator
/// (`std::alloc::Allocator`): we ignore it, because it is not useful to reason
/// about the functional behaviour.
pub fn type_to_used_params(name: &Name) -> Vec<bool> {
    trace!("{}", name);
    if name.equals_ref_name(&BOX_NAME) {
        vec![true, false]
    } else if name.equals_ref_name(&VEC_NAME) {
        vec![true, false]
    } else {
        error!("Unsupported non-local type: {}", name);
        panic!("Unsupported non-local type: {}", name)
    }
}

/// See the comments for [type_to_used_params]
/// TODO: rename to get_used_type_params_from_name
pub fn function_to_used_type_params(name: &Name) -> Vec<bool> {
    trace!("{}", name);
    if name.equals_ref_name(&PANIC_NAME) {
        vec![]
    } else if name.equals_ref_name(&BEGIN_PANIC_NAME) {
        vec![true]
    } else if name.equals_ref_name(&BOX_NEW_NAME) {
        vec![true]
    } else if name.equals_ref_name(&DEREF_DEREF_NAME) {
        vec![true]
    } else if name.equals_ref_name(&DEREF_DEREF_MUT_NAME) {
        vec![true]
    } else if name.equals_ref_name(&BOX_FREE_NAME) {
        vec![true, false]
    } else {
        error!("Unsupported non-local function: {}", name);
        panic!("Unsupported non-local function: {}", name)
    }
}

/// See the comments for [type_to_used_params]
pub fn function_to_used_args(name: &Name) -> Vec<bool> {
    trace!("{}", name);
    if name.equals_ref_name(&PANIC_NAME) {
        vec![true]
    } else if name.equals_ref_name(&BEGIN_PANIC_NAME) {
        vec![true]
    } else if name.equals_ref_name(&BOX_NEW_NAME) {
        vec![true]
    } else if name.equals_ref_name(&DEREF_DEREF_NAME) {
        vec![true]
    } else if name.equals_ref_name(&DEREF_DEREF_MUT_NAME) {
        vec![true]
    } else if name.equals_ref_name(&BOX_FREE_NAME) {
        vec![true, false]
    } else {
        error!("Unsupported non-local function: {}", name);
        panic!("Unsupported non-local function: {}", name)
    }
}

pub fn get_type_id_from_name(name: &Name) -> types::AssumedTy {
    if name.equals_ref_name(&BOX_NAME) {
        types::AssumedTy::Box
    } else if name.equals_ref_name(&VEC_NAME) {
        types::AssumedTy::Vec
    } else {
        error!("Unsupported non-local type: {}", name);
        panic!("Unsupported non-local type: {}", name)
    }
}
