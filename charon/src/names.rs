//! Defines some utilities for the variables
#![allow(dead_code)]

pub use crate::names_utils::*;
use macros::generate_index_type;
use serde::Serialize;

generate_index_type!(ImplId);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    pub name: Vec<String>,
}

pub type ModuleName = Name;
pub type TypeName = Name;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub enum FunName {
    /// "Regular" function name
    Regular(Name),
    /// The function comes from an "impl" block.
    /// As we may have several "impl" blocks for one type, we need to use
    /// a block id to disambiguate the functions (in rustc, this identifier
    /// is called a "disambiguator").
    Impl(TypeName, ImplId::Id, String),
}
