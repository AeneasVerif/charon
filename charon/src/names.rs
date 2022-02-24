//! Defines some utilities for the variables
#![allow(dead_code)]

use macros::generate_index_type;
use serde::{Serialize, Serializer};

generate_index_type!(ImplId);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    name: Vec<String>,
}

impl Name {
    pub fn from(name: Vec<String>) -> Name {
        Name { name: name }
    }

    pub fn to_vec(self) -> Vec<String> {
        self.name
    }

    pub fn len(&self) -> usize {
        self.name.len()
    }

    /// Compare the name to a constant array
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        if self.name.len() != ref_name.len() {
            return false;
        }

        for i in 0..self.name.len() {
            if self.name[i] != ref_name[i] {
                return false;
            }
        }
        return true;
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.name.join("::"))
    }
}

impl Serialize for Name {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use crate::common::*;
        let name = VecSerializer::new(&self.name);
        name.serialize(serializer)
    }
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

fn module_ident_equals_ref_name(module: &Name, ident: &String, ref_name: &[&str]) -> bool {
    if module.len() + 1 != ref_name.len() {
        return false;
    }

    for i in 0..module.len() {
        if module.name[i] != ref_name[i] {
            return false;
        }
    }
    let i = module.len();
    return ident == ref_name[i];
}

impl FunName {
    /// Compare the name to a constant array
    pub fn equals_ref_name(&self, ref_name: &[&str]) -> bool {
        match self {
            FunName::Regular(name) => name.equals_ref_name(ref_name),
            FunName::Impl(type_name, _impl_id, ident) => {
                // TODO: we ignore the impl id, which is not good
                // At some point, we will have to make some of the primitive
                // functions (the ones for the vectors, more specifically)
                // non-primitive, and always return false in this branch.
                module_ident_equals_ref_name(type_name, ident, ref_name)
            }
        }
    }
}

impl std::fmt::Display for FunName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            FunName::Regular(name) => {
                write!(f, "{}", name)
            }
            FunName::Impl(type_name, impl_id, ident) => {
                write!(f, "{}{{{}}}::{}", type_name, impl_id, ident)
            }
        }
    }
}
