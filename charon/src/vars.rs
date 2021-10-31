//! Defines some utilities for the variables
#![allow(dead_code)]

use serde::Serialize;

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Name {
    name: Vec<String>,
}

impl Name {
    pub fn from(name: Vec<String>) -> Name {
        Name { name: name }
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
