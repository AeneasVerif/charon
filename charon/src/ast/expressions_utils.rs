//! This file groups everything which is linked to implementations about [crate::expressions]
use crate::expressions::*;
use std::vec::Vec;

impl Place {
    pub fn new(var_id: VarId) -> Place {
        Place {
            var_id,
            projection: Vec::new(),
        }
    }
}
