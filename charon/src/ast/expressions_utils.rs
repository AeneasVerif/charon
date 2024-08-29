//! This file groups everything which is linked to implementations about [crate::expressions]
use crate::ast::*;

impl Place {
    pub fn new(var_id: VarId) -> Place {
        Place {
            var_id,
            projection: Vec::new(),
        }
    }
}

impl BorrowKind {
    pub fn mutable(x: bool) -> Self {
        if x {
            Self::Mut
        } else {
            Self::Shared
        }
    }
}
