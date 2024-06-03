//! Implementations for [crate::gast]

use crate::gast::*;
use crate::ids::Vector;
use crate::types::*;
use crate::values::*;

/// Makes a lambda that generates a new variable id, pushes a new variable in
/// the body locals with the given type and returns its id.
pub fn make_locals_generator(locals: &mut Vector<VarId, Var>) -> impl FnMut(Ty) -> VarId + '_ {
    move |ty| {
        locals.push_with(|index| Var {
            index,
            name: None,
            ty,
        })
    }
}

impl FunIdOrTraitMethodRef {
    pub(crate) fn mk_assumed(aid: AssumedFunId) -> Self {
        Self::Fun(FunId::Assumed(aid))
    }
}
