//! Implementations for [crate::gast]

use crate::ast::*;
use crate::ids::Vector;
use crate::llbc_ast;
use crate::ullbc_ast;

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
    pub fn mk_assumed(aid: AssumedFunId) -> Self {
        Self::Fun(FunId::Assumed(aid))
    }
}

impl Body {
    pub fn as_unstructured(&self) -> Option<&ullbc_ast::ExprBody> {
        if let Self::Unstructured(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_unstructured_mut(&mut self) -> Option<&mut ullbc_ast::ExprBody> {
        if let Self::Unstructured(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_structured(&self) -> Option<&llbc_ast::ExprBody> {
        if let Self::Structured(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_structured_mut(&mut self) -> Option<&mut llbc_ast::ExprBody> {
        if let Self::Structured(v) = self {
            Some(v)
        } else {
            None
        }
    }
}
