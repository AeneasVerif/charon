//! Implementations for [crate::gast]

use crate::ast::*;
use crate::llbc_ast;
use crate::ullbc_ast;

impl FunIdOrTraitMethodRef {
    pub fn mk_builtin(aid: BuiltinFunId) -> Self {
        Self::Fun(FunId::Builtin(aid))
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

impl Locals {
    /// Creates a new variable and returns a place pointing to it.
    pub fn new_var(&mut self, name: Option<String>, ty: Ty) -> Place {
        let var_id = self.vars.push_with(|index| Var { index, name, ty });
        Place::new(var_id)
    }

    /// Gets a place pointing to the corresponding variable.
    pub fn place_for_var(&self, var_id: VarId) -> Place {
        Place::new(var_id)
    }

    /// The place where we write the return value.
    pub fn return_place(&self) -> Place {
        self.place_for_var(VarId::new(0))
    }
}

impl std::ops::Index<VarId> for Locals {
    type Output = Var;
    fn index(&self, var_id: VarId) -> &Self::Output {
        &self.vars[var_id]
    }
}
