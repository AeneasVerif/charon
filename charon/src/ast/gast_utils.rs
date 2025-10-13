//! Implementations for [crate::gast]

use crate::ast::*;
use crate::llbc_ast;
use crate::ullbc_ast;

impl FnPtrKind {
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

    pub fn locals(&self) -> &Locals {
        match self {
            Body::Structured(body) => &body.locals,
            Body::Unstructured(body) => &body.locals,
        }
    }
}

impl Locals {
    pub fn new(arg_count: usize) -> Self {
        Self {
            arg_count,
            locals: Default::default(),
        }
    }

    /// Creates a new variable and returns a place pointing to it.
    /// Warning: don't forget to `StorageLive` it before using it.
    pub fn new_var(&mut self, name: Option<String>, ty: Ty) -> Place {
        let local_id = self.locals.push_with(|index| Local {
            index,
            name,
            ty: ty.clone(),
        });
        Place::new(local_id, ty)
    }

    /// Gets a place pointing to the corresponding variable.
    pub fn place_for_var(&self, local_id: LocalId) -> Place {
        let ty = self.locals[local_id].ty.clone();
        Place::new(local_id, ty)
    }

    /// Returns whether this local is the special return local or one of the input argument locals.
    pub fn is_return_or_arg(&self, lid: LocalId) -> bool {
        lid.index() <= self.arg_count
    }

    /// The place where we write the return value.
    pub fn return_place(&self) -> Place {
        self.place_for_var(LocalId::new(0))
    }

    /// Locals that aren't arguments or return values.
    pub fn non_argument_locals(&self) -> impl Iterator<Item = (LocalId, &Local)> {
        self.locals.iter_indexed().skip(1 + self.arg_count)
    }
}

impl std::ops::Index<LocalId> for Locals {
    type Output = Local;
    fn index(&self, local_id: LocalId) -> &Self::Output {
        &self.locals[local_id]
    }
}
impl std::ops::IndexMut<LocalId> for Locals {
    fn index_mut(&mut self, local_id: LocalId) -> &mut Self::Output {
        &mut self.locals[local_id]
    }
}

impl TraitDecl {
    pub fn methods(&self) -> impl Iterator<Item = &Binder<TraitMethod>> {
        self.methods.iter()
    }
}
impl TraitImpl {
    pub fn methods(&self) -> impl Iterator<Item = &(TraitItemName, Binder<FunDeclRef>)> {
        self.methods.iter()
    }
}

impl Binder<TraitAssocTy> {
    pub fn name(&self) -> &TraitItemName {
        &self.skip_binder.name
    }
}
impl Binder<TraitMethod> {
    pub fn name(&self) -> &TraitItemName {
        &self.skip_binder.name
    }
}
