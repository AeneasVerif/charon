//! Implementations for [crate::gast]

use crate::gast::*;
use crate::names::Name;
use crate::types::*;
use crate::values::*;
use rustc_hir::def_id::DefId;

/// Iterate on the declarations' non-empty bodies with their corresponding name and type.
/// TODO: generalize this with visitors
pub fn iter_function_bodies<T>(
    funs: &mut FunDeclId::Map<GFunDecl<T>>,
) -> impl Iterator<Item = (DefId, &Name, &mut GExprBody<T>)> {
    funs.iter_mut().flat_map(|f| match f.body.as_mut() {
        None => None, // Option::map was complaining about borrowing f
        Some(b) => Some((f.rust_id, &f.name, b)),
    })
}

/// Iterate on the declarations' non-empty bodies with their corresponding name and type.
/// Same as [iter_function_bodies] (but the `flat_map` lambda cannot be generic).
/// TODO: generalize this with visitors
pub fn iter_global_bodies<T>(
    globals: &mut GlobalDeclId::Map<GGlobalDecl<T>>,
) -> impl Iterator<Item = (DefId, &Name, &mut GExprBody<T>)> {
    globals.iter_mut().flat_map(|g| match g.body.as_mut() {
        None => None, // Option::map was complaining about borrowing g
        Some(b) => Some((g.rust_id, &g.name, b)),
    })
}

/// Makes a lambda that generates a new variable id, pushes a new variable in
/// the body locals with the given type and returns its id.
pub fn make_locals_generator(locals: &mut VarId::Vector<Var>) -> impl FnMut(Ty) -> VarId::Id + '_ {
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
