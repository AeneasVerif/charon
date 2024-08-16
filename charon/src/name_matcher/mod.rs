use itertools::{EitherOrBoth, Itertools};
use serde::{Deserialize, Serialize};

use crate::ast::*;

mod parser;

pub use Pattern as NamePattern;

#[derive(Clone, Serialize, Deserialize)]
pub struct Pattern {
    elems: Vec<PatElem>,
}

#[derive(Clone, Serialize, Deserialize)]
enum PatElem {
    /// An identifier, optionally with generic arguments. E.g. `std` or `Box<_>`.
    Ident {
        name: String,
        generics: Vec<PatTy>,
        /// For pretty-printing only: whether this is the name of a trait.
        is_trait: bool,
    },
    /// An inherent or trait implementation block. For traits, the implemented type is the first
    /// element of the pattern generics.
    Impl(Box<Pattern>),
    /// A `*` or `_`.
    Glob,
}

#[derive(Clone, Serialize, Deserialize)]
enum PatTy {
    /// A path, like `my_crate::foo::Type<_, usize>`
    Pat(Pattern),
    /// `&T`, `&mut T`
    Ref(RefKind, Box<Self>),
}

impl Pattern {
    pub fn parse(i: &str) -> Result<Self, nom_supreme::error::ErrorTree<String>> {
        use std::str::FromStr;
        Self::from_str(i)
    }

    pub fn matches(&self, ctx: &TranslatedCrate, name: &Name) -> bool {
        self.matches_with_generics(ctx, name, &GenericArgs::empty())
    }

    pub fn matches_with_generics(
        &self,
        ctx: &TranslatedCrate,
        name: &Name,
        args: &GenericArgs,
    ) -> bool {
        let zipped = self.elems.iter().zip_longest(&name.name).collect_vec();
        let zipped_len = zipped.len();
        for (i, x) in zipped.into_iter().enumerate() {
            let is_last = i + 1 == zipped_len;
            match x {
                EitherOrBoth::Both(pat, elem) => {
                    let args = if is_last { args } else { &GenericArgs::empty() };
                    if !pat.matches_with_generics(ctx, elem, args) {
                        return false;
                    }
                }
                // The pattern is shorter than the scrutinee and the previous elements match: we
                // count that as matching.
                EitherOrBoth::Right(_) => return true,
                // The pattern is longer than the scrutinee; they don't match.
                EitherOrBoth::Left(_) => return false,
            }
        }
        // Both had the same length and all the elements matched.
        true
    }

    pub fn matches_ty(&self, ctx: &TranslatedCrate, ty: &Ty) -> bool {
        if let [PatElem::Glob] = self.elems.as_slice() {
            return true;
        }
        match ty {
            Ty::Adt(TypeId::Adt(type_id), args) => {
                let Some(decl) = ctx.type_decls.get(*type_id) else {
                    return false;
                };
                self.matches_with_generics(ctx, &decl.item_meta.name, args)
            }
            Ty::Adt(TypeId::Assumed(assumed_ty), args) => {
                let name = assumed_ty.get_name();
                self.matches_with_generics(ctx, &name, args)
            }
            Ty::Adt(TypeId::Tuple, _)
            | Ty::TypeVar(_)
            | Ty::Literal(_)
            | Ty::Never
            | Ty::Ref(_, _, _)
            | Ty::RawPtr(_, _)
            | Ty::TraitType(_, _)
            | Ty::DynTrait(_)
            | Ty::Arrow(_, _, _) => false,
        }
    }

    pub fn matches_const(&self, _ctx: &TranslatedCrate, _c: &ConstGeneric) -> bool {
        if let [PatElem::Glob] = self.elems.as_slice() {
            return true;
        }
        todo!("non-trivial const generics patterns aren't implemented")
    }
}

impl PatElem {
    fn matches_with_generics(
        &self,
        ctx: &TranslatedCrate,
        elem: &PathElem,
        args: &GenericArgs,
    ) -> bool {
        match (self, elem) {
            (PatElem::Glob, _) => true,
            (
                PatElem::Ident {
                    name: pat_ident,
                    generics,
                    ..
                },
                PathElem::Ident(ident, _),
            ) => pat_ident == ident && PatTy::matches_generics(ctx, generics, args),
            (PatElem::Impl(_pat), PathElem::Impl(ImplElem::Ty(_, _ty), _)) => {
                todo!()
            }
            (PatElem::Impl(pat), PathElem::Impl(ImplElem::Trait(impl_id), _)) => {
                let Some(timpl) = ctx.trait_impls.get(*impl_id) else {
                    return false;
                };
                let Some(tdecl) = ctx.trait_decls.get(timpl.impl_trait.trait_id) else {
                    return false;
                };
                pat.matches_with_generics(ctx, &tdecl.item_meta.name, &timpl.impl_trait.generics)
            }
            _ => false,
        }
    }
}

impl PatTy {
    pub fn matches_generics(ctx: &TranslatedCrate, pats: &[Self], generics: &GenericArgs) -> bool {
        // We don't include regions in patterns.
        if pats.len() != generics.types.len() + generics.const_generics.len() {
            return false;
        }
        let (type_pats, const_pats) = pats.split_at(generics.types.len());
        let types_match = generics
            .types
            .iter()
            .zip(type_pats)
            .all(|(ty, pat)| pat.matches_ty(ctx, ty));
        let consts_match = generics
            .const_generics
            .iter()
            .zip(const_pats)
            .all(|(c, pat)| pat.matches_const(ctx, c));
        types_match && consts_match
    }

    pub fn matches_ty(&self, ctx: &TranslatedCrate, ty: &Ty) -> bool {
        match (self, ty) {
            (PatTy::Pat(p), _) => p.matches_ty(ctx, ty),
            (PatTy::Ref(pat_mtbl, p_ty), Ty::Ref(_, ty, ty_mtbl)) => {
                pat_mtbl == ty_mtbl && p_ty.matches_ty(ctx, ty)
            }
            _ => false,
        }
    }

    pub fn matches_const(&self, ctx: &TranslatedCrate, c: &ConstGeneric) -> bool {
        match self {
            PatTy::Pat(p) => p.matches_const(ctx, c),
            PatTy::Ref(..) => false,
        }
    }
}
