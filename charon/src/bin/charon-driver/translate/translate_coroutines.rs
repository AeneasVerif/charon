//! Coroutines are the state machines behind `#[coroutine]` closures, `async` blocks and `gen`
//! blocks. For now we only translate them *after rustc has lowered them*:
//! the coroutine type becomes an enum with one variant per state, and the coroutine body becomes
//! a function that switches on the current state, runs until the next suspension point, and sets
//! the new state.
//!
//! For example, given:
//! ```ignore
//! fn foo(x: u8) -> impl Coroutine<Yield = u8, Return = ()> {
//!     #[coroutine]
//!     move || {
//!         let y = 1;
//!         yield x;
//!         yield y;
//!     }
//! }
//! ```
//!
//! We generate:
//! ```text
//! enum {closure} {
//!   Unresumed { _0: u8 },
//!   Returned { _0: u8 },
//!   Panicked { _0: u8 },
//!   Suspend0 { _0: u8, _s0: MaybeUninit<u8> },
//!   Suspend1 { _0: u8 },
//! }
//!
//! fn {closure}::resume<'a>(_1: Pin<&'a mut {closure}>, _2: ()) -> CoroutineState<u8, ()> {
//!     let _6 = _1.0;
//!     match *_6 {
//!         Unresumed => {}
//!         Suspend0 => { ...; _4 = ((*_6) as Suspend0)._s0.value.value; ... }
//!         ...
//!     }
//!     ((*_6) as Suspend0)._s0.value.value = 1;
//!     ...
//! }
//! ```
use crate::hax::{self, UnderOwnerState};
use rustc_hir as hir;
use rustc_middle::ty::{self, CoroutineArgsExt};

use super::translate_crate::TransItemSourceKind;
use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::ids::IndexVec;

pub fn translate_coroutine_kind(kind: hir::CoroutineKind) -> CoroutineKind {
    use hir::CoroutineDesugaring::*;
    match kind {
        hir::CoroutineKind::Coroutine(_) => CoroutineKind::Coroutine,
        hir::CoroutineKind::Desugared(Async, _) => CoroutineKind::Async,
        hir::CoroutineKind::Desugared(Gen, _) => CoroutineKind::Gen,
        hir::CoroutineKind::Desugared(AsyncGen, _) => CoroutineKind::AsyncGen,
    }
}

impl<'tcx> ItemTransCtx<'tcx, '_> {
    pub fn translate_coroutine_adt(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
        coroutine: &hax::Coroutine<'tcx>,
    ) -> Result<TypeDeclKind, Error> {
        let tcx = self.tcx;
        let ty = def.type_of(&self.hax_state).unwrap();
        let ty::Coroutine(def_id, args) = *ty.kind() else {
            unreachable!()
        };
        let Ok(layout) = tcx.coroutine_layout(def_id, args) else {
            raise_error!(self, span, "Could not compute the states of this coroutine")
        };

        let upvars: IndexVec<FieldId, Field> = coroutine
            .upvar_tys()
            .iter()
            .enumerate()
            .map(|(i, ty)| -> Result<Field, Error> {
                Ok(Field {
                    span,
                    attr_info: AttrInfo::dummy_private(),
                    name: format!("_{i}"),
                    is_positional: true,
                    ty: self.translate_ty(span, ty)?,
                })
            })
            .try_collect()?;

        let mut variants = IndexVec::new();
        for (variant_idx, saved_locals) in layout.variant_fields.iter_enumerated() {
            let mut fields = upvars.clone();
            for &local in saved_locals {
                // Use `MaybeUninit`: the local may be uninitialised
                let local_ty = hax::inst_binder(
                    tcx,
                    self.hax_state.typing_env(),
                    Some(args),
                    ty::EarlyBinder::bind(tcx, layout.field_tys[local].ty),
                );
                let ty = ty::Ty::new_maybe_uninit(tcx, local_ty);
                fields.push(Field {
                    span,
                    attr_info: AttrInfo::dummy_private(),
                    name: format!("_s{}", local.as_usize()),
                    is_positional: true,
                    ty: self.translate_rustc_ty(span, &ty)?,
                });
            }
            let discr = args
                .as_coroutine()
                .discriminant_for_variant(def_id, tcx, variant_idx);
            let discr_ty = self.translate_rustc_ty(span, &discr.ty)?;
            let discr_ty = *discr_ty.kind().as_scalar().unwrap().as_integer().unwrap();
            variants.push_with(|id| Variant {
                id,
                span,
                attr_info: AttrInfo::dummy_public(),
                name: ty::CoroutineArgs::variant_name(variant_idx).into_owned(),
                fields,
                discriminant: IntegerValue::from_bits(discr_ty, discr.val),
            });
        }
        Ok(TypeDeclKind::Enum(variants))
    }

    pub fn translate_coroutine_info(
        &mut self,
        span: Span,
        def: &hax::FullDef<'tcx>,
    ) -> Result<CoroutineInfo, Error> {
        let hax::FullDefKind::Coroutine(coroutine) = def.kind() else {
            unreachable!()
        };
        Ok(CoroutineInfo {
            kind: translate_coroutine_kind(coroutine.kind()),
            resume: self.translate_item(span, def.this(), TransItemSourceKind::CoroutineResume)?,
        })
    }

    /// If this trait proof is the built-in impl of `Coroutine`, `Future`, `Iterator` or
    /// `AsyncIterator` for a coroutine, return the coroutine. The returned item has its regions
    /// erased.
    pub fn recognize_coroutine_impl_proof(
        &self,
        trait_proof: &hax::TraitProof<'tcx>,
    ) -> Option<hax::ItemRef<'tcx>> {
        use hax::SolverTraitLangItem as Trait;
        let hax::TraitProofKind::Builtin {
            trait_data:
                hax::BuiltinTraitData::Other(
                    Trait::Coroutine | Trait::Future | Trait::Iterator | Trait::AsyncIterator,
                ),
            ..
        } = &trait_proof.kind
        else {
            return None;
        };
        // We skip the binder and erase regions to avoid bound vars escaping.
        let hax::GenericArg::Type(self_ty) = trait_proof
            .pred
            .hax_skip_binder_ref()
            .generic_args
            .first()?
        else {
            return None;
        };
        let hax::TyKind::Coroutine(coroutine) = self_ty.kind() else {
            return None;
        };
        Some(coroutine.item.erase(self.hax_state_with_id()))
    }

    /// Translate a reference to the method that resumes this coroutine. The binder binds the
    /// late-bound lifetimes of the method.
    fn translate_coroutine_resume_bound_ref(
        &mut self,
        span: Span,
        coroutine: &hax::ItemRef<'tcx>,
    ) -> Result<RegionBinder<FunDeclRef>, Error> {
        let dref: DeclRef<ItemId> =
            self.translate_item(span, coroutine, TransItemSourceKind::CoroutineResume)?;
        let def = self.hax_def(coroutine)?;
        let hax::FullDefKind::Coroutine(c) = def.kind() else {
            unreachable!()
        };
        let sig = &c.resume_method(self.hax_state()).sig;
        self.translate_region_binder(span, sig, |ctx, _| {
            let mut dref = dref.move_under_binder();
            // The late-bound regions of the resume method come last.
            for (a, b) in dref.generics.regions.iter_mut().rev().zip(
                ctx.innermost_binder()
                    .params
                    .identity_args()
                    .regions
                    .into_iter()
                    .rev(),
            ) {
                *a = b;
            }
            Ok(dref.try_into().unwrap())
        })
    }

    /// Translate the function that resumes a coroutine.
    #[tracing::instrument(skip(self, item_meta))]
    pub fn translate_coroutine_resume(
        mut self,
        def_id: FunDeclId,
        item_meta: ItemMeta,
        def: &hax::FullDef<'tcx>,
    ) -> Result<FunDecl, Error> {
        let span = item_meta.span;
        let hax::FullDefKind::Coroutine(coroutine) = def.kind() else {
            unreachable!()
        };
        let method = coroutine.resume_method(self.hax_state());
        let signature = self.translate_fun_sig(span, &method.sig.value)?;
        let body = if item_meta.opacity.with_private_contents().is_opaque() {
            Body::Opaque
        } else {
            self.translate_def_body(span, def)
        };
        Ok(FunDecl {
            def_id,
            item_meta,
            generics: self.into_generics(),
            signature: Box::new(signature),
            src: FunSource::Normal,
            body,
        })
    }

    /// In mono mode, a call to the method of the built-in trait impl of a coroutine (e.g.
    /// `Future::poll` for an `async` block) becomes a call to the function that resumes the
    /// coroutine.
    pub(crate) fn translate_coroutine_resume_fn_ptr(
        &mut self,
        span: Span,
        item: &hax::ItemRef<'tcx>,
    ) -> Result<Option<RegionBinder<FnPtr>>, Error> {
        if !self.monomorphize() {
            return Ok(None);
        }
        let Some(in_trait) = &item.in_trait else {
            return Ok(None);
        };
        let Some(coroutine) = self.recognize_coroutine_impl_proof(in_trait) else {
            return Ok(None);
        };
        // The other methods of these traits are default methods.
        let def = self.hax_def(&coroutine)?;
        let hax::FullDefKind::Coroutine(c) = def.kind() else {
            unreachable!()
        };
        if item.def_id != c.resume_method(self.hax_state()).def_id {
            return Ok(None);
        }
        let bound_ref = self.translate_coroutine_resume_bound_ref(span, &coroutine)?;
        Ok(Some(bound_ref.map(|fn_ref| {
            FnPtr::new(FnPtrKind::Fun(fn_ref.id), fn_ref.generics)
        })))
    }
}
