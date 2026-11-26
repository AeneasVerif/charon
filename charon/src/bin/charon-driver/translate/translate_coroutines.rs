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

use super::translate_crate::{TransImplSource, TransItemSourceKind, VirtualImplKind};
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
        let kind = translate_coroutine_kind(coroutine.kind());
        let vkind = VirtualImplKind::Coroutine(kind);
        Ok(CoroutineInfo {
            kind,
            resume: self.translate_item(
                span,
                def.this(),
                TransItemSourceKind::VirtualMethod(vkind),
            )?,
            trait_impl: self.translate_item(
                span,
                def.this(),
                TransItemSourceKind::TraitImpl(TransImplSource::Virtual(vkind)),
            )?,
        })
    }
}
