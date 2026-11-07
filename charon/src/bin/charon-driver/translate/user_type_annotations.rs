//! Recover the type annotations provided by the user inside a body.
use rustc_middle::{mir, ty};

use super::translate_crate::RustcItem;
use super::translate_ctx::*;
use crate::hax;
use charon_lib::ast::*;

/// User-provided type annotations for this MIR body.
pub(crate) struct UserTypeAnnotations<'tcx> {
    annotations: ty::CanonicalUserTypeAnnotations<'tcx>,
}

impl<'tcx> UserTypeAnnotations<'tcx> {
    pub(crate) fn new(ctx: &mut ItemTransCtx<'tcx, '_>, body: &mir::Body<'tcx>) -> Self {
        let mut user_type_annotations = body.user_type_annotations.clone();
        if let RustcItem::Mono(item) = &ctx.item_src.item {
            // `CanonicalUserTypeAnnotation::user_ty` is deliberately not folded when rustc
            // instantiates a MIR body, so do the item substitution explicitly.
            let item = item.clone();
            let args = item.rustc_args(ctx.hax_state_with_id());
            for annotation in &mut user_type_annotations {
                annotation.user_ty.value = hax::substitute(
                    ctx.tcx,
                    hax::UnderOwnerState::typing_env(&ctx.hax_state),
                    Some(args),
                    annotation.user_ty.value,
                );
            }
        }
        Self {
            annotations: user_type_annotations,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.annotations.is_empty()
    }

    /// Translate a user type annotation on a place. This returns the annotated type of the place,
    /// plus some outlive obligations that must hold for the annotation to be valid.
    pub(crate) fn translate_place_annotation(
        &self,
        ctx: &mut ItemTransCtx<'tcx, '_>,
        span: Span,
        user_ty: &mir::UserTypeProjection,
    ) -> Result<(Ty, Vec<OutlivesPred>), Error> {
        let Some(owner) = ctx.item_src.def_id().as_real_or_promoted() else {
            raise_error!(ctx, span, "user type annotation without a rustc owner");
        };
        let ty_constraints = hax::rustc::recover_user_type(
            ctx.tcx,
            hax::UnderOwnerState::typing_env(&ctx.hax_state),
            &self.annotations,
            owner,
            user_ty,
        );
        let ty_constraints = match ty_constraints {
            Ok(ty_constraints) => ty_constraints,
            Err(message) => raise_error!(ctx, span, "{message}"),
        };
        let ty_constraints: hax::Binder<(hax::Ty<'tcx>, Vec<hax::Clause<'tcx>>)> =
            ctx.catch_sinto(span, &ty_constraints)?;
        let bound_constraints =
            ctx.translate_region_binder(span, &ty_constraints, |ctx, (ty, clauses)| {
                let ty = ctx.translate_ty(span, ty)?;
                let mut outlives = Vec::new();
                for clause in clauses {
                    let pred = ctx.translate_region_binder(span, &clause.kind, |ctx, kind| {
                        Ok(match kind {
                            hax::ClauseKind::RegionOutlives(p) => OutlivesPred(
                                ctx.translate_region(span, &p.lhs)?,
                                ctx.translate_region(span, &p.rhs)?,
                            ),
                            hax::ClauseKind::TypeOutlives(p) => OutlivesPred(
                                Region::Lub(ctx.translate_ty(span, &p.lhs)?),
                                ctx.translate_region(span, &p.rhs)?,
                            ),
                            _ => unreachable!(
                                "recovered ascription contains a non-region constraint"
                            ),
                        })
                    })?;
                    outlives.push(pred.no_bound_vars());
                }
                Ok((ty, outlives))
            })?;
        // Instantiate the binder with fresh body regions.
        let (ty, outlives) = ctx.erase_region_binder(bound_constraints);
        Ok((ty, outlives))
    }
}
