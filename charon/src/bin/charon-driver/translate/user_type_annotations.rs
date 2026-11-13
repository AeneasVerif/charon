//! Recover the type annotations provided by the user inside a body.
use itertools::Itertools;
use rustc_hash::FxHashMap as HashMap;
use rustc_middle::{mir, ty};

use super::translate_crate::RustcItem;
use super::translate_ctx::*;
use crate::hax;
use charon_lib::ast::*;

struct UserTypeAnnotation {
    projections: HashMap<Vec<mir::ProjectionKind>, Ty>,
}

/// User-provided type annotations for this MIR body.
pub(crate) struct UserTypeAnnotations {
    annotations: rustc_index::IndexVec<ty::UserTypeAnnotationIndex, UserTypeAnnotation>,
    pub outlives: Vec<OutlivesPred>,
}

impl UserTypeAnnotations {
    /// Translate the annotations for this body. The returned value can then be used to fetch the
    /// types of annotations.
    pub(crate) fn new<'tcx>(
        ctx: &mut ItemTransCtx<'tcx, '_>,
        body: &mir::Body<'tcx>,
    ) -> Result<Self, Error> {
        use mir::visit::Visitor as _;

        let mut annotations = body.user_type_annotations.clone();
        if let RustcItem::Mono(item) = &ctx.item_src.item {
            // `CanonicalUserTypeAnnotation::user_ty` is deliberately not folded when rustc
            // instantiates a MIR body, so do the item substitution explicitly.
            let item = item.clone();
            let args = item.rustc_args(ctx.hax_state_with_id());
            for annotation in &mut annotations {
                annotation.user_ty.value = hax::substitute(
                    ctx.tcx,
                    hax::UnderOwnerState::typing_env(&ctx.hax_state),
                    Some(args),
                    annotation.user_ty.value,
                );
            }
        }

        let mut recovered = Self {
            annotations: Default::default(),
            outlives: Vec::new(),
        };
        if annotations.is_empty() {
            return Ok(recovered);
        }

        // Gather the projections on user annotations that are actually used. Unused annotation
        // types can reference items like intrinsics that have already been lowered away.
        struct CollectProjections(
            rustc_index::IndexVec<
                ty::UserTypeAnnotationIndex,
                SeqHashSet<Vec<mir::ProjectionKind>>,
            >,
        );
        impl<'tcx> mir::visit::Visitor<'tcx> for CollectProjections {
            fn visit_user_type_projection(&mut self, projection: &mir::UserTypeProjection) {
                self.0[projection.base].insert(projection.projs.clone());
            }

            fn visit_const_operand(
                &mut self,
                operand: &mir::ConstOperand<'tcx>,
                location: mir::Location,
            ) {
                if let Some(base) = operand.user_ty {
                    self.0[base].insert(vec![]);
                }
                self.super_const_operand(operand, location);
            }

            fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: mir::Location) {
                if let mir::Rvalue::Aggregate(kind, _) = rvalue
                    && let mir::AggregateKind::Adt(_, _, _, Some(base), _) = **kind
                {
                    self.0[base].insert(vec![]);
                }
                self.super_rvalue(rvalue, location);
            }
        }
        let mut projections =
            CollectProjections(annotations.iter().map(|_| SeqHashSet::default()).collect());
        projections.visit_body(body);
        for (base, projections) in projections.0.into_iter_enumerated() {
            let annotation = &annotations[base];
            let span = ctx.translate_span(&annotation.span);
            let projections = projections.into_iter().collect_vec();
            let (tys, outlives) = translate_user_annotation(ctx, span, annotation, &projections)?;
            let annotation = UserTypeAnnotation {
                projections: projections.into_iter().zip_eq(tys).collect(),
            };
            assert_eq!(recovered.annotations.push(annotation), base);
            recovered.outlives.extend(outlives);
        }
        recovered.outlives.sort_unstable();
        recovered.outlives.dedup();
        Ok(recovered)
    }

    /// Get the type of this local and the constraints from its type annotations.
    pub(crate) fn translate_local_ty<'tcx>(
        &self,
        ctx: &mut ItemTransCtx<'tcx, '_>,
        span: Span,
        local_id: LocalId,
        decl: &mir::LocalDecl<'tcx>,
    ) -> Result<(Ty, Vec<PlaceTypeConstraint>), Error> {
        let ty = ctx.translate_rustc_ty(span, &decl.ty)?;
        let mut constraints = Vec::new();
        if let Some(user_tys) = &decl.user_ty
            && user_tys.projections().len() != 0
        {
            let outer_ref = if decl.is_nonref_binding() {
                None
            } else {
                // In `let ref x: T`, the annotation describes the pointer target. We grab the
                // appropriate region by using the normal type of the local.
                let TyKind::Ref(region, _, kind) = ty.kind() else {
                    raise_error!(ctx, span, "ref binding has non-reference type");
                };
                Some((region.clone(), *kind))
            };

            let annotated_tys = user_tys
                .projections()
                .map(|pj| self.translate_projected_annotation(pj))
                .map(|ty| {
                    if let Some((region, kind)) = &outer_ref {
                        TyKind::Ref(region.clone(), ty, *kind).into()
                    } else {
                        ty
                    }
                });
            for annotated_ty in annotated_tys {
                constraints.push(PlaceTypeConstraint {
                    place: Place::new(local_id, ty.clone()),
                    ty: annotated_ty,
                    variance: Variance::Covariant,
                });
            }
        }
        Ok((ty, constraints))
    }

    /// Look up the (unprojected) type of an annotation.
    pub(crate) fn translate_annotation(&self, index: ty::UserTypeAnnotationIndex) -> Option<Ty> {
        if self.annotations.is_empty() {
            None
        } else {
            Some(self.annotations[index].projections[&[][..]].clone())
        }
    }

    /// Look up the type of an annotation.
    pub(crate) fn translate_projected_annotation(
        &self,
        projection: &mir::UserTypeProjection,
    ) -> Ty {
        let annotation = &self.annotations[projection.base];
        annotation.projections[projection.projs.as_slice()].clone()
    }
}

/// Translate a user annotation and the outlives obligations needed to validate it.
fn translate_user_annotation<'tcx>(
    ctx: &mut ItemTransCtx<'tcx, '_>,
    span: Span,
    annotation: &ty::CanonicalUserTypeAnnotation<'tcx>,
    projections: &[hax::rustc::UserAnnotationProj],
) -> Result<(Vec<Ty>, Vec<OutlivesPred>), Error> {
    let Some(owner) = ctx.item_src.def_id().as_real_or_promoted() else {
        raise_error!(ctx, span, "user type annotation without a rustc owner");
    };
    let ty_constraints = hax::rustc::translate_user_annotation(
        ctx.tcx,
        hax::UnderOwnerState::typing_env(&ctx.hax_state),
        owner,
        annotation,
        projections,
    );
    let ty_constraints = match ty_constraints {
        Ok(ty_constraints) => ty_constraints,
        Err(message) => raise_error!(ctx, span, "{message}"),
    };
    let ty_constraints: hax::Binder<(Vec<hax::Ty<'tcx>>, Vec<hax::Clause<'tcx>>)> =
        ctx.catch_sinto(span, &ty_constraints)?;
    let bound_constraints =
        ctx.translate_region_binder(span, &ty_constraints, |ctx, (tys, clauses)| {
            let tys: Vec<Ty> = tys
                .iter()
                .map(|ty| ctx.translate_ty(span, ty))
                .try_collect()?;
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
                        _ => unreachable!("recovered ascription contains a non-region constraint"),
                    })
                })?;
                outlives.push(pred.no_bound_vars());
            }
            Ok((tys, outlives))
        })?;
    // Instantiate the binder with fresh body regions.
    let (tys, outlives) = ctx.erase_region_binder(bound_constraints);
    let outlives = outlives.iter().flat_map(|pred| pred.normalize()).collect();
    Ok((tys, outlives))
}
