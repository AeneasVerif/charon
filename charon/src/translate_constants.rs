//! Functions to translate constants to LLBC.
use crate::common::*;
use crate::gast::*;
use crate::translate_ctx::*;
use crate::types::*;
use crate::values::*;
use hax_frontend_exporter as hax;
use rustc_hir::def_id::DefId;

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn translate_constant_literal_to_raw_constant_expr(
        &mut self,
        span: rustc_span::Span,
        v: &hax::ConstantLiteral,
    ) -> Result<RawConstantExpr, Error> {
        let lit = match v {
            hax::ConstantLiteral::ByteStr(..) => {
                error_or_panic!(self, span, "byte str constants are not supported yet");
            }
            hax::ConstantLiteral::Char(c) => Literal::Char(*c),
            hax::ConstantLiteral::Bool(b) => Literal::Bool(*b),
            hax::ConstantLiteral::Int(i) => {
                use hax::ConstantInt;
                let scalar = match i {
                    ConstantInt::Int(v, int_type) => {
                        use hax::IntTy;
                        match int_type {
                            IntTy::Isize => ScalarValue::Isize(*v as i64),
                            IntTy::I8 => ScalarValue::I8(*v as i8),
                            IntTy::I16 => ScalarValue::I16(*v as i16),
                            IntTy::I32 => ScalarValue::I32(*v as i32),
                            IntTy::I64 => ScalarValue::I64(*v as i64),
                            IntTy::I128 => ScalarValue::I128(*v),
                        }
                    }
                    ConstantInt::Uint(v, int_type) => {
                        use hax::UintTy;
                        match int_type {
                            UintTy::Usize => ScalarValue::Usize(*v as u64),
                            UintTy::U8 => ScalarValue::U8(*v as u8),
                            UintTy::U16 => ScalarValue::U16(*v as u16),
                            UintTy::U32 => ScalarValue::U32(*v as u32),
                            UintTy::U64 => ScalarValue::U64(*v as u64),
                            UintTy::U128 => ScalarValue::U128(*v),
                        }
                    }
                };
                Literal::Scalar(scalar)
            }
        };
        Ok(RawConstantExpr::Literal(lit))
    }

    /// Remark: [hax::ConstantExpr] contains span information, but it is often
    /// the default span (i.e., it is useless), hence the additional span argument.
    /// TODO: the user_ty might be None because hax doesn't extract it (because
    /// we are translating a [ConstantExpr] instead of a [Constant]. We need to
    /// update hax.
    pub(crate) fn translate_constant_expr_to_constant_expr(
        &mut self,
        span: rustc_span::Span,
        user_ty: &Option<hax::UserTypeAnnotationIndex>,
        v: &hax::ConstantExpr,
    ) -> Result<ConstantExpr, Error> {
        use hax::ConstantExprKind;
        let ty = &v.ty;
        let erase_regions = true;
        let value = match &(*v.contents) {
            ConstantExprKind::Literal(lit) => {
                self.translate_constant_literal_to_raw_constant_expr(span, lit)?
            }
            ConstantExprKind::Adt { info, fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    // TODO: the user_ty is not always None
                    .map(|f| self.translate_constant_expr_to_constant_expr(span, &None, &f.value))
                    .try_collect()?;
                let vid = if info.typ_is_struct {
                    None
                } else {
                    Some(VariantId::Id::new(info.variant_index))
                };
                RawConstantExpr::Adt(vid, fields)
            }
            ConstantExprKind::Array { .. } => {
                error_or_panic!(self, span, "array constants are not supported yet")
            }
            ConstantExprKind::Tuple { fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    // TODO: the user_ty is not always None
                    .map(|f| self.translate_constant_expr_to_constant_expr(span, &None, f))
                    .try_collect()?;
                RawConstantExpr::Adt(Option::None, fields)
            }
            ConstantExprKind::TraitConst { impl_expr, name } => {
                let trait_ref = self.translate_trait_impl_expr(span, erase_regions, impl_expr)?;
                // The trait ref should be Some(...): trait markers (that we
                // may eliminate) don't have constants.
                let trait_ref = trait_ref.unwrap();
                let name = TraitItemName(name.clone());
                RawConstantExpr::TraitConst(trait_ref, name)
            }
            ConstantExprKind::GlobalName { id } => {
                RawConstantExpr::Global(self.translate_global_decl_id(span, DefId::from(id)))
            }
            ConstantExprKind::GlobalName { id } => {
                // The constant might have generics, in which case they are
                // provided by the user-provided annotations
                println!("constant.user_ty: {:?}", user_ty);
                let substs = if let Some(id) = user_ty {
                    use crate::rustc_index::Idx;
                    let id = rustc_middle::ty::UserTypeAnnotationIndex::from_usize(id.index());
                    let annots = &self.user_type_annotations.as_ref();
                    let annots = if let Option::Some(annots) = annots {
                        annots
                    } else {
                        error_or_panic!(
                            self,
                            span,
                            "No user type annotations available in the context"
                        )
                    };

                    let annot = annots.get(id).unwrap();
                    match &annot.user_ty.value {
                        rustc_middle::ty::UserType::Ty(_) => {
                            error_or_panic!(self, span, "Unexpected user type annotation")
                        }
                        rustc_middle::ty::UserType::TypeOf(def_id, user_substs) => {
                            use hax_frontend_exporter::SInto;
                            let tcx = self.t_ctx.tcx;
                            // The def id is the def id of the constant: we need
                            // to retrieve the def id of the parent impl block,
                            // then the type of this impl block.
                            let def_id = tcx.parent(*def_id);
                            println!("parent: {:?}", def_id);
                            let ty = tcx.type_of(def_id).subst(tcx, user_substs.substs);

                            println!("parent ty: {:?}", ty);

                            // We need to retrieve the trait information, because
                            // it is not provided by hax
                            println!("def_id: {:?}", def_id);
                            println!("self.def_id: {:?}", self.def_id);
                            println!("user_substs.substs: {:?}", user_substs.substs);
                            // For some reason we have to update the substitutions
                            // to refer to parameters instead of bound variables
                            /*let substs : Vec<_> = user_substs.substs.iter().cloned().map(|b| {
                                use rustc_middle::ty::GenericArgKind;
                                match b.unpack() {
                                    GenericArgKind::Lifetime(_) => {
                                        b
                                    }
                                    GenericArgKind::Type(ty) => {
                                        match ty.kind () {
                                            rustc_middle::ty::TyKind::Bound(id, )
                                            _ => b,
                                        }
                                    }
                                    GenericArgKind::Const(_) => {
                                        b
                                    }
                                }
                            }).collect();*/

                            let param_env = self.t_ctx.tcx.param_env(self.def_id);
                            println!("param_env: {:?}", param_env);
                            let trait_refs = hax::solve_item_traits(
                                &self.hax_state,
                                param_env,
                                def_id,
                                user_substs.substs,
                                None,
                            );
                            println!("trait_refs: {:?}", trait_refs);
                            panic!();

                            /*// Retrieve the trait references (there can be
                            // trait obligations, as well as a non-empty
                            // substitution, if the item was defined in a block).
                            if let Some(assoc) = tcx.opt_associated_item(def_id) {
                                if let rustc_middle::ty::AssocItemContainer::ImplContainer =
                                    assoc.container
                                {
                                    // The constant comes from an impl block.
                                    // Retrieve the type, instantiate it and solve the trait
                                    // obligations.
                                    println!("assoc.def_id: {:?}", assoc.def_id);
                                    let ty =
                                        tcx.type_of(assoc.def_id).subst(tcx, user_substs.substs);
                                    println!("type_of(assoc.def_id): {:?}", ty);

                                    panic!();
                                } else {
                                    error_or_panic!(
                                        self,
                                        span,
                                        format!("Unexpected case: {:?}", assoc.container)
                                    )
                                }
                            } else {
                                // The generic arguments should be empty
                                error_assert!(self, span, user_substs.substs.is_empty());
                                GenericArgs::empty()
                            }*/
                            /*println!("substs: {:?}", user_substs.substs);
                            println!("def_id: {:?}", def_id);
                            let ty = self.t_ctx.tcx.type_of(def_id);
                            println!("ty: {:?}", ty);
                            let ty = ty.subst(self.t_ctx.tcx, user_substs.substs);
                            println!("ty (after subst): {:?}", ty);
                            println!("\n\n");
                            panic!();

                            let erase_regions = true;
                            // Retrieve the list of used arguments
                            let used_params = if def_id.is_local() {
                                Option::None
                            } else {
                                println!("def_id: {:?}", def_id);
                                let def_id = def_id.sinto(&self.hax_state);
                                let name = self.t_ctx.def_id_to_name(&def_id)?;
                                crate::assumed::type_to_used_params(&name)
                            };

                            GenericArgs::empty()*/

                            /*
                            // We need to retrieve the trait information, because
                            // it is not provided by hax
                            println!("def_id: {:?}", def_id);
                            let param_env = self.t_ctx.tcx.param_env(self.def_id);
                            let trait_refs = hax::solve_item_traits(
                                &self.hax_state,
                                param_env,
                                *def_id,
                                user_substs.substs,
                                None,
                            );

                            let substs = user_substs.substs.sinto(&self.hax_state);
                            self.translate_substs_and_trait_refs(
                                span,
                                erase_regions,
                                used_params,
                                &substs,
                                &trait_refs,
                            )?*/
                        }
                    }
                } else {
                    GenericArgs::empty()
                };

                RawConstantExpr::Global(
                    self.translate_global_decl_id(span, id.rust_def_id.unwrap()),
                    substs,
                )
            }
            ConstantExprKind::Borrow(be) => {
                let be = self.translate_constant_expr_to_constant_expr(span, user_ty, be)?;
                RawConstantExpr::Ref(Box::new(be))
            }
            ConstantExprKind::ConstRef { id } => {
                let var_id = self.const_generic_vars_map.get(&id.index);
                if let Some(var_id) = var_id {
                    RawConstantExpr::Var(var_id)
                } else {
                    error_or_panic!(
                        self,
                        span,
                        &format!(
                            "Unexpected error: could not find the const var generic of index {}",
                            id.index
                        )
                    )
                }
            }
            ConstantExprKind::FnPtr(fn_id, substs, trait_refs, trait_info) => {
                use crate::translate_functions_to_ullbc::SubstFunIdOrPanic;
                let erase_regions = true; // TODO: not sure
                let fn_id = self.translate_fun_decl_id_with_args(
                    span,
                    erase_regions,
                    fn_id,
                    substs,
                    None,
                    trait_refs,
                    trait_info,
                )?;
                let SubstFunIdOrPanic::Fun(fn_id) = fn_id else  { unreachable!() };
                RawConstantExpr::FnPtr(fn_id.func)
            }
            ConstantExprKind::Todo(msg) => {
                // Case not yet handled by hax
                error_or_panic!(self, span, format!("Unsupported constant: {:?}", msg))
            }
        };

        let ty = self.translate_ty(span, erase_regions, ty)?;
        Ok(ConstantExpr { value, ty })
    }

    /// Remark: [hax::ConstantExpr] contains span information, but it is often
    /// the default span (i.e., it is useless), hence the additional span argument.
    pub(crate) fn translate_constant_expr_to_const_generic(
        &mut self,
        span: rustc_span::Span,
        v: &hax::ConstantExpr,
    ) -> Result<ConstGeneric, Error> {
        // Remark: we can't user globals as constant generics (meaning
        // the user provided type annotation should always be none).
        let value = self
            .translate_constant_expr_to_constant_expr(span, &None, v)?
            .value;
        match value {
            RawConstantExpr::Literal(v) => Ok(ConstGeneric::Value(v)),
            RawConstantExpr::Global(id, substs) => {
                error_assert!(self, span, substs.is_empty());
                Ok(ConstGeneric::Global(id))
            }
            RawConstantExpr::Adt(..)
            | RawConstantExpr::TraitConst { .. }
            | RawConstantExpr::Ref(_)
            | RawConstantExpr::FnPtr { .. } => {
                error_or_panic!(
                    self,
                    span,
                    format!("Unexpected constant generic: {:?}", value)
                )
            }
            RawConstantExpr::Var(v) => Ok(ConstGeneric::Var(v)),
        }
    }

    /// Remark: [hax::ConstantExpr] contains span information, but it is often
    /// the default span (i.e., it is useless), hence the additional span argument.
    pub(crate) fn translate_constant_to_constant_expr(
        &mut self,
        span: rustc_span::Span,
        v: &hax::Constant,
    ) -> Result<ConstantExpr, Error> {
        self.translate_constant_expr_to_constant_expr(span, &v.user_ty, &v.literal.constant_kind)
    }
}
