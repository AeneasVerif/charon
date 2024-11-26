//! Functions to translate constants to LLBC.
use super::translate_ctx::*;
use charon_lib::ast::*;
use hax_frontend_exporter as hax;

impl<'tcx, 'ctx> BodyTransCtx<'tcx, 'ctx> {
    fn translate_constant_literal_to_raw_constant_expr(
        &mut self,
        v: &hax::ConstantLiteral,
    ) -> Result<RawConstantExpr, Error> {
        let lit = match v {
            hax::ConstantLiteral::ByteStr(bs, _) => Literal::ByteStr(bs.clone()),
            hax::ConstantLiteral::Str(s, _) => Literal::Str(s.clone()),
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
            hax::ConstantLiteral::Float(value, float_type) => {
                let value = value.clone();
                let ty = match float_type {
                    hax::FloatTy::F16 => FloatTy::F16,
                    hax::FloatTy::F32 => FloatTy::F32,
                    hax::FloatTy::F64 => FloatTy::F64,
                    hax::FloatTy::F128 => FloatTy::F128,
                };
                Literal::Float(FloatValue { value, ty })
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
        span: Span,
        v: &hax::ConstantExpr,
    ) -> Result<ConstantExpr, Error> {
        use hax::ConstantExprKind;
        let ty = &v.ty;
        let value = match &(*v.contents) {
            ConstantExprKind::Literal(lit) => {
                self.translate_constant_literal_to_raw_constant_expr(lit)?
            }
            ConstantExprKind::Adt { info, fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    // TODO: the user_ty is not always None
                    .map(|f| self.translate_constant_expr_to_constant_expr(span, &f.value))
                    .try_collect()?;
                use hax::VariantKind;
                let vid = if let VariantKind::Enum { index, .. } = info.kind {
                    Some(VariantId::new(index))
                } else {
                    None
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
                    .map(|f| self.translate_constant_expr_to_constant_expr(span, f))
                    .try_collect()?;
                RawConstantExpr::Adt(None, fields)
            }
            ConstantExprKind::TraitConst { impl_expr, name } => {
                let trait_ref = self.translate_trait_impl_expr(span, impl_expr)?;
                let name = TraitItemName(name.clone());
                RawConstantExpr::TraitConst(trait_ref, name)
            }
            ConstantExprKind::GlobalName {
                id,
                generics,
                trait_refs,
                ..
            } => {
                trace!(
                    "\n- generics: {:?}\n- trait_resf: {:?}\n",
                    generics,
                    trait_refs
                );
                let used_params = None;
                let generics =
                    self.translate_generic_args(span, used_params, generics, trait_refs, None)?;

                let global_id = self.register_global_decl_id(span, id);
                RawConstantExpr::Global(GlobalDeclRef {
                    id: global_id,
                    generics,
                })
            }
            ConstantExprKind::Borrow(be) => {
                let be = self.translate_constant_expr_to_constant_expr(span, be)?;
                RawConstantExpr::Ref(Box::new(be))
            }
            ConstantExprKind::Cast { .. } => {
                error_or_panic!(
                    self,
                    span,
                    &format!("Unsupported constant: `ConstantExprKind::Cast {{..}}`",)
                )
            }
            ConstantExprKind::RawBorrow {
                mutability: false, ..
            } => {
                error_or_panic!(
                    self,
                    span,
                    &format!("Unsupported constant: `ConstantExprKind::RawBorrow {{mutability: false, ..}}`",)
                )
            }
            ConstantExprKind::RawBorrow {
                mutability: true,
                arg,
            } => {
                let arg = self.translate_constant_expr_to_constant_expr(span, arg)?;
                RawConstantExpr::MutPtr(Box::new(arg))
            }
            ConstantExprKind::ConstRef { id } => match self.lookup_const_generic_var(id) {
                Some(var) => RawConstantExpr::Var(var),
                None => {
                    error_or_panic!(
                        self,
                        span,
                        &format!(
                            "Unexpected error: could not find the const generic variable {}",
                            id.name
                        )
                    )
                }
            },
            ConstantExprKind::FnPtr {
                def_id: fn_id,
                generics: substs,
                generics_impls: trait_refs,
                method_impl: trait_info,
            } => {
                use super::translate_functions_to_ullbc::SubstFunIdOrPanic;
                let fn_id = self.translate_fun_decl_id_with_args(
                    span, fn_id, substs, None, trait_refs, trait_info,
                )?;
                let SubstFunIdOrPanic::Fun(fn_id) = fn_id else {
                    unreachable!()
                };
                RawConstantExpr::FnPtr(fn_id.func)
            }
            ConstantExprKind::Todo(msg) => {
                // Case not yet handled by hax
                error_or_panic!(self, span, format!("Unsupported constant: {:?}", msg))
            }
        };

        let ty = self.translate_ty(span, ty)?;
        Ok(ConstantExpr { value, ty })
    }

    /// Remark: [hax::ConstantExpr] contains span information, but it is often
    /// the default span (i.e., it is useless), hence the additional span argument.
    pub(crate) fn translate_constant_expr_to_const_generic(
        &mut self,
        span: Span,
        v: &hax::ConstantExpr,
    ) -> Result<ConstGeneric, Error> {
        // Remark: we can't user globals as constant generics (meaning
        // the user provided type annotation should always be none).
        let value = self
            .translate_constant_expr_to_constant_expr(span, v)?
            .value;
        match value {
            RawConstantExpr::Literal(v) => Ok(ConstGeneric::Value(v)),
            RawConstantExpr::Global(global_ref) => {
                // TODO: handle constant arguments with generics (this can likely only happen with
                // a feature gate).
                error_assert!(self, span, global_ref.generics.is_empty());
                Ok(ConstGeneric::Global(global_ref.id))
            }
            RawConstantExpr::Adt(..)
            | RawConstantExpr::TraitConst { .. }
            | RawConstantExpr::Ref(_)
            | RawConstantExpr::MutPtr(_)
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
        span: Span,
        v: &hax::Constant,
    ) -> Result<ConstantExpr, Error> {
        self.translate_constant_expr_to_constant_expr(span, &v.const_.constant_kind)
    }
}
