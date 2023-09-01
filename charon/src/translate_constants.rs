//! Functions to translate constants to LLBC.
#![allow(dead_code)]
use crate::expressions::*;
use crate::gast::*;
use crate::translate_ctx::*;
use crate::types::*;
use crate::values::*;
use hax_frontend_exporter as hax;
use rustc_middle::mir;
use rustc_middle::ty;

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn translate_constant_literal_to_raw_constant_expr(
        &mut self,
        v: &hax::ConstantLiteral,
    ) -> RawConstantExpr {
        let lit = match v {
            hax::ConstantLiteral::ByteStr(..) => {
                unimplemented!()
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
        RawConstantExpr::Literal(lit)
    }

    pub(crate) fn translate_constant_expr_kind_to_constant_expr(
        &mut self,
        ty: &hax::Ty,
        v: &hax::ConstantExprKind,
    ) -> ConstantExpr {
        use hax::ConstantExprKind;
        let value = match v {
            ConstantExprKind::Literal(lit) => {
                self.translate_constant_literal_to_raw_constant_expr(lit)
            }
            ConstantExprKind::Adt {
                info: _,
                vid,
                fields,
            } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    .map(|f| self.translate_constant_expr_to_constant_expr(&f.value))
                    .collect();
                let vid = vid.map(VariantId::Id::new);
                RawConstantExpr::Adt(vid, fields)
            }
            ConstantExprKind::Array { .. } => {
                unimplemented!()
            }
            ConstantExprKind::Tuple { fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    .map(|f| self.translate_constant_expr_to_constant_expr(f))
                    .collect();
                RawConstantExpr::Adt(Option::None, fields)
            }
            ConstantExprKind::TraitConst {
                impl_source,
                substs,
                name,
            } => {
                let trait_ref = self.translate_trait_impl_source(impl_source);
                // The trait ref should be Some(...): trait markers (that we
                // may eliminate) don't have constants.
                let trait_ref = trait_ref.unwrap();

                let (regions, types, const_generics) = self.translate_substs(None, substs).unwrap();
                let generics = GenericArgs {
                    regions,
                    types,
                    const_generics,
                    trait_refs: Vec::new(),
                };
                let name = TraitItemName(name.clone());
                RawConstantExpr::TraitConst(trait_ref, generics, name)
            }
            ConstantExprKind::GlobalName { id } => {
                RawConstantExpr::Global(self.translate_global_decl_id(id.rust_def_id.unwrap()))
            }
            ConstantExprKind::Borrow(be) => {
                let be = self.translate_constant_expr_to_constant_expr(be);
                RawConstantExpr::Ref(Box::new(be))
            }
            ConstantExprKind::ConstRef { id } => {
                let var_id = self.const_generic_vars_map.get(&id.index).unwrap();
                RawConstantExpr::Var(var_id)
            }
            ConstantExprKind::Todo(_) => {
                // Case not yet handled by hax
                unreachable!()
            }
        };

        let ty = self.translate_ety(ty).unwrap();
        ConstantExpr { value, ty }
    }

    pub(crate) fn translate_constant_expr_to_constant_expr(
        &mut self,
        v: &hax::ConstantExpr,
    ) -> ConstantExpr {
        self.translate_constant_expr_kind_to_constant_expr(&v.ty, &v.contents)
    }

    pub(crate) fn translate_constant_expr_to_const_generic(
        &mut self,
        v: &hax::ConstantExpr,
    ) -> ConstGeneric {
        match self.translate_constant_expr_to_constant_expr(v).value {
            RawConstantExpr::Literal(v) => ConstGeneric::Value(v),
            RawConstantExpr::Adt(..) => unreachable!(),
            RawConstantExpr::Global(v) => ConstGeneric::Global(v),
            RawConstantExpr::TraitConst { .. } | RawConstantExpr::Ref(_) => unreachable!(),
            RawConstantExpr::Var(v) => ConstGeneric::Var(v),
        }
    }

    pub(crate) fn translate_constant_to_constant_expr(
        &mut self,
        v: &hax::Constant,
    ) -> ConstantExpr {
        self.translate_constant_expr_to_constant_expr(&v.literal.constant_kind)
    }

    // TODO: remove once we make the external globals opaque
    pub(crate) fn translate_evaluated_operand_constant(
        &mut self,
        ty: ty::Ty<'tcx>,
        val: &mir::interpret::ConstValue<'tcx>,
        span: rustc_span::Span,
    ) -> ConstantExpr {
        let val = hax::const_value_to_constant_expr(&self.hax_state, ty, *val, span);
        self.translate_constant_expr_to_constant_expr(&val)
    }
}
