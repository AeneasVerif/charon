//! Functions to translate constants to LLBC.
#![allow(dead_code)]
use crate::expressions as e;
use crate::translate_ctx::*;
use crate::types as ty;
use crate::values as v;
use hax_frontend_exporter as hax;
use rustc_middle::mir;
use rustc_middle::ty::Ty;

impl<'tcx, 'ctx, 'ctx1> BodyTransCtx<'tcx, 'ctx, 'ctx1> {
    fn translate_constant_literal_to_raw_constant_expr(
        &mut self,
        v: &hax::ConstantLiteral,
    ) -> e::RawConstantExpr {
        use crate::values::*;
        use hax::ConstantLiteral;
        let lit = match v {
            ConstantLiteral::ByteStr(..) => {
                unimplemented!()
            }
            ConstantLiteral::Char(c) => v::Literal::Char(*c),
            ConstantLiteral::Bool(b) => v::Literal::Bool(*b),
            ConstantLiteral::Int(i) => {
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
                            IntTy::I128 => ScalarValue::I128(*v as i128),
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
                            UintTy::U128 => ScalarValue::U128(*v as u128),
                        }
                    }
                };
                v::Literal::Scalar(scalar)
            }
        };
        e::RawConstantExpr::Literal(lit)
    }

    pub(crate) fn translate_constant_expr_kind_to_constant_expr(
        &mut self,
        ty: &hax::Ty,
        v: &hax::ConstantExprKind,
    ) -> e::ConstantExpr {
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
                let fields: Vec<e::ConstantExpr> = fields
                    .iter()
                    .map(|f| self.translate_constant_expr_to_constant_expr(&f.value))
                    .collect();
                let vid = vid.map(ty::VariantId::Id::new);
                e::RawConstantExpr::Adt(vid, fields)
            }
            ConstantExprKind::Array { .. } => {
                unimplemented!()
            }
            ConstantExprKind::Tuple { fields } => {
                let fields: Vec<e::ConstantExpr> = fields
                    .iter()
                    .map(|f| self.translate_constant_expr_to_constant_expr(&f))
                    .collect();
                e::RawConstantExpr::Adt(Option::None, fields)
            }
            ConstantExprKind::GlobalName { id } => {
                e::RawConstantExpr::Global(self.translate_global_decl_id(id.rust_def_id.unwrap()))
            }
            ConstantExprKind::Borrow(be) => {
                let be = self.translate_constant_expr_to_constant_expr(be);
                e::RawConstantExpr::Ref(Box::new(be))
            }
            ConstantExprKind::ConstRef { id } => {
                let var_id = self.const_generic_vars_map.get(&id.index).unwrap();
                e::RawConstantExpr::Var(var_id)
            }
            ConstantExprKind::Todo(_) => {
                // Case not yet handled by hax
                unreachable!()
            }
        };

        let ty = self.translate_ety(ty).unwrap();
        e::ConstantExpr { value, ty }
    }

    pub(crate) fn translate_constant_expr_to_constant_expr(
        &mut self,
        v: &hax::ConstantExpr,
    ) -> e::ConstantExpr {
        self.translate_constant_expr_kind_to_constant_expr(&v.ty, &v.contents)
    }

    pub(crate) fn translate_constant_expr_to_const_generic(
        &mut self,
        v: &hax::ConstantExpr,
    ) -> ty::ConstGeneric {
        match self.translate_constant_expr_to_constant_expr(v).value {
            e::RawConstantExpr::Literal(v) => ty::ConstGeneric::Value(v),
            e::RawConstantExpr::Adt(..) => unreachable!(),
            e::RawConstantExpr::Global(v) => ty::ConstGeneric::Global(v),
            e::RawConstantExpr::Ref(_) => unreachable!(),
            e::RawConstantExpr::Var(v) => ty::ConstGeneric::Var(v),
        }
    }

    pub(crate) fn translate_constant_to_constant_expr(
        &mut self,
        v: &hax::Constant,
    ) -> e::ConstantExpr {
        self.translate_constant_expr_to_constant_expr(&v.literal.constant_kind)
    }

    // TODO: remove once we make the external globals opaque
    pub(crate) fn translate_evaluated_operand_constant(
        &mut self,
        ty: Ty<'tcx>,
        val: &mir::interpret::ConstValue<'tcx>,
        span: rustc_span::Span,
    ) -> e::ConstantExpr {
        let val = hax::const_value_to_constant_expr(&self.hax_state, ty, *val, span);
        self.translate_constant_expr_to_constant_expr(&val)
    }
}
