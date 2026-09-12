//! Functions to translate constants to LLBC.
use crate::hax;
use rustc_middle::ty;

use super::translate_ctx::*;
use charon_lib::ast::*;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    fn translate_constant_literal_to_constant_expr_kind(
        &mut self,
        _span: Span,
        v: &hax::ConstantLiteral,
    ) -> Result<ConstantExprKind, Error> {
        Ok(match v {
            hax::ConstantLiteral::ByteStr(bs) => ConstantExprKind::ByteStr(bs.clone()),
            hax::ConstantLiteral::Str(str) => {
                // We should only get here if we actually want to translate the data
                // backing the string, when we represent strings as unsized [u8]s
                assert!(self.t_ctx.options.unsized_strings);

                let str_bytes = str.as_bytes();
                return Ok(ConstantExprKind::RawMemory(
                    str_bytes.iter().map(|b| Byte::Value(*b)).collect(),
                ));
            }
            hax::ConstantLiteral::Char(c) => ConstantExprKind::Char(*c),
            hax::ConstantLiteral::Bool(b) => ConstantExprKind::Bool(*b),
            hax::ConstantLiteral::Int(i) => {
                use crate::hax::ConstantInt;
                let scalar = match i {
                    ConstantInt::Int(v, int_type) => {
                        let ty = Self::translate_hax_int_ty(int_type);
                        IntegerValue::Signed(ty, *v)
                    }
                    ConstantInt::Uint(v, uint_type) => {
                        let ty = Self::translate_hax_uint_ty(uint_type);
                        IntegerValue::Unsigned(ty, *v)
                    }
                };
                ConstantExprKind::Integer(scalar)
            }
            hax::ConstantLiteral::Float(value, float_type) => {
                let value = value.clone();
                let ty = match float_type {
                    hax::FloatTy::F16 => FloatTy::F16,
                    hax::FloatTy::F32 => FloatTy::F32,
                    hax::FloatTy::F64 => FloatTy::F64,
                    hax::FloatTy::F128 => FloatTy::F128,
                };
                ConstantExprKind::Float(FloatValue { value, ty })
            }
            hax::ConstantLiteral::PtrNoProvenance(v) => {
                return Ok(ConstantExprKind::PtrNoProvenance(*v));
            }
        })
    }

    fn translate_constant_byte(
        &mut self,
        span: Span,
        b: &hax::ConstantByte,
    ) -> Result<Byte, Error> {
        Ok(match b {
            hax::ConstantByte::Uninit => Byte::Uninit,
            hax::ConstantByte::Value(v) => Byte::Value(*v),
            hax::ConstantByte::Provenance(prov, offset) => {
                let prov = match prov {
                    hax::ConstantByteProvenance::Global(item) => {
                        Provenance::Global(self.translate_global_decl_ref(span, item)?)
                    }
                    hax::ConstantByteProvenance::Function(item) => {
                        let fun_ref: FunDeclRef =
                            self.translate_item(span, item, TransItemSourceKind::Fun)?;
                        Provenance::Function(fun_ref)
                    }
                    hax::ConstantByteProvenance::Unknown => Provenance::Unknown,
                };
                Byte::Provenance(prov, *offset)
            }
        })
    }

    /// Remark: [hax::ConstantExpr] contains span information, but it is often
    /// the default span (i.e., it is useless), hence the additional span argument.
    /// TODO: the user_ty might be None because hax doesn't extract it (because
    /// we are translating a [ConstantExpr] instead of a Constant. We need to
    /// update hax.
    pub(crate) fn translate_constant_expr(
        &mut self,
        span: Span,
        v: &hax::ConstantExpr,
    ) -> Result<ConstantExpr, Error> {
        let ty = self.translate_ty(span, &v.ty)?;
        let kind = match v.contents.as_ref() {
            hax::ConstantExprKind::Literal(lit) => {
                self.translate_constant_literal_to_constant_expr_kind(span, lit)?
            }
            hax::ConstantExprKind::Adt { kind, fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    .map(|f| self.translate_constant_expr(span, &f.value))
                    .try_collect()?;
                use crate::hax::VariantKind;
                let vid = if let VariantKind::Enum { index, .. } = *kind {
                    Some(self.translate_variant_id(index))
                } else {
                    None
                };
                ConstantExprKind::Adt(vid, fields)
            }
            hax::ConstantExprKind::Array { fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    .map(|x| self.translate_constant_expr(span, x))
                    .try_collect()?;

                ConstantExprKind::Array(fields)
            }
            hax::ConstantExprKind::Tuple { fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    // TODO: the user_ty is not always None
                    .map(|f| self.translate_constant_expr(span, f))
                    .try_collect()?;
                ConstantExprKind::Adt(None, fields)
            }
            hax::ConstantExprKind::NamedGlobal(item) => match &item.in_trait {
                Some(trait_proof) => {
                    let trait_ref = self.translate_trait_proof(span, trait_proof)?;
                    // Trait consts can't have their own generics.
                    assert!(item.generic_args.is_empty());
                    let const_id =
                        self.translate_assoc_const_id(trait_ref.trait_id(), &item.def_id)?;
                    ConstantExprKind::TraitConst(trait_ref, const_id)
                }
                None => {
                    let global_ref = self.translate_global_decl_ref(span, item)?;
                    ConstantExprKind::Global(global_ref)
                }
            },
            hax::ConstantExprKind::Borrow(v)
                if let hax::ConstantExprKind::Literal(hax::ConstantLiteral::Str(s)) =
                    v.contents.as_ref()
                    && !self.t_ctx.options.unsized_strings =>
            {
                ConstantExprKind::Str(s.clone())
            }

            hax::ConstantExprKind::Borrow(v) => {
                let mut val = self.translate_constant_expr(span, v)?;
                let (metadata, new_ty) = match (v.contents.as_ref(), val.ty().kind()) {
                    (
                        hax::ConstantExprKind::Array { fields },
                        TyKind::Slice(subty, ty_is_sized),
                    ) => {
                        let len = ConstantExpr::mk_usize(fields.len() as u128);
                        // the sub-constant is an array, that has it's reference unsized
                        (
                            Some(UnsizingMetadata::Length(len.clone())),
                            Some(Ty::mk_array(subty.clone(), len, ty_is_sized.clone())),
                        )
                    }

                    (hax::ConstantExprKind::Literal(hax::ConstantLiteral::Str(s)), _) => {
                        let len = ConstantExpr::mk_usize(s.len() as u128);
                        let ty_is_sized = self.translate_sized_proof(span, self.tcx.types.u8)?;
                        // the sub-constant is an array, that has it's reference unsized
                        let subty =
                            TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(UIntTy::U8)))
                                .into();
                        (
                            Some(UnsizingMetadata::Length(len.clone())),
                            Some(Ty::mk_array(subty, len, ty_is_sized)),
                        )
                    }

                    // A reference to an array-typed global, unsized to a slice.
                    (_, TyKind::Array(_, len, _))
                        if let TyKind::Ref(_, pointee, _) = ty.kind()
                            && pointee.is_slice() =>
                    {
                        (Some(UnsizingMetadata::Length(len.clone())), None)
                    }

                    _ => (None, None),
                };
                if let Some(new_ty) = new_ty {
                    val.with_contents_mut(|_, ty| *ty = new_ty);
                }
                ConstantExprKind::Ref(val, metadata)
            }
            hax::ConstantExprKind::RawBorrow { mutability, arg } => {
                let arg = self.translate_constant_expr(span, arg)?;
                let rk = RefKind::mutable(mutability.is_mut());
                ConstantExprKind::Ptr(rk, arg, None)
            }
            hax::ConstantExprKind::ConstRef { id } => {
                match self.lookup_const_generic_var(span, id) {
                    Ok(var) => ConstantExprKind::Var(var),
                    Err(err) => ConstantExprKind::Opaque(err.msg),
                }
            }
            hax::ConstantExprKind::FnDef(item) => {
                let fn_ptr = self.translate_fn_ptr(span, item, TransItemSourceKind::Fun)?;
                ConstantExprKind::FnDef(fn_ptr)
            }
            hax::ConstantExprKind::FnPtr(item) => {
                let fn_ptr = self.translate_fn_ptr(span, item, TransItemSourceKind::Fun)?;
                ConstantExprKind::FnPtr(fn_ptr)
            }
            hax::ConstantExprKind::Memory(bytes) => {
                let bytes: Vec<Byte> = bytes
                    .iter()
                    .map(|b| self.translate_constant_byte(span, b))
                    .try_collect()?;
                ConstantExprKind::RawMemory(bytes)
            }
            hax::ConstantExprKind::Todo(msg) => {
                register_error!(self, span, "Unsupported constant: {:?}", msg);
                ConstantExprKind::Opaque(msg.into())
            }
        };

        Ok(ConstantExpr::new(kind, ty))
    }

    pub(crate) fn translate_ty_constant_expr(
        &mut self,
        span: Span,
        c: &ty::Const<'tcx>,
    ) -> Result<ConstantExpr, Error> {
        let c = self.catch_sinto(span, c)?;
        self.translate_constant_expr(span, &c)
    }

    /// Evaluates a constant definition and returns the result as a [`ConstantExpr`], if one exists.
    pub(crate) fn evaluate_const_def(
        &mut self,
        def: &hax::FullDef<'tcx>,
    ) -> Option<hax::Decorated<hax::ConstantExprKind>> {
        match def.kind() {
            hax::FullDefKind::Const { .. } | hax::FullDefKind::AssocConst { .. } => {
                def.const_value(self.hax_state_with_id())
            }
            hax::FullDefKind::Static { .. } => def.static_value(self.hax_state_with_id()),
            _ => None,
        }
    }
}
