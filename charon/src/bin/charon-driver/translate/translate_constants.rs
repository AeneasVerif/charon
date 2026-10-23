//! Functions to translate constants to LLBC.
use crate::hax;
use crate::hax::state::UnderOwnerState;
use rustc_middle::ty;

use super::translate_ctx::*;
use charon_lib::ast::*;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    fn translate_constant_literal_to_constant_expr_kind(
        &mut self,
        span: Span,
        v: &hax::ConstantLiteral,
    ) -> Result<ConstantExprKind, Error> {
        Ok(match v {
            hax::ConstantLiteral::ByteStr(bs) => ConstantExprKind::ByteStr(bs.clone()),
            // A `str` value not behind a reference, e.g. the tail of a `str`-tailed DST
            hax::ConstantLiteral::Str(str) => {
                let ty_is_sized = self.translate_sized_proof(span, self.tcx.types.u8)?;
                let bytes = str
                    .bytes()
                    .map(|b| IntegerValue::Unsigned(UIntTy::U8, b.into()).to_constant())
                    .collect();
                let slice_ty = Ty::mk_slice(Ty::mk_u8(), ty_is_sized);
                let bytes = ConstantExpr::new(ConstantExprKind::Array(bytes), slice_ty);
                // we encode `str` as `struct { [u8] }`
                ConstantExprKind::Adt(None, [bytes].into())
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
            hax::ConstantLiteral::Float(value, bits, float_type) => {
                let value = value.clone();
                let bits = *bits;
                let ty = match float_type {
                    hax::FloatTy::F16 => FloatTy::F16,
                    hax::FloatTy::F32 => FloatTy::F32,
                    hax::FloatTy::F64 => FloatTy::F64,
                    hax::FloatTy::F128 => FloatTy::F128,
                };
                ConstantExprKind::Float(FloatValue { value, bits, ty })
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
                Byte::Provenance(self.translate_provenance(span, prov)?, *offset)
            }
        })
    }

    fn translate_provenance(
        &mut self,
        span: Span,
        prov: &hax::ConstantByteProvenance,
    ) -> Result<GlobalProvenance, Error> {
        Ok(match prov {
            hax::ConstantByteProvenance::Global(item) => {
                GlobalProvenance::Global(self.translate_global_decl_ref(span, item)?)
            }
            hax::ConstantByteProvenance::Function(target, fn_ptr_ty) => {
                let fn_ptr = self.translate_bound_fn_ptr_target(span, target)?;
                GlobalProvenance::Function(
                    self.erase_region_binder(fn_ptr),
                    self.translate_ty(span, fn_ptr_ty)?,
                )
            }
            hax::ConstantByteProvenance::Unknown => GlobalProvenance::Unknown,
        })
    }

    /// The function pointed to by a function pointer.
    fn translate_bound_fn_ptr_target(
        &mut self,
        span: Span,
        target: &hax::FnPtrTarget,
    ) -> Result<RegionBinder<FnPtr>, Error> {
        Ok(match target {
            hax::FnPtrTarget::Fn(item) => {
                self.translate_bound_fn_ptr(span, item, TransItemSourceKind::Fun)?
            }
            hax::FnPtrTarget::ClosureAsFn(closure) => self
                .translate_stateless_closure_as_fn_ref(span, closure)?
                .map(FnPtr::from),
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
                let fields: IndexVec<FieldId, ConstantExpr> = fields
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
                let fields: IndexVec<FieldId, ConstantExpr> = fields
                    .iter()
                    // TODO: the user_ty is not always None
                    .map(|f| self.translate_constant_expr(span, f))
                    .try_collect()?;
                ConstantExprKind::Adt(None, fields)
            }
            hax::ConstantExprKind::NamedGlobal(item) => match &item.in_trait {
                Some(trait_proof) => {
                    let trait_ref = self.translate_trait_proof(span, trait_proof)?.erase();
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
            hax::ConstantExprKind::Ptr {
                base: hax::ConstantPtrBase::Value(arg),
                ..
            } if ty.is_ref()
                && let hax::ConstantExprKind::Literal(hax::ConstantLiteral::Str(s)) =
                    arg.contents.as_ref() =>
            {
                ConstantExprKind::Str(s.clone())
            }
            hax::ConstantExprKind::Ptr {
                base,
                projections,
                metadata,
            } => {
                let mut place = match base {
                    hax::ConstantPtrBase::Global(prov, base_ty) => GlobalPlace {
                        kind: GlobalPlaceKind::Global(self.translate_provenance(span, prov)?),
                        ty: self.translate_ty(span, base_ty)?,
                    },
                    hax::ConstantPtrBase::Value(arg) => {
                        GlobalPlace::new_value(self.translate_constant_expr(span, arg)?)
                    }
                };
                for (proj, proj_ty) in projections {
                    let proj = match *proj {
                        hax::ConstantProjectionElem::Field(variant, field) => {
                            ConstProjectionElem::Field(
                                variant.map(|v| self.translate_variant_id(v)),
                                self.translate_field_id(field),
                            )
                        }
                        hax::ConstantProjectionElem::Index(i) => {
                            ConstProjectionElem::Index(IntegerValue::mk_usize(i as u128))
                        }
                        hax::ConstantProjectionElem::Subslice { from, to } => {
                            ConstProjectionElem::Subslice {
                                from: IntegerValue::mk_usize(from as u128),
                                to: IntegerValue::mk_usize(to as u128),
                            }
                        }
                        hax::ConstantProjectionElem::Offset {
                            count,
                            ref ty,
                            in_bounds,
                            ref pointee_is_sized,
                        } => ConstProjectionElem::Offset {
                            count: IntegerValue::Signed(IntTy::Isize, count as i128),
                            ty: ty
                                .as_ref()
                                .map(|ty| self.translate_ty(span, ty))
                                .transpose()?,
                            in_bounds,
                            pointee_is_sized: self
                                .options
                                .hide_marker_traits
                                .then_some(self.translate_trait_proof(span, pointee_is_sized))
                                .transpose()?
                                .map(|p| p.no_bound_vars()),
                        },
                    };
                    place = place.project(proj, self.translate_ty(span, proj_ty)?);
                }
                let metadata = metadata
                    .as_ref()
                    .map(|metadata| self.translate_unsizing_metadata(span, metadata))
                    .transpose()?;
                match ty.kind() {
                    TyKind::RawPtr(_, rk) => ConstantExprKind::Ptr(*rk, place, metadata),
                    _ => ConstantExprKind::Ref(place, metadata),
                }
            }
            hax::ConstantExprKind::PtrCast(ptr, metadata) => {
                let ptr = self.translate_constant_expr(span, ptr)?;
                let kind = if let Some(metadata) = metadata {
                    let metadata = self.translate_unsizing_metadata(span, metadata)?;
                    CastKind::Unsize(ty.clone(), metadata)
                } else {
                    CastKind::RawPtr(ty.clone())
                };
                ConstantExprKind::Cast(ptr, kind)
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
            hax::ConstantExprKind::FnPtr(target) => {
                let rustc_sig = match target {
                    hax::FnPtrTarget::Fn(item) => {
                        let args = item.rustc_args(self.hax_state_with_id());
                        let sig = self.tcx.fn_sig(item.def_id.real_rust_def_id());
                        hax::inst_binder(
                            self.tcx,
                            self.hax_state_with_id().typing_env(),
                            Some(args),
                            sig,
                        )
                    }
                    hax::FnPtrTarget::ClosureAsFn(closure) => {
                        let args = closure.item.rustc_args(self.hax_state_with_id());
                        hax::closure_sig(self.tcx, args.as_closure())
                    }
                };
                let rustc_fn_ptr = ty::Ty::new_fn_ptr(self.tcx, rustc_sig);
                let source_ty = self.translate_rustc_ty(span, &rustc_fn_ptr)?;
                let fn_ptr = self.translate_bound_fn_ptr_target(span, target)?;
                let fn_def = ConstantExpr::new(
                    ConstantExprKind::FnDef(self.erase_region_binder(fn_ptr.clone())),
                    TyKind::FnDef(fn_ptr).into_ty(),
                );
                let kind = ConstantExprKind::Cast(fn_def, CastKind::FnDefToFnPtr);
                let (TyKind::FnPtr(source), TyKind::FnPtr(target)) = (source_ty.kind(), ty.kind())
                else {
                    unreachable!("expected function pointer types")
                };
                if source.skip_binder.is_unsafe != target.skip_binder.is_unsafe {
                    ConstantExprKind::Cast(
                        ConstantExpr::new(kind, source_ty),
                        CastKind::FnPtrToUnsafe,
                    )
                } else {
                    kind
                }
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
}
