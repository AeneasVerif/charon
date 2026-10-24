//! Functions to translate constants to LLBC.
use crate::hax;
use crate::hax::SInto;
use crate::hax::state::{BaseState, UnderOwnerState};
use rustc_const_uneval::{AllocTarget, ConstKind, FnTarget, Projection, PtrTarget};
use rustc_middle::ty;

use super::translate_ctx::*;
use charon_lib::ast::*;

impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    /// The provenance to give to the bytes of a pointer into the given allocation.
    fn translate_provenance(
        &mut self,
        span: Span,
        target: AllocTarget<'tcx>,
    ) -> Result<GlobalProvenance, Error> {
        let s = self.hax_state_with_id();
        Ok(match target {
            AllocTarget::Fn(target) => {
                let fn_ptr_ty = target.fn_ptr_ty(self.tcx, s.typing_env());
                let fn_ptr = self.translate_bound_fn_ptr_target(span, target)?;
                GlobalProvenance::Function(
                    self.erase_region_binder(fn_ptr),
                    self.translate_rustc_ty(span, &fn_ptr_ty)?,
                )
            }
            AllocTarget::Global(global) if hax::const_reader(s).is_named_global(global) => {
                GlobalProvenance::Global(self.translate_global_decl_ref(span, &global.sinto(s))?)
            }
            // TODO: TypeIds
            // VTables are not reachable here, I believe: it's UB to attempt reading a VTable's data.
            AllocTarget::Global(_) | AllocTarget::VTable(..) | AllocTarget::TypeId(..) => {
                GlobalProvenance::Unknown
            }
        })
    }

    /// The function pointed to by a function pointer.
    fn translate_bound_fn_ptr_target(
        &mut self,
        span: Span,
        target: FnTarget<'tcx>,
    ) -> Result<RegionBinder<FnPtr>, Error> {
        let s = self.hax_state_with_id();
        Ok(match target {
            FnTarget::Instance(instance) => {
                let item = hax::translate_item_ref(s, instance.def_id(), instance.args);
                self.translate_bound_fn_ptr(span, &item, TransItemSourceKind::Fun)?
            }
            FnTarget::ClosureAsFn(def_id, args) => {
                let closure = hax::ClosureTy::sfrom(s, def_id, args);
                self.translate_stateless_closure_as_fn_ref(span, &closure)?
                    .map(FnPtr::from)
            }
        })
    }

    /// The metadata of a constant pointer obtained by unsizing a thin pointer.
    fn translate_const_unsize(
        &mut self,
        span: Span,
        unsize: rustc_const_uneval::Unsize<'tcx>,
    ) -> Result<UnsizingMetadata, Error> {
        let tcx = self.tcx;
        let ref_to = |ty| ty::Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, ty);
        let metadata = hax::compute_unsizing_metadata(
            self.hax_state_with_id(),
            ref_to(unsize.from),
            ref_to(unsize.to),
        );
        self.translate_unsizing_metadata(span, &metadata)
    }

    pub(crate) fn translate_constant_expr(
        &mut self,
        span: Span,
        v: &rustc_const_uneval::Const<'tcx>,
    ) -> Result<ConstantExpr, Error> {
        let tcx = self.tcx;
        let ty = self.translate_rustc_ty(span, &v.ty)?;
        // The value of a pattern type is described at its base type.
        let base_ty = match v.ty.kind() {
            ty::Pat(base_ty, _) => *base_ty,
            _ => v.ty,
        };
        let kind = match &v.kind {
            ConstKind::Scalar(x) => match *base_ty.kind() {
                ty::Char => ConstantExprKind::Char(char::try_from(*x).unwrap()),
                ty::Bool => ConstantExprKind::Bool(x.try_to_bool().unwrap()),
                ty::Int(int_ty) => {
                    let int_ty = Self::translate_hax_int_ty(&int_ty.sinto(self.hax_state()));
                    ConstantExprKind::Integer(IntegerValue::Signed(int_ty, x.to_int(x.size())))
                }
                ty::Uint(uint_ty) => {
                    let uint_ty = Self::translate_hax_uint_ty(&uint_ty.sinto(self.hax_state()));
                    ConstantExprKind::Integer(IntegerValue::Unsigned(uint_ty, x.to_uint(x.size())))
                }
                ty::Float(float_ty) => {
                    use rustc_apfloat::{Float, ieee};
                    let bits = x.to_bits_unchecked();
                    let (value, ty) = match float_ty {
                        ty::FloatTy::F16 => (ieee::Half::from_bits(bits).to_string(), FloatTy::F16),
                        ty::FloatTy::F32 => {
                            (ieee::Single::from_bits(bits).to_string(), FloatTy::F32)
                        }
                        ty::FloatTy::F64 => {
                            (ieee::Double::from_bits(bits).to_string(), FloatTy::F64)
                        }
                        ty::FloatTy::F128 => {
                            (ieee::Quad::from_bits(bits).to_string(), FloatTy::F128)
                        }
                    };
                    ConstantExprKind::Float(FloatValue { value, bits, ty })
                }
                _ => unreachable!("not a scalar type: {base_ty:?}"),
            },
            ConstKind::PtrNoProvenance(addr) => ConstantExprKind::PtrNoProvenance(*addr),
            // A `str` value not behind a reference, e.g. the tail of a `str`-tailed DST
            ConstKind::Str(str) => {
                let ty_is_sized = self.translate_sized_proof(span, tcx.types.u8)?;
                let bytes = str
                    .bytes()
                    .map(|b| IntegerValue::Unsigned(UIntTy::U8, b.into()).to_constant())
                    .collect();
                let slice_ty = Ty::mk_slice(Ty::mk_u8(), ty_is_sized);
                let bytes = ConstantExpr::new(ConstantExprKind::Array(bytes), slice_ty);
                // we encode `str` as `struct { [u8] }`
                ConstantExprKind::Adt(None, [bytes].into())
            }
            ConstKind::ByteStr(bytes) => ConstantExprKind::ByteStr(bytes.clone()),
            ConstKind::Aggregate { variant, fields } => {
                let fields: Vec<ConstantExpr> = fields
                    .iter()
                    .map(|f| self.translate_constant_expr(span, f))
                    .try_collect()?;
                match base_ty.kind() {
                    ty::Adt(adt_def, _) => {
                        let vid = if adt_def.is_enum() {
                            Some(self.translate_variant_id(variant.unwrap()))
                        } else {
                            None
                        };
                        ConstantExprKind::Adt(vid, fields.into())
                    }
                    ty::Closure(..) | ty::Tuple(_) => ConstantExprKind::Adt(None, fields.into()),
                    ty::Array(..) | ty::Slice(..) => ConstantExprKind::Array(fields),
                    _ => unreachable!("unexpected aggregate type {base_ty:?}"),
                }
            }
            ConstKind::FnDef { def, args } => {
                let item = hax::translate_item_ref(self.hax_state_with_id(), *def, args);
                let fn_ptr = self.translate_fn_ptr(span, &item, TransItemSourceKind::Fun)?;
                ConstantExprKind::FnDef(fn_ptr)
            }
            ConstKind::FnPtr(target) => {
                let rustc_sig = match *target {
                    FnTarget::Instance(instance) => hax::inst_binder(
                        tcx,
                        self.hax_state_with_id().typing_env(),
                        Some(instance.args),
                        tcx.fn_sig(instance.def_id()),
                    ),
                    FnTarget::ClosureAsFn(_, args) => hax::closure_sig(tcx, args.as_closure()),
                };
                let rustc_fn_ptr = ty::Ty::new_fn_ptr(tcx, rustc_sig);
                let source_ty = self.translate_rustc_ty(span, &rustc_fn_ptr)?;
                let fn_ptr = self.translate_bound_fn_ptr_target(span, *target)?;
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
            ConstKind::Ptr {
                target: PtrTarget::Inline(val),
                ..
            } if ty.is_ref()
                && let ConstKind::Str(s) = &val.kind =>
            {
                ConstantExprKind::Str(s.clone())
            }
            ConstKind::Ptr { target, unsize } => {
                let (mut place, projections) = match target {
                    PtrTarget::Global {
                        target,
                        ty: base_ty,
                        projections,
                    } => {
                        let prov = match *target {
                            // We name the globals we point into, even the ones that we otherwise
                            // inline.
                            AllocTarget::Global(global) => {
                                GlobalProvenance::Global(self.translate_global_decl_ref(
                                    span,
                                    &global.sinto(self.hax_state_with_id()),
                                )?)
                            }
                            _ => self.translate_provenance(span, *target)?,
                        };
                        let place = GlobalPlace {
                            kind: GlobalPlaceKind::Global(prov),
                            ty: self.translate_rustc_ty(span, base_ty)?,
                        };
                        (place, projections.as_slice())
                    }
                    PtrTarget::Inline(val) => (
                        GlobalPlace::new_value(self.translate_constant_expr(span, val)?),
                        [].as_slice(),
                    ),
                };
                for (proj, proj_ty) in projections {
                    let proj = match *proj {
                        Projection::Field(variant, field) => ConstProjectionElem::Field(
                            variant.map(|v| self.translate_variant_id(v)),
                            self.translate_field_id(field),
                        ),
                        Projection::Index(i) => {
                            ConstProjectionElem::Index(IntegerValue::mk_usize(i as u128))
                        }
                        Projection::Subslice { from, to } => ConstProjectionElem::Subslice {
                            from: IntegerValue::mk_usize(from as u128),
                            to: IntegerValue::mk_usize(to as u128),
                        },
                        Projection::Offset {
                            count,
                            ty,
                            in_bounds,
                        } => {
                            let pointee_is_sized =
                                hax::solve_sized(self.hax_state_with_id(), *proj_ty);
                            ConstProjectionElem::Offset {
                                count: IntegerValue::Signed(IntTy::Isize, count as i128),
                                ty: ty
                                    .map(|ty| self.translate_rustc_ty(span, &ty))
                                    .transpose()?,
                                in_bounds,
                                pointee_is_sized: self
                                    .options
                                    .hide_marker_traits
                                    .then_some(self.translate_trait_proof(span, &pointee_is_sized))
                                    .transpose()?
                                    .map(|p| p.no_bound_vars()),
                            }
                        }
                    };
                    place = place.project(proj, self.translate_rustc_ty(span, proj_ty)?);
                }
                let metadata = unsize
                    .map(|unsize| self.translate_const_unsize(span, unsize))
                    .transpose()?;
                match ty.kind() {
                    TyKind::RawPtr(_, rk) => ConstantExprKind::Ptr(*rk, place, metadata),
                    _ => ConstantExprKind::Ref(place, metadata),
                }
            }
            ConstKind::PtrCast { ptr, unsize } => {
                let ptr = self.translate_constant_expr(span, ptr)?;
                let kind = if let Some(unsize) = unsize {
                    let metadata = self.translate_const_unsize(span, *unsize)?;
                    CastKind::Unsize(ty.clone(), metadata)
                } else {
                    CastKind::RawPtr(ty.clone())
                };
                ConstantExprKind::Cast(ptr, kind)
            }
            ConstKind::Memory(bytes) => {
                use rustc_const_uneval::Byte as RByte;
                // The bytes of a pointer share their provenance; we translate it only once.
                let mut last_prov: Option<(AllocTarget, GlobalProvenance)> = None;
                let mut translated_bytes = Vec::with_capacity(bytes.len());
                for byte in bytes {
                    translated_bytes.push(match *byte {
                        RByte::Uninit => Byte::Uninit,
                        RByte::Value(v) => Byte::Value(v),
                        RByte::Ptr(target, i) => {
                            if last_prov.as_ref().is_none_or(|(last, _)| *last != target) {
                                let prov = self.translate_provenance(span, target)?;
                                last_prov = Some((target, prov));
                            }
                            Byte::Provenance(last_prov.as_ref().unwrap().1.clone(), i)
                        }
                    });
                }
                ConstantExprKind::RawMemory(translated_bytes)
            }
            ConstKind::Unsupported(msg) => {
                register_error!(self, span, "Unsupported constant: {:?}", msg);
                ConstantExprKind::Opaque(msg.to_string())
            }
        };

        Ok(ConstantExpr::new(kind, ty))
    }

    pub(crate) fn translate_ty_constant_expr(
        &mut self,
        span: Span,
        c: &ty::Const<'tcx>,
    ) -> Result<ConstantExpr, Error> {
        let tcx = self.tcx;
        let s = self.hax_state_with_id();
        let (kind, ty) = match c.kind() {
            ty::ConstKind::Param(p) => {
                let ty = p.find_const_ty_from_env(s.param_env());
                let kind = match self.lookup_const_generic_var(span, &p.sinto(s)) {
                    Ok(var) => ConstantExprKind::Var(var),
                    Err(err) => ConstantExprKind::Opaque(err.msg),
                };
                (kind, ty)
            }
            ty::ConstKind::Alias(_, ucv) => {
                let def = ucv
                    .kind
                    .opt_def_id()
                    .expect("AliasConstKind with no def id?");
                let src = hax::ConstSource::TyConst(ucv);
                if s.base().options.inline_anon_consts
                    // Rustc hoists inline `const {}` blocks and constant expressions into
                    // separate `AnonConst` items. This is internal to rustc, so we prefer inlining
                    // their value.
                    && matches!(tcx.def_kind(def), rustc_hir::def::DefKind::AnonConst)
                    && let Some(val) =
                        hax::read_const(s, tcx.def_span(def), src, hax::ReadMode::Structured)
                {
                    return self.translate_constant_expr(span, &val);
                }
                let item = hax::translate_item_ref(s, def, ucv.args);
                let ty = tcx.type_of(def).instantiate(tcx, ucv.args);
                let ty = hax::normalize(tcx, s.typing_env(), ty);
                let kind = match &item.in_trait {
                    Some(trait_proof) => {
                        let trait_ref = self.translate_trait_proof(span, trait_proof)?.erase();
                        // Trait consts can't have their own generics.
                        assert!(item.generic_args.is_empty());
                        let const_id =
                            self.translate_assoc_const_id(trait_ref.trait_id(), &item.def_id)?;
                        ConstantExprKind::TraitConst(trait_ref, const_id)
                    }
                    None => {
                        let global_ref = self.translate_global_decl_ref(span, &item)?;
                        ConstantExprKind::Global(global_ref)
                    }
                };
                (kind, ty)
            }
            ty::ConstKind::Value(val) => {
                let src = hax::ConstSource::ValTree(val);
                match hax::read_const(s, rustc_span::DUMMY_SP, src, hax::ReadMode::Structured) {
                    Some(val) => return self.translate_constant_expr(span, &val),
                    None => {
                        register_error!(self, span, "Unsupported constant: ConstValTree");
                        (ConstantExprKind::Opaque("ConstValTree".into()), val.ty)
                    }
                }
            }
            _ => raise_error!(self, span, "Unexpected constant kind: {c:?}"),
        };
        let ty = self.translate_rustc_ty(span, &ty)?;
        Ok(ConstantExpr::new(kind, ty))
    }
}
