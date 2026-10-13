//! Translate constants to hax: type-system constants, and the values read by `rustc_const_uneval`.
use super::*;
use rustc_const_uneval::{AllocTarget, Byte, ConstReader, PtrTarget, ReadError};
use rustc_middle::ty;

#[tracing::instrument(level = "trace", skip(s))]
fn scalar_int_to_constant_literal<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    x: rustc_middle::ty::ScalarInt,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> ConstantLiteral {
    match ty.kind() {
        ty::Char => ConstantLiteral::Char(
            char::try_from(x).s_expect(s, "scalar_int_to_constant_literal: expected a char"),
        ),
        ty::Bool => ConstantLiteral::Bool(
            x.try_to_bool()
                .s_expect(s, "scalar_int_to_constant_literal: expected a bool"),
        ),
        ty::Int(kind) => {
            let v = x.to_int(x.size());
            ConstantLiteral::Int(ConstantInt::Int(v, kind.sinto(s)))
        }
        ty::Uint(kind) => {
            let v = x.to_uint(x.size());
            ConstantLiteral::Int(ConstantInt::Uint(v, kind.sinto(s)))
        }
        ty::Float(kind) => {
            let v = x.to_bits_unchecked();
            bits_and_type_to_float_constant_literal(v, kind.sinto(s))
        }
        _ => {
            let ty_sinto: Ty = ty.sinto(s);
            supposely_unreachable_fatal!(
                s,
                "scalar_int_to_constant_literal_ExpectedLiteralType";
                { ty, ty_sinto, x }
            )
        }
    }
}

/// Converts a bit-representation of a float of type `ty` to a constant literal
fn bits_and_type_to_float_constant_literal(bits: u128, ty: FloatTy) -> ConstantLiteral {
    use rustc_apfloat::{Float, ieee};
    let string = match &ty {
        FloatTy::F16 => ieee::Half::from_bits(bits).to_string(),
        FloatTy::F32 => ieee::Single::from_bits(bits).to_string(),
        FloatTy::F64 => ieee::Double::from_bits(bits).to_string(),
        FloatTy::F128 => ieee::Quad::from_bits(bits).to_string(),
    };
    ConstantLiteral::Float(string, ty)
}

impl ConstantExprKind {
    pub fn decorate(self, ty: Ty, _span: Span) -> Decorated<Self> {
        Decorated {
            contents: Box::new(self),
            ty,
        }
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantExpr> for ty::Const<'tcx> {
    #[tracing::instrument(level = "trace", skip(s))]
    fn sinto(&self, s: &S) -> ConstantExpr {
        let tcx = s.base().tcx;
        let span = rustc_span::DUMMY_SP;
        match self.kind() {
            ty::ConstKind::Param(p) => {
                let ty = p.find_const_ty_from_env(s.param_env());
                let kind = ConstantExprKind::ConstRef { id: p.sinto(s) };
                kind.decorate(ty.sinto(s), span.sinto(s))
            }
            ty::ConstKind::Infer(..) => {
                fatal!(s[span], "ty::ConstKind::Infer node? {:#?}", self)
            }

            ty::ConstKind::Alias(_, ucv) => {
                let def = ucv
                    .kind
                    .opt_def_id()
                    .expect("AliasConstKind with no def id?");
                let src = ConstSource::TyConst(ucv);
                if s.base().options.inline_anon_consts
                    // Rustc hoists inline `const {}` blocks and constant expressions into
                    // separate `AnonConst` items. This is internal to rustc, so we prefer inlining
                    // their value.
                    && matches!(tcx.def_kind(def), rustc_hir::def::DefKind::AnonConst)
                    && let Some(val) = read_const(s, tcx.def_span(def), src, ReadMode::Structured)
                {
                    val
                } else {
                    use rustc_middle::query::QueryKey;
                    let span = tcx
                        .def_ident_span(def)
                        .unwrap_or_else(|| def.default_span(tcx));
                    let item = translate_item_ref(s, def, ucv.args);
                    let kind = ConstantExprKind::NamedGlobal(item);
                    let ty = tcx.type_of(def).instantiate(tcx, ucv.args);
                    let ty = normalize(tcx, s.typing_env(), ty);
                    kind.decorate(ty.sinto(s), span.sinto(s))
                }
            }

            ty::ConstKind::Value(val) => val.sinto(s),
            ty::ConstKind::Error(_) => fatal!(s[span], "ty::ConstKind::Error"),
            ty::ConstKind::Expr(e) => fatal!(s[span], "ty::ConstKind::Expr {:#?}", e),

            ty::ConstKind::Bound(i, bound) => {
                supposely_unreachable_fatal!(s[span], "ty::ConstKind::Bound"; {i, bound})
            }
            _ => fatal!(s[span], "unexpected case"),
        }
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantExpr> for ty::Value<'tcx> {
    #[tracing::instrument(level = "trace", skip(s))]
    fn sinto(&self, s: &S) -> ConstantExpr {
        let span = rustc_span::DUMMY_SP;
        read_const(s, span, ConstSource::ValTree(*self), ReadMode::Structured).unwrap_or_else(
            || {
                ConstantExprKind::Todo("ConstValTree".into())
                    .decorate(self.ty.sinto(s), span.sinto(s))
            },
        )
    }
}

/// The reader for constants evaluated in the current context.
fn const_reader<'tcx, S: UnderOwnerState<'tcx>>(s: &S) -> ConstReader<'tcx> {
    ConstReader {
        tcx: s.base().tcx,
        typing_env: s.typing_env(),
        config: rustc_const_uneval::Config {
            anon_allocs_as_globals: s.base().options.anon_allocs_as_globals,
        },
    }
}

/// The global standing for `self`, which must be named (see `ConstReader::is_named_global`).
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ItemRef> for GlobalRef {
    fn sinto(&self, s: &S) -> ItemRef {
        match *self {
            GlobalRef::Static(did) => translate_item_ref(s, did, Default::default()),
            GlobalRef::Alloc(alloc_id) => {
                let def_id = DefId::make_anon_alloc(s, alloc_id);
                ItemRef::dummy_without_generics(s, def_id)
            }
        }
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, FnPtrTarget> for rustc_const_uneval::FnTarget<'tcx> {
    fn sinto(&self, s: &S) -> FnPtrTarget {
        use rustc_const_uneval::FnTarget;
        match *self {
            FnTarget::Instance(instance) => {
                FnPtrTarget::Fn(translate_item_ref(s, instance.def_id(), instance.args))
            }
            FnTarget::ClosureAsFn(def_id, args) => {
                FnPtrTarget::ClosureAsFn(ClosureArgs::sfrom(s, def_id, args))
            }
        }
    }
}

/// The provenance to give to the bytes of a pointer into the given allocation.
impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantByteProvenance> for AllocTarget<'tcx> {
    fn sinto(&self, s: &S) -> ConstantByteProvenance {
        match *self {
            AllocTarget::Fn(target) => ConstantByteProvenance::Function(target.sinto(s)),
            AllocTarget::Global(global) if const_reader(s).is_named_global(global) => {
                ConstantByteProvenance::Global(global.sinto(s))
            }
            // TODO: TypeIds
            // VTables are not reachable here, I believe: it's UB to attempt reading a VTable's data.
            AllocTarget::Global(_) | AllocTarget::VTable(..) | AllocTarget::TypeId(..) => {
                ConstantByteProvenance::Unknown
            }
        }
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, ConstantExpr> for rustc_const_uneval::Const<'tcx> {
    fn sinto(&self, s: &S) -> ConstantExpr {
        use rustc_const_uneval::ConstKind;
        let tcx = s.base().tcx;
        // The value of a pattern type is described at its base type.
        let ty = match self.ty.kind() {
            ty::Pat(base_ty, _) => *base_ty,
            _ => self.ty,
        };
        let kind = match &self.kind {
            ConstKind::Scalar(scalar_int) => {
                ConstantExprKind::Literal(scalar_int_to_constant_literal(s, *scalar_int, ty))
            }
            ConstKind::PtrNoProvenance(addr) => {
                ConstantExprKind::Literal(ConstantLiteral::PtrNoProvenance(*addr))
            }
            ConstKind::Str(str) => ConstantExprKind::Literal(ConstantLiteral::Str(str.clone())),
            ConstKind::ByteStr(bytes) => {
                ConstantExprKind::Literal(ConstantLiteral::ByteStr(bytes.clone()))
            }
            ConstKind::Aggregate { variant, fields } => {
                let fields = fields.iter().map(|field| field.sinto(s));
                match ty.kind() {
                    ty::Adt(adt_def, _) => {
                        let variant = variant.unwrap();
                        ConstantExprKind::Adt {
                            kind: get_variant_kind(adt_def, variant, s),
                            fields: fields
                                .zip(&adt_def.variant(variant).fields)
                                .map(|(value, field)| ConstantFieldExpr {
                                    field: field.did.sinto(s),
                                    value,
                                })
                                .collect(),
                        }
                    }
                    ty::Closure(def_id, _) => {
                        let def_id: DefId = def_id.sinto(s);
                        ConstantExprKind::Adt {
                            kind: VariantKind::Struct,
                            fields: fields
                                .map(|value| ConstantFieldExpr {
                                    // HACK: Closure fields don't have their own def_id, but Charon
                                    // doesn't use field DefIds so we put a dummy one.
                                    field: def_id.clone(),
                                    value,
                                })
                                .collect(),
                        }
                    }
                    ty::Tuple(_) => ConstantExprKind::Tuple {
                        fields: fields.collect(),
                    },
                    ty::Array(..) | ty::Slice(..) => ConstantExprKind::Array {
                        fields: fields.collect(),
                    },
                    _ => unreachable!("unexpected aggregate type {ty:?}"),
                }
            }
            ConstKind::FnDef { def, args } => {
                ConstantExprKind::FnDef(translate_item_ref(s, *def, args))
            }
            ConstKind::FnPtr(target) => ConstantExprKind::FnPtr(target.sinto(s)),
            ConstKind::Ptr { target, unsize } => {
                let metadata = unsize.map(|unsize| {
                    let ref_to = |ty| ty::Ty::new_imm_ref(tcx, tcx.lifetimes.re_static, ty);
                    compute_unsizing_metadata(s, ref_to(unsize.from), ref_to(unsize.to))
                });
                let arg = match target {
                    PtrTarget::Global { global, ty } => Decorated {
                        contents: Box::new(ConstantExprKind::NamedGlobal(global.sinto(s))),
                        ty: ty.sinto(s),
                    },
                    PtrTarget::Inline(val) => val.sinto(s),
                };
                match ty.kind() {
                    ty::Ref(..) => ConstantExprKind::Borrow(arg, metadata),
                    ty::RawPtr(_, mutability) => ConstantExprKind::RawBorrow {
                        mutability: mutability.sinto(s),
                        arg,
                        metadata,
                    },
                    _ => unreachable!("unexpected pointer type {ty:?}"),
                }
            }
            ConstKind::Memory(bytes) => {
                // The bytes of a pointer share their provenance; we convert it only once.
                let mut last_prov: Option<(AllocTarget, ConstantByteProvenance)> = None;
                let bytes = bytes.iter().map(|byte| match *byte {
                    Byte::Uninit => ConstantByte::Uninit,
                    Byte::Value(v) => ConstantByte::Value(v),
                    Byte::Ptr(target, i) => {
                        if last_prov.as_ref().is_none_or(|(last, _)| *last != target) {
                            last_prov = Some((target, target.sinto(s)));
                        }
                        ConstantByte::Provenance(last_prov.as_ref().unwrap().1.clone(), i)
                    }
                });
                ConstantExprKind::Memory(bytes.collect())
            }
            ConstKind::Unsupported(msg) => ConstantExprKind::Todo(msg.to_string()),
        };
        Decorated {
            contents: Box::new(kind),
            ty: self.ty.sinto(s),
        }
    }
}

/// Evaluate `src` and read it back as a `ConstantExpr`.
pub fn read_const<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    span: rustc_span::Span,
    src: ConstSource<'tcx>,
    mode: ReadMode,
) -> Option<ConstantExpr> {
    match const_reader(s).read(span, src, mode) {
        Ok(val) => Some(val.sinto(s)),
        Err(ReadError::NotEvaluable) => None,
        Err(err) => {
            warning!(s[span], "Couldn't convert constant back to an expression"; {src, err});
            None
        }
    }
}
