//! Hax representations of Rust types and related type operations.

use super::predicates::resolve_for_dyn;

use crate::hax::prelude::*;

use rustc_data_structures::intern::Interned;
use rustc_middle::ty;
use rustc_middle::ty::inherent::IntoKind;
use rustc_span::def_id::DefId as RDefId;

sinto_reexport!(rustc_abi::ExternAbi);

/// Reflects [`rustc_middle::ty::Ty`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ty<'tcx> {
    pub(crate) kind: Interned<'tcx, TyKind<'tcx>>,
}

impl<'tcx> Ty<'tcx> {
    pub fn new<S: BaseState<'tcx>>(s: &S, kind: TyKind<'tcx>) -> Self {
        Ty {
            kind: s.base().ty_interner.intern(kind),
        }
    }

    pub fn kind(&self) -> &TyKind<'tcx> {
        &self.kind
    }

    /// If this type represents something that implements the `Fn*` traits, return the
    /// corresponding item.
    pub fn callable_item(&self) -> Option<&ItemRef<'tcx>> {
        match self.kind() {
            TyKind::Closure(closure) => Some(&closure.item),
            TyKind::FnDef(fn_def) => Some(&fn_def.item),
            TyKind::FnPtr(fn_ptr) => Some(&fn_ptr.item),
            _ => None,
        }
    }
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Ty<'tcx>> for rustc_middle::ty::Ty<'tcx> {
    fn sinto(&self, s: &S) -> Ty<'tcx> {
        if let Some(ty) = s.with_cache(|cache| cache.tys.get(self).cloned()) {
            return ty;
        }
        let kind: TyKind<'tcx> = self.kind().sinto(s);
        let ty = Ty::new(s, kind);
        s.with_cache(|cache| {
            cache.tys.insert(*self, ty.clone());
        });
        ty
    }
}

/// Reflects [`ty::TyKind`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TyKind<'tcx> {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    FnDef(FnDefTy<'tcx>),
    FnPtr(FnPtrTy<'tcx>),
    Closure(ClosureTy<'tcx>),
    Adt(AdtTy<'tcx>),
    Foreign(ForeignTy<'tcx>),
    Array(ArrayTy<'tcx>),
    Pat(PatTy<'tcx>),
    Slice(SliceTy<'tcx>),
    Tuple(TupleTy<'tcx>),
    Str(StrTy<'tcx>),
    RawPtr(RawPtrTy<'tcx>),
    Ref(RefTy<'tcx>),
    DynTrait(DynTraitTy<'tcx>),
    Coroutine(CoroutineTy<'tcx>),
    Never,
    Alias(Alias<'tcx>),
    Param(ParamTy),
    Bound(BoundTyRef),
    Placeholder(PlaceholderTy),
    Infer(InferTy),
    Error,
    Todo(String),
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, TyKind<'tcx>> for ty::TyKind<'tcx> {
    #[tracing::instrument(level = "trace", skip(s))]
    fn sinto(&self, s: &S) -> TyKind<'tcx> {
        let base = s.base();
        let tcx = base.tcx;
        match self {
            Self::Bool => TyKind::Bool,
            Self::Char => TyKind::Char,
            Self::Int(int_ty) => TyKind::Int(int_ty.sinto(s)),
            Self::Uint(uint_ty) => TyKind::Uint(uint_ty.sinto(s)),
            Self::Float(float_ty) => TyKind::Float(float_ty.sinto(s)),
            Self::FnDef(fun_id, generics) => {
                // Note: loss of precision, we erase the bound vars.
                let generics = erase_free_regions(tcx, generics.skip_binder());
                TyKind::FnDef(FnDefTy {
                    item: translate_item_ref(s, *fun_id, generics),
                })
            }
            Self::FnPtr(tys, header) => {
                let sig = tys.with(*header);
                let item = ItemRef::translate_fn_ptr(s, sig);
                TyKind::FnPtr(FnPtrTy {
                    sig: Box::new(sig.sinto(s)),
                    item,
                })
            }
            Self::Closure(def_id, generics) => {
                TyKind::Closure(ClosureTy::sfrom(s, *def_id, generics))
            }
            Self::Adt(adt_def, generics) => TyKind::Adt(AdtTy {
                item: translate_item_ref(s, adt_def.did(), generics),
            }),
            Self::Foreign(def_id) => TyKind::Foreign(ForeignTy {
                item: translate_item_ref(s, *def_id, Default::default()),
            }),
            Self::Array(ty, len) => {
                let args = tcx.mk_args(&[(*ty).into(), (*len).into()]);
                let sized_trait = tcx.lang_items().sized_trait().unwrap();
                TyKind::Array(ArrayTy {
                    item: ItemRef::translate_synthetic(s, SyntheticItem::Array, args),
                    has_sized_proof: !base
                        .elab_ctx
                        .bounds_options()
                        .remove_traits
                        .contains(&sized_trait),
                })
            }
            Self::Pat(ty, pat) => TyKind::Pat(PatTy {
                ty: ty.sinto(s),
                pat: pat.sinto(s),
            }),
            Self::Slice(ty) => {
                let args = tcx.mk_args(&[(*ty).into()]);
                let sized_trait = tcx.lang_items().sized_trait().unwrap();
                TyKind::Slice(SliceTy {
                    item: ItemRef::translate_synthetic(s, SyntheticItem::Slice, args),
                    has_sized_proof: !base
                        .elab_ctx
                        .bounds_options()
                        .remove_traits
                        .contains(&sized_trait),
                })
            }
            Self::Tuple(tys) => {
                let args = tcx.mk_args_from_iter(tys.into_iter().map(ty::GenericArg::from));
                TyKind::Tuple(TupleTy {
                    item: ItemRef::translate_synthetic(s, SyntheticItem::Tuple(tys.len()), args),
                })
            }
            Self::Str => {
                let args = tcx.mk_args(&[]);
                TyKind::Str(StrTy {
                    item: ItemRef::translate_synthetic(s, SyntheticItem::Str, args),
                })
            }
            Self::RawPtr(ty, mutbl) => TyKind::RawPtr(RawPtrTy {
                ty: ty.sinto(s),
                mutbl: mutbl.sinto(s),
            }),
            Self::Ref(region, ty, mutbl) => TyKind::Ref(RefTy {
                region: region.sinto(s),
                ty: ty.sinto(s),
                mutbl: mutbl.sinto(s),
            }),
            Self::Dynamic(preds, region) => TyKind::DynTrait(DynTraitTy {
                binder: resolve_for_dyn(s, preds, |_, _| ()),
                region: region.sinto(s),
            }),
            Self::Coroutine(def_id, generics) => TyKind::Coroutine(CoroutineTy {
                item: translate_item_ref(s, *def_id, generics),
            }),
            Self::Never => TyKind::Never,
            Self::Alias(_, alias_ty) => Alias::from(s, alias_ty),
            Self::Param(param) => TyKind::Param(param.sinto(s)),
            Self::Bound(index, ty) => TyKind::Bound(BoundTyRef {
                index: index.sinto(s),
                ty: ty.sinto(s),
            }),
            Self::Placeholder(placeholder) => TyKind::Placeholder(placeholder.sinto(s)),
            Self::Infer(infer) => TyKind::Infer(infer.sinto(s)),
            Self::Error(..) => TyKind::Error,
            other => TyKind::Todo(format!("{other:?}")),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnDefTy<'tcx> {
    pub item: ItemRef<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnPtrTy<'tcx> {
    pub sig: Box<PolyFnSig<'tcx>>,
    /// Points to a synthetic item used to build impls for function pointer types.
    pub item: ItemRef<'tcx>,
}

/// Reflects [`ty::ClosureArgs`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClosureTy<'tcx> {
    pub item: ItemRef<'tcx>,
}

impl<'tcx> ClosureTy<'tcx> {
    /// The base kind of this closure. The kinds are ordered by inclusion: any `Fn` works as an
    /// `FnMut`, and any `FnMut` works as an `FnOnce`.
    pub fn kind(&self, s: &impl BaseState<'tcx>) -> ClosureKind {
        let s = &s.with_hax_owner(&self.item.def_id);
        self.item.rustc_args(s).as_closure().kind().sinto(s)
    }

    /// The signature of the function that this closure implements, e.g. `fn(A, B, C) -> D`.
    pub fn fn_sig(&self, s: &impl BaseState<'tcx>) -> PolyFnSig<'tcx> {
        let s = &s.with_hax_owner(&self.item.def_id);
        let args = self.item.rustc_args(s);
        closure_sig(s.tcx(), args.as_closure()).sinto(s)
    }

    /// The arguments, tupled as the `Fn*` traits take them, e.g. `(A, B, C)`.
    /// Binds the same variables as `fn_sig()`.
    pub fn tupled_args_ty(&self, s: &impl BaseState<'tcx>) -> Binder<Ty<'tcx>> {
        let s = &s.with_hax_owner(&self.item.def_id);
        let args = self.item.rustc_args(s);
        let sig = closure_sig(s.tcx(), args.as_closure());
        tupled_args_ty(s, sig).sinto(s)
    }

    // Manual implementation because we need the `def_id` of the closure.
    pub fn sfrom<S>(s: &S, def_id: RDefId, from: ty::GenericArgsRef<'tcx>) -> Self
    where
        S: UnderOwnerState<'tcx>,
    {
        let item = translate_item_ref(s, def_id, from);
        ClosureTy { item }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtTy<'tcx> {
    pub item: ItemRef<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ForeignTy<'tcx> {
    pub item: ItemRef<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArrayTy<'tcx> {
    pub item: ItemRef<'tcx>,
    has_sized_proof: bool,
}

impl<'tcx> ArrayTy<'tcx> {
    /// The `Sized` proof for the element type, if we're not hiding `Sized`.
    pub fn element_sized_proof(&self) -> Option<&TraitProof<'tcx>> {
        if self.has_sized_proof {
            Some(&self.item.trait_proofs[0])
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PatTy<'tcx> {
    pub ty: Ty<'tcx>,
    pub pat: Pattern<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SliceTy<'tcx> {
    pub item: ItemRef<'tcx>,
    has_sized_proof: bool,
}

impl<'tcx> SliceTy<'tcx> {
    /// The `Sized` proof for the element type, if we're not hiding `Sized`.
    pub fn element_sized_proof(&self) -> Option<&TraitProof<'tcx>> {
        if self.has_sized_proof {
            Some(&self.item.trait_proofs[0])
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TupleTy<'tcx> {
    pub item: ItemRef<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StrTy<'tcx> {
    pub item: ItemRef<'tcx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RawPtrTy<'tcx> {
    pub ty: Ty<'tcx>,
    pub mutbl: Mutability,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RefTy<'tcx> {
    pub region: Region,
    pub ty: Ty<'tcx>,
    pub mutbl: Mutability,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DynTraitTy<'tcx> {
    pub binder: DynBinder<'tcx, ()>,
    pub region: Region,
}

impl<'tcx> DynTraitTy<'tcx> {
    /// The principal trait clause, if any.
    pub fn principal_trait_clause(&self) -> Option<&Binder<ClauseKind<'tcx>>> {
        let clause = &self.binder.predicates.predicates.first()?.clause.kind;
        if matches!(clause.hax_skip_binder_ref(), ClauseKind::Trait(_)) {
            Some(clause)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CoroutineTy<'tcx> {
    pub item: ItemRef<'tcx>,
}

/// Reflects [`ty::UserSelfTy`]
#[derive(Debug, Clone, AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::UserSelfTy<'tcx>, state: S as gstate)]
pub struct UserSelfTy<'tcx> {
    pub impl_def_id: DefId,
    pub self_ty: Ty<'tcx>,
}

/// Reflects [`ty::UserArgs`]
#[derive(Debug, Clone, AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::UserArgs<'tcx>, state: S as gstate)]
pub struct UserArgs<'tcx> {
    pub args: Vec<GenericArg<'tcx>>,
    pub user_self_ty: Option<UserSelfTy<'tcx>>,
}

/// Reflects [`ty::UserType`]: this is currently
/// disabled, and everything is printed as debug in the
/// [`UserType::Todo`] variant.
#[derive(Debug, Clone, AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::UserType<'tcx>, state: S as _s)]
pub enum UserType {
    // TODO: for now, we don't use user types at all.
    // We disable it for now, since it cause the following to fail:
    //
    //    pub const MY_VAL: u16 = 5;
    //    pub type Alias = MyStruct<MY_VAL>; // Using the literal 5, it goes through
    //
    //    pub struct MyStruct<const VAL: u16> {}
    //
    //    impl<const VAL: u16> MyStruct<VAL> {
    //        pub const MY_CONST: u16 = VAL;
    //    }
    //
    //    pub fn do_something() -> u32 {
    //        u32::from(Alias::MY_CONST)
    //    }
    //
    // In this case, we get a [ty::ConstKind::Bound] in
    // [do_something], which we are not able to translate.
    // See: https://github.com/hacspec/hax/pull/209

    // Ty(Ty),
    // TypeOf(DefId, UserArgs),
    #[todo]
    Todo(String),
}

/// Reflects [`rustc_ast::ast::LitIntType`]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_ast::ast::LitIntType, state: S as gstate)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LitIntType {
    Signed(IntTy),
    Unsigned(UintTy),
    Unsuffixed,
}

/// Reflects [`ty::IntTy`]
#[derive(AdtInto)]
#[args(<S>, from: ty::IntTy, state: S as _s)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

/// Reflects [`ty::FloatTy`]
#[derive(AdtInto)]
#[args(<S>, from: ty::FloatTy, state: S as _s)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

/// Reflects [`ty::UintTy`]
#[derive(AdtInto)]
#[args(<S>, from: ty::UintTy, state: S as _s)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[allow(clippy::to_string_trait_impl)]
impl ToString for IntTy {
    fn to_string(&self) -> String {
        use IntTy::*;
        match self {
            Isize => "isize".to_string(),
            I8 => "i8".to_string(),
            I16 => "i16".to_string(),
            I32 => "i32".to_string(),
            I64 => "i64".to_string(),
            I128 => "i128".to_string(),
        }
    }
}

#[allow(clippy::to_string_trait_impl)]
impl ToString for UintTy {
    fn to_string(&self) -> String {
        use UintTy::*;
        match self {
            Usize => "usize".to_string(),
            U8 => "u8".to_string(),
            U16 => "u16".to_string(),
            U32 => "u32".to_string(),
            U64 => "u64".to_string(),
            U128 => "u128".to_string(),
        }
    }
}

/// Reflects [`ty::TypeAndMut`]
#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::TypeAndMut<'tcx>, state: S as gstate)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeAndMut<'tcx> {
    pub ty: Ty<'tcx>,
    pub mutbl: Mutability,
}

impl<S, U, T: SInto<S, U>> SInto<S, Vec<U>> for ty::List<T> {
    fn sinto(&self, s: &S) -> Vec<U> {
        self.iter().map(|x| x.sinto(s)).collect()
    }
}

/// This type merges the information from
/// [`ty::AliasTyKind`] and [`ty::AliasTy`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Alias<'tcx> {
    pub kind: AliasKind<'tcx>,
    pub args: Vec<GenericArg<'tcx>>,
    pub def_id: DefId,
}

/// Reflects [`rustc_middle::ty::AliasTyKind`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AliasKind<'tcx> {
    /// The projection of a trait type: `<Ty as Trait<...>>::Type<...>`
    Projection(ItemRef<'tcx>),
    /// An associated type in an inherent impl.
    Inherent,
    /// An `impl Trait` opaque type.
    Opaque {
        /// The real type hidden inside this opaque type.
        hidden_ty: Ty<'tcx>,
    },
    /// A type alias that references opaque types. Likely to always be normalized away.
    Free,
}

pub fn alias_ty_kind_def_id<'tcx>(kind: ty::AliasTyKind<'tcx>) -> RDefId {
    match kind {
        ty::AliasTyKind::Projection { def_id }
        | ty::AliasTyKind::Inherent { def_id }
        | ty::AliasTyKind::Opaque { def_id }
        | ty::AliasTyKind::Free { def_id } => def_id,
    }
}

impl<'tcx> Alias<'tcx> {
    #[tracing::instrument(level = "trace", skip(s))]
    fn from<S: UnderOwnerState<'tcx>>(s: &S, alias_ty: &ty::AliasTy<'tcx>) -> TyKind<'tcx> {
        let tcx = s.base().tcx;
        let typing_env = s.typing_env();
        use ty::AliasTyKind as RustAliasKind;

        // Try to normalize the alias first.
        let ty = ty::Ty::new_alias(tcx, ty::IsRigid::No, *alias_ty);
        let ty = normalize(tcx, typing_env, ty::Unnormalized::new(ty));
        let ty::Alias(_is_rigid, alias_ty) = ty.kind() else {
            let ty: Ty = ty.sinto(s);
            return ty.kind().clone();
        };

        let kind = match alias_ty.kind {
            RustAliasKind::Projection { def_id } => {
                AliasKind::Projection(ItemRef::translate_projection(s, def_id, alias_ty.args))
            }
            RustAliasKind::Inherent { .. } => AliasKind::Inherent,
            RustAliasKind::Opaque { def_id } => {
                // Reveal the underlying `impl Trait` type.
                let ty = tcx.type_of(def_id).instantiate(tcx, alias_ty.args);
                let ty = normalize(tcx, s.typing_env(), ty);
                AliasKind::Opaque {
                    hidden_ty: ty.sinto(s),
                }
            }
            RustAliasKind::Free { .. } => AliasKind::Free,
        };
        TyKind::Alias(Alias {
            kind,
            args: alias_ty.args.sinto(s),
            def_id: alias_ty_kind_def_id(alias_ty.kind).sinto(s),
        })
    }
}

#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::pattern::PatternKind<'tcx>, state: S as gstate)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern<'tcx> {
    Range {
        start: ConstantExpr<'tcx>,
        end: ConstantExpr<'tcx>,
    },
    Or(Vec<Pattern<'tcx>>),
    NotNull,
}

impl<'tcx, S: UnderOwnerState<'tcx>> SInto<S, Pattern<'tcx>> for ty::Pattern<'tcx> {
    fn sinto(&self, s: &S) -> Pattern<'tcx> {
        self.kind().sinto(s)
    }
}
/// Reflects [`ty::CanonicalUserTypeAnnotation`]
#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::CanonicalUserTypeAnnotation<'tcx>, state: S as gstate)]
#[derive(Debug, Clone)]
pub struct CanonicalUserTypeAnnotation<'tcx> {
    pub user_ty: CanonicalUserType,
    pub span: Span,
    pub inferred_ty: Ty<'tcx>,
}

/// The metadata to attach to the newly-unsized ptr.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnsizingMetadata<'tcx> {
    /// Unsize an array to a slice, storing the length as metadata.
    Length(ConstantExpr<'tcx>),
    /// Unsize a non-dyn type to a dyn type, adding a vtable pointer as metadata.
    DirectVTable(TraitProof<'tcx>),
    /// Unsize a dyn-type to another dyn-type, (optionally) indexing within the current vtable.
    NestedVTable(DynBinder<'tcx, TraitProof<'tcx>>),
    /// Couldn't compute
    Unknown,
}

pub fn compute_unsizing_metadata<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    src_ty: ty::Ty<'tcx>,
    tgt_ty: ty::Ty<'tcx>,
) -> UnsizingMetadata<'tcx> {
    // TODO: also pass the list of fields we go through in the unsizing metadata.

    let tcx = s.base().tcx;
    let (Some(src_ty), Some(tgt_ty)) = (src_ty.builtin_deref(true), tgt_ty.builtin_deref(true))
    else {
        // Like `rustc_monomorphize::custom_coerce_unsize_info`: for a `CoerceUnsized` struct
        // (e.g. `Rc`), find the impl and recurse into the field it coerces.
        return match (src_ty.kind(), tgt_ty.kind()) {
            (ty::Adt(def, src_args), ty::Adt(_, tgt_args)) => {
                let coerce_trait = tcx.lang_items().coerce_unsized_trait().unwrap();
                let tref = ty::TraitRef::new(tcx, coerce_trait, [src_ty, tgt_ty]);
                let proof =
                    s.with_predicate_searcher(|ps, ctx| ps.resolve(ctx, &ty::Binder::dummy(tref)));
                let elaboration::TraitProofKind::Concrete(impl_ref) = &proof.contents().kind else {
                    unreachable!("`CoerceUnsized` between ADTs is always proven by a concrete impl")
                };
                let info = tcx
                    .coerce_unsized_info(impl_ref.def_id.real_rust_def_id())
                    .unwrap();
                // TODO: just accumulate this field index as we recurse down, for the consumer.
                let ty::adjustment::CustomCoerceUnsized::Struct(i) = info.custom_kind.unwrap();
                let field = &def.non_enum_variant().fields[i];
                let typing_env = s.typing_env();
                let src_ty = normalize(tcx, typing_env, field.ty(tcx, src_args));
                let tgt_ty = normalize(tcx, typing_env, field.ty(tcx, tgt_args));
                compute_unsizing_metadata(s, src_ty, tgt_ty)
            }
            (ty::Pat(a, _), ty::Pat(b, _)) => compute_unsizing_metadata(s, *a, *b),
            _ => UnsizingMetadata::Unknown,
        };
    };
    let typing_env = s.typing_env();
    let (src_ty, tgt_ty) =
        tcx.struct_lockstep_tails_raw(src_ty, tgt_ty, |ty| normalize(tcx, typing_env, ty));

    match (&src_ty.kind(), &tgt_ty.kind()) {
        (ty::Array(_, len), ty::Slice(_) | ty::Str) => {
            let len = len.sinto(s);
            UnsizingMetadata::Length(len)
        }
        (ty::Dynamic(from_preds, _), ty::Dynamic(to_preds, ..)) => {
            let trait_proof = resolve_for_dyn(s, from_preds, |searcher, fresh_ty| {
                let to_pred = if let Some(to_principal) = to_preds.principal() {
                    to_principal.with_self_ty(tcx, fresh_ty)
                } else {
                    let def_id = to_preds
                        .iter()
                        .find_map(|pred| match pred.skip_binder() {
                            ty::ExistentialPredicate::AutoTrait(def_id) => Some(def_id),
                            _ => None,
                        })
                        .expect("expected a trait predicate in dyn upcast target");
                    ty::Binder::dummy(ty::TraitRef::new(tcx, def_id, [fresh_ty]))
                };
                searcher.resolve(&s.base_state(), &to_pred)
            });
            UnsizingMetadata::NestedVTable(trait_proof)
        }
        (_, ty::Dynamic(preds, ..)) => {
            let pred = preds[0].with_self_ty(tcx, src_ty);
            let clause = pred.as_trait_clause().expect(
                "the first `ExistentialPredicate` of `TyKind::Dynamic` \\
                                        should be a trait clause",
            );
            let tref = clause.rebind(clause.skip_binder().trait_ref);
            let trait_proof = solve_trait(s, tref);

            UnsizingMetadata::DirectVTable(trait_proof)
        }
        _ => UnsizingMetadata::Unknown,
    }
}

/// Reflects [`ty::FnSig`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(< S: UnderOwnerState<'tcx>>, from: ty::FnSig<'tcx>, state: S as s)]
pub struct TyFnSig<'tcx> {
    #[value(self.inputs().sinto(s))]
    pub inputs: Vec<Ty<'tcx>>,
    #[value(self.output().sinto(s))]
    pub output: Ty<'tcx>,
    #[value(self.c_variadic())]
    pub c_variadic: bool,
    #[value(self.safety())]
    pub safety: Safety,
    #[value(self.abi())]
    pub abi: ExternAbi,
}

/// Reflects [`ty::PolyFnSig`]
pub type PolyFnSig<'tcx> = Binder<TyFnSig<'tcx>>;

/// The arguments of the given signature, tupled as the `Fn*` traits take them, e.g. `(A, B, C)`.
/// The result binds the same variables as the signature it comes from, so that the two agree on
/// the regions they use.
pub fn tupled_args_ty<'tcx>(
    s: &impl UnderOwnerState<'tcx>,
    sig: ty::PolyFnSig<'tcx>,
) -> ty::Binder<'tcx, ty::Ty<'tcx>> {
    let tcx = s.base().tcx;
    sig.map_bound(|sig| ty::Ty::new_tup(tcx, sig.inputs()))
}

/// Retrieve a closure's signature, recovering the regions that rustc erased as fresh bound
/// regions.
pub fn closure_sig<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    closure: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
) -> ty::PolyFnSig<'tcx> {
    use ty::TypeFoldable;
    use ty::TypeSuperFoldable;

    struct RegionUnEraserVisitor<'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        depth: u32,
        bound_vars: Vec<ty::BoundVariableKind<'tcx>>,
    }

    impl<'tcx> ty::TypeFolder<ty::TyCtxt<'tcx>> for RegionUnEraserVisitor<'tcx> {
        fn cx(&self) -> ty::TyCtxt<'tcx> {
            self.tcx
        }

        fn fold_ty(&mut self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
            ty.super_fold_with(self)
        }

        fn fold_binder<T>(&mut self, t: ty::Binder<'tcx, T>) -> ty::Binder<'tcx, T>
        where
            T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
        {
            self.depth += 1;
            let t = t.super_fold_with(self);
            self.depth -= 1;
            t
        }

        fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
            // Replace erased regions with fresh bound regions.
            if r.is_erased() {
                let bound_region = ty::BoundRegion {
                    var: ty::BoundVar::from_usize(self.bound_vars.len()),
                    kind: ty::BoundRegionKind::Anon,
                };
                self.bound_vars
                    .push(ty::BoundVariableKind::Region(bound_region.kind));
                ty::Region::new_bound(self.tcx, ty::DebruijnIndex::from(self.depth), bound_region)
            } else {
                r
            }
        }
    }

    let sig = closure.sig();
    let sig = tcx.signature_unclosure(sig, rustc_hir::Safety::Safe);
    let mut visitor = RegionUnEraserVisitor {
        tcx,
        depth: 0,
        bound_vars: sig.bound_vars().iter().collect(),
    };
    let unbound_sig = sig.skip_binder().fold_with(&mut visitor);
    let bound_vars = tcx.mk_bound_variable_kinds(&visitor.bound_vars);
    ty::Binder::bind_with_vars(unbound_sig, bound_vars)
}

/// Reflects [`ty::ClosureKind`]
#[derive(AdtInto)]
#[args(<'tcx, S: UnderOwnerState<'tcx>>, from: ty::ClosureKind, state: S as _tcx)]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}
