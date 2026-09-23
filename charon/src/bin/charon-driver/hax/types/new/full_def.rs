use crate::hax::prelude::*;

use rustc_attr_ir::LangItem;
use rustc_hir as hir;
use rustc_hir::def::DefKind as RDefKind;
use rustc_middle::mir;
use rustc_middle::ty;
use rustc_span::def_id::DefId as RDefId;
use std::cell::OnceCell;
use std::sync::Arc;

/// Gathers a lot of definition information about a [`rustc_hir::def_id::DefId`].
#[derive(Debug, Clone)]
pub struct FullDef<'tcx> {
    /// A reference to the current item. If the item was provided with generic args, they are
    /// stored here; otherwise the args are the identity_args for this item.
    pub this: ItemRef,
    /// The span of the definition of this item (e.g. for a function this is is signature).
    pub span: Span,
    /// The span of the whole definition (including e.g. the function body).
    pub source_span: Option<Span>,
    /// The text of the whole definition.
    pub source_text: Option<String>,
    /// Attributes on this definition, if applicable.
    pub attributes: Vec<hir::Attribute>,
    /// Visibility of the definition, for definitions where this makes sense.
    pub visibility: Option<bool>,
    /// If this definition is a lang item, we store the identifier, e.g. `sized`.
    pub lang_item: Option<Symbol>,
    /// If this definition is a diagnostic item, we store the identifier, e.g. `box_new`.
    pub diagnostic_item: Option<Symbol>,
    pub kind: FullDefKind<'tcx>,
}

/// Construct the `FullDefKind` for this item. If `args` is `Some`, the returned `FullDef` will be
/// instantiated with the provided generics.
fn translate_full_def<'tcx, S>(
    s: &S,
    def_id: &DefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> FullDef<'tcx>
where
    S: UnderOwnerState<'tcx>,
{
    let tcx = s.base().tcx;
    let this = if def_id.can_have_generics(s) {
        let args_or_default = args.unwrap_or_else(|| def_id.identity_args(s));
        ItemRef::translate_from_hax_def_id(s, def_id.clone(), args_or_default)
    } else {
        ItemRef::dummy_without_generics(s, def_id.clone())
    };

    let source_span;
    let lang_item;
    let diagnostic_item;
    let kind;
    match def_id.base {
        DefIdBase::Synthetic(item) => {
            match item {
                SyntheticItem::Array
                | SyntheticItem::Slice
                | SyntheticItem::Tuple(..)
                | SyntheticItem::Str => {
                    let adt_kind = match item {
                        SyntheticItem::Array => AdtKind::Array,
                        SyntheticItem::Slice => AdtKind::Slice,
                        SyntheticItem::Tuple(..) => AdtKind::Tuple,
                        SyntheticItem::Str => AdtKind::Str,
                        SyntheticItem::FnPtr(_) => unreachable!(),
                    };
                    kind = FullDefKind::Adt(Adt {
                        def_id: def_id.clone(),
                        self_ty: inst_binder(tcx, s.typing_env(), args, def_id.type_of(s)),
                        param_env: get_param_env(s, args),
                        adt_kind,
                        variants: [].into_iter().collect(),
                        repr: ReprOptions {
                            int_specified: false,
                            typ: Ty::new(s, TyKind::Int(IntTy::Isize)),
                            align: None,
                            pack: None,
                            flags: Default::default(),
                        },
                        destruct_impl: Default::default(),
                    });
                }
                SyntheticItem::FnPtr(_) => {
                    let self_ty = inst_binder(tcx, s.typing_env(), args, def_id.type_of(s));
                    let ty::TyKind::FnPtr(sig_tys, header) = self_ty.kind() else {
                        unreachable!()
                    };
                    let sig = sig_tys.with(*header);
                    let late_bound_scope = item.late_bound_scope(s);
                    kind = FullDefKind::FnPtr(FnPointer {
                        def_id: def_id.clone(),
                        self_ty,
                        rustc_sig: sig,
                        param_env: get_param_env(s, args),
                        sig: sig.sinto(s),
                        late_bound_scope,
                        fn_trait_impls: OnceCell::new(),
                    });
                }
            }

            source_span = None;
            lang_item = Default::default();
            diagnostic_item = Default::default();
        }
        DefIdBase::Promoted(rust_def_id, promoted_id) => {
            let parent_def_id = rust_def_id.sinto(s);
            let parent_def = parent_def_id.full_def_maybe_instantiated(s, args);
            let param_env = ParamEnv::empty(s, Some(parent_def.this()));
            let body = get_promoted_mir(tcx, rust_def_id, promoted_id);
            source_span = Some(body.span);

            let ty = body.local_decls[rustc_middle::mir::Local::ZERO].ty;
            let ty = substitute(tcx, s.typing_env(), args, ty).sinto(s);
            kind = FullDefKind::Const(Const {
                param_env,
                ty,
                kind: ConstKind::PromotedConst,
            });

            lang_item = Default::default();
            diagnostic_item = Default::default();
        }
        DefIdBase::Real(rust_def_id) => {
            kind = translate_full_def_kind(s, &this, args);

            source_span = rust_def_id.as_local().map(|ldid| tcx.source_span(ldid));
            lang_item = s
                .base()
                .tcx
                .as_lang_item(rust_def_id)
                .map(|litem| litem.name())
                .sinto(s);
            diagnostic_item = tcx.get_diagnostic_name(rust_def_id).sinto(s);
        }
        DefIdBase::Alloc(alloc_id) => {
            kind = FullDefKind::Static(Static {
                param_env: ParamEnv::empty(s, None),
                safety: Safety::Safe,
                mutability: tcx
                    .global_alloc(alloc_id)
                    .unwrap_memory()
                    .inner()
                    .mutability,
                thread_local: false,
                ty: def_id
                    .type_of(s)
                    .instantiate_identity()
                    .skip_normalization()
                    .sinto(s),
            });
            source_span = None;
            lang_item = Default::default();
            diagnostic_item = Default::default();
        }
        DefIdBase::ImplAssocItem(_) => {
            panic!("virtual trait impl associated items do not have `FullDef`s")
        }
    }

    let attributes = def_id.attrs(tcx).to_vec();
    let visibility = def_id.visibility(tcx);
    let source_text = source_span
        .filter(|source_span| source_span.ctxt().is_root())
        .and_then(|source_span| tcx.sess.source_map().span_to_snippet(source_span).ok());
    FullDef {
        this,
        span: def_id.def_span(s),
        source_span: source_span.sinto(s),
        source_text,
        attributes,
        visibility,
        lang_item,
        diagnostic_item,
        kind,
    }
}

impl DefId {
    /// Get the full definition of this item.
    pub fn full_def<'tcx, S>(&self, s: &S) -> Arc<FullDef<'tcx>>
    where
        S: BaseState<'tcx>,
    {
        self.full_def_maybe_instantiated(s, None)
    }

    /// Get the full definition of this item, instantiated if `args` is `Some`.
    pub fn full_def_maybe_instantiated<'tcx, S>(
        &self,
        s: &S,
        args: Option<ty::GenericArgsRef<'tcx>>,
    ) -> Arc<FullDef<'tcx>>
    where
        S: BaseState<'tcx>,
    {
        let s = &s.with_hax_owner(self);
        let cache_key = (self.promoted_id(), args);
        if let Some(def) = s.with_cache(|cache| cache.full_defs.get(&cache_key).cloned()) {
            return def;
        }
        let def = Arc::new(translate_full_def(s, self, args));
        s.with_cache(|cache| {
            cache.full_defs.insert(cache_key, def.clone());
        });
        def
    }
}

impl ItemRef {
    /// Get the full definition of the item, instantiated with the provided generics.
    pub fn instantiated_full_def<'tcx, S>(&self, s: &S) -> Arc<FullDef<'tcx>>
    where
        S: BaseState<'tcx>,
    {
        let args = self.rustc_args(s);
        self.def_id.full_def_maybe_instantiated(s, Some(args))
    }

    /// Get the drop glue shim for this. Panics if the `DefKind` isn't appropriate.
    pub fn drop_glue_shim<'tcx, S>(&self, s: &S) -> mir::Body<'tcx>
    where
        S: BaseState<'tcx>,
    {
        let s = &s.with_hax_owner(&self.def_id);
        let args = self.rustc_args(s);
        crate::hax::drop_glue_shim(s, &self.def_id, Some(args))
    }

    /// For `FnMut`&`Fn` closures: the MIR for the `call_once` method; it simply calls
    /// `call_mut`.
    pub fn closure_once_shim<'tcx, S>(&self, s: &S) -> Option<mir::Body<'tcx>>
    where
        S: BaseState<'tcx>,
    {
        let tcx = s.base().tcx;
        let s = &s.with_hax_owner(&self.def_id);
        let args = self.rustc_args(s);
        let closure_ty = inst_binder(tcx, s.typing_env(), Some(args), self.def_id.type_of(s));
        crate::hax::closure_once_shim(tcx, closure_ty)
    }
}

/// The combination of type generics and related predicates.
#[derive(Debug, Clone)]
pub struct ParamEnv {
    /// Generic parameters of the item.
    pub generics: TyGenerics,
    /// Required predicates for the item (see `traits::utils::required_predicates`).
    pub predicates: GenericPredicates,
    /// A reference to the parent of this item, with appropriate args.
    pub parent: Option<ItemRef>,
}

impl ParamEnv {
    pub fn for_each_generics<'tcx>(
        &self,
        s: &impl BaseState<'tcx>,
        f: &mut impl FnMut(&GenericParamDef),
    ) {
        if let Some(parent) = &self.parent {
            let def = parent.def_id.full_def(s);
            def.param_env().unwrap().for_each_generics(s, f);
        }
        for param in &self.generics.params {
            f(param)
        }
    }

    pub fn empty<'tcx>(s: &impl BaseState<'tcx>, parent: Option<&ItemRef>) -> ParamEnv {
        ParamEnv {
            generics: TyGenerics {
                parent: parent.map(|p| p.def_id.clone()),
                parent_count: parent
                    .map(|parent| parent.def_id.generics_of(s).count())
                    .unwrap_or(0),
                params: vec![],
                has_self: false,
                has_late_bound_regions: None,
            },
            predicates: GenericPredicates { predicates: vec![] },
            parent: parent.cloned(),
        }
    }
}

/// The kind of a constant item.
#[derive(Debug, Clone)]
pub enum ConstKind {
    /// Top-level constant: `const CONST: usize = 42;`
    TopLevel,
    /// Anonymous constant, e.g. the `1 + 2` in `[u8; 1 + 2]`, or `const { 1 + 2 }`
    AnonConst,
    /// A promoted constant, e.g. the `1 + 2` in `&(1 + 2)`
    PromotedConst,
}

/// Reflects [`rustc_hir::attrs::InlineAttr`]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[derive(AdtInto)]
#[args(<'tcx, S: BaseState<'tcx>>, from: rustc_hir::attrs::InlineAttr, state: S as _s)]
pub enum InlineAttr {
    None,
    Hint,
    Always,
    Never,
    Force {
        attr_span: Span,
        reason: Option<Symbol>,
    },
}

/// Imbues [`rustc_hir::def::DefKind`] with a lot of extra information.

#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum FullDefKind<'tcx> {
    // Types
    /// ADts (`Struct`, `Enum` and `Union` map to this variant).
    Adt(Adt<'tcx>),
    /// Type alias: `type Foo = Bar;`
    TyAlias(TyAlias),
    /// Type from an `extern` block.
    ForeignTy,
    /// Associated type: `trait MyTrait { type Assoc; }`
    AssocTy(AssocTy<'tcx>),
    /// Opaque type, aka `impl Trait`.
    OpaqueTy,

    // Traits
    Trait(Trait<'tcx>),
    /// Trait alias: `trait IntIterator = Iterator<Item = i32>;`
    TraitAlias(TraitAlias),
    TraitImpl(TraitImpl<'tcx>),
    InherentImpl(InherentImpl<'tcx>),

    // Functions
    Fn(Fn<'tcx>),
    /// Synthetic item representing a particular shape of function pointer types.
    /// E.g. `for<'a> fn(&'a u32) -> Adt<'a, u32>` is considered to be an instantiation of the fake
    /// item `for<'a> fn(&'a A) -> Adt<'a, B>` with `A=B=u32`. Note how the item can therefore
    /// have trait clauses if some Adt does.
    FnPtr(FnPointer<'tcx>),
    /// Associated function: `impl MyStruct { fn associated() {} }` or `trait Foo { fn associated()
    /// {} }`
    AssocFn(AssocFn<'tcx>),
    /// A closure, coroutine, or coroutine-closure.
    Closure(Closure<'tcx>),

    // Constants
    Const(Const),
    /// Associated constant: `trait MyTrait { const ASSOC: usize; }`
    AssocConst(AssocConst),
    Static(Static),

    // Crates and modules
    ExternCrate,
    Use,
    Mod(Mod),
    /// An `extern` block.
    ForeignMod(ForeignMod),

    // Type-level parameters
    /// Type parameter: the `T` in `struct Vec<T> { ... }`
    TyParam,
    /// Constant generic parameter: `struct Foo<const N: usize> { ... }`
    ConstParam,
    /// Lifetime parameter: the `'a` in `struct Foo<'a> { ... }`
    LifetimeParam,

    // ADT parts
    /// Refers to the variant definition, [`DefKind::Ctor`] refers to its constructor if it exists.
    Variant,
    /// The constructor function of a tuple/unit struct or tuple/unit enum variant.
    Ctor(Ctor<'tcx>),
    /// A field in a struct, enum or union. e.g.
    /// - `bar` in `struct Foo { bar: u8 }`
    /// - `Foo::Bar::0` in `enum Foo { Bar(u8) }`
    Field,

    // Others
    /// Macros
    Macro,
    /// A use of `global_asm!`.
    GlobalAsm,
    /// A synthetic coroutine body created by the lowering of a coroutine-closure, such as an async
    /// closure.
    SyntheticCoroutineBody,
    TestBinderConstraints,
}

/// ADts (`Struct`, `Enum` and `Union` map to this).
#[derive(Debug, Clone)]
pub struct Adt<'tcx> {
    def_id: DefId,
    /// The (instantiated) type of this adt.
    self_ty: ty::Ty<'tcx>,
    param_env: ParamEnv,
    adt_kind: AdtKind,
    variants: IndexVec<VariantIdx, VariantDef>,
    repr: ReprOptions,
    /// Info required to construct a virtual `Drop` impl for this adt.
    /// Computed on demand, see [`Adt::destruct_impl`].
    destruct_impl: OnceCell<Box<VirtualTraitImpl<'tcx>>>,
}

impl<'tcx> Adt<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn adt_kind(&self) -> AdtKind {
        self.adt_kind
    }
    pub fn variants(&self) -> &IndexVec<VariantIdx, VariantDef> {
        &self.variants
    }
    pub fn repr(&self) -> &ReprOptions {
        &self.repr
    }
    /// Info required to construct a virtual `Drop` impl for this adt.
    pub fn destruct_impl(&self, s: &impl BaseState<'tcx>) -> &VirtualTraitImpl<'tcx> {
        self.destruct_impl.get_or_init(|| {
            let s = &s.with_hax_owner(&self.def_id);
            let tcx = s.base().tcx;
            let destruct_trait = tcx.lang_items().destruct_trait().unwrap();
            virtual_impl_for(s, ty::TraitRef::new(tcx, destruct_trait, [self.self_ty]))
        })
    }
}

/// Type alias: `type Foo = Bar;`
#[derive(Debug, Clone)]
pub struct TyAlias {
    param_env: ParamEnv,
    ty: Ty,
}

impl TyAlias {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn ty(&self) -> &Ty {
        &self.ty
    }
}

/// Associated type: `trait MyTrait { type Assoc; }`
#[derive(Debug, Clone)]
pub struct AssocTy<'tcx> {
    def_id: DefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
    param_env: ParamEnv,
    implied_predicates: GenericPredicates,
    associated_item: AssocItem,
}

impl<'tcx> AssocTy<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn implied_predicates(&self) -> &GenericPredicates {
        &self.implied_predicates
    }
    pub fn associated_item(&self) -> &AssocItem {
        &self.associated_item
    }
    /// The value for this associated type, along with proofs of the required predicates. If
    /// we're in a trait decl, this has a value iff the type has a default; if we're in a trait
    /// impl, this has a value iff the impl provides its own value for it.
    pub fn value(&self, s: &impl BaseState<'tcx>) -> Option<(Ty, Vec<TraitProof>)> {
        let s = &s.with_hax_owner(&self.def_id);
        let tcx = s.base().tcx;
        let def_id = self.def_id.real_rust_def_id();
        if tcx.defaultness(def_id).has_value() {
            let ty = inst_binder(tcx, s.typing_env(), self.args, self.def_id.type_of(s));
            let args = self.args.unwrap_or_else(|| self.def_id.identity_args(s));
            let trait_proofs = solve_item_implied_traits(s, def_id, args);
            Some((ty.sinto(s), trait_proofs))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct Trait<'tcx> {
    def_id: DefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
    param_env: ParamEnv,
    implied_predicates: GenericPredicates,
    /// The special `Self: Trait` clause.
    self_predicate: TraitPredicate,
    /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for this trait. This is `Some` iff this
    /// trait is dyn-compatible.
    dyn_self: Option<Ty>,
    /// Computed on demand, see [`Trait::implied_trait_proofs`].
    implied_trait_proofs: OnceCell<Vec<TraitProof>>,
    /// Computed on demand, see [`Trait::items`].
    items: OnceCell<Vec<AssocItem>>,
}

impl<'tcx> Trait<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn implied_predicates(&self) -> &GenericPredicates {
        &self.implied_predicates
    }
    /// Proofs of the implied predicates. Most often uses the `Self` clause, except for builtin
    /// traits like `Sized`.
    pub fn implied_trait_proofs(&self, s: &impl BaseState<'tcx>) -> &[TraitProof] {
        self.implied_trait_proofs.get_or_init(|| {
            let s = &s.with_hax_owner(&self.def_id);
            let args = self.args.unwrap_or_else(|| self.def_id.identity_args(s));
            solve_item_implied_traits(s, self.def_id.real_rust_def_id(), args)
        })
    }
    /// The special `Self: Trait` clause.
    pub fn self_predicate(&self) -> &TraitPredicate {
        &self.self_predicate
    }
    /// Associated items, in definition order.
    pub fn items(&self, s: &impl BaseState<'tcx>) -> &[AssocItem] {
        self.items
            .get_or_init(|| assoc_items_of(&s.with_hax_owner(&self.def_id), self.args))
    }
    /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for this trait. This is `Some` iff this
    /// trait is dyn-compatible.
    pub fn dyn_self(&self) -> Option<&Ty> {
        self.dyn_self.as_ref()
    }
}

/// Trait alias: `trait IntIterator = Iterator<Item = i32>;`
#[derive(Debug, Clone)]
pub struct TraitAlias {
    param_env: ParamEnv,
    implied_predicates: GenericPredicates,
    /// The special `Self: Trait` clause.
    self_predicate: TraitPredicate,
    /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for this trait. This is `Some` iff this
    /// trait is dyn-compatible.
    dyn_self: Option<Ty>,
}

impl TraitAlias {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn implied_predicates(&self) -> &GenericPredicates {
        &self.implied_predicates
    }
    /// The special `Self: Trait` clause.
    pub fn self_predicate(&self) -> &TraitPredicate {
        &self.self_predicate
    }
    /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for this trait. This is `Some` iff this
    /// trait is dyn-compatible.
    pub fn dyn_self(&self) -> Option<&Ty> {
        self.dyn_self.as_ref()
    }
}

#[derive(Debug, Clone)]
pub struct TraitImpl<'tcx> {
    this: ItemRef,
    args: Option<ty::GenericArgsRef<'tcx>>,
    /// The implemented trait, instantiated with `args` if relevant.
    trait_ref: ty::TraitRef<'tcx>,
    param_env: ParamEnv,
    /// The trait that is implemented by this impl block.
    trait_pred: TraitPredicate,
    /// The trait proofs required to satisfy the predicates on the trait declaration. E.g.:
    /// ```ignore
    /// trait Foo: Bar {}
    /// impl Foo for () {} // would supply a proof for `Self: Bar`.
    /// ```
    implied_trait_proofs: Vec<TraitProof>,
    /// Computed on demand, see [`TraitImpl::items`].
    items: OnceCell<Vec<ImplAssocItem>>,
}

impl<'tcx> TraitImpl<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    /// The trait that is implemented by this impl block.
    pub fn trait_pred(&self) -> &TraitPredicate {
        &self.trait_pred
    }
    /// `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` for the implemented trait. This is
    /// `Some` iff the trait is dyn-compatible.
    pub fn dyn_self(&self, s: &impl BaseState<'tcx>) -> Option<Ty> {
        let s = &s.with_hax_owner(&self.this.def_id);
        dyn_self_ty(s.base().tcx, s.typing_env(), self.trait_ref).sinto(s)
    }
    /// The trait proofs required to satisfy the predicates on the trait declaration. E.g.:
    /// ```ignore
    /// trait Foo: Bar {}
    /// impl Foo for () {} // would supply a proof for `Self: Bar`.
    /// ```
    pub fn implied_trait_proofs(&self) -> &[TraitProof] {
        &self.implied_trait_proofs
    }
    /// Associated items, in the order of the trait declaration. Includes defaulted items.
    pub fn items(&self, s: &impl BaseState<'tcx>) -> &[ImplAssocItem] {
        self.items.get_or_init(|| self.compute_items(s))
    }

    fn compute_items(&self, s: &impl BaseState<'tcx>) -> Vec<ImplAssocItem> {
        use std::collections::HashMap;
        let this = &self.this;
        let s = &s.with_hax_owner(&this.def_id);
        let tcx = s.base().tcx;
        let def_id = this.def_id.real_rust_def_id();
        let trait_ref = self.trait_ref;
        let args = self.args.unwrap_or_else(|| this.def_id.identity_args(s));

        let mut item_map: HashMap<RDefId, _> = tcx
            .associated_items(def_id)
            .in_definition_order()
            .map(|assoc| (assoc.trait_item_def_id().unwrap(), assoc))
            .collect();
        let items = tcx
            .associated_items(trait_ref.def_id)
            .in_definition_order()
            .map(|decl_assoc| {
                let decl_def_id = decl_assoc.def_id;
                let trait_impl_id = def_id;
                let value = item_map.remove(&decl_def_id).map(|impl_assoc| {
                    let impl_assoc_def_id: DefId = impl_assoc.def_id.sinto(s);
                    let virtual_item =
                        VirtualImplAssocItem::new(trait_impl_id, decl_def_id, impl_assoc.def_id);
                    let virtual_item_def_id = DefId::make_assoc_item_impl(s, virtual_item);
                    let s = &s.with_hax_owner(&virtual_item_def_id);
                    let item_decl_args = virtual_item.args_for_item_decl(s, trait_ref.args);
                    let item_impl_args = virtual_item.args_for_item_impl(s, args);
                    let assoc_ty_value = matches!(decl_assoc.kind, ty::AssocKind::Type { .. })
                        .then(|| {
                            inst_binder(
                                tcx,
                                s.typing_env(),
                                Some(item_impl_args),
                                impl_assoc_def_id.type_of(s),
                            )
                            .sinto(s)
                        });
                    let required_trait_proofs =
                        solve_item_implied_traits(s, decl_def_id, item_decl_args);
                    let param_env = {
                        // Pass `None` to get the generics, but add the known parent.
                        // FIXME: maybe a custom enum instead of `Option<Args>`.
                        let mut param_env = get_param_env(s, None);
                        param_env.generics.parent = Some(this.def_id.clone());
                        param_env.parent = Some(this.clone());
                        param_env
                    };
                    let item = ItemRef::translate(s, impl_assoc.def_id, item_impl_args);
                    let late_bound = late_bound_for_def(s, impl_assoc.def_id, Some(item_impl_args));
                    let value = ImplAssocItemValue {
                        item,
                        assoc_ty_value,
                        implied_trait_proofs: required_trait_proofs,
                    };
                    TraitItemBinder {
                        def_id: virtual_item_def_id,
                        param_env,
                        late_bound,
                        skip_binder: value,
                    }
                });

                ImplAssocItem {
                    name: decl_assoc.opt_name().sinto(s),
                    value,
                    decl_def_id: decl_def_id.sinto(s),
                }
            })
            .collect();
        assert!(item_map.is_empty());
        items
    }
}

#[derive(Debug, Clone)]
pub struct InherentImpl<'tcx> {
    def_id: DefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
    param_env: ParamEnv,
    /// The type to which this block applies.
    ty: Ty,
    /// Computed on demand, see [`InherentImpl::items`].
    items: OnceCell<Vec<AssocItem>>,
}

impl<'tcx> InherentImpl<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    /// The type to which this block applies.
    pub fn ty(&self) -> &Ty {
        &self.ty
    }
    /// Associated items, in definition order.
    pub fn items(&self, s: &impl BaseState<'tcx>) -> &[AssocItem] {
        self.items
            .get_or_init(|| assoc_items_of(&s.with_hax_owner(&self.def_id), self.args))
    }
}

/// The associated items of the trait or inherent impl that owns `s`, in definition order.
fn assoc_items_of<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> Vec<AssocItem> {
    let tcx = s.base().tcx;
    let def_id = s.owner().real_rust_def_id();
    tcx.associated_items(def_id)
        .in_definition_order()
        .map(|assoc| {
            let item_args = args.map(|args| {
                let item_def_id: DefId = assoc.def_id.sinto(s);
                let item_identity_args = item_def_id.identity_args(s);
                let item_args = item_identity_args.rebase_onto(tcx, def_id, args);
                tcx.mk_args(item_args)
            });
            AssocItem::sfrom_instantiated(s, assoc, item_args)
        })
        .collect()
}

/// The virtual `Fn*` impls of a function item or constructor, which exist iff the function is
/// `Fn*`-compatible.
#[derive(Debug, Clone)]
pub struct FnTraitImpls<'tcx> {
    /// The arguments of this function, tupled as the `Fn*` traits take them, e.g. `(A, B, C)`.
    /// Binds the same variables as the function's `sig`.
    pub tupled_args_ty: Binder<Ty>,
    /// Info required to construct a virtual `FnOnce` impl for this function.
    pub fn_once_impl: Box<VirtualTraitImpl<'tcx>>,
    /// Info required to construct a virtual `FnMut` impl for this function.
    pub fn_mut_impl: Box<VirtualTraitImpl<'tcx>>,
    /// Info required to construct a virtual `Fn` impl for this function.
    pub fn_impl: Box<VirtualTraitImpl<'tcx>>,
}

/// Compute the `Fn*` impls of a callable type, given its (instantiated) signature.
fn callable_trait_impls<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    self_ty: ty::Ty<'tcx>,
    fn_sig: ty::PolyFnSig<'tcx>,
    late_bound_scope: RDefId,
) -> Option<FnTraitImpls<'tcx>> {
    let tcx = s.base().tcx;
    if !fn_sig.is_fn_trait_compatible() {
        return None;
    }
    let liberated_sig = tcx.liberate_late_bound_regions(late_bound_scope, fn_sig);
    let input_ty = ty::Ty::new_tup(tcx, liberated_sig.inputs());
    let trait_args = [self_ty, input_ty];

    let fn_once_trait = tcx.lang_items().fn_once_trait().unwrap();
    let fn_mut_trait = tcx.lang_items().fn_mut_trait().unwrap();
    let fn_trait = tcx.lang_items().fn_trait().unwrap();

    let fn_once_tref = ty::TraitRef::new(tcx, fn_once_trait, trait_args);
    let fn_mut_tref = ty::TraitRef::new(tcx, fn_mut_trait, trait_args);
    let fn_tref = ty::TraitRef::new(tcx, fn_trait, trait_args);
    Some(FnTraitImpls {
        tupled_args_ty: tupled_args_ty(s, fn_sig).sinto(s),
        fn_once_impl: virtual_impl_for(s, fn_once_tref),
        fn_mut_impl: virtual_impl_for(s, fn_mut_tref),
        fn_impl: virtual_impl_for(s, fn_tref),
    })
}

/// Compute the `Fn*` impls of the function item owned by `s`, given its (instantiated) signature.
fn fn_def_trait_impls<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
    fn_sig: ty::PolyFnSig<'tcx>,
) -> Option<FnTraitImpls<'tcx>> {
    let tcx = s.base().tcx;
    let def_id = s.owner().real_rust_def_id();
    if !tcx.codegen_fn_attrs(def_id).target_features.is_empty() {
        return None;
    }
    let fn_args = args.unwrap_or_else(|| s.owner().identity_args(s));
    let self_ty = ty::Ty::new_fn_def(tcx, def_id, fn_sig.rebind(fn_args));
    callable_trait_impls(s, self_ty, fn_sig, def_id)
}

#[derive(Debug, Clone)]
pub struct Fn<'tcx> {
    def_id: DefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
    /// The signature, instantiated with `args` if relevant.
    rustc_sig: ty::PolyFnSig<'tcx>,
    param_env: ParamEnv,
    inline: InlineAttr,
    sig: PolyFnSig,
    /// Computed on demand, see [`Fn::fn_trait_impls`].
    fn_trait_impls: OnceCell<Option<FnTraitImpls<'tcx>>>,
}

impl<'tcx> Fn<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn inline(&self) -> &InlineAttr {
        &self.inline
    }
    pub fn sig(&self) -> &PolyFnSig {
        &self.sig
    }
    /// The virtual `Fn*` impls for this function, if it is `Fn*`-compatible.
    pub fn fn_trait_impls(&self, s: &impl BaseState<'tcx>) -> Option<&FnTraitImpls<'tcx>> {
        self.fn_trait_impls
            .get_or_init(|| {
                fn_def_trait_impls(&s.with_hax_owner(&self.def_id), self.args, self.rustc_sig)
            })
            .as_ref()
    }
}

/// Associated function: `impl MyStruct { fn associated() {} }` or `trait Foo { fn associated()
/// {} }`
#[derive(Debug, Clone)]
pub struct AssocFn<'tcx> {
    def_id: DefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
    /// The signature, instantiated with `args` if relevant.
    rustc_sig: ty::PolyFnSig<'tcx>,
    param_env: ParamEnv,
    associated_item: AssocItem,
    inline: InlineAttr,
    sig: PolyFnSig,
    /// Computed on demand, see [`AssocFn::fn_trait_impls`].
    fn_trait_impls: OnceCell<Option<FnTraitImpls<'tcx>>>,
}

impl<'tcx> AssocFn<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn associated_item(&self) -> &AssocItem {
        &self.associated_item
    }
    pub fn inline(&self) -> &InlineAttr {
        &self.inline
    }
    /// The function signature when this method is used in a vtable. `None` if this method is not
    /// vtable safe. `Some(sig)` if it is vtable safe, where `sig` is the trait method declaration's
    /// signature with `Self` replaced by `dyn Trait` and associated types normalized.
    pub fn vtable_sig(&self, s: &impl BaseState<'tcx>) -> Option<PolyFnSig> {
        gen_vtable_sig(&s.with_hax_owner(&self.def_id), self.args)
    }
    pub fn sig(&self) -> &PolyFnSig {
        &self.sig
    }
    /// The virtual `Fn*` impls for this function, if it is `Fn*`-compatible.
    pub fn fn_trait_impls(&self, s: &impl BaseState<'tcx>) -> Option<&FnTraitImpls<'tcx>> {
        self.fn_trait_impls
            .get_or_init(|| {
                fn_def_trait_impls(&s.with_hax_owner(&self.def_id), self.args, self.rustc_sig)
            })
            .as_ref()
    }
}

#[derive(Debug, Clone)]
pub struct FnPointer<'tcx> {
    def_id: DefId,
    self_ty: ty::Ty<'tcx>,
    rustc_sig: ty::PolyFnSig<'tcx>,
    param_env: ParamEnv,
    sig: PolyFnSig,
    late_bound_scope: RDefId,
    fn_trait_impls: OnceCell<Option<FnTraitImpls<'tcx>>>,
}

impl<'tcx> FnPointer<'tcx> {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }

    pub fn sig(&self) -> &PolyFnSig {
        &self.sig
    }

    /// DefId we use for `liberate_bound_regions`. We stole some `DefId` from somewhere to serve as
    /// placeholder here, as this needs to be a real rustc `DefId`. It only matters for matching up
    /// generics during translation.
    pub fn late_bound_scope(&self) -> RDefId {
        self.late_bound_scope
    }

    pub fn fn_trait_impls(&self, s: &impl BaseState<'tcx>) -> Option<&FnTraitImpls<'tcx>> {
        self.fn_trait_impls
            .get_or_init(|| {
                callable_trait_impls(
                    &s.with_hax_owner(&self.def_id),
                    self.self_ty,
                    self.rustc_sig,
                    self.late_bound_scope,
                )
            })
            .as_ref()
    }
}

/// A closure, coroutine, or coroutine-closure.
#[derive(Debug, Clone)]
pub struct Closure<'tcx> {
    def_id: DefId,
    /// `[closure_ty, tupled_args_ty]`: the args of the `Fn*` traits for this closure.
    fn_trait_args: [ty::Ty<'tcx>; 2],
    kind: ty::ClosureKind,
    /// This param env is empty because the (early-bound) generics of a closure are the same as
    /// those of the item in which it is defined. We hide the special weird generics that rustc
    /// uses internally for inference on closures.
    param_env: ParamEnv,
    args: ClosureArgs,
    inline: InlineAttr,
    /// Computed on demand, see the accessors below.
    fn_once_impl: OnceCell<Box<VirtualTraitImpl<'tcx>>>,
    fn_mut_impl: OnceCell<Option<Box<VirtualTraitImpl<'tcx>>>>,
    fn_impl: OnceCell<Option<Box<VirtualTraitImpl<'tcx>>>>,
    destruct_impl: OnceCell<Box<VirtualTraitImpl<'tcx>>>,
}

impl<'tcx> Closure<'tcx> {
    /// This param env is empty because the (early-bound) generics of a closure are the same as
    /// those of the item in which it is defined. We hide the special weird generics that rustc
    /// uses internally for inference on closures.
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn args(&self) -> &ClosureArgs {
        &self.args
    }
    pub fn inline(&self) -> &InlineAttr {
        &self.inline
    }
    /// The virtual impl of this closure for the given trait.
    fn virtual_impl(
        &self,
        s: &impl BaseState<'tcx>,
        trait_lang_item: LangItem,
        trait_args: &[ty::Ty<'tcx>],
    ) -> Box<VirtualTraitImpl<'tcx>> {
        let s = &s.with_hax_owner(&self.def_id);
        let tcx = s.base().tcx;
        let def_id = tcx.lang_items().get(trait_lang_item).unwrap();
        let tref = ty::TraitRef::new(tcx, def_id, trait_args.iter().copied());
        virtual_impl_for(s, tref)
    }
    /// Info required to construct a virtual `FnOnce` impl for this closure.
    pub fn fn_once_impl(&self, s: &impl BaseState<'tcx>) -> &VirtualTraitImpl<'tcx> {
        self.fn_once_impl
            .get_or_init(|| self.virtual_impl(s, LangItem::FnOnce, &self.fn_trait_args))
    }
    /// Info required to construct a virtual `FnMut` impl for this closure.
    pub fn fn_mut_impl(&self, s: &impl BaseState<'tcx>) -> Option<&VirtualTraitImpl<'tcx>> {
        self.fn_mut_impl
            .get_or_init(|| {
                matches!(self.kind, ty::ClosureKind::FnMut | ty::ClosureKind::Fn)
                    .then(|| self.virtual_impl(s, LangItem::FnMut, &self.fn_trait_args))
            })
            .as_deref()
    }
    /// Info required to construct a virtual `Fn` impl for this closure.
    pub fn fn_impl(&self, s: &impl BaseState<'tcx>) -> Option<&VirtualTraitImpl<'tcx>> {
        self.fn_impl
            .get_or_init(|| {
                matches!(self.kind, ty::ClosureKind::Fn)
                    .then(|| self.virtual_impl(s, LangItem::Fn, &self.fn_trait_args))
            })
            .as_deref()
    }
    /// Info required to construct a virtual `Drop` impl for this closure.
    pub fn destruct_impl(&self, s: &impl BaseState<'tcx>) -> &VirtualTraitImpl<'tcx> {
        self.destruct_impl
            .get_or_init(|| self.virtual_impl(s, LangItem::Destruct, &self.fn_trait_args[..1]))
    }
}

#[derive(Debug, Clone)]
pub struct Const {
    param_env: ParamEnv,
    ty: Ty,
    kind: ConstKind,
}

impl Const {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn ty(&self) -> &Ty {
        &self.ty
    }
    pub fn kind(&self) -> &ConstKind {
        &self.kind
    }
}

/// Associated constant: `trait MyTrait { const ASSOC: usize; }`
#[derive(Debug, Clone)]
pub struct AssocConst {
    param_env: ParamEnv,
    associated_item: AssocItem,
    ty: Ty,
}

impl AssocConst {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    pub fn associated_item(&self) -> &AssocItem {
        &self.associated_item
    }
    pub fn ty(&self) -> &Ty {
        &self.ty
    }
}

#[derive(Debug, Clone)]
pub struct Static {
    param_env: ParamEnv,
    /// Whether it's a `unsafe static`, `safe static` (inside extern only) or just a `static`.
    safety: Safety,
    /// Whether it's a `static mut` or just a `static`.
    mutability: Mutability,
    /// Whether it's a `#[thread_local] static`.
    thread_local: bool,
    ty: Ty,
}

impl Static {
    pub fn param_env(&self) -> &ParamEnv {
        &self.param_env
    }
    /// Whether it's a `unsafe static`, `safe static` (inside extern only) or just a `static`.
    pub fn safety(&self) -> Safety {
        self.safety
    }
    /// Whether it's a `static mut` or just a `static`.
    pub fn mutability(&self) -> Mutability {
        self.mutability
    }
    /// Whether it's a `#[thread_local] static`.
    pub fn thread_local(&self) -> bool {
        self.thread_local
    }
    pub fn ty(&self) -> &Ty {
        &self.ty
    }
}

#[derive(Debug, Clone)]
pub struct Mod {
    def_id: DefId,
    /// Computed on demand, see [`Mod::items`].
    items: OnceCell<Vec<(Option<Ident>, DefId)>>,
}

impl Mod {
    pub fn items<'tcx>(&self, s: &impl BaseState<'tcx>) -> &[(Option<Ident>, DefId)] {
        self.items
            .get_or_init(|| get_mod_children(s.base().tcx, self.def_id.real_rust_def_id()).sinto(s))
    }
}

/// An `extern` block.
#[derive(Debug, Clone)]
pub struct ForeignMod {
    items: Vec<DefId>,
}

impl ForeignMod {
    pub fn items(&self) -> &[DefId] {
        &self.items
    }
}

/// The constructor function of a tuple/unit struct or tuple/unit enum variant.
#[derive(Debug, Clone)]
pub struct Ctor<'tcx> {
    def_id: DefId,
    args: ty::GenericArgsRef<'tcx>,
    /// The signature, instantiated with `args`.
    rustc_sig: ty::PolyFnSig<'tcx>,
    adt_def_id: DefId,
    ctor_of: CtorOf,
    variant_id: VariantIdx,
    fields: IndexVec<FieldIdx, FieldDef>,
    output_ty: Ty,
    sig: PolyFnSig,
    /// Computed on demand, see [`Ctor::fn_trait_impls`].
    fn_trait_impls: OnceCell<Option<FnTraitImpls<'tcx>>>,
}

impl<'tcx> Ctor<'tcx> {
    pub fn adt_def_id(&self) -> &DefId {
        &self.adt_def_id
    }
    pub fn ctor_of(&self) -> CtorOf {
        self.ctor_of
    }
    pub fn variant_id(&self) -> VariantIdx {
        self.variant_id
    }
    pub fn fields(&self) -> &IndexVec<FieldIdx, FieldDef> {
        &self.fields
    }
    pub fn output_ty(&self) -> &Ty {
        &self.output_ty
    }
    pub fn sig(&self) -> &PolyFnSig {
        &self.sig
    }
    /// The virtual `Fn*` impls for this constructor.
    pub fn fn_trait_impls(&self, s: &impl BaseState<'tcx>) -> Option<&FnTraitImpls<'tcx>> {
        self.fn_trait_impls
            .get_or_init(|| {
                fn_def_trait_impls(
                    &s.with_hax_owner(&self.def_id),
                    Some(self.args),
                    self.rustc_sig,
                )
            })
            .as_ref()
    }
}

/// Whether the trait method declared by `method_decl_id` takes `self: Self` by value.
pub fn vtable_receiver_is_by_value<'tcx>(tcx: ty::TyCtxt<'tcx>, method_decl_id: RDefId) -> bool {
    let decl_sig = tcx
        .fn_sig(method_decl_id)
        .instantiate_identity()
        .skip_norm_wip();
    !decl_sig.inputs().skip_binder().is_empty()
        && decl_sig.input(0).skip_binder().is_param(0)
        && tcx.generics_of(method_decl_id).has_self
}

/// If the method takes `self: Self` by value, make the vtable signature take the receiver via
/// `*mut Self` instead, like rustc's vtable shims do.
fn adjust_by_value_vtable_receiver<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    method_decl_id: RDefId,
    sig: ty::PolyFnSig<'tcx>,
) -> ty::PolyFnSig<'tcx> {
    if !vtable_receiver_is_by_value(tcx, method_decl_id) {
        return sig;
    }
    sig.map_bound(|mut sig| {
        let mut inputs_and_output = sig.inputs_and_output.to_vec();
        inputs_and_output[0] = ty::Ty::new_mut_ptr(tcx, inputs_and_output[0]);
        sig.inputs_and_output = tcx.mk_type_list(&inputs_and_output);
        sig
    })
}

fn gen_vtable_sig<'tcx>(
    // The state that owns the method DefId
    s: &impl UnderOwnerState<'tcx>,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> Option<PolyFnSig> {
    let method_def_id = s.owner().as_real_def_id().unwrap();
    let tcx = s.base().tcx;
    let assoc_item = tcx.associated_item(method_def_id);
    let container_id = assoc_item.container_id(tcx);

    // Get the original trait method id.
    let method_decl_id = match assoc_item.container {
        ty::AssocContainer::TraitImpl(Ok(id)) => id,
        ty::AssocContainer::Trait => method_def_id,
        _ => return None,
    };
    let trait_id = tcx.trait_of_assoc(method_decl_id)?;

    let decl_assoc_item = tcx.associated_item(method_decl_id);
    if !rustc_trait_selection::traits::is_vtable_safe_method(tcx, trait_id, decl_assoc_item) {
        return None;
    }

    // Move into the context of the container (trait decl or impl) instead of the method.
    let s = &s.with_rustc_owner(container_id);
    let args = {
        let container_generics = s.owner().generics_of(s);
        args.map(|args| args.truncate_to(tcx, container_generics))
    };

    let dyn_self = match assoc_item.container {
        ty::AssocContainer::Trait => get_trait_decl_dyn_self_ty(s, args),
        ty::AssocContainer::TraitImpl(..) => {
            // For impl methods, compute concrete dyn_self from the impl's trait reference
            let impl_def_id = assoc_item.container_id(tcx);
            let impl_trait_ref = tcx.impl_trait_ref(impl_def_id);
            // Get the concrete trait reference by rebasing the impl's trait ref args onto `container_args`
            let concrete_trait_ref = inst_binder(tcx, s.typing_env(), args, impl_trait_ref);
            dyn_self_ty(tcx, s.typing_env(), concrete_trait_ref)
        }
        ty::AssocContainer::InherentImpl => {
            unreachable!()
        }
    }?;

    Some(vtable_sig_with_dyn_self(s, method_decl_id, dyn_self))
}

/// The signature of `method_decl_id` as stored in a vtable, i.e. with its `Self` type replaced by
/// the given `dyn Trait<..>` type.
fn vtable_sig_with_dyn_self<'tcx>(
    s: &impl UnderOwnerState<'tcx>,
    method_decl_id: RDefId,
    dyn_self: ty::Ty<'tcx>,
) -> PolyFnSig {
    let tcx = s.base().tcx;
    // dyn_self is of form `dyn Trait<Args...>`, we extract the trait args
    let ty::Dynamic(preds, _) = dyn_self.kind() else {
        panic!("Unexpected dyn_self: {:?}", dyn_self);
    };
    // Safe to use `skip_binder` because we know the predicate we built in dyn_self_ty has no bound
    // vars.
    let ty::ExistentialPredicate::Trait(trait_ref) = preds[0].skip_binder() else {
        panic!("No principal trait found in dyn_self: {:?}", dyn_self);
    };

    // Build a full list of args for the trait: dyn_self + trait args
    // Note: trait_ref.args doesn't include Self (it's existential), so we prepend dyn_self
    let mut full_args = vec![ty::GenericArg::from(dyn_self)];
    full_args.extend(trait_ref.args.iter());
    let trait_args = tcx.mk_args(&full_args);

    // Instantiate and normalize the signature.
    let method_decl_sig = tcx.fn_sig(method_decl_id).instantiate(tcx, trait_args);
    let normalized_sig = normalize(tcx, s.typing_env(), method_decl_sig);
    let normalized_sig = adjust_by_value_vtable_receiver(tcx, method_decl_id, normalized_sig);

    normalized_sig.sinto(s)
}

/// Construct the `FullDefKind` for this item.
///
/// If `args` is `Some`, instantiate the whole definition with these generics; otherwise keep the
/// polymorphic definition.
// Note: this is tricky to get right, we have to make sure to isntantiate every single field that
// may contain a type/const/trait reference.
fn translate_full_def_kind<'tcx, S>(
    s: &S,
    this: &ItemRef,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> FullDefKind<'tcx>
where
    S: BaseState<'tcx>,
{
    let hax_def_id = &this.def_id;
    let s = &s.with_hax_owner(hax_def_id);
    let def_id = hax_def_id.real_rust_def_id();
    let tcx = s.base().tcx;
    let type_of_self = || inst_binder(tcx, s.typing_env(), args, hax_def_id.type_of(s));
    let args_or_default = || args.unwrap_or_else(|| hax_def_id.identity_args(s));
    match get_def_kind(tcx, def_id) {
        RDefKind::Struct { .. } | RDefKind::Union { .. } | RDefKind::Enum { .. } => {
            let def = tcx.adt_def(def_id);
            let variants = def
                .variants()
                .iter_enumerated()
                .map(|(variant_idx, variant)| {
                    let discr = if def.is_enum() {
                        def.discriminant_for_variant(tcx, variant_idx)
                    } else {
                        // Structs and unions have a single variant.
                        assert_eq!(variant_idx.index(), 0);
                        ty::util::Discr {
                            val: 0,
                            ty: tcx.types.isize,
                        }
                    };
                    VariantDef::sfrom(s, variant, discr, args)
                })
                .collect();

            FullDefKind::Adt(Adt {
                def_id: hax_def_id.clone(),
                self_ty: type_of_self(),
                param_env: get_param_env(s, args),
                adt_kind: def.adt_kind().sinto(s),
                variants,
                repr: def.repr().sinto(s),
                destruct_impl: Default::default(),
            })
        }
        RDefKind::TyAlias { .. } => FullDefKind::TyAlias(TyAlias {
            param_env: get_param_env(s, args),
            ty: type_of_self().sinto(s),
        }),
        RDefKind::ForeignTy => FullDefKind::ForeignTy,
        RDefKind::AssocTy { .. } => FullDefKind::AssocTy(AssocTy {
            def_id: hax_def_id.clone(),
            args,
            param_env: get_param_env(s, args),
            implied_predicates: get_implied_predicates(s, args),
            associated_item: AssocItem::sfrom_instantiated(s, &tcx.associated_item(def_id), args),
        }),
        RDefKind::OpaqueTy => FullDefKind::OpaqueTy,
        RDefKind::Trait { .. } => FullDefKind::Trait(Trait {
            def_id: hax_def_id.clone(),
            args,
            param_env: get_param_env(s, args),
            implied_predicates: get_implied_predicates(s, args),
            self_predicate: get_self_predicate(s, args),
            dyn_self: get_trait_decl_dyn_self_ty(s, args).sinto(s),
            implied_trait_proofs: OnceCell::new(),
            items: OnceCell::new(),
        }),
        RDefKind::TraitAlias { .. } => FullDefKind::TraitAlias(TraitAlias {
            param_env: get_param_env(s, args),
            implied_predicates: get_implied_predicates(s, args),
            self_predicate: get_self_predicate(s, args),
            dyn_self: get_trait_decl_dyn_self_ty(s, args).sinto(s),
        }),
        RDefKind::Impl { of_trait, .. } => {
            let param_env = get_param_env(s, args);
            if !of_trait {
                FullDefKind::InherentImpl(InherentImpl {
                    def_id: hax_def_id.clone(),
                    args,
                    param_env,
                    ty: type_of_self().sinto(s),
                    items: OnceCell::new(),
                })
            } else {
                let trait_ref = tcx.impl_trait_ref(def_id);
                let trait_ref = inst_binder(tcx, s.typing_env(), args, trait_ref);
                let polarity = tcx.impl_polarity(def_id);
                let trait_pred = TraitPredicate {
                    trait_ref: trait_ref.sinto(s),
                    is_positive: matches!(polarity, ty::ImplPolarity::Positive),
                };
                // Trait proofs required by the trait.
                let required_trait_proofs =
                    solve_item_implied_traits(s, trait_ref.def_id, trait_ref.args);
                FullDefKind::TraitImpl(TraitImpl {
                    this: this.clone(),
                    args,
                    trait_ref,
                    param_env,
                    trait_pred,
                    implied_trait_proofs: required_trait_proofs,
                    items: OnceCell::new(),
                })
            }
        }
        RDefKind::Fn { .. } => {
            let sig = tcx.fn_sig(def_id);
            let sig = inst_binder(tcx, s.typing_env(), args, sig);
            FullDefKind::Fn(Fn {
                def_id: hax_def_id.clone(),
                args,
                rustc_sig: sig,
                param_env: get_param_env(s, args),
                inline: tcx.codegen_fn_attrs(def_id).inline.sinto(s),
                sig: sig.sinto(s),
                fn_trait_impls: OnceCell::new(),
            })
        }
        RDefKind::AssocFn { .. } => {
            let item = tcx.associated_item(def_id);
            let sig = get_method_sig(tcx, s.typing_env(), def_id, args);
            FullDefKind::AssocFn(AssocFn {
                def_id: hax_def_id.clone(),
                args,
                rustc_sig: sig,
                param_env: get_param_env(s, args),
                associated_item: AssocItem::sfrom_instantiated(s, &item, args),
                inline: tcx.codegen_fn_attrs(def_id).inline.sinto(s),
                sig: sig.sinto(s),
                fn_trait_impls: OnceCell::new(),
            })
        }
        RDefKind::Closure { .. } => {
            let closure_ty = type_of_self();
            let ty::TyKind::Closure(_, closure_args) = closure_ty.kind() else {
                unreachable!()
            };
            let closure = closure_args.as_closure();
            let input_ty = tupled_args_ty(s, closure_sig(tcx, closure));
            let input_ty = tcx.liberate_late_bound_regions(def_id, input_ty);
            FullDefKind::Closure(Closure {
                def_id: hax_def_id.clone(),
                fn_trait_args: [closure_ty, input_ty],
                kind: closure.kind(),
                param_env: get_param_env(s, args),
                inline: tcx.codegen_fn_attrs(def_id).inline.sinto(s),
                args: ClosureArgs::sfrom(s, def_id, closure_args),
                fn_once_impl: Default::default(),
                fn_mut_impl: Default::default(),
                fn_impl: Default::default(),
                destruct_impl: Default::default(),
            })
        }
        kind @ (RDefKind::Const | RDefKind::AnonConst { .. }) => {
            let kind = match kind {
                RDefKind::Const => ConstKind::TopLevel,
                RDefKind::AnonConst { .. } => ConstKind::AnonConst,
                _ => unreachable!(),
            };

            let self_ty = if matches!(kind, ConstKind::AnonConst)
                && tcx.anon_const_kind(def_id) == ty::AnonConstKind::NonTypeSystemInline
                && let get_ret_ty = (|body: &mir::Body<'tcx>| body.local_decls[mir::Local::ZERO].ty)
                && let Some(ret_ty) = mir_kinds::CTFE::get_mir(tcx, def_id, get_ret_ty)
                    .or_else(|| mir_kinds::Optimized::get_mir(tcx, def_id, get_ret_ty))
            {
                // Inline consts have a special `<const_ty>` param added to them for type inference
                // purposes. `tcx.type_of` returns that, which is not useful to us. Instead, we get
                // the real type from the MIR body which is sad but works.
                inst_binder(
                    tcx,
                    s.typing_env(),
                    args,
                    ty::EarlyBinder::bind(tcx, ret_ty),
                )
            } else {
                type_of_self()
            };
            FullDefKind::Const(Const {
                param_env: get_param_env(s, args),
                ty: self_ty.sinto(s),
                kind,
            })
        }
        RDefKind::AssocConst => FullDefKind::AssocConst(AssocConst {
            param_env: get_param_env(s, args),
            associated_item: AssocItem::sfrom_instantiated(s, &tcx.associated_item(def_id), args),
            ty: type_of_self().sinto(s),
        }),
        RDefKind::Static {
            safety, mutability, ..
        } => FullDefKind::Static(Static {
            param_env: get_param_env(s, args),
            safety: safety.sinto(s),
            mutability: mutability.sinto(s),
            thread_local: tcx.is_thread_local_static(def_id),
            ty: type_of_self().sinto(s),
        }),
        RDefKind::ExternCrate => FullDefKind::ExternCrate,
        RDefKind::Use => FullDefKind::Use,
        RDefKind::Mod { .. } => FullDefKind::Mod(Mod {
            def_id: hax_def_id.clone(),
            items: OnceCell::new(),
        }),
        RDefKind::ForeignMod { .. } => FullDefKind::ForeignMod(ForeignMod {
            items: get_foreign_mod_children(tcx, def_id).sinto(s),
        }),
        RDefKind::TyParam => FullDefKind::TyParam,
        RDefKind::ConstParam => FullDefKind::ConstParam,
        RDefKind::LifetimeParam => FullDefKind::LifetimeParam,
        RDefKind::Variant => FullDefKind::Variant,
        RDefKind::Ctor(ctor_of, _) => {
            let args = args_or_default();
            let ctor_of = ctor_of.sinto(s);
            let sig = tcx.fn_sig(def_id);

            // The def_id of the adt this ctor belongs to.
            let adt_def_id = match ctor_of {
                CtorOf::Struct => tcx.parent(def_id),
                CtorOf::Variant => tcx.parent(tcx.parent(def_id)),
            };
            let adt_def = tcx.adt_def(adt_def_id);
            let variant_id = adt_def.variant_index_with_ctor_id(def_id);
            let fields = adt_def
                .variant(variant_id)
                .fields
                .iter()
                .map(|f| FieldDef::sfrom(s, f, args))
                .collect();
            let output_ty = ty::Ty::new_adt(tcx, adt_def, args).sinto(s);
            let sig = inst_binder(tcx, s.typing_env(), Some(args), sig);
            FullDefKind::Ctor(Ctor {
                def_id: hax_def_id.clone(),
                args,
                rustc_sig: sig,
                adt_def_id: adt_def_id.sinto(s),
                ctor_of,
                variant_id: variant_id.sinto(s),
                fields,
                output_ty,
                sig: sig.sinto(s),
                fn_trait_impls: OnceCell::new(),
            })
        }
        RDefKind::Field => FullDefKind::Field,
        RDefKind::Macro(..) => FullDefKind::Macro,
        RDefKind::GlobalAsm => FullDefKind::GlobalAsm,
        RDefKind::SyntheticCoroutineBody => FullDefKind::SyntheticCoroutineBody,
        RDefKind::TestBinderConstraints => FullDefKind::TestBinderConstraints,
    }
}

fn late_bound_for_def<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    def_id: RDefId,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> Binder<()> {
    if matches!(
        s.base().tcx.def_kind(def_id),
        RDefKind::Fn { .. } | RDefKind::AssocFn { .. }
    ) {
        get_method_sig(s.base().tcx, s.typing_env(), def_id, args)
            .sinto(s)
            .map(|_| ())
    } else {
        Binder::empty()
    }
}

/// An associated item in a trait impl. This can be an item provided by the trait impl, or an item
/// that reuses the trait decl default value.
#[derive(Debug, Clone)]
pub struct ImplAssocItem {
    /// This is `None` for RPTITs.
    pub name: Option<Symbol>,
    /// The definition of the item from the trait declaration. This is an `AssocTy`, `AssocFn` or
    /// `AssocConst`.
    pub decl_def_id: DefId,
    /// The value of the implemented item, if any.
    pub value: Option<TraitItemBinder<ImplAssocItemValue>>,
}

/// The binding context to use when translating a trait impl associated item.
#[derive(Debug, Clone)]
pub struct TraitItemBinder<T> {
    pub def_id: DefId,
    /// Parameters bound by the item.
    pub param_env: ParamEnv,
    /// Late-bound parameters, if any.
    pub late_bound: Binder<()>,
    pub skip_binder: T,
}

/// The item is provided by the trait impl.
#[derive(Debug, Clone)]
pub struct ImplAssocItemValue {
    /// The definition of the item in the trait impl. This is an `AssocTy`, `AssocFn` or
    /// `AssocConst`.
    pub item: ItemRef,
    /// Value of the associated type, if carried directly. `None` for methods and consts.
    pub assoc_ty_value: Option<Ty>,
    /// Trait proofs for the implied associated type bounds. E.g.:
    /// ```ignore
    /// trait Foo {
    ///     type Type<T>: Clone,
    /// }
    /// impl Foo for () {
    ///     type Type<T>: Arc<T>; // would supply a proof for `Arc<T>: Clone`.
    /// }
    /// ```
    /// Empty for methods and consts.
    pub implied_trait_proofs: Vec<TraitProof>,
}

/// Partial data for a trait impl, used for fake trait impls that we generate ourselves such as
/// `FnOnce` and `Drop` impls.
#[derive(Debug, Clone)]
pub struct VirtualTraitImpl<'tcx> {
    /// The trait that is implemented by this impl block.
    pub trait_pred: TraitPredicate,
    /// The trait proofs required to satisfy the predicates on the trait declaration.
    pub implied_trait_proofs: Vec<TraitProof>,
    /// The associated types and their predicates, in definition order.
    pub types: Vec<(Ty, Vec<TraitProof>)>,
    /// The methods, in definition order.
    pub methods: Vec<DefId>,
    /// The item under which this impl was built.
    owner: DefId,
    /// The trait ref of the implemented trait, for `dyn_data`.
    trait_ref: ty::TraitRef<'tcx>,
    /// Computed on demand, see [`VirtualTraitImpl::dyn_self`].
    dyn_data: OnceCell<Option<(Ty, Vec<PolyFnSig>)>>,
}

impl<'tcx> VirtualTraitImpl<'tcx> {
    /// The `dyn Trait<..>` type for the implemented trait ref and the vtable signatures of the
    /// methods (in definition order), if the trait is dyn-compatible. This is only needed for
    /// vtables so we compute it on demand.
    fn dyn_data(&self, s: &impl BaseState<'tcx>) -> Option<&(Ty, Vec<PolyFnSig>)> {
        self.dyn_data
            .get_or_init(|| {
                let s = &s.with_hax_owner(&self.owner);
                let tcx = s.base().tcx;
                let trait_ref = self.trait_ref;
                // The environment may lack the predicates needed to prove the trait holds;
                // translating the `dyn Trait` type would then report errors, so we check first.
                let dyn_self = (tcx.is_dyn_compatible(trait_ref.def_id)
                    && !solve_trait(s, ty::Binder::dummy(trait_ref)).kind.is_error())
                .then(|| dyn_self_ty(tcx, s.typing_env(), trait_ref))
                .flatten()?;
                let vtable_sigs = self
                    .methods
                    .iter()
                    .map(|method| vtable_sig_with_dyn_self(s, method.real_rust_def_id(), dyn_self))
                    .collect();
                Some((dyn_self.sinto(s), vtable_sigs))
            })
            .as_ref()
    }
    /// The `dyn Trait<..>` type for the implemented trait ref, if dyn-compatible.
    pub fn dyn_self(&self, s: &impl BaseState<'tcx>) -> Option<Ty> {
        self.dyn_data(s).map(|(dyn_self, _)| dyn_self.clone())
    }
    /// The vtable signature of the `i`th method, if the trait is dyn-compatible.
    pub fn vtable_sig(&self, s: &impl BaseState<'tcx>, i: usize) -> Option<&PolyFnSig> {
        self.dyn_data(s).map(|(_, sigs)| &sigs[i])
    }
}

impl<'tcx> FullDef<'tcx> {
    pub fn def_id(&self) -> &DefId {
        &self.this.def_id
    }

    /// Reference to the item itself.
    pub fn this(&self) -> &ItemRef {
        &self.this
    }

    pub fn kind(&self) -> &FullDefKind<'tcx> {
        &self.kind
    }

    /// Evaluate the value of a `Const` or `AssocConst` item.
    pub fn const_value<S>(&self, s: &S) -> Option<ConstantExpr>
    where
        S: BaseState<'tcx>,
    {
        match self.kind() {
            FullDefKind::Const(_) | FullDefKind::AssocConst(_) => {}
            _ => panic!("expected a Const or AssocConst definition"),
        }
        let s = &s.with_hax_owner(self.def_id());
        let tcx = s.base().tcx;
        let def_id = self.def_id().as_real_def_id()?;
        let args = self.this().rustc_args(s);
        let kind =
            ty::AliasConstKind::new_from_def_id(tcx, def_id, ty::AliasConstInherentArgsKind::Impl);
        let uneval = ty::AliasConst::new(tcx, kind, args);
        let Some(c) = eval_ty_constant(s, uneval) else {
            // Const-evaluation gives up on a const that isn't monomorphic. For "trivial" consts,
            // we can still read the value directly.
            let (val, ty) = tcx.trivial_const(def_id)?;
            let expr = const_value_to_constant_expr(s, ty, val, tcx.def_span(def_id));
            return expr.discard_err();
        };
        match c.kind() {
            ty::ConstKind::Error(..) => None,
            _ => Some(c.sinto(s)),
        }
    }

    /// Evaluate the initializer of a `Static` item.
    pub fn static_value<S>(&self, s: &S) -> Option<ConstantExpr>
    where
        S: BaseState<'tcx>,
    {
        match self.kind() {
            FullDefKind::Static(_) => {}
            _ => panic!("expected a Static definition"),
        }
        let s = &s.with_hax_owner(self.def_id());

        if let DefIdBase::Alloc(alloc_id) = self.def_id().base {
            // If this is an allocation, it is untyped and we need to read it as raw memory.
            let val = mir::ConstValue::Indirect {
                alloc_id,
                offset: rustc_abi::Size::ZERO,
            };
            let ty = self.def_id().type_of(s).instantiate_identity();
            let span = rustc_span::DUMMY_SP;
            return const_value_to_raw_memory(s, ty.skip_normalization(), val, span).discard_err();
        }

        let def_id = self.def_id().as_real_def_id()?;
        // Statics in `extern` blocks have no value or initializer
        if s.base().tcx.is_foreign_item(def_id) {
            return None;
        }
        let args = self.this().rustc_args(s);
        let ty = inst_binder(
            s.base().tcx,
            s.typing_env(),
            Some(args),
            self.def_id().type_of(s),
        );
        let alloc = s.base().tcx.eval_static_initializer(def_id).ok()?;
        // A static whose type has interior mutability gets a mutable allocation, which
        // const-eval refuses to read. We don't care though, so we reintern it as immutable.
        let alloc = if alloc.inner().mutability.is_mut() {
            let mut alloc = alloc.inner().clone();
            alloc.mutability = rustc_middle::mir::Mutability::Not;
            s.base().tcx.mk_const_alloc(alloc)
        } else {
            alloc
        };
        // `eval_static_initializer` returns an interned allocation without an `AllocId`; give it
        // one so we can inspect it through the existing `ConstValue` path.
        let val = mir::ConstValue::Indirect {
            alloc_id: s.base().tcx.reserve_and_set_memory_alloc(alloc),
            offset: rustc_abi::Size::ZERO,
        };
        const_value_to_constant_expr(s, ty, val, s.base().tcx.def_span(def_id)).discard_err()
    }

    /// Returns the generics and predicates for definitions that have those.
    pub fn param_env(&self) -> Option<&ParamEnv> {
        match self.kind() {
            FullDefKind::Adt(d) => Some(d.param_env()),
            FullDefKind::Trait(d) => Some(d.param_env()),
            FullDefKind::TraitAlias(d) => Some(d.param_env()),
            FullDefKind::TyAlias(d) => Some(d.param_env()),
            FullDefKind::AssocTy(d) => Some(d.param_env()),
            FullDefKind::Fn(d) => Some(d.param_env()),
            FullDefKind::FnPtr(d) => Some(d.param_env()),
            FullDefKind::AssocFn(d) => Some(d.param_env()),
            FullDefKind::Closure(d) => Some(d.param_env()),
            FullDefKind::Const(d) => Some(d.param_env()),
            FullDefKind::AssocConst(d) => Some(d.param_env()),
            FullDefKind::Static(d) => Some(d.param_env()),
            FullDefKind::TraitImpl(d) => Some(d.param_env()),
            FullDefKind::InherentImpl(d) => Some(d.param_env()),
            _ => None,
        }
    }

    /// Return the parent of this item if the item inherits the typing context from its parent.
    pub fn typing_parent(&self, s: &impl BaseState<'tcx>) -> Option<ItemRef> {
        self.this().typing_parent(s)
    }

    /// Whether the item has any generics at all (including parent generics).
    pub fn has_any_generics(&self) -> bool {
        match self.param_env() {
            Some(p) => p.generics.parent_count != 0 || !p.generics.params.is_empty(),
            None => false,
        }
    }

    /// Whether the item has any generics of its own (ignoring parent generics).
    pub fn has_own_generics(&self) -> bool {
        match self.param_env() {
            Some(p) => !p.generics.params.is_empty(),
            None => false,
        }
    }

    /// Whether the item has any generics or predicates of its own (ignoring parent
    /// generics/predicates).
    pub fn has_own_generics_or_predicates(&self) -> bool {
        match self.param_env() {
            Some(p) => {
                let has_predicates =
                    if let FullDefKind::AssocFn(_) | FullDefKind::AssocConst(_) = self.kind() {
                        // Assoc fns and consts have a special `Self: Trait` predicate inserted, which
                        // we don't want to consider as an "own predicate".
                        p.predicates.predicates.len() > 1
                    } else {
                        !p.predicates.predicates.is_empty()
                    };
                !p.generics.params.is_empty() || has_predicates
            }
            None => false,
        }
    }

    /// Returns the late bound parameters of this item, if any. Returns an empty binder if there a
    /// are none.
    pub fn late_bound(&self) -> Binder<()> {
        match self.kind() {
            FullDefKind::Fn(f) => f.sig().as_ref().rebind(()),
            FullDefKind::FnPtr(f) => f.sig().as_ref().rebind(()),
            FullDefKind::AssocFn(f) => f.sig().as_ref().rebind(()),
            _ => Binder::empty(),
        }
    }

    /// Lists the children of this item that can be named, in the way of normal rust paths. For
    /// types, this includes inherent items.
    pub fn nameable_children(&self, s: &impl BaseState<'tcx>) -> Vec<(Symbol, DefId)> {
        let mut children = match self.kind() {
            FullDefKind::Mod(m) => m
                .items(s)
                .iter()
                .filter_map(|(opt_ident, def_id)| Some((opt_ident.as_ref()?.0, def_id.clone())))
                .collect(),
            FullDefKind::Adt(adt) if matches!(adt.adt_kind(), AdtKind::Enum) => adt
                .variants()
                .iter()
                .map(|variant| (variant.name, variant.def_id.clone()))
                .collect(),
            FullDefKind::InherentImpl(i) => i
                .items(s)
                .iter()
                .filter_map(|item| Some((item.name?, item.def_id.clone())))
                .collect(),
            FullDefKind::Trait(t) => t
                .items(s)
                .iter()
                .filter_map(|item| Some((item.name?, item.def_id.clone())))
                .collect(),
            FullDefKind::TraitImpl(timpl) => timpl
                .items(s)
                .iter()
                .filter_map(|item| Some((item.name?, item.def_id()?.clone())))
                .collect(),
            _ => vec![],
        };
        // Add inherent impl items if any.
        if let Some(rust_def_id) = self.def_id().as_real_def_id() {
            let tcx = s.base().tcx;
            for impl_def_id in tcx.inherent_impls(rust_def_id) {
                children.extend(
                    tcx.associated_items(*impl_def_id)
                        .in_definition_order()
                        .filter_map(|assoc| Some((assoc.opt_name()?, assoc.def_id).sinto(s))),
                );
            }
        }
        children
    }
}

impl ImplAssocItem {
    /// The id of the item declaration.
    pub fn decl_def_id(&self) -> &DefId {
        &self.decl_def_id
    }
    /// The id of the item implementation, if there is one.
    pub fn def_id(&self) -> Option<&DefId> {
        Some(&self.value.as_ref()?.skip_binder.item.def_id)
    }
}

fn get_self_predicate<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> TraitPredicate {
    use ty::Upcast;
    let tcx = s.base().tcx;
    let pred: ty::TraitClause = self_trait_ref(s, args).no_bound_vars().unwrap().upcast(tcx);
    pred.sinto(s)
}

fn self_trait_ref<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> ty::PolyTraitRef<'tcx> {
    let tcx = s.base().tcx;
    let def_id = s.owner().as_real_def_id().unwrap();
    let typing_env = s.typing_env();
    let pred = self_predicate(tcx, def_id);
    substitute(tcx, typing_env, args, pred)
}

/// Generates a `dyn Trait<Args.., Ty = <Self as Trait>::Ty..>` type for this trait.
fn get_trait_decl_dyn_self_ty<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> Option<ty::Ty<'tcx>> {
    let tcx = s.base().tcx;
    let typing_env = s.typing_env();
    let def_id = s.owner();

    let self_tref = ty::TraitRef::new_from_args(
        tcx,
        def_id.real_rust_def_id(),
        args.unwrap_or_else(|| def_id.identity_args(s)),
    );
    rustc_utils::dyn_self_ty(tcx, typing_env, self_tref).map(|ty| {
        if args.is_some() {
            erase_free_regions(tcx, ty)
        } else {
            ty
        }
    })
}

/// Do the trait resolution necessary to create a new impl for the given trait_ref. Used when we
/// generate fake trait impls e.g. for `FnOnce` and `Drop`.
fn virtual_impl_for<'tcx, S>(s: &S, trait_ref: ty::TraitRef<'tcx>) -> Box<VirtualTraitImpl<'tcx>>
where
    S: UnderOwnerState<'tcx>,
{
    let tcx = s.base().tcx;
    let trait_pred = TraitPredicate {
        trait_ref: trait_ref.sinto(s),
        is_positive: true,
    };
    // Trait proofs required by the trait.
    let required_trait_proofs = solve_item_implied_traits(s, trait_ref.def_id, trait_ref.args);
    let types = tcx
        .associated_items(trait_ref.def_id)
        .in_definition_order()
        .filter(|assoc| matches!(assoc.kind, ty::AssocKind::Type { .. }))
        .map(|assoc| {
            // This assumes non-GAT because this is for builtin-trait (that don't
            // have GATs).
            let ty =
                ty::Ty::new_projection(tcx, ty::IsRigid::No, assoc.def_id, trait_ref.args).sinto(s);
            // Trait proofs required by the type.
            let required_trait_proofs = solve_item_implied_traits(s, assoc.def_id, trait_ref.args);
            (ty, required_trait_proofs)
        })
        .collect();
    let methods = tcx
        .associated_items(trait_ref.def_id)
        .in_definition_order()
        .filter(|assoc| matches!(assoc.kind, ty::AssocKind::Fn { .. }))
        .map(|assoc| assoc.def_id.sinto(s))
        .collect();
    Box::new(VirtualTraitImpl {
        trait_pred,
        implied_trait_proofs: required_trait_proofs,
        types,
        methods,
        owner: s.owner(),
        trait_ref,
        dyn_data: Default::default(),
    })
}

fn get_param_env<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> ParamEnv {
    let tcx = s.base().tcx;
    let owner = s.owner();
    // Rustc adds generic params to closures and inline consts for impl details purposes; we hide these.
    let is_typeck_child = owner.is_typeck_child(s);
    let mut generics = owner.generics_of(s).sinto(s);
    if is_typeck_child {
        generics.params = Default::default();
    }

    let parent = generics.parent.as_ref().map(|parent| {
        let parent_args = args
            .map(|args| args.truncate_to(tcx, parent.generics_of(s)))
            .unwrap_or_else(|| parent.identity_args(s));
        ItemRef::translate_from_hax_def_id(s, parent.clone(), parent_args)
    });
    match args {
        None => ParamEnv {
            generics,
            predicates: if is_typeck_child {
                GenericPredicates::default()
            } else {
                owner.required_predicates(s).sinto(s)
            },
            parent,
        },
        // An instantiated item is monomorphic.
        Some(_) => ParamEnv {
            generics: TyGenerics {
                parent_count: 0,
                params: Default::default(),
                ..generics
            },
            predicates: GenericPredicates::default(),
            parent,
        },
    }
}

fn get_implied_predicates<'tcx, S: UnderOwnerState<'tcx>>(
    s: &S,
    args: Option<ty::GenericArgsRef<'tcx>>,
) -> GenericPredicates {
    let tcx = s.base().tcx;
    let owner = s.owner();
    let typing_env = s.typing_env();
    let mut implied_predicates =
        ItemPredicates::implied(s.base().elab_ctx, &s.base_state(), owner.clone());
    if args.is_some() {
        for pred in implied_predicates.iter_mut() {
            pred.clause = substitute(tcx, typing_env, args, pred.clause);
        }
    }
    implied_predicates.sinto(s)
}
