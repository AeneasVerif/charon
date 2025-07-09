//! This file governs the overall translation of items.
//!
//! Translation works as follows: we translate each `TransItemSource` of interest into an
//! appropriate item. In the process of translating an item we may find more `hax::DefId`s of
//! interest; we register those as an appropriate `TransItemSource`, which will 1/ enqueue the item
//! so that it eventually gets translated too, and 2/ return an `AnyTransId` we can use to refer to
//! it.
//!
//! We start with the DefId of the current crate (or of anything passed to `--start-from`) and
//! recursively translate everything we find.
//!
//! There's another important component at play: opacity. Each item is assigned an opacity based on
//! its name. By default, items from the local crate are transparent and items from foreign crates
//! are opaque (this can be controlled with `--include`, `--opaque` and `--exclude`). If an item is
//! opaque, its signature/"outer shell" will be translated (e.g. for functions that's the
//! signature) but not its contents.
use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::options::{CliOpts, TranslateOptions};
use charon_lib::transform::TransformCtx;
use hax_frontend_exporter::{self as hax, SInto};
use itertools::Itertools;
use macros::VariantIndexArity;
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::path::PathBuf;

/// The id of an untranslated item. Note that a given `DefId` may show up as multiple different
/// item sources, e.g. a constant will have both a `Global` version (for the constant itself) and a
/// `FunDecl` one (for its initializer function).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TransItemSource {
    pub def_id: hax::DefId,
    pub kind: TransItemSourceKind,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, VariantIndexArity)]
pub enum TransItemSourceKind {
    Global,
    TraitDecl,
    TraitImpl,
    Fun,
    Type,
    /// We don't translate these as proper items, but we translate them a bit in names.
    InherentImpl,
    /// We don't translate these as proper items, but we use them to explore the crate.
    Module,
    /// An impl of the appropriate `Fn*` trait for the given closure type.
    ClosureTraitImpl(ClosureKind),
    /// The `call_*` method of the appropriate `Fn*` trait.
    ClosureMethod(ClosureKind),
    /// A cast of a state-less closure as a function pointer.
    ClosureAsFnCast,
    /// A fictitious trait impl corresponding to the drop glue code for the given ADT.
    DropGlueImpl,
    /// The `drop` method for the impl above.
    DropGlueMethod,
}

impl TransItemSource {
    pub fn new(def_id: hax::DefId, kind: TransItemSourceKind) -> Self {
        Self { def_id, kind }
    }

    pub fn as_def_id(&self) -> &hax::DefId {
        &self.def_id
    }

    /// Whether this item is the "main" item for this def_id or not (e.g. drop impl/methods are not
    /// the main item).
    pub(crate) fn is_derived_item(&self) -> bool {
        use TransItemSourceKind::*;
        match self.kind {
            Global | TraitDecl | TraitImpl | InherentImpl | Module | Fun | Type => false,
            ClosureTraitImpl(..) | ClosureMethod(..) | ClosureAsFnCast | DropGlueImpl
            | DropGlueMethod => true,
        }
    }

    /// Value with which we order values.
    fn sort_key(&self) -> impl Ord + '_ {
        (self.def_id.index, &self.kind)
    }
}

/// Manual impls because `DefId` is not orderable.
impl PartialOrd for TransItemSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TransItemSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.sort_key().cmp(&other.sort_key())
    }
}

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    /// Returns the default translation kind for the given `DefId`. Returns `None` for items that
    /// we don't translate. Errors on unexpected items.
    pub fn base_kind_for_item(&mut self, def_id: &hax::DefId) -> Option<TransItemSourceKind> {
        use hax::DefKind::*;
        Some(match &def_id.kind {
            Enum { .. } | Struct { .. } | Union { .. } | TyAlias { .. } | ForeignTy => {
                TransItemSourceKind::Type
            }
            Fn { .. } | AssocFn { .. } => TransItemSourceKind::Fun,
            Const { .. } | Static { .. } | AssocConst { .. } => TransItemSourceKind::Global,
            Trait { .. } | TraitAlias { .. } => TransItemSourceKind::TraitDecl,
            Impl { of_trait: true } => TransItemSourceKind::TraitImpl,
            Impl { of_trait: false } => TransItemSourceKind::InherentImpl,
            Mod { .. } | ForeignMod { .. } => TransItemSourceKind::Module,

            // We skip these
            ExternCrate { .. } | GlobalAsm { .. } | Macro { .. } | Use { .. } => return None,
            // We cannot encounter these since they're not top-level items.
            AnonConst { .. }
            | AssocTy { .. }
            | Closure { .. }
            | ConstParam { .. }
            | Ctor { .. }
            | Field { .. }
            | InlineConst { .. }
            | PromotedConst { .. }
            | LifetimeParam { .. }
            | OpaqueTy { .. }
            | SyntheticCoroutineBody { .. }
            | TyParam { .. }
            | Variant { .. } => {
                let span = self.def_span(def_id);
                register_error!(
                    self,
                    span,
                    "Cannot register item `{def_id:?}` with kind `{:?}`",
                    def_id.kind
                );
                return None;
            }
        })
    }

    /// Add this item to the queue of items to translate. Each translated item will then
    /// recursively register the items it refers to. We call this on the crate root and end up
    /// exploring the whole crate.
    #[tracing::instrument(skip(self))]
    pub fn enqueue_item(&mut self, def_id: &hax::DefId) -> Option<AnyTransId> {
        let kind = self.base_kind_for_item(def_id)?;
        self.register_and_enqueue_id(&None, def_id, kind)
    }

    pub(crate) fn register_id_no_enqueue(
        &mut self,
        dep_src: &Option<DepSource>,
        src: &TransItemSource,
    ) -> Option<AnyTransId> {
        let item_id = match self.id_map.get(src) {
            Some(tid) => *tid,
            None => {
                use TransItemSourceKind::*;
                let trans_id = match src.kind {
                    Type => AnyTransId::Type(self.translated.type_decls.reserve_slot()),
                    TraitDecl => AnyTransId::TraitDecl(self.translated.trait_decls.reserve_slot()),
                    TraitImpl | ClosureTraitImpl(..) | DropGlueImpl => {
                        AnyTransId::TraitImpl(self.translated.trait_impls.reserve_slot())
                    }
                    Global => AnyTransId::Global(self.translated.global_decls.reserve_slot()),
                    Fun | ClosureMethod(..) | ClosureAsFnCast | DropGlueMethod => {
                        AnyTransId::Fun(self.translated.fun_decls.reserve_slot())
                    }
                    InherentImpl | Module => return None,
                };
                // Add the id to the queue of declarations to translate
                self.id_map.insert(src.clone(), trans_id);
                self.reverse_id_map.insert(trans_id, src.clone());
                // Store the name early so the name matcher can identify paths. We can't to it for
                // trait impls because they register themselves when computing their name.
                if !matches!(src.kind, TraitImpl) {
                    if let Ok(name) = self.def_id_to_name(src.as_def_id()) {
                        self.translated.item_names.insert(trans_id, name);
                    }
                }
                trans_id
            }
        };
        self.errors
            .borrow_mut()
            .register_dep_source(dep_src, item_id, src.as_def_id().is_local);
        Some(item_id)
    }

    /// Register this id and enqueue it for translation.
    pub(crate) fn register_and_enqueue_id(
        &mut self,
        dep_src: &Option<DepSource>,
        def_id: &hax::DefId,
        kind: TransItemSourceKind,
    ) -> Option<AnyTransId> {
        let item_src = TransItemSource::new(def_id.clone(), kind);
        let id = self.register_id_no_enqueue(dep_src, &item_src);
        self.items_to_translate.insert(item_src);
        id
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::Type)
            .unwrap()
            .as_type()
            .unwrap()
    }

    pub(crate) fn register_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::Fun)
            .unwrap()
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_trait_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> TraitDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::TraitDecl)
            .unwrap()
            .as_trait_decl()
            .unwrap()
    }

    pub(crate) fn register_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> TraitImplId {
        // Register the corresponding trait early so we can filter on its name.
        if let Ok(def) = self.hax_def(def_id) {
            let trait_id = match def.kind() {
                hax::FullDefKind::TraitImpl { trait_pred, .. } => &trait_pred.trait_ref.def_id,
                hax::FullDefKind::TraitAlias { .. } => def_id,
                _ => unreachable!(),
            };
            let _ = self.register_trait_decl_id(src, trait_id);
        }

        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::TraitImpl)
            .unwrap()
            .as_trait_impl()
            .unwrap()
    }

    pub(crate) fn register_closure_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
        kind: ClosureKind,
    ) -> TraitImplId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::ClosureTraitImpl(kind))
            .unwrap()
            .as_trait_impl()
            .unwrap()
    }

    pub(crate) fn register_closure_method_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
        kind: ClosureKind,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::ClosureMethod(kind))
            .unwrap()
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_closure_as_fun_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::ClosureAsFnCast)
            .unwrap()
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_global_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> GlobalDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::Global)
            .unwrap()
            .as_global()
            .unwrap()
    }

    pub(crate) fn register_drop_trait_impl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> TraitImplId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::DropGlueImpl)
            .unwrap()
            .as_trait_impl()
            .unwrap()
    }

    pub(crate) fn register_drop_method_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> FunDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::DropGlueMethod)
            .unwrap()
            .as_fun()
            .unwrap()
    }

    pub(crate) fn register_target_info(&mut self) {
        let target_data = &self.tcx.data_layout;
        self.translated.target_information = krate::TargetInfo {
            target_pointer_size: target_data.pointer_size().bytes(),
            is_little_endian: matches!(target_data.endian, rustc_abi::Endian::Little),
        }
    }
}

// Id and item reference registration.
impl<'tcx, 'ctx> ItemTransCtx<'tcx, 'ctx> {
    pub(crate) fn make_dep_source(&self, span: Span) -> Option<DepSource> {
        Some(DepSource {
            src_id: self.item_id?,
            span: self.item_src.as_def_id().is_local.then_some(span),
        })
    }

    pub(crate) fn register_id_no_enqueue(
        &mut self,
        span: Span,
        id: TransItemSource,
    ) -> Option<AnyTransId> {
        let src = self.make_dep_source(span);
        self.t_ctx.register_id_no_enqueue(&src, &id)
    }

    pub(crate) fn register_type_decl_id(&mut self, span: Span, id: &hax::DefId) -> TypeDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_type_decl_id(&src, id)
    }

    /// Translate a type def id
    pub(crate) fn translate_type_id(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
    ) -> Result<TypeId, Error> {
        Ok(match self.recognize_builtin_type(def_id)? {
            Some(id) => TypeId::Builtin(id),
            None => TypeId::Adt(self.register_type_decl_id(span, def_id)),
        })
    }

    pub(crate) fn translate_type_decl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<TypeDeclRef, Error> {
        let id = self.translate_type_id(span, &item.def_id)?;
        let generics = self.translate_generic_args(span, &item.generic_args, &item.impl_exprs)?;
        Ok(TypeDeclRef {
            id,
            generics: Box::new(generics),
        })
    }

    pub(crate) fn register_fun_decl_id(&mut self, span: Span, id: &hax::DefId) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_fun_decl_id(&src, id)
    }

    pub(crate) fn register_fun_decl_id_no_enqueue(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
    ) -> FunDeclId {
        self.register_id_no_enqueue(
            span,
            TransItemSource::new(def_id.clone(), TransItemSourceKind::Fun),
        )
        .unwrap()
        .as_fun()
        .copied()
        .unwrap()
    }

    /// Translate a function def id
    pub(crate) fn translate_fun_id(
        &mut self,
        span: Span,
        def_id: &hax::DefId,
    ) -> Result<FunId, Error> {
        Ok(match self.recognize_builtin_fun(def_id)? {
            Some(id) => FunId::Builtin(id),
            None => FunId::Regular(self.register_fun_decl_id(span, def_id)),
        })
    }

    /// Auxiliary function to translate function calls and references to functions.
    /// Translate a function id applied with some substitutions.
    #[tracing::instrument(skip(self, span))]
    pub(crate) fn translate_fn_ptr(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<RegionBinder<FnPtr>, Error> {
        let fun_id = self.translate_fun_id(span, &item.def_id)?;
        let late_bound = match self.hax_def(&item.def_id)?.kind() {
            hax::FullDefKind::Fn { sig, .. } | hax::FullDefKind::AssocFn { sig, .. } => {
                Some(sig.as_ref().rebind(()))
            }
            _ => None,
        };
        let bound_generics = self.translate_generic_args_with_late_bound(
            span,
            &item.generic_args,
            &item.impl_exprs,
            late_bound,
        )?;
        let fun_id = match &item.in_trait {
            // Direct function call
            None => FunIdOrTraitMethodRef::Fun(fun_id),
            // Trait method
            Some(impl_expr) => {
                let trait_ref = self.translate_trait_impl_expr(span, impl_expr)?;
                let name = self.t_ctx.translate_trait_item_name(&item.def_id)?;
                let method_decl_id = *fun_id
                    .as_regular()
                    .expect("methods are not builtin functions");
                FunIdOrTraitMethodRef::Trait(trait_ref.move_under_binder(), name, method_decl_id)
            }
        };
        Ok(bound_generics.map(|generics| FnPtr {
            func: Box::new(fun_id),
            generics: Box::new(generics),
        }))
    }

    pub(crate) fn register_global_decl_id(&mut self, span: Span, id: &hax::DefId) -> GlobalDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_global_decl_id(&src, id)
    }

    pub(crate) fn translate_global_decl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<GlobalDeclRef, Error> {
        let id = self.register_global_decl_id(span, &item.def_id);
        let generics = self.translate_generic_args(span, &item.generic_args, &item.impl_exprs)?;
        Ok(GlobalDeclRef {
            id,
            generics: Box::new(generics),
        })
    }

    pub(crate) fn register_trait_decl_id(&mut self, span: Span, id: &hax::DefId) -> TraitDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_decl_id(&src, id)
    }

    pub(crate) fn translate_trait_decl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<TraitDeclRef, Error> {
        let id = self.register_trait_decl_id(span, &item.def_id);
        let generics = self.translate_generic_args(span, &item.generic_args, &item.impl_exprs)?;
        Ok(TraitDeclRef {
            id,
            generics: Box::new(generics),
        })
    }

    pub(crate) fn register_trait_impl_id(&mut self, span: Span, id: &hax::DefId) -> TraitImplId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_trait_impl_id(&src, id)
    }

    pub(crate) fn translate_trait_impl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<TraitImplRef, Error> {
        let id = self.register_trait_impl_id(span, &item.def_id);
        let generics = self.translate_generic_args(span, &item.generic_args, &item.impl_exprs)?;
        Ok(TraitImplRef {
            id,
            generics: Box::new(generics),
        })
    }

    pub(crate) fn register_closure_trait_impl_id(
        &mut self,
        span: Span,
        id: &hax::DefId,
        kind: ClosureKind,
    ) -> TraitImplId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_closure_trait_impl_id(&src, id, kind)
    }

    pub(crate) fn register_closure_method_decl_id(
        &mut self,
        span: Span,
        id: &hax::DefId,
        kind: ClosureKind,
    ) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_closure_method_decl_id(&src, id, kind)
    }

    pub(crate) fn register_closure_as_fun_decl_id(
        &mut self,
        span: Span,
        id: &hax::DefId,
    ) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_closure_as_fun_decl_id(&src, id)
    }

    pub(crate) fn register_drop_trait_impl_id(
        &mut self,
        span: Span,
        id: &hax::DefId,
    ) -> TraitImplId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_drop_trait_impl_id(&src, id)
    }

    pub(crate) fn translate_drop_trait_impl_ref(
        &mut self,
        span: Span,
        item: &hax::ItemRef,
    ) -> Result<TraitImplRef, Error> {
        let id = self.register_drop_trait_impl_id(span, &item.def_id);
        let generics = self.translate_generic_args(span, &item.generic_args, &item.impl_exprs)?;
        Ok(TraitImplRef {
            id,
            generics: Box::new(generics),
        })
    }

    pub(crate) fn register_drop_method_id(&mut self, span: Span, id: &hax::DefId) -> FunDeclId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_drop_method_id(&src, id)
    }
}

#[tracing::instrument(skip(tcx))]
pub fn translate<'tcx, 'ctx>(
    options: &CliOpts,
    tcx: TyCtxt<'tcx>,
    sysroot: PathBuf,
) -> TransformCtx {
    let hax_state = hax::state::State::new(
        tcx,
        hax::options::Options {
            inline_anon_consts: true,
            resolve_drop_bounds: options.add_drop_bounds,
        },
    );

    let crate_def_id: hax::DefId = rustc_span::def_id::CRATE_DEF_ID
        .to_def_id()
        .sinto(&hax_state);
    let crate_name = crate_def_id.krate.clone();
    trace!("# Crate: {}", crate_name);

    let mut error_ctx = ErrorCtx::new(!options.abort_on_error, options.error_on_warnings);
    let translate_options = TranslateOptions::new(&mut error_ctx, options);
    let mut ctx = TranslateCtx {
        tcx,
        sysroot,
        hax_state,
        options: translate_options,
        errors: RefCell::new(error_ctx),
        translated: TranslatedCrate {
            crate_name,
            options: options.clone(),
            ..TranslatedCrate::default()
        },
        id_map: Default::default(),
        reverse_id_map: Default::default(),
        file_to_id: Default::default(),
        items_to_translate: Default::default(),
        processed: Default::default(),
        cached_item_metas: Default::default(),
        cached_names: Default::default(),
    };
    ctx.register_target_info();

    if options.start_from.is_empty() {
        // Recursively register all the items in the crate, starting from the crate root.
        ctx.enqueue_item(&crate_def_id);
    } else {
        // Start translating from the selected items.
        for path in options.start_from.iter() {
            let path = path.split("::").collect_vec();
            let resolved = super::resolve_path::def_path_def_ids(&ctx.hax_state, &path);
            match resolved {
                Ok(resolved) => {
                    for def_id in resolved {
                        let def_id: hax::DefId = def_id.sinto(&ctx.hax_state);
                        ctx.enqueue_item(&def_id);
                    }
                }
                Err(path) => {
                    let path = path.join("::");
                    register_error!(
                        ctx,
                        Span::dummy(),
                        "path {path} does not correspond to any item"
                    );
                }
            }
        }
    }

    trace!(
        "Queue after we explored the crate:\n{:?}",
        &ctx.items_to_translate
    );

    // Translate.
    //
    // For as long as the queue of items to translate is not empty, we pop the top item and
    // translate it. If an item refers to non-translated (potentially external) items, we add them
    // to the queue.
    //
    // Note that the order in which we translate the definitions doesn't matter:
    // we never need to lookup a translated definition, and only use the map
    // from Rust ids to translated ids.
    while let Some(item_src) = ctx.items_to_translate.pop_first() {
        trace!("About to translate item: {:?}", item_src);
        if ctx.processed.insert(item_src.clone()) {
            ctx.translate_item(&item_src);
        }
    }

    // Return the context, dropping the hax state and rustc `tcx`.
    TransformCtx {
        options: ctx.options,
        translated: ctx.translated,
        errors: ctx.errors,
    }
}
