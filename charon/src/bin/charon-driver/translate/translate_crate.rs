use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::options::{CliOpts, TranslateOptions};
use charon_lib::transform::TransformCtx;
use hax::FullDefKind;
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, VariantIndexArity)]
pub enum TransItemSourceKind {
    Global,
    TraitDecl,
    TraitImpl,
    Fun,
    Type,
    /// We don't translate these as proper items, but we translate them a bit in names.
    InherentImpl,
    /// An impl of the appropriate `Fn*` trait for the given closure type.
    ClosureTraitImpl(ClosureKind),
    /// The `call_*` method of the appropriate `Fn*` trait.
    ClosureMethod(ClosureKind),
    /// A cast of a state-less closure as a function pointer.
    ClosureAsFnCast,
}

impl TransItemSource {
    pub fn new(def_id: hax::DefId, kind: TransItemSourceKind) -> Self {
        Self { def_id, kind }
    }

    pub fn as_def_id(&self) -> &hax::DefId {
        &self.def_id
    }

    /// Value with which we order values.
    fn sort_key(&self) -> impl Ord {
        let (variant_index, _) = self.kind.variant_index_arity();
        let def_id = self.as_def_id();
        let closure_kind = match self.kind {
            TransItemSourceKind::ClosureTraitImpl(k) | TransItemSourceKind::ClosureMethod(k) => {
                match k {
                    ClosureKind::Fn => 1,
                    ClosureKind::FnMut => 2,
                    ClosureKind::FnOnce => 3,
                }
            }
            _ => 0,
        };
        (def_id.index, variant_index, closure_kind)
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
    /// Register a HIR item and all its children. We call this on the crate root items and end up
    /// exploring the whole crate.
    fn register_module_item(&mut self, def_id: &hax::DefId) {
        use hax::DefKind::*;
        trace!("Registering {def_id:?}");

        match &def_id.kind {
            Enum { .. } | Struct { .. } | Union { .. } | TyAlias { .. } | ForeignTy => {
                let _ = self.register_type_decl_id(&None, def_id);
            }
            Fn { .. } | AssocFn { .. } => {
                let _ = self.register_fun_decl_id(&None, def_id);
            }
            Const { .. } | Static { .. } | AssocConst { .. } => {
                let _ = self.register_global_decl_id(&None, def_id);
            }

            Trait { .. } | TraitAlias { .. } => {
                let _ = self.register_trait_decl_id(&None, def_id);
            }
            Impl { of_trait: true } => {
                let _ = self.register_trait_impl_id(&None, def_id);
            }

            Impl { of_trait: false } | Mod { .. } | ForeignMod { .. } => {
                let Ok(def) = self.hax_def(def_id) else {
                    return; // Error has already been emitted
                };
                let Ok(name) = self.def_id_to_name(&def.def_id) else {
                    return; // Error has already been emitted
                };
                let opacity = self.opacity_for_name(&name);
                let trans_src =
                    TransItemSource::new(def.def_id.clone(), TransItemSourceKind::TraitImpl);
                let item_meta = self.translate_item_meta(&def, &trans_src, name, opacity);
                let _ = self.register_module(item_meta, &def);
            }

            // We skip these
            ExternCrate { .. } | GlobalAsm { .. } | Macro { .. } | Use { .. } => {}
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
            }
        }
    }

    /// Register the items inside this module.
    // TODO: we may want to accumulate the set of modules we found, to check that all
    // the opaque modules given as arguments actually exist
    fn register_module(&mut self, item_meta: ItemMeta, def: &hax::FullDef) -> Result<(), Error> {
        let opacity = item_meta.opacity;
        if !opacity.is_transparent() {
            return Ok(());
        }
        match def.kind() {
            FullDefKind::InherentImpl { items, .. } => {
                for (_, item_def) in items {
                    self.register_module_item(&item_def.def_id);
                }
            }
            FullDefKind::Mod { items, .. } => {
                for (_, def_id) in items {
                    self.register_module_item(def_id);
                }
            }
            FullDefKind::ForeignMod { items, .. } => {
                // Foreign modules can't be named or have attributes, so we can't mark them opaque.
                for def_id in items {
                    self.register_module_item(def_id);
                }
            }
            _ => panic!("Item should be a module but isn't: {def:?}"),
        }
        Ok(())
    }

    pub(crate) fn register_id_no_enqueue(
        &mut self,
        dep_src: &Option<DepSource>,
        src: TransItemSource,
    ) -> AnyTransId {
        let item_id = match self.id_map.get(&src) {
            Some(tid) => *tid,
            None => {
                let trans_id = match src.kind {
                    TransItemSourceKind::Type => {
                        AnyTransId::Type(self.translated.type_decls.reserve_slot())
                    }
                    TransItemSourceKind::TraitDecl => {
                        AnyTransId::TraitDecl(self.translated.trait_decls.reserve_slot())
                    }
                    TransItemSourceKind::TraitImpl | TransItemSourceKind::ClosureTraitImpl(..) => {
                        AnyTransId::TraitImpl(self.translated.trait_impls.reserve_slot())
                    }
                    TransItemSourceKind::Global => {
                        AnyTransId::Global(self.translated.global_decls.reserve_slot())
                    }
                    TransItemSourceKind::Fun
                    | TransItemSourceKind::ClosureMethod(..)
                    | TransItemSourceKind::ClosureAsFnCast => {
                        AnyTransId::Fun(self.translated.fun_decls.reserve_slot())
                    }
                    TransItemSourceKind::InherentImpl => {
                        panic!("inherent impls aren't translated to items")
                    }
                };
                // Add the id to the queue of declarations to translate
                self.id_map.insert(src.clone(), trans_id);
                self.reverse_id_map.insert(trans_id, src.clone());
                // Store the name early so the name matcher can identify paths. We can't to it for
                // trait impls because they register themselves when computing their name.
                if !matches!(src.kind, TransItemSourceKind::TraitImpl) {
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
        item_id
    }

    /// Register this id and enqueue it for translation.
    pub(crate) fn register_and_enqueue_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
        kind: TransItemSourceKind,
    ) -> AnyTransId {
        let id = TransItemSource::new(def_id.clone(), kind);
        self.items_to_translate.insert(id.clone());
        self.register_id_no_enqueue(src, id)
    }

    pub(crate) fn register_type_decl_id(
        &mut self,
        src: &Option<DepSource>,
        def_id: &hax::DefId,
    ) -> TypeDeclId {
        *self
            .register_and_enqueue_id(src, def_id, TransItemSourceKind::Type)
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
            .as_global()
            .unwrap()
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

    pub(crate) fn register_id_no_enqueue(&mut self, span: Span, id: TransItemSource) -> AnyTransId {
        let src = self.make_dep_source(span);
        self.t_ctx.register_id_no_enqueue(&src, id)
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
            resolve_drop_bounds: false,
        },
    );

    // Retrieve the crate name: if the user specified a custom name, use it, otherwise retrieve it
    // from hax.
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

    if options.start_from.is_empty() {
        // Recursively register all the items in the crate, starting from the crate root.
        ctx.register_module_item(&crate_def_id);
    } else {
        // Start translating from the selected items.
        for path in options.start_from.iter() {
            let path = path.split("::").collect_vec();
            let resolved = super::resolve_path::def_path_def_ids(&ctx.hax_state, &path);
            match resolved {
                Ok(resolved) => {
                    for def_id in resolved {
                        let def_id: hax::DefId = def_id.sinto(&ctx.hax_state);
                        ctx.register_module_item(&def_id);
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
