use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::options::CliOpts;
use charon_lib::transform::ctx::TransformOptions;
use charon_lib::transform::TransformCtx;
use hax_frontend_exporter as hax;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::path::PathBuf;

impl<'tcx, 'ctx> TranslateCtx<'tcx> {
    /// Register a HIR item and all its children. We call this on the crate root items and end up
    /// exploring the whole crate.
    fn register_local_item(&mut self, def_id: DefId) {
        use hax::FullDefKind;
        trace!("Registering {def_id:?}");

        let Ok(def) = self.hax_def(def_id) else {
            return; // Error has already been emitted
        };

        let Ok(name) = self.hax_def_id_to_name(&def.def_id) else {
            return; // Error has already been emitted
        };
        let opacity = self.opacity_for_name(&name);
        // Use `item_meta` to take into account the `charon::opaque` attribute.
        let opacity = self.translate_item_meta(&def, name, opacity).opacity;
        let explore_inside = !(opacity.is_opaque() || opacity.is_invisible());

        match def.kind() {
            FullDefKind::Enum { .. }
            | FullDefKind::Struct { .. }
            | FullDefKind::Union { .. }
            | FullDefKind::TyAlias { .. }
            | FullDefKind::AssocTy { .. }
            | FullDefKind::ForeignTy => {
                let _ = self.register_type_decl_id(&None, def_id);
            }

            FullDefKind::Fn { .. } | FullDefKind::AssocFn { .. } => {
                let _ = self.register_fun_decl_id(&None, def_id);
            }
            FullDefKind::Const { .. }
            | FullDefKind::Static { .. }
            | FullDefKind::AssocConst { .. } => {
                let _ = self.register_global_decl_id(&None, def_id);
            }

            FullDefKind::Trait { .. } => {
                let _ = self.register_trait_decl_id(&None, def_id);
            }
            FullDefKind::TraitImpl { .. } => {
                let _ = self.register_trait_impl_id(&None, def_id);
            }
            // TODO: trait aliases (https://github.com/AeneasVerif/charon/issues/366)
            FullDefKind::TraitAlias { .. } => {}

            FullDefKind::InherentImpl { items, .. } => {
                if explore_inside {
                    for (_, item_def) in items {
                        self.register_local_item(item_def.rust_def_id());
                    }
                }
            }
            FullDefKind::Mod { items, .. } => {
                // Explore the module, only if it was not marked as "opaque"
                // TODO: we may want to accumulate the set of modules we found, to check that all
                // the opaque modules given as arguments actually exist
                if explore_inside {
                    for def_id in items {
                        self.register_local_item(def_id.into());
                    }
                }
            }
            FullDefKind::ForeignMod { items, .. } => {
                // Foreign modules can't be named or have attributes, so we can't mark them opaque.
                for def_id in items {
                    self.register_local_item(def_id.into());
                }
            }

            // We skip these
            FullDefKind::ExternCrate { .. }
            | FullDefKind::GlobalAsm { .. }
            | FullDefKind::Macro { .. }
            | FullDefKind::Use { .. } => {}
            // We cannot encounter these since they're not top-level items.
            FullDefKind::AnonConst { .. }
            | FullDefKind::Closure { .. }
            | FullDefKind::ConstParam { .. }
            | FullDefKind::Ctor { .. }
            | FullDefKind::Field { .. }
            | FullDefKind::InlineConst { .. }
            | FullDefKind::LifetimeParam { .. }
            | FullDefKind::OpaqueTy { .. }
            | FullDefKind::SyntheticCoroutineBody { .. }
            | FullDefKind::TyParam { .. }
            | FullDefKind::Variant { .. } => {
                let span = self.def_span(def_id);
                register_error!(
                    self,
                    span,
                    "Cannot register this item: `{def_id:?}` with kind `{:?}`",
                    def.kind()
                );
            }
        }
    }

    pub(crate) fn translate_item(&mut self, item_src: TransItemSource, trans_id: AnyTransId) {
        if self
            .errors
            .borrow()
            .ignored_failed_decls
            .contains(&trans_id)
            || self.translated.get_item(trans_id).is_some()
        {
            return;
        }
        let rust_id = item_src.to_def_id();
        self.with_def_id(rust_id, trans_id, |mut ctx| {
            let span = ctx.def_span(rust_id);
            // Catch cycles
            let res = if ctx.translate_stack.contains(&trans_id) {
                register_error!(
                    ctx,
                    span,
                    "Cycle detected while translating {rust_id:?}! Stack: {:?}",
                    &ctx.translate_stack
                );
                Err(())
            } else {
                ctx.translate_stack.push(trans_id);

                let res = {
                    // Stopgap measure because there are still many panics in charon and hax.
                    let mut ctx = std::panic::AssertUnwindSafe(&mut ctx);
                    std::panic::catch_unwind(move || ctx.translate_item_aux(rust_id, trans_id))
                };
                let res = match res {
                    Ok(Ok(())) => Ok(()),
                    // Translation error
                    Ok(Err(_)) => Err(()),
                    // Panic
                    Err(_) => {
                        register_error!(
                            ctx,
                            span,
                            "Thread panicked when extracting item `{rust_id:?}`."
                        );
                        Err(())
                    }
                };
                // let res = ctx.translate_item_aux(rust_id, trans_id);
                ctx.translate_stack.pop();
                res
            };

            if res.is_err() {
                register_error!(ctx, span, "Item `{rust_id:?}` caused errors; ignoring.");
                ctx.errors.borrow_mut().ignore_failed_decl(trans_id);
            }
        })
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        rust_id: DefId,
        trans_id: AnyTransId,
    ) -> Result<(), Error> {
        // Translate the meta information
        let name = self.def_id_to_name(rust_id)?;
        self.translated.item_names.insert(trans_id, name.clone());
        let opacity = self.opacity_for_name(&name);
        if opacity.is_invisible() {
            // Don't even start translating the item. In particular don't call `hax_def` on it.
            return Ok(());
        }
        let def = self.hax_def(rust_id)?;
        let item_meta = self.translate_item_meta(&def, name, opacity);

        // Initialize the body translation context
        let bt_ctx = BodyTransCtx::new(rust_id, Some(trans_id), self);
        match trans_id {
            AnyTransId::Type(id) => {
                let ty = bt_ctx.translate_type(id, item_meta, &def)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            AnyTransId::Fun(id) => {
                let fun_decl = bt_ctx.translate_function(id, rust_id, item_meta, &def)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            AnyTransId::Global(id) => {
                let global_decl = bt_ctx.translate_global(id, rust_id, item_meta, &def)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            AnyTransId::TraitDecl(id) => {
                let trait_decl = bt_ctx.translate_trait_decl(id, rust_id, item_meta, &def)?;
                self.translated.trait_decls.set_slot(id, trait_decl);
            }
            AnyTransId::TraitImpl(id) => {
                let trait_impl = bt_ctx.translate_trait_impl(id, rust_id, item_meta, &def)?;
                self.translated.trait_impls.set_slot(id, trait_impl);
            }
        }
        Ok(())
    }

    /// While translating an item you may need the contents of another. Use this to retreive the
    /// translated version of this item.
    #[allow(dead_code)]
    pub(crate) fn get_or_translate(&mut self, id: AnyTransId) -> Result<AnyTransItem<'_>, Error> {
        let item_source = *self.reverse_id_map.get(&id).unwrap();
        // Translate if not already translated.
        self.translate_item(item_source, id);

        if self.errors.borrow().ignored_failed_decls.contains(&id) {
            let span = self.def_span(item_source.to_def_id());
            raise_error!(self, span, "Failed to translate item {id:?}.")
        }
        Ok(self.translated.get_item(id).unwrap())
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
            inline_macro_calls: Vec::new(),
        },
    );

    // Retrieve the crate name: if the user specified a custom name, use
    // it, otherwise retrieve it from rustc.
    let real_crate_name = tcx
        .crate_name(rustc_span::def_id::LOCAL_CRATE)
        .to_ident_string();
    let requested_crate_name: String = options
        .crate_name
        .as_ref()
        .unwrap_or(&real_crate_name)
        .clone();
    trace!("# Crate: {}", requested_crate_name);

    let mut error_ctx = ErrorCtx::new(!options.abort_on_error, options.error_on_warnings);
    let translate_options = TranslateOptions::new(&mut error_ctx, options);
    let mut ctx = TranslateCtx {
        tcx,
        sysroot,
        hax_state,
        options: translate_options,
        errors: RefCell::new(error_ctx),
        translated: TranslatedCrate {
            crate_name: requested_crate_name,
            options: options.clone(),
            real_crate_name,
            ..TranslatedCrate::default()
        },
        id_map: Default::default(),
        reverse_id_map: Default::default(),
        file_to_id: Default::default(),
        items_to_translate: Default::default(),
        translate_stack: Default::default(),
        cached_item_metas: Default::default(),
        cached_names: Default::default(),
    };

    // Recursively register all the items in the crate, starting from the crate root. We could
    // instead ask rustc for the plain list of all items in the crate, but we wouldn't be able to
    // skip items inside modules annotated with `#[charon::opaque]`.
    let crate_def_id = rustc_span::def_id::CRATE_DEF_ID.to_def_id();
    ctx.register_local_item(crate_def_id);

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
    while let Some((item_src, trans_id)) = ctx.items_to_translate.pop_first() {
        trace!("About to translate item: {:?}", item_src);
        ctx.translate_item(item_src, trans_id);
    }

    // Return the context, dropping the hax state and rustc `tcx`.
    let transform_options = TransformOptions {
        no_code_duplication: options.no_code_duplication,
        hide_marker_traits: options.hide_marker_traits,
        no_merge_goto_chains: options.no_merge_goto_chains,
        print_built_llbc: options.print_built_llbc,
        item_opacities: ctx.options.item_opacities,
    };

    TransformCtx {
        options: transform_options,
        translated: ctx.translated,
        errors: ctx.errors,
    }
}
