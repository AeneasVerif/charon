use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::options::CliOpts;
use charon_lib::transform::ctx::TransformOptions;
use charon_lib::transform::TransformCtx;
use hax_frontend_exporter as hax;
use rustc_hir::def_id::DefId;
use rustc_hir::{ForeignItemKind, ItemId, ItemKind};
use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    /// Register a HIR item and all its children. We call this on the crate root items and end up
    /// exploring the whole crate.
    fn register_local_hir_item(&mut self, item_id: ItemId) {
        let mut ctx_ref = std::panic::AssertUnwindSafe(&mut *self);
        // Catch panics that could happen during registration.
        let res = std::panic::catch_unwind(move || ctx_ref.register_local_hir_item_inner(item_id));
        if res.is_err() {
            let hir_map = self.tcx.hir();
            let item = hir_map.item(item_id);
            let def_id = item.owner_id.to_def_id();
            let span = self.tcx.def_span(def_id);
            self.errors
                .span_err_no_register(span, &format!("panicked while registering `{def_id:?}`"));
            self.errors.error_count += 1;
        }
    }

    fn register_local_hir_item_inner(&mut self, item_id: ItemId) {
        let hir_map = self.tcx.hir();
        let item = hir_map.item(item_id);
        let def_id = item.owner_id.to_def_id();
        let name = self
            .def_id_to_name(def_id)
            .expect("could not translate name");
        trace!("Registering {:?}", def_id);

        // Case disjunction on the item kind.
        match &item.kind {
            ItemKind::Enum(..)
            | ItemKind::Struct(..)
            | ItemKind::Union(..)
            | ItemKind::TyAlias(..) => {
                let _ = self.register_type_decl_id(&None, def_id);
            }
            ItemKind::Fn(..) => {
                let _ = self.register_fun_decl_id(&None, def_id);
            }
            ItemKind::Trait(..) => {
                let _ = self.register_trait_decl_id(&None, def_id);
            }
            ItemKind::Const(..) | ItemKind::Static(..) => {
                let _ = self.register_global_decl_id(&None, def_id);
            }
            ItemKind::Impl(..) => {
                trace!("impl");
                let def = self
                    .hax_def(def_id)
                    .expect("hax failed when registering impl block");
                let hax::FullDefKind::Impl {
                    items,
                    impl_subject,
                    ..
                } = &def.kind
                else {
                    unreachable!()
                };

                match impl_subject {
                    hax::ImplSubject::Trait { .. } => {
                        let _ = self.register_trait_impl_id(&None, def_id);
                    }
                    hax::ImplSubject::Inherent { .. } => {
                        // Register the items
                        for (item, item_def) in items {
                            let def_id = item_def.rust_def_id();
                            // Match on the impl item kind
                            match &item.kind {
                                // Associated constant:
                                // ```
                                // impl Bar {
                                //   const C = 32;
                                // }
                                // ```
                                hax::AssocKind::Const => {
                                    let _ = self.register_global_decl_id(&None, def_id);
                                }
                                // Associated type:
                                // ```
                                // impl Bar {
                                //   type T = bool;
                                // }
                                // ```
                                hax::AssocKind::Type => {
                                    let _ = self.register_type_decl_id(&None, def_id);
                                }
                                // Inherent method
                                // ```
                                // impl Bar {
                                //   fn is_foo() -> bool { false }
                                // }
                                // ```
                                hax::AssocKind::Fn => {
                                    let _ = self.register_fun_decl_id(&None, def_id);
                                }
                            }
                        }
                    }
                }
            }
            ItemKind::Mod(module) => {
                trace!("module");

                // Explore the module, only if it was not marked as "opaque"
                // TODO: we may want to accumulate the set of modules we found,
                // to check that all the opaque modules given as arguments actually
                // exist
                trace!("{:?}", def_id);
                let def = self
                    .hax_def(def_id)
                    .expect("hax failed when registering module");
                let opacity = self.opacity_for_name(&name);
                // Go through `item_meta` to get take into account the `charon::opaque` attribute.
                let item_meta = self.translate_item_meta(&def, name, opacity);
                if item_meta.opacity.is_opaque() || opacity.is_invisible() {
                    // Ignore
                    trace!(
                        "Ignoring module [{:?}] \
                        because it is marked as opaque",
                        def_id
                    );
                } else {
                    trace!("Diving into module [{:?}]", def_id);
                    // Lookup and register the items
                    for item_id in module.item_ids {
                        self.register_local_hir_item(*item_id);
                    }
                }
            }
            ItemKind::ForeignMod { items, .. } => {
                trace!("Diving into `extern` block [{:?}]", def_id);
                for item in *items {
                    // Lookup and register the item
                    let item = hir_map.foreign_item(item.id);
                    let def_id = item.owner_id.to_def_id();
                    match item.kind {
                        ForeignItemKind::Fn(..) => {
                            let _ = self.register_fun_decl_id(&None, def_id);
                        }
                        ForeignItemKind::Static(..) => {
                            let _ = self.register_global_decl_id(&None, def_id);
                        }
                        ForeignItemKind::Type => {
                            let _ = self.register_type_decl_id(&None, def_id);
                        }
                    }
                }
            }
            // TODO: trait aliases (https://github.com/AeneasVerif/charon/issues/366)
            ItemKind::TraitAlias(..) => {}
            // Macros are already expanded.
            ItemKind::Macro(..) => {}
            ItemKind::ExternCrate(..) | ItemKind::GlobalAsm(..) | ItemKind::Use(..) => {}
        }
    }

    pub(crate) fn translate_item(&mut self, rust_id: DefId, trans_id: AnyTransId) {
        if self.errors.ignored_failed_decls.contains(&trans_id)
            || self.translated.get_item(trans_id).is_some()
        {
            return;
        }
        self.with_def_id(rust_id, trans_id, |mut ctx| {
            let span = ctx.def_span(rust_id);
            // Catch cycles
            let res = if ctx.translate_stack.contains(&trans_id) {
                ctx.span_err(
                    span,
                    &format!(
                        "Cycle detected while translating {rust_id:?}! Stack: {:?}",
                        &ctx.translate_stack
                    ),
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
                        register_error_or_panic!(
                            ctx,
                            span,
                            format!("Thread panicked when extracting item `{rust_id:?}`.")
                        );
                        Err(())
                    }
                };
                // let res = ctx.translate_item_aux(rust_id, trans_id);
                ctx.translate_stack.pop();
                res
            };

            if res.is_err() {
                ctx.span_err(
                    span,
                    &format!("Ignoring the following item due to a previous error: {rust_id:?}"),
                );
                ctx.errors.ignore_failed_decl(trans_id);
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
        let rust_id = *self.reverse_id_map.get(&id).unwrap();
        // Translate if not already translated.
        self.translate_item(rust_id, id);

        if self.errors.ignored_failed_decls.contains(&id) {
            let span = self.def_span(rust_id);
            error_or_panic!(self, span, format!("Failed to translate item {id:?}."))
        }
        Ok(self.translated.get_item(id).unwrap())
    }
}

#[tracing::instrument(skip(tcx))]
pub fn translate<'tcx, 'ctx>(
    options: &CliOpts,
    tcx: TyCtxt<'tcx>,
    sysroot: PathBuf,
) -> TransformCtx<'tcx> {
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

    let mut error_ctx = ErrorCtx {
        continue_on_failure: !options.abort_on_error,
        error_on_warnings: options.error_on_warnings,
        dcx: tcx.dcx(),
        external_decls_with_errors: HashSet::new(),
        ignored_failed_decls: HashSet::new(),
        external_dep_sources: HashMap::new(),
        def_id: None,
        def_id_is_local: false,
        error_count: 0,
    };
    let translate_options = TranslateOptions::new(&mut error_ctx, options);
    let mut ctx = TranslateCtx {
        tcx,
        sysroot,
        hax_state,
        options: translate_options,
        errors: error_ctx,
        translated: TranslatedCrate {
            crate_name: requested_crate_name,
            real_crate_name,
            ..TranslatedCrate::default()
        },
        id_map: Default::default(),
        reverse_id_map: Default::default(),
        priority_queue: Default::default(),
        translate_stack: Default::default(),
        cached_path_elems: Default::default(),
        cached_names: Default::default(),
    };

    // Recursively register all the items in the crate, starting from the root module. We could
    // instead ask rustc for the plain list of all items in the crate, but we wouldn't be able to
    // skip items inside modules annotated with `#[charon::opaque]`.
    let hir = tcx.hir();
    for item_id in hir.root_module().item_ids {
        ctx.register_local_hir_item(*item_id);
    }

    trace!(
        "Queue after we explored the crate:\n{:?}",
        &ctx.priority_queue
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
    while let Some((ord_id, trans_id)) = ctx.priority_queue.pop_first() {
        trace!("About to translate id: {:?}", ord_id);
        ctx.translate_item(ord_id.get_id(), trans_id);
    }

    // Return the context, dropping the hax state and rustc `tcx`.
    let transform_options = TransformOptions {
        no_code_duplication: options.no_code_duplication,
        hide_marker_traits: options.hide_marker_traits,
        no_merge_goto_chains: options.no_merge_goto_chains,
        item_opacities: ctx.options.item_opacities,
    };

    TransformCtx {
        options: transform_options,
        translated: ctx.translated,
        errors: ctx.errors,
    }
}
