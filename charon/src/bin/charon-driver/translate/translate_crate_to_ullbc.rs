use super::get_mir::extract_constants_at_top_level;
use super::translate_ctx::*;
use charon_lib::ast::krate::*;
use charon_lib::common::*;
use charon_lib::options::CliOpts;
use charon_lib::transform::ctx::TransformOptions;
use charon_lib::transform::TransformCtx;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;
use rustc_hir::{ForeignItemKind, ItemId, ItemKind};
use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

impl<'tcx, 'ctx> TranslateCtx<'tcx, 'ctx> {
    /// General function to register a MIR item. It is called on all the top-level
    /// items. This includes: crate inclusions and `use` instructions (which are
    /// ignored), but also type and functions declarations.
    /// Note that this function checks if the item has been registered, and adds
    /// its def_id to the list of registered items otherwise.
    ///
    /// `stack`: the stack of definitions we explored before reaching this one.
    /// This is useful for debugging purposes, to check how we reached a point
    /// (in particular if we want to figure out where we failed to consider a
    /// definition as opaque).
    fn register_local_hir_item(&mut self, top_item: bool, item_id: ItemId) -> Result<(), Error> {
        let hir_map = self.tcx.hir();
        let item = hir_map.item(item_id);
        trace!("{:?}", item);

        // The annoying thing is that when iterating over the items in a crate, we
        // iterate over *all* the items, which is a problem with regards to the
        // *opaque* modules: we see all the definitions which are in there, and
        // not only those which are transitively reachable from the root.
        // Because of this, we need the following check: if the item is a "top"
        // item (not an item transitively reachable from an item which is not
        // opaque) and inside an opaque module (or sub-module), we ignore it.
        if top_item {
            let def_id = item.owner_id.to_def_id();
            match &item.kind {
                ItemKind::ExternCrate(..) | ItemKind::Use(..) => {
                    // This kind of item is to be ignored
                    trace!("Ignoring {:?} (ignoring item kind)", item.item_id());
                    return Ok(());
                }
                ItemKind::OpaqueTy(..)
                | ItemKind::Union(..)
                | ItemKind::TyAlias(..)
                | ItemKind::Enum(..)
                | ItemKind::Struct(..)
                | ItemKind::Fn(..)
                | ItemKind::Impl(..)
                | ItemKind::Mod(..)
                | ItemKind::ForeignMod { .. }
                | ItemKind::Const(..)
                | ItemKind::Static(..)
                | ItemKind::Macro(..)
                | ItemKind::Trait(..) => {
                    let name = self.def_id_to_name(def_id)?;
                    if self.opacity_for_name(&name).is_opaque() {
                        trace!("Ignoring {:?} (marked as opaque)", item.item_id());
                        return Ok(());
                    }
                    // Continue
                }
                _ => {
                    unimplemented!("{:?}", item.kind);
                }
            }
        }
        trace!("Registering {:?}", item.item_id());

        // Case disjunction on the item kind.
        let def_id = item.owner_id.to_def_id();
        match &item.kind {
            ItemKind::TyAlias(_, _) => {
                let _ = self.register_type_decl_id(&None, def_id);
                Ok(())
            }
            ItemKind::OpaqueTy(_) => unimplemented!(),
            ItemKind::Enum(..) | ItemKind::Struct(_, _) | ItemKind::Union(..) => {
                let _ = self.register_type_decl_id(&None, def_id);
                Ok(())
            }
            ItemKind::Fn(_, _, _) => {
                let _ = self.register_fun_decl_id(&None, def_id);
                Ok(())
            }
            ItemKind::Trait(..) => {
                let _ = self.register_trait_decl_id(&None, def_id);
                // We don't need to explore the associated items: we will
                // explore them when translating the trait
                Ok(())
            }
            ItemKind::Const(..) | ItemKind::Static(..) => {
                // We ignore the anonymous constants, which are introduced
                // by the Rust compiler: those constants will be inlined in the
                // function bodies.
                //
                // Important: if we try to retrieve the MIR of anonymous constants,
                // it will steal the MIR of the bodies of the functions in which
                // they appear.
                //
                // Also note that this is the only place where we need to check
                // if an item is an anonymous constant: when translating the bodies,
                // as the anonymous constants are inlined in those bodies, they
                // disappear completely.
                let trans_id: hax::DefId = def_id.sinto(&self.hax_state);
                if trans_id.path.last().unwrap().data != hax::DefPathItem::AnonConst {
                    if extract_constants_at_top_level(self.options.mir_level) {
                        let _ = self.register_global_decl_id(&None, def_id);
                    } else {
                        // Avoid registering globals in optimized MIR (they will be inlined)
                    }
                }
                Ok(())
            }

            ItemKind::Impl(..) => {
                trace!("impl");
                let def = self.hax_def(def_id);
                let hax::FullDefKind::Impl {
                    items,
                    impl_subject,
                    ..
                } = &def.kind
                else {
                    unreachable!()
                };

                // If this is a trait implementation, register it
                if let hax::ImplSubject::Trait(..) = impl_subject {
                    let _ = self.register_trait_impl_id(&None, def_id);
                }

                // Explore the items
                for item in items {
                    let def_id = (&item.def_id).into();
                    // Match on the impl item kind
                    match &item.kind {
                        hax::AssocKind::Const => {
                            // Associated constant:
                            // ```
                            // trait Foo {
                            //   const C : usize;
                            // }
                            // impl Foo for Bar {
                            //   const C = 32; // HERE
                            // }
                            // // or
                            // impl Bar {
                            //   const C = 32; // HERE
                            // }
                            // ```
                            let _ = self.register_global_decl_id(&None, def_id);
                        }
                        hax::AssocKind::Type => {
                            // Associated type:
                            // ```
                            // trait Foo {
                            //   type T;
                            // }
                            // impl Foo for Bar {
                            //   type T = bool; // HERE
                            // }
                            // // or
                            // impl Bar {
                            //   type T = bool; // HERE
                            // }
                            // ```
                            //
                            // Only handle inherent associated types. Associated types in trait
                            // impls will be processed when translating the impl.
                            if let hax::ImplSubject::Inherent(_) = impl_subject {
                                let _ = self.register_type_decl_id(&None, def_id);
                            }
                        }
                        hax::AssocKind::Fn => {
                            // Trait method implementation or inherent method.
                            let _ = self.register_fun_decl_id(&None, def_id);
                        }
                    }
                }
                Ok(())
            }
            ItemKind::Use(_, _) => {
                // Ignore
                Ok(())
            }
            ItemKind::ExternCrate(_) => {
                // Ignore
                Ok(())
            }
            ItemKind::Mod(module) => {
                trace!("module");

                // Explore the module, only if it was not marked as "opaque"
                // TODO: we may want to accumulate the set of modules we found,
                // to check that all the opaque modules given as arguments actually
                // exist
                trace!("{:?}", def_id);
                let def = self.hax_def(def_id);
                let name = self.def_id_to_name(def_id)?;
                let opacity = self.opacity_for_name(&name);
                // Go through `item_meta` to get take into account the `charon::opaque` attribute.
                let item_meta = self.translate_item_meta(&def, name, opacity)?;
                if item_meta.opacity.is_opaque() || opacity.is_invisible() {
                    // Ignore
                    trace!("Ignoring module [{:?}] because marked as opaque", def_id);
                } else {
                    trace!("Diving into module [{:?}]", def_id);
                    for item_id in module.item_ids {
                        // Lookup and register the item
                        self.register_local_hir_item(false, *item_id)?;
                    }
                }
                Ok(())
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
                Ok(())
            }
            ItemKind::Macro(..) => {
                // We ignore macro definitions. Note that when a macro is applied,
                // we directly see the result of its expansion by the Rustc compiler,
                // which is why we don't have to care about them.
                Ok(())
            }
            _ => {
                unimplemented!("{:?}", item.kind);
            }
        }
    }

    pub(crate) fn translate_item(&mut self, rust_id: DefId, trans_id: AnyTransId) {
        if self.errors.ignored_failed_decls.contains(&rust_id)
            || self.translated.get_item(trans_id).is_some()
        {
            return;
        }
        self.with_def_id(rust_id, |mut ctx| {
            let span = ctx.tcx.def_span(rust_id);
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
                    &format!("Ignoring the following item due to an error: {rust_id:?}"),
                );
                ctx.errors.ignore_failed_decl(rust_id);
            }
        })
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        rust_id: DefId,
        trans_id: AnyTransId,
    ) -> Result<(), Error> {
        let name = self.def_id_to_name(rust_id)?;
        self.translated.item_names.insert(trans_id, name.clone());
        let opacity = self.opacity_for_name(&name);
        if opacity.is_invisible() {
            // Don't even start translating the item. In particular don't call `hax_def` on it.
            return Ok(());
        }
        // Translate the meta information
        let def: Arc<hax::FullDef> = self.hax_def(rust_id);
        let item_meta = self.translate_item_meta(&def, name, opacity)?;
        match trans_id {
            AnyTransId::Type(id) => {
                let ty = self.translate_type(id, rust_id, item_meta, &def)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            AnyTransId::Fun(id) => {
                let fun_decl = self.translate_function(id, rust_id, item_meta, &def)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            AnyTransId::Global(id) => {
                let global_decl = self.translate_global(id, rust_id, item_meta, &def)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            AnyTransId::TraitDecl(id) => {
                let trait_decl = self.translate_trait_decl(id, rust_id, item_meta, &def)?;
                self.translated.trait_decls.set_slot(id, trait_decl);
            }
            AnyTransId::TraitImpl(id) => {
                let trait_impl = self.translate_trait_impl(id, rust_id, item_meta, &def)?;
                self.translated.trait_impls.set_slot(id, trait_impl);
            }
        }
        Ok(())
    }

    /// While translating an item you may need the contents of another. Use this to retreive the
    /// translated version of this item.
    #[allow(dead_code)]
    pub(crate) fn get_or_translate(&mut self, id: AnyTransId) -> Result<AnyTransItem<'_>, Error> {
        let rust_id = *self.translated.reverse_id_map.get(&id).unwrap();
        // Translate if not already translated.
        self.translate_item(rust_id, id);

        if self.errors.ignored_failed_decls.contains(&rust_id) {
            let span = self.tcx.def_span(rust_id);
            error_or_panic!(self, span, format!("Failed to translate item {id:?}."))
        }
        Ok(self.translated.get_item(id).unwrap())
    }
}

#[tracing::instrument(skip(tcx))]
pub fn translate<'tcx, 'ctx>(options: &CliOpts, tcx: TyCtxt<'tcx>) -> TransformCtx<'tcx> {
    let hax_state = hax::state::State::new(
        tcx,
        hax::options::Options {
            inline_macro_calls: Vec::new(),
            // downgrade_errors: options.errors_as_warnings,
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
        errors_as_warnings: options.errors_as_warnings,
        dcx: tcx.dcx(),
        decls_with_errors: HashSet::new(),
        ignored_failed_decls: HashSet::new(),
        dep_sources: HashMap::new(),
        def_id: None,
        error_count: 0,
    };
    let translate_options = TranslateOptions::new(&mut error_ctx, options);
    let mut ctx = TranslateCtx {
        tcx,
        hax_state,
        options: translate_options,
        errors: error_ctx,
        translated: TranslatedCrate {
            crate_name: requested_crate_name,
            real_crate_name,
            ..TranslatedCrate::default()
        },
        priority_queue: Default::default(),
        translate_stack: Default::default(),
        cached_defs: Default::default(),
        cached_path_elems: Default::default(),
        cached_names: Default::default(),
    };

    // First push all the items in the stack of items to translate.
    //
    // We explore the crate by starting with the root module.
    //
    // Remark: It is important to do like this (and not iterate over all the items)
    // if we want the "opaque" options (to ignore parts of the crate) to work.
    // For instance, if we mark "foo::bar" as opaque, we will ignore the module
    // "foo::bar" altogether (we will not even look at the items).
    // If we look at the items, we risk registering items just by looking
    // at their name. For instance, if we check the item `foo::bar::{foo::bar::Ty}::f`,
    // then by converting the Rust name to an LLBC name, we will actually register
    // the name "foo::bar::Ty" (so that we can generate the "impl" path element
    // `{foo::bar::Ty}`), which means we will register the item `foo::bar::Ty`.
    // We could make the name translation work differently if we do have to
    // explore all the items in the crate.
    let hir = tcx.hir();
    for item_id in hir.root_module().item_ids {
        let mut ctx = std::panic::AssertUnwindSafe(&mut ctx);
        // Stopgap measure because there are still many panics in charon and hax.
        // If registration fails we simply skip the item.
        let _ = std::panic::catch_unwind(move || ctx.register_local_hir_item(true, *item_id));
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

    let transform_options = TransformOptions {
        no_code_duplication: options.no_code_duplication,
        hide_marker_traits: options.hide_marker_traits,
        no_merge_goto_chains: options.no_merge_goto_chains,
        item_opacities: ctx.options.item_opacities,
    };
    // Return the context, dropping the hax state and rustc `tcx`.
    TransformCtx {
        options: transform_options,
        translated: ctx.translated,
        errors: ctx.errors,
    }
}
