use crate::cli_options::CliOpts;
use crate::common::*;
use crate::get_mir::{extract_constants_at_top_level, MirLevel};
use crate::transform::TransformCtx;
use crate::translate_ctx::*;

use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use rustc_hir::def_id::DefId;
use rustc_hir::{ForeignItemKind, ImplItemKind, Item, ItemKind};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::collections::{HashMap, HashSet};

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
    fn register_local_hir_item(&mut self, top_item: bool, item: &Item) -> Result<(), Error> {
        trace!("{:?}", item);

        // The annoying thing is that when iterating over the items in a crate, we
        // iterate over *all* the items, which is a problem with regards to the
        // *opaque* modules: we see all the definitions which are in there, and
        // not only those which are transitively reachable from the root.
        // Because of this, we need the following check: if the item is a "top"
        // item (not an item transitively reachable from an item which is not
        // opaque) and inside an opaque module (or sub-module), we ignore it.
        if top_item {
            match self.hir_item_to_name(item)? {
                None => {
                    // This kind of item is to be ignored
                    trace!("Ignoring {:?} (ignoring item kind)", item.item_id());
                    return Ok(());
                }
                Some(item_name) => {
                    if self.is_opaque_name(&item_name) {
                        trace!("Ignoring {:?} (marked as opaque)", item.item_id());
                        return Ok(());
                    }
                    // Continue
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
            ItemKind::Union(..) => unimplemented!(),
            ItemKind::Enum(..) | ItemKind::Struct(_, _) => {
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

            ItemKind::Impl(impl_block) => {
                trace!("impl");
                // Sanity checks
                // TODO: make proper error messages
                use rustc_hir::{Defaultness, ImplPolarity, Unsafety};
                assert!(impl_block.unsafety == Unsafety::Normal);
                // About polarity:
                // [https://doc.rust-lang.org/beta/unstable-book/language-features/negative-impls.html]
                // Not sure about what I should do about it. Should I do anything, actually?
                // This seems useful to enforce some discipline on the user-side, but not
                // necessary for analysis purposes.
                assert!(impl_block.polarity == ImplPolarity::Positive);
                // Not sure what this is about
                assert!(impl_block.defaultness == Defaultness::Final);

                // If this is a trait implementation, register it
                if self.tcx.trait_id_of_impl(def_id).is_some() {
                    let _ = self.register_trait_impl_id(&None, def_id);
                }

                // Explore the items
                let hir_map = self.tcx.hir();
                for impl_item_ref in impl_block.items {
                    // impl_item_ref only gives the reference of the impl item:
                    // we need to look it up
                    let impl_item = hir_map.impl_item(impl_item_ref.id);

                    // TODO: make a proper error message
                    assert!(impl_item.defaultness == Defaultness::Final);

                    let def_id = impl_item.owner_id.to_def_id();

                    // Match on the impl item kind
                    match &impl_item.kind {
                        ImplItemKind::Const(_, _) => {
                            // Can happen in traits:
                            // ```
                            // trait Foo {
                            //   const C : usize;
                            // }
                            //
                            // impl Foo for Bar {
                            //   const C = 32; // HERE
                            // }
                            // ```
                            let _ = self.register_global_decl_id(&None, def_id);
                        }
                        ImplItemKind::Type(_) => {
                            // Trait type:
                            // ```
                            // trait Foo {
                            //   type T;
                            // }
                            //
                            // impl Foo for Bar {
                            //   type T = bool; // HERE
                            // }
                            // ```
                            //
                            // Do nothing for now: we won't generate a top-level definition
                            // for this, and handle it when translating the trait implementation
                            // this item belongs to.
                            let tcx = self.tcx;
                            assert!(tcx.associated_item(def_id).trait_item_def_id.is_some());
                        }
                        ImplItemKind::Fn(_, _) => {
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
                let opaque = self.id_is_opaque(def_id)?;
                if opaque {
                    // Ignore
                    trace!("Ignoring module [{:?}] because marked as opaque", def_id);
                } else {
                    trace!("Diving into module [{:?}]", def_id);
                    let hir_map = self.tcx.hir();
                    for item_id in module.item_ids {
                        // Lookup and register the item
                        let item = hir_map.item(*item_id);
                        self.register_local_hir_item(false, item)?;
                    }
                }
                Ok(())
            }
            ItemKind::ForeignMod { items, .. } => {
                trace!("Diving into `extern` block [{:?}]", def_id);
                let hir_map = self.tcx.hir();
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
        if self.errors.ignored_failed_decls.contains(&rust_id) || self.get_item(trans_id).is_some()
        {
            return;
        }
        self.with_def_id(rust_id, |ctx| {
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
                let res = ctx.translate_item_aux(rust_id, trans_id);
                ctx.translate_stack.pop();
                res.map_err(|_| ())
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
        match trans_id {
            AnyTransId::Type(id) => {
                let ty = self.translate_type(id, rust_id)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            AnyTransId::Fun(id) => {
                let fun_decl = self.translate_function(id, rust_id)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            AnyTransId::Global(id) => {
                let global_decl = self.translate_global(id, rust_id)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            AnyTransId::TraitDecl(id) => {
                let trait_decl = self.translate_trait_decl(id, rust_id)?;
                self.translated.trait_decls.set_slot(id, trait_decl);
            }
            AnyTransId::TraitImpl(id) => {
                let trait_impl = self.translate_trait_impl(id, rust_id)?;
                self.translated.trait_impls.set_slot(id, trait_impl);
            }
        }
        Ok(())
    }

    fn get_item(&mut self, trans_id: AnyTransId) -> Option<AnyTransItem<'_>> {
        match trans_id {
            AnyTransId::Type(id) => self.translated.type_decls.get(id).map(AnyTransItem::Type),
            AnyTransId::Fun(id) => self.translated.fun_decls.get(id).map(AnyTransItem::Fun),
            AnyTransId::Global(id) => self
                .translated
                .global_decls
                .get(id)
                .map(AnyTransItem::Global),
            AnyTransId::TraitDecl(id) => self
                .translated
                .trait_decls
                .get(id)
                .map(AnyTransItem::TraitDecl),
            AnyTransId::TraitImpl(id) => self
                .translated
                .trait_impls
                .get(id)
                .map(AnyTransItem::TraitImpl),
        }
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
        Ok(self.get_item(id).unwrap())
    }
}

/// Translate all the declarations in the crate.
pub fn translate<'tcx, 'ctx>(
    crate_name: String,
    options: &CliOpts,
    session: &'ctx Session,
    tcx: TyCtxt<'tcx>,
    mir_level: MirLevel,
) -> Result<TransformCtx<'ctx>, Error> {
    let hax_state = hax::state::State::new(
        tcx,
        hax::options::Options {
            inline_macro_calls: Vec::new(),
        },
    );
    let mut ctx = TranslateCtx {
        tcx,
        hax_state,
        options: TransOptions {
            mir_level,
            no_code_duplication: options.no_code_duplication,
            extract_opaque_bodies: options.extract_opaque_bodies,
            opaque_mods: HashSet::from_iter(options.opaque_modules.iter().cloned()),
        },
        errors: ErrorCtx {
            continue_on_failure: !options.abort_on_error,
            errors_as_warnings: options.errors_as_warnings,
            session,
            decls_with_errors: HashSet::new(),
            ignored_failed_decls: HashSet::new(),
            dep_sources: HashMap::new(),
            def_id: None,
            error_count: 0,
        },
        translated: TranslatedCrate {
            crate_name,
            ..TranslatedCrate::default()
        },
        priority_queue: Default::default(),
        translate_stack: Default::default(),
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
        let item_id = item_id.hir_id();
        let node = hir.find(item_id).unwrap();
        let item = match node {
            rustc_hir::Node::Item(item) => item,
            _ => unreachable!(),
        };
        ctx.register_local_hir_item(true, item)?;
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
    let ctx = TransformCtx {
        options: ctx.options,
        translated: ctx.translated,
        errors: ctx.errors,
    };
    Ok(ctx)
}
