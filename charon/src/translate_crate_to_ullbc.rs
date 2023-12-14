use crate::cli_options::CliOpts;
use crate::get_mir::{extract_constants_at_top_level, MirLevel};
use crate::meta;
use crate::translate_ctx::*;
use crate::translate_functions_to_ullbc;
use crate::types as ty;
use crate::ullbc_ast as ast;
use hax_frontend_exporter as hax;
use hax_frontend_exporter::SInto;
use linked_hash_set::LinkedHashSet;
use rustc_hir::{Defaultness, ImplItem, ImplItemKind, Item, ItemKind};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use std::collections::{BTreeSet, HashMap, HashSet};

impl<'tcx, 'ctx> TransCtx<'tcx, 'ctx> {
    fn register_local_hir_impl_item(&mut self, _top_item: bool, impl_item: &ImplItem) {
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
                let _ = self.translate_global_decl_id(&None, def_id);
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
                let _ = self.translate_fun_decl_id(&None, def_id);
            }
        }
    }

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
    fn register_local_hir_item(&mut self, top_item: bool, item: &Item) {
        trace!("{:?}", item);

        // The annoying thing is that when iterating over the items in a crate, we
        // iterate over *all* the items, which is a problem with regards to the
        // *opaque* modules: we see all the definitions which are in there, and
        // not only those which are transitively reachable from the root.
        // Because of this, we need the following check: if the item is a "top"
        // item (not an item transitively reachable from an item which is not
        // opaque) and inside an opaque module (or sub-module), we ignore it.
        if top_item {
            match self.hir_item_to_name(item) {
                Option::None => {
                    // This kind of item is to be ignored
                    trace!("Ignoring {:?} (ignoring item kind)", item.item_id());
                    return;
                }
                Option::Some(item_name) => {
                    if self.crate_info.is_opaque_decl(&item_name) {
                        trace!("Ignoring {:?} (marked as opaque)", item.item_id());
                        return;
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
                // We ignore the type aliases - it seems they are inlined
            }
            ItemKind::OpaqueTy(_) => unimplemented!(),
            ItemKind::Union(..) => unimplemented!(),
            ItemKind::Enum(..) | ItemKind::Struct(_, _) => {
                let _ = self.translate_type_decl_id(&None, def_id);
            }
            ItemKind::Fn(_, _, _) => {
                let _ = self.translate_fun_decl_id(&None, def_id);
            }
            ItemKind::Trait(..) => {
                let _ = self.translate_trait_decl_id(&None, def_id);
                // We don't need to explore the associated items: we will
                // explore them when translating the trait
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
                if !trans_id.is_anon_const() {
                    if extract_constants_at_top_level(self.mir_level) {
                        let _ = self.translate_global_decl_id(&None, def_id);
                    } else {
                        // Avoid registering globals in optimized MIR (they will be inlined)
                    }
                }
            }

            ItemKind::Impl(impl_block) => {
                trace!("impl");
                // Sanity checks - TODO: remove?
                translate_functions_to_ullbc::check_impl_item(impl_block);

                // If this is a trait implementation, register it
                if self.tcx.trait_id_of_impl(def_id).is_some() {
                    let _ = self.translate_trait_impl_id(&None, def_id);
                }

                // Explore the items
                let hir_map = self.tcx.hir();
                for impl_item_ref in impl_block.items {
                    // impl_item_ref only gives the reference of the impl item:
                    // we need to look it up
                    let impl_item = hir_map.impl_item(impl_item_ref.id);

                    self.register_local_hir_impl_item(false, impl_item);
                }
            }
            ItemKind::Use(_, _) => {
                // Ignore
            }
            ItemKind::ExternCrate(_) => {
                // Ignore
            }
            ItemKind::Mod(module) => {
                trace!("module");

                // Explore the module, only if it was not marked as "opaque"
                // TODO: we may want to accumulate the set of modules we found,
                // to check that all the opaque modules given as arguments actually
                // exist
                trace!("{:?}", def_id);
                let opaque = self.id_is_opaque(def_id);
                if opaque {
                    // Ignore
                    trace!("Ignoring module [{:?}] because marked as opaque", def_id);
                } else {
                    trace!("Diving into module [{:?}]", def_id);
                    let hir_map = self.tcx.hir();
                    for item_id in module.item_ids {
                        // Lookup and register the item
                        let item = hir_map.item(*item_id);
                        self.register_local_hir_item(false, item);
                    }
                }
            }
            ItemKind::Macro(..) => {
                // We ignore macro definitions. Note that when a macro is applied,
                // we directly see the result of its expansion by the Rustc compiler,
                // which is why we don't have to care about them.
            }
            _ => {
                unimplemented!("{:?}", item.kind);
            }
        }
    }
}

/// Translate all the declarations in the crate.
pub fn translate<'tcx, 'ctx>(
    crate_info: CrateInfo,
    options: &CliOpts,
    session: &'ctx Session,
    tcx: TyCtxt<'tcx>,
    mir_level: MirLevel,
) -> TransCtx<'tcx, 'ctx> {
    let hax_state = hax::state::State::new(
        tcx,
        hax::options::Options {
            inline_macro_calls: Vec::new(),
        },
    );
    let mut ctx = TransCtx {
        session,
        tcx,
        hax_state,
        mir_level,
        crate_info,
        continue_on_failure: !options.abort_on_error,
        errors_as_warnings: options.errors_as_warnings,
        error_count: 0,
        no_code_duplication: options.no_code_duplication,
        all_ids: LinkedHashSet::new(),
        stack: BTreeSet::new(),
        def_id: None,
        file_to_id: HashMap::new(),
        id_to_file: HashMap::new(),
        real_file_counter: meta::LocalFileId::Generator::new(),
        virtual_file_counter: meta::VirtualFileId::Generator::new(),
        dep_sources: HashMap::new(),
        decls_with_errors: HashSet::new(),
        ignored_failed_decls: HashSet::new(),
        type_id_map: ty::TypeDeclId::MapGenerator::new(),
        type_decls: ty::TypeDeclId::Map::new(),
        fun_id_map: ast::FunDeclId::MapGenerator::new(),
        fun_decls: ast::FunDeclId::Map::new(),
        global_id_map: ast::GlobalDeclId::MapGenerator::new(),
        global_decls: ast::GlobalDeclId::Map::new(),
        trait_decl_id_map: ast::TraitDeclId::MapGenerator::new(),
        trait_decls: ast::TraitDeclId::Map::new(),
        trait_impl_id_map: ast::TraitImplId::MapGenerator::new(),
        trait_impl_id_to_def_id: HashMap::new(),
        trait_impls: ast::TraitImplId::Map::new(),
        ordered_decls: None,
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
        ctx.register_local_hir_item(true, item);
    }

    trace!("Stack after we explored the crate:\n{:?}", &ctx.stack);

    // Translate.
    //
    // For as long as the stack of items to translate is not empty, we pop the top item
    // and translate it. Note that we transitively translate items: if an item refers to
    // non-translated (potentially external) items, we add them to the stack.
    //
    // Note that the order in which we translate the definitions doesn't matter:
    // we never need to lookup a translated definition, and only use the map
    // from Rust ids to translated ids.
    while let Some(id) = ctx.stack.pop_first() {
        trace!("About to translate id: {:?}", id);
        match id {
            OrdRustId::Type(id) => ctx.translate_type(id),
            OrdRustId::Fun(id) | OrdRustId::ConstFun(id) => ctx.translate_function(id),
            OrdRustId::Global(id) => ctx.translate_global(id),
            OrdRustId::TraitDecl(id) => ctx.translate_trait_decl(id),
            OrdRustId::TraitImpl(id) => ctx.translate_trait_impl(id),
        }
    }

    // Return the context
    ctx
}
