use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::options::{CliOpts, TranslateOptions};
use charon_lib::transform::TransformCtx;
use hax::FullDefKind;
use hax_frontend_exporter::{self as hax, SInto};
use itertools::Itertools;
use rustc_middle::ty::TyCtxt;
use std::cell::RefCell;
use std::path::PathBuf;

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

            Trait { .. } => {
                let _ = self.register_trait_decl_id(&None, def_id);
            }
            Impl { of_trait: true } => {
                let _ = self.register_trait_impl_id(&None, def_id);
            }
            // TODO: trait aliases (https://github.com/AeneasVerif/charon/issues/366)
            TraitAlias { .. } => {}

            Impl { of_trait: false } | Mod { .. } | ForeignMod { .. } => {
                let Ok(def) = self.hax_def(def_id) else {
                    return; // Error has already been emitted
                };
                let Ok(name) = self.def_id_to_name(&def.def_id) else {
                    return; // Error has already been emitted
                };
                let opacity = self.opacity_for_name(&name);
                let trans_src = TransItemSource::TraitImpl(def.def_id.clone());
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
