use super::translate_ctx::*;
use charon_lib::ast::*;
use charon_lib::options::{CliOpts, TranslateOptions};
use charon_lib::transform::TransformCtx;
use hax::FullDefKind;
use hax_frontend_exporter::{self as hax, SInto};
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
            Enum { .. }
            | Struct { .. }
            | Union { .. }
            | TyAlias { .. }
            | AssocTy { .. }
            | ForeignTy => {
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
                self.items_to_translate
                    .insert(TransItemSource::Module(def_id.to_rust_def_id()));
            }

            // We skip these
            ExternCrate { .. } | GlobalAsm { .. } | Macro { .. } | Use { .. } => {}
            // We cannot encounter these since they're not top-level items.
            AnonConst { .. }
            | Closure { .. }
            | ConstParam { .. }
            | Ctor { .. }
            | Field { .. }
            | InlineConst { .. }
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
                for def_id in items {
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

    pub(crate) fn translate_item(&mut self, item_src: TransItemSource) {
        let trans_id = self.id_map.get(&item_src).copied();
        let rust_id = item_src.to_def_id();
        self.with_def_id(rust_id, trans_id, |mut ctx| {
            let span = ctx.def_span(rust_id);
            // Catch cycles
            let res = {
                // Stopgap measure because there are still many panics in charon and hax.
                let mut ctx = std::panic::AssertUnwindSafe(&mut ctx);
                std::panic::catch_unwind(move || ctx.translate_item_aux(item_src, trans_id))
            };
            match res {
                Ok(Ok(())) => return,
                // Translation error
                Ok(Err(_)) => {
                    register_error!(ctx, span, "Item `{rust_id:?}` caused errors; ignoring.")
                }
                // Panic
                Err(_) => register_error!(
                    ctx,
                    span,
                    "Thread panicked when extracting item `{rust_id:?}`."
                ),
            };
        })
    }

    pub(crate) fn translate_item_aux(
        &mut self,
        item_src: TransItemSource,
        trans_id: Option<AnyTransId>,
    ) -> Result<(), Error> {
        let rust_id = item_src.to_def_id();
        // Translate the meta information
        let name = self.def_id_to_name(rust_id)?;
        if let Some(trans_id) = trans_id {
            self.translated.item_names.insert(trans_id, name.clone());
        }
        let opacity = self.opacity_for_name(&name);
        if opacity.is_invisible() {
            // Don't even start translating the item. In particular don't call `hax_def` on it.
            return Ok(());
        }
        let def = self.hax_def(rust_id)?;
        let item_meta = self.translate_item_meta(&def, name, opacity);

        // Initialize the body translation context
        let bt_ctx = BodyTransCtx::new(rust_id, trans_id, self);
        match item_src {
            TransItemSource::Type(_) => {
                let id = trans_id.unwrap().as_type().copied().unwrap();
                let ty = bt_ctx.translate_type(id, item_meta, &def)?;
                self.translated.type_decls.set_slot(id, ty);
            }
            TransItemSource::Fun(_) => {
                let id = trans_id.unwrap().as_fun().copied().unwrap();
                let fun_decl = bt_ctx.translate_function(id, item_meta, &def)?;
                self.translated.fun_decls.set_slot(id, fun_decl);
            }
            TransItemSource::Global(_) => {
                let id = trans_id.unwrap().as_global().copied().unwrap();
                let global_decl = bt_ctx.translate_global(id, item_meta, &def)?;
                self.translated.global_decls.set_slot(id, global_decl);
            }
            TransItemSource::TraitDecl(_) => {
                let id = trans_id.unwrap().as_trait_decl().copied().unwrap();
                let trait_decl = bt_ctx.translate_trait_decl(id, item_meta, &def)?;
                self.translated.trait_decls.set_slot(id, trait_decl);
            }
            TransItemSource::TraitImpl(_) => {
                let id = trans_id.unwrap().as_trait_impl().copied().unwrap();
                let trait_impl = bt_ctx.translate_trait_impl(id, item_meta, &def)?;
                self.translated.trait_impls.set_slot(id, trait_impl);
            }
            TransItemSource::Module(_) => self.register_module(item_meta, &def)?,
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
            inline_macro_calls: Vec::new(),
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

    // Translate the crate root, which will recursively explore modules and items in the crate
    // while respecting opacity annotations/options.
    ctx.items_to_translate
        .insert(TransItemSource::Module(crate_def_id.to_rust_def_id()));

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
        if ctx.processed.insert(item_src) {
            ctx.translate_item(item_src);
        }
    }

    // Return the context, dropping the hax state and rustc `tcx`.
    TransformCtx {
        options: ctx.options,
        translated: ctx.translated,
        errors: ctx.errors,
    }
}
