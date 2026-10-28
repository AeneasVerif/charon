//! Evaluating constants with rustc's const-eval. This is the one place that knows how to get the
//! value of each kind of constant.
use crate::*;
use rustc_attr_ir::LangItem;
use rustc_const_eval::const_eval;
use rustc_middle::ty::TypeVisitableExt;
use rustc_span::Span;
use rustc_trait_elaboration::normalize;

/// An evaluated constant.
enum Evaluated<'tcx> {
    /// A type-system value.
    ValTree(ty::Value<'tcx>),
    /// A value in const-eval memory.
    Value(mir::ConstValue, Ty<'tcx>),
}

impl GlobalRef {
    /// The mutability of this global.
    pub fn mutability(self, tcx: TyCtxt<'_>) -> mir::Mutability {
        match self {
            GlobalRef::Static(def_id) => tcx.static_mutability(def_id).unwrap(),
            GlobalRef::Alloc(_) => self.memory(tcx).unwrap().inner().mutability,
        }
    }

    /// The memory of this global. Returns `None` for a static whose evaluation fails, or that has
    /// no initializer (in an `extern` block).
    pub fn memory<'tcx>(self, tcx: TyCtxt<'tcx>) -> Option<interpret::ConstAllocation<'tcx>> {
        let def_id = match self {
            GlobalRef::Static(def_id) if tcx.is_foreign_item(def_id) => return None,
            GlobalRef::Static(def_id) => def_id,
            GlobalRef::Alloc(alloc_id) => match tcx.global_alloc(alloc_id) {
                interpret::GlobalAlloc::Memory(alloc) => return Some(alloc),
                // A nested static.
                interpret::GlobalAlloc::Static(def_id) => def_id,
                alloc => unreachable!("unexpected GlobalRef::Alloc: {alloc:?}"),
            },
        };
        tcx.eval_static_initializer(def_id).ok()
    }
}

impl<'tcx> AllocTypes<'tcx> {
    /// Gets the view for this allocation; if none had been decided, it is now viewed untyped.
    pub(crate) fn get(&self, alloc_id: interpret::AllocId) -> AllocView<'tcx> {
        *self.0.borrow_mut().entry(alloc_id).or_default()
    }

    pub(crate) fn update_if_unset(
        &self,
        alloc_id: interpret::AllocId,
        f: impl FnOnce() -> AllocView<'tcx>,
    ) {
        self.0.borrow_mut().entry(alloc_id).or_insert_with(f);
    }

    pub(crate) fn is_typed(&self, alloc_id: interpret::AllocId) -> bool {
        matches!(self.get(alloc_id), AllocView::Typed(_))
    }

    /// The type at which we view the allocation `alloc_id`.
    pub fn ty(&self, tcx: TyCtxt<'tcx>, alloc_id: interpret::AllocId) -> Ty<'tcx> {
        if let AllocView::Typed(ty) = self.get(alloc_id) {
            return ty;
        }
        // if we haven't seen it with a type, then it's untyped!
        let size = GlobalRef::Alloc(alloc_id)
            .memory(tcx)
            .unwrap()
            .inner()
            .size();
        let bytes = Ty::new_array(tcx, tcx.types.u8, size.bytes());
        let maybe_uninit = tcx.require_lang_item(LangItem::MaybeUninit, rustc_span::DUMMY_SP);
        Ty::new_adt(tcx, tcx.adt_def(maybe_uninit), tcx.mk_args(&[bytes.into()]))
    }
}

impl<'tcx> AllocTarget<'tcx> {
    /// Whether this target is read as its typed value.
    pub(crate) fn is_read_typed(&self, views: &AllocTypes<'tcx>) -> bool {
        match self {
            AllocTarget::Global(GlobalRef::Static(_)) => true,
            AllocTarget::Global(GlobalRef::Alloc(alloc_id)) => views.is_typed(*alloc_id),
            AllocTarget::Fn(_) | AllocTarget::VTable(..) | AllocTarget::TypeId(_) => false,
        }
    }
}

/// Call `f` on the MIR of the given promoted constant.
pub fn promoted_body<'tcx, R>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    promoted: mir::Promoted,
    f: impl FnOnce(&mir::Body<'tcx>) -> R,
) -> R {
    // The promoteds of a local item are stolen once its MIR is optimized.
    if let Some(local_def_id) = def_id.as_local() {
        let (_, promoteds) = tcx.mir_promoted(local_def_id);
        if !promoteds.is_stolen() {
            return f(&promoteds.borrow()[promoted]);
        }
    }
    f(&tcx.promoted_mir(def_id)[promoted])
}

impl<'tcx> ConstReader<'tcx> {
    /// Evaluate `src` and read it back. `span` is the location rustc should blame for problems
    /// with the evaluation.
    ///
    /// Fails with:
    /// - [`ReadError::NotEvaluable`] if rustc can't evaluate the constant: if it is generic (and
    ///   not trivial, i.e. its value isn't stored directly by rustc), if its evaluation fails, or
    ///   if it's an extern static;
    /// - [`ReadError::NotLoadable`] if the interpreter can't load the evaluated value;
    /// - [`ReadError::Read`] if reading the loaded value fails.
    pub fn read(
        &self,
        span: Span,
        src: ConstSource<'tcx>,
        mode: ReadMode,
    ) -> Result<Const<'tcx>, ReadError<'tcx>> {
        match self.evaluate(span, src)? {
            Evaluated::ValTree(value) if mode == ReadMode::Structured => {
                self.read_valtree(span, value)
            }
            Evaluated::ValTree(value) => {
                let ty = self.normalize(value.ty);
                let val = self.tcx.valtree_to_const_val(ty::Value { ty, ..value });
                self.read_const_value(span, val, ty, mode)
            }
            Evaluated::Value(val, ty) => self.read_const_value(span, val, self.normalize(ty), mode),
        }
    }

    /// Ask rustc for the value of `src`.
    fn evaluate(
        &self,
        span: Span,
        src: ConstSource<'tcx>,
    ) -> Result<Evaluated<'tcx>, ReadError<'tcx>> {
        let tcx = self.tcx;
        let instantiate = |ty, args| ty::EarlyBinder::bind(tcx, ty).instantiate(tcx, args);
        Ok(match src {
            ConstSource::Item { def_id, args } => {
                let uv = mir::UnevaluatedConst {
                    def: def_id,
                    args,
                    promoted: None,
                };
                let ty = tcx
                    .type_of(def_id)
                    .instantiate_identity()
                    .skip_normalization();
                let val = tcx.const_eval_resolve(self.typing_env, uv, span).ok();
                let evaluated = val.map(|val| (val, ty));
                // Otherwise, we can still read the value of "trivial" consts, which rustc
                // stores directly. This works even for generic consts.
                let (val, ty) = evaluated
                    .or_else(|| tcx.trivial_const(def_id))
                    .ok_or(ReadError::NotEvaluable)?;
                Evaluated::Value(val, instantiate(ty, args).skip_normalization())
            }
            ConstSource::Promoted {
                def_id,
                args,
                promoted,
            } => {
                let uv = mir::UnevaluatedConst {
                    def: def_id,
                    args,
                    promoted: Some(promoted),
                };
                let val = tcx
                    .const_eval_resolve(self.typing_env, uv, span)
                    .map_err(|_| ReadError::NotEvaluable)?;
                // Promoteds aren't items so `type_of` doesn't work for them; instead we read
                // their type off the return place of their MIR body.
                let ty = promoted_body(tcx, def_id, promoted, |body| {
                    body.local_decls[mir::RETURN_PLACE].ty
                });
                Evaluated::Value(val, instantiate(ty, args).skip_normalization())
            }
            ConstSource::Global(global) => {
                let alloc = global.memory(tcx).ok_or(ReadError::NotEvaluable)?;
                // A mutable allocation (e.g. of a `static mut`, or of a static whose type has
                // interior mutability) can't be read by const-eval. We don't care though, so we
                // reintern it as immutable.
                let alloc = if alloc.inner().mutability.is_mut() {
                    let mut alloc = alloc.inner().clone();
                    alloc.mutability = mir::Mutability::Not;
                    tcx.mk_const_alloc(alloc)
                } else {
                    alloc
                };
                // Give the allocation a fresh `AllocId` so we can read it like any other
                // allocation. This creates a fresh `AllocId` each time we read the global. This
                // doesn't break sharing.
                let val = mir::ConstValue::Indirect {
                    alloc_id: tcx.reserve_and_set_memory_alloc(alloc),
                    offset: rustc_abi::Size::ZERO,
                };
                Evaluated::Value(val, self.global_ty(global))
            }
            // Evaluate these only if they represent anon consts that don't show up in the type
            // system (e.g. through `adt_const_params`).
            ConstSource::TyConst(uv)
                if let Some(def_id) = uv.kind.opt_def_id()
                    && let rustc_hir::def::DefKind::AnonConst = tcx.def_kind(def_id)
                    && let ty::AnonConstKind::NonTypeSystemInline = tcx.anon_const_kind(def_id)
                    && !uv.has_opaque_types() =>
            {
                return self.evaluate(
                    span,
                    ConstSource::Item {
                        def_id,
                        args: uv.args,
                    },
                );
            }
            ConstSource::TyConst(uv) => {
                let value = self.eval_to_valtree(span, uv);
                Evaluated::ValTree(value.ok_or(ReadError::NotEvaluable)?)
            }
            ConstSource::ValTree(value) => Evaluated::ValTree(value),
            ConstSource::Value(val, ty) => Evaluated::Value(val, ty),
        })
    }

    /// Evaluate a type-level constant to a valtree. Returns `None` if the constant is generic, if
    /// its evaluation fails, or if its type has no valtree representation.
    fn eval_to_valtree(&self, span: Span, uv: ty::AliasConst<'tcx>) -> Option<ty::Value<'tcx>> {
        let tcx = self.tcx;
        if uv.has_non_region_param() {
            return None;
        }
        let def = uv.kind.opt_def_id()?;
        let erased_uv = tcx.erase_and_anonymize_regions(uv);
        let valtree = tcx
            .const_eval_resolve_for_typeck(self.typing_env, erased_uv, span)
            .ok()?
            .ok()?;
        let ty = tcx
            .type_of(def)
            .instantiate(tcx, uv.args)
            .skip_normalization();
        Some(ty::Value {
            ty: self.normalize(ty),
            valtree,
        })
    }

    /// The type at which we read a global.
    pub fn global_ty(&self, global: GlobalRef) -> Ty<'tcx> {
        let tcx = self.tcx;
        match global {
            GlobalRef::Static(def_id) => self.normalize(
                tcx.type_of(def_id)
                    .instantiate_identity()
                    .skip_normalization(),
            ),
            GlobalRef::Alloc(alloc_id) => self.alloc_types.ty(tcx, alloc_id),
        }
    }

    /// Read `val`, a value of type `ty` in const-eval memory.
    pub(crate) fn read_const_value(
        &self,
        span: Span,
        val: mir::ConstValue,
        ty: Ty<'tcx>,
        mode: ReadMode,
    ) -> Result<Const<'tcx>, ReadError<'tcx>> {
        let (ecx, op) =
            const_eval::mk_eval_cx_for_const_val(self.tcx.at(span), self.typing_env, val, ty)
                .ok_or(ReadError::NotLoadable)?;
        let read = match mode {
            ReadMode::Structured => self.read_op(&ecx, op),
            ReadMode::Bytes => self.read_raw_bytes(&ecx, &op).map(|bytes| Const {
                ty,
                kind: ConstKind::Memory(bytes),
            }),
        };
        Ok(read.report_err()?)
    }

    pub(crate) fn normalize(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        normalize(self.tcx, self.typing_env, ty::Unnormalized::new_wip(ty))
    }
}
