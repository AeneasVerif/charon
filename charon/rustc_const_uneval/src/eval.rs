//! Evaluating constants with rustc's const-eval. This is the one place that knows how to get the
//! value of each kind of constant.
use crate::*;
use rustc_attr_ir::LangItem;
use rustc_const_eval::const_eval;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
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

impl<'tcx> ReaderState<'tcx> {
    /// How we view the allocation `alloc_id`, trying to use `ty` if possible.
    /// Returns the deduplicated `AllocId` and the type it's read at.
    pub(crate) fn register(
        &self,
        tcx: TyCtxt<'tcx>,
        alloc_id: interpret::AllocId,
        ty: Option<Ty<'tcx>>,
    ) -> (interpret::AllocId, Ty<'tcx>) {
        let allocs = &mut *self.0.borrow_mut();
        let key = *allocs.keys.entry(alloc_id).or_insert_with(|| {
            let interpret::GlobalAlloc::Memory(alloc) = tcx.global_alloc(alloc_id) else {
                return AllocKey::Unique(alloc_id);
            };
            if alloc.inner().mutability.is_mut() {
                return AllocKey::Unique(alloc_id);
            }
            AllocKey::Deduplicatable(tcx.with_stable_hashing_context(|mut hcx| {
                let mut hasher = StableHasher::new();
                // this hashes the contents of the allocation
                alloc_id.stable_hash(&mut hcx, &mut hasher);
                hasher.finish()
            }))
        });
        *allocs.globals.entry(key).or_insert_with(|| {
            if let Some(ty) = ty
                && ConstReader::ty_covers_alloca(tcx, alloc_id, ty)
            {
                return (alloc_id, ty);
            }
            let size = GlobalRef::Alloc(alloc_id)
                .memory(tcx)
                .unwrap()
                .inner()
                .size();
            let bytes = Ty::new_array(tcx, tcx.types.u8, size.bytes());
            // try avoiding `MaybeUninit<[u8; N]>` if `[u8; N]` suffices
            if ConstReader::ty_covers_alloca(tcx, alloc_id, bytes) {
                return (alloc_id, bytes);
            }
            let maybe_uninit = tcx.require_lang_item(LangItem::MaybeUninit, rustc_span::DUMMY_SP);
            let maybe_uninit =
                Ty::new_adt(tcx, tcx.adt_def(maybe_uninit), tcx.mk_args(&[bytes.into()]));
            (alloc_id, maybe_uninit)
        })
    }

    /// The type at which we view the allocation `alloc_id`. If no type has been decided,
    /// picks the default: `[u8; N]` or `MaybeUninit<[u8; N]>`.
    pub fn ty_or_default(&self, tcx: TyCtxt<'tcx>, alloc_id: interpret::AllocId) -> Ty<'tcx> {
        self.register(tcx, alloc_id, None).1
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
                let val = tcx
                    .const_eval_resolve(self.eval_typing_env(args), uv, span)
                    .ok();
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
                    .const_eval_resolve(self.eval_typing_env(args), uv, span)
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
                if let ty::AliasConstKind::Anon { def_id } = uv.kind
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
        // Normalization replaces `InherentSelf` consts with their value, so we only see one if
        // normalization failed or was skipped.
        if uv.has_non_region_param() || matches!(uv.kind, ty::AliasConstKind::InherentSelf { .. }) {
            return None;
        }
        let erased_uv = tcx.erase_and_anonymize_regions(uv);
        let valtree = tcx
            .const_eval_resolve_for_typeck(self.eval_typing_env(erased_uv), erased_uv, span)
            .ok()?
            .ok()?;
        let ty = uv.type_of(tcx).skip_normalization();
        Some(ty::Value {
            ty: self.normalize(ty),
            valtree,
        })
    }

    /// The typing env we use to evaluate a constant with arguments `args`.
    fn eval_typing_env(&self, args: impl TypeVisitableExt<TyCtxt<'tcx>>) -> ty::TypingEnv<'tcx> {
        if !args.has_param() {
            ty::TypingEnv::fully_monomorphized()
        } else {
            self.typing_env
        }
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
            GlobalRef::Alloc(alloc_id) => self.state.ty_or_default(tcx, alloc_id),
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
        // Fast path: there are lots of `FnDef` constants (one per function call)
        if mode == ReadMode::Structured && matches!(ty.kind(), ty::FnDef(..)) {
            return Ok(Const {
                ty,
                kind: ConstKind::fn_def(self.tcx, ty),
            });
        }
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
