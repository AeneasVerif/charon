//! Evaluating constants with rustc's const-eval. This is the one place that knows how to get the
//! value of each kind of constant.
use crate::*;
use rustc_attr_ir::LangItem;
use rustc_const_eval::const_eval;
use rustc_span::Span;
use rustc_trait_elaboration::normalize;

/// An evaluated constant.
enum Evaluated<'tcx> {
    /// A type-system value.
    ValTree(ty::Value<'tcx>),
    /// A value in const-eval memory.
    Value(mir::ConstValue, Ty<'tcx>),
}

impl<'tcx> ConstReader<'tcx> {
    /// Evaluate `src` and read it back. `span` is the location rustc should blame for problems
    /// with the evaluation.
    ///
    /// Fails with:
    /// - [`ReadError::NotEvaluable`] if rustc can't evaluate the constant: if its evaluation
    ///   fails or if it's an extern static;
    /// - [`ReadError::NotLoadable`] if the interpreter can't load the evaluated value;
    /// - [`ReadError::Read`] if reading the loaded value fails.
    pub fn read(
        &self,
        span: Span,
        src: ConstSource<'tcx>,
        mode: ReadMode,
    ) -> Result<Const<'tcx>, ReadError<'tcx>> {
        match self.evaluate(src)? {
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
    fn evaluate(&self, src: ConstSource<'tcx>) -> Result<Evaluated<'tcx>, ReadError<'tcx>> {
        let tcx = self.tcx;
        Ok(match src {
            ConstSource::Global(global) => {
                let alloc_id = match global {
                    // Statics in `extern` blocks have no initializer.
                    GlobalRef::Static(def_id) if tcx.is_foreign_item(def_id) => {
                        return Err(ReadError::NotEvaluable);
                    }
                    GlobalRef::Static(def_id) => {
                        let alloc = tcx
                            .eval_static_initializer(def_id)
                            .map_err(|_| ReadError::NotEvaluable)?;
                        // A static whose type has interior mutability gets a mutable allocation,
                        // which const-eval refuses to read. We don't care though, so we reintern
                        // it as immutable.
                        let alloc = if alloc.inner().mutability.is_mut() {
                            let mut alloc = alloc.inner().clone();
                            alloc.mutability = mir::Mutability::Not;
                            tcx.mk_const_alloc(alloc)
                        } else {
                            alloc
                        };
                        // `eval_static_initializer` returns an interned allocation without an
                        // `AllocId`; give it one so we can read it like any other allocation.
                        // This creates a fresh `AllocId` each time we read the static.
                        tcx.reserve_and_set_memory_alloc(alloc)
                    }
                    GlobalRef::Alloc(alloc_id) => alloc_id,
                };
                let val = mir::ConstValue::Indirect {
                    alloc_id,
                    offset: rustc_abi::Size::ZERO,
                };
                Evaluated::Value(val, self.global_ty(global))
            }
            ConstSource::ValTree(value) => Evaluated::ValTree(value),
            ConstSource::Value(val, ty) => Evaluated::Value(val, ty),
        })
    }

    /// The type at which we read a global: the type of a static, or `MaybeUninit<[u8; N]>` for
    /// an allocation without a corresponding item.
    pub fn global_ty(&self, global: GlobalRef) -> Ty<'tcx> {
        let tcx = self.tcx;
        match global {
            GlobalRef::Static(def_id) => self.normalize(
                tcx.type_of(def_id)
                    .instantiate_identity()
                    .skip_normalization(),
            ),
            GlobalRef::Alloc(alloc_id) => {
                let (size, _) = tcx
                    .global_alloc(alloc_id)
                    .size_and_align(tcx, self.typing_env);
                let bytes = Ty::new_array(tcx, tcx.types.u8, size.bytes());
                let maybe_uninit =
                    tcx.require_lang_item(LangItem::MaybeUninit, rustc_span::DUMMY_SP);
                Ty::new_adt(tcx, tcx.adt_def(maybe_uninit), tcx.mk_args(&[bytes.into()]))
            }
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
