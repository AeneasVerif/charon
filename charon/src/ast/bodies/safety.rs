//! Detect which operations and items require `unsafe`.
use macros::EnumIsA;

use crate::ast::*;
use crate::formatter::IntoFormatter;
use crate::pretty::FmtWithCtx;
use crate::{llbc_ast, ullbc_ast};

/// Whether an operation requires `unsafe`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(EnumIsA)]
pub enum Safety {
    Safe,
    Unsafe,
    Unknown(String),
}

impl Safety {
    /// Combine with the safety of something else that is also evaluated: `Unsafe` takes precedence
    /// over `Unknown`, which takes precedence over `Safe`. `other` is only computed if needed.
    pub fn or_else(self, other: impl FnOnce() -> Safety) -> Safety {
        match self {
            Safety::Unsafe => Safety::Unsafe,
            Safety::Safe => other(),
            Safety::Unknown(reason) => match other() {
                Safety::Unsafe => Safety::Unsafe,
                Safety::Safe | Safety::Unknown(_) => Safety::Unknown(reason),
            },
        }
    }
}

impl From<bool> for Safety {
    fn from(is_unsafe: bool) -> Self {
        if is_unsafe {
            Safety::Unsafe
        } else {
            Safety::Safe
        }
    }
}

/// Combine the safety of all the elements, see [`Safety::or_else`]. We stop consuming the iterator
/// once we know the result is `Unsafe`.
impl FromIterator<Safety> for Safety {
    fn from_iter<I: IntoIterator<Item = Safety>>(iter: I) -> Self {
        let mut safety = Safety::Safe;
        for other in iter {
            safety = safety.or_else(|| other);
            if safety.is_unsafe() {
                break;
            }
        }
        safety
    }
}

/// The safety of evaluating this, following the rules outlined in
/// <https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html> and
/// <https://doc.rust-lang.org/reference/unsafety.html>.
///
/// This is computed on the translated (U)LLBC, so it can't know exactly what the user wrote. For example,
/// macros like `println!("{x}")` expand to unsafe operations inside their own `unsafe` blocks. Some safe
/// operations like slice indexing also expand to a bounds check followed by an unchecked access. Dead code
/// elimination may hide an unsafe operation. So all in all this will not report exactly the same safety as
/// rustc sees in the surface code. It is however accurate if you treat (U)LLBC as its own language: we
/// accurately flag operations that have soundness preconditions.
///
/// We currently don't support unsafe fields and unsafe binders.
pub trait HasSafety {
    fn safety(&self, krate: &TranslatedCrate) -> Safety;
}

impl<I: ?Sized, T: HasSafety> HasSafety for I
where
    for<'a> &'a I: IntoIterator<Item = &'a T>,
{
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        self.into_iter().map(|x| x.safety(krate)).collect()
    }
}

impl<T: HasSafety> HasSafety for RegionBinder<T> {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        self.skip_binder.safety(krate)
    }
}

impl HasSafety for FunSig {
    fn safety(&self, _krate: &TranslatedCrate) -> Safety {
        self.is_unsafe.into()
    }
}

impl Place {
    /// The safety of reading from this place. It is unsafe if it does any of the following:
    /// - it accesses a mutable or non-safe static (safety.unsafe-static)
    /// - it dereferences a raw pointer (safety.unsafe-deref)
    /// - it accesses a union field (safety.unsafe-union-access)
    /// - it accesses an index or slice, as these are unchecked in MIR.
    pub fn read_safety(&self, krate: &TranslatedCrate) -> Safety {
        self.subplaces()
            .map(|place| place.shallow_safety(krate))
            .collect()
    }

    /// The safety of accessing this place, ignoring subplaces.
    fn shallow_safety(&self, krate: &TranslatedCrate) -> Safety {
        let (sub, proj) = match &self.kind {
            PlaceKind::Global(global_ref) => {
                return match krate.global_decls.get(global_ref.id) {
                    Some(decl) => decl.is_unsafe_to_access(krate).into(),
                    None => Safety::Unknown(format!(
                        "{} wasn't translated",
                        global_ref.with_ctx(&krate.into_fmt())
                    )),
                };
            }
            PlaceKind::Local(_) => return Safety::Safe,
            PlaceKind::Projection(sub, proj) => (sub, proj),
        };
        match proj {
            // `safety.unsafe-deref`, ignoring VTable reads (guaranteed safe)
            ProjectionElem::Deref => (sub.ty.kind().is_raw_ptr()
                && !matches!(sub.as_projection(), Some((_, ProjectionElem::PtrMetadata))))
            .into(),
            // `safety.unsafe-union-access`.
            ProjectionElem::Field(None, _) => {
                let Some(tref) = sub.ty.as_adt().filter(|tref| !tref.is_builtin()) else {
                    return Safety::Safe;
                };
                match krate.type_decls.get(tref.id).map(|decl| &decl.kind) {
                    Some(TypeDeclKind::Union(_)) => Safety::Unsafe,
                    Some(
                        TypeDeclKind::Struct(_) | TypeDeclKind::Enum(_) | TypeDeclKind::Alias(_),
                    ) => Safety::Safe,
                    Some(TypeDeclKind::Opaque | TypeDeclKind::Error(_)) | None => {
                        Safety::Unknown(format!(
                            "{} is opaque or wasn't translated",
                            tref.with_ctx(&krate.into_fmt())
                        ))
                    }
                }
            }
            ProjectionElem::Index { .. } | ProjectionElem::Subslice { .. } => Safety::Unsafe,
            ProjectionElem::Field(Some(_), _) | ProjectionElem::PtrMetadata => Safety::Safe,
        }
    }

    /// The safety of writing to this place. This is mostly like `read_safety`, except that writing
    /// to a union field is safe.
    pub fn write_safety(&self, krate: &TranslatedCrate) -> Safety {
        match self.as_projection() {
            // Writing to a field (e.g. `u.a.b = x`) only writes to its parent, never reads it.
            Some((sub, ProjectionElem::Field(..))) => sub.write_safety(krate),
            _ => self.read_safety(krate),
        }
    }
}

impl HasSafety for Operand {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        match self {
            Operand::Copy(place) | Operand::Move(place) => place.read_safety(krate),
            Operand::Const(_) => Safety::Safe,
        }
    }
}

impl HasSafety for Rvalue {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        match self {
            Rvalue::RawPtr {
                place,
                ptr_metadata,
                ..
            } => {
                // A raw borrow doesn't access the borrowed place itself. Like rustc, we only skip its
                // outermost accesses: `&raw const *ptr` is ok, but `&raw const (*ptr).field` isn't.
                let accessed = match &place.kind {
                    PlaceKind::Global(_) => None,
                    PlaceKind::Projection(sub, ProjectionElem::Deref) => Some(&**sub),
                    _ => place.subplaces().find(|place| {
                        !matches!(place.as_projection(), Some((_, ProjectionElem::Field(..))))
                            || !place.shallow_safety(krate).is_unsafe()
                    }),
                };
                accessed
                    .map_or(Safety::Safe, |place| place.read_safety(krate))
                    .or_else(|| ptr_metadata.safety(krate))
            }
            Rvalue::Ref {
                place,
                ptr_metadata,
                ..
            } => place
                .read_safety(krate)
                .or_else(|| ptr_metadata.safety(krate)),
            Rvalue::Discriminant(place) | Rvalue::Len(place, ..) => place.read_safety(krate),
            Rvalue::UnaryOp(unop, op) => unop.safety(krate).or_else(|| op.safety(krate)),
            Rvalue::Use(op, _) | Rvalue::Repeat(op, ..) => op.safety(krate),
            Rvalue::BinaryOp(binop, op1, op2) => binop
                .safety(krate)
                .or_else(|| op1.safety(krate).or_else(|| op2.safety(krate))),
            Rvalue::Aggregate(_, ops) => ops.safety(krate),
            Rvalue::NullaryOp(_) => Safety::Safe,
        }
    }
}

impl HasSafety for UnOp {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        match self {
            UnOp::Not => Safety::Safe,
            UnOp::Neg(om) => om.safety(krate),
            UnOp::Cast(CastKind::Concretize(..) | CastKind::Transmute(..)) => Safety::Unsafe,
            UnOp::Cast(CastKind::PtrWithExposedProvenance(_, tgt)) if tgt.is_ref() => {
                Safety::Unsafe
            }
            UnOp::Cast(_) => Safety::Safe,
        }
    }
}

impl HasSafety for BinOp {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        use BinOp::*;
        match self {
            Add(om) | Sub(om) | Mul(om) | Div(om) | Rem(om) | Shl(om) | Shr(om) => om.safety(krate),
            BitXor | BitAnd | BitOr | Eq | Lt | Le | Ne | Ge | Gt | AddChecked | SubChecked
            | MulChecked | Cmp => Safety::Safe,
            Offset => Safety::Unsafe,
        }
    }
}

impl HasSafety for OverflowMode {
    fn safety(&self, _krate: &TranslatedCrate) -> Safety {
        match self {
            OverflowMode::UB => Safety::Unsafe,
            OverflowMode::Panic | OverflowMode::Wrap => Safety::Safe,
        }
    }
}

impl HasSafety for SwitchData {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        match &self.scrutinee {
            SwitchScrutinee::Value(op) => op.safety(krate),
            SwitchScrutinee::Discriminant(place) => place.read_safety(krate),
        }
    }
}

/// The safety of calling the function (see [`CallSafety`]) and of evaluating the function pointer,
/// the operands and the destination.
impl HasSafety for Call {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        let callee_safety = match self.safety {
            CallSafety::Inherit => self.func.safety(krate),
            CallSafety::Safe => Safety::Safe,
            CallSafety::Unsafe => Safety::Unsafe,
        };
        callee_safety
            .or_else(|| match &self.func {
                FnOperand::Dynamic(op) => op.safety(krate),
                FnOperand::Regular(_) => Safety::Safe,
            })
            .or_else(|| self.args.safety(krate))
            .or_else(|| self.dest.write_safety(krate))
    }
}

impl HasSafety for FnOperand {
    /// The safety of calling the function, based on its signature (safety.unsafe-call). This
    /// doesn't include evaluating the function pointer itself.
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        match self {
            FnOperand::Regular(fn_ptr) => match fn_ptr.kind.as_ref() {
                FnPtrKind::Fun(fun_id) => match krate.fun_decls.get(*fun_id) {
                    Some(decl) => decl.signature.safety(krate),
                    None => Safety::Unknown(format!(
                        "{} wasn't translated",
                        fun_id.with_ctx(&krate.into_fmt())
                    )),
                },
                FnPtrKind::Trait(trait_ref, method_id) => {
                    let trait_id = trait_ref.trait_decl_ref.skip_binder.id;
                    let method = krate
                        .trait_decls
                        .get(trait_id)
                        .and_then(|decl| decl.methods.get(*method_id));
                    match method {
                        Some(method) => method.skip_binder.signature.safety(krate),
                        None => Safety::Unknown(format!(
                            "the signature of {method_id:?} of {trait_id:?} wasn't translated"
                        )),
                    }
                }
            },
            FnOperand::Dynamic(op) => op.ty().kind().as_fn_ptr().unwrap().safety(krate),
        }
    }
}

impl HasSafety for BorrowckStatement {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        match self {
            BorrowckStatement::FakeRead(place) => place.read_safety(krate),
            BorrowckStatement::SetOutlives(..)
            | BorrowckStatement::PredicateHolds(..)
            | BorrowckStatement::SetType { .. } => Safety::Safe,
        }
    }
}

impl HasSafety for AbortKind {
    fn safety(&self, _krate: &TranslatedCrate) -> Safety {
        match self {
            AbortKind::UndefinedBehavior => Safety::Unsafe,
            AbortKind::Panic(..) | AbortKind::UnwindTerminate => Safety::Safe,
        }
    }
}

/// This doesn't look into nested blocks.
impl HasSafety for llbc_ast::Statement {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        use llbc_ast::StatementKind;
        match &self.kind {
            StatementKind::Assign(place, rvalue) => {
                place.write_safety(krate).or_else(|| rvalue.safety(krate))
            }
            StatementKind::SetDiscriminant(place, _) => place.write_safety(krate),
            StatementKind::PlaceMention(place) | StatementKind::Drop { place, .. } => {
                place.read_safety(krate)
            }
            StatementKind::Borrowck(st) => st.safety(krate),
            StatementKind::Assert {
                assert, on_failure, ..
            } => assert
                .cond
                .safety(krate)
                .or_else(|| on_failure.safety(krate)),
            StatementKind::Call { call, .. } => call.safety(krate),
            StatementKind::Switch { data, .. } => data.safety(krate),
            StatementKind::InlineAsm { asm, .. } => asm.kind.is_asm().into(),
            StatementKind::UndefinedBehavior => Safety::Unsafe,
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::Loop(_)
            | StatementKind::Break(_)
            | StatementKind::Continue(_)
            | StatementKind::Return
            | StatementKind::Panic { .. }
            | StatementKind::UnwindResume
            | StatementKind::UnwindTerminate => Safety::Safe,
        }
    }
}

/// Note that calls are terminators.
impl HasSafety for ullbc_ast::Statement {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        use ullbc_ast::StatementKind;
        match &self.kind {
            StatementKind::Assign(place, rvalue) => {
                place.write_safety(krate).or_else(|| rvalue.safety(krate))
            }
            StatementKind::SetDiscriminant(place, _) => place.write_safety(krate),
            StatementKind::PlaceMention(place) => place.read_safety(krate),
            StatementKind::Borrowck(st) => st.safety(krate),
            StatementKind::Assert { assert, on_failure } => assert
                .cond
                .safety(krate)
                .or_else(|| on_failure.safety(krate)),
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {
                Safety::Safe
            }
        }
    }
}

impl HasSafety for ullbc_ast::Terminator {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        use ullbc_ast::TerminatorKind;
        match &self.kind {
            TerminatorKind::Switch { data, .. } => data.safety(krate),
            TerminatorKind::Call { call, .. } => call.safety(krate),
            TerminatorKind::Drop { place, .. } => place.read_safety(krate),
            TerminatorKind::Assert { assert, .. } => assert.cond.safety(krate),
            TerminatorKind::InlineAsm { asm, .. } => asm.kind.is_asm().into(),
            TerminatorKind::UndefinedBehavior => Safety::Unsafe,
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Panic { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate => Safety::Safe,
        }
    }
}
