//! Detect which operations and items require `unsafe`.
use macros::EnumIsA;

use crate::ast::*;
use crate::{llbc_ast, ullbc_ast};

/// Whether something requires `unsafe`.
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
    pub fn read_safety(&self, krate: &TranslatedCrate) -> Safety {
        self.subplaces()
            .map(|place| {
                let (sub, proj) = match &place.kind {
                    PlaceKind::Global(global_ref) => {
                        return match krate.global_decls.get(global_ref.id) {
                            Some(decl) => decl.is_unsafe_to_access(krate).into(),
                            None => {
                                Safety::Unknown(format!("{:?} wasn't translated", global_ref.id))
                            }
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
                        let Some(tref) = sub.ty.as_adt() else {
                            return Safety::Safe;
                        };
                        match krate.type_decls.get(tref.id).map(|decl| &decl.kind) {
                            Some(TypeDeclKind::Union(_)) => Safety::Unsafe,
                            Some(
                                TypeDeclKind::Struct(_)
                                | TypeDeclKind::Enum(_)
                                | TypeDeclKind::Alias(_),
                            ) => Safety::Safe,
                            // We can't tell whether this is a union.
                            Some(TypeDeclKind::Opaque | TypeDeclKind::Error(_)) | None => {
                                Safety::Unknown(format!(
                                    "{:?} is opaque or wasn't translated",
                                    tref.id
                                ))
                            }
                        }
                    }
                    ProjectionElem::Index { offset, .. } => offset.safety(krate),
                    ProjectionElem::Subslice { from, to, .. } => {
                        from.safety(krate).or_else(|| to.safety(krate))
                    }
                    ProjectionElem::Field(Some(_), _) | ProjectionElem::PtrMetadata => Safety::Safe,
                }
            })
            .collect()
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
                let place_safety = match place.as_projection() {
                    // `&raw const *ptr` only reads `ptr`.
                    Some((sub, ProjectionElem::Deref)) => sub.read_safety(krate),
                    // `&raw const STATIC_MUT` doesn't read or write the static.
                    _ if place.kind.is_global() => Safety::Safe,
                    _ => place.read_safety(krate),
                };
                place_safety.or_else(|| ptr_metadata.safety(krate))
            }
            Rvalue::Ref {
                place,
                ptr_metadata,
                ..
            } => place
                .read_safety(krate)
                .or_else(|| ptr_metadata.safety(krate)),
            Rvalue::Discriminant(place) | Rvalue::Len(place, ..) => place.read_safety(krate),
            Rvalue::Use(op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, ..) => {
                op.safety(krate)
            }
            Rvalue::BinaryOp(_, op1, op2) => op1.safety(krate).or_else(|| op2.safety(krate)),
            Rvalue::Aggregate(_, ops) => ops.safety(krate),
            Rvalue::NullaryOp(_) => Safety::Safe,
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

/// The safety of calling the function (unless the call is marked `callee_safe`) and of evaluating
/// the function pointer, the operands and the destination.
impl HasSafety for Call {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        let callee_safety = if self.callee_safe {
            Safety::Safe
        } else {
            self.func.safety(krate)
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
                    None => Safety::Unknown(format!("{fun_id:?} wasn't translated")),
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

/// This doesn't look into nested blocks.
impl HasSafety for llbc_ast::Statement {
    fn safety(&self, krate: &TranslatedCrate) -> Safety {
        use llbc_ast::StatementKind;
        match &self.kind {
            StatementKind::Assign(place, rvalue) => {
                place.write_safety(krate).or_else(|| rvalue.safety(krate))
            }
            StatementKind::SetDiscriminant(place, _)
            | StatementKind::PlaceMention(place)
            | StatementKind::Drop { place, .. } => place.read_safety(krate),
            StatementKind::Borrowck(st) => st.safety(krate),
            StatementKind::Assert { assert, .. } => assert.cond.safety(krate),
            StatementKind::Call { call, .. } => call.safety(krate),
            StatementKind::Switch { data, .. } => data.safety(krate),
            // Using `asm!`. `naked_asm!` is instead covered by the unsafe `#[naked]` attribute on the function.
            StatementKind::InlineAsm { kind, .. } => kind.is_asm().into(),
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Abort(_)
            | StatementKind::Return
            | StatementKind::UnwindResume
            | StatementKind::Break(_)
            | StatementKind::Continue(_)
            | StatementKind::Nop
            | StatementKind::Loop(_)
            | StatementKind::Error(_) => Safety::Safe,
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
            StatementKind::SetDiscriminant(place, _) | StatementKind::PlaceMention(place) => {
                place.read_safety(krate)
            }
            StatementKind::Borrowck(st) => st.safety(krate),
            StatementKind::Assert { assert, .. } => assert.cond.safety(krate),
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
            // Using `asm!`. `naked_asm!` is instead covered by the unsafe `#[naked]` attribute on the function.
            TerminatorKind::InlineAsm { kind, .. } => kind.is_asm().into(),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Abort(..)
            | TerminatorKind::Return
            | TerminatorKind::UnwindResume => Safety::Safe,
        }
    }
}
