//! Detect which operations and items require `unsafe`.
use crate::ast::*;
use crate::{llbc_ast, ullbc_ast};

/// Whether evaluating this requires `unsafe`, following the rules outlined in
/// <https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html> and
/// <https://doc.rust-lang.org/reference/unsafety.html>.
pub trait IsUnsafe {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool;
}

impl<I: ?Sized, T: IsUnsafe> IsUnsafe for I
where
    for<'a> &'a I: IntoIterator<Item = &'a T>,
{
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        self.into_iter().any(|x| x.is_unsafe(krate))
    }
}

impl Place {
    /// Whether reading from this place requires `unsafe`. This is true if it does any of the following:
    /// - it accesses a mutable or non-safe static (safety.unsafe-static)
    /// - dereferences a raw pointer (safety.unsafe-deref)
    /// - accesses a union field. (safety.unsafe-union-access)
    pub fn is_unsafe_to_read(&self, krate: &TranslatedCrate) -> bool {
        self.subplaces().any(|place| {
            let (sub, proj) = match &place.kind {
                PlaceKind::Global(global_ref) => {
                    return krate
                        .global_decls
                        .get(global_ref.id)
                        .is_some_and(|decl| decl.is_unsafe_to_access(krate));
                }
                PlaceKind::Local(_) => return false,
                PlaceKind::Projection(sub, proj) => (sub, proj),
            };
            match proj {
                // `safety.unsafe-deref`, ignoring VTable reads (guaranteed safe)
                ProjectionElem::Deref => {
                    sub.ty.kind().is_raw_ptr()
                        && !matches!(sub.as_projection(), Some((_, ProjectionElem::PtrMetadata)))
                }
                // `safety.unsafe-union-access`.
                ProjectionElem::Field(None, _) => sub
                    .ty
                    .as_adt()
                    .and_then(|tref| krate.type_decls.get(tref.id))
                    .is_some_and(|decl| decl.kind.is_union()),
                ProjectionElem::Index { offset, .. } => offset.is_unsafe(krate),
                ProjectionElem::Subslice { from, to, .. } => {
                    from.is_unsafe(krate) || to.is_unsafe(krate)
                }
                ProjectionElem::Field(Some(_), _) | ProjectionElem::PtrMetadata => false,
            }
        })
    }

    /// Whether writing to this place requires `unsafe`. This is mostly like `is_unsafe_to_read`,
    /// except that writing to a union field is safe.
    pub fn is_unsafe_to_write(&self, krate: &TranslatedCrate) -> bool {
        match self.as_projection() {
            // Writing to a field (e.g. `u.a.b = x`) only writes to its parent, never reads it.
            Some((sub, ProjectionElem::Field(..))) => sub.is_unsafe_to_write(krate),
            _ => self.is_unsafe_to_read(krate),
        }
    }
}

impl IsUnsafe for Operand {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        match self {
            Operand::Copy(place) | Operand::Move(place) => place.is_unsafe_to_read(krate),
            Operand::Const(_) => false,
        }
    }
}

impl IsUnsafe for Rvalue {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        match self {
            Rvalue::RawPtr {
                place,
                ptr_metadata,
                ..
            } => {
                let place_is_unsafe = match place.as_projection() {
                    // `&raw const *ptr` only reads `ptr`.
                    Some((sub, ProjectionElem::Deref)) => sub.is_unsafe_to_read(krate),
                    // `&raw const STATIC_MUT` doesn't read or write the static.
                    _ if place.kind.is_global() => false,
                    _ => place.is_unsafe_to_read(krate),
                };
                place_is_unsafe || ptr_metadata.is_unsafe(krate)
            }
            Rvalue::Ref {
                place,
                ptr_metadata,
                ..
            } => place.is_unsafe_to_read(krate) || ptr_metadata.is_unsafe(krate),
            Rvalue::Discriminant(place) | Rvalue::Len(place, ..) => place.is_unsafe_to_read(krate),
            Rvalue::Use(op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, ..) => {
                op.is_unsafe(krate)
            }
            Rvalue::BinaryOp(_, op1, op2) => op1.is_unsafe(krate) || op2.is_unsafe(krate),
            Rvalue::Aggregate(_, ops) => ops.is_unsafe(krate),
            Rvalue::NullaryOp(_) => false,
        }
    }
}

impl IsUnsafe for SwitchData {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        match &self.scrutinee {
            SwitchScrutinee::Value(op) => op.is_unsafe(krate),
            SwitchScrutinee::Discriminant(place) => place.is_unsafe_to_read(krate),
        }
    }
}

/// Whether the called function is unsafe to call (unless the call is marked `callee_safe`), or
/// evaluating the function pointer, the operands or the destination is.
impl IsUnsafe for Call {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        let fn_ptr_is_unsafe = matches!(&self.func, FnOperand::Dynamic(op) if op.is_unsafe(krate));
        (self.func.is_unsafe_to_call(krate) && !self.callee_safe)
            || fn_ptr_is_unsafe
            || self.args.is_unsafe(krate)
            || self.dest.is_unsafe_to_write(krate)
    }
}

impl FnOperand {
    /// Whether the function is unsafe to call, based on its signature (safety.unsafe-call). This
    /// doesn't include evaluating the function pointer itself.
    pub fn is_unsafe_to_call(&self, krate: &TranslatedCrate) -> bool {
        match self {
            FnOperand::Regular(fn_ptr) => match fn_ptr.kind.as_ref() {
                FnPtrKind::Fun(fun_id) => krate
                    .fun_decls
                    .get(*fun_id)
                    .is_some_and(|decl| decl.is_unsafe_to_call(krate)),
                FnPtrKind::Trait(trait_ref, method_id) => krate
                    .trait_decls
                    .get(trait_ref.trait_decl_ref.skip_binder.id)
                    .is_some_and(|decl| decl.is_unsafe_to_call_method(*method_id, krate)),
            },
            FnOperand::Dynamic(op) => op.ty().kind().as_fn_ptr().unwrap().skip_binder.is_unsafe,
        }
    }
}

impl IsUnsafe for BorrowckStatement {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        match self {
            BorrowckStatement::FakeRead(place) => place.is_unsafe_to_read(krate),
            BorrowckStatement::SetOutlives(..)
            | BorrowckStatement::PredicateHolds(..)
            | BorrowckStatement::SetType { .. } => false,
        }
    }
}

/// This doesn't look into nested blocks.
impl IsUnsafe for llbc_ast::Statement {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        use llbc_ast::StatementKind;
        match &self.kind {
            StatementKind::Assign(place, rvalue) => {
                place.is_unsafe_to_write(krate) || rvalue.is_unsafe(krate)
            }
            StatementKind::SetDiscriminant(place, _)
            | StatementKind::PlaceMention(place)
            | StatementKind::Drop { place, .. } => place.is_unsafe_to_read(krate),
            StatementKind::Borrowck(st) => st.is_unsafe(krate),
            StatementKind::Assert { assert, .. } => assert.cond.is_unsafe(krate),
            StatementKind::Call { call, .. } => call.is_unsafe(krate),
            StatementKind::Switch { data, .. } => data.is_unsafe(krate),
            // Using `asm!`. `naked_asm!` is instead covered by the unsafe `#[naked]` attribute on the function.
            StatementKind::InlineAsm { kind, .. } => kind.is_asm(),
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Abort(_)
            | StatementKind::Return
            | StatementKind::UnwindResume
            | StatementKind::Break(_)
            | StatementKind::Continue(_)
            | StatementKind::Nop
            | StatementKind::Loop(_)
            | StatementKind::Error(_) => false,
        }
    }
}

/// Note that calls are terminators.
impl IsUnsafe for ullbc_ast::Statement {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        use ullbc_ast::StatementKind;
        match &self.kind {
            StatementKind::Assign(place, rvalue) => {
                place.is_unsafe_to_write(krate) || rvalue.is_unsafe(krate)
            }
            StatementKind::SetDiscriminant(place, _) | StatementKind::PlaceMention(place) => {
                place.is_unsafe_to_read(krate)
            }
            StatementKind::Borrowck(st) => st.is_unsafe(krate),
            StatementKind::Assert { assert, .. } => assert.cond.is_unsafe(krate),
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {
                false
            }
        }
    }
}

impl IsUnsafe for ullbc_ast::Terminator {
    fn is_unsafe(&self, krate: &TranslatedCrate) -> bool {
        use ullbc_ast::TerminatorKind;
        match &self.kind {
            TerminatorKind::Switch { data, .. } => data.is_unsafe(krate),
            TerminatorKind::Call { call, .. } => call.is_unsafe(krate),
            TerminatorKind::Drop { place, .. } => place.is_unsafe_to_read(krate),
            TerminatorKind::Assert { assert, .. } => assert.cond.is_unsafe(krate),
            // Using `asm!`. `naked_asm!` is instead covered by the unsafe `#[naked]` attribute on the function.
            TerminatorKind::InlineAsm { kind, .. } => kind.is_asm(),
            TerminatorKind::Goto { .. }
            | TerminatorKind::Abort(..)
            | TerminatorKind::Return
            | TerminatorKind::UnwindResume => false,
        }
    }
}

impl Attribute {
    /// Whether this attribute is unsafe to apply (safety.unsafe-attribute), as listed in
    /// attributes.safety (<https://doc.rust-lang.org/reference/attributes.html>).
    pub fn is_unsafe_to_apply(&self) -> bool {
        use from_rustc::AttributeKind::*;
        matches!(
            self,
            Attribute::Builtin(ExportName { .. } | LinkSection { .. } | Naked(..) | NoMangle(..))
        )
    }
}

impl ItemMeta {
    /// Whether the item is unsafe to declare: if it is declared in an `extern` block (safety.unsafe-extern),
    /// or it has an unsafe attribute (safety.unsafe-attribute).
    pub fn is_unsafe_to_declare(&self) -> bool {
        self.is_extern
            || self
                .attr_info
                .attributes
                .iter()
                .any(|attr| attr.is_unsafe_to_apply())
    }
}

impl FunDecl {
    /// Whether this function is unsafe to call, because it is declared `unsafe` (safety.unsafe-call).
    pub fn is_unsafe_to_call(&self, _krate: &TranslatedCrate) -> bool {
        self.signature.is_unsafe
    }

    /// Whether this function is unsafe to declare.
    pub fn is_unsafe_to_declare(&self, _krate: &TranslatedCrate) -> bool {
        // The initializer of a global is part of the global's declaration.
        !matches!(self.src, FunSource::GlobalInitializer(_))
            && self.item_meta.is_unsafe_to_declare()
    }
}

impl GlobalDecl {
    /// Whether this global is unsafe to access, because it is a mutable or unsafe external static (safety.unsafe-static).
    pub fn is_unsafe_to_access(&self, _krate: &TranslatedCrate) -> bool {
        match self.global_kind {
            GlobalKind::Static {
                is_mut,
                is_safe,
                is_thread_local: _,
            } => is_mut || !is_safe,
            GlobalKind::NamedConst | GlobalKind::AnonConst | GlobalKind::VTable => false,
        }
    }

    /// Whether this global is unsafe to declare.
    pub fn is_unsafe_to_declare(&self, _krate: &TranslatedCrate) -> bool {
        self.item_meta.is_unsafe_to_declare()
    }
}

impl TraitDecl {
    /// Whether this trait is unsafe to implement, because it is declared `unsafe` (safety.unsafe-impl).
    pub fn is_unsafe_to_implement(&self, _krate: &TranslatedCrate) -> bool {
        self.is_unsafe
    }

    /// Whether this trait method is unsafe to call, because it is declared `unsafe` (safety.unsafe-call).
    pub fn is_unsafe_to_call_method(
        &self,
        method_id: TraitMethodId,
        _krate: &TranslatedCrate,
    ) -> bool {
        self.methods[method_id].skip_binder.signature.is_unsafe
    }
}

impl TraitImpl {
    /// Whether this trait impl is unsafe to declare, because the trait is unsafe (safety.unsafe-impl)
    /// or it has an unsafe attribute (safety.unsafe-attribute).
    pub fn is_unsafe_to_declare(&self, krate: &TranslatedCrate) -> bool {
        krate.trait_decls[self.impl_trait.id].is_unsafe_to_implement(krate)
            || self.item_meta.is_unsafe_to_declare()
    }
}

impl ItemRef<'_> {
    /// Whether this item is unsafe to declare, i.e. whether whoever declares it discharges a proof
    /// obligation. Note that declaring an `unsafe fn` or `unsafe trait` is safe: the obligation is on the
    /// callers/implementors respectively.
    pub fn is_unsafe_to_declare(&self, krate: &TranslatedCrate) -> bool {
        match self {
            ItemRef::Fun(decl) => decl.is_unsafe_to_declare(krate),
            ItemRef::Global(decl) => decl.is_unsafe_to_declare(krate),
            ItemRef::TraitImpl(decl) => decl.is_unsafe_to_declare(krate),
            ItemRef::Type(_) | ItemRef::TraitDecl(_) => self.item_meta().is_unsafe_to_declare(),
        }
    }
}
