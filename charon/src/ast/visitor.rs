//! Defines two overrideable visitor traits that can be used to conveniently traverse the whole
//! contents of an item. This is useful when e.g. dealing with types, which show up pretty much
//! everywhere in the ast.
//!
//! The crate defines two traits:
/// - `AstVisitable` is a trait implemented by all the types that can be visited by this;
/// - `VisitAst[Mut]` is a (pair of) visitor trait(s) that can be implemented by visitors.
/// To define a visitor, implement `VisitAst[Mut]` and override the methods you need. Calling
/// `x.drive[_mut](&mut visitor)` will then traverse `x`, calling the visitor methods on all the
/// subvalues encountered.
///
/// Underneath it all, this uses `derive_generic_visitor::Drive[Mut]` to do the actual visiting.
use std::{any::Any, collections::HashMap};

use crate::ast::*;
use derive_generic_visitor::*;
use index_vec::Idx;
use indexmap::IndexMap;

/// An overrideable visitor trait that can be used to conveniently traverse the whole contents of
/// an item. This is useful when e.g. dealing with types, which show up pretty much everywhere in
/// the ast.
///
/// This defines three traits:
/// - `AstVisitable` is a trait implemented by all the types listed below; it has a
/// `drive[_mut]` method that takes a `VisitAst[Mut]` visitor and calls its methods on all
/// the relevant subvalues of `self` encountered.
/// - `VisitAst[Mut]` is a (pair of) visitor trait(s) that can be implemented by visitors. To
/// define a visitor, implement `VisitAst[Mut]` and override the methods you need.
///
/// This trait has a `drive[_mut]` method that knows how to drive a `VisitAst[Mut]` visitor. This
/// trait is implemented for all the listed types. If listed as `override`, the corresponding
/// visitor trait has an overrideable method to visit this type. If listed as `drive`, the type
/// will only be visited by recursing into its contents.
///
/// Morally this represents the predicate `for<V: VisitAst[Mut]> Self:
/// Drive[Mut]<AstVisitableWrapper<V>>`
#[visitable_group(
    // Defines the `Visit[Mut]` traits and the `drive[_mut]` method that drives them.
    visitor(drive(&VisitAst)),
    visitor(drive_mut(&mut VisitAstMut)),
    // Types that we unconditionally explore.
    drive(
        AbortKind, Assert, BinOp, Body, BorrowKind, BuiltinFunId, BuiltinIndexOp, BuiltinTy, Call,
        CastKind, ClosureInfo, ClosureKind, ConstGenericVar, ConstGenericVarId,
        Disambiguator, ExistentialPredicate, Field, FieldId, FieldProjKind, FloatTy, FloatValue,
        FnOperand, FunId, FunIdOrTraitMethodRef, FunSig, ImplElem, IntegerTy, Literal, LiteralTy,
        llbc_ast::Block, llbc_ast::ExprBody, llbc_ast::RawStatement, llbc_ast::Switch,
        Locals, Name, NullOp, Opaque, Operand, PathElem, PlaceKind, ProjectionElem, RawConstantExpr,
        RefKind, RegionId, RegionVar, ScalarValue, TraitItemName,
        TranslatedCrate, TypeDeclKind, TypeId, TypeVar, TypeVarId,
        ullbc_ast::BlockData, ullbc_ast::BlockId, ullbc_ast::ExprBody, ullbc_ast::RawStatement,
        ullbc_ast::RawTerminator, ullbc_ast::SwitchTargets, ullbc_ast::Terminator,
        UnOp, Local, Variant, VariantId, LocalId, CopyNonOverlapping, Layout, VariantLayout, PtrMetadata, VTable,
        for<T: AstVisitable> Box<T>,
        for<T: AstVisitable> Option<T>,
        for<A: AstVisitable, B: AstVisitable> (A, B),
        for<A: AstVisitable, B: AstVisitable> Result<A, B>,
        for<A: AstVisitable, B: AstVisitable> OutlivesPred<A, B>,
        for<T: AstVisitable> Vec<T>,
        for<I: Idx, T: AstVisitable> Vector<I, T>,
    ),
    // Types for which we call the corresponding `visit_$ty` method, which by default explores the
    // type but can be overridden.
    override(
        DeBruijnId, Ty, TyKind, Region, ConstGeneric, TraitRef, TraitRefKind,
        TypeDeclRef, FunDeclRef, MaybeBuiltinFunDeclRef, TraitMethodRef, GlobalDeclRef, TraitDeclRef, TraitImplRef,
        GenericArgs, GenericParams, TraitClause, TraitClauseId, TraitTypeConstraint, Place, Rvalue,
        for<T: AstVisitable + Idx> DeBruijnVar<T>,
        for<T: AstVisitable> RegionBinder<T>,
        for<T: AstVisitable> Binder<T>,
        llbc_statement: llbc_ast::Statement, ullbc_statement: ullbc_ast::Statement,
        AggregateKind, FnPtr, ItemKind, ItemMeta, Span, ConstantExpr,
        FunDeclId, GlobalDeclId, TypeDeclId, TraitDeclId, TraitImplId,
        FunDecl, GlobalDecl, TypeDecl, TraitDecl, TraitImpl
    )
)]
pub trait AstVisitable: Any {
    /// The name of the type, used for debug logging.
    fn name(&self) -> &'static str {
        std::any::type_name::<Self>()
    }
    /// Visit all occurrences of that type inside `self`, in pre-order traversal.
    fn dyn_visit<T: AstVisitable>(&self, f: impl FnMut(&T)) {
        let _ = self.drive(&mut DynVisitor::new_shared::<T>(f));
    }
    /// Visit all occurrences of that type inside `self`, in pre-order traversal.
    fn dyn_visit_mut<T: AstVisitable>(&mut self, f: impl FnMut(&mut T)) {
        let _ = self.drive_mut(&mut DynVisitor::new_mut::<T>(f));
    }
}

/// Manual impl that only visits the values
impl<K: Any, T: AstVisitable> AstVisitable for HashMap<K, T> {
    fn drive<V: VisitAst>(&self, v: &mut V) -> ControlFlow<V::Break> {
        for x in self.values() {
            v.visit(x)?;
        }
        Continue(())
    }
    fn drive_mut<V: VisitAstMut>(&mut self, v: &mut V) -> ControlFlow<V::Break> {
        for x in self.values_mut() {
            v.visit(x)?;
        }
        Continue(())
    }
}

/// Manual impl that only visits the values
impl<K: Any, T: AstVisitable> AstVisitable for IndexMap<K, T> {
    fn drive<V: VisitAst>(&self, v: &mut V) -> ControlFlow<V::Break> {
        for x in self.values() {
            v.visit(x)?;
        }
        Continue(())
    }
    fn drive_mut<V: VisitAstMut>(&mut self, v: &mut V) -> ControlFlow<V::Break> {
        for x in self.values_mut() {
            v.visit(x)?;
        }
        Continue(())
    }
}

/// A smaller visitor group just for function bodies. This explores statements, places and
/// operands, but does not recurse into types.
///
/// This defines three traits:
/// - `BodyVisitable` is a trait implemented by all the types listed below; it has a
/// `drive_body[_mut]` method that takes a `VisitBody[Mut]` visitor and calls its methods on all
/// the relevant subvalues of `self` encountered.
/// - `VisitBody[Mut]` is a (pair of) visitor trait(s) that can be implemented by visitors. To
/// define a visitor, implement `VisitBody[Mut]` and override the methods you need.
///
/// Morally this represents the predicate `for<V: VisitBody[Mut]> Self:
/// Drive[Mut]<BodyVisitableWrapper<V>>`
#[visitable_group(
    // Defines the `VisitBody[Mut]` traits and the `drive_body[_mut]` method that drives them.
    visitor(drive_body(&VisitBody)),
    visitor(drive_body_mut(&mut VisitBodyMut)),
    // Types that are ignored when encountered.
    skip(
        AbortKind, BinOp, BorrowKind, ConstantExpr, ConstGeneric, FieldId, FieldProjKind,
        TypeDeclRef, FunDeclId, FunIdOrTraitMethodRef, GenericArgs, GlobalDeclRef, IntegerTy,
        NullOp, RefKind, ScalarValue, Span, Ty, TypeDeclId, TypeId, UnOp, VariantId, LocalId,
    ),
    // Types that we unconditionally explore.
    drive(
        Assert, PlaceKind,
        llbc_ast::ExprBody, llbc_ast::RawStatement, llbc_ast::Switch,
        ullbc_ast::BlockData, ullbc_ast::ExprBody, ullbc_ast::RawStatement,
        ullbc_ast::RawTerminator, ullbc_ast::SwitchTargets, CopyNonOverlapping,
        Body, Opaque, Locals, Local,
        for<T: BodyVisitable> Box<T>,
        for<T: BodyVisitable> Option<T>,
        for<T: BodyVisitable, E: BodyVisitable> Result<T, E>,
        for<A: BodyVisitable, B: BodyVisitable> (A, B),
        for<T: BodyVisitable> Vec<T>,
        for<I: Idx, T: BodyVisitable> Vector<I, T>,
    ),
    // Types for which we call the corresponding `visit_$ty` method, which by default explores the
    // type but can be overridden.
    override(
        AggregateKind, Call, FnOperand, FnPtr,
        Operand, Place, ProjectionElem, Rvalue,
        llbc_block: llbc_ast::Block,
        llbc_statement: llbc_ast::Statement,
        ullbc_statement: ullbc_ast::Statement,
        ullbc_terminator: ullbc_ast::Terminator,
        ullbc_block_id: ullbc_ast::BlockId,
    )
)]
pub trait BodyVisitable: Any {
    /// Visit all occurrences of that type inside `self`, in pre-order traversal.
    fn dyn_visit_in_body<T: BodyVisitable>(&self, f: impl FnMut(&T)) {
        let _ = self.drive_body(&mut DynVisitor::new_shared::<T>(f));
    }

    /// Visit all occurrences of that type inside `self`, in pre-order traversal.
    fn dyn_visit_in_body_mut<T: BodyVisitable>(&mut self, f: impl FnMut(&mut T)) {
        let _ = self.drive_body_mut(&mut DynVisitor::new_mut::<T>(f));
    }
}

/// Ast and body visitor that uses dynamic dispatch to call the provided function on the visited
/// values of the right type.
#[derive(Visitor)]
pub struct DynVisitor<F> {
    enter: F,
}
impl DynVisitor<()> {
    pub fn new_shared<T: Any>(mut f: impl FnMut(&T)) -> DynVisitor<impl FnMut(&dyn Any)> {
        let enter = move |x: &dyn Any| {
            if let Some(x) = x.downcast_ref::<T>() {
                f(x);
            }
        };
        DynVisitor { enter }
    }
    pub fn new_mut<T: Any>(mut f: impl FnMut(&mut T)) -> DynVisitor<impl FnMut(&mut dyn Any)> {
        let enter = move |x: &mut dyn Any| {
            if let Some(x) = x.downcast_mut::<T>() {
                f(x);
            }
        };
        DynVisitor { enter }
    }
}
impl<F> VisitAst for DynVisitor<F>
where
    F: FnMut(&dyn Any),
{
    fn visit<'a, T: AstVisitable>(&'a mut self, x: &T) -> ControlFlow<Self::Break> {
        (self.enter)(x);
        x.drive(self)?;
        Continue(())
    }
}
impl<F> VisitAstMut for DynVisitor<F>
where
    F: FnMut(&mut dyn Any),
{
    fn visit<'a, T: AstVisitable>(&'a mut self, x: &mut T) -> ControlFlow<Self::Break> {
        (self.enter)(x);
        x.drive_mut(self)?;
        Continue(())
    }
}
impl<F> VisitBody for DynVisitor<F>
where
    F: FnMut(&dyn Any),
{
    fn visit<'a, T: BodyVisitable>(&'a mut self, x: &T) -> ControlFlow<Self::Break> {
        (self.enter)(x);
        x.drive_body(self)?;
        Continue(())
    }
}
impl<F> VisitBodyMut for DynVisitor<F>
where
    F: FnMut(&mut dyn Any),
{
    fn visit<'a, T: BodyVisitable>(&'a mut self, x: &mut T) -> ControlFlow<Self::Break> {
        (self.enter)(x);
        x.drive_body_mut(self)?;
        Continue(())
    }
}
