use crate::ast::*;
use derive_generic_visitor::{ControlFlow, Drive, DriveMut, DriveTwo, VisitTwo, Visitor};
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};

pub mod fun_decl;
pub mod global_decl;
pub mod item_ids;
pub mod layout;
pub mod layout_guarantee_utils;
pub mod layout_guarantees;
pub mod trait_decl;
pub mod trait_impl;
pub mod type_decl;

pub use fun_decl::*;
pub use global_decl::*;
pub use item_ids::*;
pub use layout::*;
pub use layout_guarantees::*;
pub use trait_decl::*;
pub use trait_impl::*;
pub use type_decl::*;

/// A translated item.
#[derive(
    Debug, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity, Drive, DriveMut, DriveTwo,
)]
pub enum ItemByVal {
    Type(TypeDecl),
    Fun(FunDecl),
    Global(GlobalDecl),
    TraitDecl(TraitDecl),
    TraitImpl(TraitImpl),
}

/// A reference to a translated item.
#[derive(
    Debug,
    Clone,
    Copy,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    VariantIndexArity,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum ItemRef<'ctx> {
    Type(&'ctx TypeDecl),
    Fun(&'ctx FunDecl),
    Global(&'ctx GlobalDecl),
    TraitDecl(&'ctx TraitDecl),
    TraitImpl(&'ctx TraitImpl),
}

/// A mutable reference to a translated item.
#[derive(
    Debug, EnumIsA, EnumAsGetters, VariantName, VariantIndexArity, Drive, DriveMut, DriveTwo,
)]
pub enum ItemRefMut<'ctx> {
    Type(&'ctx mut TypeDecl),
    Fun(&'ctx mut FunDecl),
    Global(&'ctx mut GlobalDecl),
    TraitDecl(&'ctx mut TraitDecl),
    TraitImpl(&'ctx mut TraitImpl),
}

impl ItemByVal {
    pub fn as_ref(&self) -> ItemRef<'_> {
        match self {
            Self::Type(d) => ItemRef::Type(d),
            Self::Fun(d) => ItemRef::Fun(d),
            Self::Global(d) => ItemRef::Global(d),
            Self::TraitDecl(d) => ItemRef::TraitDecl(d),
            Self::TraitImpl(d) => ItemRef::TraitImpl(d),
        }
    }
    pub fn as_mut(&mut self) -> ItemRefMut<'_> {
        match self {
            Self::Type(d) => ItemRefMut::Type(d),
            Self::Fun(d) => ItemRefMut::Fun(d),
            Self::Global(d) => ItemRefMut::Global(d),
            Self::TraitDecl(d) => ItemRefMut::TraitDecl(d),
            Self::TraitImpl(d) => ItemRefMut::TraitImpl(d),
        }
    }
}

impl<'ctx> ItemRef<'ctx> {
    pub fn id(&self) -> ItemId {
        match self {
            ItemRef::Type(d) => d.def_id.into(),
            ItemRef::Fun(d) => d.def_id.into(),
            ItemRef::Global(d) => d.def_id.into(),
            ItemRef::TraitDecl(d) => d.def_id.into(),
            ItemRef::TraitImpl(d) => d.def_id.into(),
        }
    }

    pub fn to_owned(&self) -> ItemByVal {
        match *self {
            Self::Type(d) => ItemByVal::Type(d.clone()),
            Self::Fun(d) => ItemByVal::Fun(d.clone()),
            Self::Global(d) => ItemByVal::Global(d.clone()),
            Self::TraitDecl(d) => ItemByVal::TraitDecl(d.clone()),
            Self::TraitImpl(d) => ItemByVal::TraitImpl(d.clone()),
        }
    }

    pub fn item_meta(&self) -> &'ctx ItemMeta {
        match self {
            Self::Type(d) => &d.item_meta,
            Self::Fun(d) => &d.item_meta,
            Self::Global(d) => &d.item_meta,
            Self::TraitDecl(d) => &d.item_meta,
            Self::TraitImpl(d) => &d.item_meta,
        }
    }
    /// The generic parameters of this item.
    pub fn generic_params(&self) -> &'ctx GenericParams {
        match self {
            ItemRef::Type(d) => &d.generics,
            ItemRef::Fun(d) => &d.generics,
            ItemRef::Global(d) => &d.generics,
            ItemRef::TraitDecl(d) => &d.generics,
            ItemRef::TraitImpl(d) => &d.generics,
        }
    }

    /// See [`GenericParams::identity_args`].
    pub fn identity_args(&self) -> GenericArgs {
        self.generic_params().identity_args()
    }

    /// We can't implement `AstVisitable` because of the `'static` constraint, but it's ok because
    /// `ItemRef` isn't contained in any of our types.
    pub fn drive<V: VisitAst>(&self, visitor: &mut V) -> ControlFlow<V::Break> {
        match *self {
            ItemRef::Type(d) => visitor.visit(d),
            ItemRef::Fun(d) => visitor.visit(d),
            ItemRef::Global(d) => visitor.visit(d),
            ItemRef::TraitDecl(d) => visitor.visit(d),
            ItemRef::TraitImpl(d) => visitor.visit(d),
        }
    }

    /// Visit two items in lockstep.
    pub fn drive_two<V: ZipAst>(&self, other: &Self, visitor: &mut V) -> ControlFlow<V::Break> {
        /// Adapter needed because `ZipAst => Any => 'static` so `&'ctx X` can't be `ZipAst`.
        struct ItemRefZipVisitor<'a, V>(&'a mut V);

        impl<V: Visitor> Visitor for ItemRefZipVisitor<'_, V> {
            type Break = V::Break;
        }

        impl<'s, 'ctx, T: AstVisitable, V: ZipAst> VisitTwo<'s, &'ctx T> for ItemRefZipVisitor<'_, V> {
            fn visit(&mut self, left: &'s &'ctx T, right: &'s &'ctx T) -> ControlFlow<Self::Break> {
                self.0.visit(*left, *right)
            }
        }

        DriveTwo::drive_two_inner(self, other, &mut ItemRefZipVisitor(visitor))
    }

    /// Visit all occurrences of that type inside `self`, in pre-order traversal.
    pub fn dyn_visit<T: AstVisitable>(&self, f: impl FnMut(&T)) {
        match *self {
            ItemRef::Type(d) => d.dyn_visit(f),
            ItemRef::Fun(d) => d.dyn_visit(f),
            ItemRef::Global(d) => d.dyn_visit(f),
            ItemRef::TraitDecl(d) => d.dyn_visit(f),
            ItemRef::TraitImpl(d) => d.dyn_visit(f),
        }
    }
}

impl<'ctx> ItemRefMut<'ctx> {
    pub fn as_ref(&self) -> ItemRef<'_> {
        match self {
            ItemRefMut::Type(d) => ItemRef::Type(d),
            ItemRefMut::Fun(d) => ItemRef::Fun(d),
            ItemRefMut::Global(d) => ItemRef::Global(d),
            ItemRefMut::TraitDecl(d) => ItemRef::TraitDecl(d),
            ItemRefMut::TraitImpl(d) => ItemRef::TraitImpl(d),
        }
    }
    pub fn reborrow(&mut self) -> ItemRefMut<'_> {
        match self {
            ItemRefMut::Type(d) => ItemRefMut::Type(d),
            ItemRefMut::Fun(d) => ItemRefMut::Fun(d),
            ItemRefMut::Global(d) => ItemRefMut::Global(d),
            ItemRefMut::TraitDecl(d) => ItemRefMut::TraitDecl(d),
            ItemRefMut::TraitImpl(d) => ItemRefMut::TraitImpl(d),
        }
    }

    pub fn set_id(&mut self, id: ItemId) {
        match (self, id) {
            (Self::Type(d), ItemId::Type(id)) => d.def_id = id,
            (Self::Fun(d), ItemId::Fun(id)) => d.def_id = id,
            (Self::Global(d), ItemId::Global(id)) => d.def_id = id,
            (Self::TraitDecl(d), ItemId::TraitDecl(id)) => d.def_id = id,
            (Self::TraitImpl(d), ItemId::TraitImpl(id)) => d.def_id = id,
            _ => unreachable!(),
        }
    }

    pub fn item_meta(&mut self) -> &mut ItemMeta {
        match self {
            Self::Type(d) => &mut d.item_meta,
            Self::Fun(d) => &mut d.item_meta,
            Self::Global(d) => &mut d.item_meta,
            Self::TraitDecl(d) => &mut d.item_meta,
            Self::TraitImpl(d) => &mut d.item_meta,
        }
    }
    /// The generic parameters of this item.
    pub fn generic_params(&mut self) -> &mut GenericParams {
        match self {
            ItemRefMut::Type(d) => &mut d.generics,
            ItemRefMut::Fun(d) => &mut d.generics,
            ItemRefMut::Global(d) => &mut d.generics,
            ItemRefMut::TraitDecl(d) => &mut d.generics,
            ItemRefMut::TraitImpl(d) => &mut d.generics,
        }
    }

    /// We can't implement `AstVisitable` because of the `'static` constraint, but it's ok because
    /// `ItemRefMut` isn't contained in any of our types.
    pub fn drive_mut<V: VisitAstMut>(&mut self, visitor: &mut V) -> ControlFlow<V::Break> {
        match self {
            ItemRefMut::Type(d) => visitor.visit(*d),
            ItemRefMut::Fun(d) => visitor.visit(*d),
            ItemRefMut::Global(d) => visitor.visit(*d),
            ItemRefMut::TraitDecl(d) => visitor.visit(*d),
            ItemRefMut::TraitImpl(d) => visitor.visit(*d),
        }
    }

    /// Visit all occurrences of that type inside `self`, in pre-order traversal.
    pub fn dyn_visit_mut<T: AstVisitable>(&mut self, f: impl FnMut(&mut T)) {
        match self {
            ItemRefMut::Type(d) => d.dyn_visit_mut(f),
            ItemRefMut::Fun(d) => d.dyn_visit_mut(f),
            ItemRefMut::Global(d) => d.dyn_visit_mut(f),
            ItemRefMut::TraitDecl(d) => d.dyn_visit_mut(f),
            ItemRefMut::TraitImpl(d) => d.dyn_visit_mut(f),
        }
    }
}
