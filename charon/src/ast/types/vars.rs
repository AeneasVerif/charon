//! Type-level variables. There are 4 kinds of variables at the type-level: regions, types, const
//! generics and trait clauses. The relevant definitions are in this module.
use derive_visitor::{Drive, DriveMut, Event, Visitor, VisitorMut};
use serde::{Deserialize, Serialize};

use crate::ast::*;

/// The index of a binder, counting from the innermost. See [`DeBruijnVar`] for details.
#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize,
    Drive,
    DriveMut,
)]
#[serde(transparent)]
#[drive(skip)]
pub struct DeBruijnId {
    pub index: usize,
}

/// Type-level variable.
///
/// Variables are bound in groups. Each item has a top-level binding group in its `generic_params`
/// field, and then inner binders are possible using the `RegionBinder<T>` type. Each variable is
/// linked to exactly one binder. The `Id` then identifies the specific variable among all those
/// bound in that group.
///
/// We distinguish the top-level (item-level) binder from others: a `Free` variable indicates a
/// variable bound at the item level; a `Bound` variable indicates a variable bound at an inner
/// binder, using a de Bruijn index (i.e. counting binders from the innermost out).
///
/// This distinction is not necessary (we could use bound variables only) but is practical.
///
/// For instance, we have the following:
/// ```text
/// fn f<'a, 'b>(x: for<'c> fn(&'b u8, &'c u16, for<'d> fn(&'b u32, &'c u64, &'d u128)) -> u64) {}
///      ^^^^^^         ^^       ^       ^          ^^       ^        ^        ^
///        |       inner binder  |       |     inner binder  |        |        |
///  top-level binder            |       |                   |        |        |
///                           Free(b)    |                Free(b)     |     Bound(0, d)
///                                      |                            |
///                                  Bound(0, c)                 Bound(1, c)
/// ```
///
/// At the moment only region variables can be bound in a non-top-level binder.
#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum DeBruijnVar<Id> {
    /// A variable attached to the nth binder, counting from the innermost.
    Bound(DeBruijnId, Id),
    /// A variable attached to the outermost binder (the one on the item).
    Free(Id),
}

// We need to manipulate a lot of indices for the types, variables, definitions, etc. In order not
// to confuse them, we define an index type for every one of them (which is just a struct with a
// unique usize field), together with some utilities like a fresh index generator, using the
// `generate_index_type` macro.
generate_index_type!(RegionId, "Region");
generate_index_type!(TypeVarId, "T");
generate_index_type!(ConstGenericVarId, "Const");
generate_index_type!(TraitClauseId, "TraitClause");

/// A type variable in a signature or binder.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct TypeVar {
    /// Index identifying the variable among other variables bound at the same level.
    pub index: TypeVarId,
    /// Variable name
    #[drive(skip)]
    pub name: String,
}

/// A region variable in a signature or binder.
#[derive(
    Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Drive, DriveMut,
)]
pub struct RegionVar {
    /// Index identifying the variable among other variables bound at the same level.
    pub index: RegionId,
    /// Region name
    #[drive(skip)]
    pub name: Option<String>,
}

/// A const generic variable in a signature or binder.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct ConstGenericVar {
    /// Index identifying the variable among other variables bound at the same level.
    pub index: ConstGenericVarId,
    /// Const generic name
    #[drive(skip)]
    pub name: String,
    /// Type of the const generic
    pub ty: LiteralTy,
}

/// A trait predicate in a signature, of the form `Type: Trait<Args>`. This functions like a
/// variable binder, to which variables of the form `TraitRefKind::Clause` can refer to.
#[derive(Debug, Clone, Hash, Serialize, Deserialize, Drive, DriveMut)]
pub struct TraitClause {
    /// Index identifying the clause among other clauses bound at the same level.
    pub clause_id: TraitClauseId,
    // TODO: does not need to be an option.
    pub span: Option<Span>,
    /// Where the predicate was written, relative to the item that requires it.
    #[charon::opaque]
    #[drive(skip)]
    pub origin: PredicateOrigin,
    /// The trait that is implemented.
    #[charon::rename("trait")]
    pub trait_: PolyTraitDeclRef,
}

pub type RegionDbVar = DeBruijnVar<RegionId>;
pub type TypeDbVar = DeBruijnVar<TypeVarId>;
pub type ConstGenericDbVar = DeBruijnVar<ConstGenericVarId>;
pub type ClauseDbVar = DeBruijnVar<TraitClauseId>;

impl DeBruijnId {
    pub fn zero() -> Self {
        DeBruijnId { index: 0 }
    }

    pub fn one() -> Self {
        DeBruijnId { index: 1 }
    }

    pub fn new(index: usize) -> Self {
        DeBruijnId { index }
    }

    pub fn is_zero(&self) -> bool {
        self.index == 0
    }

    pub fn incr(&self) -> Self {
        DeBruijnId {
            index: self.index + 1,
        }
    }

    pub fn decr(&self) -> Self {
        DeBruijnId {
            index: self.index - 1,
        }
    }

    pub fn plus(&self, delta: Self) -> Self {
        DeBruijnId {
            index: self.index + delta.index,
        }
    }

    pub fn sub(&self, delta: Self) -> Option<Self> {
        Some(DeBruijnId {
            index: self.index.checked_sub(delta.index)?,
        })
    }
}

impl<Id> DeBruijnVar<Id>
where
    Id: Copy,
{
    pub fn new_at_zero(id: Id) -> Self {
        DeBruijnVar::Bound(DeBruijnId::new(0), id)
    }

    pub fn free(id: Id) -> Self {
        DeBruijnVar::Free(id)
    }

    pub fn bound(index: DeBruijnId, id: Id) -> Self {
        DeBruijnVar::Bound(index, id)
    }

    pub fn incr(&self) -> Self {
        match *self {
            DeBruijnVar::Bound(dbid, varid) => DeBruijnVar::Bound(dbid.incr(), varid),
            DeBruijnVar::Free(varid) => DeBruijnVar::Free(varid),
        }
    }

    pub fn decr(&self) -> Self {
        match *self {
            DeBruijnVar::Bound(dbid, varid) => DeBruijnVar::Bound(dbid.decr(), varid),
            DeBruijnVar::Free(varid) => DeBruijnVar::Free(varid),
        }
    }

    /// Returns the variable id if it is bound as the given depth.
    pub fn bound_at_depth(&self, depth: DeBruijnId) -> Option<Id> {
        match *self {
            DeBruijnVar::Bound(dbid, varid) if dbid == depth => Some(varid),
            _ => None,
        }
    }

    /// Move the variable out of `depth` binders. Returns `None` if the variable is bound in one of
    /// these `depth` binders.
    pub fn move_out_from_depth(&self, depth: DeBruijnId) -> Option<Self> {
        Some(match *self {
            DeBruijnVar::Bound(dbid, varid) => DeBruijnVar::Bound(dbid.sub(depth)?, varid),
            DeBruijnVar::Free(_) => *self,
        })
    }

    /// Move under `depth` binders.
    pub fn move_under_binders(&self, depth: DeBruijnId) -> Self {
        match *self {
            DeBruijnVar::Bound(dbid, varid) => DeBruijnVar::Bound(dbid.plus(depth), varid),
            DeBruijnVar::Free(_) => *self,
        }
    }
}

impl TypeVar {
    pub fn new(index: TypeVarId, name: String) -> TypeVar {
        TypeVar { index, name }
    }
}

impl Default for DeBruijnId {
    fn default() -> Self {
        Self::zero()
    }
}

// The derive macro doesn't handle generics.
impl<Id: Drive> Drive for DeBruijnVar<Id> {
    fn drive<V: Visitor>(&self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        match self {
            DeBruijnVar::Bound(x, y) => {
                x.drive(visitor);
                y.drive(visitor);
            }
            DeBruijnVar::Free(x) => {
                x.drive(visitor);
            }
        }
        visitor.visit(self, Event::Exit);
    }
}

impl<Id: DriveMut> DriveMut for DeBruijnVar<Id> {
    fn drive_mut<V: VisitorMut>(&mut self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        match self {
            DeBruijnVar::Bound(x, y) => {
                x.drive_mut(visitor);
                y.drive_mut(visitor);
            }
            DeBruijnVar::Free(x) => {
                x.drive_mut(visitor);
            }
        }
        visitor.visit(self, Event::Exit);
    }
}
