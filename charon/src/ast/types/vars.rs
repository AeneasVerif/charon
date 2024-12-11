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
pub struct DeBruijnId {
    pub index: usize,
}

/// Bound region variable.
///
/// **Important**:
/// ==============
/// Similarly to what the Rust compiler does, we use De Bruijn indices to
/// identify *groups* of bound variables, and variable identifiers to
/// identity the variables inside the groups.
///
/// For instance, we have the following:
/// ```text
///                     we compute the De Bruijn indices from here
///                            VVVVVVVVVVVVVVVVVVVVVVV
/// fn f<'a, 'b>(x: for<'c> fn(&'a u8, &'b u16, &'c u32) -> u64) {}
///      ^^^^^^         ^^       ^       ^        ^
///        |      De Bruijn: 0   |       |        |
///  De Bruijn: 1                |       |        |
///                        De Bruijn: 1  |    De Bruijn: 0
///                           Var id: 0  |       Var id: 0
///                                      |
///                                De Bruijn: 1
///                                   Var id: 1
/// ```
#[derive(Debug, PartialEq, Eq, Copy, Clone, Hash, PartialOrd, Ord, Serialize, Deserialize)]
// TODO: translate toplevel lifetimes as free vars
pub enum DeBruijnVar<Id> {
    /// A variable attached to the nth binder, counting from the inside.
    Bound(DeBruijnId, Id),
    /// A variable attached to an implicit binder outside all other binders. This is not present in
    /// translated code, and only provided as a convenience for convenient variable manipulation.
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
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub struct TypeVar {
    /// Index identifying the variable among other variables bound at the same level.
    pub index: TypeVarId,
    /// Variable name
    pub name: String,
}

/// A region variable in a signature or binder.
#[derive(
    Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Hash, PartialOrd, Ord, Drive, DriveMut,
)]
pub struct RegionVar {
    /// Index identifying the variable among other variables bound at the same level.
    pub index: RegionId,
    /// Region name
    pub name: Option<String>,
}

/// A const generic variable in a signature or binder.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize, Drive, DriveMut)]
pub struct ConstGenericVar {
    /// Index identifying the variable among other variables bound at the same level.
    pub index: ConstGenericVarId,
    /// Const generic name
    pub name: String,
    /// Type of the const generic
    pub ty: LiteralTy,
}

/// A trait predicate in a signature, of the form `Type: Trait<Args>`. This functions like a
/// variable binder, to which variables of the form `TraitRefKind::Clause` can refer to.
#[derive(Debug, Clone, Serialize, Deserialize, Drive, DriveMut)]
pub struct TraitClause {
    /// Index identifying the clause among other clauses bound at the same level.
    pub clause_id: TraitClauseId,
    // TODO: does not need to be an option.
    pub span: Option<Span>,
    /// Where the predicate was written, relative to the item that requires it.
    #[charon::opaque]
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

    pub fn decr(&self) -> Self {
        match *self {
            DeBruijnVar::Bound(dbid, varid) => DeBruijnVar::Bound(dbid.decr(), varid),
            DeBruijnVar::Free(varid) => DeBruijnVar::Free(varid),
        }
    }

    pub fn bound_at_depth(&self, depth: DeBruijnId) -> Option<Id> {
        match *self {
            DeBruijnVar::Bound(dbid, varid) if dbid == depth => Some(varid),
            _ => None,
        }
    }
}

impl TypeVar {
    pub fn new(index: TypeVarId, name: String) -> TypeVar {
        TypeVar { index, name }
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
