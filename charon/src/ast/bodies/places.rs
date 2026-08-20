//! Implements expressions: paths, operands, rvalues, lvalues
use crate::ast::*;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::{EnumAsGetters, EnumIsA, EnumToGetters, VariantName};
use serde_state::{DeserializeState, SerializeState};

#[derive(
    Debug, PartialEq, Eq, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo,
)]
#[serde_state(state_implements = HashConsSerializerState)] // Avoid corecursive impls due to perfect derive
pub struct Place {
    pub kind: PlaceKind,
    pub ty: Ty,
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Place"))]
pub enum PlaceKind {
    /// A local variable in a function body.
    Local(LocalId),
    /// A subplace of a place.
    Projection(Box<Place>, ProjectionElem),
    /// A global (const or static).
    /// Not present in MIR; introduced in [simplify_constants.rs].
    Global(GlobalDeclRef),
}

/// Note that we don't have the equivalent of "downcasts".
/// Downcasts are actually necessary, for instance when initializing enumeration
/// values: the value is initially `Bottom`, and we need a way of knowing the
/// variant.
/// For example:
/// `((_0 as Right).0: T2) = move _1;`
/// In MIR, downcasts always happen before field projections: in our internal
/// language, we thus merge downcasts and field projections.
#[derive(
    Debug,
    PartialEq,
    Eq,
    Clone,
    EnumIsA,
    EnumAsGetters,
    EnumToGetters,
    VariantName,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum ProjectionElem {
    /// Dereference a shared/mutable reference, a box, or a raw pointer.
    Deref,
    /// Projection from ADTs (variants, structures).
    /// We allow projections to be used as left-values and right-values.
    /// We should never have projections to fields of symbolic variants (they
    /// should have been expanded before through a match).
    Field(FieldProjKind, FieldId),
    /// A built-in pointer (a reference, raw pointer, or `Box`) in Rust is always a fat pointer: it
    /// contains an address and metadata for the pointed-to place. This metadata is empty for sized
    /// types, it's the length for slices, and the vtable for `dyn Trait`.
    ///
    /// We consider such pointers to be like a struct with two fields; this represent access to the
    /// metadata "field".
    PtrMetadata,
    /// MIR imposes that the argument to an index projection be a local variable, meaning
    /// that even constant indices into arrays are let-bound as separate variables.
    /// We **eliminate** this variant in a micro-pass for LLBC.
    #[cfg_attr(feature = "charon_on_charon", charon::rename("ProjIndex"))]
    Index {
        offset: Box<Operand>,
        #[drive(skip)]
        from_end: bool,
    },
    /// Take a subslice of a slice or array. If `from_end` is `true` this is
    /// `slice[from..slice.len() - to]`, otherwise this is `slice[from..to]`.
    /// We **eliminate** this variant in a micro-pass for LLBC.
    Subslice {
        from: Box<Operand>,
        to: Box<Operand>,
        #[drive(skip)]
        from_end: bool,
    },
}

#[derive(
    Debug,
    PartialEq,
    Eq,
    Copy,
    Clone,
    EnumIsA,
    EnumAsGetters,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Proj"))]
pub enum FieldProjKind {
    Adt(TypeDeclId, Option<VariantId>),
    /// If we project from a tuple, the projection kind gives the arity of the tuple.
    #[drive(skip)]
    Tuple(usize),
}

impl Place {
    pub fn new(local_id: LocalId, ty: Ty) -> Place {
        Place {
            kind: PlaceKind::Local(local_id),
            ty,
        }
    }

    pub fn new_global(global: GlobalDeclRef, ty: Ty) -> Place {
        Place {
            kind: PlaceKind::Global(global),
            ty,
        }
    }

    pub fn ty(&self) -> &Ty {
        &self.ty
    }

    /// Whether this place corresponds to a local variable without any projections.
    pub fn is_local(&self) -> bool {
        self.as_local().is_some()
    }

    /// If this place corresponds to an unprojected local, return the variable id.
    pub fn as_local(&self) -> Option<LocalId> {
        self.kind.as_local().copied()
    }

    pub fn as_projection(&self) -> Option<(&Self, &ProjectionElem)> {
        self.kind.as_projection().map(|(pl, pj)| (pl.as_ref(), pj))
    }

    #[deprecated(note = "use `local_id` instead")]
    pub fn var_id(&self) -> Option<LocalId> {
        self.local_id()
    }
    pub fn local_id(&self) -> Option<LocalId> {
        match &self.kind {
            PlaceKind::Local(var_id) => Some(*var_id),
            PlaceKind::Projection(subplace, _) => subplace.local_id(),
            PlaceKind::Global(_) => None,
        }
    }

    pub fn project(self, elem: ProjectionElem, ty: Ty) -> Self {
        Self {
            kind: PlaceKind::Projection(Box::new(self), elem),
            ty,
        }
    }

    pub fn project_auto_ty(self, krate: &TranslatedCrate, proj: ProjectionElem) -> Option<Self> {
        Some(Place {
            ty: proj.project_type(krate, &self.ty)?,
            kind: PlaceKind::Projection(Box::new(self), proj),
        })
    }

    /// Dereferences the place. Panics if the type cannot be dereferenced.
    pub fn deref(self) -> Place {
        use TyKind::*;
        let proj_ty = match self.ty.kind() {
            Ref(_, ty, _) | RawPtr(ty, _) => ty.clone(),
            Adt(tref) if matches!(tref.id, TypeId::Builtin(BuiltinTy::Box)) => {
                tref.generics.types[0].clone()
            }
            Adt(..) | TypeVar(_) | Literal(_) | Never | TraitType(..) | DynTrait(..)
            | FnPtr(..) | FnDef(..) | PtrMetadata(..) | Array(..) | Slice(_) | Pattern(..)
            | Error(..) => {
                panic!("internal type error")
            }
        };
        Place {
            ty: proj_ty,
            kind: PlaceKind::Projection(Box::new(self), ProjectionElem::Deref),
        }
    }

    pub fn projections(&self) -> impl Iterator<Item = &ProjectionElem> {
        let mut place = self;
        std::iter::from_fn(move || {
            let (new_place, proj) = place.as_projection()?;
            place = new_place;
            Some(proj)
        })
    }
}

impl ProjectionElem {
    /// Compute the type obtained when applying the current projection to a place of type `ty`.
    pub fn project_type(&self, krate: &TranslatedCrate, ty: &Ty) -> Option<Ty> {
        use ProjectionElem::*;
        Some(match self {
            Deref => {
                use TyKind::*;
                match ty.kind() {
                    Ref(_, ty, _) | RawPtr(ty, _) => ty.clone(),
                    Adt(tref) if matches!(tref.id, TypeId::Builtin(BuiltinTy::Box)) => {
                        tref.generics.types[0].clone()
                    }
                    Adt(..) | TypeVar(_) | Literal(_) | Never | TraitType(..) | DynTrait(..)
                    | Array(..) | Slice(..) | FnPtr(..) | FnDef(..) | PtrMetadata(..)
                    | Pattern(..) | Error(..) => {
                        // Type error
                        return None;
                    }
                }
            }
            Field(pkind, field_id) => {
                // Lookup the type decl
                use FieldProjKind::*;
                match pkind {
                    Adt(type_decl_id, variant_id) => {
                        // Can fail if the type declaration was not translated.
                        let type_decl = krate.type_decls.get(*type_decl_id)?;
                        let tref = ty.as_adt()?;
                        assert!(TypeId::Adt(*type_decl_id) == tref.id);
                        use TypeDeclKind::*;
                        match &type_decl.kind {
                            Struct(fields) | Union(fields) => {
                                if variant_id.is_some() {
                                    return None;
                                };
                                fields.get(*field_id)?.ty.clone().substitute(&tref.generics)
                            }
                            Enum(variants) => {
                                let variant_id = (*variant_id)?;
                                let variant = variants.get(variant_id)?;
                                variant
                                    .fields
                                    .get(*field_id)?
                                    .ty
                                    .clone()
                                    .substitute(&tref.generics)
                            }
                            Opaque | Alias(_) | Error(_) => return None,
                        }
                    }
                    Tuple(_) => ty
                        .as_tuple()?
                        .get(TypeVarId::from(usize::from(*field_id)))?
                        .clone(),
                }
            }
            PtrMetadata => ty.get_ptr_metadata(krate).into_type(),
            Index { .. } | Subslice { .. } => ty.as_array_or_slice()?.clone(),
        })
    }
}
