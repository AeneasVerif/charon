//! This file groups everything which is linked to implementations about [crate::expressions]
use crate::ast::*;
use crate::ids::Vector;

impl Place {
    pub fn new(local_id: LocalId, ty: Ty) -> Place {
        Place {
            kind: PlaceKind::Local(local_id),
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
    pub fn var_id(&self) -> LocalId {
        self.local_id()
    }
    pub fn local_id(&self) -> LocalId {
        match &self.kind {
            PlaceKind::Local(var_id) => *var_id,
            PlaceKind::Projection(subplace, _) => subplace.local_id(),
        }
    }

    pub fn project(self, elem: ProjectionElem, ty: Ty) -> Self {
        Self {
            kind: PlaceKind::Projection(Box::new(self), elem),
            ty,
        }
    }

    pub fn projections<'a>(&'a self) -> impl Iterator<Item = &'a ProjectionElem> {
        let mut place = self;
        std::iter::from_fn(move || {
            let (new_place, proj) = place.as_projection()?;
            place = new_place;
            Some(proj)
        })
    }
}

impl Rvalue {
    pub fn unit_value() -> Self {
        Rvalue::Aggregate(
            AggregateKind::Adt(
                TypeId::Tuple,
                None,
                None,
                Box::new(GenericArgs::empty(GenericsSource::Builtin)),
            ),
            Vec::new(),
        )
    }
}

impl BorrowKind {
    pub fn mutable(x: bool) -> Self {
        if x {
            Self::Mut
        } else {
            Self::Shared
        }
    }
}

impl ProjectionElem {
    /// Compute the type obtained when applying the current projection to a place of type `ty`.
    pub fn project_type(
        &self,
        type_decls: &Vector<TypeDeclId, TypeDecl>,
        ty: &Ty,
    ) -> Result<Ty, ()> {
        use ProjectionElem::*;
        Ok(match self {
            Deref => {
                use TyKind::*;
                match ty.kind() {
                    Ref(_, ty, _) | RawPtr(ty, _) => ty.clone(),
                    Adt(TypeId::Builtin(BuiltinTy::Box), args) => {
                        args.types.get(TypeVarId::new(0)).unwrap().clone()
                    }
                    Adt(..) | TypeVar(_) | Literal(_) | Never | TraitType(..) | DynTrait(_)
                    | Arrow(..) | Error(..) => {
                        // Type error
                        return Err(());
                    }
                }
            }
            Field(pkind, field_id) => {
                // Lookup the type decl
                use FieldProjKind::*;
                match pkind {
                    Adt(type_decl_id, variant_id) => {
                        // Can fail if the type declaration was not translated.
                        let type_decl = type_decls.get(*type_decl_id).ok_or(())?;
                        let (type_id, generics) = ty.as_adt().ok_or(())?;
                        assert!(TypeId::Adt(*type_decl_id) == type_id);
                        use TypeDeclKind::*;
                        match &type_decl.kind {
                            Struct(fields, _) | Union(fields) => {
                                if variant_id.is_some() {
                                    return Err(());
                                };
                                fields
                                    .get(*field_id)
                                    .ok_or(())?
                                    .ty
                                    .clone()
                                    .substitute(generics)
                            }
                            Enum(variants) => {
                                let variant_id = variant_id.ok_or(())?;
                                let variant = variants.get(variant_id).ok_or(())?;
                                variant
                                    .fields
                                    .get(*field_id)
                                    .ok_or(())?
                                    .ty
                                    .clone()
                                    .substitute(generics)
                            }
                            Opaque | Alias(_) | Error(_) => return Err(()),
                        }
                    }
                    Tuple(_) => ty
                        .as_tuple()
                        .ok_or(())?
                        .get(TypeVarId::from(usize::from(*field_id)))
                        .ok_or(())?
                        .clone(),
                }
            }
            Index { .. } | Subslice { .. } => ty.as_array_or_slice().ok_or(())?.clone(),
        })
    }
}
