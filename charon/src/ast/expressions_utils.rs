//! This file groups everything which is linked to implementations about [crate::expressions]
use crate::ast::*;
use crate::ids::Vector;

impl Place {
    pub fn new(var_id: VarId) -> Place {
        Place {
            var_id,
            projection: Vec::new(),
        }
    }

    /// Whether this place corresponds to a local variable without any projections.
    pub fn is_local(&self) -> bool {
        self.projection.is_empty()
    }

    /// If this place corresponds to an unprojected local, return the variable id.
    pub fn as_local(&self) -> Option<VarId> {
        self.projection.is_empty().then_some(self.var_id)
    }

    pub fn as_projection(&self) -> Option<(Self, &ProjectionElem)> {
        match self.projection.as_slice() {
            [] => None,
            [rest @ .., p] => Some((
                Place {
                    var_id: self.var_id,
                    projection: rest.to_vec(),
                },
                p,
            )),
        }
    }

    pub fn var_id(&self) -> VarId {
        self.var_id
    }

    pub fn project(mut self, elem: ProjectionElem) -> Self {
        self.projection.push(elem);
        self
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

impl Place {
    /// Compute the type of a place.
    pub fn ty(
        &self,
        type_decls: &Vector<TypeDeclId, TypeDecl>,
        locals: &Vector<VarId, Var>,
    ) -> Result<Ty, ()> {
        // Lookup the local
        let mut cur_ty = locals.get(self.var_id).ok_or(())?.ty.clone();

        // Apply the projection
        for pe in &self.projection {
            cur_ty = pe.project_type(type_decls, &cur_ty)?;
        }

        Ok(cur_ty)
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
                    | Arrow(..) => {
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
                        assert!(generics.regions.len() == type_decl.generics.regions.len());
                        assert!(generics.types.len() == type_decl.generics.types.len());
                        assert!(
                            generics.const_generics.len()
                                == type_decl.generics.const_generics.len()
                        );
                        assert!(
                            generics.trait_refs.len() == type_decl.generics.trait_clauses.len()
                        );
                        use TypeDeclKind::*;
                        match &type_decl.kind {
                            Struct(fields) | Union(fields) => {
                                if variant_id.is_some() {
                                    return Err(());
                                };
                                let mut ty = fields.get(*field_id).ok_or(())?.ty.clone();
                                ty.substitute(generics);
                                ty
                            }
                            Enum(variants) => {
                                let variant_id = variant_id.ok_or(())?;
                                let variant = variants.get(variant_id).ok_or(())?;
                                let mut ty = variant.fields.get(*field_id).ok_or(())?.ty.clone();
                                ty.substitute(generics);
                                ty
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
                    ClosureState => return Err(()),
                }
            }
            Index { ty, .. } | Subslice { ty, .. } => {
                let expected_ty = ty.as_array_or_slice().ok_or(())?;
                let ty = ty.as_array_or_slice().ok_or(())?;
                // Sanity check: ensure we're using the same types.
                if expected_ty == ty {
                    ty.clone()
                } else {
                    return Err(());
                }
            }
        })
    }
}
