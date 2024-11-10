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
    pub fn compute_projected_type(
        &self,
        type_decls: &Vector<TypeDeclId, TypeDecl>,
        locals: &Vector<VarId, Var>,
    ) -> Result<Ty, ()> {
        // Lookup the local
        let mut cur_ty = locals.get(self.var_id).ok_or(())?.ty.clone();

        // Apply the projection
        use ProjectionElem::*;
        for pe in &self.projection {
            cur_ty = match pe {
                Deref => {
                    use TyKind::*;
                    match cur_ty.kind() {
                        Ref(_, ty, _) | RawPtr(ty, _) => ty.clone(),
                        Adt(..) | TypeVar(_) | Literal(_) | Never | TraitType(..) | DynTrait(_)
                        | Arrow(..) => {
                            // Unreachable
                            return Err(());
                        }
                    }
                }
                Field(pkind, field_id) => {
                    // Lookup the type decl
                    use FieldProjKind::*;
                    match pkind {
                        Adt(type_decl_id, variant_id) => {
                            let type_decl = type_decls.get(*type_decl_id).ok_or(())?;
                            let (type_id, generics) = cur_ty.as_adt().ok_or(())?;
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
                                Struct(fields) => {
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
                                    let mut ty =
                                        variant.fields.get(*field_id).ok_or(())?.ty.clone();
                                    ty.substitute(generics);
                                    ty
                                }
                                Union(_) | Opaque | Alias(_) | Error(_) => return Err(()),
                            }
                        }
                        Tuple(_) => cur_ty
                            .as_tuple()
                            .ok_or(())?
                            .get(TypeVarId::from(usize::from(*field_id)))
                            .ok_or(())?
                            .clone(),
                        ClosureState => return Err(()),
                    }
                }
                Index { ty, .. } | Subslice { ty, .. } => {
                    // We could check that that the current type is compatible with
                    // the type of the
                    let cur_ty = cur_ty.as_array_or_slice().ok_or(())?;
                    let ty = ty.as_array_or_slice().ok_or(())?;
                    if cur_ty == ty {
                        ty.clone()
                    } else {
                        return Err(());
                    }
                }
            };
        }

        Ok(cur_ty)
    }
}
