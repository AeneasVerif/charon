use std::{cmp::max, collections::HashMap};

use either::Either;
use serde::Serialize;

use crate::ast::{
    BuiltinTy, ByteCount, Field, FieldId, GenericParams, Layout, TranslatedCrate, Ty, TyKind,
    TypeDeclKind, TypeDeclRef, TypeId, TypeVarId, VariantLayout, Vector,
};

type GenericCtx<'a> = Option<&'a GenericParams>;

/// A utility to compute/lookup layouts of types from the crate's data.
/// Uses memoization to not re-compute already requested type layouts.
/// Should be constructed exactly once and kept around as long as the crate is used.
///
/// WARNING: Using this will lead to leaked memory to guarantee that computed layouts stay available.
/// Since any crate should only have finitely many types, the memory usage is bounded.
pub struct LayoutComputer<'a> {
    memoized_layouts: HashMap<(Ty, Option<GenericParams>), Either<&'a Layout, LayoutHint>>,
    krate: &'a TranslatedCrate,
}

// TODO: use `repr` information

/// Minimal information about a type's layout that can be known without
/// querying the rustc type layout algorithm.
#[derive(Debug, Clone, Copy, Serialize)]
pub struct LayoutHint {
    /// The minimal size of the type.
    ///
    /// Includes the minimal sizes of all its fields (if known), but doesn't take
    /// alignment and possible padding, or wide pointers into consideration.
    pub min_size: ByteCount,
    /// The minimal alignment.
    ///
    /// Corresponds to the greatest known alignment of the types fields.
    pub min_alignment: ByteCount,
    /// Whether thy type might be uninhabited.
    /// This can be the case if there are type variables as parameters that
    /// have influence on the layout of the type.
    ///
    /// Will only be set to false, if its guaranteed that it is inhabited.
    pub possibly_uninhabited: bool,
}

impl<'a> LayoutComputer<'a> {
    pub fn new<'b: 'a>(krate: &'b TranslatedCrate) -> Self {
        Self {
            memoized_layouts: HashMap::new(),
            krate,
        }
    }

    /// Compute the layout of a tuple as precise as possible.
    ///
    /// If the elements have different sizes and thus might need padding,
    /// it returns a hint, otherwise the precise layout.
    fn get_layout_of_tuple<'c, 't>(
        &'c mut self,
        type_decl_ref: &'t TypeDeclRef,
        generic_ctx: GenericCtx,
    ) -> Option<Either<&'a Layout, LayoutHint>> {
        let mut total_min_size = 0;
        let mut max_align = 1;
        let mut uninhabited_part = false;
        let mut possibly_same_size = None;
        let mut must_have_same_size = true;

        for ty_arg in type_decl_ref.generics.types.iter() {
            uninhabited_part |= ty_arg.is_possibly_uninhabited();
            match self.get_layout_of(ty_arg, generic_ctx) {
                Some(Either::Left(l)) => {
                    if let Some(size) = l.size {
                        total_min_size += size;
                        match possibly_same_size {
                            Some(other_size) => {
                                if size != other_size {
                                    must_have_same_size = false;
                                }
                            }
                            None => possibly_same_size = Some(size),
                        }
                    }
                    if let Some(align) = l.align {
                        max_align = max(max_align, align);
                    }
                }
                Some(Either::Right(h)) => {
                    total_min_size += h.min_size;
                    max_align = max(max_align, h.min_alignment);
                    must_have_same_size = false;
                }
                None => (),
            }
        }
        // If all elements have the same size, there is cannot be any padding between the elements
        // and we are guaranteed to get a layout (we just don't know the order of elements).
        Some(
            if must_have_same_size && let Some(size) = possibly_same_size {
                let new_layout = Layout::mk_uniform_tuple(
                    size,
                    type_decl_ref.generics.types.elem_count(),
                    max_align,
                );
                let layout_ref = Box::leak(Box::new(new_layout));
                Either::Left(layout_ref)
            } else {
                Either::Right(LayoutHint {
                    min_size: total_min_size,
                    min_alignment: max_align,
                    possibly_uninhabited: uninhabited_part,
                })
            },
        )
    }

    /// Approximate a layout for a struct (or enum variant) based on the fields.
    fn compute_layout_from_fields(
        &mut self,
        fields: &Vector<FieldId, Field>,
        ty_var_map: &HashMap<TypeVarId, Ty>,
        generic_ctx: GenericCtx,
    ) -> Option<Either<&'a Layout, LayoutHint>> {
        let mut total_min_size = 0;
        let mut max_align = 1;
        let mut uninhabited_part = false;

        // If it is a new-type struct, we should be able to get a layout.
        if fields.elem_count() == 1 {
            let field = fields.get(FieldId::from_raw(0)).unwrap();
            let ty = if field.ty.is_type_var() {
                let id = field.ty.as_type_var().unwrap().get_raw();
                ty_var_map.get(id)?
            } else {
                &field.ty
            };

            match self.get_layout_of(ty, generic_ctx) {
                Some(Either::Left(l)) => {
                    // Simply exchange the field_offsets and variants.
                    let new_layout = Layout {
                        variant_layouts: [VariantLayout {
                            field_offsets: [0].into(),
                            uninhabited: false,
                            tag: None,
                        }]
                        .into(),
                        ..l.clone()
                    };
                    let layout_ref = Box::leak(Box::new(new_layout));
                    Some(Either::Left(layout_ref))
                }
                r => r,
            }
        } else {
            for field in fields {
                let ty = if field.ty.is_type_var() {
                    let id = field.ty.as_type_var().unwrap().get_raw();
                    ty_var_map.get(id)?
                } else {
                    &field.ty
                };

                uninhabited_part |= ty.is_possibly_uninhabited();
                match self.get_layout_of(ty, generic_ctx) {
                    Some(Either::Left(l)) => {
                        if let Some(size) = l.size {
                            total_min_size += size;
                        }
                        if let Some(align) = l.align {
                            max_align = max(max_align, align);
                        }
                    }
                    Some(Either::Right(h)) => {
                        total_min_size += h.min_size;
                        max_align = max(max_align, h.min_alignment);
                    }
                    None => (),
                }
            }
            Some(Either::Right(LayoutHint {
                min_size: total_min_size,
                min_alignment: max_align,
                possibly_uninhabited: uninhabited_part,
            }))
        }
    }

    /// Tries to compute a layout hint for otherwise generic ADTs with the given type arguments.
    ///
    /// Most of time, we can't compute a full layout due to potential reordering and padding bytes.
    fn get_layout_hint_for_generic_adt(
        &mut self,
        type_decl_ref: &TypeDeclRef,
    ) -> Option<Either<&'a Layout, LayoutHint>> {
        let generics = &*type_decl_ref.generics;
        let type_decl_id = type_decl_ref.id.as_adt()?;
        let type_decl = self.krate.type_decls.get(*type_decl_id)?;

        // If we certainly can't instantiate all relevant type parameters, fail.
        if generics.types.elem_count() != type_decl.generics.types.elem_count()
            || generics.types.iter().find(|ty| ty.is_type_var()).is_some()
        {
            return None;
        }

        // Map the generic type parameter variables to the given instantiations.
        let ty_var_map: HashMap<TypeVarId, Ty> = type_decl
            .generics
            .types
            .iter()
            .map(|ty_var| ty_var.index)
            .zip(generics.types.iter().cloned())
            .collect();

        match &type_decl.kind {
            TypeDeclKind::Struct(fields) => {
                self.compute_layout_from_fields(fields, &ty_var_map, None)
            }
            TypeDeclKind::Enum(variants) => {
                // Assume that there could be a niche and ignore the discriminant for the hint.
                let variant_layouts: Vec<Option<Either<&'a Layout, LayoutHint>>> = variants.iter().map(|variant| self.compute_layout_from_fields(&variant.fields, &ty_var_map,None)).collect();
                // If all variants have at least a layout hint, combine them.
                if variant_layouts.iter().all(|l| l.is_some()) {
                    let mut max_variant_size = 0;
                    let mut max_variant_align = 1;
                    let mut all_variants_inhabited = variants.elem_count() == 0;
                    for variant_layout in variant_layouts {
                        match variant_layout {
                            Some(Either::Left(l)) => {
                                all_variants_inhabited &= !l.uninhabited;
                                if let Some(size) = l.size {
                                    max_variant_size = max(max_variant_size,size);
                                }
                                if let Some(align) = l.align {
                                    max_variant_align = max(max_variant_align, align);
                                }
                            }
                            Some(Either::Right(h)) => {
                                max_variant_size = max(max_variant_size,h.min_size);
                                max_variant_align = max(max_variant_align, h.min_alignment);
                                all_variants_inhabited &= !h.possibly_uninhabited;
                            }
                            None => (),
                        };
                    }
                    Some(Either::Right(LayoutHint {
                        min_size: max_variant_size,
                        min_alignment: max_variant_align,
                        // Enums are only considered uninhabited if they have no variants or all are uninhabited.
                        possibly_uninhabited: all_variants_inhabited,
                    }))
                } else {
                    None
                }
            },
            TypeDeclKind::Union(_) // No idea about unions
            | TypeDeclKind::Opaque // TODO: maybe hardcode layouts for some opaque types from std?
            | TypeDeclKind::Alias(_)
            | TypeDeclKind::Error(_) => None,
        }
    }

    /// Computes the layout of pointers.
    ///
    /// Tries to use information about whether the pointee is sized,
    /// if it's a type variable.
    fn get_layout_of_ptr_type<'c, 't>(
        &'c mut self,
        pointee: &'t Ty,
        generic_ctx: GenericCtx,
    ) -> Either<&'a Layout, LayoutHint> {
        match pointee.needs_metadata(&self.krate, generic_ctx) {
            Some(true) => {
                let new_layout = Layout::mk_ptr_layout_with_metadata(
                    self.krate.target_information.target_pointer_size,
                );
                let layout_ref = Box::leak(Box::new(new_layout));
                Either::Left(layout_ref)
            }
            Some(false) => {
                let new_layout = Layout::mk_ptr_layout_wo_metadata(
                    self.krate.target_information.target_pointer_size,
                );
                let layout_ref = Box::leak(Box::new(new_layout));
                Either::Left(layout_ref)
            }
            None => Either::Right(LayoutHint {
                min_size: self.krate.target_information.target_pointer_size,
                min_alignment: self.krate.target_information.target_pointer_size,
                possibly_uninhabited: false,
            }),
        }
    }

    /// Computes or looks up layout of given type if possible or tries to produce a layout hint instead.
    ///
    /// If the layout was not already available, it will be computed and leaked to guarantee
    /// that it stays available.
    ///
    /// The generic context is used to obtain more information about the type and should correspond
    /// to where the type occurs, e.g. the generic context of a function signature for one of its argument's types.
    pub fn get_layout_of<'c, 't>(
        &'c mut self,
        ty: &'t Ty,
        generic_ctx: GenericCtx<'_>,
    ) -> Option<Either<&'a Layout, LayoutHint>> {
        // Check memoization.
        let key = (ty.clone(), generic_ctx.cloned());
        if let Some(layout) = self.memoized_layouts.get(&key) {
            return Some(*layout);
        }

        let res: Option<Either<&'a Layout, LayoutHint>> = match ty {
            TyKind::Adt(type_decl_ref) => {
                match type_decl_ref.id {
                    TypeId::Adt(type_decl_id) => self
                        .krate
                        .type_decls
                        .get(type_decl_id)
                        .unwrap()
                        .layout
                        .as_ref()
                        .map(|l| Either::Left(l))
                        .or_else(|| self.get_layout_hint_for_generic_adt(type_decl_ref)),
                    TypeId::Tuple => {
                        if ty.is_unit() {
                            let new_layout = Layout::mk_1zst_layout();
                            let layout_ref = Box::leak(Box::new(new_layout));
                            Some(Either::Left(layout_ref))
                        } else {
                            self.get_layout_of_tuple(type_decl_ref, generic_ctx)
                        }
                    }
                    TypeId::Builtin(builtin_ty) => {
                        match builtin_ty {
                            BuiltinTy::Box => {
                                // Box has only one relevant type parameters: the boxed type.
                                let boxed_ty =
                                    type_decl_ref.generics.types.get(TypeVarId::ZERO).unwrap();
                                Some(self.get_layout_of_ptr_type(boxed_ty, generic_ctx))
                            }
                            // Slices are non-sized and can be handled as such.
                            BuiltinTy::Slice | BuiltinTy::Str => {
                                let new_layout = Layout::mk_unsized_layout();
                                let layout_ref = Box::leak(Box::new(new_layout));
                                Some(Either::Left(layout_ref))
                            }
                            BuiltinTy::Array => None,
                        }
                    }
                }
            }
            TyKind::Literal(literal_ty) => {
                let size =
                    literal_ty.target_size(self.krate.target_information.target_pointer_size);
                let new_layout = Layout::mk_simple_layout(size as u64);
                let layout_ref = Box::leak(Box::new(new_layout));
                Some(Either::Left(layout_ref))
            }
            TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) => {
                Some(self.get_layout_of_ptr_type(ty, generic_ctx))
            }
            TyKind::DynTrait(_) => {
                let new_layout = Layout::mk_unsized_layout();
                let layout_ref = Box::leak(Box::new(new_layout));
                Some(Either::Left(layout_ref))
            }
            // We cannot get a layout for TypeVar, TraitType, Never, DynTrait, Error, FnPtr (probably?), and FnDef (probably?)
            _ => None,
        };

        // Update memoization.
        if let Some(layout) = res {
            self.memoized_layouts.insert(key, layout);
        }

        res
    }

    /// Checks whether the type is known to be a ZST.
    /// Computes the layout first if necessary.
    pub fn is_known_zst(&mut self, ty: &Ty) -> bool {
        // The generic context cannot change whether a type is a ZST.
        match self.get_layout_of(ty, None) {
            Some(Either::Left(l)) => {
                if let Some(size) = l.size {
                    size == 0
                } else {
                    false
                }
            }
            // Since the hint could have min_size == 0 but not be a ZST, we also return false for it.
            _ => false,
        }
    }

    /// Checks whether the type is known to be uninhabited.
    /// Computes the layout first if necessary.
    pub fn is_known_uninhabited(&mut self, ty: &Ty) -> bool {
        if ty.is_never() {
            true
        } else {
            // The generic context cannot change whether a type is uninhabited.
            match self.get_layout_of(ty, None) {
                Some(Either::Left(l)) => l.uninhabited,
                // Since the hint can only tell whether a type is guarantee to be inhabited,
                // we can never be sure that it is uninhabited.
                Some(Either::Right(_)) => false,
                None => false,
            }
        }
    }

    /// Checks whether the type is known to be inhabited.
    /// Computes the layout first if necessary.
    pub fn is_known_inhabited(&mut self, ty: &Ty) -> bool {
        if ty.is_never() {
            false
        } else {
            // The generic context cannot change whether a type is uninhabited.
            match self.get_layout_of(ty, None) {
                Some(Either::Left(l)) => !l.uninhabited,
                Some(Either::Right(h)) => !h.possibly_uninhabited,
                None => false,
            }
        }
    }
}
