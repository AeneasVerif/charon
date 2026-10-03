use super::*;

impl<T: mini::Target> TranslateCtx<'_, T> {
    pub(super) fn ty(&self, span: Span, ty: &Ty) -> Result<mini::Type> {
        Ok(match ty.kind() {
            TyKind::Scalar(ScalarTy::Integer(integer)) => mini::Type::Int(self.int_type(*integer)),
            TyKind::Scalar(ScalarTy::Bool) => mini::Type::Bool,
            TyKind::Scalar(ScalarTy::Char) => mini::Type::Int(mini::IntType {
                signed: mini::Signedness::Unsigned,
                size: mini_size(4),
            }),
            TyKind::Scalar(ScalarTy::Float(_)) => {
                raise!(span, "MiniRust has no floating-point types")
            }
            TyKind::Array(elem_ty, len, _) => mini::Type::Array {
                elem: mini::GcCow::new(self.ty(span, elem_ty)?),
                count: mini::Int::from(
                    len.as_usize_literal()
                        .ok_or("non-concrete array length")
                        .context(span)?,
                ),
            },
            TyKind::Slice(elem_ty, _) => mini::Type::Slice {
                elem: mini::GcCow::new(self.ty(span, elem_ty)?),
            },
            TyKind::Adt(tref) if tref.is_box() => {
                let pointee = ty
                    .builtin_deref(self.krate)
                    .ok_or("Box type is missing its pointee")
                    .context(span)?;
                mini::Type::Ptr(mini::PtrType::Box {
                    pointee: self.pointee_info(span, pointee)?,
                })
            }
            TyKind::Adt(tref) => self.adt_type(span, tref)?,
            TyKind::Ref(_, pointee, kind) => mini::Type::Ptr(mini::PtrType::Ref {
                mutbl: match kind {
                    RefKind::Mut => mini::Mutability::Mutable,
                    RefKind::Shared => mini::Mutability::Immutable,
                },
                pointee: self.pointee_info(span, pointee)?,
            }),
            TyKind::RawPtr(pointee, _) => mini::Type::Ptr(mini::PtrType::Raw {
                meta_kind: self.metadata_kind(span, pointee)?,
            }),
            TyKind::FnDef(_) => mini::unit_ty(),
            TyKind::FnPtr(_) => mini::Type::Ptr(mini::PtrType::FnPtr),
            TyKind::Never => mini::Type::Enum {
                variants: Default::default(),
                discriminant_ty: self.int_type(IntegerTy::Unsigned(UIntTy::U8)),
                discriminator: mini::Discriminator::Invalid,
                size: mini_size(0),
                align: mini_align(span, 1)?,
            },
            TyKind::Pattern(base, _) => self.ty(span, base)?,
            TyKind::PtrMetadata(pointee) => match self.metadata_kind(span, pointee)? {
                mini::PointerMetaKind::None => mini::unit_ty(),
                mini::PointerMetaKind::ElementCount => {
                    mini::Type::Int(self.int_type(IntegerTy::Unsigned(UIntTy::Usize)))
                }
                mini::PointerMetaKind::VTablePointer(trait_name) => {
                    mini::Type::Ptr(mini::PtrType::VTablePtr(trait_name))
                }
            },
            TyKind::DynTrait(_) => {
                // FIXME(minirust): support dyn Trait
                raise!(span, "MiniRust output does not support `dyn Trait`")
            }
            TyKind::TypeVar(_) | TyKind::TraitType(..) => {
                raise!(
                    span,
                    "MiniRust output requires a monomorphized crate: {}",
                    ty.with_ctx(&self.fmt)
                )
            }
            TyKind::Error(error) => raise!(span, "type error: {error}"),
        })
    }

    fn adt_type(&self, span: Span, tref: &TypeDeclRef) -> Result<mini::Type> {
        let tdecl = self
            .krate
            .type_decls
            .get(tref.id)
            .ok_or_else(|| format!("missing type declaration {}", tref.id.with_ctx(&self.fmt)))
            .context(span)?;
        let layout = tdecl
            .layout
            .get(self.target_name)
            .ok_or_else(|| {
                format!(
                    "missing layout for {}",
                    tdecl.item_meta.name.with_ctx(&self.fmt)
                )
            })
            .context(span)?;
        let decl_span = tdecl.item_meta.span;
        match layout.repr.align_modif {
            Some(AlignmentModifier::Pack(_)) => {
                raise!(decl_span, "MiniRust output does not support packed layouts")
            }
            Some(AlignmentModifier::Align(_)) => {
                raise!(
                    decl_span,
                    "MiniRust output does not support overaligned layouts"
                )
            }
            None => {}
        }
        Ok(match &tdecl.kind {
            TypeDeclKind::Struct(fields) => {
                let variant_layout = layout.variant_layouts[VariantId::ZERO].as_ref();
                self.tuple_type(
                    span,
                    fields,
                    variant_layout,
                    &layout.size,
                    &layout.align,
                    &tref.generics,
                )?
            }
            TypeDeclKind::Union(_) => {
                // let variant_layout = layout.variant_layouts[VariantId::ZERO].as_ref();
                // let fields = self.fields(span, fields, variant_layout)?;
                // // FIXME(minirust): compute the precise union chunks. Treating the complete
                // // allocation as one chunk preserves too much padding for some repr(C) unions.
                // mini::Type::Union {
                //     fields,
                //     chunks: ????
                //     size,
                //     align,
                // }
                raise!(
                    decl_span,
                    "MiniRust output does not support unions because we lack padding information"
                )
            }
            TypeDeclKind::Enum(variants) => {
                let size = mini_size(self.size(span, &layout.size)?);
                let align = mini_align(span, self.size(span, &layout.align)?)?;
                let discriminant_ty = self.int_type(
                    variants
                        .first()
                        .map(|variant| variant.discriminant.ty())
                        .unwrap_or(IntegerTy::Unsigned(UIntTy::U8)),
                );
                let mini_variants = variants
                    .iter_enumerated()
                    .map(|(id, variant)| -> Result<_> {
                        let variant_layout = layout.variant_layouts[id].as_ref();
                        let ty = self.tuple_type(
                            span,
                            &variant.fields,
                            variant_layout,
                            &layout.size,
                            &layout.align,
                            &tref.generics,
                        )?;
                        let tagger = variant_layout
                            .map(|layout| {
                                layout
                                    .tagger
                                    .iter()
                                    .map(|(offset, value)| {
                                        (
                                            mini_size(*offset),
                                            (self.int_type(value.ty()), mini_int(*value)),
                                        )
                                    })
                                    .collect()
                            })
                            .unwrap_or_default();
                        Ok((mini_int(variant.discriminant), mini::Variant { ty, tagger }))
                    })
                    .try_collect()?;
                let discriminator = if let Some(discriminator) = &layout.discriminator {
                    self.discriminator(span, variants, discriminator)?
                } else {
                    mini::Discriminator::Invalid
                };
                mini::Type::Enum {
                    variants: mini_variants,
                    discriminant_ty,
                    discriminator,
                    size,
                    align,
                }
            }
            TypeDeclKind::Alias(ty) => self.ty(span, &ty.clone().substitute(&tref.generics))?,
            TypeDeclKind::Opaque => {
                raise!(span, "opaque type is not representable in MiniRust")
            }
            TypeDeclKind::Error(error) => raise!(span, "type error: {error}"),
        })
    }

    fn tuple_type(
        &self,
        span: Span,
        fields: &IndexVec<FieldId, Field>,
        layout: Option<&VariantLayout>,
        size: &crate::ast::Size,
        align: &crate::ast::Size,
        generics: &GenericArgs,
    ) -> Result<mini::Type> {
        let mut sized_fields = mini::Fields::new();
        let mut head_align = mini::Align::ONE;
        let mut unsized_field = None;
        let mut tail_offset = None;
        for (id, field) in fields.iter_enumerated() {
            let ty = self.ty(span, &field.ty.clone().substitute(generics))?;
            let offset = match layout {
                Some(layout) => layout.field_offsets[id]
                    .chosen
                    .ok_or("missing field offset in ADT layout")
                    .context(span)?,
                // An elided enum variant can only contain zero-sized fields.
                None => 0,
            };
            match ty.layout::<T>() {
                mini::LayoutStrategy::Sized(_, field_align) => {
                    head_align = head_align.max(field_align);
                    sized_fields.push((mini_size(offset), ty));
                }
                _ => {
                    check!(
                        span,
                        id.index() + 1 == fields.len(),
                        "non-tail field is unsized"
                    );
                    unsized_field = Some(ty);
                    tail_offset = Some(offset);
                }
            }
        }
        let (end, head_align) = match tail_offset {
            // Include any padding before the tail in the head.
            Some(offset) => (mini_size(offset), head_align),
            None => (
                mini_size(self.size(span, size)?),
                mini_align(span, self.size(span, align)?)?,
            ),
        };
        Ok(mini::Type::Tuple {
            sized_fields,
            sized_head_layout: mini::TupleHeadLayout {
                end,
                align: head_align,
                packed_align: None,
            },
            unsized_field: mini::GcCow::new(unsized_field),
        })
    }

    fn discriminator(
        &self,
        span: Span,
        variants: &IndexVec<VariantId, Variant>,
        value: &Discriminator,
    ) -> Result<mini::Discriminator> {
        Ok(match value {
            Discriminator::Known(variant) => {
                mini::Discriminator::Known(mini_int(variants[*variant].discriminant))
            }
            Discriminator::Invalid => mini::Discriminator::Invalid,
            Discriminator::Branch {
                offset,
                int_ty,
                children,
                fallback,
            } => mini::Discriminator::Branch {
                offset: mini_size(
                    offset
                        .chosen
                        .ok_or("non-concrete discriminator offset")
                        .context(span)?,
                ),
                value_type: self.int_type(*int_ty),
                fallback: mini::GcCow::new(self.discriminator(span, variants, fallback)?),
                children: children
                    .iter()
                    .map(|(range, child)| -> Result<_> {
                        let start = mini_int(*range.start());
                        let end = mini_int(*range.end()) + 1;
                        Ok(((start, end), self.discriminator(span, variants, child)?))
                    })
                    .try_collect()?,
            },
        })
    }

    pub(super) fn variant_discriminant(
        &self,
        span: Span,
        ty: &Ty,
        variant: VariantId,
    ) -> Result<mini::Int> {
        let tref = ty.as_adt().ok_or("variant on non-ADT").context(span)?;
        self.variant_discriminant_for_tref(span, tref, variant)
    }

    pub(super) fn variant_discriminant_for_tref(
        &self,
        span: Span,
        tref: &TypeDeclRef,
        variant: VariantId,
    ) -> Result<mini::Int> {
        let tdecl = self
            .krate
            .type_decls
            .get(tref.id)
            .ok_or("missing enum declaration")
            .context(span)?;
        let variants = tdecl
            .kind
            .as_enum()
            .ok_or("variant on non-enum")
            .context(span)?;
        Ok(mini_int(variants[variant].discriminant))
    }

    pub(super) fn pointee_info(&self, span: Span, ty: &Ty) -> Result<mini::PointeeInfo> {
        let mini_ty = self.ty(span, ty)?;
        let layout = mini_ty.layout::<T>();
        let inhabited = !ty
            .inhabited_predicate(self.krate, Some(self.target_name))
            .always_false();
        let unsafe_cells = self.unsafe_cell_strategy(span, ty)?;
        let (freeze, unpin) = self.freeze_and_unpin(span, ty)?;
        Ok(mini::PointeeInfo {
            layout,
            inhabited,
            unsafe_cells,
            freeze,
            unpin,
        })
    }

    fn freeze_and_unpin(&self, span: Span, ty: &Ty) -> Result<(bool, bool)> {
        Ok(match ty.kind() {
            TyKind::Array(element, ..) | TyKind::Slice(element, ..) => {
                self.freeze_and_unpin(span, element)?
            }
            TyKind::Adt(tref) => {
                let marker_traits = self
                    .krate
                    .type_decls
                    .get(tref.id)
                    .and_then(|decl| decl.marker_traits.as_deref())
                    .ok_or("missing marker-trait information for this type")
                    .context(span)?;
                (marker_traits.is_freeze, marker_traits.is_unpin)
            }
            TyKind::Pattern(ty, _) => self.freeze_and_unpin(span, ty)?,
            TyKind::TypeVar(_) | TyKind::TraitType(..) => raise!(
                span,
                "MiniRust output requires a monomorphized crate: {}",
                ty.with_ctx(&self.fmt)
            ),
            TyKind::DynTrait(_) => raise!(span, "MiniRust output does not support `dyn Trait`"),
            TyKind::Error(error) => raise!(span, "type error: {error}"),
            TyKind::Scalar(_)
            | TyKind::Ref(..)
            | TyKind::RawPtr(..)
            | TyKind::FnDef(_)
            | TyKind::FnPtr(_)
            | TyKind::Never
            | TyKind::PtrMetadata(_) => (true, true),
        })
    }

    fn unsafe_cell_strategy(&self, span: Span, ty: &Ty) -> Result<mini::UnsafeCellStrategy> {
        /// Strategy that labels every byte as a cell.
        fn all_cells_strategy(layout: mini::LayoutStrategy) -> mini::UnsafeCellStrategy {
            let whole_range = |size| {
                if size == mini::Size::ZERO {
                    mini::List::new()
                } else {
                    [(mini::Size::ZERO, size)].into_iter().collect()
                }
            };
            match layout {
                mini::LayoutStrategy::Sized(size, _) => mini::UnsafeCellStrategy::Sized {
                    cells: whole_range(size),
                },
                mini::LayoutStrategy::Slice(element_size, _) => mini::UnsafeCellStrategy::Slice {
                    element_cells: whole_range(element_size),
                },
                mini::LayoutStrategy::Tuple { head, tail } => mini::UnsafeCellStrategy::Tuple {
                    head_cells: whole_range(head.end),
                    tail_cells: mini::GcCow::new(all_cells_strategy(tail.extract())),
                },
                mini::LayoutStrategy::TraitObject(_) => mini::UnsafeCellStrategy::TraitObject,
            }
        }

        Ok(match ty.kind() {
            TyKind::Adt(tref) => {
                let tdecl = self
                    .krate
                    .type_decls
                    .get(tref.id)
                    .ok_or("untranslated type decl")
                    .context(span)?;
                if matches!(
                    tdecl.item_meta.lang_item.as_ref(),
                    Some(LangItem::UnsafeCell)
                ) {
                    let mini_ty = self.ty(span, ty)?;
                    all_cells_strategy(mini_ty.layout::<T>())
                } else {
                    let layout = tdecl
                        .layout
                        .get(self.target_name)
                        .ok_or("missing layout for ADT")
                        .context(span)?;

                    let mut sized_cells: Vec<(mini::Size, mini::Size)> = Vec::new();
                    let mut tail_cells = None;
                    // Add the fields of this variant.
                    let mut add_fields = |fields: &IndexVec<FieldId, Field>,
                                          variant_layout: Option<&VariantLayout>|
                     -> Result<()> {
                        for (field_id, field) in fields.iter_enumerated() {
                            let offset = match variant_layout {
                                Some(layout) => layout
                                    .field_offsets
                                    .get(field_id)
                                    .and_then(|offset| offset.chosen)
                                    .ok_or("missing field offset in ADT layout")
                                    .context(span)?,
                                None => 0,
                            };
                            let field_ty = field.ty.clone().substitute(&tref.generics);
                            match self.unsafe_cell_strategy(span, &field_ty)? {
                                mini::UnsafeCellStrategy::Sized { cells: field_cells } => {
                                    for (field_cell_offset, cell_size) in field_cells {
                                        let field_cell_offset =
                                            size_bytes(span, field_cell_offset)?;
                                        let offset = offset
                                            .checked_add(field_cell_offset)
                                            .ok_or("UnsafeCell offset overflows u64")
                                            .context(span)?;
                                        sized_cells.push((mini_size(offset), cell_size));
                                    }
                                }
                                strategy => {
                                    check!(
                                        span,
                                        field_id.index() + 1 == fields.len()
                                            && tail_cells.is_none(),
                                        "non-tail field is unsized"
                                    );
                                    tail_cells = Some(strategy);
                                }
                            }
                        }
                        Ok(())
                    };

                    match &tdecl.kind {
                        TypeDeclKind::Struct(fields) => {
                            let variant_layout = layout.variant_layouts[VariantId::ZERO].as_ref();
                            add_fields(fields, variant_layout)?;
                        }
                        TypeDeclKind::Enum(variants) => {
                            for (variant_id, variant) in variants.iter_enumerated() {
                                if let Some(variant_layout) =
                                    layout.variant_layouts[variant_id].as_ref()
                                {
                                    add_fields(&variant.fields, Some(variant_layout))?;
                                }
                            }
                            check!(
                                span,
                                tail_cells.is_none(),
                                "enum variant has an unsized field"
                            );
                        }
                        TypeDeclKind::Union(_) => {
                            raise!(span, "MiniRust output does not support unions")
                        }
                        TypeDeclKind::Opaque => {
                            raise!(span, "opaque type is not representable in MiniRust")
                        }
                        TypeDeclKind::Alias(alias) => {
                            return self.unsafe_cell_strategy(
                                span,
                                &alias.clone().substitute(&tref.generics),
                            );
                        }
                        TypeDeclKind::Error(error) => raise!(span, "type error: {error}"),
                    };

                    // Cells from different enum variants may overlap.
                    sized_cells.sort_unstable();
                    let mut merged_ranges: Vec<(u64, u64)> = Vec::new();
                    for (offset, size) in sized_cells {
                        let start = size_bytes(span, offset)?;
                        let size = size_bytes(span, size)?;
                        let end = start
                            .checked_add(size)
                            .ok_or("UnsafeCell range overflows u64")
                            .context(span)?;
                        if let Some((_, previous_end)) = merged_ranges.last_mut()
                            && start <= *previous_end
                        {
                            *previous_end = (*previous_end).max(end);
                        } else {
                            merged_ranges.push((start, end));
                        }
                    }
                    let sized_cells = merged_ranges
                        .into_iter()
                        .map(|(start, end)| (mini_size(start), mini_size(end - start)))
                        .collect();

                    match tail_cells {
                        None => mini::UnsafeCellStrategy::Sized { cells: sized_cells },
                        Some(tail_cells) => mini::UnsafeCellStrategy::Tuple {
                            head_cells: sized_cells,
                            tail_cells: mini::GcCow::new(tail_cells),
                        },
                    }
                }
            }
            TyKind::Array(elem_ty, len, ..) => {
                let len = len
                    .as_usize_literal()
                    .ok_or("non-concrete array length")
                    .context(span)?;
                let (elem_size, _) = self.size_and_align(span, elem_ty)?;
                let mini::UnsafeCellStrategy::Sized { cells } =
                    self.unsafe_cell_strategy(span, elem_ty)?
                else {
                    unreachable!()
                };
                mini::UnsafeCellStrategy::Sized {
                    cells: cells
                        .into_iter()
                        .cartesian_product(0u128..len)
                        .map(|((offset, cell_size), index)| -> Result<_> {
                            let index = u64::try_from(index)
                                .map_err(|_| "array index does not fit u64")
                                .context(span)?;
                            let elem_start = index
                                .checked_mul(elem_size)
                                .ok_or("array cell offset overflows u64")
                                .context(span)?;
                            Ok((mini_size(elem_start) + offset, cell_size))
                        })
                        .try_collect()?,
                }
            }
            TyKind::Slice(elem_ty, ..) => {
                let mini::UnsafeCellStrategy::Sized { cells } =
                    self.unsafe_cell_strategy(span, elem_ty)?
                else {
                    unreachable!()
                };
                mini::UnsafeCellStrategy::Slice {
                    element_cells: cells,
                }
            }
            TyKind::Pattern(ty, _) => self.unsafe_cell_strategy(span, ty)?,
            TyKind::TypeVar(_) | TyKind::TraitType(..) => raise!(
                span,
                "MiniRust output requires a monomorphized crate: {}",
                ty.with_ctx(&self.fmt)
            ),
            TyKind::DynTrait(_) => mini::UnsafeCellStrategy::TraitObject,
            TyKind::Error(error) => raise!(span, "type error: {error}"),
            TyKind::Scalar(_)
            | TyKind::Ref(..)
            | TyKind::RawPtr(..)
            | TyKind::FnDef(_)
            | TyKind::FnPtr(_)
            | TyKind::Never
            | TyKind::PtrMetadata(_) => mini::UnsafeCellStrategy::Sized {
                cells: Default::default(),
            },
        })
    }

    pub(super) fn size_and_align(&self, span: Span, ty: &Ty) -> Result<(u64, u64)> {
        let ty = self.ty(span, ty)?;
        Ok(match ty.layout::<T>() {
            mini::LayoutStrategy::Sized(size, align) => {
                (size_bytes(span, size)?, align_bytes(span, align)?)
            }
            _ => raise!(span, "expected a sized type"),
        })
    }

    pub(super) fn metadata_kind(&self, span: Span, ty: &Ty) -> Result<mini::PointerMetaKind> {
        Ok(match ty.get_ptr_metadata(self.krate) {
            PtrMetadata::None => mini::PointerMetaKind::None,
            PtrMetadata::Length => mini::PointerMetaKind::ElementCount,
            PtrMetadata::VTable(_) | PtrMetadata::InheritFrom(_) => {
                // FIXME(minirust): dyn Trait
                raise!(span, "MiniRust output does not support `dyn Trait`")
            }
        })
    }

    pub(super) fn int_type(&self, ty: IntegerTy) -> mini::IntType {
        let signed = match ty {
            IntegerTy::Signed(_) => mini::Signedness::Signed,
            IntegerTy::Unsigned(_) => mini::Signedness::Unsigned,
        };
        mini::IntType {
            signed,
            size: mini::Size::from_bytes(ty.target_size(self.target.target_pointer_size)).unwrap(),
        }
    }

    pub(super) fn size(&self, span: Span, size: &crate::ast::Size) -> Result<u64> {
        let expr = size
            .chosen
            .as_ref()
            .ok_or("layout has no concrete size")
            .context(span)?;
        match expr.kind() {
            SizeExprKind::Constant(value) => {
                if let Some(value) = value.as_usize_literal() {
                    u64::try_from(value)
                        .map_err(|_| "layout size does not fit u64")
                        .context(span)
                } else {
                    Ok(match value.kind() {
                        ConstantExprKind::SizeOf(ty) => self.size_and_align(span, ty)?.0,
                        ConstantExprKind::AlignOf(ty) => self.size_and_align(span, ty)?.1,
                        _ => raise!(span, "layout has no concrete size"),
                    })
                }
            }
            _ => raise!(span, "layout has no concrete size"),
        }
    }
}
