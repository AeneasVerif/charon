//! Guarantees about the layout of types, as given by the Rust Reference.
use crate::ast::*;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, VariantName};
use serde_state::{DeserializeState, SerializeState};

/// Guaranteed facts about a layout size.
#[derive(Debug, Clone, SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub enum SizeGuarantee {
    Equals(ExactSizeExpr),
    AtLeast(ExactSizeExpr),
}

/// Guaranteed facts about a field offset.
#[derive(
    Debug,
    Clone,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
pub enum OffsetGuarantee {
    /// Guaranteed to be at offset zero. This applies for `repr(transparent)` and in some `repr(C)` cases.
    AtOffsetZero,
    /// Guaranteed only to be aligned to the given expression.
    GuaranteedAlignment(Box<ExactSizeExpr>),
    /// This offset is computed by the layout algorithm for C: take the previous field offset, add
    /// the previous field size, and align to the current field alignment.
    ReprCField {
        /// If this is `None`, then the field is directly after the enum tag.
        predecessor: Option<FieldId>,
    },
}

/// Layout information given by the metadata of an unsized type.
#[derive(
    Debug,
    Clone,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variant_prefix("LayoutValue"))]
pub enum MetadataValue {
    /// For a DST with `dyn Trait` metadata, this refers to the size found in the metadata.
    DynSize,
    /// For a DST with `dyn Trait` metadata, this refers to the alignment found in the metadata.
    DynAlign,
    /// For a DST with slice metadata, this refers to the length found in the metadata.
    SliceLength,
}

/// An expression that represents a size in bytes.
#[derive(
    Debug,
    Clone,
    EnumIsA,
    EnumAsGetters,
    VariantName,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("ExactSizeExpr"))]
#[serde_state(state_implements = HashConsSerializerState)]
pub enum ExactSizeExpr {
    /// An arbitrary constant of type `usize`.
    Constant(ConstantExpr),
    /// Layout information stored in the pointer metadata to this object.
    FromMetadata(MetadataValue),
    Max(Vec<ExactSizeExpr>),
    Min(Vec<ExactSizeExpr>),
    Plus(Box<ExactSizeExpr>, Box<ExactSizeExpr>),
    Scale(Box<ExactSizeExpr>, ConstantExpr),
    /// The next multiple of `target_align` from `base`.
    AlignTo {
        base: Box<ExactSizeExpr>,
        target_align: Box<ExactSizeExpr>,
    },
    /// A size expression that depens on whether the given type is inhabited.
    IfInhabited {
        ty: Ty,
        then_size: Box<ExactSizeExpr>,
        else_size: Box<ExactSizeExpr>,
    },
}

impl ExactSizeExpr {
    /// Recursively evaluate the parts of this expression that are known in `krate`.
    pub fn normalize_mut(&mut self, krate: &TranslatedCrate, target: &TargetTriple) {
        #[derive(Visitor)]
        struct NormalizeSizeExpr<'a> {
            krate: &'a TranslatedCrate,
            target: &'a TargetTriple,
        }

        /// Take out the concrete values from the vec and fold them with the provided function.
        fn fold_concrete_values(
            values: &mut Vec<ExactSizeExpr>,
            f: impl Fn(u128, u128) -> u128,
        ) -> Option<u128> {
            values
                .extract_if(.., |val| val.as_usize().is_some())
                .map(|val| val.as_usize().unwrap())
                .reduce(f)
        }

        impl VisitAstMut for NormalizeSizeExpr<'_> {
            fn exit_exact_size_expr(&mut self, expr: &mut ExactSizeExpr) {
                *expr = match expr {
                    ExactSizeExpr::Constant(constant) => {
                        debug_assert!(constant.ty.is_usize());
                        let exact_guarantee = |size: &SizeExpr| match &size.guarantee {
                            Some(SizeGuarantee::Equals(value)) => Some(value.clone()),
                            Some(SizeGuarantee::AtLeast(_)) | None => None,
                        };
                        let mut guaranteed = match &constant.kind {
                            ConstantExprKind::SizeOf(ty) => match ty.kind() {
                                TyKind::Never => ExactSizeExpr::from_usize(0),
                                TyKind::Literal(literal_ty) => {
                                    if let Some(target) =
                                        self.krate.target_information.get(self.target)
                                    {
                                        ExactSizeExpr::from_usize(
                                            literal_ty.target_size(target.target_pointer_size)
                                                as u128,
                                        )
                                    } else {
                                        return;
                                    }
                                }
                                _ => {
                                    if let Some(ty_ref) = ty.as_adt()
                                        && let Some(id) = ty_ref.as_adt()
                                        && let Some(decl) = self.krate.type_decls.get(id)
                                        && let Some(layout) = decl.layout.get(self.target)
                                        && let Some(value) = exact_guarantee(&layout.size)
                                    {
                                        value.substitute(&ty_ref.generics)
                                    } else {
                                        return;
                                    }
                                }
                            },
                            ConstantExprKind::AlignOf(ty) => match ty.kind() {
                                TyKind::Never => ExactSizeExpr::from_usize(1),
                                TyKind::Literal(literal_ty) => {
                                    if let Some(target) =
                                        self.krate.target_information.get(self.target)
                                        && let Some(value) =
                                            target.primitive_alignments.get(literal_ty)
                                    {
                                        ExactSizeExpr::from_usize(u128::from(*value))
                                    } else {
                                        return;
                                    }
                                }
                                _ => {
                                    if let Some(ty_ref) = ty.as_adt()
                                        && let Some(id) = ty_ref.as_adt()
                                        && let Some(decl) = self.krate.type_decls.get(id)
                                        && let Some(layout) = decl.layout.get(self.target)
                                        && let Some(value) = exact_guarantee(&layout.align)
                                    {
                                        value.substitute(&ty_ref.generics)
                                    } else {
                                        return;
                                    }
                                }
                            },
                            _ => return,
                        };
                        self.visit(&mut guaranteed);
                        guaranteed
                    }
                    ExactSizeExpr::FromMetadata(_) => return,
                    ExactSizeExpr::Max(values) => {
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val {
                                ExactSizeExpr::Max(nested) => values.extend(nested),
                                val => values.push(val),
                            }
                        }
                        // Get the max of the concrete values.
                        if let Some(value) = fold_concrete_values(values, std::cmp::max)
                            && value != 0
                        {
                            // Zero is the identity of `Max` so we don't push in that case.
                            values.push(ExactSizeExpr::from_usize(value));
                        }
                        if values.len() == 1 {
                            values.pop().unwrap()
                        } else if values.is_empty() {
                            ExactSizeExpr::from_usize(0)
                        } else {
                            return;
                        }
                    }
                    ExactSizeExpr::Min(values) => {
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val {
                                ExactSizeExpr::Min(nested) => values.extend(nested),
                                val => values.push(val),
                            }
                        }
                        // Get the min of the concrete values.
                        if let Some(value) = fold_concrete_values(values, std::cmp::min) {
                            // Zero is absorbing for `Min`.
                            if value == 0 {
                                values.clear();
                            }
                            values.push(ExactSizeExpr::from_usize(value));
                        }
                        if values.len() == 1 {
                            values.pop().unwrap()
                        } else {
                            return;
                        }
                    }
                    ExactSizeExpr::Plus(left, right) => match (left.as_usize(), right.as_usize()) {
                        (Some(left), Some(right)) => {
                            ExactSizeExpr::from_usize(left.strict_add(right))
                        }
                        (Some(0), None) => (**right).clone(),
                        (None, Some(0)) => (**left).clone(),
                        _ => return,
                    },
                    ExactSizeExpr::Scale(base, multiplier) => {
                        match (base.as_usize(), multiplier.as_usize_literal()) {
                            (_, Some(0)) | (Some(0), _) => ExactSizeExpr::from_usize(0),
                            (_, Some(1)) => (**base).clone(),
                            (Some(base), Some(multiplier)) => {
                                ExactSizeExpr::from_usize(base.strict_mul(multiplier))
                            }
                            _ => return,
                        }
                    }
                    ExactSizeExpr::AlignTo { base, target_align } => {
                        match (base.as_usize(), target_align.as_usize()) {
                            (_, Some(1)) => (**base).clone(),
                            (Some(0), Some(align)) if align != 0 => (**base).clone(),
                            (Some(base), Some(align)) if align != 0 => {
                                let remainder = base % align;
                                ExactSizeExpr::from_usize(if remainder == 0 {
                                    base
                                } else {
                                    base.strict_add(align - remainder)
                                })
                            }
                            _ => return,
                        }
                    }
                    ExactSizeExpr::IfInhabited { .. } => {
                        // FIXME: evaluate type inhabitedness
                        return;
                    }
                };
            }
        }

        NormalizeSizeExpr { krate, target }.visit(self);
    }

    fn as_usize(&self) -> Option<u128> {
        if let ExactSizeExpr::Constant(constant) = self {
            constant.as_usize_literal()
        } else {
            None
        }
    }

    fn from_usize(value: u128) -> Self {
        Self::Constant(ConstantExpr::mk_usize(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_krate() -> (TranslatedCrate, TargetTriple) {
        let mut krate = TranslatedCrate::default();
        let target = "test-target".to_owned();
        krate.target_information.insert(
            target.clone(),
            TargetInfo {
                target_pointer_size: 8,
                is_little_endian: true,
                c_enum_smallest_repr_ty: IntTy::I32,
                primitive_alignments: SeqHashMap::new(),
            },
        );
        (krate, target)
    }

    #[test]
    fn normalize_arithmetic() {
        let (krate, target) = test_krate();
        let mut expr = ExactSizeExpr::AlignTo {
            base: Box::new(ExactSizeExpr::Plus(
                Box::new(ExactSizeExpr::from_usize(2)),
                Box::new(ExactSizeExpr::Scale(
                    Box::new(ExactSizeExpr::from_usize(3)),
                    ConstantExpr::mk_usize(4),
                )),
            )),
            target_align: Box::new(ExactSizeExpr::from_usize(8)),
        };

        expr.normalize_mut(&krate, &target);

        assert_eq!(expr.as_usize(), Some(16));
    }

    #[test]
    fn normalize_extrema_partially() {
        let (krate, target) = test_krate();
        let mut expr = ExactSizeExpr::Max(vec![
            ExactSizeExpr::from_usize(2),
            ExactSizeExpr::Max(vec![
                ExactSizeExpr::from_usize(5),
                ExactSizeExpr::FromMetadata(MetadataValue::DynSize),
            ]),
            ExactSizeExpr::from_usize(3),
        ]);

        expr.normalize_mut(&krate, &target);

        let ExactSizeExpr::Max(contenders) = expr else {
            panic!("expected a partially normalized maximum")
        };
        assert_eq!(contenders.len(), 2);
        assert_eq!(contenders[1].as_usize(), Some(5));
        assert!(matches!(
            contenders[0],
            ExactSizeExpr::FromMetadata(MetadataValue::DynSize)
        ));

        let mut empty = ExactSizeExpr::Max(Vec::new());
        empty.normalize_mut(&krate, &target);
        assert_eq!(empty.as_usize(), Some(0));
    }

    #[test]
    fn normalize_extrema_identities() {
        let (krate, target) = test_krate();
        let mut max = ExactSizeExpr::Max(vec![
            ExactSizeExpr::from_usize(0),
            ExactSizeExpr::FromMetadata(MetadataValue::DynSize),
        ]);
        let mut min = ExactSizeExpr::Min(vec![
            ExactSizeExpr::from_usize(7),
            ExactSizeExpr::FromMetadata(MetadataValue::DynSize),
            ExactSizeExpr::from_usize(0),
        ]);

        max.normalize_mut(&krate, &target);
        min.normalize_mut(&krate, &target);

        assert!(matches!(
            max,
            ExactSizeExpr::FromMetadata(MetadataValue::DynSize)
        ));
        assert_eq!(min.as_usize(), Some(0));
    }

    #[test]
    fn normalize_if_inhabited() {
        let (krate, target) = test_krate();
        let mut expr = ExactSizeExpr::IfInhabited {
            ty: TyKind::Never.into_ty(),
            then_size: Box::new(ExactSizeExpr::from_usize(10)),
            else_size: Box::new(ExactSizeExpr::Plus(
                Box::new(ExactSizeExpr::from_usize(2)),
                Box::new(ExactSizeExpr::from_usize(3)),
            )),
        };

        expr.normalize_mut(&krate, &target);

        let ExactSizeExpr::IfInhabited {
            then_size,
            else_size,
            ..
        } = expr
        else {
            panic!("inhabitedness is not normalized yet")
        };
        assert_eq!(then_size.as_usize(), Some(10));
        assert_eq!(else_size.as_usize(), Some(5));
    }

    #[test]
    fn normalize_for_the_selected_target() {
        let mut krate = TranslatedCrate::default();
        let literal_ty = LiteralTy::UInt(UIntTy::U64);
        for (triple, pointer_size, alignment) in [("a", 4, 4), ("b", 8, 8)] {
            let mut primitive_alignments = SeqHashMap::new();
            primitive_alignments.insert(literal_ty, alignment);
            krate.target_information.insert(
                triple.to_owned(),
                TargetInfo {
                    target_pointer_size: pointer_size,
                    is_little_endian: true,
                    c_enum_smallest_repr_ty: IntTy::I32,
                    primitive_alignments,
                },
            );
        }

        let mut size = ExactSizeExpr::Constant(ConstantExpr {
            kind: ConstantExprKind::SizeOf(TyKind::Literal(literal_ty).into_ty()),
            ty: Ty::mk_usize(),
        });
        let mut align = ExactSizeExpr::Constant(ConstantExpr {
            kind: ConstantExprKind::AlignOf(TyKind::Literal(literal_ty).into_ty()),
            ty: Ty::mk_usize(),
        });
        let pointer_size = ExactSizeExpr::Constant(ConstantExpr {
            kind: ConstantExprKind::SizeOf(Ty::mk_usize()),
            ty: Ty::mk_usize(),
        });
        let mut pointer_size_a = pointer_size.clone();
        let mut pointer_size_b = pointer_size;
        let target_a = "a".to_owned();
        let target_b = "b".to_owned();

        size.normalize_mut(&krate, &target_a);
        align.normalize_mut(&krate, &target_a);
        pointer_size_a.normalize_mut(&krate, &target_a);
        pointer_size_b.normalize_mut(&krate, &target_b);

        assert_eq!(size.as_usize(), Some(8));
        assert_eq!(align.as_usize(), Some(4));
        assert_eq!(pointer_size_a.as_usize(), Some(4));
        assert_eq!(pointer_size_b.as_usize(), Some(8));
    }

    #[test]
    fn normalize_uses_guarantees_not_chosen_values() {
        let (mut krate, target) = test_krate();
        let id = TypeDeclId::ZERO;
        let mut generics = GenericParams::empty();
        generics
            .types
            .push_with(|id| TypeParam::new(id, "T".to_owned(), Variance::Invariant));
        let generic_ty = generics.identity_args().types[TypeVarId::ZERO].clone();
        let mut layouts = SeqHashMap::new();
        layouts.insert(
            target.clone(),
            Layout {
                size: SizeExpr {
                    guarantee: None,
                    chosen: Some(99),
                },
                align: SizeExpr::new(1),
                discriminator: None,
                uninhabited: false,
                variant_layouts: Default::default(),
                repr: Default::default(),
            },
        );
        krate.type_decls.insert(
            id,
            TypeDecl {
                def_id: id,
                item_meta: ItemMeta::dummy_public(
                    Span::default(),
                    Name::from_path(&["T"]),
                    true,
                    ItemOpacity::Transparent,
                ),
                generics,
                src: TypeSource::Normal,
                kind: TypeDeclKind::Opaque,
                layout: layouts,
                ptr_metadata: PtrMetadata::None,
            },
        );
        let ty = TyKind::Adt(TypeDeclRef::new(
            TypeId::Adt(id),
            GenericArgs::new_types(
                [TyKind::Literal(LiteralTy::UInt(UIntTy::U16)).into_ty()]
                    .into_iter()
                    .collect(),
            ),
        ))
        .into_ty();
        let size_of = || {
            ExactSizeExpr::Constant(ConstantExpr {
                kind: ConstantExprKind::SizeOf(ty.clone()),
                ty: Ty::mk_usize(),
            })
        };

        let mut without_guarantee = size_of();
        without_guarantee.normalize_mut(&krate, &target);
        assert!(matches!(
            without_guarantee,
            ExactSizeExpr::Constant(ConstantExpr {
                kind: ConstantExprKind::SizeOf(_),
                ..
            })
        ));

        let size = &mut krate.type_decls.get_mut(id).unwrap().layout[&target].size;
        size.guarantee = Some(SizeGuarantee::Equals(ExactSizeExpr::Plus(
            Box::new(ExactSizeExpr::Constant(ConstantExpr {
                kind: ConstantExprKind::SizeOf(generic_ty),
                ty: Ty::mk_usize(),
            })),
            Box::new(ExactSizeExpr::from_usize(5)),
        )));
        let mut with_guarantee = size_of();
        with_guarantee.normalize_mut(&krate, &target);
        assert_eq!(with_guarantee.as_usize(), Some(7));
    }
}
