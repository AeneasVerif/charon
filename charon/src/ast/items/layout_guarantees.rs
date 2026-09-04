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
    GuaranteedAlignment(ExactSizeExpr),
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
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
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
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    SerializeState,
    DeserializeState,
    Drive,
    DriveMut,
    DriveTwo,
)]
#[serde_state(state_implements = DedupSerializerState)]
pub struct ExactSizeExpr(pub HashConsed<ExactSizeExprKind>);

#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
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
pub enum ExactSizeExprKind {
    /// An arbitrary constant of type `usize`.
    Constant(ConstantExpr),
    /// Layout information stored in the pointer metadata to this object.
    FromMetadata(MetadataValue),
    Max(Vec<ExactSizeExpr>),
    Min(Vec<ExactSizeExpr>),
    Plus(ExactSizeExpr, ExactSizeExpr),
    Scale(ExactSizeExpr, ConstantExpr),
    /// The next multiple of `target_align` from `base`.
    AlignTo {
        base: ExactSizeExpr,
        target_align: ExactSizeExpr,
    },
    /// A size expression that depens on whether the given type is inhabited.
    IfInhabited {
        ty: Ty,
        then_size: ExactSizeExpr,
        else_size: ExactSizeExpr,
    },
}

impl ExactSizeExpr {
    pub fn new(kind: ExactSizeExprKind) -> Self {
        Self(HashConsed::new(kind))
    }

    pub fn kind(&self) -> &ExactSizeExprKind {
        self.0.inner()
    }

    pub fn with_kind_mut<R>(&mut self, f: impl FnOnce(&mut ExactSizeExprKind) -> R) -> R {
        self.0.with_inner_mut(f)
    }

    /// Recursively evaluate the parts of this expression that are known in `krate`.
    pub fn normalize(mut self, krate: &TranslatedCrate, target: &TargetTriple) -> Self {
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
            fn exit_exact_size_expr_kind(&mut self, expr: &mut ExactSizeExprKind) {
                *expr = match expr {
                    ExactSizeExprKind::Constant(constant) => {
                        debug_assert!(constant.ty().is_usize());
                        let exact_guarantee = |size: &SizeExpr| match &size.guarantee {
                            Some(SizeGuarantee::Equals(value)) => Some(value.clone()),
                            Some(SizeGuarantee::AtLeast(_)) | None => None,
                        };
                        let mut guaranteed = match constant.kind() {
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
                                        && let Some(decl) = self.krate.type_decls.get(ty_ref.id)
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
                                        && let Some(decl) = self.krate.type_decls.get(ty_ref.id)
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
                        guaranteed.kind().clone()
                    }
                    ExactSizeExprKind::FromMetadata(_) => return,
                    ExactSizeExprKind::Max(values) => {
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val.kind() {
                                ExactSizeExprKind::Max(nested) => {
                                    values.extend(nested.iter().cloned())
                                }
                                _ => values.push(val),
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
                            values.pop().unwrap().kind().clone()
                        } else if values.is_empty() {
                            ExactSizeExprKind::zero()
                        } else {
                            return;
                        }
                    }
                    ExactSizeExprKind::Min(values) => {
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val.kind() {
                                ExactSizeExprKind::Min(nested) => {
                                    values.extend(nested.iter().cloned())
                                }
                                _ => values.push(val),
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
                            values.pop().unwrap().kind().clone()
                        } else {
                            return;
                        }
                    }
                    ExactSizeExprKind::Plus(left, right) => {
                        match (left.as_usize(), right.as_usize()) {
                            (Some(left), Some(right)) => {
                                ExactSizeExprKind::from_usize(left.strict_add(right))
                            }
                            (Some(0), None) => right.kind().clone(),
                            (None, Some(0)) => left.kind().clone(),
                            _ => return,
                        }
                    }
                    ExactSizeExprKind::Scale(base, multiplier) => {
                        match (base.as_usize(), multiplier.as_usize_literal()) {
                            (_, Some(0)) | (Some(0), _) => ExactSizeExprKind::zero(),
                            (_, Some(1)) => base.kind().clone(),
                            (Some(base), Some(multiplier)) => {
                                ExactSizeExprKind::from_usize(base.strict_mul(multiplier))
                            }
                            _ => return,
                        }
                    }
                    ExactSizeExprKind::AlignTo { base, target_align } => {
                        match (base.as_usize(), target_align.as_usize()) {
                            (_, Some(1)) => base.kind().clone(),
                            (Some(0), Some(align)) if align != 0 => base.kind().clone(),
                            (Some(base), Some(align)) if align != 0 => {
                                let remainder = base % align;
                                ExactSizeExprKind::from_usize(if remainder == 0 {
                                    base
                                } else {
                                    base.strict_add(align - remainder)
                                })
                            }
                            _ => return,
                        }
                    }
                    ExactSizeExprKind::IfInhabited { .. } => {
                        // FIXME: evaluate type inhabitedness
                        return;
                    }
                };
            }
        }

        NormalizeSizeExpr { krate, target }.visit(&mut self);
        self
    }

    fn as_usize(&self) -> Option<u128> {
        if let ExactSizeExprKind::Constant(constant) = self.kind() {
            constant.as_usize_literal()
        } else {
            None
        }
    }

    fn from_usize(value: u128) -> Self {
        ExactSizeExprKind::from_usize(value).into_expr()
    }
}

impl ExactSizeExprKind {
    pub fn zero() -> Self {
        Self::from_usize(0)
    }

    pub fn from_usize(value: u128) -> Self {
        Self::Constant(ConstantExpr::mk_usize(value))
    }

    pub fn into_expr(self) -> ExactSizeExpr {
        ExactSizeExpr::new(self)
    }
}

impl From<ExactSizeExprKind> for ExactSizeExpr {
    fn from(kind: ExactSizeExprKind) -> Self {
        kind.into_expr()
    }
}

impl std::ops::Deref for ExactSizeExpr {
    type Target = ExactSizeExprKind;

    fn deref(&self) -> &Self::Target {
        self.kind()
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
        let expr = ExactSizeExprKind::AlignTo {
            base: ExactSizeExprKind::Plus(
                ExactSizeExpr::from_usize(2),
                ExactSizeExprKind::Scale(ExactSizeExpr::from_usize(3), ConstantExpr::mk_usize(4))
                    .into_expr(),
            )
            .into_expr(),
            target_align: ExactSizeExpr::from_usize(8),
        }
        .into_expr()
        .normalize(&krate, &target);

        assert_eq!(expr.as_usize(), Some(16));
    }

    #[test]
    fn normalize_extrema_partially() {
        let (krate, target) = test_krate();
        let expr = ExactSizeExprKind::Max(vec![
            ExactSizeExpr::from_usize(2),
            ExactSizeExprKind::Max(vec![
                ExactSizeExpr::from_usize(5),
                ExactSizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
            ])
            .into_expr(),
            ExactSizeExpr::from_usize(3),
        ])
        .into_expr()
        .normalize(&krate, &target);

        let ExactSizeExprKind::Max(contenders) = expr.kind() else {
            panic!("expected a partially normalized maximum")
        };
        assert_eq!(contenders.len(), 2);
        assert_eq!(contenders[1].as_usize(), Some(5));
        assert!(matches!(
            contenders[0].kind(),
            ExactSizeExprKind::FromMetadata(MetadataValue::DynSize)
        ));

        let empty = ExactSizeExprKind::Max(Vec::new())
            .into_expr()
            .normalize(&krate, &target);
        assert_eq!(empty.as_usize(), Some(0));
    }

    #[test]
    fn normalize_extrema_identities() {
        let (krate, target) = test_krate();
        let max = ExactSizeExprKind::Max(vec![
            ExactSizeExpr::from_usize(0),
            ExactSizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
        ])
        .into_expr()
        .normalize(&krate, &target);
        let min = ExactSizeExprKind::Min(vec![
            ExactSizeExpr::from_usize(7),
            ExactSizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
            ExactSizeExpr::from_usize(0),
        ])
        .into_expr()
        .normalize(&krate, &target);

        assert!(matches!(
            max.kind(),
            ExactSizeExprKind::FromMetadata(MetadataValue::DynSize)
        ));
        assert_eq!(min.as_usize(), Some(0));
    }

    #[test]
    fn normalize_if_inhabited() {
        let (krate, target) = test_krate();
        let expr = ExactSizeExprKind::IfInhabited {
            ty: TyKind::Never.into_ty(),
            then_size: ExactSizeExpr::from_usize(10),
            else_size: ExactSizeExprKind::Plus(
                ExactSizeExpr::from_usize(2),
                ExactSizeExpr::from_usize(3),
            )
            .into_expr(),
        }
        .into_expr()
        .normalize(&krate, &target);

        let ExactSizeExprKind::IfInhabited {
            then_size,
            else_size,
            ..
        } = expr.kind()
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
        let target_a = "a".to_owned();
        let target_b = "b".to_owned();

        let size = ExactSizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::SizeOf(TyKind::Literal(literal_ty).into_ty()),
            Ty::mk_usize(),
        ))
        .into_expr()
        .normalize(&krate, &target_a);
        let align = ExactSizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::AlignOf(TyKind::Literal(literal_ty).into_ty()),
            Ty::mk_usize(),
        ))
        .into_expr()
        .normalize(&krate, &target_a);
        let pointer_size = ExactSizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::SizeOf(Ty::mk_usize()),
            Ty::mk_usize(),
        ))
        .into_expr();
        let pointer_size_a = pointer_size.clone().normalize(&krate, &target_a);
        let pointer_size_b = pointer_size.normalize(&krate, &target_b);

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
            id,
            GenericArgs::new_types(
                [TyKind::Literal(LiteralTy::UInt(UIntTy::U16)).into_ty()]
                    .into_iter()
                    .collect(),
            ),
            None,
        ))
        .into_ty();
        let size_of = || {
            ExactSizeExprKind::Constant(ConstantExpr::new(
                ConstantExprKind::SizeOf(ty.clone()),
                Ty::mk_usize(),
            ))
            .into_expr()
        };

        let without_guarantee = size_of().normalize(&krate, &target);
        assert!(matches!(
            without_guarantee.kind(),
            ExactSizeExprKind::Constant(constant)
                if matches!(constant.kind(), ConstantExprKind::SizeOf(_))
        ));

        let size = &mut krate.type_decls.get_mut(id).unwrap().layout[&target].size;
        size.guarantee = Some(SizeGuarantee::Equals(
            ExactSizeExprKind::Plus(
                ExactSizeExprKind::Constant(ConstantExpr::new(
                    ConstantExprKind::SizeOf(generic_ty),
                    Ty::mk_usize(),
                ))
                .into_expr(),
                ExactSizeExpr::from_usize(5),
            )
            .into_expr(),
        ));
        let with_guarantee = size_of().normalize(&krate, &target);
        assert_eq!(with_guarantee.as_usize(), Some(7));
    }
}
