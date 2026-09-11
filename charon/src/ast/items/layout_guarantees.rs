//! Guarantees about the layout of types, as given by the Rust Reference.
use crate::ast::*;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, VariantName};
use serde_state::{DeserializeState, SerializeState};

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
    GuaranteedAlignment(SizeExpr),
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
pub struct SizeExpr(pub HashConsed<SizeExprKind>);

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
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("SizeExpr"))]
pub enum SizeExprKind {
    /// An arbitrary constant of type `usize`.
    Constant(ConstantExpr),
    /// Layout information stored in the pointer metadata to this object.
    FromMetadata(MetadataValue),
    Max(Vec<SizeExpr>),
    Min(Vec<SizeExpr>),
    Plus(SizeExpr, SizeExpr),
    /// Multiply by a constant.
    Scale(SizeExpr, ConstantExpr),
    /// The size is at least the value of this expression.
    AtLeast(SizeExpr),
    /// The next multiple of `target_align` from `base`.
    AlignTo {
        base: SizeExpr,
        target_align: SizeExpr,
    },
    /// A size expression that depens on whether the given type is inhabited.
    IfInhabited {
        ty: Ty,
        then_size: SizeExpr,
        else_size: SizeExpr,
    },
}

impl SizeExpr {
    pub fn new(kind: SizeExprKind) -> Self {
        Self(HashConsed::new(kind))
    }

    pub fn kind(&self) -> &SizeExprKind {
        self.0.inner()
    }

    pub fn with_kind_mut<R>(&mut self, f: impl FnOnce(&mut SizeExprKind) -> R) -> R {
        self.0.with_inner_mut(f)
    }

    /// Recursively evaluate the parts of this expression that are known in `krate`.
    /// If `allow_precision_loss` is false, `SizeOf` and `AlignOf` are only replaced with a
    /// [`SizeExprKind::Constant`].
    pub fn normalize(
        mut self,
        krate: &TranslatedCrate,
        target: &TargetTriple,
        allow_precision_loss: bool,
    ) -> Self {
        #[derive(Visitor)]
        struct NormalizeSizeExpr<'a> {
            krate: &'a TranslatedCrate,
            target: &'a TargetTriple,
            allow_precision_loss: bool,
        }

        /// Take out the concrete values from the vec and fold them with the provided function.
        fn fold_concrete_values(
            values: &mut Vec<SizeExpr>,
            f: impl Fn(u128, u128) -> u128,
        ) -> Option<u128> {
            values
                .extract_if(.., |val| val.as_usize().is_some())
                .map(|val| val.as_usize().unwrap())
                .reduce(f)
        }

        impl VisitAstMut for NormalizeSizeExpr<'_> {
            fn exit_size_expr_kind(&mut self, expr: &mut SizeExprKind) {
                *expr = match expr {
                    SizeExprKind::Constant(constant) => {
                        debug_assert!(constant.ty().is_usize());
                        let mut guaranteed = match constant.kind() {
                            ConstantExprKind::SizeOf(ty) => match ty.kind() {
                                TyKind::Never => SizeExpr::from_usize(0),
                                TyKind::Scalar(scalar_ty) => {
                                    if let Some(target) =
                                        self.krate.target_information.get(self.target)
                                    {
                                        SizeExpr::from_usize(
                                            scalar_ty.target_size(target.target_pointer_size)
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
                                        && let Some(value) = layout.size.guarantee.clone()
                                    {
                                        value.substitute(&ty_ref.generics)
                                    } else {
                                        return;
                                    }
                                }
                            },
                            ConstantExprKind::AlignOf(ty) => match ty.kind() {
                                TyKind::Never => SizeExpr::from_usize(1),
                                TyKind::Scalar(scalar_ty) => {
                                    if let Some(target) =
                                        self.krate.target_information.get(self.target)
                                        && let Some(value) =
                                            target.primitive_alignments.get(scalar_ty)
                                    {
                                        SizeExpr::from_usize(u128::from(*value))
                                    } else {
                                        return;
                                    }
                                }
                                _ => {
                                    if let Some(ty_ref) = ty.as_adt()
                                        && let Some(decl) = self.krate.type_decls.get(ty_ref.id)
                                        && let Some(layout) = decl.layout.get(self.target)
                                        && let Some(value) = layout.align.guarantee.clone()
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
                        if !self.allow_precision_loss
                            && !matches!(guaranteed.kind(), SizeExprKind::Constant(_))
                        {
                            return;
                        }
                        guaranteed.kind().clone()
                    }
                    SizeExprKind::Max(values) => {
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val.kind() {
                                SizeExprKind::Max(nested) => values.extend(nested.iter().cloned()),
                                _ => values.push(val),
                            }
                        }
                        // Get the max of the concrete values.
                        if let Some(value) = fold_concrete_values(values, std::cmp::max)
                            && value != 0
                        {
                            // Zero is the identity of `Max` so we don't push in that case.
                            values.push(SizeExpr::from_usize(value));
                        }
                        if values.len() == 1 {
                            values.pop().unwrap().kind().clone()
                        } else if values.is_empty() {
                            SizeExprKind::zero()
                        } else {
                            return;
                        }
                    }
                    SizeExprKind::Min(values) => {
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val.kind() {
                                SizeExprKind::Min(nested) => values.extend(nested.iter().cloned()),
                                _ => values.push(val),
                            }
                        }
                        // Get the min of the concrete values.
                        if let Some(value) = fold_concrete_values(values, std::cmp::min) {
                            // Zero is absorbing for `Min`.
                            if value == 0 {
                                values.clear();
                            }
                            values.push(SizeExpr::from_usize(value));
                        }
                        if values.len() == 1 {
                            values.pop().unwrap().kind().clone()
                        } else {
                            return;
                        }
                    }
                    SizeExprKind::Plus(left, right) => match (left.as_usize(), right.as_usize()) {
                        (Some(left), Some(right)) => {
                            SizeExprKind::from_usize(left.strict_add(right))
                        }
                        (Some(0), None) => right.kind().clone(),
                        (None, Some(0)) => left.kind().clone(),
                        _ => return,
                    },
                    SizeExprKind::Scale(base, multiplier) => {
                        match (base.as_usize(), multiplier.as_usize_literal()) {
                            (_, Some(0)) | (Some(0), _) => SizeExprKind::zero(),
                            (_, Some(1)) => base.kind().clone(),
                            (Some(base), Some(multiplier)) => {
                                SizeExprKind::from_usize(base.strict_mul(multiplier))
                            }
                            _ => return,
                        }
                    }
                    SizeExprKind::AlignTo { base, target_align } => {
                        match (base.as_usize(), target_align.as_usize()) {
                            (_, Some(1)) => base.kind().clone(),
                            (Some(0), Some(align)) if align != 0 => base.kind().clone(),
                            (Some(base), Some(align)) if align != 0 => {
                                let remainder = base % align;
                                SizeExprKind::from_usize(if remainder == 0 {
                                    base
                                } else {
                                    base.strict_add(align - remainder)
                                })
                            }
                            _ => return,
                        }
                    }
                    SizeExprKind::IfInhabited { .. } => {
                        // FIXME: evaluate type inhabitedness
                        return;
                    }
                    SizeExprKind::AtLeast(_) | SizeExprKind::FromMetadata(_) => return,
                };
            }
        }

        NormalizeSizeExpr {
            krate,
            target,
            allow_precision_loss,
        }
        .visit(&mut self);
        self
    }

    fn as_usize(&self) -> Option<u128> {
        if let SizeExprKind::Constant(constant) = self.kind() {
            constant.as_usize_literal()
        } else {
            None
        }
    }

    fn from_usize(value: u128) -> Self {
        SizeExprKind::from_usize(value).into_expr()
    }
}

impl SizeExprKind {
    pub fn zero() -> Self {
        Self::from_usize(0)
    }

    pub fn from_usize(value: u128) -> Self {
        Self::Constant(ConstantExpr::mk_usize(value))
    }

    pub fn into_expr(self) -> SizeExpr {
        SizeExpr::new(self)
    }
}

impl From<SizeExprKind> for SizeExpr {
    fn from(kind: SizeExprKind) -> Self {
        kind.into_expr()
    }
}

impl std::ops::Deref for SizeExpr {
    type Target = SizeExprKind;

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
        let expr = SizeExprKind::AlignTo {
            base: SizeExprKind::Plus(
                SizeExpr::from_usize(2),
                SizeExprKind::Scale(SizeExpr::from_usize(3), ConstantExpr::mk_usize(4)).into_expr(),
            )
            .into_expr(),
            target_align: SizeExpr::from_usize(8),
        }
        .into_expr()
        .normalize(&krate, &target, false);

        assert_eq!(expr.as_usize(), Some(16));
    }

    #[test]
    fn normalize_extrema_partially() {
        let (krate, target) = test_krate();
        let expr = SizeExprKind::Max(vec![
            SizeExpr::from_usize(2),
            SizeExprKind::Max(vec![
                SizeExpr::from_usize(5),
                SizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
            ])
            .into_expr(),
            SizeExpr::from_usize(3),
        ])
        .into_expr()
        .normalize(&krate, &target, false);

        let SizeExprKind::Max(contenders) = expr.kind() else {
            panic!("expected a partially normalized maximum")
        };
        assert_eq!(contenders.len(), 2);
        assert_eq!(contenders[1].as_usize(), Some(5));
        assert!(matches!(
            contenders[0].kind(),
            SizeExprKind::FromMetadata(MetadataValue::DynSize)
        ));

        let empty = SizeExprKind::Max(Vec::new())
            .into_expr()
            .normalize(&krate, &target, false);
        assert_eq!(empty.as_usize(), Some(0));
    }

    #[test]
    fn normalize_extrema_identities() {
        let (krate, target) = test_krate();
        let max = SizeExprKind::Max(vec![
            SizeExpr::from_usize(0),
            SizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
        ])
        .into_expr()
        .normalize(&krate, &target, false);
        let min = SizeExprKind::Min(vec![
            SizeExpr::from_usize(7),
            SizeExprKind::FromMetadata(MetadataValue::DynSize).into_expr(),
            SizeExpr::from_usize(0),
        ])
        .into_expr()
        .normalize(&krate, &target, false);

        assert!(matches!(
            max.kind(),
            SizeExprKind::FromMetadata(MetadataValue::DynSize)
        ));
        assert_eq!(min.as_usize(), Some(0));
    }

    #[test]
    fn normalize_if_inhabited() {
        let (krate, target) = test_krate();
        let expr = SizeExprKind::IfInhabited {
            ty: TyKind::Never.into_ty(),
            then_size: SizeExpr::from_usize(10),
            else_size: SizeExprKind::Plus(SizeExpr::from_usize(2), SizeExpr::from_usize(3))
                .into_expr(),
        }
        .into_expr()
        .normalize(&krate, &target, false);

        let SizeExprKind::IfInhabited {
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
        let scalar_ty = ScalarTy::Integer(IntegerTy::Unsigned(UIntTy::U64));
        for (triple, pointer_size, alignment) in [("a", 4, 4), ("b", 8, 8)] {
            let mut primitive_alignments = SeqHashMap::new();
            primitive_alignments.insert(scalar_ty, alignment);
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

        let size = SizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::SizeOf(TyKind::Scalar(scalar_ty).into_ty()),
            Ty::mk_usize(),
        ))
        .into_expr()
        .normalize(&krate, &target_a, false);
        let align = SizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::AlignOf(TyKind::Scalar(scalar_ty).into_ty()),
            Ty::mk_usize(),
        ))
        .into_expr()
        .normalize(&krate, &target_a, false);
        let pointer_size = SizeExprKind::Constant(ConstantExpr::new(
            ConstantExprKind::SizeOf(Ty::mk_usize()),
            Ty::mk_usize(),
        ))
        .into_expr();
        let pointer_size_a = pointer_size.clone().normalize(&krate, &target_a, false);
        let pointer_size_b = pointer_size.normalize(&krate, &target_b, false);

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
                size: Size {
                    chosen: SizeExpr::from_usize(99),
                    guarantee: None,
                },
                align: Size::new(1),
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
                [TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(UIntTy::U16))).into_ty()]
                    .into_iter()
                    .collect(),
            ),
            None,
        ))
        .into_ty();
        let size_of = || {
            SizeExprKind::Constant(ConstantExpr::new(
                ConstantExprKind::SizeOf(ty.clone()),
                Ty::mk_usize(),
            ))
            .into_expr()
        };
        let align_of = || {
            SizeExprKind::Constant(ConstantExpr::new(
                ConstantExprKind::AlignOf(ty.clone()),
                Ty::mk_usize(),
            ))
            .into_expr()
        };

        let without_guarantee = size_of().normalize(&krate, &target, false);
        assert!(matches!(
            without_guarantee.kind(),
            SizeExprKind::Constant(constant)
                if matches!(constant.kind(), ConstantExprKind::SizeOf(_))
        ));

        {
            let layout = &mut krate.type_decls.get_mut(id).unwrap().layout[&target];
            layout.size.guarantee =
                Some(SizeExprKind::AtLeast(SizeExpr::from_usize(2)).into_expr());
            layout.align.guarantee =
                Some(SizeExprKind::AtLeast(SizeExpr::from_usize(1)).into_expr());
        }

        let size_without_precision_loss = size_of().normalize(&krate, &target, false);
        assert!(matches!(
            size_without_precision_loss.kind(),
            SizeExprKind::Constant(constant)
                if matches!(constant.kind(), ConstantExprKind::SizeOf(_))
        ));
        let align_without_precision_loss = align_of().normalize(&krate, &target, false);
        assert!(matches!(
            align_without_precision_loss.kind(),
            SizeExprKind::Constant(constant)
                if matches!(constant.kind(), ConstantExprKind::AlignOf(_))
        ));

        let size_with_precision_loss = size_of().normalize(&krate, &target, true);
        assert!(matches!(
            size_with_precision_loss.kind(),
            SizeExprKind::AtLeast(value) if value.as_usize() == Some(2)
        ));
        let align_with_precision_loss = align_of().normalize(&krate, &target, true);
        assert!(matches!(
            align_with_precision_loss.kind(),
            SizeExprKind::AtLeast(value) if value.as_usize() == Some(1)
        ));

        let size = &mut krate.type_decls.get_mut(id).unwrap().layout[&target].size;
        size.guarantee = Some(
            SizeExprKind::Plus(
                SizeExprKind::Constant(ConstantExpr::new(
                    ConstantExprKind::SizeOf(generic_ty),
                    Ty::mk_usize(),
                ))
                .into_expr(),
                SizeExpr::from_usize(5),
            )
            .into_expr(),
        );
        let with_guarantee = size_of().normalize(&krate, &target, false);
        assert_eq!(with_guarantee.as_usize(), Some(7));
    }
}
