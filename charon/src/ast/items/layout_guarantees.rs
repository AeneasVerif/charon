//! Guarantees about the layout of types, as given by the Rust Reference.
use crate::ast::*;
use derive_generic_visitor::*;
use macros::{EnumAsGetters, EnumIsA, VariantName};
use serde_state::{DeserializeState, SerializeState};

/// Guaranteed facts about a field offset.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
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
    GuaranteedAlignment(SizeGuarantee),
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
pub struct SizeGuarantee(pub HashConsed<SizeGuaranteeKind>);

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
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("SizeGuarantee"))]
pub enum SizeGuaranteeKind {
    /// An arbitrary constant of type `usize`.
    Constant(ConstantExpr),
    /// Layout information stored in the pointer metadata to this object.
    FromMetadata(MetadataValue),
    Max(Vec<SizeGuarantee>),
    Min(Vec<SizeGuarantee>),
    Plus(SizeGuarantee, SizeGuarantee),
    Scale(SizeGuarantee, ConstantExpr),
    /// The next multiple of `target_align` from `base`.
    AlignTo {
        base: SizeGuarantee,
        target_align: SizeGuarantee,
    },
    /// A size expression that depens on whether the given type is inhabited.
    IfInhabited {
        ty: Ty,
        then_size: SizeGuarantee,
        else_size: SizeGuarantee,
    },
    /// The offset of the given field inside the referenced type.
    FieldOffset(TypeDeclRef, Option<VariantId>, FieldId),
    /// Any value larger than that one.
    AtLeast(SizeGuarantee),
}

impl SizeGuarantee {
    pub fn new(kind: SizeGuaranteeKind) -> Self {
        Self(HashConsed::new(kind))
    }

    pub fn kind(&self) -> &SizeGuaranteeKind {
        self.0.inner()
    }

    pub fn with_kind_mut<R>(&mut self, f: impl FnOnce(&mut SizeGuaranteeKind) -> R) -> R {
        self.0.with_inner_mut(f)
    }

    pub fn mk_const_byte_count(bytes: ByteCount) -> Self {
        Self::new(SizeGuaranteeKind::Constant(ConstantExpr::new(
            ConstantExprKind::Literal(Literal::Scalar(ScalarValue::Unsigned(
                UIntTy::Usize,
                bytes as u128,
            ))),
            Ty::mk_usize(),
        )))
    }

    fn extract_exact(&self) -> Self {
        if let SizeGuaranteeKind::AtLeast(inner) = self.kind() {
            inner.clone()
        } else {
            self.clone()
        }
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
            values: &mut Vec<SizeGuarantee>,
            f: impl Fn(u128, u128) -> u128,
        ) -> Option<u128> {
            values
                .extract_if(.., |val| val.as_usize().is_some())
                .map(|val| val.as_usize().unwrap())
                .reduce(f)
        }

        impl VisitAstMut for NormalizeSizeExpr<'_> {
            fn exit_size_guarantee_kind(&mut self, expr: &mut SizeGuaranteeKind) {
                *expr = match expr {
                    SizeGuaranteeKind::Constant(constant) => {
                        debug_assert!(constant.ty().is_usize());
                        let mut guaranteed = match constant.kind() {
                            ConstantExprKind::SizeOf(ty) => match ty.kind() {
                                TyKind::Never => SizeGuarantee::from_usize(0),
                                TyKind::Scalar(scalar_ty) => {
                                    if let Some(target) =
                                        self.krate.target_information.get(self.target)
                                    {
                                        SizeGuarantee::from_usize(
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
                                        && let Some(value) = &layout.size.guarantee
                                    {
                                        value.clone().substitute(&ty_ref.generics)
                                    } else {
                                        return;
                                    }
                                }
                            },
                            ConstantExprKind::AlignOf(ty) => match ty.kind() {
                                TyKind::Never => SizeGuarantee::from_usize(1),
                                TyKind::Scalar(scalar_ty) => {
                                    if let Some(target) =
                                        self.krate.target_information.get(self.target)
                                        && let Some(value) =
                                            target.primitive_alignments.get(scalar_ty)
                                    {
                                        SizeGuarantee::from_usize(u128::from(*value))
                                    } else {
                                        return;
                                    }
                                }
                                _ => {
                                    if let Some(ty_ref) = ty.as_adt()
                                        && let Some(decl) = self.krate.type_decls.get(ty_ref.id)
                                        && let Some(layout) = decl.layout.get(self.target)
                                        && let Some(value) = &layout.align.guarantee
                                    {
                                        value.clone().substitute(&ty_ref.generics)
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
                    SizeGuaranteeKind::FromMetadata(_) => return,
                    SizeGuaranteeKind::Max(values) => {
                        let mut is_exact = true;
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val.kind() {
                                SizeGuaranteeKind::Max(nested) => {
                                    values.extend(nested.iter().cloned())
                                }
                                SizeGuaranteeKind::AtLeast(val) => {
                                    is_exact = false;
                                    values.push(val.clone());
                                }
                                _ => values.push(val),
                            }
                        }
                        values.iter_mut().for_each(|val| {
                            self.visit(val);
                        });
                        // Get the max of the concrete values.
                        if let Some(value) = fold_concrete_values(values, std::cmp::max)
                            && value != 0
                        {
                            // Zero is the identity of `Max` so we don't push in that case.
                            values.push(SizeGuarantee::from_usize(value));
                        }
                        if values.len() == 1 {
                            values.pop().unwrap().kind().clone()
                        } else if values.is_empty() {
                            SizeGuaranteeKind::zero()
                        } else {
                            return;
                        }
                        .make(is_exact)
                    }
                    SizeGuaranteeKind::Min(values) => {
                        // Flatten nested operations.
                        for val in std::mem::take(values) {
                            match val.kind() {
                                SizeGuaranteeKind::Min(nested) => {
                                    values.extend(nested.iter().cloned())
                                }
                                _ => values.push(val),
                            }
                        }
                        values.iter_mut().for_each(|val| {
                            self.visit(val);
                        });
                        // Get the min of the concrete values.
                        // If it is only an `AtLeast`, we need to lift the `AtLeast` to the overall-result,
                        // if it is not an `AtLeast`, we can ignore all `AtLeast`s with concrete values inside.

                        if let Some((value, exact)) = values
                            .extract_if(.., |val| val.as_usize_exact().is_some())
                            .map(|val| val.as_usize_exact().unwrap())
                            .reduce(|(x, x_f), (y, y_f)| {
                                if x < y {
                                    (x, x_f)
                                } else if x > y {
                                    (y, y_f)
                                } else {
                                    (x, x_f || y_f)
                                }
                            })
                        {
                            // Zero is absorbing for `Min`.
                            if value == 0 {
                                values.clear();
                            }
                            values
                                .push(SizeGuarantee::make(SizeGuarantee::from_usize(value), exact));
                        }
                        if values.len() == 1 {
                            values.pop().unwrap().kind().clone()
                        } else {
                            return;
                        }
                    }
                    SizeGuaranteeKind::Plus(left, right) => {
                        match (left.as_usize(), right.as_usize()) {
                            (Some(left), Some(right)) => {
                                SizeGuaranteeKind::from_usize(left.strict_add(right))
                            }
                            (Some(0), None) => right.kind().clone(),
                            (None, Some(0)) => left.kind().clone(),
                            _ if left.kind().is_at_least() || right.kind().is_at_least() => {
                                let mut new_inner = SizeGuaranteeKind::Plus(
                                    left.extract_exact(),
                                    right.extract_exact(),
                                )
                                .into_expr();
                                self.visit(&mut new_inner);
                                SizeGuaranteeKind::AtLeast(new_inner)
                            }
                            _ => {
                                return;
                            }
                        }
                    }
                    SizeGuaranteeKind::Scale(base, multiplier) => {
                        match (base.as_usize(), multiplier.as_usize_literal()) {
                            (_, Some(0)) | (Some(0), _) => SizeGuaranteeKind::zero(),
                            (_, Some(1)) => base.kind().clone(),
                            (Some(base), Some(multiplier)) => {
                                SizeGuaranteeKind::from_usize(base.strict_mul(multiplier))
                            }
                            _ if base.kind().is_at_least() => {
                                let mut new_inner = SizeGuaranteeKind::Scale(
                                    base.extract_exact(),
                                    multiplier.clone(),
                                )
                                .into_expr();
                                self.visit(&mut new_inner);
                                SizeGuaranteeKind::AtLeast(new_inner)
                            }
                            _ => {
                                return;
                            }
                        }
                    }
                    SizeGuaranteeKind::AlignTo { base, target_align } => {
                        match (base.as_usize(), target_align.as_usize()) {
                            (_, Some(1)) => base.kind().clone(),
                            (Some(0), Some(align)) if align != 0 => base.kind().clone(),
                            (Some(base), Some(align)) if align != 0 => {
                                let remainder = base % align;
                                SizeGuaranteeKind::from_usize(if remainder == 0 {
                                    base
                                } else {
                                    base.strict_add(align - remainder)
                                })
                            }
                            _ if base.kind().is_at_least() || target_align.kind().is_at_least() => {
                                let mut new_inner = SizeGuaranteeKind::AlignTo {
                                    base: base.extract_exact(),
                                    target_align: target_align.extract_exact(),
                                }
                                .into_expr();
                                self.visit(&mut new_inner);
                                SizeGuaranteeKind::AtLeast(new_inner)
                            }
                            _ => return,
                        }
                    }
                    SizeGuaranteeKind::IfInhabited { .. } => {
                        // FIXME: evaluate type inhabitedness
                        return;
                    }
                    SizeGuaranteeKind::FieldOffset(_, _, _) => {
                        // TODO: Can we do anything here?
                        return;
                    }
                    SizeGuaranteeKind::AtLeast(inner) => {
                        self.visit(inner);
                        // Strip nested layers of `AtLeast` away.
                        if inner.kind().is_at_least() {
                            inner.kind().clone()
                        } else {
                            SizeGuaranteeKind::AtLeast(inner.clone())
                        }
                    }
                };
            }
        }

        NormalizeSizeExpr { krate, target }.visit(&mut self);
        self
    }

    fn as_usize(&self) -> Option<u128> {
        if let SizeGuaranteeKind::Constant(constant) = self.kind() {
            constant.as_usize_literal()
        } else {
            None
        }
    }

    fn as_usize_exact(&self) -> Option<(u128, bool)> {
        match self.kind() {
            SizeGuaranteeKind::Constant(constant) => constant.as_usize_literal().map(|u| (u, true)),
            SizeGuaranteeKind::AtLeast(inner) => inner.as_usize().map(|u| (u, false)),
            _ => None,
        }
    }

    fn from_usize(value: u128) -> Self {
        SizeGuaranteeKind::from_usize(value).into_expr()
    }

    pub fn unalign(self) -> SizeGuarantee {
        match self.kind() {
            SizeGuaranteeKind::AlignTo { base, .. } => base.clone(),
            _ => self,
        }
    }

    pub(crate) fn make(self, exact: bool) -> Self {
        if exact {
            self
        } else {
            SizeGuaranteeKind::AtLeast(self).into_expr()
        }
    }
}

impl SizeGuaranteeKind {
    pub fn zero() -> Self {
        Self::from_usize(0)
    }

    pub fn from_usize(value: u128) -> Self {
        Self::Constant(ConstantExpr::mk_usize(value))
    }

    pub fn into_expr(self) -> SizeGuarantee {
        SizeGuarantee::new(self)
    }

    pub fn add_max(&mut self, other: SizeGuarantee) {
        if let Self::Max(elems) = self {
            if let Self::Max(rhs_max) = other.kind().clone() {
                elems.extend(rhs_max);
            } else {
                elems.push(other);
            }
        } else {
            *self = Self::Max(vec![self.clone().into_expr(), other]);
        }
    }

    pub(crate) fn make(self, exact: bool) -> Self {
        if exact {
            self
        } else {
            SizeGuaranteeKind::AtLeast(self.into_expr())
        }
    }
}

impl From<SizeGuaranteeKind> for SizeGuarantee {
    fn from(kind: SizeGuaranteeKind) -> Self {
        kind.into_expr()
    }
}

impl std::ops::Deref for SizeGuarantee {
    type Target = SizeGuaranteeKind;

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
        let expr = SizeGuaranteeKind::AlignTo {
            base: SizeGuaranteeKind::Plus(
                SizeGuarantee::from_usize(2),
                SizeGuaranteeKind::Scale(SizeGuarantee::from_usize(3), ConstantExpr::mk_usize(4))
                    .into_expr(),
            )
            .into_expr(),
            target_align: SizeGuarantee::from_usize(8),
        }
        .into_expr()
        .normalize(&krate, &target);

        assert_eq!(expr.as_usize(), Some(16));
    }

    #[test]
    fn normalize_extrema_partially() {
        let (krate, target) = test_krate();
        let expr = SizeGuaranteeKind::Max(vec![
            SizeGuarantee::from_usize(2),
            SizeGuaranteeKind::Max(vec![
                SizeGuarantee::from_usize(5),
                SizeGuaranteeKind::FromMetadata(MetadataValue::DynSize).into_expr(),
            ])
            .into_expr(),
            SizeGuarantee::from_usize(3),
        ])
        .into_expr()
        .normalize(&krate, &target);

        let SizeGuaranteeKind::Max(contenders) = expr.kind() else {
            panic!("expected a partially normalized maximum")
        };
        assert_eq!(contenders.len(), 2);
        assert_eq!(contenders[1].as_usize(), Some(5));
        assert!(matches!(
            contenders[0].kind(),
            SizeGuaranteeKind::FromMetadata(MetadataValue::DynSize)
        ));

        let empty = SizeGuaranteeKind::Max(Vec::new())
            .into_expr()
            .normalize(&krate, &target);
        assert_eq!(empty.as_usize(), Some(0));
    }

    #[test]
    fn normalize_extrema_identities() {
        let (krate, target) = test_krate();
        let max = SizeGuaranteeKind::Max(vec![
            SizeGuarantee::from_usize(0),
            SizeGuaranteeKind::FromMetadata(MetadataValue::DynSize).into_expr(),
        ])
        .into_expr()
        .normalize(&krate, &target);
        let min = SizeGuaranteeKind::Min(vec![
            SizeGuarantee::from_usize(7),
            SizeGuaranteeKind::FromMetadata(MetadataValue::DynSize).into_expr(),
            SizeGuarantee::from_usize(0),
        ])
        .into_expr()
        .normalize(&krate, &target);

        assert!(matches!(
            max.kind(),
            SizeGuaranteeKind::FromMetadata(MetadataValue::DynSize)
        ));
        assert_eq!(min.as_usize(), Some(0));
    }

    #[test]
    fn normalize_if_inhabited() {
        let (krate, target) = test_krate();
        let expr = SizeGuaranteeKind::IfInhabited {
            ty: TyKind::Never.into_ty(),
            then_size: SizeGuarantee::from_usize(10),
            else_size: SizeGuaranteeKind::Plus(
                SizeGuarantee::from_usize(2),
                SizeGuarantee::from_usize(3),
            )
            .into_expr(),
        }
        .into_expr()
        .normalize(&krate, &target);

        let SizeGuaranteeKind::IfInhabited {
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

        let size = SizeGuaranteeKind::Constant(ConstantExpr::new(
            ConstantExprKind::SizeOf(TyKind::Scalar(scalar_ty).into_ty()),
            Ty::mk_usize(),
        ))
        .into_expr()
        .normalize(&krate, &target_a);
        let align = SizeGuaranteeKind::Constant(ConstantExpr::new(
            ConstantExprKind::AlignOf(TyKind::Scalar(scalar_ty).into_ty()),
            Ty::mk_usize(),
        ))
        .into_expr()
        .normalize(&krate, &target_a);
        let pointer_size = SizeGuaranteeKind::Constant(ConstantExpr::new(
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
                [TyKind::Scalar(ScalarTy::Integer(IntegerTy::Unsigned(UIntTy::U16))).into_ty()]
                    .into_iter()
                    .collect(),
            ),
            None,
        ))
        .into_ty();
        let size_of = || {
            SizeGuaranteeKind::Constant(ConstantExpr::new(
                ConstantExprKind::SizeOf(ty.clone()),
                Ty::mk_usize(),
            ))
            .into_expr()
        };

        let without_guarantee = size_of().normalize(&krate, &target);
        assert!(matches!(
            without_guarantee.kind(),
            SizeGuaranteeKind::Constant(constant)
                if matches!(constant.kind(), ConstantExprKind::SizeOf(_))
        ));

        let size = &mut krate.type_decls.get_mut(id).unwrap().layout[&target].size;
        size.guarantee = Some(
            SizeGuaranteeKind::Plus(
                SizeGuaranteeKind::Constant(ConstantExpr::new(
                    ConstantExprKind::SizeOf(generic_ty),
                    Ty::mk_usize(),
                ))
                .into_expr(),
                SizeGuarantee::from_usize(5),
            )
            .into_expr(),
        );
        let with_guarantee = size_of().normalize(&krate, &target);
        assert_eq!(with_guarantee.as_usize(), Some(7));
    }
}
