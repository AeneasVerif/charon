use derive_generic_visitor::*;
use serde::de::Deserializer;
use serde::ser::Serializer;
use serde_state::{DeserializeState, SerializeState};

use crate::ast::*;

bitflags::bitflags! {
    #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct TypeFlags: u8 {
        const HAS_ERASED_OR_BODY_REGIONS = 1 << 0;
        const MENTIONS_SELF_CLAUSE = 1 << 1;
        const USES_SIZE_METADATA = 1 << 2;
        const POTENTIALLY_NORMALIZABLE = 1 << 3;
        const MENTIONS_FREE_VAR = 1 << 4;
    }
}

/// Various bits of information about the contents of a type-level value.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeInfo {
    pub max_de_bruijn_id: Option<DeBruijnId>,
    pub flags: TypeFlags,
}

impl TypeInfo {
    pub fn compute(value: &impl TyVisitable) -> Self {
        #[derive(Visitor)]
        struct TypeInfoVisitor {
            info: TypeInfo,
            binder_depth: DeBruijnId,
        }

        impl VisitorWithBinderDepth for TypeInfoVisitor {
            fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
                &mut self.binder_depth
            }
        }
        impl VisitAst for TypeInfoVisitor {
            fn visit<T: AstVisitable>(&mut self, value: &T) -> ControlFlow<Self::Break> {
                VisitWithBinderDepth::new(self).visit(value)
            }

            fn visit_with_cached_type_info<T: AstVisitable>(
                &mut self,
                value: &WithCachedTypeInfo<T>,
            ) -> ControlFlow<Self::Break> {
                let TypeInfo {
                    max_de_bruijn_id,
                    flags,
                } = value.info;
                self.info.flags |= flags;
                if let Some(id) = max_de_bruijn_id {
                    self.visit_de_bruijn_id(&id);
                }
                Continue(())
            }

            fn visit_de_bruijn_id(&mut self, &id: &DeBruijnId) -> ControlFlow<Self::Break> {
                if let Some(id) = id.sub(self.binder_depth) {
                    self.info.max_de_bruijn_id = Some(
                        self.info
                            .max_de_bruijn_id
                            .unwrap_or(DeBruijnId::ZERO)
                            .max(id),
                    );
                }
                Continue(())
            }

            fn enter_de_bruijn_var<T: AstVisitable + Idx>(&mut self, var: &DeBruijnVar<T>) {
                if matches!(var, DeBruijnVar::Free(_)) {
                    self.info.flags.insert(TypeFlags::MENTIONS_FREE_VAR);
                }
            }

            fn enter_region(&mut self, region: &Region) {
                match region {
                    Region::Body(..) | Region::Erased => self
                        .info
                        .flags
                        .insert(TypeFlags::HAS_ERASED_OR_BODY_REGIONS),
                    Region::Var(..) | Region::Static => {}
                }
            }

            fn enter_ty_kind(&mut self, kind: &TyKind) {
                match kind {
                    TyKind::TraitType(..) | TyKind::PtrMetadata(..) => {
                        self.info.flags.insert(TypeFlags::POTENTIALLY_NORMALIZABLE);
                    }
                    TyKind::TypeVar(..)
                    | TyKind::Scalar(..)
                    | TyKind::Array(..)
                    | TyKind::Slice(..)
                    | TyKind::Adt(..)
                    | TyKind::Ref(..)
                    | TyKind::RawPtr(..)
                    | TyKind::FnDef(..)
                    | TyKind::FnPtr(..)
                    | TyKind::DynTrait(..)
                    | TyKind::Pattern(..)
                    | TyKind::Never
                    | TyKind::Error(..) => {}
                }
            }

            fn enter_trait_ref_kind(&mut self, kind: &TraitRefKind) {
                match kind {
                    TraitRefKind::ParentClause(..) | TraitRefKind::ItemClause { .. } => {
                        self.info.flags.insert(TypeFlags::POTENTIALLY_NORMALIZABLE)
                    }
                    TraitRefKind::SelfId => self.info.flags.insert(TypeFlags::MENTIONS_SELF_CLAUSE),
                    TraitRefKind::TraitImpl(..)
                    | TraitRefKind::Clause(..)
                    | TraitRefKind::BuiltinOrAuto { .. }
                    | TraitRefKind::Dyn
                    | TraitRefKind::Unknown(_) => {}
                }
            }

            fn enter_constant_expr_kind(&mut self, kind: &ConstantExprKind) {
                match kind {
                    ConstantExprKind::Global(..)
                    | ConstantExprKind::TraitConst(..)
                    | ConstantExprKind::Call(..)
                    | ConstantExprKind::Discriminant(..)
                    | ConstantExprKind::VTableRef(..)
                    | ConstantExprKind::SizeOf(..)
                    | ConstantExprKind::AlignOf(..)
                    | ConstantExprKind::OffsetOf(..) => {
                        self.info.flags.insert(TypeFlags::POTENTIALLY_NORMALIZABLE);
                    }
                    ConstantExprKind::Var(..)
                    | ConstantExprKind::Bool(..)
                    | ConstantExprKind::Integer(..)
                    | ConstantExprKind::Char(..)
                    | ConstantExprKind::Float(..)
                    | ConstantExprKind::Adt(..)
                    | ConstantExprKind::Array(..)
                    | ConstantExprKind::Ref(..)
                    | ConstantExprKind::Ptr(..)
                    | ConstantExprKind::Str(..)
                    | ConstantExprKind::ByteStr(..)
                    | ConstantExprKind::FnDef(..)
                    | ConstantExprKind::FnPtr(..)
                    | ConstantExprKind::PtrNoProvenance(..)
                    | ConstantExprKind::TypeId(..)
                    | ConstantExprKind::RawMemory(..)
                    | ConstantExprKind::Opaque(..) => {}
                }
            }

            fn enter_size_expr_kind(&mut self, kind: &SizeExprKind) {
                match kind {
                    SizeExprKind::Constant(_) => {}
                    SizeExprKind::FromMetadata(_) => {
                        self.info.flags.insert(TypeFlags::USES_SIZE_METADATA);
                    }
                    SizeExprKind::Max(..)
                    | SizeExprKind::Min(..)
                    | SizeExprKind::Plus(..)
                    | SizeExprKind::Scale(..)
                    | SizeExprKind::AtLeast(..)
                    | SizeExprKind::AlignTo { .. }
                    | SizeExprKind::IfInhabited { .. } => {
                        self.info.flags.insert(TypeFlags::POTENTIALLY_NORMALIZABLE);
                    }
                }
            }
        }

        let mut visitor = TypeInfoVisitor {
            info: Self::default(),
            binder_depth: DeBruijnId::zero(),
        };
        let Continue(()) = visitor.visit(value);
        visitor.info
    }
}

/// A wrapper that caches type-specific information about the contained value.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Drive, DriveTwo)]
pub struct WithCachedTypeInfo<T> {
    pub value: T,
    info: TypeInfo,
}

impl<T: TyVisitable> WithCachedTypeInfo<T> {
    pub fn new(value: T) -> Self {
        let info = value.type_info();
        Self { value, info }
    }

    pub fn with_value_mut<R>(&mut self, f: impl FnOnce(&mut T) -> R) -> R {
        let ret = f(&mut self.value);
        // Recompute the cached values.
        self.info = self.value.type_info();
        ret
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for WithCachedTypeInfo<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

impl<T> std::ops::Deref for WithCachedTypeInfo<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<'s, T: TyVisitable, V> DriveMut<'s, V> for WithCachedTypeInfo<T>
where
    V: Visitor + for<'a> VisitMut<'a, T>,
{
    fn drive_inner_mut(&'s mut self, v: &mut V) -> ControlFlow<V::Break> {
        self.with_value_mut(|value| v.visit(value))
    }
}

impl<T, State> SerializeState<State> for WithCachedTypeInfo<T>
where
    T: SerializeState<State>,
{
    fn serialize_state<S>(&self, state: &State, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.value.serialize_state(state, serializer)
    }
}

impl<'de, T, State> DeserializeState<'de, State> for WithCachedTypeInfo<T>
where
    T: DeserializeState<'de, State> + TyVisitable,
{
    fn deserialize_state<D>(state: &State, deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        T::deserialize_state(state, deserializer).map(Self::new)
    }
}
