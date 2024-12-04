//! This file groups everything which is linked to implementations about [crate::types]
use crate::types::*;
use crate::{common::visitor_event::VisitEvent, ids::Vector};
use derive_visitor::{Drive, DriveMut, Event, Visitor, VisitorMut};
use std::{collections::HashMap, iter::Iterator};

impl DeBruijnId {
    pub fn zero() -> Self {
        DeBruijnId { index: 0 }
    }

    pub fn new(index: usize) -> Self {
        DeBruijnId { index }
    }

    pub fn is_zero(&self) -> bool {
        self.index == 0
    }

    pub fn incr(&self) -> Self {
        DeBruijnId {
            index: self.index + 1,
        }
    }

    pub fn decr(&self) -> Self {
        DeBruijnId {
            index: self.index - 1,
        }
    }
}

impl TypeVar {
    pub fn new(index: TypeVarId, name: String) -> TypeVar {
        TypeVar { index, name }
    }
}

impl GenericParams {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn has_predicates(&self) -> bool {
        !self.trait_clauses.is_empty()
            || !self.types_outlive.is_empty()
            || !self.regions_outlive.is_empty()
            || !self.trait_type_constraints.is_empty()
    }

    pub fn len(&self) -> usize {
        let GenericParams {
            regions,
            types,
            const_generics,
            trait_clauses,
            regions_outlive,
            types_outlive,
            trait_type_constraints,
        } = self;
        regions.len()
            + types.len()
            + const_generics.len()
            + trait_clauses.len()
            + regions_outlive.len()
            + types_outlive.len()
            + trait_type_constraints.len()
    }

    /// Construct a set of generic arguments in the scope of `self` that matches `self` and feeds
    /// each required parameter with itself. E.g. given parameters for `<T, U> where U:
    /// PartialEq<T>`, the arguments would be `<T, U>[@TraitClause0]`.
    pub fn identity_args(&self) -> GenericArgs {
        GenericArgs {
            regions: self
                .regions
                .iter_indexed()
                .map(|(id, _)| Region::BVar(DeBruijnId::new(0), id))
                .collect(),
            types: self
                .types
                .iter_indexed()
                .map(|(id, _)| TyKind::TypeVar(id).into_ty())
                .collect(),
            const_generics: self
                .const_generics
                .iter_indexed()
                .map(|(id, _)| ConstGeneric::Var(id))
                .collect(),
            trait_refs: self
                .trait_clauses
                .iter_indexed()
                .map(|(id, clause)| TraitRef {
                    kind: TraitRefKind::Clause(id),
                    trait_decl_ref: clause.trait_.clone(),
                })
                .collect(),
        }
    }
}

impl GenericArgs {
    pub fn len(&self) -> usize {
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        regions.len() + types.len() + const_generics.len() + trait_refs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn empty() -> Self {
        GenericArgs::default()
    }

    pub fn new_from_types(types: Vector<TypeVarId, Ty>) -> Self {
        GenericArgs {
            types,
            ..Self::default()
        }
    }

    pub fn new(
        regions: Vector<RegionId, Region>,
        types: Vector<TypeVarId, Ty>,
        const_generics: Vector<ConstGenericVarId, ConstGeneric>,
        trait_refs: Vector<TraitClauseId, TraitRef>,
    ) -> Self {
        Self {
            regions,
            types,
            const_generics,
            trait_refs,
        }
    }

    /// Check whether this matches the given `GenericParams`.
    /// TODO: check more things, e.g. that the trait refs use the correct trait and generics.
    pub fn matches(&self, params: &GenericParams) -> bool {
        params.regions.len() == self.regions.len()
            && params.types.len() == self.types.len()
            && params.const_generics.len() == self.const_generics.len()
            && params.trait_clauses.len() == self.trait_refs.len()
    }

    /// Return the same generics, but where we pop the first type arguments.
    /// This is useful for trait references (for pretty printing for instance),
    /// because the first type argument is the type for which the trait is
    /// implemented.
    pub fn pop_first_type_arg(&self) -> (Ty, Self) {
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        let mut it = types.iter();
        let ty = it.next().unwrap().clone();
        let types = it.cloned().collect();
        (
            ty,
            GenericArgs {
                regions: regions.clone(),
                types,
                const_generics: const_generics.clone(),
                trait_refs: trait_refs.clone(),
            },
        )
    }

    /// Concatenate this set of arguments with another one. Use with care, you must manage the
    /// order of arguments correctly.
    pub fn concat(mut self, other: &Self) -> Self {
        let Self {
            regions,
            types,
            const_generics,
            trait_refs,
        } = &mut self;
        regions.extend(other.regions.iter().cloned());
        types.extend(other.types.iter().cloned());
        const_generics.extend(other.const_generics.iter().cloned());
        trait_refs.extend(other.trait_refs.iter().cloned());
        self
    }
}

impl IntegerTy {
    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            IntegerTy::Isize
                | IntegerTy::I8
                | IntegerTy::I16
                | IntegerTy::I32
                | IntegerTy::I64
                | IntegerTy::I128
        )
    }

    pub fn is_unsigned(&self) -> bool {
        !(self.is_signed())
    }

    /// Return the size (in bytes) of an integer of the proper type
    pub fn size(&self) -> usize {
        use std::mem::size_of;
        match self {
            IntegerTy::Isize => size_of::<isize>(),
            IntegerTy::I8 => size_of::<i8>(),
            IntegerTy::I16 => size_of::<i16>(),
            IntegerTy::I32 => size_of::<i32>(),
            IntegerTy::I64 => size_of::<i64>(),
            IntegerTy::I128 => size_of::<i128>(),
            IntegerTy::Usize => size_of::<isize>(),
            IntegerTy::U8 => size_of::<u8>(),
            IntegerTy::U16 => size_of::<u16>(),
            IntegerTy::U32 => size_of::<u32>(),
            IntegerTy::U64 => size_of::<u64>(),
            IntegerTy::U128 => size_of::<u128>(),
        }
    }
}

impl Ty {
    /// Return true if it is actually unit (i.e.: 0-tuple)
    pub fn is_unit(&self) -> bool {
        match self.kind() {
            TyKind::Adt(TypeId::Tuple, args) => {
                assert!(args.regions.is_empty());
                assert!(args.const_generics.is_empty());
                args.types.is_empty()
            }
            _ => false,
        }
    }

    /// Return the unit type
    pub fn mk_unit() -> Ty {
        TyKind::Adt(TypeId::Tuple, GenericArgs::empty()).into_ty()
    }

    /// Return true if this is a scalar type
    pub fn is_scalar(&self) -> bool {
        match self.kind() {
            TyKind::Literal(kind) => kind.is_integer(),
            _ => false,
        }
    }

    pub fn is_unsigned_scalar(&self) -> bool {
        match self.kind() {
            TyKind::Literal(LiteralTy::Integer(kind)) => kind.is_unsigned(),
            _ => false,
        }
    }

    pub fn is_signed_scalar(&self) -> bool {
        match self.kind() {
            TyKind::Literal(LiteralTy::Integer(kind)) => kind.is_signed(),
            _ => false,
        }
    }

    /// Return true if the type is Box
    pub fn is_box(&self) -> bool {
        match self.kind() {
            TyKind::Adt(TypeId::Builtin(BuiltinTy::Box), generics) => {
                assert!(generics.regions.is_empty());
                assert!(generics.types.len() == 1);
                assert!(generics.const_generics.is_empty());
                true
            }
            _ => false,
        }
    }

    pub fn as_box(&self) -> Option<&Ty> {
        match self.kind() {
            TyKind::Adt(TypeId::Builtin(BuiltinTy::Box), generics) => {
                assert!(generics.regions.is_empty());
                assert!(generics.types.len() == 1);
                assert!(generics.const_generics.is_empty());
                Some(&generics.types[0])
            }
            _ => None,
        }
    }

    pub fn as_array_or_slice(&self) -> Option<&Ty> {
        match self.kind() {
            TyKind::Adt(TypeId::Builtin(BuiltinTy::Array | BuiltinTy::Slice), generics) => {
                assert!(generics.regions.is_empty());
                assert!(generics.types.len() == 1);
                Some(&generics.types[0])
            }
            _ => None,
        }
    }

    pub fn as_tuple(&self) -> Option<&Vector<TypeVarId, Ty>> {
        match self.kind() {
            TyKind::Adt(TypeId::Tuple, generics) => {
                assert!(generics.regions.is_empty());
                assert!(generics.const_generics.is_empty());
                Some(&generics.types)
            }
            _ => None,
        }
    }

    pub fn as_adt(&self) -> Option<(TypeId, &GenericArgs)> {
        match self.kind() {
            TyKind::Adt(id, generics) => Some((*id, generics)),
            _ => None,
        }
    }

    /// Wrap a visitor to make it visit the contents of types it encounters.
    pub fn visit_inside<V>(visitor: V) -> VisitInsideTy<V> {
        VisitInsideTy {
            visitor,
            cache: None,
        }
    }
    /// Wrap a stateless visitor to make it visit the contents of types it encounters. This will
    /// only visit each type once and cache the results. For this to behave as expecte, the visitor
    /// must be stateless.
    /// The performance impact does not appear to be significant.
    pub fn visit_inside_stateless<V>(visitor: V) -> VisitInsideTy<V> {
        VisitInsideTy {
            visitor,
            cache: Some(Default::default()),
        }
    }
}

impl TyKind {
    pub fn into_ty(self) -> Ty {
        Ty::new(self)
    }
}

impl From<TyKind> for Ty {
    fn from(kind: TyKind) -> Ty {
        kind.into_ty()
    }
}

/// Convenience for migration purposes.
impl std::ops::Deref for Ty {
    type Target = TyKind;

    fn deref(&self) -> &Self::Target {
        self.kind()
    }
}
/// For deref patterns.
unsafe impl std::ops::DerefPure for Ty {}

impl Field {
    /// The new name for this field, as suggested by the `#[charon::rename]` attribute.
    pub fn renamed_name(&self) -> Option<&str> {
        self.attr_info.rename.as_deref().or(self.name.as_deref())
    }

    /// Whether this field has a `#[charon::opaque]` annotation.
    pub fn is_opaque(&self) -> bool {
        self.attr_info
            .attributes
            .iter()
            .any(|attr| attr.is_opaque())
    }
}

impl Variant {
    /// The new name for this variant, as suggested by the `#[charon::rename]` and
    /// `#[charon::variants_prefix]` attributes.
    pub fn renamed_name(&self) -> &str {
        self.attr_info
            .rename
            .as_deref()
            .unwrap_or(self.name.as_ref())
    }

    /// Whether this variant has a `#[charon::opaque]` annotation.
    pub fn is_opaque(&self) -> bool {
        self.attr_info
            .attributes
            .iter()
            .any(|attr| attr.is_opaque())
    }
}

impl RefKind {
    pub fn mutable(x: bool) -> Self {
        if x {
            Self::Mut
        } else {
            Self::Shared
        }
    }
}

// The derive macro doesn't handle generics.
impl<T: Drive> Drive for RegionBinder<T> {
    fn drive<V: Visitor>(&self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        self.regions.drive(visitor);
        self.skip_binder.drive(visitor);
        visitor.visit(self, Event::Exit);
    }
}

impl<T: DriveMut> DriveMut for RegionBinder<T> {
    fn drive_mut<V: VisitorMut>(&mut self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        self.regions.drive_mut(visitor);
        self.skip_binder.drive_mut(visitor);
        visitor.visit(self, Event::Exit);
    }
}

/// See comment on `Ty`: this impl doesn't recurse into the contents of the type.
impl Drive for Ty {
    fn drive<V: Visitor>(&self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        visitor.visit(self, Event::Exit);
    }
}

/// See comment on `Ty`: this impl doesn't recurse into the contents of the type.
impl DriveMut for Ty {
    fn drive_mut<V: VisitorMut>(&mut self, visitor: &mut V) {
        visitor.visit(self, Event::Enter);
        visitor.visit(self, Event::Exit);
    }
}

pub struct VisitInsideTy<V> {
    visitor: V,
    /// If `Some`, record the effected visits and don't do them again. Only valid if the wrapped
    /// visitor is stateless.
    cache: Option<HashMap<(Ty, VisitEvent), Ty>>,
}

impl<V> VisitInsideTy<V> {
    pub fn into_inner(self) -> V {
        self.visitor
    }
}

impl<V: Visitor> Visitor for VisitInsideTy<V> {
    fn visit(&mut self, item: &dyn std::any::Any, event: Event) {
        match item.downcast_ref::<Ty>() {
            Some(ty) => {
                let visit_event: VisitEvent = (&event).into();

                // Shortcut if we already visited this.
                if let Some(cache) = &self.cache
                    && cache.contains_key(&(ty.clone(), visit_event))
                {
                    return;
                }

                // Recursively visit the type.
                self.visitor.visit(ty, event);
                if matches!(visit_event, VisitEvent::Enter) {
                    ty.drive_inner(self);
                }

                // Remember we just visited that.
                if let Some(cache) = &mut self.cache {
                    cache.insert((ty.clone(), visit_event), ty.clone());
                }
            }
            None => {
                self.visitor.visit(item, event);
            }
        }
    }
}
impl<V: VisitorMut> VisitorMut for VisitInsideTy<V> {
    fn visit(&mut self, item: &mut dyn std::any::Any, event: Event) {
        match item.downcast_mut::<Ty>() {
            Some(ty) => {
                let visit_event: VisitEvent = (&event).into();

                // Shortcut if we already visited this.
                if let Some(cache) = &self.cache
                    && let Some(new_ty) = cache.get(&(ty.clone(), visit_event))
                {
                    *ty = new_ty.clone();
                    return;
                }

                // Recursively visit the type.
                let pre_visit = ty.clone();
                self.visitor.visit(ty, event);
                if matches!(visit_event, VisitEvent::Enter) {
                    ty.drive_inner_mut(self);
                }

                // Cache the visit we just did.
                if let Some(cache) = &mut self.cache {
                    let post_visit = ty.clone();
                    cache.insert((pre_visit, visit_event), post_visit);
                }
            }
            None => {
                self.visitor.visit(item, event);
            }
        }
    }
}

impl<V> std::ops::Deref for VisitInsideTy<V> {
    type Target = V;
    fn deref(&self) -> &Self::Target {
        &self.visitor
    }
}
impl<V> std::ops::DerefMut for VisitInsideTy<V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.visitor
    }
}

type FnTys = (Vec<Ty>, Ty);

/// Visitor for the [Ty::substitute] function.
#[derive(VisitorMut)]
#[visitor(
    PolyTraitDeclRef(enter, exit),
    FnTys(enter, exit),
    Region(exit),
    Ty(exit),
    ConstGeneric(exit),
    TraitRef(exit)
)]
struct SubstVisitor<'a> {
    generics: &'a GenericArgs,
    // Tracks the depth of binders we're inside of.
    // Important: we must update it whenever we go inside a binder. Visitors are not generic so we
    // must handle all the specific cases by hand. So far there's:
    // - `PolyTraitDeclRef`
    // - The contents of `TyKind::Arrow`
    binder_depth: DeBruijnId,
}

impl<'a> SubstVisitor<'a> {
    pub(crate) fn new(generics: &'a GenericArgs) -> VisitInsideTy<Self> {
        Ty::visit_inside(Self {
            generics,
            binder_depth: DeBruijnId::zero(),
        })
    }

    fn enter_poly_trait_decl_ref(&mut self, _: &mut PolyTraitDeclRef) {
        self.binder_depth = self.binder_depth.incr();
    }

    fn exit_poly_trait_decl_ref(&mut self, _: &mut PolyTraitDeclRef) {
        self.binder_depth = self.binder_depth.decr();
    }

    fn enter_fn_tys(&mut self, _: &mut FnTys) {
        self.binder_depth = self.binder_depth.incr();
    }

    fn exit_fn_tys(&mut self, _: &mut FnTys) {
        self.binder_depth = self.binder_depth.decr();
    }

    fn exit_region(&mut self, r: &mut Region) {
        match r {
            Region::BVar(db, id) => {
                if *db == self.binder_depth {
                    *r = self.generics.regions.get(*id).unwrap().clone()
                }
            }
            _ => (),
        }
    }

    fn exit_ty(&mut self, ty: &mut Ty) {
        match ty.kind() {
            TyKind::TypeVar(id) => *ty = self.generics.types.get(*id).unwrap().clone(),
            _ => (),
        }
    }

    fn exit_const_generic(&mut self, cg: &mut ConstGeneric) {
        match cg {
            ConstGeneric::Var(id) => *cg = self.generics.const_generics.get(*id).unwrap().clone(),
            _ => (),
        }
    }

    fn exit_trait_ref(&mut self, tr: &mut TraitRef) {
        match &mut tr.kind {
            TraitRefKind::Clause(id) => *tr = self.generics.trait_refs.get(*id).unwrap().clone(),
            _ => (),
        }
    }
}

impl Ty {
    pub fn substitute(&mut self, generics: &GenericArgs) {
        self.drive_inner_mut(&mut SubstVisitor::new(generics));
    }
}
