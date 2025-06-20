//! This file groups everything which is linked to implementations about [crate::types]
use crate::ast::*;
use crate::ids::Vector;
use derive_generic_visitor::*;
use std::collections::HashSet;
use std::convert::Infallible;
use std::fmt::Debug;
use std::iter::Iterator;
use std::mem;
use std::ops::Index;

impl TraitClause {
    /// Constructs the trait ref that refers to this clause.
    pub fn identity_tref(&self) -> TraitRef {
        self.identity_tref_at_depth(DeBruijnId::zero())
    }

    /// Like `identity_tref` but uses variables bound at the given depth.
    pub fn identity_tref_at_depth(&self, depth: DeBruijnId) -> TraitRef {
        TraitRef {
            kind: TraitRefKind::Clause(DeBruijnVar::bound(depth, self.clause_id)),
            trait_decl_ref: self.trait_.clone().move_under_binders(depth),
        }
    }
}

impl GenericParams {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Whether this has any explicit arguments (types, regions or const generics).
    pub fn has_explicits(&self) -> bool {
        !self.regions.is_empty() || !self.types.is_empty() || !self.const_generics.is_empty()
    }
    /// Whether this has any implicit arguments (trait clauses, outlives relations, associated type
    /// equality constraints).
    pub fn has_predicates(&self) -> bool {
        !self.trait_clauses.is_empty()
            || !self.types_outlive.is_empty()
            || !self.regions_outlive.is_empty()
            || !self.trait_type_constraints.is_empty()
    }

    /// Run some sanity checks.
    pub fn check_consistency(&self) {
        // Sanity check: check the clause ids are consistent.
        assert!(self
            .trait_clauses
            .iter()
            .enumerate()
            .all(|(i, c)| c.clause_id.index() == i));

        // Sanity check: region names are pairwise distinct (this caused trouble when generating
        // names for the backward functions in Aeneas): at some point, Rustc introduced names equal
        // to `Some("'_")` for the anonymous regions, instead of using `None` (we now check in
        // [translate_region_name] and ignore names equal to "'_").
        let mut s = HashSet::new();
        for r in &self.regions {
            if let Some(name) = &r.name {
                assert!(
                    !s.contains(name),
                    "Name \"{}\" reused for two different lifetimes",
                    name
                );
                s.insert(name);
            }
        }
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
        regions.elem_count()
            + types.elem_count()
            + const_generics.elem_count()
            + trait_clauses.elem_count()
            + regions_outlive.len()
            + types_outlive.len()
            + trait_type_constraints.elem_count()
    }

    /// Construct a set of generic arguments in the scope of `self` that matches `self` and feeds
    /// each required parameter with itself. E.g. given parameters for `<T, U> where U:
    /// PartialEq<T>`, the arguments would be `<T, U>[@TraitClause0]`.
    pub fn identity_args(&self) -> GenericArgs {
        self.identity_args_at_depth(DeBruijnId::zero())
    }

    /// Like `identity_args` but uses variables bound at the given depth.
    pub fn identity_args_at_depth(&self, depth: DeBruijnId) -> GenericArgs {
        GenericArgs {
            regions: self
                .regions
                .map_ref_indexed(|id, _| Region::Var(DeBruijnVar::bound(depth, id))),
            types: self
                .types
                .map_ref_indexed(|id, _| TyKind::TypeVar(DeBruijnVar::bound(depth, id)).into_ty()),
            const_generics: self
                .const_generics
                .map_ref_indexed(|id, _| ConstGeneric::Var(DeBruijnVar::bound(depth, id))),
            trait_refs: self
                .trait_clauses
                .map_ref(|clause| clause.identity_tref_at_depth(depth)),
        }
    }
}

impl<T> Binder<T> {
    pub fn new(kind: BinderKind, params: GenericParams, skip_binder: T) -> Self {
        Self {
            params,
            skip_binder,
            kind,
        }
    }

    /// Substitute the provided arguments for the variables bound in this binder and return the
    /// substituted inner value.
    pub fn apply(self, args: &GenericArgs) -> T
    where
        T: TyVisitable,
    {
        self.skip_binder.substitute(args)
    }
}

impl<T: AstVisitable> Binder<Binder<T>> {
    /// Flatten two levels of binders into a single one.
    pub fn flatten(self) -> Binder<T> {
        #[derive(Visitor)]
        struct FlattenVisitor<'a> {
            shift_by: &'a GenericParams,
            binder_depth: DeBruijnId,
        }
        impl VisitAstMut for FlattenVisitor<'_> {
            fn enter_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
                self.binder_depth = self.binder_depth.incr()
            }
            fn exit_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
                self.binder_depth = self.binder_depth.decr()
            }
            fn enter_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
                self.binder_depth = self.binder_depth.incr()
            }
            fn exit_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
                self.binder_depth = self.binder_depth.decr()
            }
            fn enter_de_bruijn_id(&mut self, db_id: &mut DeBruijnId) {
                if *db_id > self.binder_depth {
                    // We started visiting at the inner binder, so in this branch we're either
                    // mentioning the outer binder or a binder further beyond. Either way we
                    // decrease the depth; variables that point to the outer binder don't have to
                    // be shifted.
                    *db_id = db_id.decr();
                }
            }
            fn enter_region(&mut self, x: &mut Region) {
                if let Region::Var(var) = x
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.regions.slot_count();
                }
            }
            fn enter_ty_kind(&mut self, x: &mut TyKind) {
                if let TyKind::TypeVar(var) = x
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.types.slot_count();
                }
            }
            fn enter_const_generic(&mut self, x: &mut ConstGeneric) {
                if let ConstGeneric::Var(var) = x
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.const_generics.slot_count();
                }
            }
            fn enter_trait_ref_kind(&mut self, x: &mut TraitRefKind) {
                if let TraitRefKind::Clause(var) = x
                    && let Some(id) = var.bound_at_depth_mut(self.binder_depth)
                {
                    *id += self.shift_by.trait_clauses.slot_count();
                }
            }
        }

        // We will concatenate both sets of params.
        let mut outer_params = self.params;

        // The inner value needs to change:
        // - at binder level 0 we shift all variable ids to match the concatenated params;
        // - at binder level > 0 we decrease binding level because there's one fewer binder.
        let mut bound_value = self.skip_binder.skip_binder;
        let _ = bound_value.drive_mut(&mut FlattenVisitor {
            shift_by: &outer_params,
            binder_depth: Default::default(),
        });

        // The inner params must also be updated, as they can refer to themselves and the outer
        // one.
        let mut inner_params = self.skip_binder.params;
        let _ = inner_params.drive_mut(&mut FlattenVisitor {
            shift_by: &outer_params,
            binder_depth: Default::default(),
        });
        inner_params
            .regions
            .iter_mut()
            .for_each(|v| v.index += outer_params.regions.slot_count());
        inner_params
            .types
            .iter_mut()
            .for_each(|v| v.index += outer_params.types.slot_count());
        inner_params
            .const_generics
            .iter_mut()
            .for_each(|v| v.index += outer_params.const_generics.slot_count());
        inner_params
            .trait_clauses
            .iter_mut()
            .for_each(|v| v.clause_id += outer_params.trait_clauses.slot_count());

        let GenericParams {
            regions,
            types,
            const_generics,
            trait_clauses,
            regions_outlive,
            types_outlive,
            trait_type_constraints,
        } = &inner_params;
        outer_params.regions.extend_from_slice(regions);
        outer_params.types.extend_from_slice(types);
        outer_params
            .const_generics
            .extend_from_slice(const_generics);
        outer_params.trait_clauses.extend_from_slice(trait_clauses);
        outer_params
            .regions_outlive
            .extend_from_slice(regions_outlive);
        outer_params.types_outlive.extend_from_slice(types_outlive);
        outer_params
            .trait_type_constraints
            .extend_from_slice(trait_type_constraints);

        Binder {
            params: outer_params,
            skip_binder: bound_value,
            kind: BinderKind::Other,
        }
    }
}

impl<T> RegionBinder<T> {
    /// Wrap the value in an empty region binder, shifting variables appropriately.
    pub fn empty(x: T) -> Self
    where
        T: TyVisitable,
    {
        RegionBinder {
            regions: Default::default(),
            skip_binder: x.move_under_binder(),
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> RegionBinder<U> {
        RegionBinder {
            regions: self.regions,
            skip_binder: f(self.skip_binder),
        }
    }

    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> RegionBinder<U> {
        RegionBinder {
            regions: self.regions.clone(),
            skip_binder: f(&self.skip_binder),
        }
    }

    /// Substitute the bound variables with erased lifetimes.
    pub fn erase(self) -> T
    where
        T: AstVisitable,
    {
        let args = GenericArgs {
            regions: self.regions.map_ref_indexed(|_, _| Region::Erased),
            ..GenericArgs::empty()
        };
        self.skip_binder.substitute(&args)
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
        regions.elem_count()
            + types.elem_count()
            + const_generics.elem_count()
            + trait_refs.elem_count()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Whether this has any explicit arguments (types, regions or const generics).
    pub fn has_explicits(&self) -> bool {
        !self.regions.is_empty() || !self.types.is_empty() || !self.const_generics.is_empty()
    }
    /// Whether this has any implicit arguments (trait refs).
    pub fn has_implicits(&self) -> bool {
        !self.trait_refs.is_empty()
    }

    pub fn empty() -> Self {
        GenericArgs {
            regions: Default::default(),
            types: Default::default(),
            const_generics: Default::default(),
            trait_refs: Default::default(),
        }
    }

    pub fn new_for_builtin(types: Vector<TypeVarId, Ty>) -> Self {
        GenericArgs {
            types,
            ..Self::empty()
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

    pub fn new_types(types: Vector<TypeVarId, Ty>) -> Self {
        Self {
            types,
            ..Self::empty()
        }
    }

    /// Check whether this matches the given `GenericParams`.
    /// TODO: check more things, e.g. that the trait refs use the correct trait and generics.
    pub fn matches(&self, params: &GenericParams) -> bool {
        params.regions.elem_count() == self.regions.elem_count()
            && params.types.elem_count() == self.types.elem_count()
            && params.const_generics.elem_count() == self.const_generics.elem_count()
            && params.trait_clauses.elem_count() == self.trait_refs.elem_count()
    }

    /// Return the same generics, but where we pop the first type arguments.
    /// This is useful for trait references (for pretty printing for instance),
    /// because the first type argument is the type for which the trait is
    /// implemented.
    pub fn pop_first_type_arg(&self) -> (Ty, Self) {
        let mut generics = self.clone();
        let mut it = mem::take(&mut generics.types).into_iter();
        let ty = it.next().unwrap();
        generics.types = it.collect();
        (ty, generics)
    }

    /// Concatenate this set of arguments with another one. Use with care, you must manage the
    /// order of arguments correctly.
    pub fn concat(mut self, other: &Self) -> Self {
        let Self {
            regions,
            types,
            const_generics,
            trait_refs,
        } = other;
        self.regions.extend_from_slice(regions);
        self.types.extend_from_slice(types);
        self.const_generics.extend_from_slice(const_generics);
        self.trait_refs.extend_from_slice(trait_refs);
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

    pub fn to_unsigned(&self) -> Self {
        match self {
            IntegerTy::Isize => IntegerTy::Usize,
            IntegerTy::I8 => IntegerTy::U8,
            IntegerTy::I16 => IntegerTy::U16,
            IntegerTy::I32 => IntegerTy::U32,
            IntegerTy::I64 => IntegerTy::U64,
            IntegerTy::I128 => IntegerTy::U128,
            _ => *self,
        }
    }
}

/// A value of type `T` bound by the generic parameters of item
/// `item`. Used when dealing with multiple items at a time, to
/// ensure we don't mix up generics.
///
/// To get the value, use `under_binder_of` or `subst_for`.
#[derive(Debug, Clone, Copy)]
pub struct ItemBinder<ItemId, T> {
    pub item_id: ItemId,
    val: T,
}

impl<ItemId, T> ItemBinder<ItemId, T>
where
    ItemId: Debug + Copy + PartialEq,
{
    pub fn new(item_id: ItemId, val: T) -> Self {
        Self { item_id, val }
    }

    pub fn as_ref(&self) -> ItemBinder<ItemId, &T> {
        ItemBinder {
            item_id: self.item_id,
            val: &self.val,
        }
    }

    pub fn map_bound<U>(self, f: impl FnOnce(T) -> U) -> ItemBinder<ItemId, U> {
        ItemBinder {
            item_id: self.item_id,
            val: f(self.val),
        }
    }

    fn assert_item_id(&self, item_id: ItemId) {
        assert_eq!(
            self.item_id, item_id,
            "Trying to use item bound for {:?} as if it belonged to {:?}",
            self.item_id, item_id
        );
    }

    /// Assert that the value is bound for item `item_id`, and returns it. This is used when we
    /// plan to store the returned value inside that item.
    pub fn under_binder_of(self, item_id: ItemId) -> T {
        self.assert_item_id(item_id);
        self.val
    }

    /// Given generic args for `item_id`, assert that the value is bound for `item_id` and
    /// substitute it with the provided generic arguments. Because the arguments are bound in the
    /// context of another item, so it the resulting substituted value.
    pub fn substitute<OtherItem: Debug + Copy + PartialEq>(
        self,
        args: ItemBinder<OtherItem, &GenericArgs>,
    ) -> ItemBinder<OtherItem, T>
    where
        ItemId: Into<AnyTransId>,
        T: TyVisitable,
    {
        args.map_bound(|args| self.val.substitute(args))
    }
}

/// Dummy item identifier that represents the current item when not ambiguous.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CurrentItem;

impl<T> ItemBinder<CurrentItem, T> {
    pub fn under_current_binder(self) -> T {
        self.val
    }
}

impl Ty {
    /// Return the unit type
    pub fn mk_unit() -> Ty {
        Self::mk_tuple(vec![])
    }

    pub fn mk_tuple(tys: Vec<Ty>) -> Ty {
        TyKind::Adt(TypeDeclRef {
            id: TypeId::Tuple,
            generics: Box::new(GenericArgs::new_for_builtin(tys.into())),
        })
        .into_ty()
    }

    pub fn mk_slice(ty: Ty) -> Ty {
        TyKind::Adt(TypeDeclRef {
            id: TypeId::Builtin(BuiltinTy::Slice),
            generics: Box::new(GenericArgs::new_for_builtin(vec![ty].into())),
        })
        .into_ty()
    }
    /// Return true if it is actually unit (i.e.: 0-tuple)
    pub fn is_unit(&self) -> bool {
        match self.as_tuple() {
            Some(tys) => tys.is_empty(),
            None => false,
        }
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
            TyKind::Adt(ty_ref) if let TypeId::Builtin(BuiltinTy::Box) = ty_ref.id => true,
            _ => false,
        }
    }

    pub fn as_box(&self) -> Option<&Ty> {
        match self.kind() {
            TyKind::Adt(ty_ref) if let TypeId::Builtin(BuiltinTy::Box) = ty_ref.id => {
                Some(&ty_ref.generics.types[0])
            }
            _ => None,
        }
    }

    pub fn as_array_or_slice(&self) -> Option<&Ty> {
        match self.kind() {
            TyKind::Adt(ty_ref)
                if let TypeId::Builtin(BuiltinTy::Array | BuiltinTy::Slice) = ty_ref.id =>
            {
                Some(&ty_ref.generics.types[0])
            }
            _ => None,
        }
    }

    pub fn as_tuple(&self) -> Option<&Vector<TypeVarId, Ty>> {
        match self.kind() {
            TyKind::Adt(ty_ref) if let TypeId::Tuple = ty_ref.id => Some(&ty_ref.generics.types),
            _ => None,
        }
    }

    pub fn as_adt(&self) -> Option<&TypeDeclRef> {
        self.kind().as_adt()
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

impl TypeDeclRef {
    pub fn new(id: TypeId, generics: GenericArgs) -> Self {
        Self {
            id,
            generics: Box::new(generics),
        }
    }
}

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

/// Visitor for the [TyVisitable::substitute] function.
/// This substitutes variables bound at the level where we start to substitute (level 0).
#[derive(Visitor)]
pub(crate) struct SubstVisitor<'a> {
    generics: &'a GenericArgs,
    self_ref: &'a TraitRefKind,
    // Tracks the depth of binders we're inside of.
    // Important: we must update it whenever we go inside a binder.
    binder_depth: DeBruijnId,
}

impl<'a> SubstVisitor<'a> {
    pub(crate) fn new(generics: &'a GenericArgs, self_ref: &'a TraitRefKind) -> Self {
        Self {
            generics,
            self_ref,
            binder_depth: DeBruijnId::zero(),
        }
    }

    /// Process the variable, either modifying the variable in-place or returning the new value to
    /// assign to the type/region/const generic/trait ref that was this variable.
    fn process_var<Id, T>(&self, var: &mut DeBruijnVar<Id>) -> Option<T>
    where
        Id: Copy,
        GenericArgs: Index<Id, Output = T>,
        T: Clone + TyVisitable,
    {
        use std::cmp::Ordering::*;
        match var {
            DeBruijnVar::Bound(dbid, varid) => match (*dbid).cmp(&self.binder_depth) {
                Equal => Some(
                    self.generics[*varid]
                        .clone()
                        .move_under_binders(self.binder_depth),
                ),
                Greater => {
                    // This is bound outside the binder we're substituting for.
                    *dbid = dbid.decr();
                    None
                }
                Less => None,
            },
            DeBruijnVar::Free(..) => None,
        }
    }
}

impl VisitAstMut for SubstVisitor<'_> {
    fn enter_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
        self.binder_depth = self.binder_depth.incr()
    }
    fn exit_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
        self.binder_depth = self.binder_depth.decr()
    }
    fn enter_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
        self.binder_depth = self.binder_depth.incr()
    }
    fn exit_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
        self.binder_depth = self.binder_depth.decr()
    }

    fn exit_region(&mut self, r: &mut Region) {
        match r {
            Region::Var(var) => {
                if let Some(new_r) = self.process_var(var) {
                    *r = new_r;
                }
            }
            _ => (),
        }
    }

    fn exit_ty(&mut self, ty: &mut Ty) {
        let new_ty = ty.with_kind_mut(|kind| match kind {
            TyKind::TypeVar(var) => self.process_var(var),
            _ => None,
        });
        if let Some(new_ty) = new_ty {
            *ty = new_ty
        }
    }

    fn exit_const_generic(&mut self, cg: &mut ConstGeneric) {
        match cg {
            ConstGeneric::Var(var) => {
                if let Some(new_cg) = self.process_var(var) {
                    *cg = new_cg;
                }
            }
            _ => (),
        }
    }

    fn exit_constant_expr(&mut self, ce: &mut ConstantExpr) {
        match &mut ce.value {
            RawConstantExpr::Var(var) => {
                if let Some(new_ce) = self.process_var(var) {
                    ce.value = match new_ce {
                        ConstGeneric::Global(id) => RawConstantExpr::Global(GlobalDeclRef {
                            id,
                            generics: Box::new(GenericArgs::empty()),
                        }),
                        ConstGeneric::Var(var) => RawConstantExpr::Var(var),
                        ConstGeneric::Value(lit) => RawConstantExpr::Literal(lit),
                    };
                }
            }
            _ => (),
        }
    }

    fn exit_trait_ref_kind(&mut self, kind: &mut TraitRefKind) {
        match kind {
            TraitRefKind::SelfId => {
                *kind = self.self_ref.clone().move_under_binders(self.binder_depth);
            }
            TraitRefKind::Clause(var) => {
                if let Some(new_tr) = self.process_var(var) {
                    *kind = new_tr.kind;
                }
            }
            _ => (),
        }
    }
}

/// Types that are involved at the type-level and may be substituted around.
pub trait TyVisitable: Sized + AstVisitable {
    fn substitute(self, generics: &GenericArgs) -> Self {
        self.substitute_with_self(generics, &TraitRefKind::SelfId)
    }

    fn substitute_with_self(mut self, generics: &GenericArgs, self_ref: &TraitRefKind) -> Self {
        let _ = self.drive_mut(&mut SubstVisitor::new(generics, self_ref));
        self
    }

    /// Move under one binder.
    fn move_under_binder(self) -> Self {
        self.move_under_binders(DeBruijnId::one())
    }

    /// Move under `depth` binders.
    fn move_under_binders(mut self, depth: DeBruijnId) -> Self {
        if !depth.is_zero() {
            let Continue(()) = self.visit_db_id::<Infallible>(|id| {
                *id = id.plus(depth);
                Continue(())
            });
        }
        self
    }

    /// Move from under one binder.
    fn move_from_under_binder(self) -> Option<Self> {
        self.move_from_under_binders(DeBruijnId::one())
    }

    /// Move the value out of `depth` binders. Returns `None` if it contains a variable bound in
    /// one of these `depth` binders.
    fn move_from_under_binders(mut self, depth: DeBruijnId) -> Option<Self> {
        self.visit_db_id::<()>(|id| match id.sub(depth) {
            Some(sub) => {
                *id = sub;
                Continue(())
            }
            None => Break(()),
        })
        .is_continue()
        .then_some(self)
    }

    /// Visit the de Bruijn ids contained in `self`, as seen from the outside of `self`. This means
    /// that any variable bound inside `self` will be skipped, and all the seen indices will count
    /// from the outside of self.
    fn visit_db_id<B>(
        &mut self,
        f: impl FnMut(&mut DeBruijnId) -> ControlFlow<B>,
    ) -> ControlFlow<B> {
        struct Wrap<F> {
            f: F,
            depth: DeBruijnId,
        }
        impl<B, F> Visitor for Wrap<F>
        where
            F: FnMut(&mut DeBruijnId) -> ControlFlow<B>,
        {
            type Break = B;
        }
        impl<B, F> VisitAstMut for Wrap<F>
        where
            F: FnMut(&mut DeBruijnId) -> ControlFlow<B>,
        {
            fn enter_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
                self.depth = self.depth.incr()
            }
            fn exit_region_binder<T: AstVisitable>(&mut self, _: &mut RegionBinder<T>) {
                self.depth = self.depth.decr()
            }
            fn enter_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
                self.depth = self.depth.incr()
            }
            fn exit_binder<T: AstVisitable>(&mut self, _: &mut Binder<T>) {
                self.depth = self.depth.decr()
            }

            fn visit_de_bruijn_id(&mut self, x: &mut DeBruijnId) -> ControlFlow<Self::Break> {
                if let Some(mut shifted) = x.sub(self.depth) {
                    (self.f)(&mut shifted)?;
                    *x = shifted.plus(self.depth)
                }
                Continue(())
            }
        }
        self.drive_mut(&mut Wrap {
            f,
            depth: DeBruijnId::zero(),
        })
    }
}

impl TypeDecl {
    /// Looks up the variant corresponding to the tag (i.e. the in-memory bytes that represent the discriminant).
    /// Returns `None` for types that don't have a relevant discriminant (e.g. uninhabited types).
    ///
    /// If the `tag` does not correspond to any valid discriminant but there is a niche,
    /// the resulting `VariantId` will be for the untagged variant [`TagEncoding::Niche::untagged_variant`].
    pub fn get_variant_from_tag(&self, tag: ScalarValue) -> Option<VariantId> {
        let layout = self.layout.as_ref()?;
        if layout.uninhabited {
            return None;
        };
        let discr_layout = layout.discriminant_layout.as_ref()?;

        let variant_for_tag =
            layout
                .variant_layouts
                .iter_indexed()
                .find_map(|(id, variant_layout)| {
                    if variant_layout.tag == Some(tag) {
                        Some(id)
                    } else {
                        None
                    }
                });

        match &discr_layout.encoding {
            TagEncoding::Direct => {
                assert_eq!(tag.get_integer_ty(), discr_layout.tag_ty);
                variant_for_tag
            }
            TagEncoding::Niche { untagged_variant } => variant_for_tag.or(Some(*untagged_variant)),
        }
    }
}

impl Layout {
    pub fn is_variant_uninhabited(&self, variant_id: VariantId) -> bool {
        if let Some(v) = self.variant_layouts.get(variant_id) {
            v.uninhabited
        } else {
            false
        }
    }
}

impl<T: AstVisitable> TyVisitable for T {}

impl Eq for TraitClause {}

mk_index_impls!(GenericArgs.regions[RegionId]: Region);
mk_index_impls!(GenericArgs.types[TypeVarId]: Ty);
mk_index_impls!(GenericArgs.const_generics[ConstGenericVarId]: ConstGeneric);
mk_index_impls!(GenericArgs.trait_refs[TraitClauseId]: TraitRef);
mk_index_impls!(GenericParams.regions[RegionId]: RegionVar);
mk_index_impls!(GenericParams.types[TypeVarId]: TypeVar);
mk_index_impls!(GenericParams.const_generics[ConstGenericVarId]: ConstGenericVar);
mk_index_impls!(GenericParams.trait_clauses[TraitClauseId]: TraitClause);
