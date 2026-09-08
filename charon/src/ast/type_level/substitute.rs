use crate::ast::*;
use derive_generic_visitor::*;
use std::borrow::Cow;
use std::convert::Infallible;
use std::fmt::Debug;
use std::iter::Iterator;

/// Visitor for type-level variables. Used to visit the variables contained in a value, as seen
/// from the outside of the value. This means that any variable bound inside the value will be
/// skipped, and all the seen De Bruijn indices will count from the outside of the value. The
/// returned value, if any, will be put in place of the variable.
pub trait VarsVisitor {
    fn visit_erased_region(&mut self) -> Option<Region> {
        None
    }
    fn visit_region_var(&mut self, _v: RegionDbVar) -> Option<Region> {
        None
    }
    fn visit_type_var(&mut self, _v: TypeDbVar) -> Option<Ty> {
        None
    }
    fn visit_const_generic_var(&mut self, _v: ConstGenericDbVar) -> Option<ConstantExprKind> {
        None
    }
    fn visit_clause_var(&mut self, _v: ClauseDbVar) -> Option<TraitRefKind> {
        None
    }
    fn visit_self_clause(&mut self) -> Option<TraitRefKind> {
        None
    }
    fn visit_metadata_value(&mut self, _value: &MetadataValue) {}
}

/// Visitor for the [TyVisitable::substitute] function.
/// This substitutes variables bound at the level where we start to substitute (level 0).
#[derive(Visitor)]
pub(crate) struct SubstVisitor<'a> {
    generics: &'a GenericArgs,
    self_ref: Option<&'a TraitRefKind>,
    /// Whether to substitute explicit variables only (types, regions, const generics).
    explicits_only: bool,
    had_error: bool,
    allow_metadata: bool,
}
impl<'a> SubstVisitor<'a> {
    pub(crate) fn new(
        generics: &'a GenericArgs,
        self_ref: Option<&'a TraitRefKind>,
        explicits_only: bool,
    ) -> Self {
        Self {
            generics,
            self_ref,
            explicits_only,
            had_error: false,
            allow_metadata: false,
        }
    }

    pub(crate) fn new_allow_metadata(
        generics: &'a GenericArgs,
        self_ref: Option<&'a TraitRefKind>,
        explicits_only: bool,
    ) -> Self {
        Self {
            generics,
            self_ref,
            explicits_only,
            had_error: false,
            allow_metadata: true,
        }
    }

    pub fn visit<T: TyVisitable>(mut self, mut x: T) -> Result<T, GenericsMismatch> {
        x.visit_vars(&mut self);
        if self.had_error {
            Err(GenericsMismatch)
        } else {
            Ok(x)
        }
    }

    /// Returns the value for this variable, if any.
    fn process_var<Id, T>(
        &mut self,
        var: DeBruijnVar<Id>,
        get: impl Fn(Id) -> Option<&'a T>,
    ) -> Option<T>
    where
        Id: Copy,
        T: Clone + TyVisitable,
        DeBruijnVar<Id>: Into<T>,
    {
        match var {
            DeBruijnVar::Bound(dbid, varid) => {
                Some(if let Some(dbid) = dbid.sub(DeBruijnId::one()) {
                    // This is bound outside the binder we're substituting for.
                    DeBruijnVar::Bound(dbid, varid).into()
                } else {
                    match get(varid) {
                        Some(v) => v.clone(),
                        None => {
                            self.had_error = true;
                            return None;
                        }
                    }
                })
            }
            DeBruijnVar::Free(..) => None,
        }
    }
}
impl VarsVisitor for SubstVisitor<'_> {
    fn visit_region_var(&mut self, v: RegionDbVar) -> Option<Region> {
        self.process_var(v, |id| self.generics.regions.get(id))
    }
    fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
        self.process_var(v, |id| self.generics.types.get(id))
    }
    fn visit_const_generic_var(&mut self, v: ConstGenericDbVar) -> Option<ConstantExprKind> {
        self.process_var(v, |id| {
            self.generics.const_generics.get(id).map(|c| c.kind())
        })
    }
    fn visit_clause_var(&mut self, v: ClauseDbVar) -> Option<TraitRefKind> {
        if self.explicits_only {
            None
        } else {
            self.process_var(v, |id| Some(&self.generics.trait_refs.get(id)?.kind))
        }
    }
    fn visit_self_clause(&mut self) -> Option<TraitRefKind> {
        Some(self.self_ref.cloned().expect(
            "used `substitute` on an item coming from a trait; \
            use `substitute_with_self` or `substitute_inner_binder` instead.",
        ))
    }
    fn visit_metadata_value(&mut self, _value: &MetadataValue) {
        if !self.allow_metadata {
            self.had_error = true;
        }
    }
}

#[derive(Debug)]
pub struct GenericsMismatch;

/// Types that are involved at the type-level and may be substituted around.
pub trait TyVisitable: Sized + AstVisitable {
    /// Visit the variables contained in `self`, as seen from the outside of `self`. This means
    /// that any variable bound inside `self` will be skipped, and all the seen De Bruijn indices
    /// will count from the outside of `self`.
    fn visit_vars(&mut self, v: &mut impl VarsVisitor) {
        #[derive(Visitor)]
        struct Wrap<'v, V> {
            v: &'v mut V,
            depth: DeBruijnId,
        }
        impl<V> VisitorWithBinderDepth for Wrap<'_, V> {
            fn binder_depth_mut(&mut self) -> &mut DeBruijnId {
                &mut self.depth
            }
        }
        impl<V: VarsVisitor> VisitAstMut for Wrap<'_, V> {
            fn visit<T: AstVisitable>(&mut self, x: &mut T) -> ControlFlow<Self::Break> {
                VisitWithBinderDepth::new(self).visit(x)
            }

            fn exit_region(&mut self, r: &mut Region) {
                match r {
                    Region::Var(var)
                        if let Some(var) = var.move_out_from_depth(self.depth)
                            && let Some(new_r) = self.v.visit_region_var(var) =>
                    {
                        *r = new_r.move_under_binders(self.depth);
                    }
                    Region::Erased | Region::Body(..)
                        if let Some(new_r) = self.v.visit_erased_region() =>
                    {
                        *r = new_r.move_under_binders(self.depth);
                    }
                    _ => (),
                }
            }
            fn exit_ty(&mut self, ty: &mut Ty) {
                if let TyKind::TypeVar(var) = ty.kind()
                    && let Some(var) = var.move_out_from_depth(self.depth)
                    && let Some(new_ty) = self.v.visit_type_var(var)
                {
                    *ty = new_ty.move_under_binders(self.depth);
                }
            }
            fn exit_constant_expr_kind(&mut self, kind: &mut ConstantExprKind) {
                if let ConstantExprKind::Var(var) = kind
                    && let Some(var) = var.move_out_from_depth(self.depth)
                    && let Some(new_cg) = self.v.visit_const_generic_var(var)
                {
                    *kind = new_cg.move_under_binders(self.depth);
                }
            }
            fn exit_trait_ref_kind(&mut self, kind: &mut TraitRefKind) {
                match kind {
                    TraitRefKind::SelfId => {
                        if let Some(new_kind) = self.v.visit_self_clause() {
                            *kind = new_kind.move_under_binders(self.depth);
                        }
                    }
                    TraitRefKind::Clause(var) => {
                        if let Some(var) = var.move_out_from_depth(self.depth)
                            && let Some(new_kind) = self.v.visit_clause_var(var)
                        {
                            *kind = new_kind.move_under_binders(self.depth);
                        }
                    }
                    _ => {}
                }
            }
            fn enter_metadata_value(&mut self, value: &mut MetadataValue) {
                self.v.visit_metadata_value(value);
            }
        }
        Wrap {
            v,
            depth: DeBruijnId::zero(),
        }
        .visit(self);
    }

    /// Substitute the generic variables inside `self` by replacing them with the provided values.
    /// Note: if `self` is an item that comes from a `TraitDecl`, you must use
    /// `substitute_with_self` or `substitute_inner_binder`, otherwise you'll get panics.
    fn substitute(self, generics: &GenericArgs) -> Self {
        SubstVisitor::new(generics, None, false)
            .visit(self)
            .unwrap()
    }
    /// Substitute the generic variables inside `self` by replacing them with the provided values.
    /// This is appropriate when substituting an inner binder.
    fn substitute_inner_binder(self, generics: &GenericArgs) -> Self {
        self.substitute_with_self(generics, &TraitRefKind::SelfId)
    }
    /// Substitute only the type, region and const generic args.
    fn substitute_explicits(self, generics: &GenericArgs) -> Self {
        SubstVisitor::new(generics, None, true).visit(self).unwrap()
    }
    /// Substitute the generic variables as well as the `TraitRefKind::SelfId` trait ref.
    fn substitute_with_self(self, generics: &GenericArgs, self_ref: &TraitRefKind) -> Self {
        self.try_substitute_with_self(generics, self_ref).unwrap()
    }
    /// Substitute the generic variables as well as the `TraitRefKind::SelfId` trait ref.
    fn substitute_with_tref(self, tref: &TraitRef) -> Self {
        let pred = tref.trait_decl_ref.clone().erase();
        self.substitute_with_self(&pred.generics, &tref.kind)
    }
    /// Substitute the generic variables as well as the `TraitRefKind::SelfId` trait ref.
    fn try_substitute_with_tref(self, tref: &TraitRef) -> Result<Self, GenericsMismatch> {
        let pred = tref.trait_decl_ref.clone().erase();
        self.try_substitute_with_self(&pred.generics, &tref.kind)
    }

    fn try_substitute(self, generics: &GenericArgs) -> Result<Self, GenericsMismatch> {
        SubstVisitor::new(generics, None, false).visit(self)
    }
    fn try_substitute_with_self(
        self,
        generics: &GenericArgs,
        self_ref: &TraitRefKind,
    ) -> Result<Self, GenericsMismatch> {
        SubstVisitor::new(generics, Some(self_ref), false).visit(self)
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

    /// Replace all the erased regions by the output of the provided function. Binders levels are
    /// handled automatically.
    fn replace_erased_regions(mut self, f: impl FnMut() -> Region) -> Self {
        #[derive(Visitor)]
        struct RefreshErasedRegions<F>(F);
        impl<F: FnMut() -> Region> VarsVisitor for RefreshErasedRegions<F> {
            fn visit_erased_region(&mut self) -> Option<Region> {
                Some((self.0)())
            }
        }
        self.visit_vars(&mut RefreshErasedRegions(f));
        self
    }
}

impl<T: AstVisitable> TyVisitable for T {}

/// A value of type `T` applied to some `GenericArgs`, except we havent applied them yet to avoid a
/// deep clone.
#[derive(Debug, Clone)]
pub struct Substituted<'a, T> {
    pub val: &'a T,
    pub generics: Cow<'a, GenericArgs>,
    pub trait_self: Option<&'a TraitRefKind>,
}

impl<'a, T> Substituted<'a, T> {
    pub fn new(val: &'a T, generics: &'a GenericArgs) -> Self {
        Self {
            val,
            generics: Cow::Borrowed(generics),
            trait_self: None,
        }
    }
    pub fn new_for_trait(
        val: &'a T,
        generics: &'a GenericArgs,
        trait_self: &'a TraitRefKind,
    ) -> Self {
        Self {
            val,
            generics: Cow::Borrowed(generics),
            trait_self: Some(trait_self),
        }
    }
    pub fn new_for_trait_ref(val: &'a T, tref: &'a TraitRef) -> Self {
        Self {
            val,
            generics: Cow::Owned(*tref.trait_decl_ref.clone().erase().generics),
            trait_self: Some(&tref.kind),
        }
    }

    pub fn rebind<U>(&self, val: &'a U) -> Substituted<'a, U> {
        Substituted {
            val,
            generics: self.generics.clone(),
            trait_self: self.trait_self,
        }
    }

    pub fn substitute(&self) -> T
    where
        T: TyVisitable + Clone,
    {
        self.try_substitute().unwrap()
    }
    pub fn try_substitute(&self) -> Result<T, GenericsMismatch>
    where
        T: TyVisitable + Clone,
    {
        match self.trait_self {
            None => self.val.clone().try_substitute(&self.generics),
            Some(trait_self) => self
                .val
                .clone()
                .try_substitute_with_self(&self.generics, trait_self),
        }
    }

    pub fn iter<Item: 'a>(&self) -> impl Iterator<Item = Substituted<'a, Item>>
    where
        &'a T: IntoIterator<Item = &'a Item>,
    {
        self.val.into_iter().map(move |x| self.rebind(x))
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
        ItemId: Into<ItemId>,
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
