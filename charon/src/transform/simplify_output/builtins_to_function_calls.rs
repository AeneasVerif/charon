//! Desugar built-in operations and array/slice indexing to standard library function calls.

use std::collections::{HashMap, HashSet};

use crate::llbc_ast::*;
use crate::name_matcher::NamePattern;
use crate::transform::ctx::{BodyTransformCtx, LlbcStatementTransformCtx};
use crate::transform::{CowBox, TransformCtx};
use derive_generic_visitor::*;
use itertools::Itertools;

use crate::transform::ctx::LlbcPass;

fn mk_fn_ptr(ctx: &TransformCtx, id: ItemId, mut generics: GenericArgs) -> FnPtr {
    if ctx.options.add_destruct_bounds
        && let Some(item) = ctx.translated.get_item(id)
    {
        // Charon adds `Destruct` as the last trait clause of every generic item.
        let trait_decl_ref = item
            .generic_params()
            .trait_clauses
            .last()
            .unwrap()
            .trait_
            .clone()
            .substitute(&generics);
        let kind = TraitRefKind::BuiltinOrAuto {
            builtin_data: BuiltinImplData::UntrackedDestruct,
            parent_trait_refs: Default::default(),
            types: Default::default(),
            vtable: None,
        };
        generics
            .trait_refs
            .push(TraitRef::new(kind, trait_decl_ref));
    }
    let fun_id = *id.as_fun().unwrap();
    FnPtr::new(FnPtrKind::Fun(FunId::Regular(fun_id)), generics)
}

/// Instantiate the trait impl that provides the given method.
fn method_impl_trait_ref(
    ctx: &TransformCtx,
    id: ItemId,
    fun_generics: &GenericArgs,
) -> Option<TraitRef> {
    let fun_id = *id.as_fun()?;
    let fun = ctx.translated.fun_decls.get(fun_id)?;
    let FunSource::TraitImpl { impl_ref, .. } = &fun.src else {
        return None;
    };
    let impl_ref = impl_ref.clone().substitute(fun_generics);
    let trait_impl = ctx.translated.trait_impls.get(impl_ref.id)?;
    let trait_decl_ref =
        RegionBinder::empty(trait_impl.impl_trait.clone().substitute(&impl_ref.generics));
    Some(TraitRef::new(
        TraitRefKind::TraitImpl(impl_ref),
        trait_decl_ref,
    ))
}

fn index_method_types(
    params: &GenericParams,
    elem_ty: &Ty,
    index_ty: &Ty,
    output_ty: &Ty,
) -> Option<IndexVec<TypeVarId, Ty>> {
    let mut types: IndexVec<TypeVarId, Ty> =
        [elem_ty.clone(), index_ty.clone()].into_iter().collect();
    match params.types.len() {
        // With `--lift-associated-types`, `Index::Output` is an explicit type parameter.
        3 => {
            types.push(output_ty.clone());
        }
        2 => {}
        _ => return None,
    }
    Some(types)
}

fn transform_operation(std_items: &Transform, ctx: &TransformCtx, statement: &mut Statement) {
    match &statement.kind {
        // Transform the ArrayToSlice unop.
        StatementKind::Assign(
            place,
            Rvalue::UnaryOp(
                UnOp::Cast(CastKind::Unsize(src_ty, tgt_ty, UnsizingMetadata::Length(_))),
                operand,
            ),
        ) => {
            if let (TyKind::Ref(_, src_ty, src_kind), TyKind::Ref(_, tgt_ty, tgt_kind)) =
                (src_ty.kind(), tgt_ty.kind())
                && let TyKind::Array(elem_ty, len, elem_ty_is_sized) = src_ty.kind()
                && let TyKind::Slice(..) = tgt_ty.kind()
            {
                // In MIR terminology, we go from &[T; l] to &[T] which means we
                // effectively "unsize" the type, as `l` no longer appears in the
                // destination type. At runtime, the converse happens: the length
                // materializes into the fat pointer.
                assert!(src_kind == tgt_kind);
                // We could avoid the clone operations below if we take the content of
                // the statement. In practice, this shouldn't have much impact.
                let item = match src_kind {
                    RefKind::Shared => StdItem::ArrayAsSlice,
                    RefKind::Mut => StdItem::ArrayAsMutSlice,
                };
                let Some(&fun_id) = std_items.item_map.get(&item) else {
                    return;
                };
                let generics = GenericArgs::new(
                    [Region::Erased].into(),
                    [elem_ty.clone()].into(),
                    [len.clone()].into(),
                    elem_ty_is_sized.iter().cloned().collect(),
                );
                statement.kind = StatementKind::Call {
                    call: Call {
                        func: FnOperand::Regular(mk_fn_ptr(ctx, fun_id, generics)),
                        args: vec![operand.clone()],
                        dest: place.clone(),
                    },
                    on_unwind: Block::new_unreachable(statement.span),
                };
            }
        }
        // Transform the array aggregates to function calls.
        StatementKind::Assign(place, Rvalue::Repeat(operand, ty, len, ty_is_copy)) => {
            // We could avoid the clone operations below if we take the content of
            // the statement. In practice, this shouldn't have much impact.
            let Some(&fun_id) = std_items.item_map.get(&StdItem::ArrayRepeat) else {
                return;
            };
            let TyKind::Array(_, _, ty_is_sized) = place.ty().kind() else {
                return;
            };
            // `Copy`'s explicit `Clone` supertrait follows its optional implicit marker clause.
            // `array::repeat` has the corresponding `Clone` bound at the same position.
            let clone_clause_id = TraitClauseId::new(usize::from(ty_is_sized.is_some()));
            let Some(ty_is_clone) = ty_is_copy
                .clone()
                .project_parent_clause(&ctx.translated, clone_clause_id)
            else {
                return;
            };
            let generics = GenericArgs::new(
                [].into(),
                [ty.clone()].into(),
                [len.clone()].into(),
                ty_is_sized.iter().cloned().chain([ty_is_clone]).collect(),
            );
            statement.kind = StatementKind::Call {
                call: Call {
                    func: FnOperand::Regular(mk_fn_ptr(ctx, fun_id, generics)),
                    args: vec![operand.clone()],
                    dest: place.clone(),
                },
                on_unwind: Block::new_unreachable(statement.span),
            };
        }
        _ => {}
    }
}

/// We replace some place constructors with function calls. To do that, we explore all the places
/// in a body and deconstruct a given place access into intermediate assignments.
///
/// We accumulate the new assignments as statements in the visitor, and at the end we insert these
/// statements before the one that was just explored.
#[derive(Visitor)]
struct IndexVisitor<'a, 'b> {
    ctx: &'b mut LlbcStatementTransformCtx<'a>,
    std_items: &'b Transform,
    // When we visit a place, we need to know if it is being accessed mutably or not. Whenever we
    // visit something that contains a place we push the relevant mutability on this stack.
    // Unfortunately this requires us to be very careful to catch all the cases where we see
    // places.
    place_mutability_stack: Vec<bool>,
}

impl<'a, 'b> IndexVisitor<'a, 'b> {
    /// transform `place: subplace[i]` into indexing function calls for `subplace` and `i`
    fn transform_place(&mut self, mut_access: bool, place: &mut Place) {
        use ProjectionElem::*;
        // This function is naturally called recusively, so `subplace` cannot be another `Index` or `Subslice`.
        // Hence, `subplace`, if still projecting, must be either a `Deref` or a `Field`.
        let Some((subplace, pe @ (Index { .. } | Subslice { .. }))) = place.as_projection() else {
            return;
        };

        let (ty, len, ty_is_sized) = match subplace.ty.kind() {
            TyKind::Array(ty, len, ty_is_sized) => (ty.clone(), Some(len.clone()), ty_is_sized),
            TyKind::Slice(ty, ty_is_sized) => (ty.clone(), None, ty_is_sized),
            _ => unreachable!("Indexing can only be done on arrays or slices"),
        };

        let mutability = RefKind::mutable(mut_access);
        let item = match (pe.is_subslice(), mutability) {
            (false, RefKind::Shared) => StdItem::SliceIndex,
            (false, RefKind::Mut) => StdItem::SliceIndexMut,
            (true, RefKind::Shared) => StdItem::RangeIndex,
            (true, RefKind::Mut) => StdItem::RangeIndexMut,
        };
        let Some(&index_fun_id) = self.std_items.item_map.get(&item) else {
            return;
        };
        let Some(index_fun) = index_fun_id
            .as_fun()
            .and_then(|id| self.ctx.ctx.translated.fun_decls.get(*id))
        else {
            return;
        };
        let index_generics = GenericArgs::new(
            [Region::Erased].into(),
            [ty.clone()].into(),
            [].into(),
            ty_is_sized.iter().cloned().collect(),
        );
        let index_fn_ptr = mk_fn_ptr(self.ctx.ctx, index_fun_id, index_generics);
        let index_ty = index_fun.signature.inputs[0]
            .clone()
            .substitute(&index_fn_ptr.generics);

        let output_inner_ty = if matches!(pe, Index { .. }) {
            ty.clone()
        } else {
            TyKind::Slice(ty.clone(), ty_is_sized.clone()).into_ty()
        };
        let output_ty = {
            TyKind::Ref(
                Region::Erased,
                output_inner_ty.clone(),
                RefKind::mutable(mut_access),
            )
            .into_ty()
        };

        // Push the statements:
        // `storage_live(tmp0)`
        // `tmp0 = &{mut}p`
        let input_var =
            self.ctx
                .borrow_to_new_var(subplace.clone(), BorrowKind::mutable(mut_access), None);

        // Construct the arguments to pass to the indexing function.
        let (last_arg, from_end) = match &pe {
            Index {
                offset: x,
                from_end,
                ..
            }
            | Subslice {
                to: x, from_end, ..
            } => (x.as_ref().clone(), *from_end),
            _ => unreachable!(),
        };
        let to_idx = self
            .ctx
            .compute_subslice_end_idx(subplace, last_arg, from_end);
        let index = match &pe {
            Index { .. } => to_idx,
            Subslice { from, .. } => {
                let Some(range_ref) = index_ty.as_adt().cloned() else {
                    return;
                };
                let range_ty = TyKind::Adt(range_ref.clone()).into_ty();
                let range_var = self.ctx.fresh_var(None, range_ty);
                self.ctx.insert_assn_stmt(
                    range_var.clone(),
                    Rvalue::Aggregate(
                        AggregateKind::Adt(range_ref, None, None),
                        vec![from.as_ref().clone(), to_idx],
                    ),
                );
                Operand::Move(range_var)
            }
            _ => unreachable!(),
        };

        let (index_fn_ptr, args) = if let Some(len) = len {
            let (array_item, slice_item) = match mutability {
                RefKind::Shared => (StdItem::ArrayIndex, StdItem::SliceIndexImpl),
                RefKind::Mut => (StdItem::ArrayIndexMut, StdItem::SliceIndexMutImpl),
            };
            let Some(&array_fun_id) = self.std_items.item_map.get(&array_item) else {
                return;
            };
            let Some(array_fun) = array_fun_id
                .as_fun()
                .and_then(|id| self.ctx.ctx.translated.fun_decls.get(*id))
            else {
                return;
            };
            let Some(&slice_fun_id) = self.std_items.item_map.get(&slice_item) else {
                return;
            };
            let Some(slice_fun) = slice_fun_id
                .as_fun()
                .and_then(|id| self.ctx.ctx.translated.fun_decls.get(*id))
            else {
                return;
            };

            let Some(slice_types) =
                index_method_types(&slice_fun.generics, &ty, &index_ty, &output_inner_ty)
            else {
                return;
            };
            let mut slice_generics =
                GenericArgs::new([Region::Erased].into(), slice_types, [].into(), [].into());
            let Some(slice_index_trait_ref) =
                method_impl_trait_ref(self.ctx.ctx, index_fun_id, &index_fn_ptr.generics)
            else {
                return;
            };
            let index_ty_is_sized = if ty_is_sized.is_some() {
                let Some(clause) = slice_fun.generics.trait_clauses.get(TraitClauseId::new(1))
                else {
                    return;
                };
                let trait_decl_ref = clause.trait_.clone().substitute_explicits(&slice_generics);
                let Some(meta_sized) = slice_index_trait_ref
                    .clone()
                    .project_parent_clause(&self.ctx.ctx.translated, TraitClauseId::ZERO)
                else {
                    return;
                };
                Some(TraitRef::new(
                    TraitRefKind::BuiltinOrAuto {
                        builtin_data: BuiltinImplData::Sized,
                        parent_trait_refs: [meta_sized].into_iter().collect(),
                        types: Default::default(),
                        vtable: None,
                    },
                    trait_decl_ref,
                ))
            } else {
                None
            };
            slice_generics.trait_refs = ty_is_sized
                .iter()
                .cloned()
                .chain(index_ty_is_sized.iter().cloned())
                .chain([slice_index_trait_ref])
                .collect();
            let slice_fn_ptr = mk_fn_ptr(self.ctx.ctx, slice_fun_id, slice_generics);
            let Some(slice_trait_ref) =
                method_impl_trait_ref(self.ctx.ctx, slice_fun_id, &slice_fn_ptr.generics)
            else {
                return;
            };

            let Some(array_types) =
                index_method_types(&array_fun.generics, &ty, &index_ty, &output_inner_ty)
            else {
                return;
            };
            let array_generics = GenericArgs::new(
                [Region::Erased].into(),
                array_types,
                [len].into(),
                ty_is_sized
                    .iter()
                    .cloned()
                    .chain(index_ty_is_sized)
                    .chain([slice_trait_ref])
                    .collect(),
            );
            (
                mk_fn_ptr(self.ctx.ctx, array_fun_id, array_generics),
                vec![Operand::Move(input_var), index],
            )
        } else {
            (index_fn_ptr, vec![index, Operand::Move(input_var)])
        };

        // Call the indexing function:
        // `storage_live(tmp1)`
        // `tmp1 = {Array,Slice}{Mut,Shared}{Index,SubSlice}(move tmp0, <other args>)`
        let output_var = {
            let output_var = self.ctx.fresh_var(None, output_ty);
            let index_call = Call {
                func: FnOperand::Regular(index_fn_ptr),
                args,
                dest: output_var.clone(),
            };
            let kind = StatementKind::Call {
                call: index_call,
                on_unwind: Block::new_unreachable(self.ctx.span),
            };
            self.ctx
                .statements
                .push(Statement::new(self.ctx.span, kind));
            output_var
        };

        // Update the place.
        *place = output_var.project(ProjectionElem::Deref, output_inner_ty);
    }

    /// Calls `self.visit_inner()` with `mutability` pushed on the stack.
    fn visit_inner_with_mutability<T>(
        &mut self,
        x: &mut T,
        mutability: bool,
    ) -> ControlFlow<Infallible>
    where
        T: for<'s> DriveMut<'s, BodyVisitableWrapper<Self>> + BodyVisitable,
    {
        self.place_mutability_stack.push(mutability);
        self.visit_inner(x)?;
        self.place_mutability_stack.pop();
        Continue(())
    }
}

/// The visitor methods.
impl VisitBodyMut for IndexVisitor<'_, '_> {
    /// We explore places from the inside-out --- recursion naturally happens here.
    fn exit_place(&mut self, place: &mut Place) {
        // We have intercepted every traversal that would reach a place and pushed the correct
        // mutability on the stack.
        let mut_access = *self.place_mutability_stack.last().unwrap();
        self.transform_place(mut_access, place);
    }

    fn visit_operand(&mut self, x: &mut Operand) -> ControlFlow<Infallible> {
        match x {
            Operand::Move(_) => self.visit_inner_with_mutability(x, true),
            Operand::Copy(_) => self.visit_inner_with_mutability(x, false),
            Operand::Const(..) => self.visit_inner(x),
        }
    }

    fn visit_call(&mut self, x: &mut Call) -> ControlFlow<Infallible> {
        self.visit_inner_with_mutability(x, true)
    }

    fn visit_fn_operand(&mut self, x: &mut FnOperand) -> ControlFlow<Infallible> {
        match x {
            FnOperand::Regular(_) => self.visit_inner(x),
            FnOperand::Dynamic(_) => self.visit_inner_with_mutability(x, true),
        }
    }

    fn visit_rvalue(&mut self, x: &mut Rvalue) -> ControlFlow<Infallible> {
        use Rvalue::*;
        match x {
            // `UniqueImmutable` de facto gives mutable access and only shows up if there is nested
            // mutable access.
            RawPtr {
                kind: RefKind::Mut, ..
            }
            | Ref {
                kind: BorrowKind::Mut | BorrowKind::TwoPhaseMut | BorrowKind::UniqueImmutable,
                ..
            } => self.visit_inner_with_mutability(x, true),
            RawPtr {
                kind: RefKind::Shared,
                ..
            }
            | Ref {
                kind: BorrowKind::Shared | BorrowKind::Shallow,
                ..
            }
            | Discriminant(..)
            | Len(..) => self.visit_inner_with_mutability(x, false),

            Use(..) | NullaryOp(..) | UnaryOp(..) | BinaryOp(..) | Aggregate(..) | Repeat(..) => {
                self.visit_inner(x)
            }
        }
    }

    fn visit_llbc_block(&mut self, _: &mut llbc_ast::Block) -> ControlFlow<Infallible> {
        ControlFlow::Continue(())
    }
}

/// We do the following.
///
/// If `p` is a projection (for instance: `var`, `*var`, `var.f`, etc.), we
/// detect:
/// - whether it operates on a slice or an array (we keep track of the types)
/// - whether the access might mutate the value or not (it is
///   the case if it is in a `move`, `&mut` or at the lhs of an assignment),
///   and do the following transformations
///
/// ```text
///   // If array and mutable access:
///   ... p[i] ...
///      ~~>
///   tmp0 = &mut p
///   tmp1 = <[_; _] as IndexMut<_>>::index_mut(move tmp0, i)
///   ... *tmp1 ...
///
///   // If array and non-mutable access:
///   ... p[i] ...
///      ~~>
///   tmp0 := & p
///   tmp1 := <[_; _] as Index<_>>::index(move tmp0, i)
///   ... *tmp1 ...
///
///   // Omitting the slice cases, which are similar
/// ```
///
/// For instance, it leads to the following transformations:
/// ```text
///   // x : [u32; N]
///   y : u32 = copy x[i]
///      ~~>
///   tmp0 : & [u32; N] := &x
///   tmp1 : &u32 = <[_; _] as Index<_>>::index(move tmp0, i)
///   y : u32 = copy (*tmp1)
///
///   // x : &[T; N]
///   y : &T = & (*x)[i]
///      ~~>
///   tmp0 : & [T; N] := & (*x)
///   tmp1 : &T = <[_; _] as Index<_>>::index(move tmp0, i)
///   y : &T = & (*tmp1)
///
///   // x : [u32; N]
///   y = &mut x[i]
///      ~~>
///   tmp0 : &mut [u32; N] := &mut x
///   tmp1 : &mut u32 := <[_; _] as IndexMut<_>>::index_mut(move tmp0, i)
///   y = &mut (*tmp)
///
///   // When using an index on the lhs:
///   // y : [T; N]
///   y[i] = x
///      ~~>
///   tmp0 : &mut [T; N] := &mut y;
///   tmp1 : &mut T = <[_; _] as IndexMut<_>>::index_mut(move tmp0, i)
///   *tmp1 = x
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum StdItem {
    ArrayAsSlice,
    ArrayAsMutSlice,
    ArrayRepeat,
    ArrayIndex,
    ArrayIndexMut,
    SliceIndexImpl,
    SliceIndexMutImpl,
    SliceIndex,
    SliceIndexMut,
    RangeIndex,
    RangeIndexMut,
}

pub struct Transform {
    item_map: HashMap<StdItem, ItemId>,
    item_set: HashSet<ItemId>,
}

impl Transform {
    pub fn new(ctx: &TransformCtx) -> CowBox<dyn LlbcPass> {
        use StdItem::*;

        let mut matches: [(StdItem, NamePattern, Vec<ItemId>); _] = [
            (ArrayAsSlice, "core::array::_::as_slice"),
            (ArrayAsMutSlice, "core::array::_::as_mut_slice"),
            (ArrayRepeat, "core::array::repeat"),
            (
                SliceIndex,
                "core::slice::index::{impl core::slice::index::SliceIndex<_> for usize}::index",
            ),
            (
                SliceIndexMut,
                "core::slice::index::{impl core::slice::index::SliceIndex<_> for usize}::index_mut",
            ),
            (
                RangeIndex,
                "core::slice::index::{impl core::slice::index::SliceIndex<_> for core::ops::range::Range<usize>}::index",
            ),
            (
                RangeIndexMut,
                "core::slice::index::{impl core::slice::index::SliceIndex<_> for core::ops::range::Range<usize>}::index_mut",
            ),
        ]
        .map(|(item, path)| (item, NamePattern::parse(path).unwrap(), Vec::new()));

        // Resolve the items
        for (id, name) in &ctx.translated.item_names {
            for (_, pattern, found) in &mut matches {
                if pattern.matches(&ctx.translated, name) {
                    found.push(*id);
                }
            }
        }

        let mut index_impl_methods: HashMap<StdItem, Vec<ItemId>> = HashMap::new();
        for fun in &ctx.translated.fun_decls {
            let FunSource::TraitImpl { trait_ref, .. } = &fun.src else {
                continue;
            };
            let Some(trait_decl) = ctx.translated.trait_decls.get(trait_ref.id) else {
                continue;
            };
            let Some(self_ty) = trait_ref.self_ty(&ctx.translated) else {
                continue;
            };
            let item = match (&trait_decl.item_meta.lang_item, self_ty.kind()) {
                (Some(crate::ast::from_rustc::LangItem::Index), TyKind::Array(..)) => ArrayIndex,
                (Some(crate::ast::from_rustc::LangItem::IndexMut), TyKind::Array(..)) => {
                    ArrayIndexMut
                }
                (Some(crate::ast::from_rustc::LangItem::Index), TyKind::Slice(..)) => {
                    SliceIndexImpl
                }
                (Some(crate::ast::from_rustc::LangItem::IndexMut), TyKind::Slice(..)) => {
                    SliceIndexMutImpl
                }
                _ => continue,
            };
            index_impl_methods
                .entry(item)
                .or_default()
                .push(ItemId::Fun(fun.def_id));
        }
        let item_map = matches
            .into_iter()
            .map(|(item, _, found)| (item, found))
            .chain(index_impl_methods)
            .filter_map(|(item, found)| found.into_iter().exactly_one().ok().map(|id| (item, id)))
            .collect::<HashMap<_, _>>();
        let item_set = item_map.values().copied().collect();
        CowBox::Owned(Box::new(Self { item_map, item_set }))
    }
}

impl LlbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.ops_to_function_calls || options.index_to_function_calls
    }

    fn transform_function(&self, ctx: &mut TransformCtx, decl: &mut FunDecl) {
        if self.item_set.contains(&ItemId::Fun(decl.def_id)) {
            return;
        }
        let Some(body) = decl.body.as_structured_mut() else {
            return;
        };
        if ctx.options.ops_to_function_calls {
            body.body
                .visit_statements(&mut |statement: &mut Statement| {
                    transform_operation(self, ctx, statement)
                });
        }
        if ctx.options.index_to_function_calls {
            decl.transform_llbc_statements(ctx, |ctx, st: &mut Statement| {
                let mut visitor = IndexVisitor {
                    ctx,
                    std_items: self,
                    place_mutability_stack: Vec::new(),
                };
                use StatementKind::*;
                match &mut st.kind {
                    Assign(..) | SetDiscriminant(..) | Drop { .. } | Call { .. } => {
                        let _ = visitor.visit_inner_with_mutability(st, true);
                    }
                    Switch { .. } | PlaceMention(..) | Borrowck(..) => {
                        let _ = visitor.visit_inner_with_mutability(st, false);
                    }
                    Nop
                    | UnwindResume
                    | Error(..)
                    | InlineAsm { .. }
                    | Assert { .. }
                    | Abort(..)
                    | StorageDead(..)
                    | StorageLive(..)
                    | Return
                    | Break(..)
                    | Continue(..)
                    | Loop(..) => {
                        let _ = st.drive_body_mut(&mut visitor);
                    }
                }
            })
        }
    }
}
