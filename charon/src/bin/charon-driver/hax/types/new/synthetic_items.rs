use crate::hax::prelude::*;

use {
    rustc_hir::definitions::PerParentDisambiguatorState,
    rustc_middle::ty,
    rustc_span::{DUMMY_SP, Symbol},
    rustc_type_ir::Upcast,
};

/// We create some extra `DefId`s to represent things that rustc doesn't have a `DefId` for. This
/// makes the pipeline much easier to have "real" def_ids for them.
/// We generate fake struct-like items for each of: arrays, slices, and tuples. This makes it
/// easier to emit trait impls for these types, especially with monomorphization. This enum tracks
/// identifies these builtin types.
#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum SyntheticItem {
    /// Fake ADT representing the `[T; N]` type.
    Array,
    /// Fake ADT representing the `[T]` type.
    Slice,
    /// Fake ADT representing the length-n tuple `(A, B, ...)`.
    Tuple(usize),
}

#[derive(Clone, Copy)]
pub struct SyntheticItemData<'tcx> {
    generics: &'tcx ty::Generics,
    clauses: &'tcx [ty::Clause<'tcx>],
    param_env: ty::ParamEnv<'tcx>,
}

impl SyntheticItem {
    pub fn name(&self) -> String {
        match self {
            SyntheticItem::Array => "<array>".to_string(),
            SyntheticItem::Slice => "<slice>".to_string(),
            SyntheticItem::Tuple(n) => format!("<tuple_{n}>"),
        }
    }

    pub fn can_have_generics<'tcx>(&self, s: &impl BaseState<'tcx>) -> bool {
        !self.generics_of(s).own_params.is_empty()
    }

    pub fn generics_of<'tcx>(&self, s: &impl BaseState<'tcx>) -> &'tcx ty::Generics {
        self.data(s).generics
    }

    pub fn identity_args<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::GenericArgsRef<'tcx> {
        let tcx = s.base().tcx;
        tcx.mk_args_from_iter(
            self.generics_of(s)
                .own_params
                .iter()
                .map(|param| tcx.mk_param_from_def(param)),
        )
    }

    pub fn param_env<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::ParamEnv<'tcx> {
        self.data(s).param_env
    }

    pub fn predicates_defined_on<'tcx>(
        &self,
        s: &impl BaseState<'tcx>,
        def_id: DefId,
        direction: PredicateDirection,
    ) -> ItemPredicates<'tcx, DefId> {
        ItemPredicates::new(
            def_id,
            direction,
            self.data(s)
                .clauses
                .iter()
                .copied()
                .map(|clause| (clause, DUMMY_SP)),
        )
    }

    pub fn type_of<'tcx>(&self, s: &impl BaseState<'tcx>) -> ty::EarlyBinder<'tcx, ty::Ty<'tcx>> {
        let tcx = s.base().tcx;
        let args = self.identity_args(s);
        let type_of = match self {
            SyntheticItem::Array => {
                let item_ty = args[0].as_type().unwrap();
                let len = args[1].as_const().unwrap();
                ty::Ty::new_array_with_const_len(tcx, item_ty, len)
            }
            SyntheticItem::Slice => {
                let item_ty = args[0].as_type().unwrap();
                ty::Ty::new_slice(tcx, item_ty)
            }
            SyntheticItem::Tuple(_) => {
                let tys = args.iter().map(|arg| arg.as_type().unwrap());
                let tys = tcx.arena.alloc_from_iter(tys);
                ty::Ty::new_tup(tcx, tys)
            }
        };
        ty::EarlyBinder::bind(type_of)
    }

    fn data<'tcx>(&self, s: &impl BaseState<'tcx>) -> SyntheticItemData<'tcx> {
        s.with_global_cache(|c| c.synthetic_data(s, *self))
    }
}

impl<'tcx> GlobalCache<'tcx> {
    fn synthetic_data(
        &mut self,
        s: &impl BaseState<'tcx>,
        item: SyntheticItem,
    ) -> SyntheticItemData<'tcx> {
        if let Some(data) = self.synthetic_item_data.get(&item) {
            return *data;
        }
        let tcx = s.base().tcx;
        let mut disambiguator_state = PerParentDisambiguatorState::default();
        let mut generics = ty::Generics {
            parent: None,
            parent_count: 0,
            own_params: Default::default(),
            param_def_id_to_index: Default::default(),
            has_self: false,
            has_late_bound_regions: None,
        };
        // The synthetic item itself is hax-only. We still create rustc defs for its generic
        // parameters because rustc generic params carry a `DefId`, and const params need a
        // `type_of` entry.
        let mut mk_param = |name: &str, def_kind, kind| {
            let name = Symbol::intern(name);
            let def_name = Symbol::intern(&format!("{}::{name}", item.name()));
            let param_feed = tcx.create_def(
                rustc_span::def_id::CRATE_DEF_ID,
                Some(def_name),
                def_kind,
                None,
                &mut disambiguator_state,
            );
            // Avoid ICEs
            param_feed.def_span(DUMMY_SP);
            param_feed.feed_hir();
            param_feed.visibility(ty::Visibility::Public);

            let param_def_id = param_feed.def_id().into();
            let index = generics.own_params.len() as u32;
            let param_def = ty::GenericParamDef {
                name,
                def_id: param_def_id,
                index,
                kind,
                pure_wrt_drop: true,
            };
            let arg = tcx.mk_param_from_def(&param_def);
            generics.own_params.push(param_def);
            generics.param_def_id_to_index.insert(param_def_id, index);
            (arg, param_feed)
        };

        let mut clauses = vec![];
        let sized_trait = tcx.lang_items().sized_trait().unwrap();
        match item {
            SyntheticItem::Array => {
                let (t_arg, _) = mk_param(
                    "T",
                    rustc_hir::def::DefKind::TyParam,
                    ty::GenericParamDefKind::Type {
                        has_default: false,
                        synthetic: false,
                    },
                );
                let (n_arg, n_feed) = mk_param(
                    "N",
                    rustc_hir::def::DefKind::ConstParam,
                    ty::GenericParamDefKind::Const { has_default: false },
                );
                n_feed.type_of(ty::EarlyBinder::bind(tcx.types.usize));

                let item_ty = t_arg.as_type().unwrap();
                let len = n_arg.as_const().unwrap();

                let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [item_ty]);
                clauses.push(ty_is_sized.upcast(tcx));
                let len_is_usize = ty::ClauseKind::ConstArgHasType(len, tcx.types.usize);
                clauses.push(len_is_usize.upcast(tcx));
            }
            SyntheticItem::Slice => {
                let (t_arg, _) = mk_param(
                    "T",
                    rustc_hir::def::DefKind::TyParam,
                    ty::GenericParamDefKind::Type {
                        has_default: false,
                        synthetic: false,
                    },
                );

                let item_ty = t_arg.as_type().unwrap();

                let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [item_ty]);
                clauses.push(ty_is_sized.upcast(tcx));
            }
            SyntheticItem::Tuple(len) => {
                let tys = (0..len).map(|i| {
                    let name: String = if i < 26 {
                        format!("{}", (b'A' + i as u8) as char)
                    } else {
                        format!("T{i}")
                    };
                    let (arg, _) = mk_param(
                        &name,
                        rustc_hir::def::DefKind::TyParam,
                        ty::GenericParamDefKind::Type {
                            has_default: false,
                            synthetic: false,
                        },
                    );
                    arg.as_type().unwrap()
                });
                let tys = tcx.arena.alloc_from_iter(tys);

                // All types except the last one are sized.
                for ty in tys.iter().rev().skip(1).rev() {
                    let arg: ty::GenericArg = (*ty).into();
                    let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [arg]);
                    clauses.push(ty_is_sized.upcast(tcx));
                }
            }
        }

        let clauses = tcx.arena.alloc_from_iter(clauses);
        let data = SyntheticItemData {
            generics: Box::leak(Box::new(generics)),
            clauses,
            param_env: ty::ParamEnv::new(tcx.mk_clauses_from_iter(clauses.iter().copied())),
        };
        self.synthetic_item_data.insert(item, data);
        data
    }
}

impl ItemRef {
    pub fn translate_synthetic<'tcx, S: UnderOwnerState<'tcx>>(
        s: &S,
        synthetic: SyntheticItem,
        generics: ty::GenericArgsRef<'tcx>,
    ) -> ItemRef {
        let hax_def_id = DefId::make_synthetic(s, synthetic);
        ItemRef::translate_from_hax_def_id(s, hax_def_id, generics)
    }
}
