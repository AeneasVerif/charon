use crate::ast::*;
use derive_generic_visitor::{Drive, DriveMut, DriveTwo};
use macros::EnumIsA;
use macros::VariantName;
use serde_state::DeserializeState;
use serde_state::SerializeState;

/// A function definition
#[derive(Debug, Clone)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct FunDecl {
    pub def_id: FunDeclId,
    /// The meta data associated with the declaration.
    pub item_meta: ItemMeta,
    pub generics: GenericParams,
    /// The signature contains the inputs/output types and ABI details.
    pub signature: Box<FunSig>,
    /// The function kind: "regular" function, trait method declaration, etc.
    pub src: FunSource,
    /// The function body.
    pub body: Body,
}

/// A function signature.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
pub struct FunSig {
    /// Is the function unsafe or not
    pub is_unsafe: bool,
    /// The calling convention of this function.
    pub abi: Abi,
    /// Whether this is a C-variadic function (its last parameter is `...`).
    pub is_variadic: bool,
    pub inputs: Vec<Ty>,
    pub output: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(VariantName, EnumIsA)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[serde_state(stateless)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_prefix("Abi"))]
pub enum Abi {
    Rust,
    C,
    /// Rust's spelling for the ABI, e.g. "C-unwind" or "system".
    Other(ustr::Ustr),
}

/// Where a given function came from.
#[derive(Debug, Clone)]
#[derive(SerializeState, DeserializeState, Drive, DriveMut, DriveTwo)]
#[cfg_attr(feature = "charon_on_charon", charon::variants_suffix("Fun"))]
pub enum FunSource {
    /// A normal function.
    Normal,
    /// A synthetic function representing an ADT constructor.
    AdtConstructor,
    /// A method in an inherent implementation.
    InherentImpl {
        /// The self type of the impl block.
        self_ty: Ty,
    },
    /// A default method in a trait declaration.
    TraitDefault {
        /// The trait declaration this item belongs to.
        trait_ref: TraitDeclRef,
        /// The method this corresponds to.
        // TODO: also include method generics so we can recover a full `FnPtr::TraitMethod`
        item_id: TraitMethodId,
    },
    /// A method in a trait implementation.
    TraitImpl {
        /// The trait implementation the method belongs to.
        impl_ref: TraitImplRef,
        /// The trait declaration that the impl block implements.
        trait_ref: TraitDeclRef,
        /// The method this corresponds to.
        // TODO: also include method generics so we can recover a full `FnPtr::TraitMethod`
        item_id: TraitMethodId,
        /// True if the trait decl had a default implementation for this method and this item is a
        /// copy of the default item.
        reuses_default: bool,
    },
    /// Wraps a concrete implementation of a method into a function that takes `dyn Trait` as its
    /// `Self` type. This shim casts the receiver to the known concrete type and calls the real
    /// method.
    VTableShim,
    /// The initializer for a global.
    GlobalInitializer(GlobalDeclRef),
    /// A target-specific variant behind a `TargetDispatch` façade. The dispatcher is the function
    /// with the `Body::TargetDispatch` body that dispatches to this function.
    TargetDependent { dispatcher: FunDeclRef },
}

impl FunDecl {
    /// Replace the generic parameters of this function with the ones given by the binder.
    pub fn substitute_params(self, subst: Binder<GenericArgs>) -> Self {
        let FunDecl {
            def_id,
            item_meta,
            generics: _,
            signature,
            src,
            body,
        } = self;
        let signature = signature.substitute(&subst.skip_binder);
        let src = src.substitute(&subst.skip_binder);
        let body = body.substitute(&subst.skip_binder);
        FunDecl {
            def_id,
            item_meta,
            generics: subst.params,
            signature,
            src,
            body,
        }
    }

    /// Whether this function is unsafe to call, because it is declared `unsafe` (safety.unsafe-call),
    /// or because it is a safe `#[target_feature]` function (safety.unsafe-target-feature-call). This
    /// may be overriden at the call site, if we can statically discharge the unsafety (see [`CallSafety`]).
    pub fn is_unsafe_to_call(&self, _krate: &TranslatedCrate) -> bool {
        self.signature.is_unsafe
    }

    /// Whether this function is unsafe to declare.
    pub fn is_unsafe_to_declare(&self, _krate: &TranslatedCrate) -> bool {
        // The initializer of a global is part of the global's declaration.
        !matches!(self.src, FunSource::GlobalInitializer(_))
            && self.item_meta.is_unsafe_to_declare()
    }

    /// The function pointer signature of this item, binding its late-bound regions.
    pub fn as_fn_ptr(&self) -> RegionBinder<FunSig> {
        struct RebindLateRegions<'a> {
            late_regions: &'a IndexVec<RegionId, Option<RegionId>>,
        }

        impl VarsVisitor for RebindLateRegions<'_> {
            fn visit_region_var(&mut self, var: RegionDbVar) -> Option<Region> {
                let DeBruijnVar::Bound(depth, id) = var else {
                    return None;
                };
                if depth == DeBruijnId::one() {
                    self.late_regions[id].map(|id| Region::Var(DeBruijnVar::new_at_zero(id)))
                } else {
                    None
                }
            }
        }

        let mut regions = IndexVec::new();
        let late_regions = self.generics.regions.map_ref(|param| {
            if param.late_bound {
                Some(regions.push_with(|index| RegionParam {
                    index,
                    ..param.clone()
                }))
            } else {
                None
            }
        });
        let mut signature = self.signature.as_ref().clone().move_under_binder();
        signature.visit_vars(&mut RebindLateRegions {
            late_regions: &late_regions,
        });
        RegionBinder {
            regions,
            // Late-bound regions are guaranteed to not be involved in any non-implied outlives
            // relations.
            outlives: Vec::new(),
            skip_binder: signature,
        }
    }
}

impl RegionBinder<FunSig> {
    /// Infer how the bound regions of `self` appear in `target`. The returned binder binds the
    /// same regions as `target`; other lifetimes may differ.
    pub fn infer_region_mapping(&self, target: &Self) -> Option<RegionBinder<RegionArgs>> {
        struct RegionMapping {
            regions: IndexVec<RegionId, Option<Region>>,
            depth: DeBruijnId,
        }

        impl Visitor for RegionMapping {
            type Break = ();
        }

        impl ZipAst for RegionMapping {
            fn visit_region_param(
                &mut self,
                _source: &RegionParam,
                _target: &RegionParam,
            ) -> ControlFlow<()> {
                // Binder positions identify regions; names and metadata need not match.
                ControlFlow::Continue(())
            }

            fn visit_region(&mut self, source: &Region, target: &Region) -> ControlFlow<()> {
                if let (Region::Lub(source), Region::Lub(target)) = (source, target) {
                    return self.visit(source, target);
                }
                // We're only concerned with mapping bound variables.
                if let Region::Var(var @ DeBruijnVar::Bound(depth, _)) = source
                    && *depth <= self.depth
                {
                    if let Some(id) = var.bound_at_depth(self.depth) {
                        let Some(target) = target.clone().move_from_under_binders(self.depth)
                        else {
                            return ControlFlow::Break(());
                        };
                        let mapped = &mut self.regions[id];
                        if let Some(previous) = mapped
                            && *previous != target
                        {
                            return ControlFlow::Break(());
                        }
                        *mapped = Some(target);
                        ControlFlow::Continue(())
                    } else if source != target {
                        ControlFlow::Break(())
                    } else {
                        ControlFlow::Continue(())
                    }
                } else {
                    ControlFlow::Continue(())
                }
            }

            fn visit_region_binder<T: AstVisitable>(
                &mut self,
                source: &RegionBinder<T>,
                target: &RegionBinder<T>,
            ) -> ControlFlow<()> {
                self.depth = self.depth.incr();
                let result = self.visit_inner(source, target);
                self.depth = self.depth.decr();
                result
            }
        }

        let mut mapping = RegionMapping {
            regions: self.regions.map_ref_indexed(|_, _| None),
            depth: DeBruijnId::zero(),
        };
        if ZipAst::visit(&mut mapping, &self.skip_binder, &target.skip_binder).is_break() {
            return None;
        }
        let regions = RegionArgs::new(mapping.regions.into_iter().collect::<Option<_>>()?);
        Some(RegionBinder {
            regions: target.regions.clone(),
            outlives: target.outlives.clone(),
            skip_binder: regions,
        })
    }
}

impl Abi {
    pub fn rust() -> Self {
        Self::Rust
    }

    pub fn rust_name(&self) -> &str {
        match self {
            Self::Rust => "Rust",
            Self::C => "C",
            Self::Other(name) => name.as_str(),
        }
    }
}
