//! This file contains various substitution utilities

#![allow(dead_code)]
use hashlink::linked_hash_map::LinkedHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{BoundRegion, FreeRegion, Region, RegionKind, TyCtxt};

/// Instantiate the bound region variables in a binder, by turning the bound
/// regions variables into free region variables. Note that the indices used
/// for the free regions are the indices used for the bound regions: we do not
/// generate *fresh* regions in an ad-hoc manner.
///
/// This is typically used when instantiating function signatures (but not only):
/// signatures are wrapped in a [`Binder`](rustc_middle::ty::Binder), which we
/// need to remove through a proper instantiation (we simply instantiate bound
/// variables with free variables).
///
/// This code is inspired by
/// [`liberate_late_bound_regions`](TyCtx::liberate_late_bound_regions).
///
/// The rationale is as follows:
/// - it seems liberate_late_bound_regions is a proper way of retrieving
///   a signature where all the bound variables have been replaced with
///   free variables, so that we can study it easily (without having, for
///   instance, to deal with DeBruijn indices)
/// - my understanding of why it is enough to bind late-bound regions: the
///   early bound regions are not bound here (they are free), because
///   they reference regions introduced by the `impl` block (if this definition
///   is defined in an `impl` block - otherwise there are no early bound variables)
///   while the late bound regions are introduced by the function itself.
///   For example, in:
///   ```
///   impl<'a> Foo<'a> {
///       fn bar<'b>(...) -> ... { ... }
///   }
///   ```
///   `'a` is early-bound while `'b` is late-bound.
/// - we can't just use `liberate_late_bound_regions`, because we want to know
///   in which *order* the regions were bound, while it is unclear that the
///   b-tree returned by `liberate_late_bound_regions` preserves this order.
///   Also note that this is just a matter of stability of the translation.
///   For instance, when generating function translations, we have to generate
///   one backward function per region, and we need to know in which order to
///   introduce those backward functions.
pub fn replace_late_bound_regions<'tcx, T>(
    tcx: TyCtxt<'tcx>,
    value: rustc_middle::ty::Binder<'tcx, T>,
    def_id: DefId,
) -> (T, LinkedHashMap<BoundRegion, Region<'tcx>>)
where
    T: rustc_middle::ty::TypeFoldable<'tcx>,
{
    // Instantiate the regions bound in the signature, and generate a mapping
    // while doing so (the mapping uses a linked hash map so that we remember
    // in which order we introduced the regions).
    // Note that replace_late_bound_regions` returns a map from bound regions to
    // regions, but it is unclear whether this map preserves the order in which
    // the regions were introduced (the map is a BTreeMap, so I guess it depends
    // on how the the bound variables were numbered) and it doesn't cost us
    // much to create this mapping ourselves.
    let mut late_bound_regions: LinkedHashMap<BoundRegion, Region> = LinkedHashMap::new();
    let (value, _) = tcx.replace_late_bound_regions(value, |br| {
        let nregion = tcx.mk_region(RegionKind::ReFree(FreeRegion {
            scope: def_id,
            bound_region: br.kind,
        }));
        late_bound_regions.insert(br, nregion);
        nregion
    });
    (value, late_bound_regions)
}
