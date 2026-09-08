//! Layout guarantees might refer to types that themselves were not translated at that time.
//! Thus, these symbolic place holders can only be instantiated after the translation in this transformation pass.
//! Place holders can only occur in these cases:
//! - type aliases
//! - unresolved type variables
//! - type declarations without layout information for the requested target
//!
//! For the latter two points, there's no way to resolve the symbolic place holders,
//! but the first case should be resolved as much as possible.

use crate::{
    ast::{TargetTriple, TypeDeclId, layout_guarantee_utils::LayoutGuarantees},
    transform::{TransformCtx, ctx::TransformPass},
};

pub struct Transform;

impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        info!("Hello from fixing pass");
        // Steps:
        // 1. find all aliases and store the corresponding types,
        // 2. get guarantees for these types
        // 3. update the alias layouts with the new guarantees

        let mut aliases = Vec::new();
        for type_decl in ctx.translated.type_decls.iter() {
            if let Some(aliased_ty) = type_decl.kind.as_alias() {
                info!(
                    "Alias in def {} with {} many layouts aliasing {aliased_ty:?}",
                    type_decl.def_id,
                    type_decl.layout.len()
                );
                aliases.push((
                    type_decl.def_id,
                    aliased_ty.clone(),
                    type_decl.layout.keys().collect::<Vec<&TargetTriple>>(),
                ));
            }
        }

        let alias_guarantees: Vec<(TypeDeclId, Vec<(TargetTriple, LayoutGuarantees)>)> = aliases
            .into_iter()
            .map(|(id, ty, targets)| {
                (
                    id,
                    targets
                        .into_iter()
                        .filter_map(|target| {
                            LayoutGuarantees::for_ty(&ty, &ctx.translated, Some(target))
                                .map(|guarantees| (target.clone(), guarantees))
                        })
                        .collect(),
                )
            })
            .collect();

        let type_decls = &mut ctx.translated.type_decls;
        for (td_id, guarantees) in alias_guarantees.into_iter() {
            info!("Alias {td_id} with guarantees {:?}", guarantees);
            let type_decl = type_decls.get_mut(td_id).unwrap();
            for (target, guarantee) in guarantees {
                if let Some(layout) = type_decl.layout.get_mut(&target) {
                    layout.update_guarantees(guarantee.clone(), Some(&target));
                }
            }
        }
    }
}
