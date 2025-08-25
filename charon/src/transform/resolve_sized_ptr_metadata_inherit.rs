
use crate::{ast::*, formatter::IntoFormatter, pretty::FmtWithCtx};

use super::{TransformCtx, ctx::TransformPass};

pub struct Transform;

impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let trait_decls = &ctx.translated.trait_decls;
        let mut metadata = vec![];
        for type_decl in &ctx.translated.type_decls {
            let fmt = &ctx.into_fmt();
            let meta = match &type_decl.ptr_metadata {
                PtrMetadata::InheritFrom(ty) => {
                    match ty.kind() {
                        TyKind::TypeVar(..) => {
                            let is_sized = type_decl.generics.trait_clauses.iter().any(|clause| {
                                let impl_trait = clause.trait_.clone().erase();
                                impl_trait.generics.types[0] == *ty
                                && {
                                    let trait_decl = trait_decls.get(impl_trait.id).unwrap();
                                    matches!(trait_decl.item_meta.lang_item, Some("sized"))
                                }
                            });
                            if is_sized {
                                trace!("Resolved ptr-metadata for type {}", type_decl.def_id.with_ctx(fmt));
                                PtrMetadata::None
                            } else {
                                trace!("Ptr-metadata for type {} inheriting from {} is not Sized, keep inheritance.", type_decl.def_id.with_ctx(fmt), ty.with_ctx(fmt));
                                // Otherwise, it cannot be resolved
                                PtrMetadata::InheritFrom(ty.clone())
                            }
                        }
                        // Will there be other cases?
                        _ => {
                            trace!("Non-type-var inheritance found for type: {}, inheriting from: {}", type_decl.def_id.with_ctx(fmt), ty.with_ctx(fmt));
                            PtrMetadata::InheritFrom(ty.clone())
                        }
                    }
                }
                x => x.clone()
            };
            metadata.push(meta);
        };
        let mut iter = metadata.into_iter();
        for type_decl in &mut ctx.translated.type_decls {
            type_decl.ptr_metadata = iter.next().unwrap();
        }
    }
}
