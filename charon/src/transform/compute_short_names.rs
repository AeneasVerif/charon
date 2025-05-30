use std::collections::{hash_map::Entry, HashMap};

use crate::ast::*;

use super::{ctx::TransformPass, TransformCtx};

enum FoundName {
    Unique(AnyTransId),
    Multiple,
}

pub struct Transform;
impl TransformPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        let mut short_names: HashMap<String, FoundName> = Default::default();
        for (&id, mut name) in &ctx.translated.item_names {
            // Trait impls are sufficiently unique information, so truncate starting from the
            // rightmost impl.
            let trunc_name;
            if let Some((i, _)) = name
                .name
                .as_slice()
                .iter()
                .enumerate()
                .rfind(|(_, elem)| matches!(elem, PathElem::Impl(ImplElem::Trait(..), ..)))
            {
                trunc_name = Name {
                    name: name.name[i..].to_vec(),
                };
                ctx.translated.short_names.insert(id, trunc_name.clone());
                name = &trunc_name;
            }
            match name.name.as_slice() {
                [.., PathElem::Ident(ident, _)] => match short_names.entry(ident.clone()) {
                    Entry::Occupied(mut e) => {
                        e.insert(FoundName::Multiple);
                    }
                    Entry::Vacant(e) => {
                        e.insert(FoundName::Unique(id));
                    }
                },
                _ => {}
            }
        }

        for (short, found) in short_names {
            if let FoundName::Unique(id) = found {
                ctx.translated.short_names.insert(
                    id,
                    Name {
                        name: vec![PathElem::Ident(short, Disambiguator::ZERO)],
                    },
                );
            }
        }
    }
}
