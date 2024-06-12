use proc_macro::{Span, TokenStream};
use quote::ToTokens;
use std::vec::Vec;
use syn::{
    parse_macro_input, Block, Expr, FnArg, Ident, Item, ItemTrait, Pat, ReturnType, Stmt,
    TraitItem, Type, TypeParamBound,
};

fn generic_type_to_mut(ty: &mut Type) {
    match ty {
        Type::Reference(r) => match &mut r.mutability {
            Option::None => {
                r.mutability = Option::Some(syn::token::Mut([Span::call_site().into()]))
            }
            Option::Some(_) => (),
        },
        _ => (),
    }
}

fn generic_stmt_to_mut(s: &mut Stmt) {
    match s {
        Stmt::Local(s) => s
            .init
            .iter_mut()
            .for_each(|e| generic_expr_to_mut(&mut e.1)),
        Stmt::Item(item) => generic_item_to_mut(item),
        Stmt::Expr(e) => generic_expr_to_mut(e),
        Stmt::Semi(e, _) => generic_expr_to_mut(e),
    }
}

fn generic_stmts_to_mut(stmts: &mut Vec<Stmt>) {
    for stmt in stmts {
        generic_stmt_to_mut(stmt)
    }
}

fn generic_item_to_mut(item: &mut Item) {
    use Item::*;
    match item {
        Const(_) => unimplemented!("Item::Const"),
        Enum(_) => unimplemented!("Item::Enum"),
        ExternCrate(_) => unimplemented!("Item::ExternCrate"),
        Fn(_) => unimplemented!("Item::Fn"),
        ForeignMod(_) => unimplemented!("Item::ForeignMod"),
        Impl(_) => unimplemented!("Item::Impl"),
        Macro(_) => unimplemented!("Item::Macro"),
        Macro2(_) => unimplemented!("Item::Macro2"),
        Mod(_) => unimplemented!("Item::Mod"),
        Static(_) => unimplemented!("Item::Static"),
        Struct(_) => unimplemented!("Item::Struct"),
        Trait(_) => unimplemented!("Item::Trait"),
        TraitAlias(_) => unimplemented!("Item::TraitAlias"),
        Type(_) => unimplemented!("Item::Type"),
        Union(_) => unimplemented!("Item::Union"),
        Use(_) => (), // Nothing to do
        Verbatim(_) => unimplemented!("Item::Verbatim"),
        #[cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        _ => {
            unimplemented!();
        }
    }
}

fn generic_block_to_mut(e: &mut Block) {
    generic_stmts_to_mut(&mut (e.stmts));
}

fn generic_expr_to_mut(e: &mut Expr) {
    // There are really a lot of cases: we try to filter the ones in which
    // we are not interested.
    match e {
        Expr::Assign(e) => {
            generic_expr_to_mut(&mut (*e.left));
            generic_expr_to_mut(&mut (*e.right));
        }
        Expr::AssignOp(e) => {
            generic_expr_to_mut(&mut (*e.left));
            generic_expr_to_mut(&mut (*e.right));
        }
        Expr::Binary(e) => {
            generic_expr_to_mut(&mut (*e.left));
            generic_expr_to_mut(&mut (*e.right));
        }
        Expr::Block(e) => {
            generic_block_to_mut(&mut (e.block));
        }
        Expr::Box(e) => {
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Call(e) => {
            generic_expr_to_mut(&mut (*e.func));
            for arg in e.args.iter_mut() {
                generic_expr_to_mut(arg);
            }
        }
        Expr::Closure(e) => {
            // Keeping things simple
            e.inputs.iter_mut().for_each(|i| generic_pat_to_mut(i));
            generic_expr_to_mut(&mut (*e.body));
        }
        Expr::Field(e) => {
            generic_expr_to_mut(&mut (*e.base));
        }
        Expr::ForLoop(e) => {
            // We ignore the pattern for now
            generic_expr_to_mut(&mut (*e.expr));
            generic_block_to_mut(&mut (e.body));
        }
        Expr::Group(e) => {
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::If(e) => {
            generic_expr_to_mut(&mut (*e.cond));
            generic_block_to_mut(&mut (e.then_branch));
            e.else_branch
                .iter_mut()
                .for_each(|(_, b)| generic_expr_to_mut(b));
        }
        Expr::Index(e) => {
            generic_expr_to_mut(&mut (*e.expr));
            generic_expr_to_mut(&mut (*e.index));
        }
        Expr::Let(e) => {
            // Ignoring the pattern
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Loop(e) => {
            generic_block_to_mut(&mut (e.body));
        }
        Expr::Macro(_) => {
            // Doing nothing
        }
        Expr::Match(e) => {
            generic_expr_to_mut(&mut (*e.expr));
            e.arms.iter_mut().for_each(|a| {
                a.guard.iter_mut().for_each(|(_, g)| generic_expr_to_mut(g));
                generic_expr_to_mut(&mut a.body)
            });
        }
        Expr::MethodCall(e) => {
            generic_expr_to_mut(&mut (*e.receiver));
            e.args.iter_mut().for_each(|a| generic_expr_to_mut(a));

            // IMPORTANT: check the name of the method: if it is `iter` change
            // to `iter_mut`
            let id = e.method.to_string();
            if id == "iter" {
                e.method = Ident::new("iter_mut", Span::call_site().into());
            }
        }
        Expr::Paren(e) => {
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Path(_) => {
            // Doing nothing
        }
        Expr::Reference(e) => {
            // IMPORTANT: change the mutability
            // Remark: closures are handled elsewhere
            e.mutability = Option::Some(syn::token::Mut([Span::call_site().into()]));
            generic_expr_to_mut(&mut (*e.expr));
        }
        Expr::Return(e) => {
            e.expr.iter_mut().for_each(|e| generic_expr_to_mut(e));
        }
        Expr::Type(e) => {
            generic_expr_to_mut(&mut (*e.expr));
            generic_type_to_mut(&mut (*e.ty));
        }
        Expr::While(e) => {
            generic_expr_to_mut(&mut (*e.cond));
            generic_block_to_mut(&mut (e.body));
        }
        _ => (),
    }
}

/// We use this method to update the names of the supertraits
/// when defining an implementation generic over the borrow type.
///
/// For instance, if we write:
/// ```ignore
/// make_generic_in_borrows! {
///   trait AstVisitor : ExprVisitor { ... }
/// }
/// ```
///
/// We want to generate two definitions:
/// ```ignore
/// make_generic_in_borrows! {
///   trait SharedAstVisitor : SharedExprVisitor { ... }
/// }
/// ```
///
/// and:
/// ```ignore
/// make_generic_in_borrows! {
///   trait MutAstVisitor : MutExprVisitor { ... }
/// }
/// ```
fn generic_supertraits_to_mut_shared(tr: &mut ItemTrait, to_mut: bool) {
    for p in tr.supertraits.iter_mut() {
        match p {
            TypeParamBound::Trait(t) => {
                // Update the path: update the last segment
                let mut it = t.path.segments.iter_mut();
                let mut last_s = it.next().unwrap();
                while let Some(s) = it.next() {
                    last_s = s;
                }
                last_s.ident = generic_mk_ident(&last_s.ident, to_mut);
            }
            TypeParamBound::Lifetime(_) => (),
        }
    }
}

fn generic_mk_ident(id: &syn::Ident, to_mut: bool) -> syn::Ident {
    // TODO: not sure about the spans
    // Not very clean, but does the job
    let id = id.to_string();
    let name = if to_mut {
        format!("Mut{}", id)
    } else {
        format!("Shared{}", id)
    };
    syn::Ident::new(&name, Span::call_site().into())
}

fn generic_pat_to_mut(p: &mut Pat) {
    match p {
        Pat::Type(p) => generic_type_to_mut(&mut p.ty),
        _ => (),
    }
}

fn generic_mk_item(id: &Ident, to_mut: bool, item: &mut TraitItem) {
    match item {
        TraitItem::Const(_) | TraitItem::Macro(_) => {
            unimplemented!("Trait item")
        }
        TraitItem::Type(ty) => {
            // Update the references to self (we need to change the name).
            // For now, we only update the bounds
            for bound in &mut ty.bounds {
                if let TypeParamBound::Trait(tr) = bound {
                    if tr.path.segments.len() == 1 {
                        if let Some(last) = tr.path.segments.last_mut() {
                            if &last.ident == id {
                                last.ident = generic_mk_ident(&mut last.ident, to_mut)
                            }
                        }
                    }
                }
            }
        }
        TraitItem::Verbatim(_) => (),
        TraitItem::Method(s) => {
            // Update the borrows
            if to_mut {
                // Update the signature
                for input in &mut s.sig.inputs {
                    match input {
                        FnArg::Receiver(_) => {
                            /* We don't touch the self parameter for now */
                            ()
                        }
                        FnArg::Typed(arg) => {
                            // Change the reference types
                            generic_type_to_mut(&mut (*arg.ty));
                        }
                    }
                }

                match &mut s.sig.output {
                    ReturnType::Default => (),
                    ReturnType::Type(_, ty) => {
                        generic_type_to_mut(ty);
                    }
                }

                // Update the body
                // - we replace all the references
                // - we replace the occurrences of `iter`
                match &mut s.default {
                    Option::None => (),
                    Option::Some(body) => {
                        generic_stmts_to_mut(&mut body.stmts);
                    }
                }
            }
        }
        #[cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        _ => {
            /* See the fox of [TraitItem] */
            unimplemented!()
        }
    }
}

/// We use this macro to write implementation which are generic in borrow
/// kinds (i.e., from one implementation, we derive two implementations which
/// use shared borrows or mut borrows).
///
/// Note that this macro is meant to work on a limited set of cases: it is not
/// very general.
/// For instance, for now it only works on traits.
///
/// Applied on a trait definition named "Trait", it will generate two traits:
/// "MutTrait" and "SharedTrait".
pub fn make_generic_in_borrows(tokens: TokenStream) -> TokenStream {
    let input_item = parse_macro_input!(tokens as ItemTrait);
    // We should have received the shared version
    let mut shared_item = input_item.clone();
    let mut mut_item = input_item;

    let id = shared_item.ident.clone();
    mut_item.ident = generic_mk_ident(&id, true);
    shared_item.ident = generic_mk_ident(&id, false);

    generic_supertraits_to_mut_shared(&mut shared_item, false);
    generic_supertraits_to_mut_shared(&mut mut_item, true);

    // Update the shared version
    for item in &mut shared_item.items {
        generic_mk_item(&id, false, item)
    }

    // Update the mutable version
    for item in &mut mut_item.items {
        generic_mk_item(&id, true, item)
    }

    // TODO: This is not very clean, but I don't know how to concatenate stream tokens
    format!(
        "{}\n{}",
        shared_item.to_token_stream(),
        mut_item.to_token_stream()
    )
    .parse()
    .unwrap()
}
