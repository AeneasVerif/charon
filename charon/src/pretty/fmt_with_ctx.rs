//! Utilities for pretty-printing (u)llbc.
use crate::{
    assumed::get_name_from_type_id,
    common::TAB_INCR,
    formatter::*,
    ids::Vector,
    llbc_ast::{self as llbc, *},
    names::*,
    reorder_decls::*,
    translate_predicates::NonLocalTraitClause,
    types::*,
    ullbc_ast::{self as ullbc, *},
    values::*,
};
use hax_frontend_exporter as hax;

/// Format the AST type as a string.
pub trait FmtWithCtx<C> {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // By default use no tab.
        self.fmt_with_ctx_and_indent("", ctx)
    }

    fn fmt_with_ctx_and_indent(&self, _tab: &str, _ctx: &C) -> String {
        panic!("This type does not know how to be formatted with indent")
    }

    /// Returns a struct that implements `Display`. This allows the following:
    /// ```text
    ///     println!("{}", self.with_ctx(ctx));
    /// ```
    fn with_ctx<'a>(&'a self, ctx: &'a C) -> impl std::fmt::Display + 'a {
        pub struct WithCtx<'a, C, T: ?Sized> {
            val: &'a T,
            ctx: &'a C,
        }

        impl<'a, C, T: ?Sized> std::fmt::Display for WithCtx<'a, C, T>
        where
            T: FmtWithCtx<C>,
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = self.val.fmt_with_ctx(self.ctx);
                f.write_str(&s)
            }
        }

        WithCtx { val: self, ctx }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for BlockData {
    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        let mut out: Vec<String> = Vec::new();

        // Format the statements
        for statement in &self.statements {
            out.push(format!("{}{};\n", tab, statement.fmt_with_ctx(ctx)).to_string());
        }

        // Format the terminator
        out.push(format!("{}{};", tab, self.terminator.fmt_with_ctx(ctx)));

        // Join the strings
        out.join("")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for CastKind {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            CastKind::Scalar(src, tgt) => format!("cast<{src},{tgt}>"),
            CastKind::FnPtr(src, tgt) => {
                format!("cast<{},{}>", src.fmt_with_ctx(ctx), tgt.fmt_with_ctx(ctx))
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ConstantExpr {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        self.value.fmt_with_ctx(ctx)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ConstGeneric {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            ConstGeneric::Var(id) => ctx.format_object(*id),
            ConstGeneric::Value(v) => v.to_string(),
            ConstGeneric::Global(id) => ctx.format_object(*id),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for DeclarationGroup {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        use DeclarationGroup::*;
        match self {
            Type(g) => format!("Type decls group: {}", g.fmt_with_ctx(ctx)),
            Fun(g) => format!("Fun decls group: {}", g.fmt_with_ctx(ctx)),
            Global(g) => format!("Global decls group: {}", g.fmt_with_ctx(ctx)),
            TraitDecl(g) => format!("Trait decls group: {}", g.fmt_with_ctx(ctx)),
            TraitImpl(g) => format!("Trait impls group: {}", g.fmt_with_ctx(ctx)),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Field {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match &self.name {
            Option::Some(name) => format!("{}: {}", name, self.ty.fmt_with_ctx(ctx)),
            Option::None => self.ty.fmt_with_ctx(ctx),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for FnOperand {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            FnOperand::Regular(func) => func.fmt_with_ctx(ctx),
            FnOperand::Move(p) => format!("(move {})", p.fmt_with_ctx(ctx)),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for FnPtr {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let generics = self.generics.fmt_with_ctx_split_trait_refs(ctx);
        let f = match &self.func {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id)) => {
                format!("{}", ctx.format_object(*def_id),)
            }
            FunIdOrTraitMethodRef::Fun(FunId::Assumed(assumed)) => {
                format!("@{}", assumed.variant_name())
            }
            FunIdOrTraitMethodRef::Trait(trait_ref, method_id, _) => {
                format!("{}::{}", trait_ref.fmt_with_ctx(ctx), &method_id.0)
            }
        };
        format!("{}{}", f, generics)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for FunSig {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let ctx = &ctx.set_generics(&self.generics);

        // Unsafe keyword
        let unsafe_kw = if self.is_unsafe {
            "unsafe ".to_string()
        } else {
            "".to_string()
        };

        // Generic parameters
        let (params, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for ty in &self.inputs {
            args.push(ty.fmt_with_ctx(ctx).to_string());
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_string()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx))
        };

        // Clauses
        let clauses = fmt_where_clauses_with_ctx(
            ctx,
            "",
            &self.parent_params_info,
            trait_clauses,
            &self.preds,
        );

        // Put everything together
        format!("{unsafe_kw}fn{params}({args}){ret_ty}{clauses}",)
    }
}

impl<Id: Copy, C: AstFormatter + Formatter<Id>> FmtWithCtx<C> for GDeclarationGroup<Id> {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        use GDeclarationGroup::*;
        match self {
            NonRec(id) => format!("Non rec: {}", ctx.format_object(*id)),
            Rec(ids) => {
                let ids = ids
                    .iter()
                    .map(|id| ctx.format_object(*id))
                    .collect::<Vec<String>>()
                    .join(", ");
                format!("Rec: {}", ids)
            }
        }
    }
}

impl GenericArgs {
    pub(crate) fn fmt_with_ctx_no_brackets<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let mut params = Vec::new();
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        for x in regions {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in types {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in const_generics {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in trait_refs {
            params.push(x.fmt_with_ctx(ctx))
        }
        params.join(", ")
    }

    pub fn fmt_with_ctx_split_trait_refs<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let mut params = Vec::new();
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs,
        } = self;
        for x in regions {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in types {
            params.push(x.fmt_with_ctx(ctx));
        }
        for x in const_generics {
            params.push(x.fmt_with_ctx(ctx));
        }
        let params = if params.is_empty() {
            "".to_string()
        } else {
            format!("<{}>", params.join(", "))
        };

        let mut clauses = Vec::new();
        for x in trait_refs {
            clauses.push(x.fmt_with_ctx(ctx));
        }
        let clauses = if clauses.is_empty() {
            "".to_string()
        } else {
            format!("[{}]", clauses.join(", "))
        };
        format!("{params}{clauses}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for GenericArgs {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        if self.is_empty() {
            "".to_string()
        } else {
            format!("<{}>", self.fmt_with_ctx_no_brackets(ctx),)
        }
    }
}

impl GenericParams {
    pub fn fmt_with_ctx_with_trait_clauses<C>(&self, ctx: &C) -> (String, Vec<String>)
    where
        C: AstFormatter,
    {
        let mut params = Vec::new();
        let GenericParams {
            regions,
            types,
            const_generics,
            trait_clauses,
        } = self;
        for x in regions {
            params.push(x.to_string());
        }
        for x in types {
            params.push(x.to_string());
        }
        for x in const_generics {
            params.push(x.to_string());
        }
        let params = if params.is_empty() {
            "".to_string()
        } else {
            format!("<{}>", params.join(", "))
        };

        let mut clauses = Vec::new();
        for x in trait_clauses {
            clauses.push(x.fmt_with_ctx(ctx));
        }
        (params, clauses)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for GenericParams {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        if self.is_empty() {
            "".to_string()
        } else {
            let mut params = Vec::new();
            let GenericParams {
                regions,
                types,
                const_generics,
                trait_clauses,
            } = self;
            for x in regions {
                params.push(x.to_string());
            }
            for x in types {
                params.push(x.to_string());
            }
            for x in const_generics {
                params.push(x.to_string());
            }
            for x in trait_clauses {
                params.push(x.fmt_with_ctx(ctx));
            }
            format!("<{}>", params.join(", "))
        }
    }
}

impl<T, C> FmtWithCtx<C> for GExprBody<T>
where
    C: for<'a> SetLocals<'a>,
    for<'a> <C as SetLocals<'a>>::C: AstFormatter,
    for<'a, 'b> <C as SetLocals<'a>>::C: AstFormatter + Formatter<&'b T>,
{
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // By default use a tab.
        self.fmt_with_ctx_and_indent(TAB_INCR, ctx)
    }

    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        // Update the context
        let ctx = &ctx.set_locals(&self.locals);

        // Format the local variables
        let mut locals: Vec<String> = Vec::new();
        for v in &self.locals {
            let index = v.index.index();
            let comment = if index == 0 {
                "// return".to_string()
            } else if index <= self.arg_count {
                format!("// arg #{index}").to_string()
            } else {
                match &v.name {
                    Some(_) => "// local".to_string(),
                    None => "// anonymous local".to_string(),
                }
            };

            let var_id = v.index.to_pretty_string();
            let var_name = match &v.name {
                Some(name) => format!("{name}{var_id}"),
                None => var_id,
            };

            locals.push(
                format!(
                    "{tab}let {var_name}: {}; {comment}\n",
                    v.ty.fmt_with_ctx(ctx),
                )
                .to_string(),
            );
        }

        let mut locals = locals.join("");
        locals.push('\n');

        // Format the body blocks - TODO: we don't take the indentation
        // into account, here
        let body = ctx.format_object(&self.body);

        // Put everything together
        let mut out = locals;
        out.push_str(&body);
        out
    }
}

impl<T, C> FmtWithCtx<C> for GFunDecl<T>
where
    // For the signature
    C: for<'a> SetGenerics<'a>,
    for<'a> <C as SetGenerics<'a>>::C: AstFormatter,
    for<'a, 'b> <C as SetGenerics<'a>>::C: AstFormatter + Formatter<&'b T>,
    // For the body
    for<'a, 'b> <C as SetGenerics<'a>>::C: SetLocals<'b>,
    for<'a, 'b> <<C as SetGenerics<'a>>::C as SetLocals<'b>>::C: AstFormatter,
    for<'a, 'b, 'c> <<C as SetGenerics<'a>>::C as SetLocals<'b>>::C: Formatter<&'c T>,
{
    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        // Update the context
        let ctx = &ctx.set_generics(&self.signature.generics);

        // Unsafe keyword
        let unsafe_kw = if self.signature.is_unsafe {
            "unsafe ".to_string()
        } else {
            "".to_string()
        };

        // Function name
        let name = self.name.fmt_with_ctx(ctx);

        // Generic parameters
        let (params, trait_clauses) = self.signature.generics.fmt_with_ctx_with_trait_clauses(ctx);

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for i in 0..self.signature.inputs.len() {
            // The input variables start at index 1
            let id = VarId::new(i + 1);
            let arg_ty = &self.signature.inputs.get(i).unwrap();
            args.push(
                format!("{}: {}", id.to_pretty_string(), arg_ty.fmt_with_ctx(ctx)).to_string(),
            );
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.signature.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_string()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx))
        };

        // Predicates
        let preds = fmt_where_clauses_with_ctx(
            ctx,
            tab,
            &self.signature.parent_params_info,
            trait_clauses,
            &self.signature.preds,
        );

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{tab}{unsafe_kw}fn {name}{params}({args}){ret_ty}{preds}")
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{tab}{TAB_INCR}");
                let body = body.fmt_with_ctx_and_indent(&body_tab, ctx);

                // Put everything together
                format!(
                    "{tab}{unsafe_kw}fn {name}{params}({args}){ret_ty}{preds}\n{tab}{{\n{body}\n{tab}}}",
                )
            }
        }
    }
}

impl<T, C> FmtWithCtx<C> for GGlobalDecl<T>
where
    C: AstFormatter,
    C: for<'a> SetLocals<'a>,
    for<'a> <C as SetGenerics<'a>>::C: AstFormatter,
    for<'a, 'b> <<C as SetGenerics<'a>>::C as SetLocals<'b>>::C: AstFormatter,
    for<'a, 'b, 'c> <<C as SetGenerics<'a>>::C as SetLocals<'b>>::C:
        AstFormatter + Formatter<&'c T>,
{
    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        // Update the context with the generics
        let ctx = &ctx.set_generics(&self.generics);

        // Translate the parameters and the trait clauses
        let (params, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);
        // Predicates
        let eq_space = if trait_clauses.is_empty() && self.preds.is_empty() {
            " ".to_string()
        } else {
            "\n ".to_string()
        };
        let preds = fmt_where_clauses_with_ctx(ctx, "  ", &None, trait_clauses, &self.preds);

        // Decl name
        let name = self.name.fmt_with_ctx(ctx);

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{tab}global {name}{params}{preds}{eq_space}")
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{tab}{TAB_INCR}");
                let body = body.fmt_with_ctx_and_indent(&body_tab, ctx);

                // Put everything together
                format!("{tab}global {name}{params}{preds}{eq_space} {{\n{body}\n{tab}}}")
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ImplElem {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let d = if self.disambiguator.is_zero() {
            "".to_string()
        } else {
            format!("#{}", self.disambiguator)
        };
        let ctx = ctx.set_generics(&self.generics);
        // Just printing the generics (not the predicates)
        format!("{{{}{d}}}", self.kind.fmt_with_ctx(&ctx),)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ImplElemKind {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            ImplElemKind::Ty(ty) => ty.fmt_with_ctx(ctx),
            ImplElemKind::Trait(tr) => {
                // We need to put the first type parameter aside: it is
                // the type for which we implement the trait.
                // This is not very clean because it's hard to move the
                // first element out of a vector...
                let TraitDeclRef { trait_id, generics } = tr;
                let (ty, generics) = generics.pop_first_type_arg();
                let tr = TraitDeclRef {
                    trait_id: *trait_id,
                    generics,
                };
                format!("impl {} for {}", tr.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Name {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let name = self
            .name
            .iter()
            .map(|x| x.fmt_with_ctx(ctx))
            .collect::<Vec<String>>();
        name.join("::")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for NonLocalTraitClause {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let clause_id = self.clause_id.fmt_with_ctx(ctx);
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("[{clause_id}]: {trait_id}{generics}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Operand {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            Operand::Copy(p) => format!("copy ({})", p.fmt_with_ctx(ctx)),
            Operand::Move(p) => format!("move ({})", p.fmt_with_ctx(ctx)),
            Operand::Const(c) => format!("const ({})", c.fmt_with_ctx(ctx)),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for PathElem {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            PathElem::Ident(s, d) => {
                let d = if d.is_zero() {
                    "".to_string()
                } else {
                    format!("#{}", d)
                };
                format!("{s}{d}")
            }
            PathElem::Impl(impl_elem) => impl_elem.fmt_with_ctx(ctx),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Place {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let mut out = ctx.format_object(self.var_id);

        for p in &self.projection {
            match p {
                ProjectionElem::Deref => {
                    out = format!("*({out})");
                }
                ProjectionElem::DerefBox => {
                    out = format!("deref_box ({out})");
                }
                ProjectionElem::DerefRawPtr => {
                    out = format!("deref_raw_ptr ({out})");
                }
                ProjectionElem::Field(proj_kind, field_id) => match proj_kind {
                    FieldProjKind::Adt(adt_id, opt_variant_id) => {
                        let field_name = ctx.format_object((*adt_id, *opt_variant_id, *field_id));
                        let downcast = match opt_variant_id {
                            None => "".to_string(),
                            Some(variant_id) => format!(" as variant @{variant_id}"),
                        };
                        out = format!("({out}{downcast}).{field_name}");
                    }
                    FieldProjKind::Tuple(_) => {
                        out = format!("({out}).{field_id}");
                    }
                    FieldProjKind::ClosureState => {
                        out = format!("({out}).@closure_state_field_{field_id}");
                    }
                },
                ProjectionElem::Index(operand, _) => out = format!("({out})[{}]", operand),
            }
        }

        out
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for RawConstantExpr {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            RawConstantExpr::Literal(c) => c.to_string(),
            RawConstantExpr::Adt(variant_id, values) => {
                // It is a bit annoying: in order to properly format the value,
                // we need the type (which contains the type def id).
                // Anyway, the printing utilities are mostly for debugging.
                let variant_id = match variant_id {
                    Option::Some(id) => format!("Some({id})"),
                    Option::None => "None".to_string(),
                };
                let values: Vec<String> = values.iter().map(|v| v.fmt_with_ctx(ctx)).collect();
                format!("ConstAdt {} [{}]", variant_id, values.join(", "))
            }
            RawConstantExpr::Global(id, generics) => {
                format!(
                    "{}{}",
                    ctx.format_object(*id),
                    generics.fmt_with_ctx_split_trait_refs(ctx)
                )
            }
            RawConstantExpr::TraitConst(trait_ref, name) => {
                format!("{}::{name}", trait_ref.fmt_with_ctx(ctx),)
            }
            RawConstantExpr::Ref(cv) => {
                format!("&{}", cv.fmt_with_ctx(ctx))
            }
            RawConstantExpr::Var(id) => format!("{}", ctx.format_object(*id)),
            RawConstantExpr::FnPtr(f) => {
                format!("{}", f.fmt_with_ctx(ctx),)
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Region {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            Region::Static => "'static".to_string(),
            Region::BVar(grid, id) => ctx.format_object((*grid, *id)),
            Region::Erased => "'_".to_string(),
            Region::Unknown => "'_UNKNOWN_".to_string(),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Rvalue {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            Rvalue::Use(x) => x.fmt_with_ctx(ctx),
            Rvalue::Ref(place, borrow_kind) => match borrow_kind {
                BorrowKind::Shared => format!("&{}", place.fmt_with_ctx(ctx)),
                BorrowKind::Mut => format!("&mut {}", place.fmt_with_ctx(ctx)),
                BorrowKind::TwoPhaseMut => {
                    format!("&two-phase-mut {}", place.fmt_with_ctx(ctx))
                }
                BorrowKind::Shallow => format!("&shallow {}", place.fmt_with_ctx(ctx)),
            },
            Rvalue::UnaryOp(unop, x) => {
                format!("{}({})", unop.fmt_with_ctx(ctx), x.fmt_with_ctx(ctx))
            }
            Rvalue::BinaryOp(binop, x, y) => {
                format!("{} {} {}", x.fmt_with_ctx(ctx), binop, y.fmt_with_ctx(ctx))
            }
            Rvalue::Discriminant(p, _) => {
                format!("@discriminant({})", p.fmt_with_ctx(ctx),)
            }
            Rvalue::Aggregate(kind, ops) => {
                let ops_s: Vec<String> = ops.iter().map(|op| op.fmt_with_ctx(ctx)).collect();
                match kind {
                    AggregateKind::Adt(def_id, variant_id, _) => {
                        match def_id {
                            TypeId::Tuple => format!("({})", ops_s.join(", ")),
                            TypeId::Assumed(_) => unreachable!(),
                            TypeId::Adt(def_id) => {
                                // Format every field
                                let mut fields = vec![];
                                for (i, op) in ops.iter().enumerate() {
                                    let field_id = FieldId::new(i);
                                    let field_name =
                                        ctx.format_object((*def_id, *variant_id, field_id));
                                    fields.push(format!(
                                        "{}: {}",
                                        field_name,
                                        op.fmt_with_ctx(ctx)
                                    ));
                                }

                                let variant = match variant_id {
                                    None => ctx.format_object(*def_id),
                                    Some(variant_id) => ctx.format_object((*def_id, *variant_id)),
                                };
                                format!("{} {{ {} }}", variant, fields.join(", "))
                            }
                        }
                    }
                    AggregateKind::Array(_, len) => {
                        format!("[{}; {}]", ops_s.join(", "), len.fmt_with_ctx(ctx))
                    }
                    AggregateKind::Closure(fn_id, generics) => {
                        format!(
                            "{{{}{}}} {{{}}}",
                            ctx.format_object(*fn_id),
                            generics.fmt_with_ctx_split_trait_refs(ctx),
                            ops_s.join(", ")
                        )
                    }
                }
            }
            Rvalue::Global(gid, generics) => {
                format!(
                    "{}{}",
                    ctx.format_object(*gid),
                    generics.fmt_with_ctx_split_trait_refs(ctx)
                )
            }
            Rvalue::Len(place, ..) => format!("len({})", place.fmt_with_ctx(ctx)),
            Rvalue::Repeat(op, _ty, cg) => {
                format!("[{}; {}]", op.fmt_with_ctx(ctx), cg.fmt_with_ctx(ctx))
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ullbc::Statement {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        use ullbc::RawStatement;
        match &self.content {
            RawStatement::Assign(place, rvalue) => format!(
                "{} := {}",
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            ),
            RawStatement::FakeRead(place) => {
                format!("@fake_read({})", place.fmt_with_ctx(ctx))
            }
            RawStatement::SetDiscriminant(place, variant_id) => format!(
                "@discriminant({}) := {}",
                place.fmt_with_ctx(ctx),
                variant_id
            ),
            RawStatement::StorageDead(vid) => {
                format!("@storage_dead({})", vid.to_pretty_string())
            }
            RawStatement::Deinit(place) => {
                format!("@deinit({})", place.fmt_with_ctx(ctx))
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for llbc::Statement {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // By default use a tab.
        self.fmt_with_ctx_and_indent(TAB_INCR, ctx)
    }

    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        use llbc::RawStatement;
        match &self.content {
            RawStatement::Assign(place, rvalue) => format!(
                "{}{} := {}",
                tab,
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            ),
            RawStatement::FakeRead(place) => {
                format!("{}@fake_read({})", tab, place.fmt_with_ctx(ctx))
            }
            RawStatement::SetDiscriminant(place, variant_id) => format!(
                "{}@discriminant({}) := {}",
                tab,
                place.fmt_with_ctx(ctx),
                variant_id
            ),
            RawStatement::Drop(place) => {
                format!("{}drop {}", tab, place.fmt_with_ctx(ctx))
            }
            RawStatement::Assert(assert) => format!(
                "{}assert({} == {})",
                tab,
                assert.cond.fmt_with_ctx(ctx),
                assert.expected,
            ),
            RawStatement::Call(call) => {
                let (call_s, _) = fmt_call(ctx, call);
                format!("{tab}{} := {call_s}", call.dest.fmt_with_ctx(ctx),)
            }
            RawStatement::Panic => format!("{tab}panic"),
            RawStatement::Return => format!("{tab}return"),
            RawStatement::Break(index) => format!("{tab}break {index}"),
            RawStatement::Continue(index) => format!("{tab}continue {index}"),
            RawStatement::Nop => format!("{tab}nop"),
            RawStatement::Sequence(st1, st2) => format!(
                "{}\n{}",
                st1.fmt_with_ctx_and_indent(tab, ctx),
                st2.fmt_with_ctx_and_indent(tab, ctx)
            ),
            RawStatement::Switch(switch) => match switch {
                Switch::If(discr, true_st, false_st) => {
                    let inner_tab = format!("{tab}{TAB_INCR}");
                    format!(
                        "{}if {} {{\n{}\n{}}}\n{}else {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        true_st.fmt_with_ctx_and_indent(&inner_tab, ctx),
                        tab,
                        tab,
                        false_st.fmt_with_ctx_and_indent(&inner_tab, ctx),
                        tab,
                    )
                }
                Switch::SwitchInt(discr, _ty, maps, otherwise) => {
                    let inner_tab1 = format!("{tab}{TAB_INCR}");
                    let inner_tab2 = format!("{inner_tab1}{TAB_INCR}");
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(pvl, st)| {
                            // Note that there may be several pattern values
                            let pvl: Vec<String> = pvl.iter().map(|v| v.to_string()).collect();
                            format!(
                                "{}{} => {{\n{}\n{}}}",
                                inner_tab1,
                                pvl.join(" | "),
                                st.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                                inner_tab1
                            )
                        })
                        .collect();
                    maps.push(format!(
                        "{}_ => {{\n{}\n{}}}",
                        inner_tab1,
                        otherwise.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                        inner_tab1
                    ));
                    let maps = maps.join(",\n");

                    format!(
                        "{}switch {} {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        maps,
                        tab
                    )
                }
                Switch::Match(discr, maps, otherwise) => {
                    let inner_tab1 = format!("{tab}{TAB_INCR}");
                    let inner_tab2 = format!("{inner_tab1}{TAB_INCR}");
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(pvl, st)| {
                            // Note that there may be several pattern values
                            let pvl: Vec<String> = pvl.iter().map(|v| v.to_string()).collect();
                            format!(
                                "{}{} => {{\n{}\n{}}}",
                                inner_tab1,
                                pvl.join(" | "),
                                st.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                                inner_tab1
                            )
                        })
                        .collect();
                    if let Some(otherwise) = otherwise {
                        maps.push(format!(
                            "{}_ => {{\n{}\n{}}}",
                            inner_tab1,
                            otherwise.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                            inner_tab1
                        ));
                    };
                    let maps = maps.join(",\n");

                    format!(
                        "{}match {} {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        maps,
                        tab
                    )
                }
            },
            RawStatement::Loop(body) => {
                let inner_tab = format!("{tab}{TAB_INCR}");
                format!(
                    "{}loop {{\n{}\n{}}}",
                    tab,
                    body.fmt_with_ctx_and_indent(&inner_tab, ctx),
                    tab
                )
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Terminator {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match &self.content {
            RawTerminator::Goto { target } => format!("goto bb{target}"),
            RawTerminator::Switch { discr, targets } => match targets {
                SwitchTargets::If(true_block, false_block) => format!(
                    "if {} -> bb{} else -> bb{}",
                    discr.fmt_with_ctx(ctx),
                    true_block,
                    false_block
                ),
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(v, bid)| format!("{}: bb{}", v.to_string(), bid))
                        .collect();
                    maps.push(format!("otherwise: bb{otherwise}"));
                    let maps = maps.join(", ");

                    format!("switch {} -> {}", discr.fmt_with_ctx(ctx), maps)
                }
            },
            RawTerminator::Panic => "panic".to_string(),
            RawTerminator::Return => "return".to_string(),
            RawTerminator::Unreachable => "unreachable".to_string(),
            RawTerminator::Drop { place, target } => {
                format!("drop {} -> bb{}", place.fmt_with_ctx(ctx), target)
            }
            RawTerminator::Call { call, target } => {
                let (call_s, _) = fmt_call(ctx, call);
                format!("{} := {call_s} -> bb{target}", call.dest.fmt_with_ctx(ctx),)
            }
            RawTerminator::Assert {
                cond,
                expected,
                target,
            } => format!(
                "assert({} == {}) -> bb{}",
                cond.fmt_with_ctx(ctx),
                expected,
                target
            ),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitClause {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let clause_id = ctx.format_object(self.clause_id);
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("[{clause_id}]: {trait_id}{generics}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitDecl {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // Update the context
        let ctx = &ctx.set_generics(&self.generics);

        let name = self.name.fmt_with_ctx(ctx);
        let (generics, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);
        let clauses = fmt_where_clauses_with_ctx(ctx, "", &None, trait_clauses, &self.preds);

        let items = {
            let items = self
                .parent_clauses
                .iter()
                .map(|c| {
                    format!(
                        "{TAB_INCR}parent_clause_{} : {}\n",
                        c.clause_id.to_string(),
                        c.fmt_with_ctx(ctx)
                    )
                })
                .chain(
                    self.consts
                        .iter()
                        .map(|(name, (ty, opt_id))| {
                            let ty = ty.fmt_with_ctx(ctx);
                            match opt_id {
                                None => format!("{TAB_INCR}const {name} : {ty}\n"),
                                Some(id) => {
                                    format!(
                                        "{TAB_INCR}const {name} : {ty} = {}\n",
                                        ctx.format_object(*id)
                                    )
                                }
                            }
                        })
                        .chain(self.types.iter().map(|(name, (trait_clauses, opt_ty))| {
                            let trait_clauses: Vec<_> =
                                trait_clauses.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
                            let clauses = fmt_where_clauses(
                                &format!("{TAB_INCR}{TAB_INCR}"),
                                0,
                                trait_clauses,
                            );
                            match opt_ty {
                                None => format!("{TAB_INCR}type {name}{clauses}\n"),
                                Some(ty) => {
                                    format!(
                                        "{TAB_INCR}type {name} = {}{clauses}\n",
                                        ty.fmt_with_ctx(ctx)
                                    )
                                }
                            }
                        }))
                        .chain(self.required_methods.iter().map(|(name, f)| {
                            format!("{TAB_INCR}fn {name} : {}\n", ctx.format_object(*f))
                        }))
                        .chain(self.provided_methods.iter().map(|(name, f)| match f {
                            None => format!("{TAB_INCR}fn {name}\n"),
                            Some(f) => format!("{TAB_INCR}fn {name} : {}\n", ctx.format_object(*f)),
                        })),
                )
                .collect::<Vec<String>>();
            if items.is_empty() {
                "".to_string()
            } else {
                format!("\n{{\n{}}}", items.join(""))
            }
        };

        format!("trait {name}{generics}{clauses}{items}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitDeclRef {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx_split_trait_refs(ctx);
        format!("{trait_id}{generics}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitImpl {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // Update the context
        let ctx = &ctx.set_generics(&self.generics);

        let name = self.name.fmt_with_ctx(ctx);
        let (generics, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);
        let clauses = fmt_where_clauses_with_ctx(ctx, "", &None, trait_clauses, &self.preds);

        let items = {
            let items = self
                .parent_trait_refs
                .iter()
                .enumerate()
                .map(|(i, clause)| {
                    let i = TraitClauseId::new(i);
                    format!(
                        "{TAB_INCR}parent_clause{i} = {}\n",
                        clause.fmt_with_ctx(ctx)
                    )
                })
                .chain(self.consts.iter().map(|(name, (ty, id))| {
                    format!(
                        "{TAB_INCR}const {name} : {} = {}\n",
                        ty.fmt_with_ctx(ctx),
                        ctx.format_object(*id)
                    )
                }))
                .chain(self.types.iter().map(|(name, (trait_refs, ty))| {
                    let trait_refs = trait_refs
                        .iter()
                        .map(|x| x.fmt_with_ctx(ctx))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!(
                        "{TAB_INCR}type {name} = {} with [{}]\n",
                        ty.fmt_with_ctx(ctx),
                        trait_refs
                    )
                }))
                .chain(
                    self.required_methods
                        .iter()
                        .chain(self.provided_methods.iter())
                        .map(|(name, f)| {
                            format!("{TAB_INCR}fn {name} = {}\n", ctx.format_object(*f))
                        }),
                )
                .collect::<Vec<String>>();
            if items.is_empty() {
                "".to_string()
            } else {
                format!("\n{{\n{}}}", items.join(""))
            }
        };

        let impl_trait = self.impl_trait.fmt_with_ctx(ctx);
        format!("impl{generics} {name}{generics} : {impl_trait}{clauses}{items}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitInstanceId {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            TraitInstanceId::SelfId => "Self".to_string(),
            TraitInstanceId::ParentClause(id, _decl_id, clause_id) => {
                let id = id.fmt_with_ctx(ctx);
                // Using on purpose [to_pretty_string] instead of [format_object]:
                // the clause is local to the associated type, so it should not
                // be referenced in the current context.
                let clause = clause_id.to_pretty_string();
                format!("(parents({id})::[{clause}])")
            }
            TraitInstanceId::ItemClause(id, _decl_id, type_name, clause_id) => {
                let id = id.fmt_with_ctx(ctx);
                // Using on purpose [to_pretty_string] instead of [format_object]:
                // the clause is local to the associated type, so it should not
                // be referenced in the current context.
                let clause = clause_id.to_pretty_string();
                format!("({id}::{type_name}::[{clause}])")
            }
            TraitInstanceId::TraitImpl(id) => ctx.format_object(*id),
            TraitInstanceId::Clause(id) => ctx.format_object(*id),
            TraitInstanceId::BuiltinOrAuto(id) => ctx.format_object(*id),
            TraitInstanceId::FnPointer(box ty) => {
                format!("(fn_ptr:{})", ty.fmt_with_ctx(ctx))
            }
            TraitInstanceId::Closure(fid, generics) => {
                format!(
                    "(closure:{}{})",
                    ctx.format_object(*fid),
                    generics.fmt_with_ctx(ctx)
                )
            }
            TraitInstanceId::Unsolved(trait_id, generics) => {
                format!(
                    "Unsolved({}{})",
                    ctx.format_object(*trait_id),
                    generics.fmt_with_ctx(ctx),
                )
            }
            TraitInstanceId::Unknown(msg) => format!("UNKNOWN({msg})"),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitRef {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let trait_id = self.trait_id.fmt_with_ctx(ctx);
        let generics = self.generics.fmt_with_ctx_split_trait_refs(ctx);
        format!("{trait_id}{generics}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitTypeConstraint {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let trait_ref = self.trait_ref.fmt_with_ctx(ctx);
        let ty = self.ty.fmt_with_ctx(ctx);
        format!("{}::{} = {}", trait_ref, self.type_name, ty)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Ty {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            Ty::Adt(id, generics) => {
                let adt_ident = id.fmt_with_ctx(ctx);

                if id.is_tuple() {
                    assert!(generics.trait_refs.is_empty());
                    let generics = generics.fmt_with_ctx_no_brackets(ctx);
                    format!("({generics})")
                } else {
                    let generics = generics.fmt_with_ctx(ctx);
                    format!("{adt_ident}{generics}")
                }
            }
            Ty::TypeVar(id) => ctx.format_object(*id),
            Ty::Literal(kind) => kind.to_string(),
            Ty::Never => "!".to_string(),
            Ty::Ref(r, ty, kind) => match kind {
                RefKind::Mut => {
                    format!("&{} mut ({})", r.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
                }
                RefKind::Shared => {
                    format!("&{} ({})", r.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
                }
            },
            Ty::RawPtr(ty, kind) => match kind {
                RefKind::Mut => format!("*const {}", ty.fmt_with_ctx(ctx)),
                RefKind::Shared => format!("*mut {}", ty.fmt_with_ctx(ctx)),
            },
            Ty::TraitType(trait_ref, name) => {
                format!("{}::{name}", trait_ref.fmt_with_ctx(ctx),)
            }
            Ty::Arrow(regions, inputs, box output) => {
                // Update the bound regions
                let ctx = &ctx.push_bound_regions(regions);

                let regions = if regions.is_empty() {
                    "".to_string()
                } else {
                    format!(
                        "<{}>",
                        regions
                            .iter()
                            .map(|r| r.to_string())
                            .collect::<Vec<String>>()
                            .join(", ")
                    )
                };
                let inputs = inputs
                    .iter()
                    .map(|x| x.fmt_with_ctx(ctx))
                    .collect::<Vec<String>>()
                    .join(", ");
                if output.is_unit() {
                    format!("fn{regions}({inputs})")
                } else {
                    let output = output.fmt_with_ctx(ctx);
                    format!("fn{regions}({inputs}) -> {output}")
                }
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TypeDecl {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let ctx = &ctx.set_generics(&self.generics);

        let (params, trait_clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx);
        // Predicates
        let eq_space = if trait_clauses.is_empty() && self.preds.is_empty() {
            " ".to_string()
        } else {
            "\n ".to_string()
        };
        let preds = fmt_where_clauses_with_ctx(ctx, "  ", &None, trait_clauses, &self.preds);

        match &self.kind {
            TypeDeclKind::Struct(fields) => {
                if !fields.is_empty() {
                    let fields: Vec<String> = fields
                        .iter()
                        .map(|f| format!("\n  {}", f.fmt_with_ctx(ctx)))
                        .collect();
                    let fields = fields.join(",");
                    format!(
                        "struct {}{params}{preds}{eq_space}=\n{{{fields}\n}}",
                        self.name.fmt_with_ctx(ctx)
                    )
                } else {
                    format!(
                        "struct {}{params}{preds}{eq_space}= {{}}",
                        self.name.fmt_with_ctx(ctx)
                    )
                }
            }
            TypeDeclKind::Enum(variants) => {
                let variants: Vec<String> = variants
                    .iter()
                    .map(|v| format!("|  {}", v.fmt_with_ctx(ctx)))
                    .collect();
                let variants = variants.join("\n");
                format!(
                    "enum {}{params}{preds}{eq_space}=\n{variants}\n",
                    self.name.fmt_with_ctx(ctx)
                )
            }
            TypeDeclKind::Opaque => {
                format!("opaque type {}{params}{preds}", self.name.fmt_with_ctx(ctx))
            }
            TypeDeclKind::Error(msg) => {
                format!(
                    "opaque type {}{params}{preds} = ERROR({msg})",
                    self.name.fmt_with_ctx(ctx),
                )
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TypeId {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            TypeId::Tuple => "".to_string(),
            TypeId::Adt(def_id) => ctx.format_object(*def_id),
            TypeId::Assumed(aty) => get_name_from_type_id(*aty).join("::"),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for UnOp {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            UnOp::Not => "~".to_string(),
            UnOp::Neg => "-".to_string(),
            UnOp::Cast(kind) => kind.fmt_with_ctx(ctx),
            UnOp::ArrayToSlice(..) => "array_to_slice".to_string(),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Variant {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let fields: Vec<String> = self.fields.iter().map(|f| f.fmt_with_ctx(ctx)).collect();
        let fields = fields.join(", ");
        format!("{}({})", self.name, fields)
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            BinOp::BitXor => write!(f, "^"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Ge => write!(f, ">="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::CheckedAdd => write!(f, "checked.+"),
            BinOp::CheckedSub => write!(f, "checked.-"),
            BinOp::CheckedMul => write!(f, "checked.*"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Shr => write!(f, ">>"),
        }
    }
}

impl std::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            BorrowKind::Shared => write!(f, "Shared"),
            BorrowKind::Mut => write!(f, "Mut"),
            BorrowKind::TwoPhaseMut => write!(f, "TwoPhaseMut"),
            BorrowKind::Shallow => write!(f, "Shallow"),
        }
    }
}

impl std::fmt::Display for ConstantExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl std::fmt::Display for IntegerTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            IntegerTy::Isize => write!(f, "isize"),
            IntegerTy::I8 => write!(f, "i8"),
            IntegerTy::I16 => write!(f, "i16"),
            IntegerTy::I32 => write!(f, "i32"),
            IntegerTy::I64 => write!(f, "i64"),
            IntegerTy::I128 => write!(f, "i128"),
            IntegerTy::Usize => write!(f, "usize"),
            IntegerTy::U8 => write!(f, "u8"),
            IntegerTy::U16 => write!(f, "u16"),
            IntegerTy::U32 => write!(f, "u32"),
            IntegerTy::U64 => write!(f, "u64"),
            IntegerTy::U128 => write!(f, "u128"),
        }
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Literal::Scalar(v) => write!(f, "{v}"),
            Literal::Bool(v) => write!(f, "{v}"),
            Literal::Char(v) => write!(f, "{v}"),
            Literal::Str(v) => write!(f, "\"{v}\""),
            Literal::ByteStr(v) => write!(f, "{v:?}"),
        }
    }
}

impl std::fmt::Display for LiteralTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            LiteralTy::Integer(ty) => ty.fmt(f),
            LiteralTy::Char => write!(f, "char"),
            LiteralTy::Bool => write!(f, "bool"),
        }
    }
}

impl std::fmt::Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl std::fmt::Display for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl std::fmt::Display for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Region::Static => write!(f, "'static"),
            Region::BVar(grid, id) => write!(f, "'_{}_{id}", grid.index),
            Region::Erased => write!(f, "'_"),
            Region::Unknown => write!(f, "'_UNKNOWN_"),
        }
    }
}

impl std::fmt::Display for Rvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl std::fmt::Display for ScalarValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            ScalarValue::Isize(v) => write!(f, "{v} : isize"),
            ScalarValue::I8(v) => write!(f, "{v} : i8"),
            ScalarValue::I16(v) => write!(f, "{v} : i16"),
            ScalarValue::I32(v) => write!(f, "{v} : i32"),
            ScalarValue::I64(v) => write!(f, "{v} : i64"),
            ScalarValue::I128(v) => write!(f, "{v} : i128"),
            ScalarValue::Usize(v) => write!(f, "{v} : usize"),
            ScalarValue::U8(v) => write!(f, "{v} : u8"),
            ScalarValue::U16(v) => write!(f, "{v} : u16"),
            ScalarValue::U32(v) => write!(f, "{v} : u32"),
            ScalarValue::U64(v) => write!(f, "{v} : u64"),
            ScalarValue::U128(v) => write!(f, "{v} : u128"),
        }
    }
}

impl std::fmt::Display for TraitItemName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl std::string::ToString for ConstGenericVar {
    fn to_string(&self) -> String {
        format!("const {} : {}", self.name, self.ty.to_string())
    }
}

impl std::string::ToString for Field {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&FmtCtx::new())
    }
}

impl std::string::ToString for RegionVar {
    fn to_string(&self) -> String {
        match &self.name {
            Some(name) => name.to_string(),
            None => format!("'_{}", self.index),
        }
    }
}

impl std::string::ToString for TypeVar {
    fn to_string(&self) -> String {
        self.name.to_string()
    }
}

impl std::string::ToString for Var {
    fn to_string(&self) -> String {
        let id = self.index.to_pretty_string();
        match &self.name {
            // We display both the variable name and its id because some
            // variables may have the same name (in different scopes)
            Some(name) => format!("{name}{id}"),
            None => id,
        }
    }
}

impl std::string::ToString for Variant {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&FmtCtx::new())
    }
}

/// Format a function call.
/// We return the pair: (function call, comment)
pub fn fmt_call<C>(ctx: &C, call: &Call) -> (String, Option<String>)
where
    C: AstFormatter,
{
    let args: Vec<String> = call.args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    let args = args.join(", ");
    let f = call.func.fmt_with_ctx(ctx);
    (format!("{f}({args})"), None)
}

pub(crate) fn fmt_body_blocks_with_ctx<C>(
    body: &Vector<BlockId, BlockData>,
    tab: &str,
    ctx: &C,
) -> String
where
    C: AstFormatter,
{
    let block_tab = format!("{tab}{TAB_INCR}");
    let mut blocks: Vec<String> = Vec::new();
    for (bid, block) in body.iter_indexed_values() {
        blocks.push(
            format!(
                "{tab}bb{}: {{\n{}\n{tab}}}\n",
                bid.index(),
                block.fmt_with_ctx_and_indent(&block_tab, ctx),
            )
            .to_string(),
        );
    }
    blocks.join("\n")
}

/// [num_parent_clauses]: we store in the definitions all the clauses
/// they have access to, which includes the clauses inherited from the parent.
/// This can be confusing: we insert a delimiter between the inherited clauses
/// and the local clauses.
pub fn fmt_where_clauses(tab: &str, num_parent_clauses: usize, clauses: Vec<String>) -> String {
    if clauses.is_empty() {
        "".to_string()
    } else {
        let mut clauses = clauses
            .iter()
            .map(|x| format!("\n{tab}{TAB_INCR}{x},"))
            .collect::<Vec<String>>();
        if num_parent_clauses > 0 {
            let local_clauses = clauses.split_off(num_parent_clauses);

            let delim1 = if local_clauses.is_empty() {
                "".to_string()
            } else {
                format!("\n{tab}{TAB_INCR}// Local clauses:")
            };

            let delim0 = if clauses.is_empty() {
                "".to_string()
            } else {
                format!("\n{tab}{TAB_INCR}// Inherited clauses:")
            };

            let clauses = clauses.join("");
            let local_clauses = local_clauses.join("");
            format!("\n{tab}where{delim0}{clauses}{delim1}{local_clauses}")
        } else {
            let clauses = clauses.join("");
            format!("\n{tab}where{clauses}")
        }
    }
}

pub fn fmt_where_clauses_with_ctx<C>(
    ctx: &C,
    tab: &str,
    info: &Option<ParamsInfo>,
    mut trait_clauses: Vec<String>,
    preds: &Predicates,
) -> String
where
    C: AstFormatter,
{
    let mut types_outlive: Vec<_> = preds
        .types_outlive
        .iter()
        .map(|OutlivesPred(x, y)| format!("{} : {}", x.fmt_with_ctx(ctx), y.fmt_with_ctx(ctx)))
        .collect();
    let mut regions_outlive: Vec<_> = preds
        .regions_outlive
        .iter()
        .map(|OutlivesPred(x, y)| format!("{} : {}", x.fmt_with_ctx(ctx), y.fmt_with_ctx(ctx)))
        .collect();
    let mut type_constraints: Vec<_> = preds
        .trait_type_constraints
        .iter()
        .map(|x| x.fmt_with_ctx(ctx))
        .collect();
    match info {
        None => {
            let clauses: Vec<_> = trait_clauses
                .into_iter()
                .chain(types_outlive.into_iter())
                .chain(regions_outlive.into_iter())
                .chain(type_constraints.into_iter())
                .collect();
            fmt_where_clauses(tab, 0, clauses)
        }
        Some(info) => {
            // Below: definitely not efficient nor convenient, but it is not really
            // important
            let local_clauses: Vec<_> = trait_clauses
                .split_off(info.num_trait_clauses)
                .into_iter()
                .chain(regions_outlive.split_off(info.num_regions_outlive))
                .chain(types_outlive.split_off(info.num_types_outlive).into_iter())
                .chain(
                    type_constraints
                        .split_off(info.num_trait_type_constraints)
                        .into_iter(),
                )
                .collect();
            let inherited_clauses: Vec<_> = trait_clauses
                .into_iter()
                .chain(regions_outlive.into_iter())
                .chain(types_outlive.into_iter())
                .chain(type_constraints.into_iter())
                .collect();
            let num_inherited = inherited_clauses.len();
            let all_clauses: Vec<_> = inherited_clauses
                .into_iter()
                .chain(local_clauses.into_iter())
                .collect();
            fmt_where_clauses(tab, num_inherited, all_clauses)
        }
    }
}

// IntTy is not defined in the current crate
pub fn intty_to_string(ty: hax::IntTy) -> String {
    use hax::IntTy::*;
    match ty {
        Isize => "isize".to_string(),
        I8 => "i8".to_string(),
        I16 => "i16".to_string(),
        I32 => "i32".to_string(),
        I64 => "i64".to_string(),
        I128 => "i128".to_string(),
    }
}

// UintTy is not defined in the current crate
pub fn uintty_to_string(ty: hax::UintTy) -> String {
    use hax::UintTy::*;
    match ty {
        Usize => "usize".to_string(),
        U8 => "u8".to_string(),
        U16 => "u16".to_string(),
        U32 => "u32".to_string(),
        U64 => "u64".to_string(),
        U128 => "u128".to_string(),
    }
}
