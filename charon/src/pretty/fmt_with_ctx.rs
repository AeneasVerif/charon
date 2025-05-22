//! Utilities for pretty-printing (u)llbc.
use crate::{
    common::TAB_INCR,
    formatter::*,
    gast,
    ids::Vector,
    llbc_ast::{self as llbc, *},
    reorder_decls::*,
    ullbc_ast::{self as ullbc, *},
};
use itertools::Itertools;
use std::{
    borrow::Cow,
    fmt::{self, Debug, Display, Write},
};

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

impl<C: AstFormatter> FmtWithCtx<C> for AbortKind {
    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        match self {
            AbortKind::Panic(name) => {
                let name = if let Some(name) = name {
                    format!("({})", name.fmt_with_ctx(ctx))
                } else {
                    format!("")
                };
                format!("{tab}panic{name}")
            }
            AbortKind::UndefinedBehavior => format!("{tab}undefined_behavior"),
            AbortKind::UnwindTerminate => format!("{tab}unwind_terminate"),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for AnyTransItem<'_> {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            AnyTransItem::Type(d) => d.fmt_with_ctx(ctx),
            AnyTransItem::Fun(d) => d.fmt_with_ctx(ctx),
            AnyTransItem::Global(d) => d.fmt_with_ctx(ctx),
            AnyTransItem::TraitDecl(d) => d.fmt_with_ctx(ctx),
            AnyTransItem::TraitImpl(d) => d.fmt_with_ctx(ctx),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Assert {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        format!(
            "assert({} == {})",
            self.cond.fmt_with_ctx(ctx),
            self.expected,
        )
    }
}

impl<T> Binder<T> {
    /// Format the parameters and contents of this binder and returns the resulting strings. Note:
    /// this assumes the binder fully replaces the existing generics.
    fn fmt_split<'a, C>(&'a self, ctx: &'a C) -> (String, String)
    where
        C: AstFormatter,
        T: FmtWithCtx<<C as PushBinder<'a>>::C>,
    {
        let ctx = &ctx.push_binder(Cow::Borrowed(&self.params));
        (
            self.params.fmt_with_ctx_single_line(ctx),
            self.skip_binder.fmt_with_ctx(ctx),
        )
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for llbc::Block {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // By default use a tab.
        self.fmt_with_ctx_and_indent(TAB_INCR, ctx)
    }

    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        self.statements
            .iter()
            .map(|st| st.fmt_with_ctx_and_indent(tab, ctx))
            .map(|st| format!("{st}\n"))
            .join("")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ullbc::BlockData {
    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        let mut out: Vec<String> = Vec::new();

        // Format the statements
        for statement in &self.statements {
            out.push(format!("{};\n", statement.fmt_with_ctx_and_indent(tab, ctx)).to_string());
        }

        // Format the terminator
        out.push(format!(
            "{};",
            self.terminator.fmt_with_ctx_and_indent(tab, ctx)
        ));

        // Join the strings
        out.join("")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for gast::Body {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            Body::Unstructured(b) => b.fmt_with_ctx(ctx),
            Body::Structured(b) => b.fmt_with_ctx(ctx),
        }
    }

    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        match self {
            Body::Unstructured(b) => b.fmt_with_ctx_and_indent(tab, ctx),
            Body::Structured(b) => b.fmt_with_ctx_and_indent(tab, ctx),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for CastKind {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            CastKind::Scalar(src, tgt) => format!("cast<{src}, {tgt}>"),
            CastKind::FnPtr(src, tgt) | CastKind::RawPtr(src, tgt) => {
                format!("cast<{}, {}>", src.fmt_with_ctx(ctx), tgt.fmt_with_ctx(ctx))
            }
            CastKind::Unsize(src, tgt) => {
                format!(
                    "unsize_cast<{}, {}>",
                    src.fmt_with_ctx(ctx),
                    tgt.fmt_with_ctx(ctx)
                )
            }
            CastKind::Transmute(src, tgt) => {
                format!(
                    "transmute<{}, {}>",
                    src.fmt_with_ctx(ctx),
                    tgt.fmt_with_ctx(ctx)
                )
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

impl<C: AstFormatter> FmtWithCtx<C> for ConstGenericVar {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let ty = self.ty.fmt_with_ctx(ctx);
        format!("const {} : {}", self.name, ty)
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
            Mixed(g) => format!("Mixed group: {}", g.fmt_with_ctx(ctx)),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ExistentialPredicate {
    fn fmt_with_ctx(&self, _ctx: &C) -> String {
        format!("exists(TODO)")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Field {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match &self.name {
            Some(name) => format!("{}: {}", name, self.ty.fmt_with_ctx(ctx)),
            None => self.ty.fmt_with_ctx(ctx),
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
        let generics = self.generics.fmt_with_ctx(ctx);
        let f = match self.func.as_ref() {
            FunIdOrTraitMethodRef::Fun(FunId::Regular(def_id)) => {
                format!("{}", ctx.format_object(*def_id),)
            }
            FunIdOrTraitMethodRef::Fun(FunId::Builtin(builtin)) => {
                format!("@{}", builtin)
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
        let (params, clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx, "");

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
        assert!(self.trait_refs.is_empty());
        let mut params = Vec::new();
        let GenericArgs {
            regions,
            types,
            const_generics,
            trait_refs: _,
            target: _,
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
            target: _,
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
        self.fmt_with_ctx_split_trait_refs(ctx)
    }
}

impl GenericParams {
    fn format_params<'a, C>(&'a self, ctx: &'a C) -> impl Iterator<Item = String> + use<'a, C>
    where
        C: AstFormatter,
    {
        let regions = self.regions.iter().map(|x| x.fmt_with_ctx(ctx));
        let types = self.types.iter().map(|x| x.fmt_with_ctx(ctx));
        let const_generics = self.const_generics.iter().map(|x| x.fmt_with_ctx(ctx));
        regions.chain(types).chain(const_generics)
    }

    fn format_clauses<'a, C>(&'a self, ctx: &'a C) -> impl Iterator<Item = String> + use<'a, C>
    where
        C: AstFormatter,
    {
        let trait_clauses = self.trait_clauses.iter().map(|x| x.fmt_with_ctx(ctx));
        let types_outlive = self.types_outlive.iter().map(|x| x.fmt_as_for(ctx));
        let regions_outlive = self.regions_outlive.iter().map(|x| x.fmt_as_for(ctx));
        let type_constraints = self
            .trait_type_constraints
            .iter()
            .map(|x| x.fmt_as_for(ctx));
        trait_clauses
            .chain(types_outlive)
            .chain(regions_outlive)
            .chain(type_constraints)
    }

    pub fn fmt_with_ctx_with_trait_clauses<C>(&self, ctx: &C, tab: &str) -> (String, String)
    where
        C: AstFormatter,
    {
        let params = self.format_params(ctx).join(", ");
        let params = if params.is_empty() {
            String::new()
        } else {
            format!("<{}>", params)
        };
        let clauses = self
            .format_clauses(ctx)
            .map(|x| format!("\n{tab}{TAB_INCR}{x},"))
            .join("");
        let clauses = if clauses.is_empty() {
            String::new()
        } else {
            format!("\n{tab}where{clauses}")
        };
        (params, clauses)
    }

    pub fn fmt_with_ctx_single_line<C>(&self, ctx: &C) -> String
    where
        C: AstFormatter,
    {
        let params = self
            .format_params(ctx)
            .chain(self.format_clauses(ctx))
            .join(", ");
        if params.is_empty() {
            String::new()
        } else {
            format!("<{}>", params)
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
        for v in &self.locals.locals {
            let index = v.index.index();
            let comment = if index == 0 {
                "// return".to_string()
            } else if index <= self.locals.arg_count {
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

impl<C> FmtWithCtx<C> for FunDecl
where
    C: AstFormatter,
    // For the signature
    C: for<'a> SetGenerics<'a>,
    for<'a> <C as SetGenerics<'a>>::C: AstFormatter,
    // For the body
    for<'a, 'b> <C as SetGenerics<'a>>::C: SetLocals<'b>,
    for<'a, 'b> <<C as SetGenerics<'a>>::C as SetLocals<'b>>::C: AstFormatter,
{
    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        let keyword = if self.signature.is_unsafe {
            "unsafe fn"
        } else {
            "fn"
        };
        let intro = self.item_meta.fmt_item_intro(ctx, tab, keyword);

        // Update the context
        let ctx = &ctx.set_generics(&self.signature.generics);

        // Generic parameters
        let (params, preds) = self
            .signature
            .generics
            .fmt_with_ctx_with_trait_clauses(ctx, tab);

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for i in 0..self.signature.inputs.len() {
            // The input variables start at index 1
            let id = LocalId::new(i + 1);
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

        // Body
        let body = match &self.body {
            Ok(body) => {
                let body = body.fmt_with_ctx(ctx);
                format!("\n{tab}{{\n{body}{tab}}}")
            }
            Err(Opaque) => String::new(),
        };

        // Put everything together
        format!("{intro}{params}({args}){ret_ty}{preds}{body}",)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for FunDeclRef {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let id = ctx.format_object(self.id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("{id}{generics}")
    }
}

impl<C> FmtWithCtx<C> for GlobalDecl
where
    C: AstFormatter,
    C: for<'a> SetLocals<'a>,
    for<'a> <C as SetGenerics<'a>>::C: AstFormatter,
    for<'a, 'b> <<C as SetGenerics<'a>>::C as SetLocals<'b>>::C: AstFormatter,
    for<'a, 'b, 'c> <<C as SetGenerics<'a>>::C as SetLocals<'b>>::C: AstFormatter,
{
    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        let keyword = match self.global_kind {
            GlobalKind::Static => "static",
            GlobalKind::AnonConst | GlobalKind::NamedConst => "const",
        };
        let intro = self.item_meta.fmt_item_intro(ctx, tab, keyword);

        // Update the context with the generics
        let ctx = &ctx.set_generics(&self.generics);

        // Translate the parameters and the trait clauses
        let (params, preds) = self.generics.fmt_with_ctx_with_trait_clauses(ctx, "  ");
        // Type
        let ty = self.ty.fmt_with_ctx(ctx);
        // Predicates
        let eq_space = if !self.generics.has_predicates() {
            " ".to_string()
        } else {
            "\n ".to_string()
        };

        // Decl name
        let initializer = ctx.format_object(self.init);

        // Put everything together
        format!("{intro}{params}: {ty}{preds}{eq_space}= {initializer}()")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for GlobalDeclRef {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let id = ctx.format_object(self.id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("{id}{generics}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ImplElem {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        ctx.format_object(self)
    }
}

impl ItemMeta {
    /// Format the start of an item definition, up to the name.
    pub fn fmt_item_intro<C>(&self, ctx: &C, tab: &str, keyword: &str) -> String
    where
        C: AstFormatter,
    {
        let name = self.name.fmt_with_ctx(ctx);
        let vis = if self.attr_info.public { "pub " } else { "" };
        let lang_item = self
            .lang_item
            .as_ref()
            .map(|id| format!("{tab}#[lang_item(\"{id}\")]\n"))
            .unwrap_or_default();
        format!("{lang_item}{tab}{vis}{keyword} {name}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for LiteralTy {
    fn fmt_with_ctx(&self, _ctx: &C) -> String {
        match self {
            LiteralTy::Integer(ty) => ty.to_string(),
            LiteralTy::Float(ty) => ty.to_string(),
            LiteralTy::Char => "char".to_owned(),
            LiteralTy::Bool => "bool".to_owned(),
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

impl<C: AstFormatter> FmtWithCtx<C> for NullOp {
    fn fmt_with_ctx(&self, _ctx: &C) -> String {
        match self {
            NullOp::SizeOf => "size_of".to_string(),
            NullOp::AlignOf => "align_of".to_string(),
            NullOp::OffsetOf(_) => "offset_of(?)".to_string(),
            NullOp::UbChecks => "ub_checks".to_string(),
        }
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

impl<C: AstFormatter, T, U> FmtWithCtx<C> for OutlivesPred<T, U>
where
    T: FmtWithCtx<C>,
    U: FmtWithCtx<C>,
{
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        format!(
            "{} : {}",
            self.0.fmt_with_ctx(ctx),
            self.1.fmt_with_ctx(ctx)
        )
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
            PathElem::Impl(impl_elem, d) => {
                let impl_elem = impl_elem.fmt_with_ctx(ctx);
                let d = if d.is_zero() {
                    "".to_string()
                } else {
                    format!("#{}", d)
                };
                format!("{impl_elem}{d}")
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Place {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match &self.kind {
            PlaceKind::Local(var_id) => ctx.format_object(*var_id),
            PlaceKind::Projection(subplace, projection) => {
                let sub = subplace.fmt_with_ctx(ctx);
                match projection {
                    ProjectionElem::Deref => {
                        format!("*({sub})")
                    }
                    ProjectionElem::Field(proj_kind, field_id) => match proj_kind {
                        FieldProjKind::Adt(adt_id, opt_variant_id) => {
                            let field_name =
                                ctx.format_object((*adt_id, *opt_variant_id, *field_id));
                            let downcast = match opt_variant_id {
                                None => "".to_string(),
                                Some(variant_id) => format!(" as variant @{variant_id}"),
                            };
                            format!("({sub}{downcast}).{field_name}")
                        }
                        FieldProjKind::Tuple(_) => {
                            format!("({sub}).{field_id}")
                        }
                        FieldProjKind::ClosureState => {
                            format!("({sub}).@closure_state_field_{field_id}")
                        }
                    },
                    ProjectionElem::Index {
                        offset,
                        from_end: true,
                        ..
                    } => format!("({sub})[-{}]", offset.fmt_with_ctx(ctx)),
                    ProjectionElem::Index {
                        offset,
                        from_end: false,
                        ..
                    } => format!("({sub})[{}]", offset.fmt_with_ctx(ctx)),
                    ProjectionElem::Subslice {
                        from,
                        to,
                        from_end: true,
                        ..
                    } => format!(
                        "({sub})[{}..-{}]",
                        from.fmt_with_ctx(ctx),
                        to.fmt_with_ctx(ctx)
                    ),
                    ProjectionElem::Subslice {
                        from,
                        to,
                        from_end: false,
                        ..
                    } => format!(
                        "({sub})[{}..{}]",
                        from.fmt_with_ctx(ctx),
                        to.fmt_with_ctx(ctx)
                    ),
                }
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for PolyTraitDeclRef {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        self.fmt_as_for(ctx)
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
                    Some(id) => format!("Some({id})"),
                    None => "None".to_string(),
                };
                let values: Vec<String> = values.iter().map(|v| v.fmt_with_ctx(ctx)).collect();
                format!("ConstAdt {} [{}]", variant_id, values.join(", "))
            }
            RawConstantExpr::Array(values) => {
                let values = values.iter().map(|v| v.fmt_with_ctx(ctx)).format(", ");
                format!("[{}]", values)
            }
            RawConstantExpr::Global(global_ref) => global_ref.fmt_with_ctx(ctx),
            RawConstantExpr::TraitConst(trait_ref, name) => {
                format!("{}::{name}", trait_ref.fmt_with_ctx(ctx),)
            }
            RawConstantExpr::Ref(cv) => {
                format!("&{}", cv.fmt_with_ctx(ctx))
            }
            RawConstantExpr::MutPtr(cv) => {
                format!("&raw mut {}", cv.fmt_with_ctx(ctx))
            }
            RawConstantExpr::Var(id) => format!("{}", ctx.format_object(*id)),
            RawConstantExpr::FnPtr(f) => {
                format!("{}", f.fmt_with_ctx(ctx))
            }
            RawConstantExpr::RawMemory(bytes) => format!("RawMemory({bytes:?})"),
            RawConstantExpr::Opaque(cause) => format!("Opaque({cause})"),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Region {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            Region::Static => "'static".to_string(),
            Region::Var(var) => ctx.format_object(*var),
            Region::Erased => "'_".to_string(),
        }
    }
}

impl Region {
    pub fn fmt_without_ctx(&self) -> String {
        match self {
            Region::Static => "'static".to_string(),
            Region::Var(var) => format!("'_{var}"),
            Region::Erased => "'_".to_string(),
        }
    }
}

impl<T> RegionBinder<T> {
    /// Format the parameters and contents of this binder and returns the resulting strings.
    fn fmt_split<'a, C>(&'a self, ctx: &'a C) -> (String, String)
    where
        C: AstFormatter,
        T: FmtWithCtx<<C as PushBinder<'a>>::C>,
    {
        let ctx = &ctx.push_bound_regions(&self.regions);
        (
            self.regions.iter().map(|r| ctx.format_object(r)).join(", "),
            self.skip_binder.fmt_with_ctx(ctx),
        )
    }

    /// Formats the binder as `for<params> value`.
    fn fmt_as_for<'a, C>(&'a self, ctx: &'a C) -> String
    where
        C: AstFormatter,
        T: FmtWithCtx<<C as PushBinder<'a>>::C>,
    {
        let (regions, value) = self.fmt_split(ctx);
        let regions = if regions.is_empty() {
            "".to_string()
        } else {
            format!("for<{regions}> ",)
        };
        format!("{regions}{value}",)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for RegionVar {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        ctx.format_object(self)
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Rvalue {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            Rvalue::Use(x) => x.fmt_with_ctx(ctx),
            Rvalue::Ref(place, borrow_kind) => {
                let borrow_kind = match borrow_kind {
                    BorrowKind::Shared => "&",
                    BorrowKind::Mut => "&mut ",
                    BorrowKind::TwoPhaseMut => "&two-phase-mut ",
                    BorrowKind::UniqueImmutable => "&uniq ",
                    BorrowKind::Shallow => "&shallow ",
                };
                format!("{borrow_kind}{}", place.fmt_with_ctx(ctx))
            }
            Rvalue::RawPtr(place, mutability) => {
                let ptr_kind = match mutability {
                    RefKind::Shared => "&raw const ",
                    RefKind::Mut => "&raw mut ",
                };
                format!("{ptr_kind}{}", place.fmt_with_ctx(ctx))
            }

            Rvalue::BinaryOp(binop, x, y) => {
                format!("{} {} {}", x.fmt_with_ctx(ctx), binop, y.fmt_with_ctx(ctx))
            }
            Rvalue::UnaryOp(unop, x) => {
                format!("{}({})", unop.fmt_with_ctx(ctx), x.fmt_with_ctx(ctx))
            }
            Rvalue::NullaryOp(op, ty) => {
                format!("{}<{}>", op.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
            }
            Rvalue::Discriminant(p, _) => {
                format!("@discriminant({})", p.fmt_with_ctx(ctx),)
            }
            Rvalue::Aggregate(kind, ops) => {
                let ops_s: Vec<String> = ops.iter().map(|op| op.fmt_with_ctx(ctx)).collect();
                match kind {
                    AggregateKind::Adt(def_id, variant_id, field_id, _) => {
                        match def_id {
                            TypeId::Tuple => format!("({})", ops_s.join(", ")),
                            TypeId::Builtin(_) => unreachable!(),
                            TypeId::Adt(def_id) => {
                                // Format every field
                                let mut fields = vec![];
                                for (i, op) in ops.iter().enumerate() {
                                    let field_id = match *field_id {
                                        None => FieldId::new(i),
                                        Some(field_id) => {
                                            assert_eq!(i, 0); // there should be only one operand
                                            field_id
                                        }
                                    };
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
                    AggregateKind::Array(..) => {
                        format!("[{}]", ops_s.join(", "))
                    }
                    AggregateKind::Closure(fn_id, generics) => {
                        format!(
                            "{{{}{}}} {{{}}}",
                            ctx.format_object(*fn_id),
                            generics.fmt_with_ctx(ctx),
                            ops_s.join(", ")
                        )
                    }
                    AggregateKind::RawPtr(_, rmut) => {
                        let mutability = match rmut {
                            RefKind::Shared => "const",
                            RefKind::Mut => "mut ",
                        };
                        format!("*{} ({})", mutability, ops_s.join(", "))
                    }
                }
            }
            Rvalue::Global(global_ref) => global_ref.fmt_with_ctx(ctx),
            Rvalue::GlobalRef(global_ref, RefKind::Shared) => {
                format!("&{}", global_ref.fmt_with_ctx(ctx))
            }
            Rvalue::GlobalRef(global_ref, RefKind::Mut) => {
                format!("&raw mut {}", global_ref.fmt_with_ctx(ctx))
            }
            Rvalue::Len(place, ..) => format!("len({})", place.fmt_with_ctx(ctx)),
            Rvalue::Repeat(op, _ty, cg) => {
                format!("[{}; {}]", op.fmt_with_ctx(ctx), cg.fmt_with_ctx(ctx))
            }
            Rvalue::ShallowInitBox(op, ty) => {
                format!(
                    "shallow_init_box::<{}>({})",
                    ty.fmt_with_ctx(ctx),
                    op.fmt_with_ctx(ctx)
                )
            }
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for ullbc::Statement {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // By default use a tab.
        self.fmt_with_ctx_and_indent(TAB_INCR, ctx)
    }

    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        use ullbc::RawStatement;
        let mut out = String::new();
        for line in &self.comments_before {
            let _ = writeln!(&mut out, "{tab}// {line}");
        }
        let _ = match &self.content {
            RawStatement::Assign(place, rvalue) => write!(
                &mut out,
                "{tab}{} := {}",
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            ),
            RawStatement::SetDiscriminant(place, variant_id) => write!(
                &mut out,
                "{tab}@discriminant({}) := {}",
                place.fmt_with_ctx(ctx),
                variant_id
            ),
            RawStatement::CopyNonOverlapping(box CopyNonOverlapping { src, dst, count }) => write!(
                &mut out,
                "{}copy_nonoverlapping({}, {}, {})",
                tab,
                src.fmt_with_ctx(ctx),
                dst.fmt_with_ctx(ctx),
                count.fmt_with_ctx(ctx),
            ),
            RawStatement::StorageLive(var_id) => {
                write!(
                    &mut out,
                    "{tab}storage_live({})",
                    ctx.format_object(*var_id)
                )
            }
            RawStatement::StorageDead(var_id) => {
                write!(
                    &mut out,
                    "{tab}storage_dead({})",
                    ctx.format_object(*var_id)
                )
            }
            RawStatement::Deinit(place) => {
                write!(&mut out, "{tab}deinit({})", place.fmt_with_ctx(ctx))
            }
            RawStatement::Drop(place) => {
                write!(&mut out, "{tab}drop {}", place.fmt_with_ctx(ctx))
            }
            RawStatement::Assert(assert) => write!(&mut out, "{tab}{}", assert.fmt_with_ctx(ctx)),
            RawStatement::Nop => write!(&mut out, "{tab}nop"),
            RawStatement::Error(s) => write!(&mut out, "{tab}@Error({})", s),
        };
        out
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for llbc::Statement {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // By default use a tab.
        self.fmt_with_ctx_and_indent(TAB_INCR, ctx)
    }

    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        use llbc::RawStatement;
        let mut out = String::new();
        for line in &self.comments_before {
            let _ = writeln!(&mut out, "{tab}// {line}");
        }
        let _ = match &self.content {
            RawStatement::Assign(place, rvalue) => write!(
                &mut out,
                "{}{} := {}",
                tab,
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            ),
            RawStatement::SetDiscriminant(place, variant_id) => write!(
                &mut out,
                "{}@discriminant({}) := {}",
                tab,
                place.fmt_with_ctx(ctx),
                variant_id
            ),
            RawStatement::CopyNonOverlapping(box CopyNonOverlapping { src, dst, count }) => write!(
                &mut out,
                "{}copy_nonoverlapping({}, {}, {})",
                tab,
                src.fmt_with_ctx(ctx),
                dst.fmt_with_ctx(ctx),
                count.fmt_with_ctx(ctx),
            ),
            RawStatement::StorageLive(var_id) => {
                write!(
                    &mut out,
                    "{tab}storage_live({})",
                    ctx.format_object(*var_id)
                )
            }
            RawStatement::StorageDead(var_id) => {
                write!(
                    &mut out,
                    "{tab}storage_dead({})",
                    ctx.format_object(*var_id)
                )
            }
            RawStatement::Deinit(place) => {
                write!(&mut out, "{tab}deinit({})", place.fmt_with_ctx(ctx))
            }
            RawStatement::Drop(place) => {
                write!(&mut out, "{tab}drop {}", place.fmt_with_ctx(ctx))
            }
            RawStatement::Assert(assert) => {
                write!(&mut out, "{tab}{}", assert.fmt_with_ctx(ctx),)
            }
            RawStatement::Call(call) => {
                let (call_s, _) = fmt_call(ctx, call);
                write!(&mut out, "{tab}{} := {call_s}", call.dest.fmt_with_ctx(ctx),)
            }
            RawStatement::Abort(kind) => {
                write!(&mut out, "{}", kind.fmt_with_ctx_and_indent(tab, ctx))
            }
            RawStatement::Return => write!(&mut out, "{tab}return"),
            RawStatement::Break(index) => write!(&mut out, "{tab}break {index}"),
            RawStatement::Continue(index) => write!(&mut out, "{tab}continue {index}"),
            RawStatement::Nop => write!(&mut out, "{tab}nop"),
            RawStatement::Switch(switch) => match switch {
                Switch::If(discr, true_st, false_st) => {
                    let inner_tab = format!("{tab}{TAB_INCR}");
                    write!(
                        &mut out,
                        "{tab}if {} {{\n{}{tab}}}\n{tab}else {{\n{}{tab}}}",
                        discr.fmt_with_ctx(ctx),
                        true_st.fmt_with_ctx_and_indent(&inner_tab, ctx),
                        false_st.fmt_with_ctx_and_indent(&inner_tab, ctx),
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
                                "{inner_tab1}{} => {{\n{}{inner_tab1}}},\n",
                                pvl.join(" | "),
                                st.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                            )
                        })
                        .collect();
                    maps.push(format!(
                        "{inner_tab1}_ => {{\n{}{inner_tab1}}},\n",
                        otherwise.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                    ));

                    write!(
                        &mut out,
                        "{tab}switch {} {{\n{}{tab}}}",
                        discr.fmt_with_ctx(ctx),
                        maps.iter().format(""),
                    )
                }
                Switch::Match(discr, maps, otherwise) => {
                    let inner_tab1 = format!("{tab}{TAB_INCR}");
                    let inner_tab2 = format!("{inner_tab1}{TAB_INCR}");
                    let discr_type: Option<TypeDeclId> = discr
                        .ty
                        .kind()
                        .as_adt()
                        .and_then(|(x, _)| x.as_adt())
                        .copied();
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(cases, st)| {
                            // Note that there may be several pattern values
                            let cases: Vec<String> = cases
                                .iter()
                                .map(|v| match discr_type {
                                    Some(type_id) => ctx.format_object((type_id, *v)),
                                    None => v.to_pretty_string(),
                                })
                                .collect();
                            format!(
                                "{inner_tab1}{} => {{\n{}{inner_tab1}}},\n",
                                cases.join(" | "),
                                st.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                            )
                        })
                        .collect();
                    if let Some(otherwise) = otherwise {
                        maps.push(format!(
                            "{inner_tab1}_ => {{\n{}{inner_tab1}}},\n",
                            otherwise.fmt_with_ctx_and_indent(&inner_tab2, ctx),
                        ));
                    };

                    write!(
                        &mut out,
                        "{tab}match {} {{\n{}{tab}}}",
                        discr.fmt_with_ctx(ctx),
                        maps.iter().format(""),
                    )
                }
            },
            RawStatement::Loop(body) => {
                let inner_tab = format!("{tab}{TAB_INCR}");
                write!(
                    &mut out,
                    "{tab}loop {{\n{}{tab}}}",
                    body.fmt_with_ctx_and_indent(&inner_tab, ctx),
                )
            }
            RawStatement::Error(s) => write!(&mut out, "{tab}@ERROR({})", s),
        };
        out
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for Terminator {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        // By default use a tab.
        self.fmt_with_ctx_and_indent(TAB_INCR, ctx)
    }

    fn fmt_with_ctx_and_indent(&self, tab: &str, ctx: &C) -> String {
        let mut out = String::new();
        for line in &self.comments_before {
            let _ = writeln!(&mut out, "{tab}// {line}");
        }
        let _ = match &self.content {
            RawTerminator::Goto { target } => write!(&mut out, "{tab}goto bb{target}"),
            RawTerminator::Switch { discr, targets } => match targets {
                SwitchTargets::If(true_block, false_block) => write!(
                    &mut out,
                    "{tab}if {} -> bb{} else -> bb{}",
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

                    write!(
                        &mut out,
                        "{tab}switch {} -> {}",
                        discr.fmt_with_ctx(ctx),
                        maps
                    )
                }
            },
            RawTerminator::Call {
                call,
                target,
                on_unwind,
            } => {
                let (call_s, _) = fmt_call(ctx, call);
                write!(
                    &mut out,
                    "{tab}{} := {call_s} -> bb{target} (unwind: bb{on_unwind})",
                    call.dest.fmt_with_ctx(ctx)
                )
            }
            RawTerminator::Abort(kind) => write!(&mut out, "{tab}{}", kind.fmt_with_ctx(ctx)),
            RawTerminator::Return => write!(&mut out, "{tab}return"),
            RawTerminator::UnwindResume => write!(&mut out, "{tab}unwind_continue"),
        };
        out
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitClause {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let clause_id = self.clause_id.to_pretty_string();
        let trait_ = self.trait_.fmt_with_ctx(ctx);
        format!("[{clause_id}]: {trait_}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitDecl {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let intro = self.item_meta.fmt_item_intro(ctx, "", "trait");

        // Update the context
        let ctx = &ctx.set_generics(&self.generics);

        let (generics, clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx, "");

        let items = {
            let items = self
                .parent_clauses
                .iter()
                .map(|c| {
                    format!(
                        "{TAB_INCR}parent_clause{} : {}\n",
                        c.clause_id,
                        c.fmt_with_ctx(ctx)
                    )
                })
                .chain(self.type_clauses.iter().map(|(name, clauses)| {
                    clauses
                        .iter()
                        .map(|c| {
                            format!(
                                "{TAB_INCR}item_clause_{name}_{} : {}\n",
                                c.clause_id.to_string(),
                                c.fmt_with_ctx(ctx)
                            )
                        })
                        .collect()
                }))
                .chain(self.consts.iter().map(|(name, ty)| {
                    let ty = ty.fmt_with_ctx(ctx);
                    format!("{TAB_INCR}const {name} : {ty}\n")
                }))
                .chain(
                    self.types
                        .iter()
                        .map(|name| format!("{TAB_INCR}type {name}\n")),
                )
                .chain(self.methods().map(|(name, bound_fn)| {
                    let (params, fn_ref) = bound_fn.fmt_split(ctx);
                    format!("{TAB_INCR}fn {name}{params} = {fn_ref}\n",)
                }))
                .collect::<Vec<String>>();
            if items.is_empty() {
                "".to_string()
            } else {
                format!("\n{{\n{}}}", items.join(""))
            }
        };

        format!("{intro}{generics}{clauses}{items}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitDeclRef {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let trait_id = ctx.format_object(self.trait_id);
        let generics = self.generics.fmt_with_ctx(ctx);
        format!("{trait_id}{generics}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitImpl {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let intro = self.item_meta.fmt_item_intro(ctx, "", "impl");

        // Update the context
        let ctx = &ctx.set_generics(&self.generics);

        let (generics, clauses) = self.generics.fmt_with_ctx_with_trait_clauses(ctx, "");

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
                .chain(self.type_clauses.iter().map(|(name, clauses)| {
                    clauses
                        .iter()
                        .enumerate()
                        .map(|(i, c)| {
                            let i = TraitClauseId::new(i);
                            format!(
                                "{TAB_INCR}item_clause_{name}_{i} = {}\n",
                                c.fmt_with_ctx(ctx)
                            )
                        })
                        .collect()
                }))
                .chain(self.consts.iter().map(|(name, global)| {
                    format!("{TAB_INCR}const {name} = {}\n", global.fmt_with_ctx(ctx))
                }))
                .chain(self.types.iter().map(|(name, ty)| {
                    format!("{TAB_INCR}type {name} = {}\n", ty.fmt_with_ctx(ctx),)
                }))
                .chain(self.methods().map(|(name, bound_fn)| {
                    let (params, fn_ref) = bound_fn.fmt_split(ctx);
                    format!("{TAB_INCR}fn {name}{params} = {fn_ref}\n",)
                }))
                .collect::<Vec<String>>();
            if items.is_empty() {
                "".to_string()
            } else {
                format!("\n{{\n{}}}", items.join(""))
            }
        };

        let impl_trait = self.impl_trait.fmt_with_ctx(ctx);
        format!("{intro}{generics} : {impl_trait}{clauses}{items}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitRefKind {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            TraitRefKind::SelfId => "Self".to_string(),
            TraitRefKind::ParentClause(id, _decl_id, clause_id) => {
                let id = id.fmt_with_ctx(ctx);
                format!("{id}::parent_clause{clause_id}")
            }
            TraitRefKind::ItemClause(id, _decl_id, type_name, clause_id) => {
                let id = id.fmt_with_ctx(ctx);
                // Using on purpose [to_pretty_string] instead of [format_object]:
                // the clause is local to the associated type, so it should not
                // be referenced in the current context.
                let clause = clause_id.to_pretty_string();
                format!("({id}::{type_name}::[{clause}])")
            }
            TraitRefKind::TraitImpl(id, args) => {
                let impl_ = ctx.format_object(*id);
                let args = args.fmt_with_ctx(ctx);
                format!("{impl_}{args}")
            }
            TraitRefKind::Clause(id) => ctx.format_object(*id),
            TraitRefKind::BuiltinOrAuto {
                trait_decl_ref: tr,
                types,
                ..
            } => {
                let tr = tr.fmt_with_ctx(ctx);
                let types = if types.is_empty() {
                    String::new()
                } else {
                    let types = types
                        .iter()
                        .map(|(name, ty)| {
                            let ty = ty.fmt_with_ctx(ctx);
                            format!("{name}  = {ty}")
                        })
                        .join(", ");
                    format!(" where {types}")
                };
                format!("{tr}{types}")
            }
            TraitRefKind::Dyn(tr) => tr.fmt_with_ctx(ctx),
            TraitRefKind::Unknown(msg) => format!("UNKNOWN({msg})"),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TraitRef {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        self.kind.fmt_with_ctx(ctx)
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
        match self.kind() {
            TyKind::Adt(id, generics) => {
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
            TyKind::Closure { fun_id, .. } => ctx.format_object(*fun_id),
            TyKind::TypeVar(id) => ctx.format_object(*id),
            TyKind::Literal(kind) => kind.to_string(),
            TyKind::Never => "!".to_string(),
            TyKind::Ref(r, ty, kind) => match kind {
                RefKind::Mut => {
                    format!("&{} mut ({})", r.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
                }
                RefKind::Shared => {
                    format!("&{} ({})", r.fmt_with_ctx(ctx), ty.fmt_with_ctx(ctx))
                }
            },
            TyKind::RawPtr(ty, kind) => match kind {
                RefKind::Shared => format!("*const {}", ty.fmt_with_ctx(ctx)),
                RefKind::Mut => format!("*mut {}", ty.fmt_with_ctx(ctx)),
            },
            TyKind::TraitType(trait_ref, name) => {
                format!("{}::{name}", trait_ref.fmt_with_ctx(ctx),)
            }
            TyKind::DynTrait(pred) => format!("dyn ({})", pred.with_ctx(ctx)),
            TyKind::Arrow(io) => {
                // Update the bound regions
                let ctx = &ctx.push_bound_regions(&io.regions);

                let regions = if io.regions.is_empty() {
                    "".to_string()
                } else {
                    format!(
                        "<{}>",
                        io.regions.iter().map(|r| ctx.format_object(r)).join(", ")
                    )
                };
                let (inputs, output) = &io.skip_binder;
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
            TyKind::Error(msg) => format!("type_error(\"{msg}\")"),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TypeDecl {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        let keyword = match &self.kind {
            TypeDeclKind::Struct(..) => "struct",
            TypeDeclKind::Union(..) => "union",
            TypeDeclKind::Enum(..) => "enum",
            TypeDeclKind::Alias(..) => "type",
            TypeDeclKind::Opaque | TypeDeclKind::Error(..) => "opaque type",
        };
        let intro = self.item_meta.fmt_item_intro(ctx, "", keyword);

        let ctx = &ctx.set_generics(&self.generics);
        let (params, preds) = self.generics.fmt_with_ctx_with_trait_clauses(ctx, "  ");
        // Predicates
        let nl_or_space = if !self.generics.has_predicates() {
            " ".to_string()
        } else {
            "\n ".to_string()
        };

        let contents = match &self.kind {
            TypeDeclKind::Struct(fields) => {
                if !fields.is_empty() {
                    let fields = fields
                        .iter()
                        .map(|f| format!("\n  {},", f.fmt_with_ctx(ctx)))
                        .format("");
                    format!("{nl_or_space}=\n{{{fields}\n}}")
                } else {
                    format!("{nl_or_space}= {{}}")
                }
            }
            TypeDeclKind::Union(fields) => {
                let fields = fields
                    .iter()
                    .map(|f| format!("\n  {},", f.fmt_with_ctx(ctx)))
                    .format("");
                format!("{nl_or_space}=\n{{{fields}\n}}")
            }
            TypeDeclKind::Enum(variants) => {
                let variants = variants
                    .iter()
                    .map(|v| format!("|  {}", v.fmt_with_ctx(ctx)))
                    .format("\n");
                format!("{nl_or_space}=\n{variants}\n")
            }
            TypeDeclKind::Alias(ty) => format!(" = {}", ty.fmt_with_ctx(ctx)),
            TypeDeclKind::Opaque => format!(""),
            TypeDeclKind::Error(msg) => format!(" = ERROR({msg})"),
        };
        format!("{intro}{params}{preds}{contents}")
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TypeId {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            TypeId::Tuple => "".to_string(),
            TypeId::Adt(def_id) => ctx.format_object(*def_id),
            TypeId::Builtin(aty) => aty.get_name().fmt_with_ctx(ctx),
        }
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for TypeVar {
    fn fmt_with_ctx(&self, _ctx: &C) -> String {
        self.name.to_string()
    }
}

impl<C: AstFormatter> FmtWithCtx<C> for UnOp {
    fn fmt_with_ctx(&self, ctx: &C) -> String {
        match self {
            UnOp::Not => "~".to_string(),
            UnOp::Neg => "-".to_string(),
            UnOp::PtrMetadata => "ptr_metadata".to_string(),
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

impl std::fmt::Display for AnyTransId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        let s = match self {
            AnyTransId::Type(x) => x.to_pretty_string(),
            AnyTransId::Fun(x) => x.to_pretty_string(),
            AnyTransId::Global(x) => x.to_pretty_string(),
            AnyTransId::TraitDecl(x) => x.to_pretty_string(),
            AnyTransId::TraitImpl(x) => x.to_pretty_string(),
        };
        f.write_str(&s)
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
            BinOp::WrappingAdd => write!(f, "wrapping.+"),
            BinOp::WrappingSub => write!(f, "wrapping.-"),
            BinOp::WrappingMul => write!(f, "wrapping.*"),
            BinOp::CheckedAdd => write!(f, "checked.+"),
            BinOp::CheckedSub => write!(f, "checked.-"),
            BinOp::CheckedMul => write!(f, "checked.*"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Shr => write!(f, ">>"),
            BinOp::Cmp => write!(f, "cmp"),
            BinOp::Offset => write!(f, "offset"),
        }
    }
}

impl std::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        // Reuse the derived `Debug` impl to get the variant name.
        write!(f, "{self:?}")
    }
}

impl std::fmt::Display for BuiltinFunId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        let name = match *self {
            BuiltinFunId::BoxNew => "BoxNew",
            BuiltinFunId::ArrayToSliceShared => "ArrayToSliceShared",
            BuiltinFunId::ArrayToSliceMut => "ArrayToSliceMut",
            BuiltinFunId::ArrayRepeat => "ArrayRepeat",
            BuiltinFunId::Index(BuiltinIndexOp {
                is_array,
                mutability,
                is_range,
            }) => {
                let ty = if is_array { "Array" } else { "Slice" };
                let op = if is_range { "SubSlice" } else { "Index" };
                let mutability = mutability.variant_name();
                &format!("{ty}{op}{mutability}")
            }
            BuiltinFunId::PtrFromParts(mutability) => {
                let mutability = mutability.variant_name();
                &format!("PtrFromParts{mutability}")
            }
        };
        f.write_str(name)
    }
}

impl std::fmt::Display for DeBruijnId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.index)
    }
}

impl<Id> Display for DeBruijnVar<Id>
where
    Id: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bound(dbid, varid) => write!(f, "{dbid}_{varid}"),
            Self::Free(varid) => write!(f, "{varid}"),
        }
    }
}

impl std::fmt::Display for ConstantExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx(&FmtCtx::new()))
    }
}

impl std::fmt::Display for FileName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            FileName::Virtual(path_buf) | FileName::Local(path_buf) => {
                write!(f, "{}", path_buf.display())
            }
            FileName::NotReal(name) => write!(f, "{}", name),
        }
    }
}

impl std::fmt::Display for FloatTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            FloatTy::F16 => write!(f, "f16"),
            FloatTy::F32 => write!(f, "f32"),
            FloatTy::F64 => write!(f, "f64"),
            FloatTy::F128 => write!(f, "f128"),
        }
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

impl std::fmt::Display for GenericParams {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.fmt_with_ctx_single_line(&FmtCtx::new()))
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Literal::Scalar(v) => write!(f, "{v}"),
            Literal::Float(v) => write!(f, "{v}"),
            Literal::Bool(v) => write!(f, "{v}"),
            Literal::Char(v) => write!(f, "{v}"),
            Literal::Str(v) => write!(f, "\"{}\"", v.replace("\\", "\\\\").replace("\n", "\\n")),
            Literal::ByteStr(v) => write!(f, "{v:?}"),
        }
    }
}

impl std::fmt::Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl std::fmt::Display for RawAttribute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.path)?;
        if let Some(args) = &self.args {
            write!(f, "({args})")?;
        }
        Ok(())
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

impl std::fmt::Display for FloatValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        let v = &self.value;
        match self.ty {
            FloatTy::F16 => write!(f, "{v} : f16"),
            FloatTy::F32 => write!(f, "{v} : f32"),
            FloatTy::F64 => write!(f, "{v} : f64"),
            FloatTy::F128 => write!(f, "{v} : f128"),
        }
    }
}

impl std::fmt::Display for TraitItemName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl std::string::ToString for Local {
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

macro_rules! impl_display_via_ctx {
    ($ty:ty) => {
        impl Display for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.fmt_with_ctx(&FmtCtx::new()))
            }
        }
    };
}
macro_rules! impl_debug_via_display {
    ($ty:ty) => {
        impl Debug for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <_ as Display>::fmt(self, f)
            }
        }
    };
}

impl_display_via_ctx!(Field);
impl_display_via_ctx!(GenericArgs);
impl_display_via_ctx!(LiteralTy);
impl_display_via_ctx!(Operand);
impl_display_via_ctx!(Place);
impl_display_via_ctx!(Rvalue);
impl_display_via_ctx!(Variant);
impl_debug_via_display!(GenericArgs);
impl_debug_via_display!(GenericParams);

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
