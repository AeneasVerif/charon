//! Our Internal MIR ast (IM), intended to be close to the rust compiler MIR ast.
//! We don't even try to reconstruct the if then else blocks or the loop blocks
//! at this point.
#![allow(dead_code)]

use crate::expressions::*;
use crate::formatter::Formatter;
use crate::types::*;
use crate::values::*;
use crate::vars::Name;
use hashlink::linked_hash_map::LinkedHashMap;
use macros::generate_index_type;
use macros::{EnumAsGetters, EnumIsA, VariantName};

// TODO: move this definition
pub static TAB: &'static str = "    ";

// Block identifier. Similar to rust's `BasicBlock`.
generate_index_type!(BlockId);

pub static START_BLOCK_ID: BlockId::Id = BlockId::ZERO;

/// A function signature.
/// Note that a signature uses unerased lifetimes, while function bodies (and
/// execution) use erased lifetimes.
/// We need the functions' signatures *with* the region parameters in order
/// to correctly abstract those functions (number and signature of the backward
/// functions) - we only use regions for this purpose.
/// TODO: still unsure about where we should put the region and type parameters.
/// In the FunSig or in the FunDecl? And should we have an FunSig data structure
/// at all actually?
#[derive(Debug, Clone)]
pub struct FunSig {
    pub region_params: RegionVarId::Vector<RegionVar>,
    /// The region parameters contain early bound and late bound parameters.
    /// The early bound regions are those introduced by the `impl` block (if
    /// this definition  is defined in an `impl` block), the late bound regions
    /// are those introduced by the function itself.
    ///  For example, in:
    ///  ```
    ///  impl<'a> Foo<'a> {
    ///      fn bar<'b>(...) -> ... { ... }
    ///  }
    /// `'a` is early-bound while `'b` is late-bound.
    ///  ```
    pub num_early_bound_regions: usize,
    pub type_params: TypeVarId::Vector<TypeVar>,
    pub inputs: VarId::Vector<SigTy>,
    pub output: SigTy,
}

/// A function declaration
#[derive(Debug, Clone)]
pub struct FunDecl {
    pub def_id: DefId::Id,
    pub name: Name,
    /// The signature contains the inputs/output types *with* non-erased regions.
    /// It also contains the list of region and type parameters.
    pub signature: FunSig,
    /// true if the function might diverge (is recursive, part of a mutually
    /// recursive group, contains loops or calls functions which might diverge)
    pub divergent: bool,
    pub body: Body,
}

/// A function body.
/// We have a separate type definition for this (and don't merge it in
/// [`FunDecl`](FunDecl) to be able to perform type substitutions to
/// get instantiated bodies when executing code.
/// TODO: this is not necessary anymore, we don't execute code
#[derive(Debug, Clone)]
pub struct Body {
    pub arg_count: usize,
    pub locals: VarId::Vector<Var>,
    pub blocks: BlockId::Vector<BlockData>,
}

pub type FunDecls = DefId::Vector<FunDecl>;

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName)]
pub enum Statement {
    Assign(Place, Rvalue),
    FakeRead(Place),
    SetDiscriminant(Place, VariantId::Id),
    StorageDead(VarId::Id),
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, VariantName)]
pub enum SwitchTargets {
    /// Gives the `if` block and the `else` block
    If(BlockId::Id, BlockId::Id),
    /// Gives the integer type, a map linking values to switch branches, and the
    /// otherwise block. Note that matches over enumerations are performed by
    /// switching over the discriminant, which is an integer.
    /// Also, we use a `LinkedHashMap` to make sure the order of the switch
    /// branches is preserved.
    SwitchInt(
        IntegerTy,
        LinkedHashMap<ScalarValue, BlockId::Id>,
        BlockId::Id,
    ),
}

/// A function identifier. See [`Terminator`](Terminator)
#[derive(Debug, Clone, Copy, EnumIsA, EnumAsGetters, VariantName)]
pub enum FunId {
    /// A function local to the crate, whose body we will translate.
    Local(DefId::Id),
    /// An assumed function, coming from a standard library (for instance:
    /// `alloc::boxed::Box::new`).
    Assumed(AssumedFunId),
}

/// An assumed function identifier, identifying a function coming from a
/// standard library.
#[derive(Debug, Clone, Copy, EnumIsA, EnumAsGetters)]
pub enum AssumedFunId {
    /// `alloc::boxed::Box::new`
    BoxNew,
    /// `core::ops::deref::Deref::<alloc::boxed::Box::>::deref`
    BoxDeref,
    /// `core::ops::deref::DerefMut::<alloc::boxed::Box::>::deref_mut`
    BoxDerefMut,
    /// `alloc::alloc::box_free`
    /// This is actually an unsafe function, but the rust compiler sometimes
    /// introduces it when going to MIR. We add it only to track it: in practice,
    /// it is only implemented with a drop.
    BoxFree,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters)]
pub enum Terminator {
    Goto {
        target: BlockId::Id,
    },
    Switch {
        discr: Operand,
        targets: SwitchTargets,
    },
    Panic,
    Return,
    Unreachable,
    Drop {
        place: Place,
        target: BlockId::Id,
    },
    /// Function call.
    /// For now, we only accept calls to top-level functions.
    Call {
        func: FunId,
        /// Technically, this is useless, but we still keep it because we might
        /// want to introduce some information (and the way we encode from MIR
        /// is as simple as possible - and in MIR we also have a vector of erased
        /// regions).
        region_params: Vec<ErasedRegion>,
        type_params: Vec<ETy>,
        args: Vec<Operand>,
        dest: Place,
        target: BlockId::Id,
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: BlockId::Id,
    },
}

#[derive(Debug, Clone)]
pub struct BlockData {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

impl Statement {
    /// Substitute the type variables and return the resulting statement.
    /// Actually simply clones the statement, while performing sanity checks (a
    /// statement shouldn't contain references to type variables anywhere).
    pub fn substitute(&self, _subst: &ETypeSubst) -> Statement {
        match self {
            Statement::Assign(place, rvalue) => {
                assert!(rvalue.contains_no_variables());
                Statement::Assign(place.clone(), rvalue.clone())
            }
            Statement::FakeRead(place) => Statement::FakeRead(place.clone()),
            Statement::SetDiscriminant(place, variant_id) => {
                Statement::SetDiscriminant(place.clone(), *variant_id)
            }
            Statement::StorageDead(var_id) => Statement::StorageDead(*var_id),
        }
    }
}

impl Terminator {
    /// Substitute the type variables and return the resulting terminator
    pub fn substitute(&self, subst: &ETypeSubst) -> Terminator {
        match self {
            Terminator::Goto { target } => Terminator::Goto { target: *target },
            Terminator::Switch { discr, targets } => {
                assert!(discr.contains_no_variables());
                Terminator::Switch {
                    discr: discr.clone(),
                    targets: targets.clone(),
                }
            }
            Terminator::Panic => Terminator::Panic,
            Terminator::Return => Terminator::Return,
            Terminator::Unreachable => Terminator::Unreachable,
            Terminator::Drop { place, target } => Terminator::Drop {
                place: place.clone(),
                target: *target,
            },
            Terminator::Call {
                func,
                region_params,
                type_params,
                args,
                dest,
                target,
            } => {
                assert!(args.iter().all(|x| x.contains_no_variables()));
                Terminator::Call {
                    func: func.clone(),
                    region_params: region_params.clone(),
                    type_params: type_params
                        .iter()
                        .map(|ty| ty.substitute_types(subst))
                        .collect(),
                    args: args.clone(),
                    dest: dest.clone(),
                    target: *target,
                }
            }
            Terminator::Assert {
                cond,
                expected,
                target,
            } => {
                assert!(cond.contains_no_variables());
                Terminator::Assert {
                    cond: cond.clone(),
                    expected: *expected,
                    target: *target,
                }
            }
        }
    }
}

impl BlockData {
    /// Substitute the type variables and return the resulting `BlockData`
    pub fn substitute(&self, subst: &ETypeSubst) -> BlockData {
        let statements = self
            .statements
            .iter()
            .map(|x| x.substitute(subst))
            .collect();
        let terminator = self.terminator.substitute(subst);
        BlockData {
            statements,
            terminator,
        }
    }
}

impl Body {
    /// Substitute the type variables and return the resulting `Body`
    pub fn substitute(&self, subst: &ETypeSubst) -> Body {
        use std::iter::FromIterator;
        let locals = self.locals.iter().map(|var| var.substitute(subst));
        let locals = VarId::Vector::from_iter(locals);
        let blocks = self.blocks.iter().map(|block| block.substitute(subst));
        let blocks = BlockId::Vector::from_iter(blocks);

        Body {
            arg_count: self.arg_count,
            locals,
            blocks,
        }
    }
}

impl FunDecl {
    /// Substitute the type variables in the function's body and return the resulting
    /// `Body`
    pub fn substitute_in_body(&self, subst: &ETypeSubst) -> Body {
        self.body.substitute(subst)
    }

    pub fn apply_instantiation_in_body(&self, type_params: &Vec<ETy>) -> Body {
        let type_vars = self.signature.type_params.iter().map(|x| x.index);
        let subst = make_type_subst(type_vars, type_params.iter());
        self.body.substitute(&subst)
    }
}

impl Statement {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            //            + Formatter<ValueId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Statement::Assign(place, rvalue) => format!(
                "{} := {}",
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            )
            .to_owned(),
            Statement::FakeRead(place) => {
                format!("@fake_read({})", place.fmt_with_ctx(ctx),).to_owned()
            }
            Statement::SetDiscriminant(place, variant_id) => format!(
                "@discriminant({}) := {}",
                place.fmt_with_ctx(ctx),
                variant_id.to_string()
            )
            .to_owned(),
            Statement::StorageDead(vid) => {
                format!("@storage_dead({})", var_id_to_pretty_string(*vid)).to_owned()
            }
        }
    }
}

impl<'ctx> Formatter<&Statement> for AstFormatter<'ctx> {
    fn format_object(&self, statement: &Statement) -> String {
        statement.fmt_with_ctx(self)
    }
}

impl Terminator {
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            //            + Formatter<ValueId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<DefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>,
    {
        match self {
            Terminator::Goto { target } => format!("goto bb{}", target.to_string()).to_owned(),
            Terminator::Switch { discr, targets } => match targets {
                SwitchTargets::If(true_block, false_block) => format!(
                    "if {} -> bb{} else -> bb{}",
                    discr.fmt_with_ctx(ctx),
                    true_block.to_string(),
                    false_block.to_string()
                )
                .to_owned(),
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(v, bid)| {
                            format!("{}: bb{}", v.to_string(), bid.to_string()).to_owned()
                        })
                        .collect();
                    maps.push(format!("otherwise: bb{}", otherwise.to_string()).to_owned());
                    let maps = maps.join(", ");

                    format!("switch {} -> {}", discr.fmt_with_ctx(ctx), maps).to_owned()
                }
            },
            Terminator::Panic => "panic".to_owned(),
            Terminator::Return => "return".to_owned(),
            Terminator::Unreachable => "unreachable".to_owned(),
            Terminator::Drop { place, target } => format!(
                "drop {} -> bb{}",
                place.fmt_with_ctx(ctx),
                target.to_string()
            )
            .to_owned(),
            Terminator::Call {
                func,
                region_params,
                type_params,
                args,
                dest,
                target,
            } => {
                let params = if region_params.len() + type_params.len() == 0 {
                    "".to_owned()
                } else {
                    let regions_s: Vec<String> =
                        region_params.iter().map(|x| x.to_string()).collect();
                    let mut types_s: Vec<String> =
                        type_params.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
                    let mut s = regions_s;
                    s.append(&mut types_s);
                    format!("<{}>", s.join(", ")).to_owned()
                };
                let args: Vec<String> = args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
                let args = args.join(", ");

                let f = match func {
                    FunId::Local(def_id) => {
                        format!("{}{}", ctx.format_object(*def_id), params).to_owned()
                    }
                    FunId::Assumed(assumed) => match assumed {
                        AssumedFunId::BoxNew => {
                            format!("alloc::boxed::Box{}::new", params).to_owned()
                        }
                        AssumedFunId::BoxDeref => {
                            format!("core::ops::deref::Deref<Box{}>::deref", params).to_owned()
                        }
                        AssumedFunId::BoxDerefMut => {
                            format!("core::ops::deref::DerefMut<Box{}>::deref_mut", params)
                                .to_owned()
                        }
                        AssumedFunId::BoxFree => {
                            format!("alloc::alloc::box_free<{}>", params).to_owned()
                        }
                    },
                };

                format!(
                    "{} := {}({}) -> bb{}",
                    dest.fmt_with_ctx(ctx),
                    f,
                    args,
                    target.to_string(),
                )
                .to_owned()
            }
            Terminator::Assert {
                cond,
                expected,
                target,
            } => format!(
                "assert({} == {}) -> bb{}",
                cond.fmt_with_ctx(ctx),
                expected,
                target.to_string()
            )
            .to_owned(),
        }
    }
}

impl BlockData {
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDefId::Id>
            + Formatter<DefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        let mut out: Vec<String> = Vec::new();

        // Format the statements
        for statement in &self.statements {
            out.push(format!("{}{};\n", tab, statement.fmt_with_ctx(ctx)).to_owned());
        }

        // Format the terminator
        out.push(format!("{}{};", tab, self.terminator.fmt_with_ctx(ctx)).to_owned());

        // Join the strings
        out.join("")
    }
}

impl Body {
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            //            + Formatter<ValueId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<DefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        // Format the local variables
        let mut locals: Vec<String> = Vec::new();
        for v in &self.locals {
            use crate::id_vector::ToUsize;
            let index = v.index.to_usize();
            let comment = if index == 0 {
                "// return".to_owned()
            } else {
                if index <= self.arg_count {
                    format!("// arg #{}", index).to_owned()
                } else {
                    match &v.name {
                        Some(_) => "// local".to_owned(),
                        None => "// anonymous local".to_owned(),
                    }
                }
            };

            let var_name = match &v.name {
                Some(name) => name.clone(),
                None => var_id_to_pretty_string(v.index),
            };

            locals.push(
                format!(
                    "{}let {}: {}; {}\n",
                    tab,
                    var_name,
                    v.ty.fmt_with_ctx(ctx),
                    comment
                )
                .to_owned(),
            );
        }

        let mut locals = locals.join("");
        locals.push_str("\n");

        // Format the blocks
        let block_tab = format!("{}{}", tab, TAB);
        let mut blocks: Vec<String> = Vec::new();
        for (bid, block) in self.blocks.iter_indexed_values() {
            use crate::id_vector::ToUsize;
            blocks.push(
                format!(
                    "{}bb{}: {{\n{}\n{}}}\n",
                    tab,
                    bid.to_usize(),
                    block.fmt_with_ctx(&block_tab, ctx),
                    tab
                )
                .to_owned(),
            );
        }
        let blocks = blocks.join("\n");

        // Put everything together
        let mut out = locals;
        out.push_str(&blocks);
        out
    }
}

impl FunSig {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>,
    {
        // Type parameters
        let params = if self.region_params.len() + self.type_params.len() == 0 {
            "".to_owned()
        } else {
            let regions: Vec<String> = self.region_params.iter().map(|x| x.to_string()).collect();
            let mut types: Vec<String> = self.type_params.iter().map(|x| x.to_string()).collect();
            let mut params = regions;
            params.append(&mut types);
            format!("<{}>", params.join(", ")).to_owned()
        };

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for ty in &self.inputs {
            args.push(format!("{}", ty.fmt_with_ctx(ctx)).to_owned());
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_owned()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx)).to_owned()
        };

        // Put everything together
        format!("fn{}({}){}", params, args, ret_ty).to_owned()
    }
}

pub struct FunSigFormatter<'a> {
    pub ty_ctx: &'a TypeDecls,
    pub sig: &'a FunSig,
}

impl<'a> Formatter<TypeVarId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.sig.type_params.get(id).unwrap().to_string()
    }
}

impl<'a> Formatter<RegionVarId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        self.sig.region_params.get(id).unwrap().to_string()
    }
}

impl<'a> Formatter<&Region<RegionVarId::Id>> for FunSigFormatter<'a> {
    fn format_object(&self, r: &Region<RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<TypeDefId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: TypeDefId::Id) -> String {
        self.ty_ctx.format_object(id)
    }
}

impl FunSig {
    pub fn fmt_with_decls<'ctx>(&self, ty_ctx: &'ctx TypeDecls) -> String {
        // Initialize the formatting context
        let ctx = FunSigFormatter { ty_ctx, sig: self };

        // Use the context for printing
        self.fmt_with_ctx(&ctx)
    }
}

impl FunDecl {
    /// This is an auxiliary function for printing declarations. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function declaration already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// declaration). See [`fmt_with_decls`](FunDecl::fmt_with_decls).
    pub fn fmt_with_ctx<'a, 'b, 'c, T1, T2>(
        &'a self,
        tab: &'b str,
        sig_ctx: &'c T1,
        body_ctx: &'c T2,
    ) -> String
    where
        T1: Formatter<TypeVarId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>,
        T2: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            //            + Formatter<ValueId::Id>
            + Formatter<TypeDefId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<DefId::Id>
            + Formatter<(TypeDefId::Id, VariantId::Id)>
            + Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        // Function name
        let name = self.name.to_string();

        // Type parameters
        let params = if self.signature.region_params.len() + self.signature.type_params.len() == 0 {
            "".to_owned()
        } else {
            let regions: Vec<String> = self
                .signature
                .region_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut types: Vec<String> = self
                .signature
                .type_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut params = regions;
            params.append(&mut types);
            format!("<{}>", params.join(", ")).to_owned()
        };

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for i in 1..self.body.arg_count {
            let id = VarId::Id::new(i);
            let arg_ty = &self.signature.inputs.get(id).unwrap();
            args.push(
                format!(
                    "{}: {}",
                    var_id_to_pretty_string(id),
                    arg_ty.fmt_with_ctx(sig_ctx)
                )
                .to_owned(),
            );
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.signature.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_owned()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(sig_ctx)).to_owned()
        };

        // Body
        let body_tab = format!("{}{}", tab, TAB);
        let body = self.body.fmt_with_ctx(&body_tab, body_ctx);

        // Put everything together
        format!(
            "{}fn {}{}({}){} {{\n{}\n{}}}",
            tab, name, params, args, ret_ty, body, tab
        )
        .to_owned()
    }
}

impl<'ctx> Formatter<DefId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: DefId::Id) -> String {
        let f = self.fun_context.get(id).unwrap();
        f.name.to_string()
    }
}

impl<'ctx> Formatter<&Terminator> for AstFormatter<'ctx> {
    fn format_object(&self, terminator: &Terminator) -> String {
        terminator.fmt_with_ctx(self)
    }
}

struct AstFormatter<'ctx> {
    pub type_context: &'ctx TypeDecls,
    pub fun_context: &'ctx FunDecls,
    pub type_vars: &'ctx TypeVarId::Vector<TypeVar>,
    pub vars: &'ctx VarId::Vector<Var>,
}

impl<'ctx> AstFormatter<'ctx> {
    pub fn new(
        type_context: &'ctx TypeDecls,
        fun_context: &'ctx FunDecls,
        type_vars: &'ctx TypeVarId::Vector<TypeVar>,
        vars: &'ctx VarId::Vector<Var>,
    ) -> Self {
        AstFormatter {
            type_context,
            fun_context,
            type_vars,
            vars,
        }
    }
}

impl<'ctx> Formatter<VarId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: VarId::Id) -> String {
        let v = self.vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'ctx> Formatter<TypeVarId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.type_vars.get(id).unwrap().to_string()
    }
}

/// For adt types
impl<'ctx> Formatter<TypeDefId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: TypeDefId::Id) -> String {
        self.type_context.format_object(id)
    }
}

/// For enum values: `List::Cons`
impl<'ctx> Formatter<(TypeDefId::Id, VariantId::Id)> for AstFormatter<'ctx> {
    fn format_object(&self, id: (TypeDefId::Id, VariantId::Id)) -> String {
        let (def_id, variant_id) = id;
        let ctx = self.type_context;
        let gen_decl = ctx.get_type_decl(def_id).unwrap();
        let decl = gen_decl.as_enum();
        let mut name = gen_decl.get_formatted_name();
        let variant_name = &decl.variants.get(variant_id).unwrap().name;
        name.push_str("::");
        name.push_str(variant_name);
        name
    }
}

/// For struct/enum values: retrieve a field name
impl<'ctx> Formatter<(TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)> for AstFormatter<'ctx> {
    fn format_object(&self, id: (TypeDefId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        let ctx = self.type_context;
        let gen_decl = ctx.get_type_decl(def_id).unwrap();
        match (gen_decl, opt_variant_id) {
            (TypeDecl::Enum(decl), Some(variant_id)) => {
                let field = decl
                    .variants
                    .get(variant_id)
                    .unwrap()
                    .fields
                    .get(field_id)
                    .unwrap();
                field.name.clone()
            }
            (TypeDecl::Struct(decl), None) => {
                let field = decl.fields.get(field_id).unwrap();
                field.name.clone()
            }
            _ => unreachable!(),
        }
    }
}

impl<'ctx> Formatter<&ErasedRegion> for AstFormatter<'ctx> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'ctx> Formatter<&ETy> for AstFormatter<'ctx> {
    fn format_object(&self, ty: &ETy) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl<'ctx> Formatter<&Rvalue> for AstFormatter<'ctx> {
    fn format_object(&self, v: &Rvalue) -> String {
        v.fmt_with_ctx(self)
    }
}

impl<'ctx> Formatter<&Place> for AstFormatter<'ctx> {
    fn format_object(&self, p: &Place) -> String {
        p.fmt_with_ctx(self)
    }
}

impl<'ctx> Formatter<&Operand> for AstFormatter<'ctx> {
    fn format_object(&self, op: &Operand) -> String {
        op.fmt_with_ctx(self)
    }
}

impl FunDecl {
    pub fn fmt_with_decls<'ctx>(&self, ty_ctx: &'ctx TypeDecls, fun_ctx: &'ctx FunDecls) -> String {
        // Initialize the contexts
        let fun_sig_ctx = FunSigFormatter {
            ty_ctx,
            sig: &self.signature,
        };

        let eval_ctx = AstFormatter::new(
            ty_ctx,
            fun_ctx,
            &self.signature.type_params,
            &self.body.locals,
        );

        // Use the contexts for printing
        self.fmt_with_ctx("", &fun_sig_ctx, &eval_ctx)
    }
}
