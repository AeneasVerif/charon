use crate::assumed;
use crate::common::*;
use crate::generics;
use crate::names::Name;
use crate::names::{
    constant_def_id_to_name, function_def_id_to_name, hir_item_to_name, module_def_id_to_name,
    type_def_id_to_name, FunName, TypeName,
};
use crate::translate_functions_to_im;
use hashlink::LinkedHashMap;
use linked_hash_set::LinkedHashSet;
use rustc_hir::{
    def_id::DefId, def_id::LocalDefId, Defaultness, ImplItem, ImplItemKind, Item, ItemKind,
};
use rustc_middle::mir;
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::Span;
use std::collections::HashSet;

fn is_fn_decl(item: &Item) -> bool {
    match item.kind {
        ItemKind::Fn(_, _, _) => true,
        _ => false,
    }
}

pub struct CrateInfo {
    pub crate_name: String,
    pub opaque_mods: HashSet<String>,
}

impl CrateInfo {
    fn contains(&self, name: &Name) -> bool {
        name.is_in_modules(&self.crate_name, &self.opaque_mods)
    }
}

/// All kind of supported Rust top-level declarations.
#[derive(Debug, PartialEq, Eq)]
pub enum DeclKind {
    Type,
    Function,
    Global,
}

pub type DeclDependencies = LinkedHashSet<DefId>;

/// A registered declaration, listing its dependencies.
#[derive(Debug)]
pub struct Declaration {
    // The declaration may be local or extern (id.is_local()).
    pub id: DefId,
    pub kind: DeclKind,
    // The IDs of the declarations its body depends on.
    // None if opaque (it means that the body is unavailable).
    pub deps: Option<DeclDependencies>,
}

impl Declaration {
    fn new_opaque(id: DefId, kind: DeclKind) -> Declaration {
        Declaration {
            id,
            kind,
            deps: None,
        }
    }

    fn new_visible(id: DefId, kind: DeclKind, deps: LinkedHashSet<DefId>) -> Declaration {
        Declaration {
            id,
            kind,
            deps: Some(deps),
        }
    }

    pub fn is_local(&self) -> bool {
        self.id.is_local()
    }

    pub fn is_visible(&self) -> bool {
        self.deps.is_some()
    }
}

pub type RegisteredDeclarations = LinkedHashMap<DefId, Declaration>;

/// The declarations are registered in two steps :
/// It must first add their id before adding the whole declaration.
/// This is done to prevent infinite recursion while registering declarations.
struct DeclarationsRegister {
    decl_ids: LinkedHashSet<DefId>,
    decls: RegisteredDeclarations,
}

impl DeclarationsRegister {
    fn new() -> DeclarationsRegister {
        DeclarationsRegister {
            decl_ids: LinkedHashSet::new(),
            decls: RegisteredDeclarations::new(),
        }
    }

    fn knows(&self, id: &DefId) -> bool {
        self.decl_ids.contains(id)
    }

    fn add_id(&mut self, id: DefId) {
        assert!(self.decl_ids.insert(id), "Already knows {:?}", id);
    }

    fn add(&mut self, decl: Declaration) {
        let id = decl.id;
        assert!(self.knows(&id));

        assert!(
            self.decls.insert(id, decl).is_none(),
            "Registered the same declaration {:?} twice",
            id
        );
    }

    fn get_declarations(self) -> RegisteredDeclarations {
        for id in self.decl_ids.iter() {
            assert!(self.decls.contains_key(id), "Did not register {:?}", id);
        }
        self.decls
    }
}

struct RegisterContext<'a, 'b, 'c> {
    rustc: TyCtxt<'a>,
    sess: &'b Session,
    crate_info: &'c CrateInfo,
}

/// Register a HIR type.
/// This function is called when processing top-level declarations. It mostly
/// delegates the work to functions operating on the MIR (and once in MIR we
/// stay in MIR).
fn register_hir_type(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    item: &Item,
    def_id: DefId,
) -> Result<()> {
    trace!();
    decls.add_id(def_id);

    match &item.kind {
        ItemKind::TyAlias(_, _) => {
            // It seems type alias are not converted to MIR, and are inlined,
            // so we don't need to do anything. Note that we actually filter
            // type aliases before calling this function.
            trace!("enum");
            unreachable!();
        }
        ItemKind::Struct(_, _) | ItemKind::Enum(_, _) => {
            trace!("adt");

            // Retrieve the MIR adt from the def id and register it, retrieve
            // the list of dependencies at the same time.
            let adt = ctx.rustc.adt_def(def_id);
            return register_local_adt(ctx, decls, adt);
        }
        _ => {
            unreachable!();
        }
    }
}

/// Register a MIR ADT.
/// Note that the def id of the ADT should already have been stored in the set of
/// explored def ids.
fn register_local_adt(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    adt: &AdtDef,
) -> Result<()> {
    trace!("> adt: {:?}", adt);

    // First, retrieve the HIR definition - this function may have been
    // called from MIR code, which is why we don't take an item or a HIR
    // definition as parameter. We use it only for the span, to report
    // precise error messages to the user.
    let hir_map = ctx.rustc.hir();
    let item = if let rustc_hir::Node::Item(item) = hir_map.get_if_local(adt.did).unwrap() {
        item
    } else {
        unreachable!();
    };

    // Check the generics - TODO: we check this here and in translate_types
    generics::check_type_generics(ctx.rustc, adt.did);

    let type_id = adt.did;

    // We explore the type definition only if it is not in a module flagged
    // as opaque
    let name = type_def_id_to_name(ctx.rustc, adt.did);
    if ctx.crate_info.contains(&name) {
        // The type is opaque
        // Register it as having no dependencies (dependencies are introduced
        // by exploring the type definition, to check the types used in the fields).
        decls.add(Declaration::new_opaque(type_id, DeclKind::Type));
        return Ok(());
    }

    // Use a dummy substitution to instantiate the type parameters
    let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(ctx.rustc, adt.did);

    // Explore all the variants. Note that we also explore the HIR to retrieve
    // precise spans: for instance, to indicate which variant is problematic
    // in case of an enum.
    let hir_variants: &[rustc_hir::Variant] = match &item.kind {
        ItemKind::Enum(enum_def, _) => enum_def.variants,
        ItemKind::Struct(_, _) => {
            // Nothing to return
            &[]
        }
        _ => {
            unreachable!()
        }
    };

    let mut ty_deps = DeclDependencies::new();
    let mut i = 0; // The index of the variant
    for var_def in adt.variants.iter() {
        trace!("var_def");
        // Retrieve the most precise span (the span of the variant if this is an
        // enum, the span of the whole ADT otherwise).
        let var_span = if adt.is_enum() {
            &hir_variants[i].span
        } else {
            &item.span
        };

        for field_def in var_def.fields.iter() {
            trace!("field_def");
            let ty = field_def.ty(ctx.rustc, substs);
            trace!("ty");
            register_mir_ty(ctx, decls, var_span, &mut ty_deps, &ty)?;
        }

        i += 1;
    }

    // Add the type declaration to the registered declarations
    decls.add(Declaration::new_visible(type_id, DeclKind::Type, ty_deps));
    Ok(())
}

/// Register a non-local MIR ADT.
/// Note that the def id of the ADT should already have been stored in the set of
/// explored def ids.
///
/// For now, we don't do much.
/// In the future, we will explore the ADT, to reveal its public information
/// (public fields in case of a structure, variants in case of a public
/// enumeration).
fn register_non_local_adt(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    adt: &AdtDef,
    name: TypeName,
) -> Result<()> {
    trace!("> non-local adt: {:?}", adt);

    // First, check if the ADT has primitive support: if it is the case, there
    // is nothing to do
    if assumed::type_to_used_params(&name).is_some() {
        // Primitive
        return Ok(());
    }

    // Non-primitive (i.e.: external)
    let type_id = adt.did;

    // Check if registered
    if decls.knows(&type_id) {
        return Ok(());
    }
    decls.add_id(type_id);

    // Check the generics - TODO: we check this here and in translate_types
    generics::check_type_generics(ctx.rustc, type_id);

    // Register the type as having no dependencies
    decls.add(Declaration::new_opaque(type_id, DeclKind::Type));
    return Ok(());
}

/// Auxiliary function to register a list of type parameters.
fn register_mir_substs<'tcx>(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    span: &Span,
    ty_deps: &mut LinkedHashSet<DefId>,
    used_params: Option<Vec<bool>>,
    substs: &rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Result<()> {
    trace!("substs: {:?}", substs);

    // Filter the arguments, if necessary
    let params: Vec<rustc_middle::ty::subst::GenericArg<'tcx>> = match used_params {
        Option::None => substs.iter().collect(),
        Option::Some(used_params) => {
            // Note that the substs doesn't necessarily define a substitution
            // for all the parameters, because some of them have default
            // values: for this reason we can't check the length and used the
            // fact that `zip` below stops once one of the two iterators is
            // consumed.
            assert!(substs.len() == used_params.len());
            substs
                .iter()
                .zip(used_params.into_iter())
                .filter_map(|(param, used)| if used { Some(param) } else { None })
                .collect()
        }
    };

    // Register the arguments
    for param in params.into_iter() {
        match param.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                register_mir_ty(ctx, decls, span, ty_deps, &param_ty)?;
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(_)
            | rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                // Nothing to do
            }
        }
    }
    return Ok(());
}

/// Explore a base type and register all the types inside.
/// There is no need to perform any check on the type (to prevent cyclic calls)
/// before calling this function.
fn register_mir_ty(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    span: &Span,
    ty_deps: &mut LinkedHashSet<DefId>,
    ty: &Ty,
) -> Result<()> {
    trace!("> ty: {:?}", ty);

    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Str
        | TyKind::Float(_)
        | TyKind::Never => {
            // Nothing to do
            trace!("base type (Bool, Char, Int...)");
            return Ok(());
        }

        TyKind::Adt(adt, substs) => {
            trace!("Adt");

            // Identify the type by retrieving its name
            let name = type_def_id_to_name(ctx.rustc, adt.did);

            // Check if the type is primitive

            // Check if the type is primitive.
            //
            // Note that if the type is primitive, we might ignore
            // some of its parameters (for instance, we ignore the Allocator
            // parameter of `Box` and `Vec`).
            //
            // [used_params] below is an option:
            // - `Some` if the type is primitive and we need to filter some
            //   of its parameters
            // - `None` if it is not primitive (no filter information)
            let used_params = if adt.did.is_local() {
                // We probably do not need to check if the type is local...
                Option::None
            } else {
                assumed::type_to_used_params(&name)
            };

            // We probably don't need to check if the type is local...
            let is_prim = !adt.did.is_local() && used_params.is_some();
            // Add this ADT to the list of dependencies, only if it is not
            // primitive
            if !is_prim {
                ty_deps.insert(adt.did);
            }

            // From now onwards, we do something different depending on
            // whether the type is a local type (i.e., defined in the current
            // crate) or an assumed (external) type like box or vec
            if !adt.did.is_local() {
                // Explore the type parameters instantiation
                // There are two possibilities:
                // - either the type is considered primitive (i.e., it belongs
                //   to a well-identified list of types like `Box` which benefit
                //   from primitive treatment)
                // - or the type is external, in which case we register it as such

                // Explore the type parameters instantiation
                register_mir_substs(ctx, decls, span, ty_deps, used_params, substs)?;

                // Register the ADT.
                // Note that [register_non_local_adt] checks if the def id
                // has already been registered, and inserts it in the list
                // of def ids if necessary (not the same behaviour as the
                // "local" case, where we do that *before*).
                // TODO: we may want to do this more consistent.
                return register_non_local_adt(ctx, decls, adt, name);
            } else {
                // Explore the type parameters instantiation
                register_mir_substs(ctx, decls, span, ty_deps, Option::None, substs)?;

                // Explore the ADT, if we haven't already registered it
                // Check if registered
                if decls.knows(&adt.did) {
                    trace!("Adt already registered");
                    return Ok(());
                }
                trace!("Adt not registered");
                decls.add_id(adt.did);

                // Register and explore
                return register_local_adt(ctx, decls, adt);
            }
        }
        TyKind::Array(ty, const_param) => {
            trace!("Array");

            register_mir_ty(ctx, decls, span, ty_deps, ty)?;
            return register_mir_ty(ctx, decls, span, ty_deps, &const_param.ty);
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            return register_mir_ty(ctx, decls, span, ty_deps, ty);
        }
        TyKind::Ref(_, ty, _) => {
            trace!("Ref");

            return register_mir_ty(ctx, decls, span, ty_deps, ty);
        }
        TyKind::Tuple(substs) => {
            trace!("Tuple");

            for param in substs.iter() {
                let param_ty = param.expect_ty();
                register_mir_ty(ctx, decls, span, ty_deps, &param_ty)?;
            }

            return Ok(());
        }

        TyKind::RawPtr(_) => {
            // A raw pointer
            trace!("RawPtr");
            span_err(ctx.sess, span.clone(), "raw pointers are not supported");
            return Err(());
        }
        TyKind::Foreign(_) => {
            // A raw pointer
            trace!("Foreign");
            span_err(ctx.sess, span.clone(), "FFI types are not supported");
            return Err(());
        }
        TyKind::Infer(_) => {
            trace!("Infer");
            span_err(
                ctx.sess,
                span.clone(),
                "Inconsistant state: found an `Infer` type",
            );
            return Err(());
        }

        TyKind::FnDef(_, _) => {
            // We shouldn't get there
            trace!("FnDef");
            unreachable!();
        }

        TyKind::FnPtr(sig) => {
            trace!("FnPtr");
            for param_ty in sig.inputs_and_output().no_bound_vars().unwrap().iter() {
                register_mir_ty(ctx, decls, span, ty_deps, &param_ty)?;
            }
            return Ok(());
        }

        TyKind::Dynamic(_, _) => {
            // A trait object
            trace!("Dynamic");
            unimplemented!();
        }
        TyKind::Closure(_, _) => {
            trace!("Closure");
            unimplemented!();
        }

        TyKind::Generator(_, _, _) | TyKind::GeneratorWitness(_) => {
            trace!("Generator");
            span_err(ctx.sess, span.clone(), "Generators are not supported");
            return Err(());
        }

        TyKind::Error(_) => {
            trace!("Error");
            span_err(
                ctx.sess,
                span.clone(),
                "Error type found: the code doesn't typecheck",
            );
            return Err(());
        }
        TyKind::Projection(_) => {
            unimplemented!();
        }
        TyKind::Opaque(_, _) => {
            unimplemented!();
        }
        TyKind::Param(_) => {
            // A type parameter, for example `T` in `fn f<T>(x : T) {}`
            // We have nothing to do
            trace!("Param");
            return Ok(());
        }
        TyKind::Bound(_, _) => {
            unimplemented!();
        }
        TyKind::Placeholder(_) => {
            unimplemented!();
        }
    }
}

// Extract function information from an operand
fn get_fun_from_operand<'tcx>(
    op: &mir::Operand<'tcx>,
) -> Option<(DefId, rustc_middle::ty::subst::SubstsRef<'tcx>)> {
    let fun_ty = op.constant().unwrap().literal.ty();
    match fun_ty.kind() {
        TyKind::FnDef(def_id, substs) => return Some((*def_id, substs)),
        _ => {
            return None;
        }
    }
}

// Visits all statements and terminators of the body blocks.
fn visit_block<'tcx, V: mir::visit::Visitor<'tcx>>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    mut visitor: V,
) {
    use mir::visit::MirVisitable;

    // The location is not used below, so we pass an arbitrary one there.
    for statement in block.statements.iter() {
        statement.apply(mir::Location::START, &mut visitor);
    }
    block.terminator().apply(mir::Location::START, &mut visitor);
}

fn visit_constants<'tcx>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    f: &mut dyn FnMut(&'tcx rustc_middle::ty::Const<'tcx>),
) {
    // Implement the visitor trait for the given lambda.
    // It may be possible to avoid erasing f type with more rust-fu.
    struct ConstVisitor<'tcx, 'f> {
        f: &'f mut dyn FnMut(&'tcx rustc_middle::ty::Const<'tcx>),
    }
    impl<'tcx, 'f> mir::visit::Visitor<'tcx> for ConstVisitor<'tcx, 'f> {
        fn visit_const(&mut self, c: &&'tcx rustc_middle::ty::Const<'tcx>, _: mir::Location) {
            (self.f)(c);
        }
    }
    visit_block(block, ConstVisitor { f });
}

fn visit_constant_dependencies<'tcx, F: FnMut(DefId)>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    mut f: F,
) {
    visit_constants(block, &mut |c| match c.val {
        rustc_middle::ty::ConstKind::Value(_) => (),
        rustc_middle::ty::ConstKind::Unevaluated(uv) => {
            f(uv.def.did);
        }
        rustc_middle::ty::ConstKind::Param(_)
        | rustc_middle::ty::ConstKind::Infer(_)
        | rustc_middle::ty::ConstKind::Bound(_, _)
        | rustc_middle::ty::ConstKind::Placeholder(_)
        | rustc_middle::ty::ConstKind::Error(_) => {
            unimplemented!();
        }
    });
}

/// Rk.: contrary to the "local" case, [register_non_local_function] inserts
/// itself the def id in the declarations list. The reason is that we need
/// to check if the function has primitive support first.
fn register_non_local_function(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    def_id: DefId,
    name: FunName,
) -> Result<Option<Declaration>> {
    // First, check if the function has primitive support: if it is the case,
    // there is nothing to do
    if assumed::function_to_info(&name).is_some() {
        // Primitive
        return Ok(None);
    }

    // Check if registered
    if decls.knows(&def_id) {
        return Ok(None);
    }
    decls.add_id(def_id);

    // Check the generics - TODO: we check this here and in translate_functions_to_im
    generics::check_function_generics(ctx.rustc, def_id);

    // Register the function as having no dependencies
    Ok(Some(Declaration::new_opaque(def_id, DeclKind::Function)))
}

/// Register the identifiers found in a function or global body.
fn register_body(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    def_id: LocalDefId,
    deps: &mut LinkedHashSet<DefId>,
) -> Result<()> {
    // Retrieve the MIR code
    let body = crate::get_mir::get_mir_for_def_id(ctx.rustc, def_id);

    for b in body.basic_blocks().iter() {
        visit_constant_dependencies(b, |c_id| {
            if deps.insert_if_absent(c_id) {
                trace!(
                    "added constant dependency {:?} ~> {}",
                    def_id,
                    constant_def_id_to_name(ctx.rustc, c_id)
                );
            }
        });
    }

    // Start by registering the types found in the local variable declarations.
    // Note that those local variables include the parameters as well as the
    // return variable, and is thus enough to register the function signature.
    for v in body.local_decls.iter() {
        register_mir_ty(ctx, decls, &v.source_info.span, deps, &v.ty)?;
    }

    // Explore the body itself.
    // We need it to compute the dependencies between the functions and global
    // declarations, and also because some functions might be parameterized
    // with types which don't appear in the local variables (unlikely, but
    // can happen if some type parameters are not used).
    // We initially considered using visitors, but the MIR visitors return unit,
    // while we need to use a result type...
    // A basic block is a list of statements, followed by a terminator.
    for block in body.basic_blocks().iter() {
        // Statements
        for statement in block.statements.iter() {
            match &statement.kind {
                mir::StatementKind::Assign(_)
                | mir::StatementKind::FakeRead(_)
                | mir::StatementKind::SetDiscriminant {
                    place: _,
                    variant_index: _,
                }
                | mir::StatementKind::StorageLive(_)
                | mir::StatementKind::StorageDead(_)
                | mir::StatementKind::AscribeUserType(_, _)
                | mir::StatementKind::Coverage(_)
                | mir::StatementKind::Nop => {
                    // Nothing to do
                }

                mir::StatementKind::CopyNonOverlapping(_) => {
                    trace!("Copy non overlapping");
                    span_err(
                        ctx.sess,
                        statement.source_info.span.clone(),
                        "Copy non overlapping not supported",
                    );
                }
                mir::StatementKind::Retag(_, _) => {
                    // retag statements are only used by MIRI, so we have nothing
                    // to do
                }
            }
        }

        // Terminator
        let terminator = block.terminator();
        match &terminator.kind {
            mir::terminator::TerminatorKind::Goto { target: _ }
            | mir::terminator::TerminatorKind::SwitchInt {
                discr: _,
                switch_ty: _,
                targets: _,
            }
            | mir::terminator::TerminatorKind::Resume
            | mir::terminator::TerminatorKind::Abort
            | mir::terminator::TerminatorKind::Return
            | mir::terminator::TerminatorKind::Unreachable
            | mir::terminator::TerminatorKind::Drop {
                place: _,
                target: _,
                unwind: _,
            }
            | mir::terminator::TerminatorKind::Assert {
                cond: _,
                expected: _,
                msg: _,
                target: _,
                cleanup: _,
            }
            | mir::terminator::TerminatorKind::FalseEdge {
                real_target: _,
                imaginary_target: _,
            }
            | mir::terminator::TerminatorKind::FalseUnwind {
                real_target: _,
                unwind: _,
            }
            | mir::terminator::TerminatorKind::DropAndReplace {
                place: _,
                value: _,
                target: _,
                unwind: _,
            } => {
                // Nothing to do
            }
            mir::terminator::TerminatorKind::Call {
                func,
                args,
                destination: _,
                cleanup: _,
                from_hir_call: _,
                fn_span,
            } => {
                trace!("terminator: Call\n{:?}", &terminator);
                trace!("terminator:Call:func: {:?}", func);

                let (fid, substs) = get_fun_from_operand(func).expect("Expected a function call");
                trace!("terminator:Call:fid {:?}", fid);

                let name = function_def_id_to_name(ctx.rustc, fid);
                trace!("called function: name: {:?}", name);

                // We may need to filter the types and arguments, if the type
                // is considered primitive
                let (used_types, used_args, is_prim) = if fid.is_local() {
                    // We probably do not need to check if the function is local...
                    (Option::None, Option::None, false)
                } else {
                    match assumed::function_to_info(&name) {
                        Option::Some(used) => {
                            // The function is primitive
                            (
                                Option::Some(used.used_type_params),
                                Option::Some(used.used_args),
                                true,
                            )
                        }
                        Option::None => {
                            // The function is non-primitive (i.e., external)
                            (Option::None, Option::None, false)
                        }
                    }
                };

                // Add this function to the list of dependencies, only if
                // it is non-primitive
                if !is_prim {
                    deps.insert(fid);
                }

                // Register the types given as parameters.
                register_mir_substs(ctx, decls, &fn_span, deps, used_types, &substs)?;

                // Filter and register the argument types.
                // There is something very annoying, which is that MIR is quite
                // low level.
                // Very specifically, when introducing `box_free`, rustc introduces
                // something of the following form:
                // ```
                // _9 = alloc::alloc::box_free::<T, std::alloc::Global>(
                //   move (_4.0: std::ptr::Unique<T>),
                //   move (_4.1: std::alloc::Global)) -> bb3;
                // ```
                // We don't support unique pointers, so we have to ignore the
                // arguments in this case (and the `box_free` case has a
                // special treatment when translating function bodies).
                // Note that the type parameters have already been registered.
                if !name.equals_ref_name(&assumed::BOX_FREE_NAME) {
                    let args: Vec<&mir::Operand<'_>> = match used_args {
                        Option::None => args.iter().collect(),
                        Option::Some(used_args) => {
                            // Filter
                            trace!("args: {:?}, used_args: {:?}", args, used_args);
                            assert!(args.len() == used_args.len());
                            args.iter()
                                .zip(used_args.into_iter())
                                .filter_map(|(param, used)| if used { Some(param) } else { None })
                                .collect()
                        }
                    };
                    for a in args.into_iter() {
                        trace!("terminator: Call: arg: {:?}", a);

                        let ty = a.ty(&body.local_decls, ctx.rustc);
                        register_mir_ty(ctx, decls, &fn_span, deps, &ty)?;
                    }
                }

                // Note that we don't need to register the "bare" function
                // signature: all the types it contains are already covered
                // by the type arguments and the parameters.

                // Lookup the function definition, if it is local (i.e.: is
                // defined in the current crate).
                let hir_map = ctx.rustc.hir();
                let f_node = hir_map.get_if_local(fid);
                match f_node {
                    Some(f_node) => {
                        trace!("Function is local");
                        match f_node {
                            rustc_hir::Node::Item(f_item) => {
                                trace!("Item");
                                assert!(is_fn_decl(f_item));
                                register_hir_item(ctx, decls, false, f_item)?;
                            }
                            rustc_hir::Node::ImplItem(impl_item) => {
                                trace!("Impl item");
                                // [register_hir_impl_item doesn't check if the item
                                // has already been registered, so we need to
                                // check it before calling it.
                                register_hir_impl_item(ctx, decls, impl_item)?;
                            }
                            _ => {
                                unreachable!();
                            }
                        }
                    }
                    None => {
                        trace!("Function external");
                        // Register
                        // Rk.: [register_non_local_function] checks if the def
                        // id has already been registered, and inserts it in the
                        // decls set if necessary (not the same behaviour as
                        // the "local" case).
                        register_non_local_function(ctx, decls, fid, name)?;
                    }
                }
            }
            mir::terminator::TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => {
                trace!("terminator: Yield");
                span_err(
                    ctx.sess,
                    terminator.source_info.span.clone(),
                    "Yield is not supported",
                );
            }
            mir::terminator::TerminatorKind::GeneratorDrop => {
                trace!("terminator: GeneratorDrop");
                span_err(
                    ctx.sess,
                    terminator.source_info.span.clone(),
                    "Generators are not supported",
                );
            }
            mir::terminator::TerminatorKind::InlineAsm {
                template: _,
                operands: _,
                options: _,
                line_spans: _,
                destination: _,
                cleanup: _,
            } => {
                trace!("terminator: InlineASM");
                span_err(
                    ctx.sess,
                    terminator.source_info.span.clone(),
                    "Inline ASM is not supported",
                );
            }
        }
    }

    Ok(())
}

/// Register a function.
/// It must not have been registered before.
fn register_local_function(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    ldef_id: LocalDefId,
) -> Result<()> {
    trace!("{:?}", ldef_id);

    let def_id = ldef_id.to_def_id();
    decls.add_id(def_id);

    // Check the generics - TODO: we check this here and in translate_functions_to_im
    generics::check_function_generics(ctx.rustc, def_id);

    // We explore the function definition only if it is not in a module flagged
    // as opaque
    let name = function_def_id_to_name(ctx.rustc, def_id);
    if ctx.crate_info.contains(&name) {
        // The function is opaque
        // Store the function declaration in the declaration map
        decls.add(Declaration::new_opaque(def_id, DeclKind::Function));
        return Ok(());
    }

    let mut fn_deps = DeclDependencies::new();

    // The function is not opaque
    // Explore the body
    register_body(ctx, decls, ldef_id, &mut fn_deps)?;

    // Store the function declaration in the declarations map
    decls.add(Declaration::new_visible(
        def_id,
        DeclKind::Function,
        fn_deps,
    ));
    return Ok(());
}

/// Register a constant, in the same way we register functions.
fn register_local_global(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    ldef_id: LocalDefId,
) -> Result<()> {
    trace!("{:?}", ldef_id);

    let def_id = ldef_id.to_def_id();
    decls.add_id(def_id);

    // Check the generics
    // TODO: Refuse anything depending on a generic parameter.
    generics::check_constant_generics(ctx.rustc, def_id);

    // We explore the constant definition only if it is not in a module flagged
    // as opaque
    let name = constant_def_id_to_name(ctx.rustc, def_id);
    if ctx.crate_info.contains(&name) {
        // The constant is opaque
        // Store the constant declaration in the declaration map
        decls.add(Declaration::new_opaque(def_id, DeclKind::Global));
        return Ok(());
    }

    let mut const_deps = DeclDependencies::new();

    // The constant is not opaque
    // Explore the body
    register_body(ctx, decls, ldef_id, &mut const_deps)?;

    // Store the constant declaration in the declarations map
    decls.add(Declaration::new_visible(
        def_id,
        DeclKind::Global,
        const_deps,
    ));
    return Ok(());
}

/// General function to register a MIR item. It is called on all the top-level
/// items. This includes: crate inclusions and `use` instructions (which are
/// ignored), but also type and functions declarations.
/// Note that this function checks if the item has been registered, and adds
/// its def_id to the list of registered items otherwise.
fn register_hir_item(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    top_item: bool,
    item: &Item,
) -> Result<()> {
    trace!("{:?}", item);

    // First check if the item definition has already been registered
    // (or is currently being registered). If it is the case, return to
    // prevent cycles. If not registered yet, do not immediately add it:
    // it may be an item we won't translate (`use module`, `extern crate`...).
    let def_id = item.def_id.to_def_id();
    if decls.knows(&def_id) {
        return Ok(());
    }

    // The annoying thing is that when iterating over the items in a crate, we
    // iterate over *all* the items, which is annoying with regards to the
    // *opaque* modules: we see all the definitions which are in there, and
    // not only those which are transitively reachable from the root.
    // Because of this, we need the following check: if the item is a "top"
    // item (not an item transitively reachable from an item which is not
    // opaque) and inside an opaque module (or sub-module), we ignore it.
    if top_item {
        match hir_item_to_name(ctx.rustc, item) {
            Option::None => {
                // This kind of item is to be ignored
                return Ok(());
            }
            Option::Some(item_name) => {
                if ctx.crate_info.contains(&item_name) {
                    return Ok(());
                }
            }
        }
    }

    // Case disjunction on the kind. Note that here we retrieve the HIR items,
    // but then work on the MIR.
    match &item.kind {
        ItemKind::TyAlias(_, _) => {
            // We ignore the type aliases - it seems they are inlined
            Ok(())
        }
        ItemKind::OpaqueTy(_) => unimplemented!(),
        ItemKind::Union(_, _) => unimplemented!(),
        ItemKind::Enum(_, _) | ItemKind::Struct(_, _) => {
            register_hir_type(ctx, decls, item, def_id)
        }
        ItemKind::Fn(_, _, _) => register_local_function(ctx, decls, item.def_id),
        ItemKind::Const(_, _) | ItemKind::Static(_, _, _) => {
            register_local_global(ctx, decls, item.def_id)
        }
        ItemKind::Impl(impl_block) => {
            trace!("impl");
            // Sanity checks
            translate_functions_to_im::check_impl_item(impl_block);

            // Explore the items
            let hir_map = ctx.rustc.hir();
            for impl_item_ref in impl_block.items {
                // impl_item_ref only gives the reference of the impl item:
                // we need to look it up
                let impl_item = hir_map.impl_item(impl_item_ref.id);

                register_hir_impl_item(ctx, decls, impl_item)?;
            }
            Ok(())
        }
        ItemKind::Use(_, _) => {
            // Ignore
            trace!("use");
            Ok(())
        }
        ItemKind::ExternCrate(_) => {
            // Ignore
            trace!("extern crate");
            Ok(())
        }
        ItemKind::Mod(module) => {
            trace!("module");

            // Explore the module, only if it was not marked as "opaque"
            // TODO: we may want to accumulate the set of modules we found,
            // to check that all the opaque modules given as arguments actually
            // exist
            trace!("{:?}", def_id);
            let module_name = module_def_id_to_name(ctx.rustc, def_id);
            let opaque = ctx.crate_info.contains(&module_name);
            if opaque {
                // Ignore
                trace!("Ignoring module [{}] because marked as opaque", module_name);
                Ok(())
            } else {
                trace!("Diving into module [{}]", module_name);
                let hir_map = ctx.rustc.hir();
                for item_id in module.item_ids {
                    // Lookup and register the item
                    let item = hir_map.item(*item_id);
                    register_hir_item(ctx, decls, false, item)?;
                }
                Ok(())
            }
        }
        _ => {
            unimplemented!("{:?}", item.kind);
        }
    }
}

/// Register an impl item (an item defined in an `impl` block).
fn register_hir_impl_item(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    impl_item: &ImplItem,
) -> Result<()> {
    // Check if the item has already been registered
    let def_id = impl_item.def_id.to_def_id();
    if decls.knows(&def_id) {
        return Ok(());
    }

    // TODO: make proper error message
    assert!(impl_item.defaultness == Defaultness::Final);

    // Match on the impl item kind
    match &impl_item.kind {
        ImplItemKind::Const(_, _) => unimplemented!(),
        ImplItemKind::TyAlias(_) => unimplemented!(),
        ImplItemKind::Fn(_, _) => {
            let local_def_id = impl_item.def_id;
            register_local_function(ctx, decls, local_def_id)
        }
    }
}

/// General function to register the declarations in a crate.
pub fn register_crate(
    crate_info: &CrateInfo,
    sess: &Session,
    tcx: TyCtxt,
) -> Result<RegisteredDeclarations> {
    let ctx = RegisterContext {
        rustc: tcx,
        crate_info,
        sess,
    };
    let mut decls = DeclarationsRegister::new();

    // TODO: in order to have a good ordering when extracting the information
    // from a crate with several modules, it would be better to not register
    // def ids immediately upon finding them, put rather to push them on a
    // stack, so that we can try to explore them in the order in which they
    // are defined in their respective modules.

    // The way rustc works is as follows:
    // - we call it on the root of the crate (for instance "main.rs"), and it
    //   explores all the files from there (typically listed through statements
    //   of the form "mod MODULE_NAME")
    // - the other files in the crate are Module items in the HIR graph
    for item in tcx.hir().items() {
        register_hir_item(&ctx, &mut decls, true, item)?;
    }
    Ok(decls.get_declarations())
}
