//! Explore a crate to register all the definitions inside, their dependencies,
//! and the dependency graph.
//!
//! TODO: this is a bit messy and should be restructured. In particular, it
//! is not always obvious at which point we cross definition boundaries, which
//! means it is not obvious where we should check whether we already registered
//! an id or not (to prevent exploration cycles).
//! Maybe we could have some functions which return unit (and do in-place updates),
//! and some others which return a declaration. One kind of definitions would
//! also perform a check upon being called, while the other would not.

use crate::assumed;
use crate::common::*;
use crate::generics;
use crate::get_mir::{extract_constants_at_top_level, get_mir_for_def_id_and_level, MirLevel};
use crate::meta;
use crate::meta::{FileInfo, FileName};
use crate::names::Name;
use crate::names::{
    function_def_id_to_name, global_def_id_to_name, hir_item_to_name, module_def_id_to_name,
    type_def_id_to_name,
};
use crate::translate_functions_to_ullbc;
use hashlink::LinkedHashMap;
use im::Vector;
use linked_hash_set::LinkedHashSet;
use rustc_hir::{
    def_id::DefId, def_id::LocalDefId, Defaultness, ImplItem, ImplItemKind, Item, ItemKind,
};
use rustc_middle::mir;
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};

/// `stack`: see the explanations for [explore_local_hir_item].
pub(crate) fn stack_to_string(stack: &Vector<DefId>) -> String {
    let v: Vec<String> = stack.iter().map(|id| format!("  {id:?}")).collect();
    v.join("\n")
}

pub struct CrateInfo {
    pub crate_name: String,
    pub opaque_mods: HashSet<String>,
}

impl CrateInfo {
    fn has_opaque_decl(&self, name: &Name) -> bool {
        name.is_in_modules(&self.crate_name, &self.opaque_mods)
    }
}

/// All kind of supported Rust top-level declarations.
/// const and static variables are merged together in the global kind.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Type,
    Fun,
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

    fn new_transparent(id: DefId, kind: DeclKind, deps: DeclDependencies) -> Declaration {
        Declaration {
            id,
            kind,
            deps: Some(deps),
        }
    }

    pub fn is_transparent(&self) -> bool {
        self.deps.is_some()
    }
}

fn get_decl_name(tcx: TyCtxt, kind: DeclKind, id: DefId) -> Name {
    match kind {
        DeclKind::Type => type_def_id_to_name(tcx, id),
        DeclKind::Fun => function_def_id_to_name(tcx, id),
        DeclKind::Global => global_def_id_to_name(tcx, id),
    }
}

fn is_primitive_decl(kind: DeclKind, id: DefId, name: &Name) -> bool {
    if id.is_local() {
        return false;
    }
    match kind {
        DeclKind::Type => assumed::type_to_used_params(name).is_some(),
        DeclKind::Fun => assumed::function_to_info(name).is_some(),
        DeclKind::Global => false,
    }
}

fn check_decl_generics(kind: DeclKind, tcx: TyCtxt, id: DefId) {
    match kind {
        DeclKind::Type => generics::check_type_generics(tcx, id),
        DeclKind::Fun => generics::check_function_generics(tcx, id),
        DeclKind::Global => generics::check_global_generics(tcx, id),
    }
}

fn new_opaque_declaration(
    tcx: TyCtxt,
    id: DefId,
    kind: DeclKind,
    name: &Name,
) -> Option<Declaration> {
    trace!("opaque declaration {}", name);

    if is_primitive_decl(kind, id, name) {
        return None;
    }

    // TODO: we check this here and in translate_types
    check_decl_generics(kind, tcx, id);
    Some(Declaration::new_opaque(id, kind))
}

// TODO: simplify: we should be able to merge 'b and 'c
struct RegisterContext<'a, 'b, 'c> {
    rustc: TyCtxt<'a>, // TODO: rename
    sess: &'b Session,
    crate_info: &'c CrateInfo,
    mir_level: MirLevel,
}

pub type RegisteredDeclarations = LinkedHashMap<DefId, Declaration>;

/// Structure used to register declarations: see
/// [DeclarationsRegister::register_opaque_declaration] and
/// [DeclarationsRegister::register_local_declaration].
///
/// TODO: merge with [RegisterContext]?
struct DeclarationsRegister {
    decl_ids: LinkedHashSet<DefId>,
    decls: RegisteredDeclarations,
    files: HashMap<FileName, FileInfo>,
}

impl DeclarationsRegister {
    fn new() -> DeclarationsRegister {
        DeclarationsRegister {
            decl_ids: LinkedHashSet::new(),
            decls: RegisteredDeclarations::new(),
            files: HashMap::new(),
        }
    }

    /// Register the file containing a definition (rem.: we register the
    /// file containing the definition itself, not its def ident).
    fn register_file_from_def_id(&mut self, ctx: &RegisterContext, def_id: DefId) {
        let span = meta::get_rspan_from_def_id(ctx.rustc, def_id);
        self.register_file_from_span(ctx, span);
    }

    /// Register the file referenced by a span
    fn register_file_from_span(&mut self, ctx: &RegisterContext, span: rustc_span::Span) {
        let filename = meta::get_filename_from_rspan(ctx.sess, span);
        self.register_file(filename);
    }

    /// Register a file if it is a "real" file if it was not already registered
    fn register_file(&mut self, filename: FileName) {
        let _ = self.files.insert(filename, FileInfo {});
    }

    /// Indicates if the declaration is being (or has been) added.
    fn knows(&self, id: &DefId) -> bool {
        self.decl_ids.contains(id)
    }

    /// The declarations are registered in two steps:
    /// When their exploration begins, we must first add their id.
    /// This is done to prevent cycles while registering declarations.
    ///
    /// Should not be called outside [DeclarationsRegister]'s methods:
    /// Use either [DeclarationsRegister::register_opaque_declaration]
    /// or [DeclarationsRegister::register_local_declaration] instead.
    fn add_begin(&mut self, id: DefId) {
        assert!(self.decl_ids.insert(id), "Already knows {:?}", id);
    }

    /// Finalize the registering of a declaration.
    ///
    /// Should not be called outside [DeclarationsRegister]'s methods:
    /// Use either [DeclarationsRegister::register_opaque_declaration]
    /// or [DeclarationsRegister::register_local_declaration] instead.
    fn add_end(&mut self, decl: Declaration) {
        let id = decl.id;
        assert!(self.knows(&id));

        assert!(
            self.decls.insert(id, decl).is_none(),
            "Registered the same declaration {:?} twice",
            id
        );
    }

    /// Register an opaque declaration (can be an external declaration,
    /// or a local declaration).
    ///
    /// Does not explore further the declaration content: if the declaration was
    /// unknown, registers it without dependencies.
    ///
    /// `stack`: see the explanations for [explore_local_hir_item].
    fn register_opaque_declaration(
        &mut self,
        ctx: &RegisterContext,
        stack: &Vector<DefId>,
        id: DefId,
        kind: DeclKind,
        name: &Name,
    ) {
        if self.knows(&id) {
            return;
        }

        trace!(
            "Registering opaque declaration {}\n\nStack:\n{}",
            name,
            stack_to_string(stack)
        );

        // Register the file
        self.register_file_from_def_id(ctx, id);

        if let Some(decl) = new_opaque_declaration(ctx.rustc, id, kind, name) {
            self.add_begin(id);
            self.add_end(decl);
        }
    }

    /// Registers a local declaration and its dependencies recursively.
    ///
    /// This function takes a closure as input. We do this so that we
    /// can make sure the closure, which should explore the content
    /// of the declaration and its dependencies, is called between
    /// [DeclarationsRegister::add_begin] and [DeclarationsRegister::add_end].
    ///
    /// The visitor takes `&mut self` to avoid a double borrow.
    fn register_local_declaration<
        F: FnOnce(&mut DeclarationsRegister) -> Result<DeclDependencies>,
    >(
        &mut self,
        ctx: &RegisterContext,
        stack: &Vector<DefId>,
        local_id: LocalDefId,
        kind: DeclKind,
        list_dependencies: F,
    ) -> Result<()> {
        trace!(
            "Registering transparent declaration {:?}\n\nStack:\n{}",
            local_id,
            stack_to_string(stack)
        );

        let id = local_id.to_def_id();
        self.add_begin(id);

        // Register the file
        self.register_file_from_def_id(ctx, id);

        let name = get_decl_name(ctx.rustc, kind, id);

        // Only local declarations are supported for now, it should not be primitive.
        if is_primitive_decl(kind, id, &name) {
            unreachable!();
        }

        // TODO: we check this here and in translate_functions_to_ullbc
        check_decl_generics(kind, ctx.rustc, id);

        // We don't explore declarations in opaque modules.
        if ctx.crate_info.has_opaque_decl(&name) {
            self.add_end(Declaration::new_opaque(id, kind));
            Ok(())
        } else {
            let deps = list_dependencies(self)?;
            self.add_end(Declaration::new_transparent(id, kind, deps));
            Ok(())
        }
    }

    /// Returns all registered files and declarations.
    /// Verifies that no known id or dependency is missing.
    fn get_files_and_declarations(self) -> (HashMap<FileName, FileInfo>, RegisteredDeclarations) {
        for id in self.decl_ids.iter() {
            assert!(
                self.decls.contains_key(id),
                "Did not register known id {:?}",
                id
            );
        }
        // for (_, decl) in &self.decls {
        //     for id in decl.deps.iter().flatten() {
        //         assert!(
        //             self.decls.contains_key(id),
        //             "Did not register dependency id {:?} from {:?} in {:?}",
        //             id,
        //             decl.id,
        //             self.decls,
        //         )
        //     }
        // }
        (self.files, self.decls)
    }
}

/// Explore an HIR type.
/// This function is called when processing top-level declarations. It mostly
/// delegates the work to functions operating on the MIR (and once in MIR we
/// stay in MIR).
///
/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_local_hir_type_item(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    item: &Item,
    def_id: DefId,
) -> Result<()> {
    trace!();

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
            explore_local_adt(ctx, stack, decls, &adt)
        }
        _ => {
            unreachable!();
        }
    }
}

/// Register a MIR ADT.
/// Note that the def id of the ADT should already have been stored in the set of
/// explored def ids.
///
/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_local_adt(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    adt: &AdtDef,
) -> Result<()> {
    trace!("> adt: {:?}", adt);

    // First, retrieve the HIR definition - this function may have been
    // called from MIR code, which is why we don't take an item or a HIR
    // definition as parameter. We use it only for the span, to report
    // precise error messages to the user.
    let adt_did = adt.did();
    let hir_map = ctx.rustc.hir();
    let item = if let rustc_hir::Node::Item(item) = hir_map.get_if_local(adt_did).unwrap() {
        item
    } else {
        unreachable!();
    };

    let local_id = adt_did.as_local().unwrap();

    // Update the stack for when we explore the ADT body
    let mut nstack = stack.clone();
    nstack.push_back(local_id.to_def_id());

    decls.register_local_declaration(ctx, &stack, local_id, DeclKind::Type, |decls| {
        // Use a dummy substitution to instantiate the type parameters
        let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(ctx.rustc, adt_did);

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
        for (i, var_def) in adt.variants().iter().enumerate() {
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

                explore_mir_ty(ctx, nstack.clone(), decls, var_span, &mut ty_deps, &ty)?;
            }
        }
        Ok(ty_deps)
    })
}

/// Auxiliary function to register a list of type parameters.
///
/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_mir_substs<'tcx>(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    span: &Span,
    ty_deps: &mut DeclDependencies,
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
            assert!(
                substs.len() == used_params.len(),
                "Subst: {:?}, Used params: {:?}",
                substs,
                used_params
            );
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
                explore_mir_ty(ctx, stack.clone(), decls, span, ty_deps, &param_ty)?;
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(_)
            | rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                // Nothing to do
            }
        }
    }
    Ok(())
}

/// Explore a base type and register all the types inside.
/// There is no need to perform any check on the type (to prevent cyclic calls)
/// before calling this function.
///
/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_mir_ty(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    span: &Span,
    ty_deps: &mut DeclDependencies,
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
            Ok(())
        }

        TyKind::Adt(adt, substs) => {
            trace!("Adt");

            let adt_did = adt.did();

            // Identify the type by retrieving its name
            let name = type_def_id_to_name(ctx.rustc, adt_did);

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
            let used_params = if adt_did.is_local() {
                // We probably do not need to check if the type is local...
                Option::None
            } else {
                assumed::type_to_used_params(&name)
            };

            // We probably don't need to check if the type is local...
            let is_prim = !adt_did.is_local() && used_params.is_some();
            // Add this ADT to the list of dependencies, only if it is not
            // primitive
            if !is_prim {
                ty_deps.insert(adt_did);
            }

            // From now onwards, we do something different depending on
            // whether the type is a local type (i.e., defined in the current
            // crate) or an assumed (external) type like box or vec
            if !adt_did.is_local() {
                // Explore the type parameters instantiation
                // There are two possibilities:
                // - either the type is considered primitive (i.e., it belongs
                //   to a well-identified list of types like `Box` which benefit
                //   from primitive treatment)
                // - or the type is external, in which case we register it as such

                // Explore the type parameters instantiation
                explore_mir_substs(
                    ctx,
                    stack.clone(),
                    decls,
                    span,
                    ty_deps,
                    used_params,
                    substs,
                )?;

                // Register the external ADT as an opaque declaration.
                // In the future, we will explore the ADT, to reveal its public
                // information (public fields in case of a structure, variants in
                // case of a public enumeration).
                decls.register_opaque_declaration(ctx, &stack, adt_did, DeclKind::Type, &name);
                Ok(())
            } else {
                // Explore the type parameters instantiation
                explore_mir_substs(
                    ctx,
                    stack.clone(),
                    decls,
                    span,
                    ty_deps,
                    Option::None,
                    substs,
                )?;

                // Explore the ADT, if we haven't already registered it
                // Check if registered
                if decls.knows(&adt_did) {
                    trace!("Adt already registered");
                    return Ok(());
                }
                trace!("Adt not registered");

                // Register and explore
                explore_local_adt(ctx, stack, decls, adt)
            }
        }
        TyKind::Array(ty, const_param) => {
            trace!("Array");

            explore_mir_ty(ctx, stack.clone(), decls, span, ty_deps, ty)?;
            explore_mir_ty(ctx, stack, decls, span, ty_deps, &const_param.ty())
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            explore_mir_ty(ctx, stack, decls, span, ty_deps, ty)
        }
        TyKind::Ref(_, ty, _) => {
            trace!("Ref");

            explore_mir_ty(ctx, stack, decls, span, ty_deps, ty)
        }
        TyKind::Tuple(substs) => {
            trace!("Tuple");

            for param in substs.iter() {
                explore_mir_ty(ctx, stack.clone(), decls, span, ty_deps, &param)?;
            }

            Ok(())
        }

        TyKind::RawPtr(_) => {
            // A raw pointer
            trace!("RawPtr");
            Ok(())
        }
        TyKind::Foreign(_) => {
            // A raw pointer
            trace!("Foreign");
            span_err(ctx.sess, *span, "FFI types are not supported");
            Err(())
        }
        TyKind::Infer(_) => {
            trace!("Infer");
            span_err(ctx.sess, *span, "Inconsistant state: found an `Infer` type");
            Err(())
        }

        TyKind::FnDef(_, _) => {
            // We shouldn't get there
            trace!("FnDef");
            unreachable!();
        }

        TyKind::FnPtr(sig) => {
            trace!("FnPtr");
            for param_ty in sig.inputs_and_output().no_bound_vars().unwrap().iter() {
                explore_mir_ty(ctx, stack.clone(), decls, span, ty_deps, &param_ty)?;
            }
            Ok(())
        }

        TyKind::Dynamic(_, _, _) => {
            // A trait object
            trace!("Dynamic");
            trace!("Patch");
            Ok(())
        }
        TyKind::Closure(_, _) => {
            trace!("Closure");
            trace!("Patch");
            Ok(())
        }

        TyKind::Generator(_, _, _) | TyKind::GeneratorWitness(_) => {
            trace!("Generator");
            span_err(ctx.sess, *span, "Generators are not supported");
            Err(())
        }

        TyKind::Alias(_, _) => {
            unimplemented!();
        }

        TyKind::Error(_) => {
            trace!("Error");
            span_err(
                ctx.sess,
                *span,
                "Error type found: the code doesn't typecheck",
            );
            Err(())
        }
        TyKind::Param(_) => {
            // A type parameter, for example `T` in `fn f<T>(x: T) {}`
            // We have nothing to do
            trace!("Param");
            Ok(())
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
        TyKind::FnDef(def_id, substs) => Some((*def_id, substs)),
        _ => None,
    }
}

// Visits all statements and terminators of the body blocks.
fn visit_block<'tcx, V: mir::visit::Visitor<'tcx>>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    mut visitor: V,
) {
    use mir::visit::MirVisitable;

    // The location is not used in the visitor, so we pass an arbitrary one there.
    for statement in block.statements.iter() {
        statement.apply(mir::Location::START, &mut visitor);
    }
    block.terminator().apply(mir::Location::START, &mut visitor);
}

// TODO: it seems we miss some globals when using `visit_constant`.
// Reimplement our own visitor.
fn visit_globals<'tcx>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    f: &mut dyn FnMut(&rustc_middle::mir::Constant<'tcx>),
) {
    // Implement the visitor trait for the given lambda.
    // It may be possible to avoid erasing f type with more rust-fu.
    struct ConstantVisitor<'tcx, 'f> {
        f: &'f mut dyn FnMut(&rustc_middle::mir::Constant<'tcx>),
    }
    impl<'tcx, 'f> mir::visit::Visitor<'tcx> for ConstantVisitor<'tcx, 'f> {
        fn visit_constant(&mut self, c: &rustc_middle::mir::Constant<'tcx>, _: mir::Location) {
            (self.f)(c);
        }
    }
    visit_block(block, ConstantVisitor { f });
}

/// Return true if the type is exactly `&str`
fn ty_is_shared_borrow_str(ty: &Ty) -> bool {
    match ty.kind() {
        TyKind::Ref(_, sty, rustc_middle::mir::Mutability::Not) => {
            matches!(sty.kind(), TyKind::Str)
        }
        _ => false,
    }
}

/// Visit the globals used in a block.
///
/// This function should be called *only if* we extract the constants at the top
/// level (typically if we extract the built MIR). Otherwise, the constants
/// should be evaluated away and inlined in the code.
fn visit_global_dependencies<'tcx, F: FnMut(DefId)>(
    mir_level: MirLevel,
    block: &'tcx mir::BasicBlockData<'tcx>,
    mut f: F,
) {
    visit_globals(block, &mut |c| match c.literal {
        // This is the "normal" constant case
        // TODO: this changed when we updated from Nightly 2022-01-29 to
        // Nightly 2022-09-19
        mir::ConstantKind::Ty(c) => match c.kind() {
            rustc_middle::ty::ConstKind::Value(_) => (),
            rustc_middle::ty::ConstKind::Unevaluated(cv) => {
                // We should get there only if we don't need to evaluate
                // the constant: in this case we register its id
                assert!(extract_constants_at_top_level(mir_level));
                f(cv.def.did);
            }
            rustc_middle::ty::ConstKind::Expr(_)
            | rustc_middle::ty::ConstKind::Param(_)
            | rustc_middle::ty::ConstKind::Infer(_)
            | rustc_middle::ty::ConstKind::Bound(_, _)
            | rustc_middle::ty::ConstKind::Placeholder(_)
            | rustc_middle::ty::ConstKind::Error(_) => {
                unimplemented!();
            }
        },
        // I'm not sure what this is about: the documentation is weird.
        mir::ConstantKind::Val(cv, ty) => {
            match cv {
                mir::interpret::ConstValue::Scalar(_) => {
                    // Nothing to do
                }
                mir::interpret::ConstValue::ByRef { .. } => {
                    unimplemented!()
                }
                mir::interpret::ConstValue::Slice { .. } => {
                    trace!("ConstValue::Slice: ty: {:?}", ty);
                    // For now we support slices only if they are `&str` -
                    // we should encounter them only through the error messages
                    // raised when panicking (because we use visitors, we explore
                    // *everything*, including the arguments of `std::core::panic`
                    // for instance).
                    // TODO: change that.
                    assert!(ty_is_shared_borrow_str(&ty));
                }
                mir::interpret::ConstValue::ZeroSized { .. } => {
                    // Nothing to do
                }
            }
        }
        rustc_middle::mir::ConstantKind::Unevaluated(cv, _) => {
            // We should get there only if we don't need to evaluate
            // the constant: in this case we register its id
            assert!(extract_constants_at_top_level(mir_level));
            f(cv.def.did);
        }
    });
}

/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_dependency_item(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    id: DefId,
    kind: DeclKind,
    name: &Name,
) -> Result<()> {
    match ctx.rustc.hir().get_if_local(id) {
        None => {
            trace!("external expression");

            // Register the external expression as an opaque one.
            decls.register_opaque_declaration(ctx, &stack, id, kind, name);
            Ok(())
        }
        Some(node) => {
            trace!("local expression");
            match node {
                rustc_hir::Node::Item(item) => {
                    trace!("Item");
                    explore_local_hir_item(ctx, stack, decls, false, item)
                }
                rustc_hir::Node::ImplItem(impl_item) => {
                    trace!("Impl item");
                    explore_local_hir_impl_item(ctx, stack, decls, impl_item)
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }
}

/// Register the identifiers found in a function or global body.
///
/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_body(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    def_id: LocalDefId,
    deps: &mut DeclDependencies,
) -> Result<()> {
    // Retrieve the MIR code.
    let body = get_mir_for_def_id_and_level(ctx.rustc, def_id, ctx.mir_level);

    // Register the file from the span
    decls.register_file_from_span(ctx, body.span);

    trace!("Body: {:?}", body);

    // Visit the global dependencies if the MIR is not optimized.
    if extract_constants_at_top_level(ctx.mir_level) {
        // TODO: For now the order of dependencies export depend on the order
        // in which they are discovered. By storing their metadata, we would be
        // able to order them properly, without depending on the visit ordering.
        // Avoid registering globals in optimized MIR (they will be inlined).
        for b in body.basic_blocks.iter() {
            propagate_error(
                |f| visit_global_dependencies(ctx.mir_level, b, f),
                |id| {
                    let name = global_def_id_to_name(ctx.rustc, id);

                    if is_primitive_decl(DeclKind::Global, id, &name) {
                        return Ok(());
                    }
                    if !deps.insert_if_absent(id) {
                        return Ok(());
                    }

                    trace!("added constant dependency {:?} -> {}", def_id, name);
                    // The stack already contains the id of the body owner: no
                    // need to update it.
                    explore_dependency_item(ctx, stack.clone(), decls, id, DeclKind::Global, &name)
                },
            )?;
        }
    }

    // Start by registering the types found in the local variable declarations.
    // Note that those local variables include the parameters as well as the
    // return variable, and is thus enough to register the function signature.
    trace!("Locals: {:?}", body.local_decls);
    for v in body.local_decls.iter() {
        trace!("Local: {:?}", v);
        explore_mir_ty(ctx, stack.clone(), decls, &v.source_info.span, deps, &v.ty)?;
    }

    // Explore the body itself.
    // We need it to compute the dependencies between the functions and global
    // declarations, and also because some functions might be parameterized
    // with types which don't appear in the local variables (unlikely, but
    // can happen if some type parameters are not used).
    // We initially considered using visitors, but the MIR visitors return unit,
    // while we need to use a result type...
    // A basic block is a list of statements, followed by a terminator.
    for block in body.basic_blocks.iter() {
        // Statements
        for statement in block.statements.iter() {
            // We have to register the statements' spans (when we expand macro
            // for instance, those spans refer to the file where the macro is
            // defined).
            decls.register_file_from_span(ctx, statement.source_info.span);
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
                | mir::StatementKind::Deinit(_)
                | mir::StatementKind::Intrinsic(_)
                | mir::StatementKind::Nop => {
                    // Nothing to do
                }
                mir::StatementKind::Retag(_, _) => {
                    // retag statements are only used by MIRI, so we have nothing
                    // to do
                }
            }
        }

        // Terminator
        let terminator = block.terminator();
        // We have to register the terminator's span
        decls.register_file_from_span(ctx, terminator.source_info.span);
        match &terminator.kind {
            mir::TerminatorKind::Goto { target: _ }
            | mir::TerminatorKind::SwitchInt {
                discr: _,
                targets: _,
            }
            | mir::TerminatorKind::Resume
            | mir::TerminatorKind::Abort
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable
            | mir::TerminatorKind::Drop {
                place: _,
                target: _,
                unwind: _,
            }
            | mir::TerminatorKind::Assert {
                cond: _,
                expected: _,
                msg: _,
                target: _,
                cleanup: _,
            }
            | mir::TerminatorKind::FalseEdge {
                real_target: _,
                imaginary_target: _,
            }
            | mir::TerminatorKind::FalseUnwind {
                real_target: _,
                unwind: _,
            }
            | mir::TerminatorKind::DropAndReplace {
                place: _,
                value: _,
                target: _,
                unwind: _,
            } => {
                // Nothing to do
            }
            mir::TerminatorKind::Call {
                func,
                args,
                destination: _,
                target: _,
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
                explore_mir_substs(
                    ctx,
                    stack.clone(),
                    decls,
                    fn_span,
                    deps,
                    used_types,
                    &substs,
                )?;

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
                        explore_mir_ty(ctx, stack.clone(), decls, fn_span, deps, &ty)?;
                    }
                }

                // Note that we don't need to register the "bare" function
                // signature: all the types it contains are already covered
                // by the type arguments and the parameters.

                // The stack already contains the id of the body owner: no
                // need to update it.
                explore_dependency_item(ctx, stack.clone(), decls, fid, DeclKind::Fun, &name)?;
            }
            mir::TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => {
                trace!("terminator: Yield");
                span_err(
                    ctx.sess,
                    terminator.source_info.span,
                    "Yield is not supported",
                );
            }
            mir::TerminatorKind::GeneratorDrop => {
                trace!("terminator: GeneratorDrop");
                span_err(
                    ctx.sess,
                    terminator.source_info.span,
                    "Generators are not supported",
                );
            }
            mir::TerminatorKind::InlineAsm {
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
                    terminator.source_info.span,
                    "Inline ASM is not supported",
                );
            }
        }
    }

    Ok(())
}

/// Explore a transparent item with a body (either a fonction or a constant).
///
/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_local_item_with_body(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    local_id: LocalDefId,
    kind: DeclKind,
) -> Result<()> {
    // Update the stack
    let mut stack = stack;
    stack.push_back(local_id.to_def_id());

    decls.register_local_declaration(ctx, &stack, local_id, kind, |decls| {
        let mut deps = DeclDependencies::new();
        explore_body(ctx, stack.clone(), decls, local_id, &mut deps)?;
        Ok(deps)
    })
}

/// General function to register a MIR item. It is called on all the top-level
/// items. This includes: crate inclusions and `use` instructions (which are
/// ignored), but also type and functions declarations.
/// Note that this function checks if the item has been registered, and adds
/// its def_id to the list of registered items otherwise.
///
/// `stack`: the stack of definitions we explored before reaching this one.
/// This is useful for debugging purposes, to check how we reached a point
/// (in particular if we want to figure out where we failed to consider a
/// definition as opaque).
fn explore_local_hir_item(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    top_item: bool,
    item: &Item,
) -> Result<()> {
    trace!("{:?}", item);

    // Check if the item definition has already been registered (or is currently
    // being registered). If it is the case, return to prevent cycles. If not
    // registered yet, **do not immediately add it**: it may be an item we won't
    // translate (`use module`, `extern crate`...).
    let def_id = item.owner_id.to_def_id();
    if decls.knows(&def_id) {
        return Ok(());
    }

    // The annoying thing is that when iterating over the items in a crate, we
    // iterate over *all* the items, which is a problem with regards to the
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
                if ctx.crate_info.has_opaque_decl(&item_name) {
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
            explore_local_hir_type_item(ctx, stack, decls, item, def_id)
        }
        ItemKind::Fn(_, _, _) => explore_local_item_with_body(
            ctx,
            stack,
            decls,
            item.owner_id.to_def_id().as_local().unwrap(),
            DeclKind::Fun,
        ),
        ItemKind::Const(_, _) | ItemKind::Static(_, _, _) => {
            if extract_constants_at_top_level(ctx.mir_level) {
                explore_local_item_with_body(
                    ctx,
                    stack,
                    decls,
                    item.owner_id.to_def_id().as_local().unwrap(),
                    DeclKind::Global,
                )
            } else {
                // Avoid registering globals in optimized MIR (they will be inlined).
                Ok(())
            }
        }

        ItemKind::Impl(impl_block) => {
            trace!("impl");
            // Sanity checks
            translate_functions_to_ullbc::check_impl_item(impl_block);

            // Update the stack
            let mut stack = stack;
            stack.push_back(def_id);

            // Explore the items
            let hir_map = ctx.rustc.hir();
            for impl_item_ref in impl_block.items {
                // impl_item_ref only gives the reference of the impl item:
                // we need to look it up
                let impl_item = hir_map.impl_item(impl_item_ref.id);

                explore_local_hir_impl_item(ctx, stack.clone(), decls, impl_item)?;
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
            let opaque = ctx.crate_info.has_opaque_decl(&module_name);
            if opaque {
                // Ignore
                trace!("Ignoring module [{}] because marked as opaque", module_name);
                Ok(())
            } else {
                trace!("Diving into module [{}]", module_name);
                // Update the stack
                let mut stack = stack;
                stack.push_back(def_id);

                let hir_map = ctx.rustc.hir();
                for item_id in module.item_ids {
                    // Lookup and register the item
                    let item = hir_map.item(*item_id);
                    explore_local_hir_item(ctx, stack.clone(), decls, false, item)?;
                }
                Ok(())
            }
        }
        _ => {
            unimplemented!("{:?}", item.kind);
        }
    }
}

/// Explore an impl item (an item defined in an `impl` block).
///
/// `stack`: see the explanations for [explore_local_hir_item].
fn explore_local_hir_impl_item(
    ctx: &RegisterContext,
    stack: Vector<DefId>,
    decls: &mut DeclarationsRegister,
    impl_item: &ImplItem,
) -> Result<()> {
    // Check if the item has already been registered
    let def_id = impl_item.owner_id.to_def_id();
    if decls.knows(&def_id) {
        return Ok(());
    }

    // TODO: make a proper error message
    assert!(impl_item.defaultness == Defaultness::Final);

    // Match on the impl item kind
    match &impl_item.kind {
        ImplItemKind::Const(_, _) => Ok(()), // patch
        ImplItemKind::Type(_) => {
            // Note sure what to do with associated types yet
            unimplemented!();
        }
        ImplItemKind::Fn(_, _) => {
            let local_id = impl_item.owner_id.to_def_id().as_local().unwrap();
            explore_local_item_with_body(ctx, stack, decls, local_id, DeclKind::Fun)
        }
    }
}

/// General function to register the declarations in a crate.
pub fn explore_crate(
    crate_info: &CrateInfo,
    sess: &Session,
    tcx: TyCtxt,
    mir_level: MirLevel,
) -> Result<(HashMap<FileName, FileInfo>, RegisteredDeclarations)> {
    let ctx = RegisterContext {
        rustc: tcx,
        crate_info,
        sess,
        mir_level,
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
    let hir = tcx.hir();
    for item_id in hir.items() {
        let item_id = item_id.hir_id();
        let node = hir.find(item_id).unwrap();
        let item = match node {
            rustc_hir::Node::Item(item) => item,
            _ => unreachable!(),
        };
        let stack = Vector::new();
        explore_local_hir_item(&ctx, stack, &mut decls, true, item)?;
    }
    Ok(decls.get_files_and_declarations())
}
