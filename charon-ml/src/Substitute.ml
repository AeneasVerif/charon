(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

open Types
open TypesUtils
open GAstUtils
open Expressions
open LlbcAst

(* TODO: use Core.Fn.compose *)
let compose f g x = f (g x)

(* A substitution that takes a full variable as input *)
type subst = {
  r_subst : RegionId.id de_bruijn_var -> region;
      (** Remark: this might be called with bound regions with a negative
          DeBruijn index. A negative DeBruijn index means that the region
          is locally bound. *)
  ty_subst : TypeVarId.id de_bruijn_var -> ty;
  cg_subst : ConstGenericVarId.id de_bruijn_var -> const_generic;
      (** Substitution from *local* trait clause to trait instance *)
  tr_subst : TraitClauseId.id de_bruijn_var -> trait_instance_id;
      (** Substitution for the [Self] trait instance *)
  tr_self : trait_instance_id;
}

(* A substitution that applies to a specific binder. Use it with
   `subst_at_binder_zero` or `subst_free_vars` to get a real `subst`. *)
type single_binder_subst = {
  r_sb_subst : RegionId.id -> region;
  ty_sb_subst : TypeVarId.id -> ty;
  cg_sb_subst : ConstGenericVarId.id -> const_generic;
  tr_sb_subst : TraitClauseId.id -> trait_instance_id;
      (** Substitution for the [Self] trait instance *)
  tr_sb_self : trait_instance_id;
}

let empty_subst : subst =
  {
    r_subst = (fun var -> RVar var);
    ty_subst = (fun var -> TVar var);
    cg_subst = (fun var -> CgVar var);
    tr_subst = (fun var -> Clause var);
    tr_self = Self;
  }

(** The do-nothing substitution when used with `subst_free_vars` *)
let empty_bound_sb_subst : single_binder_subst =
  {
    r_sb_subst = compose empty_subst.r_subst zero_db_var;
    ty_sb_subst = compose empty_subst.ty_subst zero_db_var;
    cg_sb_subst = compose empty_subst.cg_subst zero_db_var;
    tr_sb_subst = compose empty_subst.tr_subst zero_db_var;
    tr_sb_self = empty_subst.tr_self;
  }

(** The do-nothing substitution when used with `subst_at_binder_zero` *)
let empty_free_sb_subst : single_binder_subst =
  let free x = Free x in
  {
    r_sb_subst = compose empty_subst.r_subst free;
    ty_sb_subst = compose empty_subst.ty_subst free;
    cg_sb_subst = compose empty_subst.cg_subst free;
    tr_sb_subst = compose empty_subst.tr_subst free;
    tr_sb_self = empty_subst.tr_self;
  }

let error_sb_subst : single_binder_subst =
  let error _ = failwith "Unexpected bound variable" in
  {
    r_sb_subst = compose empty_subst.r_subst error;
    ty_sb_subst = compose empty_subst.ty_subst error;
    cg_sb_subst = compose empty_subst.cg_subst error;
    tr_sb_subst = compose empty_subst.tr_subst error;
    tr_sb_self = empty_subst.tr_self;
  }

(** Substitute the free variables. *)
let subst_free_vars (subst : single_binder_subst) : subst =
  let subst_free subst nosubst = function
    | Free id -> subst id
    | var -> nosubst var
  in
  {
    r_subst = subst_free subst.r_sb_subst empty_subst.r_subst;
    ty_subst = subst_free subst.ty_sb_subst empty_subst.ty_subst;
    cg_subst = subst_free subst.cg_sb_subst empty_subst.cg_subst;
    tr_subst = subst_free subst.tr_sb_subst empty_subst.tr_subst;
    tr_self = subst.tr_sb_self;
  }

(** Substitute the variables bound by the currently innermost (level 0) binder. *)
let subst_at_binder_zero (subst : single_binder_subst) : subst =
  let subst_if_zero subst nosubst = function
    | Bound (0, id) -> subst id
    | var -> nosubst var
  in
  {
    r_subst = subst_if_zero subst.r_sb_subst empty_subst.r_subst;
    ty_subst = subst_if_zero subst.ty_sb_subst empty_subst.ty_subst;
    cg_subst = subst_if_zero subst.cg_sb_subst empty_subst.cg_subst;
    tr_subst = subst_if_zero subst.tr_sb_subst empty_subst.tr_subst;
    tr_self = subst.tr_sb_self;
  }

(** Substitute the variables bound by the current (level 0) binder, and shift variables to remove the current binder level. *)
let subst_remove_binder_zero (subst : single_binder_subst) : subst =
  let subst_remove_zero subst nosubst = function
    | Bound (0, id) -> subst id
    | Bound (dbid, varid) when dbid > 0 -> nosubst (Bound (dbid - 1, varid))
    | var -> nosubst var
  in
  {
    r_subst = subst_remove_zero subst.r_sb_subst empty_subst.r_subst;
    ty_subst = subst_remove_zero subst.ty_sb_subst empty_subst.ty_subst;
    cg_subst = subst_remove_zero subst.cg_sb_subst empty_subst.cg_subst;
    tr_subst = subst_remove_zero subst.tr_sb_subst empty_subst.tr_subst;
    tr_self = subst.tr_sb_self;
  }

(** Visitor that shifts all bound variables by the given delta *)
let st_shift_visitor =
  object (self)
    inherit [_] map_statement
    method! visit_de_bruijn_id delta dbid = dbid + delta
  end

(* Shift the the substitution under one binder. *)
let shift_subst (subst : subst) : subst =
  (* We decrement the input because the variables we encounter will be bound
     deeper. We shift the output so that it's valid at the new depth we're
     substituting it into. *)
  {
    r_subst =
      compose
        (st_shift_visitor#visit_region 1)
        (compose subst.r_subst decr_db_var);
    ty_subst =
      compose (st_shift_visitor#visit_ty 1) (compose subst.ty_subst decr_db_var);
    cg_subst =
      compose
        (st_shift_visitor#visit_const_generic 1)
        (compose subst.cg_subst decr_db_var);
    tr_subst =
      compose
        (st_shift_visitor#visit_trait_instance_id 1)
        (compose subst.tr_subst decr_db_var);
    tr_self = subst.tr_self;
  }

(** Visitor that applies the given substitution *)
let st_substitute_visitor =
  object (self)
    inherit [_] map_statement

    method! visit_binder visit_value (subst : subst) x =
      (* Note that we don't visit the bound variables. *)
      let { binder_params; binder_value } = x in
      (* Crucial: we shift the substitution to be valid under this binder. *)
      let binder_value = visit_value (shift_subst subst) binder_value in
      { binder_params; binder_value }

    method! visit_region_binder visit_value (subst : subst) x =
      (* Note that we don't visit the bound variables. *)
      let { binder_regions; binder_value } = x in
      (* Crucial: we shift the substitution to be valid under this binder. *)
      let binder_value = visit_value (shift_subst subst) binder_value in
      { binder_regions; binder_value }

    method! visit_RVar (subst : subst) var = subst.r_subst var
    method! visit_TVar (subst : subst) var = subst.ty_subst var
    method! visit_CgVar (subst : subst) var = subst.cg_subst var
    method! visit_Clause (subst : subst) var = subst.tr_subst var
    method! visit_Self (subst : subst) = subst.tr_self

    method! visit_type_var_id _ _ =
      (* We should never get here because we reimplemented [visit_TypeVar] *)
      raise (Failure "Unexpected")

    method! visit_const_generic_var_id _ _ =
      (* We should never get here because we reimplemented [visit_Var] *)
      raise (Failure "Unexpected")
  end

(** Substitute types variables and regions in a type.

    **IMPORTANT**: this doesn't normalize the types.
 *)
let ty_substitute (subst : subst) (ty : ty) : ty =
  st_substitute_visitor#visit_ty subst ty

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_ref_substitute (subst : subst) (tr : trait_ref) : trait_ref =
  st_substitute_visitor#visit_trait_ref subst tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_decl_ref_substitute (subst : subst) (tr : trait_decl_ref) :
    trait_decl_ref =
  st_substitute_visitor#visit_trait_decl_ref subst tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_instance_id_substitute (subst : subst) (tr : trait_instance_id) :
    trait_instance_id =
  st_substitute_visitor#visit_trait_instance_id subst tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let generic_args_substitute (subst : subst) (g : generic_args) : generic_args =
  st_substitute_visitor#visit_generic_args subst g

(** Substitute the predicates (clauses, outlives predicates, etc) inside these
    generic params. This leaves the list of parameters (regions, types and
    const_generics) untouched.
    **IMPORTANT**: this doesn't normalize the types. *)
let predicates_substitute (subst : subst) (p : generic_params) : generic_params
    =
  let visitor = st_substitute_visitor in
  let {
    regions;
    types;
    const_generics;
    trait_clauses;
    regions_outlive;
    types_outlive;
    trait_type_constraints;
  } =
    p
  in
  (* We leave the three lists of parameters untouched *)
  {
    regions;
    types;
    const_generics;
    trait_clauses = List.map (visitor#visit_trait_clause subst) trait_clauses;
    regions_outlive =
      List.map
        (visitor#visit_region_binder visitor#visit_region_outlives subst)
        regions_outlive;
    types_outlive =
      List.map
        (visitor#visit_region_binder visitor#visit_type_outlives subst)
        types_outlive;
    trait_type_constraints =
      List.map
        (visitor#visit_region_binder visitor#visit_trait_type_constraint subst)
        trait_type_constraints;
  }

let erase_regions_subst : subst =
  { empty_subst with r_subst = (fun _ -> RErased) }

(** Erase the region variables in a type *)
let erase_regions (ty : ty) : ty = ty_substitute erase_regions_subst ty

let trait_ref_erase_regions (tr : trait_ref) : trait_ref =
  trait_ref_substitute erase_regions_subst tr

let trait_instance_id_erase_regions (tr : trait_instance_id) : trait_instance_id
    =
  trait_instance_id_substitute erase_regions_subst tr

let generic_args_erase_regions (tr : generic_args) : generic_args =
  generic_args_substitute erase_regions_subst tr

(** Erase the regions in a type and perform a substitution *)
let erase_regions_substitute_types (subst : subst) (ty : ty) : ty =
  let subst = { subst with r_subst = (fun _ -> RErased) } in
  ty_substitute subst ty

(** Move the value out of the binder by shifting relevant binding levels.
    Errors if a variable bound in this binder is found. *)
let extract_from_binder (substituer : subst -> 'a -> 'a)
    (bound_val : 'a region_binder) : 'a =
  let subst = subst_remove_binder_zero error_sb_subst in
  substituer subst bound_val.binder_value

(** Substitute the free regions corresponding to each `var_id` with the
    corresponding provided region. *)
let make_region_subst (var_ids : RegionId.id list) (regions : region list) :
    RegionId.id -> region =
  let map = RegionId.Map.of_list (List.combine var_ids regions) in
  fun varid -> RegionId.Map.find varid map

let make_region_subst_from_vars (vars : region_var list) (regions : region list)
    : RegionId.id -> region =
  make_region_subst (List.map (fun (x : region_var) -> x.index) vars) regions

(** Create a type substitution from a list of type variable ids and a list of
    types (with which to substitute the type variable ids) *)
let make_type_subst (var_ids : TypeVarId.id list) (tys : ty list) :
    TypeVarId.id -> ty =
  let map = TypeVarId.Map.of_list (List.combine var_ids tys) in
  fun varid -> TypeVarId.Map.find varid map

let make_type_subst_from_vars (vars : type_var list) (tys : ty list) :
    TypeVarId.id -> ty =
  make_type_subst (List.map (fun (x : type_var) -> x.index) vars) tys

(** Create a const generic substitution from a list of const generic variable ids and a list of
    const generics (with which to substitute the const generic variable ids) *)
let make_const_generic_subst (var_ids : ConstGenericVarId.id list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  let map = ConstGenericVarId.Map.of_list (List.combine var_ids cgs) in
  fun varid -> ConstGenericVarId.Map.find varid map

let make_const_generic_subst_from_vars (vars : const_generic_var list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  make_const_generic_subst
    (List.map (fun (x : const_generic_var) -> x.index) vars)
    cgs

(** Create a trait substitution from a list of trait clause ids and a list of
    trait refs *)
let make_trait_subst (var_ids : TraitClauseId.id list)
    (trs : trait_instance_id list) : TraitClauseId.id -> trait_instance_id =
  let map = TraitClauseId.Map.of_list (List.combine var_ids trs) in
  fun varid -> TraitClauseId.Map.find varid map

let make_trait_subst_from_clauses (clauses : trait_clause list)
    (trs : trait_ref list) : TraitClauseId.id -> trait_instance_id =
  make_trait_subst
    (List.map (fun (x : trait_clause) -> x.clause_id) clauses)
    (List.map (fun (x : trait_ref) -> x.trait_id) trs)

let make_sb_subst_from_generics (params : generic_params) (args : generic_args)
    : single_binder_subst =
  let r_sb_subst = make_region_subst_from_vars params.regions args.regions in
  let ty_sb_subst = make_type_subst_from_vars params.types args.types in
  let cg_sb_subst =
    make_const_generic_subst_from_vars params.const_generics args.const_generics
  in
  let tr_sb_subst =
    make_trait_subst_from_clauses params.trait_clauses args.trait_refs
  in
  { r_sb_subst; ty_sb_subst; cg_sb_subst; tr_sb_subst; tr_sb_self = Self }

let make_subst_from_generics (params : generic_params) (args : generic_args) :
    subst =
  subst_free_vars (make_sb_subst_from_generics params args)

let make_subst_from_generics_erase_regions (params : generic_params)
    (generics : generic_args) : subst =
  let generics = generic_args_erase_regions generics in
  let subst = make_subst_from_generics params generics in
  { subst with r_subst = (fun _ -> RErased) }

(** Instantiate the type variables in an ADT definition, and return, for
    every variant, the list of the types of its fields.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_variants_fields_types (def : type_decl)
    (generics : generic_args) : (VariantId.id option * ty list) list =
  let subst = make_subst_from_generics def.generics generics in
  let (variants_fields : (VariantId.id option * field list) list) =
    match def.kind with
    | Enum variants ->
        List.mapi (fun i v -> (Some (VariantId.of_int i), v.fields)) variants
    | Struct fields | Union fields -> [ (None, fields) ]
    | Alias _ | Opaque | TError _ ->
        raise
          (Failure
             ("Can't retrieve the variants of non-adt type: "
             ^ show_name def.item_meta.name))
  in
  List.map
    (fun (id, fields) ->
      (id, List.map (fun f -> ty_substitute subst f.field_ty) fields))
    variants_fields

(** Instantiate the type variables in an ADT definition, and return the list
    of types of the fields for the chosen variant.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_field_types (def : type_decl)
    (opt_variant_id : VariantId.id option) (generics : generic_args) : ty list =
  (* For now, check that there are no clauses - otherwise we might need
     to normalize the types *)
  assert (def.generics.trait_clauses = []);
  let subst = make_subst_from_generics def.generics generics in
  let fields = type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute subst f.field_ty) fields

(** Apply a type substitution to a place *)
let place_substitute (subst : subst) (p : place) : place =
  (* There is in fact nothing to do *)
  st_substitute_visitor#visit_place subst p

(** Apply a type substitution to an operand *)
let operand_substitute (subst : subst) (op : operand) : operand =
  st_substitute_visitor#visit_operand subst op

(** Apply a type substitution to an rvalue *)
let rvalue_substitute (subst : subst) (rv : rvalue) : rvalue =
  st_substitute_visitor#visit_rvalue subst rv

(** Apply a type substitution to an assertion *)
let assertion_substitute (subst : subst) (a : assertion) : assertion =
  st_substitute_visitor#visit_assertion subst a

(** Apply a type substitution to a call *)
let call_substitute (subst : subst) (call : call) : call =
  st_substitute_visitor#visit_call subst call

(** Apply a type substitution to a statement *)
let statement_substitute (subst : subst) (st : statement) : statement =
  st_substitute_visitor#visit_statement subst st

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_body_substitute_in_body (subst : subst) (body : fun_body) :
    var list * statement =
  let locals =
    List.map
      (fun (v : var) -> { v with var_ty = ty_substitute subst v.var_ty })
      body.locals.vars
  in
  let body = statement_substitute subst body.body in
  (locals, body)

let trait_type_constraint_substitute (subst : subst)
    (ttc : trait_type_constraint) : trait_type_constraint =
  let { trait_ref; type_name; ty } = ttc in
  let visitor = st_substitute_visitor in
  let trait_ref = visitor#visit_trait_ref subst trait_ref in
  let ty = visitor#visit_ty subst ty in
  { trait_ref; type_name; ty }

(** Substitute variable identifiers in a type *)
let statement_substitute_ids (ty_subst : TypeVarId.id -> TypeVarId.id)
    (cg_subst : ConstGenericVarId.id -> ConstGenericVarId.id) (ty : ty) : ty =
  let visitor =
    object
      inherit [_] map_ty
      method visit_'r _ r = r
      method! visit_type_var_id _ id = ty_subst id
      method! visit_const_generic_var_id _ id = cg_subst id
    end
  in
  visitor#visit_ty () ty

(** Remove this binder by substituting the provided arguments for each bound
    variable. The `substitutor` argument must be the appropriate
    `st_substitute_visitor` method. *)
let apply_args_to_binder (args : generic_args) (substitutor : subst -> 'a -> 'a)
    (binder : 'a binder) : 'a =
  substitutor
    (subst_remove_binder_zero
       (make_sb_subst_from_generics binder.binder_params args))
    binder.binder_value

(** Remove this binder by substituting the provided arguments for each bound
    variable. The `substitutor` argument must be the appropriate
    `st_substitute_visitor` method. *)
let apply_args_to_item_binder (args : generic_args)
    (substitutor : subst -> 'a -> 'a) (binder : 'a item_binder) : 'a =
  substitutor
    (subst_free_vars
       (make_sb_subst_from_generics binder.item_binder_params args))
    binder.item_binder_value

(** Helper *)
let instantiate_method item_generics method_generics
    (bound_fn : fun_decl_ref binder item_binder) : fun_decl_ref =
  apply_args_to_binder method_generics st_substitute_visitor#visit_fun_decl_ref
    (apply_args_to_item_binder item_generics
       (st_substitute_visitor#visit_binder
          st_substitute_visitor#visit_fun_decl_ref)
       bound_fn)

(** Like lookup_trait_decl_provided_method, but also correctly substitutes the generics. *)
let lookup_and_subst_trait_decl_method (tdecl : trait_decl)
    (name : trait_item_name) decl_generics method_generics : fun_decl_ref option
    =
  Option.map
    (instantiate_method decl_generics method_generics)
    (lookup_trait_decl_method tdecl name)

(** Like lookup_trait_decl_provided_method, but also correctly substitutes the generics. *)
let lookup_and_subst_trait_decl_provided_method (tdecl : trait_decl)
    (name : trait_item_name) decl_generics method_generics : fun_decl_ref option
    =
  Option.map
    (instantiate_method decl_generics method_generics)
    (lookup_trait_decl_provided_method tdecl name)

(** Like lookup_trait_decl_required_method, but also correctly substitutes the generics. *)
let lookup_and_subst_trait_decl_required_method (tdecl : trait_decl)
    (name : trait_item_name) decl_generics method_generics : fun_decl_ref option
    =
  Option.map
    (instantiate_method decl_generics method_generics)
    (lookup_trait_decl_required_method tdecl name)

(** Like lookup_trait_impl_provided_method, but also correctly substitutes the generics. *)
let lookup_and_subst_trait_impl_provided_method (timpl : trait_impl)
    (name : trait_item_name) impl_generics method_generics : fun_decl_ref option
    =
  Option.map
    (instantiate_method impl_generics method_generics)
    (lookup_trait_impl_provided_method timpl name)

(** Like lookup_trait_impl_required_method, but also correctly substitutes the generics. *)
let lookup_and_subst_trait_impl_required_method (timpl : trait_impl)
    (name : trait_item_name) impl_generics method_generics : fun_decl_ref option
    =
  Option.map
    (instantiate_method impl_generics method_generics)
    (lookup_trait_impl_required_method timpl name)
