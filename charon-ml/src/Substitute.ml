(** This file implements various substitution utilities to instantiate types,
    function bodies, etc.
 *)

open Types
open TypesUtils
open Expressions
open LlbcAst

type subst = {
  r_subst : region -> region;
      (** Remark: this might be called with bound regions with a negative
          DeBruijn index. A negative DeBruijn index means that the region
          is locally bound. *)
  ty_subst : TypeVarId.id -> ty;
  cg_subst : ConstGenericVarId.id -> const_generic;
      (** Substitution from *local* trait clause to trait instance *)
  tr_subst : TraitClauseId.id -> trait_instance_id;
      (** Substitution for the [Self] trait instance *)
  tr_self : trait_instance_id;
}

let empty_subst : subst =
  {
    r_subst = (fun x -> x);
    ty_subst = (fun id -> TVar id);
    cg_subst = (fun id -> CgVar id);
    tr_subst = (fun id -> Clause id);
    tr_self = Self;
  }

let st_substitute_visitor (subst : subst) =
  object (self)
    inherit [_] map_statement
    method! visit_region (subst : subst) r = subst.r_subst r

    (** We need to properly handle the DeBruijn indices *)
    method! visit_TArrow subst regions inputs output =
      (* Decrement the DeBruijn indices before calling the substitution *)
      let r_subst r =
        match r with
        | RBVar (db, rid) -> subst.r_subst (RBVar (db - 1, rid))
        | _ -> subst.r_subst r
      in
      let subst = { subst with r_subst } in
      (* Note that we ignore the bound regions variables *)
      let inputs = List.map (self#visit_ty subst) inputs in
      let output = self#visit_ty subst output in
      TArrow (regions, inputs, output)

    method! visit_TVar (subst : subst) id = subst.ty_subst id

    method! visit_type_var_id _ _ =
      (* We should never get here because we reimplemented [visit_TypeVar] *)
      raise (Failure "Unexpected")

    method! visit_CgVar _ id = subst.cg_subst id

    method! visit_const_generic_var_id _ _ =
      (* We should never get here because we reimplemented [visit_Var] *)
      raise (Failure "Unexpected")

    method! visit_Clause (subst : subst) id = subst.tr_subst id
    method! visit_Self (subst : subst) = subst.tr_self
  end

(** Substitute types variables and regions in a type.

    **IMPORTANT**: this doesn't normalize the types.
 *)
let ty_substitute (subst : subst) (ty : ty) : ty =
  let visitor = st_substitute_visitor subst in
  visitor#visit_ty subst ty

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_ref_substitute (subst : subst) (tr : trait_ref) : trait_ref =
  let visitor = st_substitute_visitor subst in
  visitor#visit_trait_ref subst tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let trait_instance_id_substitute (subst : subst) (tr : trait_instance_id) :
    trait_instance_id =
  let visitor = st_substitute_visitor subst in
  visitor#visit_trait_instance_id subst tr

(** **IMPORTANT**: this doesn't normalize the types. *)
let generic_args_substitute (subst : subst) (g : generic_args) : generic_args =
  let visitor = st_substitute_visitor subst in
  visitor#visit_generic_args subst g

let predicates_substitute (subst : subst) (p : predicates) : predicates =
  let visitor = st_substitute_visitor subst in
  visitor#visit_predicates subst p

let erase_regions_subst : subst =
  {
    r_subst = (fun _ -> RErased);
    ty_subst = (fun vid -> TVar vid);
    cg_subst = (fun id -> CgVar id);
    tr_subst = (fun id -> Clause id);
    tr_self = Self;
  }

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
let erase_regions_substitute_types (ty_subst : TypeVarId.id -> ty)
    (cg_subst : ConstGenericVarId.id -> const_generic)
    (tr_subst : TraitClauseId.id -> trait_instance_id)
    (tr_self : trait_instance_id) (ty : ty) : ty =
  let r_subst (_ : region) : region = RErased in
  let subst = { r_subst; ty_subst; cg_subst; tr_subst; tr_self } in
  ty_substitute subst ty

(** Create a region substitution from a list of region variable ids and a list of
    regions (with which to substitute the region variable ids *)
let make_region_subst (var_ids : RegionVarId.id list) (regions : region list) :
    region -> region =
  let ls = List.combine var_ids regions in
  let mp =
    List.fold_left
      (fun mp (k, v) -> RegionVarId.Map.add k v mp)
      RegionVarId.Map.empty ls
  in
  fun r ->
    match r with
    | RStatic | RErased -> r
    | RFVar _ -> raise (Failure "Unexpected")
    | RBVar (bdid, id) ->
        (* Only substitute the bound regions with DeBruijn index equal to 0 *)
        if bdid = 0 then RegionVarId.Map.find id mp else r

let make_region_subst_from_vars (vars : region_var list) (regions : region list)
    : region -> region =
  make_region_subst (List.map (fun (x : region_var) -> x.index) vars) regions

(** Create a type substitution from a list of type variable ids and a list of
    types (with which to substitute the type variable ids) *)
let make_type_subst (var_ids : TypeVarId.id list) (tys : ty list) :
    TypeVarId.id -> ty =
  let ls = List.combine var_ids tys in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TypeVarId.Map.add k v mp)
      TypeVarId.Map.empty ls
  in
  fun id -> TypeVarId.Map.find id mp

let make_type_subst_from_vars (vars : type_var list) (tys : ty list) :
    TypeVarId.id -> ty =
  make_type_subst (List.map (fun (x : type_var) -> x.index) vars) tys

(** Create a const generic substitution from a list of const generic variable ids and a list of
    const generics (with which to substitute the const generic variable ids) *)
let make_const_generic_subst (var_ids : ConstGenericVarId.id list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  let ls = List.combine var_ids cgs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> ConstGenericVarId.Map.add k v mp)
      ConstGenericVarId.Map.empty ls
  in
  fun id -> ConstGenericVarId.Map.find id mp

let make_const_generic_subst_from_vars (vars : const_generic_var list)
    (cgs : const_generic list) : ConstGenericVarId.id -> const_generic =
  make_const_generic_subst
    (List.map (fun (x : const_generic_var) -> x.index) vars)
    cgs

(** Create a trait substitution from a list of trait clause ids and a list of
    trait refs *)
let make_trait_subst (clause_ids : TraitClauseId.id list) (trs : trait_ref list)
    : TraitClauseId.id -> trait_instance_id =
  let ls = List.combine clause_ids trs in
  let mp =
    List.fold_left
      (fun mp (k, v) -> TraitClauseId.Map.add k (TraitRef v) mp)
      TraitClauseId.Map.empty ls
  in
  fun id -> TraitClauseId.Map.find id mp

let make_trait_subst_from_clauses (clauses : trait_clause list)
    (trs : trait_ref list) : TraitClauseId.id -> trait_instance_id =
  make_trait_subst
    (List.map (fun (x : trait_clause) -> x.clause_id) clauses)
    trs

let make_subst_from_generics (params : generic_params) (args : generic_args)
    (tr_self : trait_instance_id) : subst =
  let r_subst = make_region_subst_from_vars params.regions args.regions in
  let ty_subst = make_type_subst_from_vars params.types args.types in
  let cg_subst =
    make_const_generic_subst_from_vars params.const_generics args.const_generics
  in
  let tr_subst =
    make_trait_subst_from_clauses params.trait_clauses args.trait_refs
  in
  { r_subst; ty_subst; cg_subst; tr_subst; tr_self }

let make_subst_from_generics_erase_regions (params : generic_params)
    (generics : generic_args) (tr_self : trait_instance_id) =
  let generics = generic_args_erase_regions generics in
  let tr_self = trait_instance_id_erase_regions tr_self in
  let subst = make_subst_from_generics params generics tr_self in
  { subst with r_subst = (fun _ -> RErased) }

(** Instantiate the type variables in an ADT definition, and return, for
    every variant, the list of the types of its fields.

    **IMPORTANT**: this function doesn't normalize the types, you may want to
    use the [AssociatedTypes] equivalent instead.
*)
let type_decl_get_instantiated_variants_fields_types (def : type_decl)
    (generics : generic_args) : (VariantId.id option * ty list) list =
  (* There shouldn't be any reference to Self *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics def.generics generics tr_self in
  let (variants_fields : (VariantId.id option * field list) list) =
    match def.kind with
    | Enum variants ->
        List.mapi (fun i v -> (Some (VariantId.of_int i), v.fields)) variants
    | Struct fields -> [ (None, fields) ]
    | Opaque ->
        raise
          (Failure
             ("Can't retrieve the variants of an opaque type: "
            ^ show_name def.name))
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
  (* There shouldn't be any reference to Self *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let subst = make_subst_from_generics def.generics generics tr_self in
  let fields = type_decl_get_fields def opt_variant_id in
  List.map (fun f -> ty_substitute subst f.field_ty) fields

(** Apply a type substitution to a place *)
let place_substitute (subst : subst) (p : place) : place =
  (* There is in fact nothing to do *)
  (st_substitute_visitor subst)#visit_place subst p

(** Apply a type substitution to an operand *)
let operand_substitute (subst : subst) (op : operand) : operand =
  (st_substitute_visitor subst)#visit_operand subst op

(** Apply a type substitution to an rvalue *)
let rvalue_substitute (subst : subst) (rv : rvalue) : rvalue =
  (st_substitute_visitor subst)#visit_rvalue subst rv

(** Apply a type substitution to an assertion *)
let assertion_substitute (subst : subst) (a : assertion) : assertion =
  (st_substitute_visitor subst)#visit_assertion subst a

(** Apply a type substitution to a call *)
let call_substitute (subst : subst) (call : call) : call =
  (st_substitute_visitor subst)#visit_call subst call

(** Apply a type substitution to a statement *)
let statement_substitute (subst : subst) (st : statement) : statement =
  (st_substitute_visitor subst)#visit_statement subst st

(** Apply a type substitution to a function body. Return the local variables
    and the body. *)
let fun_body_substitute_in_body (subst : subst) (body : fun_body) :
    var list * statement =
  let locals =
    List.map
      (fun (v : var) -> { v with var_ty = ty_substitute subst v.var_ty })
      body.locals
  in
  let body = statement_substitute subst body.body in
  (locals, body)

let trait_type_constraint_substitute (subst : subst)
    (ttc : trait_type_constraint) : trait_type_constraint =
  let { trait_ref; generics; type_name; ty } = ttc in
  let visitor = st_substitute_visitor subst in
  let trait_ref = visitor#visit_trait_ref subst trait_ref in
  let generics = visitor#visit_generic_args subst generics in
  let ty = visitor#visit_ty subst ty in
  { trait_ref; generics; type_name; ty }

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
