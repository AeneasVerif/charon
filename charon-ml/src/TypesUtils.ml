open Collections
open Types
open Utils

module RegionOrderedType : OrderedType with type t = region = struct
  type t = region

  let compare = compare_region
  let to_string = show_region
  let pp_t = pp_region
  let show_t = show_region
end

module RegionMap = Collections.MakeMap (RegionOrderedType)
module RegionSet = Collections.MakeSet (RegionOrderedType)

let to_name (ls : string list) : name =
  List.map (fun s -> PeIdent (s, Disambiguator.zero)) ls

let as_ident (e : path_elem) : string =
  match e with PeIdent (s, _) -> s | _ -> raise (Failure "Unexpected")

let type_decl_is_opaque (d : type_decl) : bool =
  match d.kind with Struct _ | Enum _ -> false | Opaque -> true

(** Retrieve the list of fields for the given variant of a {!Charon.Types.type_decl}.

    Raises [Invalid_argument] if the arguments are incorrect.
 *)
let type_decl_get_fields (def : type_decl)
    (opt_variant_id : VariantId.id option) : field list =
  match (def.kind, opt_variant_id) with
  | Enum variants, Some variant_id -> (VariantId.nth variants variant_id).fields
  | Struct fields, None -> fields
  | _ ->
      let opt_variant_id =
        match opt_variant_id with None -> "None" | Some _ -> "Some"
      in
      raise
        (Invalid_argument
           ("The variant id should be [Some] if and only if the definition is \
             an enumeration:\n\
             - def: " ^ show_type_decl def ^ "\n- opt_variant_id: "
          ^ opt_variant_id))

let type_decl_is_enum (def : type_decl) : bool =
  match def.kind with Struct _ -> false | Enum _ -> true | Opaque -> false

(** Return [true] if a {!type:Charon.Types.ty} is actually [unit] *)
let ty_is_unit (ty : ty) : bool =
  match ty with
  | TAdt
      (TTuple, { regions = []; types = []; const_generics = []; trait_refs = _ })
    ->
      true
  | _ -> false

let ty_is_adt (ty : ty) : bool =
  match ty with TAdt (_, _) -> true | _ -> false

let ty_as_adt (ty : ty) : type_id * generic_args =
  match ty with
  | TAdt (id, generics) -> (id, generics)
  | _ -> raise (Failure "Unreachable")

let ty_as_ref (ty : ty) : region * ty * ref_kind =
  match ty with
  | TRef (r, ref_ty, kind) -> (r, ref_ty, kind)
  | _ -> raise (Failure "Unreachable")

let ty_is_custom_adt (ty : ty) : bool =
  match ty with TAdt (TAdtId _, _) -> true | _ -> false

let ty_as_custom_adt (ty : ty) : TypeDeclId.id * generic_args =
  match ty with
  | TAdt (TAdtId id, generics) -> (id, generics)
  | _ -> raise (Failure "Unreachable")

let ty_as_literal (ty : ty) : literal_type =
  match ty with TLiteral lty -> lty | _ -> raise (Failure "Unreachable")

let const_generic_as_literal (cg : const_generic) : Values.literal =
  match cg with CgValue v -> v | _ -> raise (Failure "Unreachable")

let trait_instance_id_as_trait_impl (id : trait_instance_id) : trait_impl_id =
  match id with TraitImpl id -> id | _ -> raise (Failure "Unreachable")

let empty_generic_args : generic_args =
  { regions = []; types = []; const_generics = []; trait_refs = [] }

let mk_generic_args (regions : region list) (types : ty list)
    (const_generics : const_generic list) (trait_refs : trait_ref list) :
    generic_args =
  { regions; types; const_generics; trait_refs }

let mk_generic_args_from_types (types : ty list) : generic_args =
  { regions = []; types; const_generics = []; trait_refs = [] }

let empty_generic_params : generic_params =
  { regions = []; types = []; const_generics = []; trait_clauses = [] }

let empty_predicates : predicates =
  { regions_outlive = []; types_outlive = []; trait_type_constraints = [] }

let merge_generic_args (g1 : generic_args) (g2 : generic_args) : generic_args =
  let { regions = r1; types = tys1; const_generics = cgs1; trait_refs = tr1 } =
    g1
  in
  let { regions = r2; types = tys2; const_generics = cgs2; trait_refs = tr2 } =
    g2
  in
  {
    regions = r1 @ r2;
    types = tys1 @ tys2;
    const_generics = cgs1 @ cgs2;
    trait_refs = tr1 @ tr2;
  }

(** The unit type *)
let mk_unit_ty : ty = TAdt (TTuple, empty_generic_args)

(** The usize type *)
let mk_usize_ty : ty = TLiteral (TInteger Usize)

(** Deconstruct a type of the form [Box<T>] to retrieve the [T] inside *)
let ty_get_box (box_ty : ty) : ty =
  match box_ty with
  | TAdt (TAssumed TBox, { types = [ boxed_ty ]; _ }) -> boxed_ty
  | _ -> raise (Failure "Not a boxed type")

(** Deconstruct a type of the form [&T] or [&mut T] to retrieve the [T] (and
    the borrow kind, etc.)
 *)
let ty_get_ref (ty : ty) : region * ty * ref_kind =
  match ty with
  | TRef (r, ty, ref_kind) -> (r, ty, ref_kind)
  | _ -> raise (Failure "Not a ref type")

let mk_ref_ty (r : region) (ty : ty) (ref_kind : ref_kind) : ty =
  TRef (r, ty, ref_kind)

(** Make a box type *)
let mk_box_ty (ty : ty) : ty =
  TAdt (TAssumed TBox, mk_generic_args_from_types [ ty ])

(** Check if a region is in a set of regions.

    This function should be used on non-erased and non-bound regions.
    For sanity, we raise exceptions if this is not the case.
 *)
let region_in_set (r : region) (rset : RegionId.Set.t) : bool =
  match r with
  | RStatic -> false
  | RErased ->
      raise (Failure "region_in_set shouldn't be called on erased regions")
  | RBVar _ ->
      raise (Failure "region_in_set shouldn't be called on bound regions")
  | RFVar id -> RegionId.Set.mem id rset

(** Return the set of regions in an type - TODO: add static?

    This function should be used on non-erased and non-bound regions.
    For sanity, we raise exceptions if this is not the case.
 *)
let ty_regions (ty : ty) : RegionId.Set.t =
  let s = ref RegionId.Set.empty in
  let add_region (r : region) =
    match r with
    | RStatic -> () (* TODO: static? *)
    | RErased ->
        raise (Failure "ty_regions shouldn't be called on erased regions")
    | RBVar _ ->
        raise (Failure "region_in_set shouldn't be called on bound regions")
    | RFVar rid -> s := RegionId.Set.add rid !s
  in
  let obj =
    object
      inherit [_] iter_ty
      method! visit_region _env r = add_region r
    end
  in
  (* Explore the type *)
  obj#visit_ty () ty;
  (* Return the set of accumulated regions *)
  !s

(* TODO: merge with ty_has_regions_in_set *)
let ty_regions_intersect (ty : ty) (regions : RegionId.Set.t) : bool =
  let ty_regions = ty_regions ty in
  not (RegionId.Set.disjoint ty_regions regions)

(** Check if a {!type:Charon.Types.ty} contains regions from a given set *)
let ty_has_regions_in_set (rset : RegionId.Set.t) (ty : ty) : bool =
  let obj =
    object
      inherit [_] iter_ty
      method! visit_region _ r = if region_in_set r rset then raise Found
    end
  in
  try
    obj#visit_ty () ty;
    false
  with Found -> true

(** Return true if a type is "primitively copyable".
  *
  * "Primitively copyable" means that copying instances of this type doesn't
  * require calling dedicated functions defined through the [Copy] trait. It
  * is the case for types like integers, shared borrows, etc.
  *
  * Generally, ADTs are not primitively copyable. But some ADTs from the standard
  * library like [Option] are. As it is not easy to check which external ADTs
  * are primitively copyable (we would need to perform a lookup of the ADT
  * definition and check its name, for instance) we don't fully check it.
  *)
let rec ty_is_primitively_copyable (ty : ty) : bool =
  match ty with
  | TAdt (TAdtId _, generics) ->
      List.for_all ty_is_primitively_copyable generics.types
  | TAdt (TAssumed (TBox | TStr | TSlice), _) -> false
  | TAdt ((TTuple | TAssumed TArray), generics) ->
      List.for_all ty_is_primitively_copyable generics.types
  | TVar _ | TNever -> false
  | TLiteral (TBool | TChar | TInteger _) -> true
  | TTraitType _ | TArrow (_, _, _) -> false
  | TRef (_, _, RMut) -> false
  | TRef (_, _, RShared) -> true
  | TRawPtr (_, _) ->
      (* Not sure what to do here, so being conservative *)
      false
