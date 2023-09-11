open Types
open Utils

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

(** Return [true] if a {!type: Types.ty} is actually [unit] *)
let ty_is_unit (ty : 'r ty) : bool =
  match ty with
  | Adt
      (Tuple, { regions = []; types = []; const_generics = []; trait_refs = _ })
    ->
      true
  | _ -> false

let ty_is_adt (ty : 'r ty) : bool =
  match ty with Adt (_, _) -> true | _ -> false

let ty_as_adt (ty : 'r ty) : type_id * 'r generic_args =
  match ty with
  | Adt (id, generics) -> (id, generics)
  | _ -> raise (Failure "Unreachable")

let ty_as_ref (ty : 'r ty) : 'r * 'r ty * ref_kind =
  match ty with
  | Ref (r, ref_ty, kind) -> (r, ref_ty, kind)
  | _ -> raise (Failure "Unreachable")

let ty_is_custom_adt (ty : 'r ty) : bool =
  match ty with Adt (AdtId _, _) -> true | _ -> false

let ty_as_custom_adt (ty : 'r ty) : TypeDeclId.id * 'r generic_args =
  match ty with
  | Adt (AdtId id, generics) -> (id, generics)
  | _ -> raise (Failure "Unreachable")

let ty_as_literal (ty : 'r ty) : literal_type =
  match ty with Literal lty -> lty | _ -> raise (Failure "Unreachable")

let const_generic_as_literal (cg : const_generic) : PrimitiveValues.literal =
  match cg with ConstGenericValue v -> v | _ -> raise (Failure "Unreachable")

let trait_instance_id_as_trait_impl (id : 'r trait_instance_id) : trait_impl_id
    =
  match id with TraitImpl id -> id | _ -> raise (Failure "Unreachable")

let mk_empty_generic_args : 'r generic_args =
  { regions = []; types = []; const_generics = []; trait_refs = [] }

let mk_generic_args (regions : 'r list) (types : 'r ty list)
    (const_generics : const_generic list) (trait_refs : 'r trait_ref list) :
    'r generic_args =
  { regions; types; const_generics; trait_refs }

let mk_generic_args_from_types (types : 'r ty list) : 'r generic_args =
  { regions = []; types; const_generics = []; trait_refs = [] }

let mk_empty_generic_params : generic_params =
  { regions = []; types = []; const_generics = []; trait_clauses = [] }

let mk_empty_predicates : predicates =
  { regions_outlive = []; types_outlive = []; trait_type_constraints = [] }

let merge_generic_args (g1 : 'r generic_args) (g2 : 'r generic_args) :
    'r generic_args =
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
let mk_unit_ty : 'r ty = Adt (Tuple, mk_empty_generic_args)

(** The usize type *)
let mk_usize_ty : 'r ty = Literal (Integer Usize)

(** Deconstruct a type of the form [Box<T>] to retrieve the [T] inside *)
let ty_get_box (box_ty : ety) : ety =
  match box_ty with
  | Adt (Assumed Box, { types = [ boxed_ty ]; _ }) -> boxed_ty
  | _ -> raise (Failure "Not a boxed type")

(** Deconstruct a type of the form [&T] or [&mut T] to retrieve the [T] (and
    the borrow kind, etc.)
 *)
let ty_get_ref (ty : 'r ty) : 'r * 'r ty * ref_kind =
  match ty with
  | Ref (r, ty, ref_kind) -> (r, ty, ref_kind)
  | _ -> raise (Failure "Not a ref type")

let mk_ref_ty (r : 'r) (ty : 'r ty) (ref_kind : ref_kind) : 'r ty =
  Ref (r, ty, ref_kind)

(** Make a box type *)
let mk_box_ty (ty : 'r ty) : 'r ty =
  Adt (Assumed Box, mk_generic_args_from_types [ ty ])

(** Make a vec type *)
let mk_vec_ty (ty : 'r ty) : 'r ty =
  Adt (Assumed Vec, mk_generic_args_from_types [ ty ])

(** Check if a region is in a set of regions *)
let region_in_set (r : RegionId.id region) (rset : RegionId.Set.t) : bool =
  match r with Static -> false | Var id -> RegionId.Set.mem id rset

(** Return the set of regions in an rty *)
let rty_regions (ty : rty) : RegionId.Set.t =
  let s = ref RegionId.Set.empty in
  let add_region (r : RegionId.id region) =
    match r with Static -> () | Var rid -> s := RegionId.Set.add rid !s
  in
  let obj =
    object
      inherit [_] iter_ty
      method! visit_'r _env r = add_region r
    end
  in
  (* Explore the type *)
  obj#visit_ty () ty;
  (* Return the set of accumulated regions *)
  !s

let rty_regions_intersect (ty : rty) (regions : RegionId.Set.t) : bool =
  let ty_regions = rty_regions ty in
  not (RegionId.Set.disjoint ty_regions regions)

(** Convert an {!Types.ety}, containing no region variables, to an {!Types.rty}
    or an {!Types.sty}.

    In practice, it is the identity.
 *)
let rec ety_no_regions_to_gr_ty (ty : ety) : 'a gr_ty =
  match ty with
  | Adt (type_id, generics) ->
      let generics = egeneric_args_no_regions_to_gr_generic_args generics in
      Adt (type_id, generics)
  | TypeVar v -> TypeVar v
  | Literal ty -> Literal ty
  | Never -> Never
  | TraitType (trait_ref, generics, type_name) ->
      let trait_ref = etrait_ref_no_regions_to_gr_trait_ref trait_ref in
      let generics = egeneric_args_no_regions_to_gr_generic_args generics in
      TraitType (trait_ref, generics, type_name)
  | Ref (_, _, _) ->
      raise
        (Failure
           "Can't convert a ref with erased regions to a ref with non-erased \
            regions")

and egeneric_args_no_regions_to_gr_generic_args (g : egeneric_args) :
    'a region generic_args =
  let { regions; types; const_generics; trait_refs } = g in
  assert (regions = []);
  let types = List.map ety_no_regions_to_gr_ty types in
  let trait_refs = List.map etrait_ref_no_regions_to_gr_trait_ref trait_refs in
  { regions = []; types; const_generics; trait_refs }

and etrait_ref_no_regions_to_gr_trait_ref (tr : etrait_ref) :
    'a region trait_ref =
  let ({ trait_id; generics; trait_decl_ref } : etrait_ref) = tr in
  let trait_id =
    etrait_instance_id_no_regions_to_gr_trait_instance_id trait_id
  in
  let generics = egeneric_args_no_regions_to_gr_generic_args generics in
  let trait_decl_ref =
    etrait_decl_ref_no_regions_to_gr_trait_decl_ref trait_decl_ref
  in
  { trait_id; generics; trait_decl_ref }

and etrait_decl_ref_no_regions_to_gr_trait_decl_ref (tr : etrait_decl_ref) :
    'a region trait_decl_ref =
  let ({ trait_decl_id; decl_generics } : etrait_decl_ref) = tr in
  let decl_generics =
    egeneric_args_no_regions_to_gr_generic_args decl_generics
  in
  { trait_decl_id; decl_generics }

and etrait_instance_id_no_regions_to_gr_trait_instance_id
    (id : etrait_instance_id) : 'a region trait_instance_id =
  match id with
  | Self -> Self
  | TraitImpl id -> TraitImpl id
  | BuiltinOrAuto id -> BuiltinOrAuto id
  | Clause id -> Clause id
  | ParentClause (id, decl_id, cid) ->
      let id = etrait_instance_id_no_regions_to_gr_trait_instance_id id in
      ParentClause (id, decl_id, cid)
  | ItemClause (id, decl_id, name, cid) ->
      let id = etrait_instance_id_no_regions_to_gr_trait_instance_id id in
      ItemClause (id, decl_id, name, cid)
  | TraitRef tr ->
      let tr = etrait_ref_no_regions_to_gr_trait_ref tr in
      TraitRef tr
  | UnknownTrait msg -> UnknownTrait msg

let ety_no_regions_to_rty (ty : ety) : rty = ety_no_regions_to_gr_ty ty
let ety_no_regions_to_sty (ty : ety) : sty = ety_no_regions_to_gr_ty ty

(** Check if a {!type: Types.ty} contains regions from a given set *)
let ty_has_regions_in_set (rset : RegionId.Set.t) (ty : rty) : bool =
  let obj =
    object
      inherit [_] iter_ty
      method! visit_'r _ r = if region_in_set r rset then raise Found
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
  * Generally, ADTs are not primitively copyable. However, some of the primitive
  * ADTs are (e.g., [Option]).
  *)
let rec ty_is_primitively_copyable (ty : 'r ty) : bool =
  match ty with
  | Adt (Assumed Option, generics) ->
      List.for_all ty_is_primitively_copyable generics.types
  | Adt ((AdtId _ | Assumed (Box | Vec | Str | Slice | Range)), _) -> false
  | Adt ((Tuple | Assumed Array), generics) ->
      List.for_all ty_is_primitively_copyable generics.types
  | TypeVar _ | Never -> false
  | Literal (Bool | Char | Integer _) -> true
  | TraitType _ -> false
  | Ref (_, _, Mut) -> false
  | Ref (_, _, Shared) -> true
