(** Utilities to identify Rust definitions by matching on their names.

    Identifying Rust definitions is non trivial because of:
    - the impl blocks, which are identified by their types
    - trait instances, which don't have a name (and which we identify
      with trait references)

    For this reason, we define:
    - a small pattern matching language for Rust names
    - a parser for this language
    - matchers which check if a name matches a pattern
    - helpers to derive patterns from names (useful when one identifies
      some external functions that need custom treatment, as it avoids
      writing patterns by hand)

    Here are some examples of patterns:
    - "core::mem::replace": the function `core::mem::replace`
    - "alloc::vec::{alloc::vec::Vec<@>}::push": the function `push` in any
      impl block of type `alloc::vec::Vec<T>`, where T is a type variable.
      Note that "@" means that this matches any (type) variable. In case
      we need stronger constraints, we can name those variables: "@T". All the
      occurrences of "@T" must match the same variable (ex.: "Foo<@T, @T>"
      would match `Foo<U, U>` but not `Foo<T, U>`).
    - the "@" syntax is used both for types and const generics. For regions/lifetimes,
      we use "'": "&'a mut @T"
    - for the types we put inside blocks, we have syntax for arrays, slices,
      and references:
      - "[@T; @N]": slice
      - "&'R mut @T": mutable reference

    Remark: `Box` is treated as a primitive type, which means that one only
    needs to type "Box" (instead of "alloc::boxed::Box" - though the latter
    also works).
 *)

(* The "raw" name matcher patterns *)
include Name_matcher_parser.Ast
include Name_matcher_parser.Interface
module T = Types

(*
 * Match a name
 *)

module VarOrderedType : Collections.OrderedType with type t = var = struct
  type t = var

  let compare = compare_var
  let to_string x = show_var x
  let pp_t fmt x = Format.pp_print_string fmt (show_var x)
  let show_t x = show_var x
end

module VarMap = Collections.MakeMap (VarOrderedType)

(* Context to lookup definitions *)
type ctx = {
  type_decls : T.type_decl T.TypeDeclId.Map.t;
  global_decls : LlbcAst.global_decl T.GlobalDeclId.Map.t;
  trait_decls : GAst.trait_decl T.TraitDeclId.Map.t;
}

(** Match configuration *)
type match_config = {
  map_vars_to_vars : bool;
      (** If true, only allow matching variables to variables.

          This is important when matching names: if the pattern
          is `alloc::boxed::{Box<@T>}::new`, we only want to match
          names where `@T` is a variable. For instance, we wouldn't
          want to match `alloc::boxed::{Box<u32>}::new` (if it existed...).
          However, we might want to match instantiations (i.e., for which
          `@T` is matched to `usize`) when matching function calls inside
          bodies.
       *)
}

(** Mapped expressions.

    The {!MRegion} variant is used when matching generics.
 *)
type mexpr = MTy of T.ty | MCg of T.const_generic | MRegion of T.region

(* Small helper to store the mappings from variables to expressions *)
type maps = {
  rmap : T.region VarMap.t ref;  (** Regions map *)
  vmap : mexpr VarMap.t ref;
      (** Variables map (accounts both for the types and const generics) *)
}

let mk_empty_maps () = { rmap = ref VarMap.empty; vmap = ref VarMap.empty }

(** Update a map and check that there are no incompatible
    constraints at the same time. *)
let update_map (find_opt : 'a -> 'm -> 'b option) (add : 'a -> 'b -> 'm -> 'm)
    (m : 'm ref) (id : 'a) (v : 'b) : bool =
  match find_opt id !m with
  | None ->
      (* Simply update *)
      m := add id v !m;
      true
  | Some v' ->
      (* Check the binding *)
      v = v'

let update_rmap (c : match_config) (m : maps) (id : var) (v : T.region) : bool =
  let is_var = match v with RVar _ -> true | _ -> false in
  if c.map_vars_to_vars && not is_var then false
  else update_map VarMap.find_opt VarMap.add m.rmap id v

let update_tmap (c : match_config) (m : maps) (id : var) (v : T.ty) : bool =
  let is_var = match v with TVar _ -> true | _ -> false in
  if c.map_vars_to_vars && not is_var then false
  else update_map VarMap.find_opt VarMap.add m.vmap id (MTy v)

let update_cmap (c : match_config) (m : maps) (id : var) (v : T.const_generic) :
    bool =
  let is_var = match v with CgVar _ -> true | _ -> false in
  if c.map_vars_to_vars && not is_var then false
  else update_map VarMap.find_opt VarMap.add m.vmap id (MCg v)

let opt_update_rmap (c : match_config) (m : maps) (id : var option)
    (v : T.region) : bool =
  match id with None -> true | Some id -> update_rmap c m id v

let opt_update_tmap (c : match_config) (m : maps) (id : var option) (v : T.ty) :
    bool =
  match id with None -> true | Some id -> update_tmap c m id v

let opt_update_cmap (c : match_config) (m : maps) (id : var option)
    (v : T.const_generic) : bool =
  match id with None -> true | Some id -> update_cmap c m id v

(** Pay attention when updating the names because we use this function
    for several purposes:
    - to match patterns with literal types
    - to convert patterns to strings which can be parsed as patterns
    - to convert patterns to string for printing/name generation
 *)
let literal_type_to_string (ty : T.literal_type) : string =
  match ty with
  | TBool -> "bool"
  | TChar -> "char"
  | TInteger ty -> (
      match ty with
      | Isize -> "isize"
      | I8 -> "i8"
      | I16 -> "i16"
      | I32 -> "i32"
      | I64 -> "i64"
      | I128 -> "i128"
      | Usize -> "usize"
      | U8 -> "u8"
      | U16 -> "u16"
      | U32 -> "u32"
      | U64 -> "u64"
      | U128 -> "u128")

(** Match a pattern with a region.

    Region true and update the maps if the match is successful, return false
    otherwise. *)
let match_region (c : match_config) (m : maps) (id : region) (v : T.region) :
    bool =
  match (id, v) with
  | RStatic, RStatic -> true
  | RVar id, RVar _ -> opt_update_rmap c m id v
  | RVar id, RStatic ->
      if c.map_vars_to_vars then false else opt_update_rmap c m id v
  | _ -> false

let match_ref_kind (prk : ref_kind) (rk : T.ref_kind) : bool =
  match (prk, rk) with RMut, RMut | RShared, RShared -> true | _ -> false

let match_literal (pl : literal) (l : PrimitiveValues.literal) : bool =
  match (pl, l) with
  | LInt pv, VScalar v -> pv = v.value
  | LBool pv, VBool v -> pv = v
  | LChar pv, VChar v -> pv = v
  | _ -> false

let rec match_name_with_generics (ctx : ctx) (c : match_config) (p : pattern)
    (n : T.name) (g : T.generic_args) : bool =
  match (p, n) with
  | [], [] -> false (* We shouldn't get there: the names should be non empty *)
  | [ PIdent (pid, pg) ], [ PeIdent (id, _) ] ->
      (* We reached the end: match the generics.
         We have to generate an empty map. *)
      pid = id && match_generic_args ctx c (mk_empty_maps ()) pg g
  | PIdent (pid, pg) :: p, PeIdent (id, _) :: n ->
      (* This is not the end: check that the generics are empty *)
      pid = id && pg = [] && match_name_with_generics ctx c p n g
  | PImpl pty :: p, PeImpl impl :: n ->
      match_expr_with_ty ctx c (mk_empty_maps ()) pty impl.ty
      && match_name_with_generics ctx c p n g
  | _ -> false

and match_name (ctx : ctx) (c : match_config) (p : pattern) (n : T.name) : bool
    =
  match_name_with_generics ctx c p n TypesUtils.empty_generic_args

and match_pattern_with_type_id (ctx : ctx) (c : match_config) (m : maps)
    (pid : pattern) (id : T.type_id) (generics : T.generic_args) : bool =
  match id with
  | TAdtId id ->
      (* Lookup the type decl and match the name *)
      let d = T.TypeDeclId.Map.find id ctx.type_decls in
      match_name_with_generics ctx c pid d.name generics
  | TTuple -> false
  | TAssumed id -> (
      match (id, pid) with
      | ( TBox,
          ( [ PIdent ("Box", pgenerics) ]
          | [
              PIdent ("alloc", []);
              PIdent ("boxed", []);
              PIdent ("Box", pgenerics);
            ] ) ) ->
          match_generic_args ctx c m pgenerics generics
      | TStr, [ PIdent ("str", []) ] -> generics = TypesUtils.empty_generic_args
      | _ -> false)

and match_pattern_with_literal_type (pty : pattern) (ty : T.literal_type) : bool
    =
  let ty = literal_type_to_string ty in
  pty = [ PIdent (ty, []) ]

and match_primitive_adt (pid : primitive_adt) (id : T.type_id) : bool =
  match (pid, id) with
  | TTuple, TTuple | TArray, TAssumed TArray | TSlice, TAssumed TSlice -> true
  | _ -> false

and match_expr_with_ty (ctx : ctx) (c : match_config) (m : maps) (pty : expr)
    (ty : T.ty) : bool =
  match (pty, ty) with
  | EComp pid, TAdt (id, generics) ->
      match_pattern_with_type_id ctx c m pid id generics
  | EComp pid, TLiteral lit -> match_pattern_with_literal_type pid lit
  | EPrimAdt (pid, pgenerics), TAdt (id, generics) ->
      match_primitive_adt pid id
      && match_generic_args ctx c m pgenerics generics
  | ERef (pr, pty, prk), TRef (r, ty, rk) ->
      match_region c m pr r
      && match_expr_with_ty ctx c m pty ty
      && match_ref_kind prk rk
  | EVar v, _ -> opt_update_tmap c m v ty
  | EComp pid, TTraitType (trait_ref, generics, type_name) ->
      generics = TypesUtils.empty_generic_args
      && match_trait_type ctx c pid trait_ref type_name
  | _ -> false

and match_trait_type (ctx : ctx) (c : match_config) (pid : pattern)
    (tr : T.trait_ref) (type_name : string) : bool =
  (* We match the trait decl ref *)
  (* We split the pattern between the trait decl ref and the associated type name *)
  let pid, ptype_name = Collections.List.pop_last pid in
  (* Lookup the trait declaration *)
  let d =
    T.TraitDeclId.Map.find tr.trait_decl_ref.trait_decl_id ctx.trait_decls
  in
  (* Match the trait decl ref *)
  match_name_with_generics ctx c pid d.name tr.trait_decl_ref.decl_generics
  &&
  (* Match the type name *)
  match ptype_name with
  | PIdent (ptype_name, []) -> ptype_name = type_name
  | _ -> false

and match_generic_args (ctx : ctx) (c : match_config) (m : maps)
    (pgenerics : generic_args) (generics : T.generic_args) : bool =
  let { regions; types; const_generics; trait_refs = _ } : T.generic_args =
    generics
  in
  let generics =
    List.concat
      [
        List.map (fun x -> MRegion x) regions;
        List.map (fun x -> MTy x) types;
        List.map (fun x -> MCg x) const_generics;
      ]
  in
  if List.length pgenerics = List.length generics then
    List.for_all2 (match_generic_arg ctx c m) pgenerics generics
  else false

and match_generic_arg (ctx : ctx) (c : match_config) (m : maps)
    (pg : generic_arg) (g : mexpr) : bool =
  match (pg, g) with
  | GRegion pr, MRegion r -> match_region c m pr r
  | GExpr e, MTy ty -> match_expr_with_ty ctx c m e ty
  | GExpr e, MCg cg -> match_expr_with_const_generic ctx c m e cg
  | GValue v, MCg (CgValue cg) -> match_literal v cg
  | _ -> false

and match_expr_with_const_generic (ctx : ctx) (c : match_config) (m : maps)
    (pcg : expr) (cg : T.const_generic) : bool =
  match (pcg, cg) with
  | EVar pv, _ -> opt_update_cmap c m pv cg
  | EComp pat, CgGlobal gid ->
      (* Lookup the decl and match the name *)
      let d = T.GlobalDeclId.Map.find gid ctx.global_decls in
      match_name ctx c pat d.name
  | _ -> false

let mk_name_with_generics_matcher (ctx : ctx) (c : match_config) (pat : string)
    : T.name -> T.generic_args -> bool =
  let pat = parse_pattern pat in
  match_name_with_generics ctx c pat

let mk_name_matcher (ctx : ctx) (c : match_config) (pat : string) :
    T.name -> bool =
  let pat = parse_pattern pat in
  match_name ctx c pat

(*
 * Helpers to convert names to patterns
 *)

(* We use this to store the constraints maps (the map from variable
   ids to option pattern variable ids) *)
type constraints = {
  rmap : var option T.RegionId.Map.t;
  tmap : var option T.TypeVarId.Map.t;
  cmap : var option T.ConstGenericVarId.Map.t;
}

let ref_kind_to_pattern (rk : T.ref_kind) : ref_kind =
  match rk with RMut -> RMut | RShared -> RShared

let region_to_pattern (m : constraints) (r : T.region) : region =
  match r with
  | RVar r -> RVar (T.RegionId.Map.find r m.rmap)
  | RStatic -> RStatic
  | _ -> raise (Failure "Unexpected")

let type_var_to_pattern (m : constraints) (v : T.TypeVarId.id) : var option =
  T.TypeVarId.Map.find v m.tmap

let compute_constraints_map (generics : T.generic_params) : constraints =
  let fresh_id (gen : int ref) : int =
    let id = !gen in
    gen := id + 1;
    id
  in
  let rmap =
    let rid_gen = ref 0 in
    T.RegionId.Map.of_list
      (List.map
         (fun (r : T.region_var) ->
           let v =
             match r.name with
             | None -> VarIndex (fresh_id rid_gen)
             | Some name -> VarName name
           in
           (r.index, Some v))
         generics.regions)
  in
  let tmap =
    T.TypeVarId.Map.of_list
      (List.map
         (fun (x : T.type_var) -> (x.index, Some (VarName x.name)))
         generics.types)
  in
  let cmap =
    T.ConstGenericVarId.Map.of_list
      (List.map
         (fun (x : T.const_generic_var) -> (x.index, Some (VarName x.name)))
         generics.const_generics)
  in
  { rmap; tmap; cmap }

(*let region_to_pattern (m : constraints) (r : T.region) : int option =
    match r with
    | RVar r -> T.RegionId.Map.find r m.rmap
    | _ -> raise (Failure "Unimplemented")

  let const_generic_to_pattern (m : constraints) (cg : T.const_generic) :
      const_generic =
    match cg with
    | CGVar v -> CgVar (T.ConstGenericVarId.Map.find v m.cmap)
    | CGValue (VScalar v) -> CgValue v.value
    | _ -> raise (Failure "Unimplemented") *)

(*
(** Visitor to compute constraints map.

    We essentially count the occurrences of (type, region, const generic)
    variables. If a variable appears once, it doesn't have any constraints
    (we use the @R, @T, @C patterns). If a variable appears more than once,
    we give it an identifier (@T1, etc.).
*)
let mk_compute_constraints_map_visitor () =
  (* The sets of variables we encounter *)
  let rset = ref T.RegionId.Set.empty in
  let tset = ref T.TypeVarId.Set.empty in
  let cset = ref T.ConstGenericVarId.Set.empty in
  (* The sets of variables we encounter twice *)
  let rset_dup = ref T.RegionId.Set.empty in
  let tset_dup = ref T.TypeVarId.Set.empty in
  let cset_dup = ref T.ConstGenericVarId.Set.empty in
  (* Helpers *)
  let register_var (type s e)
      (module S : Collections.Set with type t = s and type elt = e)
      (set : S.t ref) (set_dup : S.t ref) (x : S.elt) : unit =
    (* If the variable has already been registered, add it to the duplicate
       set, otherwise register it in the "regular" set *)
    if S.mem x !set then set_dup := S.add x !set_dup else set := S.add x !set
  in
  let register_region_var =
    register_var (module T.RegionId.Set) rset rset_dup
  in
  let register_type_var = register_var (module T.TypeVarId.Set) tset tset_dup in
  let register_const_generic_var =
    register_var (module T.ConstGenericVarId.Set) cset cset_dup
  in
  (* TODO: we can't parameterize with a module M satisfying Collections.Map,
     because we would then need to introduce a constraint on the polymorphic
     type 'a M.t, which is not possible in OCaml *)
  let get_var_pattern_ids (type s e)
      (module S : Collections.Set with type t = s and type elt = e)
      (set : S.t ref) (set_dup : S.t ref) (id_gen : int ref) :
      (S.elt * int option) list =
    List.map
      (fun x ->
        let id =
          if S.mem x !set_dup then (
            let id = !id_gen in
            id_gen := id + 1;
            Some id)
          else None
        in
        (x, id))
      (S.elements !set)
  in
  let get_constraints () : constraints =
    let rmap =
      T.RegionId.Map.of_list
        (get_var_pattern_ids (module T.RegionId.Set) rset rset_dup (ref 0))
    in
    let tmap =
      T.TypeVarId.Map.of_list
        (get_var_pattern_ids (module T.TypeVarId.Set) tset tset_dup (ref 0))
    in
    let cmap =
      T.ConstGenericVarId.Map.of_list
        (get_var_pattern_ids
           (module T.ConstGenericVarId.Set)
           cset cset_dup (ref 0))
    in
    { rmap; tmap; cmap }
  in
  let visitor =
    object
      inherit [_] Types.iter_ty
      method! visit_region_id _ id = register_region_var id
      method! visit_type_var_id _ id = register_type_var id
      method! visit_const_generic_var_id _ id = register_const_generic_var id
    end
  in
  (visitor, get_constraints)*)

let literal_type_to_pattern (lit : T.literal_type) : expr =
  EComp [ PIdent (literal_type_to_string lit, []) ]

let literal_to_pattern (lit : PrimitiveValues.literal) : literal =
  match lit with
  | VScalar sv -> LInt sv.value
  | VBool v -> LBool v
  | VChar v -> LChar v

let rec name_with_generic_args_to_pattern_aux (ctx : ctx) (n : T.name)
    (generics : generic_args option) : pattern =
  match n with
  | [] -> raise (Failure "Empty names are not valid")
  | [ e ] -> [ path_elem_with_generic_args_to_pattern ctx e generics ]
  | e :: n ->
      path_elem_with_generic_args_to_pattern ctx e None
      :: name_with_generic_args_to_pattern_aux ctx n generics

and name_to_pattern_aux (ctx : ctx) (n : T.name) : pattern =
  name_with_generic_args_to_pattern_aux ctx n None

and path_elem_with_generic_args_to_pattern (ctx : ctx) (e : T.path_elem)
    (generics : generic_args option) : pattern_elem =
  match e with
  | PeIdent (s, _) -> (
      match generics with
      | None -> PIdent (s, [])
      | Some args -> PIdent (s, args))
  | PeImpl impl ->
      assert (generics = None);
      impl_elem_to_pattern ctx impl

and impl_elem_to_pattern (ctx : ctx) (impl : T.impl_elem) : pattern_elem =
  PImpl (ty_to_pattern ctx impl.generics impl.ty)

and ty_to_pattern_aux (ctx : ctx) (m : constraints) (ty : T.ty) : expr =
  match ty with
  | TAdt (id, generics) -> (
      let generics = generic_args_to_pattern ctx m generics in
      match id with
      | TAdtId id ->
          (* Lookup the declaration *)
          let d = T.TypeDeclId.Map.find id ctx.type_decls in
          EComp
            (name_with_generic_args_to_pattern_aux ctx d.name (Some generics))
      | TTuple -> EPrimAdt (TTuple, generics)
      | TAssumed TArray -> EPrimAdt (TArray, generics)
      | TAssumed TSlice -> EPrimAdt (TSlice, generics)
      | TAssumed TBox -> EComp [ PIdent ("Box", generics) ]
      | TAssumed TStr -> EComp [ PIdent ("str", generics) ])
  | TVar v -> EVar (type_var_to_pattern m v)
  | TLiteral lit -> literal_type_to_pattern lit
  | TRef (r, ty, rk) ->
      ERef
        ( region_to_pattern m r,
          ty_to_pattern_aux ctx m ty,
          ref_kind_to_pattern rk )
  | TTraitType (trait_ref, generics, type_name) ->
      assert (generics = TypesUtils.empty_generic_args);
      let trait_decl_ref = trait_ref.trait_decl_ref in
      let d =
        T.TraitDeclId.Map.find trait_decl_ref.trait_decl_id ctx.trait_decls
      in
      let g = generic_args_to_pattern ctx m trait_decl_ref.decl_generics in
      let name = name_with_generic_args_to_pattern_aux ctx d.name (Some g) in
      let name = name @ [ PIdent (type_name, []) ] in
      EComp name
  | TNever | TRawPtr _ | TArrow _ -> raise (Failure "Unimplemented")

and ty_to_pattern (ctx : ctx) (params : T.generic_params) (ty : T.ty) : expr =
  (* Compute the constraints map *)
  let m = compute_constraints_map params in
  (* Convert the type *)
  ty_to_pattern_aux ctx m ty

and const_generic_to_pattern (ctx : ctx) (m : constraints)
    (cg : T.const_generic) : generic_arg =
  match cg with
  | CgVar v -> GExpr (EVar (T.ConstGenericVarId.Map.find v m.cmap))
  | CgValue v -> GValue (literal_to_pattern v)
  | CgGlobal gid ->
      let d = T.GlobalDeclId.Map.find gid ctx.global_decls in
      let n = name_to_pattern_aux ctx d.name in
      GExpr (EComp n)

and generic_args_to_pattern (ctx : ctx) (m : constraints)
    (generics : T.generic_args) : generic_args =
  let { regions; types; const_generics; trait_refs = _ } : T.generic_args =
    generics
  in
  let regions = List.map (region_to_pattern m) regions in
  let types = List.map (ty_to_pattern_aux ctx m) types in
  let const_generics =
    List.map (const_generic_to_pattern ctx m) const_generics
  in
  List.concat
    [
      List.map (fun x -> GRegion x) regions;
      List.map (fun x -> GExpr x) types;
      const_generics;
    ]

let name_to_pattern (ctx : ctx) (n : T.name) : pattern =
  (* Convert the name to a pattern *)
  let pat = name_to_pattern_aux ctx n in
  (* Sanity check: the name should match the pattern *)
  assert (match_name ctx { map_vars_to_vars = true } pat n);
  (* Return *)
  pat

let name_with_generics_to_pattern (ctx : ctx) (n : T.name)
    (params : T.generic_params) (args : T.generic_args) : pattern =
  (* Convert the name to a pattern *)
  let pat =
    let m = compute_constraints_map params in
    let args = generic_args_to_pattern ctx m args in
    name_with_generic_args_to_pattern_aux ctx n (Some args)
  in
  (* Sanity check: the name should match the pattern *)
  assert (match_name_with_generics ctx { map_vars_to_vars = true } pat n args);
  (* Return *)
  pat

(*
 * Convert patterns to strings
 *)
type target_kind =
  | TkPattern  (** Generate a string which can be parsed as a pattern *)
  | TkPretty  (** Pretty printing *)
  | TkName  (** A name for code extraction (for instance for trait instances) *)

type print_config = { tgt_kind : target_kind }

let literal_to_string (c : print_config) (l : literal) : string =
  match l with
  | LInt v -> Z.to_string v
  | LBool b -> Bool.to_string b
  | LChar x -> (
      match c.tgt_kind with
      | TkPattern ->
          (* TODO: we can't use the syntax 'x' for now because of lifetimes *)
          raise (Failure "TODO")
      | TkPretty -> "'" ^ String.make 1 x ^ "'"
      | TkName -> String.make 1 x)

let region_var_to_string (c : print_config) (v : var option) : string =
  match c.tgt_kind with
  | TkPattern | TkPretty -> (
      match v with
      | None -> "'_"
      | Some (VarName n) -> "'" ^ n
      | Some (VarIndex id) -> "'" ^ string_of_int id)
  | TkName -> (
      match v with
      | None -> ""
      | Some (VarName n) -> StringUtils.capitalize_first_letter n
      | Some (VarIndex id) -> string_of_int id)

let region_to_string (c : print_config) (r : region) : string =
  match r with
  | RStatic -> (
      match c.tgt_kind with
      | TkPattern | TkPretty -> "'static"
      | TkName -> "Static")
  | RVar v -> region_var_to_string c v

let opt_var_to_string (c : print_config) (v : var option) : string =
  match c.tgt_kind with
  | TkPattern -> (
      match v with
      | None -> "@"
      | Some (VarName n) -> "@" ^ n
      | Some (VarIndex id) -> "@" ^ string_of_int id)
  | TkPretty | TkName -> (
      (* Below: when generating names, we shouldn't use the None or VarIndex cases *)
      match v with
      | None -> "P"
      | Some (VarName n) -> n
      | Some (VarIndex id) -> "P" ^ string_of_int id)

let rec pattern_to_string (c : print_config) (p : pattern) : string =
  String.concat "::" (List.map (pattern_elem_to_string c) p)

and pattern_elem_to_string (c : print_config) (e : pattern_elem) : string =
  match e with
  | PIdent (s, g) -> s ^ generic_args_to_string c g
  | PImpl ty -> "{" ^ expr_to_string c ty ^ "}"

and expr_to_string (c : print_config) (e : expr) : string =
  match e with
  | EComp pat -> pattern_to_string c pat
  | EPrimAdt (id, generics) -> (
      match id with
      | TTuple -> (
          let generics = List.map (generic_arg_to_string c) generics in
          match c.tgt_kind with
          | TkPattern | TkPretty -> "(" ^ String.concat ", " generics ^ ")"
          | TkName -> "Tuple" ^ String.concat "" generics)
      | TArray -> (
          match generics with
          | [ ty; cg ] -> (
              let ty = generic_arg_to_string c ty in
              let cg = generic_arg_to_string c cg in
              match c.tgt_kind with
              | TkPattern | TkPretty -> "[" ^ ty ^ "; " ^ cg ^ "]"
              | TkName -> "Array" ^ ty ^ cg)
          | _ -> raise (Failure "Ill-formed pattern"))
      | TSlice -> (
          match generics with
          | [ ty ] -> (
              let ty = generic_arg_to_string c ty in
              match c.tgt_kind with
              | TkPattern | TkPretty -> "[" ^ ty ^ "]"
              | TkName -> "Slice" ^ ty)
          | _ -> raise (Failure "Ill-formed pattern")))
  | ERef (r, ty, rk) ->
      let rk = match rk with RMut -> "mut " | RShared -> "" in
      "&" ^ region_to_string c r ^ " " ^ rk ^ expr_to_string c ty
  | EVar v -> opt_var_to_string c v

and generic_arg_to_string (c : print_config) (g : generic_arg) : string =
  match g with
  | GExpr e -> expr_to_string c e
  | GValue l -> literal_to_string c l
  | GRegion r -> region_to_string c r

and generic_args_to_string (c : print_config) (generics : generic_args) : string
    =
  if generics = [] then ""
  else
    "<" ^ String.concat ", " (List.map (generic_arg_to_string c) generics) ^ ">"
