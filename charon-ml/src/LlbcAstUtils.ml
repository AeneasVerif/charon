include GAstUtils
open LlbcAst
open Utils
open Collections

(** Returns a list of all functions in a crate *)
let fun_decl_list_from_crate (crate : crate) : fun_decl list =
  snd (List.split (FunDeclId.Map.bindings crate.fun_decls))

(** Returns a list option of all arguments of a functions
    If a function does not have a body, it cannot access
    the locals field where the arguments are so it returns None
*)
let get_fun_args (fun_decl : fun_decl) : var list option =
  match fun_decl.body with
  | Some body ->
      let input_number = body.arg_count in
      let input_list = List.tl body.locals in
      Some (fst (List.split_at input_list input_number))
  | None -> None

(** Check if a {!type:Charon.LlbcAst.statement} contains loops *)
let statement_has_loops (st : statement) : bool =
  let obj =
    object
      inherit [_] iter_statement
      method! visit_Loop _ _ = raise Found
    end
  in
  try
    obj#visit_statement () st;
    false
  with Found -> true

(** Check if a {!type:Charon.LlbcAst.fun_decl} contains loops *)
let fun_decl_has_loops (fd : fun_decl) : bool =
  match fd.body with
  | Some body -> statement_has_loops body.body
  | None -> false

(** Create a sequence *)
let mk_sequence (st1 : statement) (st2 : statement) : statement =
  let span = MetaUtils.combine_span st1.span st2.span in
  let content = Sequence (st1, st2) in
  { span; content; comments_before = [] }

(** Chain two statements into a sequence, by pushing the second statement
    at the end of the first one (diving into sequences, switches, etc.).
 *)
let rec chain_statements (st1 : statement) (st2 : statement) : statement =
  match st1.content with
  | SetDiscriminant _ | Assert _ | Call _ | Assign _ | FakeRead _ | Drop _
  | Loop _ | Error _ ->
      (* Simply create a sequence *)
      mk_sequence st1 st2
  | Nop -> (* Ignore the nop *) st2
  | Break _ | Continue _ | Panic | Return ->
      (* Ignore the second statement, which won't be evaluated *) st1
  | Switch switch ->
      (* Insert inside the switch *)
      let span = MetaUtils.combine_span st1.span st2.span in
      let content = Switch (chain_statements_in_switch switch st2) in
      { span; content; comments_before = [] }
  | Sequence (st3, st4) ->
      (* Insert at the end of the statement *)
      mk_sequence st3 (chain_statements st4 st2)

and chain_statements_in_switch (switch : switch) (st : statement) : switch =
  match switch with
  | If (op, st0, st1) ->
      If (op, chain_statements st0 st, chain_statements st1 st)
  | SwitchInt (op, int_ty, branches, otherwise) ->
      let branches =
        List.map (fun (svl, br) -> (svl, chain_statements br st)) branches
      in
      let otherwise = chain_statements otherwise st in
      SwitchInt (op, int_ty, branches, otherwise)
  | Match (op, branches, otherwise) ->
      let branches =
        List.map (fun (svl, br) -> (svl, chain_statements br st)) branches
      in
      let otherwise =
        match otherwise with
        | None -> None
        | Some otherwise -> Some (chain_statements otherwise st)
      in
      Match (op, branches, otherwise)

(** Compute a map from function declaration ids to declaration groups. *)
let compute_fun_decl_groups_map (c : crate) : FunDeclId.Set.t FunDeclId.Map.t =
  FunDeclId.Map.of_list
    (List.flatten
       (List.filter_map
          (function
            | FunGroup (NonRecGroup id) ->
                Some [ (id, FunDeclId.Set.singleton id) ]
            | FunGroup (RecGroup ids) ->
                let idset = FunDeclId.Set.of_list ids in
                Some (List.map (fun id -> (id, idset)) ids)
            | TypeGroup _ | GlobalGroup _ | TraitDeclGroup _ | TraitImplGroup _
              ->
                None
            | MixedGroup _ ->
                raise
                  (Failure
                     "Mixed declaration groups cannot be indexed by declaration"))
          c.declarations))
