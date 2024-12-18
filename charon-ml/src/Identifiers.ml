module C = Collections

(** Signature for a module describing an identifier.
    
    We often need identifiers (for definitions, variables, etc.) and in
    order to make sure we don't mix them, we use a generative functor
    (see {!IdGen}).

    Because {!Id.id} is an opaque type, even though it is [int] in practice
    it is not possible to mix ids coming from two different instances of the
    {!IdGen} functor.

    For instance, if we do:
    {[
      module TypeDeclId = IdGen ()
      module VariantId = IdGen ()
      module FieldId = IdGen ()
    ]}

    the types [TypeDeclId.id], [VariantId.id] and [FieldId.id] will be
    considered as different by the OCaml typechecker.

    This is especially useful when one manipulates functions which take
    several ids of different kinds as inputs: if identifiers were (transparently)
    integers, we could mix them, while here the compiler prevents us from doing us,
    avoiding mistakes which are easy to do and hard to debug.

    It is sometimes necessary to generate ids from integers (and convert ids to
    integers), and we provide functions for doing so: they should of course be
    manipulated with care. In this regard, the point of {!Id} is not so much to have
    opaque types but rather to provide a way of manipulating ids in a disciplined
    manner, to prevent bugs by leveraging the typechecker.
*)
module type Id = sig
  type id

  (** Id generator - simply a counter *)
  type generator

  val zero : id
  val generator_zero : generator
  val generator_from_id : id -> generator
  val generator_from_incr_id : id -> generator
  val fresh_stateful_generator : unit -> generator ref * (unit -> id)
  val mk_stateful_generator : generator -> generator ref * (unit -> id)
  val mk_stateful_generator_starting_at_id : id -> generator ref * (unit -> id)
  val incr : id -> id

  (** This function returns the current value of the counter, without incrementing it *)
  val get_counter_value : generator -> id

  (* TODO: this should be stateful! - but we may want to be able to duplicate
     contexts...
     Maybe we could have a [fresh] and a [global_fresh]
     TODO: change the order of the returned types
  *)
  val fresh : generator -> id * generator
  val to_string : id -> string
  val pp_id : Format.formatter -> id -> unit
  val show_id : id -> string
  val id_of_json : 'ctx -> Yojson.Basic.t -> (id, string) result
  val compare_id : id -> id -> int
  val max : id -> id -> id
  val min : id -> id -> id
  val pp_generator : Format.formatter -> generator -> unit
  val show_generator : generator -> string
  val to_int : id -> int
  val of_int : int -> id

  (** This function should be used in the rare cases where we have a list whose
      elements should be indexable through ids (for example, the fields of
      a structure can be indexed by the field id).

      Note that in Rust we have a special vector type for such lists, and it
      works well because Rust has typeclasses. We hesitated to have a special
      type in OCaml too but it proved too cumbersome to use so we finally
      resorted to having lists.
   *)
  val nth : 'a list -> id -> 'a

  (** See the comments for {!nth} *)
  val nth_opt : 'a list -> id -> 'a option

  (** Update the nth element of the list.

      See the comments for {!nth}.

      Raises [Invalid_argument] if the identifier is out of range.
   *)
  val update_nth : 'a list -> id -> 'a -> 'a list

  (** See the comments for {!nth} *)
  val mapi : (id -> 'a -> 'b) -> 'a list -> 'b list

  (** Same as {!mapi}, but where the indices start with 1.

      This function should be used with even more care than {!mapi}.
       
      TODO: generalize to [map_from_i]
   *)
  val mapi_from1 : (id -> 'a -> 'b) -> 'a list -> 'b list

  (** See the comments for {!nth} *)
  val iteri : (id -> 'a -> unit) -> 'a list -> unit

  module Ord : C.OrderedType with type t = id
  module Set : C.Set with type elt = id
  module Map : C.Map with type key = id
  module InjSubst : C.InjMap with type key = id and type elem = id
end

(** Generative functor for identifiers.

    See {!Id}.
*)
module IdGen () : Id = struct
  (* TODO: use Z.t *)
  type id = int [@@deriving show]
  type generator = id [@@deriving show]

  let zero = 0
  let generator_zero = 0

  let incr x =
    (* Identifiers should never overflow (because max_int is a really big
     * value - but we really want to make sure we detect overflows if
     * they happen *)
    if x = max_int then raise (Utils.IntegerOverflow ()) else x + 1

  let generator_from_id id = id
  let generator_from_incr_id id = incr id

  let mk_stateful_generator g =
    let g = ref g in
    let fresh () =
      let id = !g in
      g := incr id;
      id
    in
    (g, fresh)

  let mk_stateful_generator_starting_at_id id = mk_stateful_generator id
  let get_counter_value gen = gen
  let fresh_stateful_generator () = mk_stateful_generator 0
  let fresh gen = (gen, incr gen)
  let to_string = string_of_int
  let to_int x = x
  let of_int x = x
  let id_of_json = OfJsonBasic.int_of_json
  let compare_id = compare
  let max id0 id1 = if id0 > id1 then id0 else id1
  let min id0 id1 = if id0 < id1 then id0 else id1
  let nth v id = List.nth v id
  let nth_opt v id = List.nth_opt v id

  let rec update_nth vec id v =
    match (vec, id) with
    | [], _ -> raise (Invalid_argument "Out of range")
    | _ :: vec', 0 -> v :: vec'
    | x :: vec', _ -> x :: update_nth vec' (id - 1) v

  let mapi = List.mapi

  let mapi_from1 f ls =
    let rec aux i ls =
      match ls with
      | [] -> []
      | x :: ls' -> f i x :: aux (i + 1) ls'
    in
    aux 1 ls

  let iteri = List.iteri

  module Ord = struct
    type t = id

    let compare = compare
    let to_string = to_string
    let pp_t = pp_id
    let show_t = show_id
  end

  module Set = C.MakeSet (Ord)
  module Map = C.MakeMap (Ord)
  module InjSubst = C.MakeInjMap (Ord) (Ord)
end
