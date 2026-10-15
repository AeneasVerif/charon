(** Hash functions for the base types, used by the generated hash functions. *)

let combine (h : int) (x : int) : int = (31 * h) + x
let hash_bool (b : bool) : int = Bool.to_int b
let hash_int (x : int) : int = x
let hash_string (s : string) : int = Hashtbl.hash s

let hash_list (hash_a : 'a -> int) (l : 'a list) : int =
  List.fold_left (fun h x -> combine h (hash_a x)) 0 l

let hash_option (hash_a : 'a -> int) (x : 'a option) : int =
  match x with
  | None -> 0
  | Some x -> combine 1 (hash_a x)
