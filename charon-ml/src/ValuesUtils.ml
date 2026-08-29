open Values

let literal_type_is_integer (t : literal_type) : bool =
  match t with
  | TInt _ -> true
  | TUInt _ -> true
  | _ -> false
