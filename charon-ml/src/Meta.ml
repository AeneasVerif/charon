(** Meta data like code spans *)
include Generated_Meta

(** Ordered file name *)
module OrderedFileName : Collections.OrderedType with type t = file_name =
struct
  type t = file_name

  let compare = compare_file_name
  let to_string s = show_file_name s
  let pp_t fmt s = pp_file_name fmt s
  let show_t s = show_file_name s
end

module FileNameSet = Collections.MakeSet (OrderedFileName)
module FileNameMap = Collections.MakeMap (OrderedFileName)

module OrderedAnyDeclId : Collections.OrderedType with type t = item_id = struct
  type t = item_id

  let compare = compare_item_id
  let to_string = show_item_id
  let pp_t fmt x = Format.pp_print_string fmt (show_item_id x)
  let show_t = show_item_id
end

module AnyDeclIdSet = Collections.MakeSet (OrderedAnyDeclId)
module AnyDeclIdMap = Collections.MakeMap (OrderedAnyDeclId)
