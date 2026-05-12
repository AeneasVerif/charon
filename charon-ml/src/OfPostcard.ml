open OfPostcardBasic
open Types
include Generated_OfPostcard

let crate_of_postcard_file (file : string) : (GAst.crate, string) result =
  with_state_of_file file @@ fun st ->
  let* () =
    match format_hint_of_postcard st with
    | Postcard -> Ok ()
    | Json ->
        Format.kasprintf Result.error
          "This file looks like JSON, but Postcard deserialization was \
           requested: %s. Please use JSON deserialization or regenerate as \
           Postcard."
          file
    | Empty -> Error ("Input file is empty: " ^ file)
  in
  let* charon_version = string_of_postcard () st in
  if not (String.equal charon_version CharonVersion.supported_charon_version)
  then
    Format.kasprintf Result.error
      "Incompatible version of charon: this program supports llbc emitted by \
       charon v%s but attempted to read a file emitted by charon v%s."
      CharonVersion.supported_charon_version charon_version
  else
    let ctx = empty_of_postcard_ctx in
    let* crate = translated_crate_of_postcard ctx st in
    let* _has_errors = bool_of_postcard ctx st in
    let* () = ensure_eof st in
    Ok
      ({
         name = crate.crate_name;
         options = crate.options;
         target_information = crate.target_information;
         assoc_item_names = crate.assoc_item_names;
         declarations = Option.value ~default:[] crate.ordered_decls;
         type_decls = crate.type_decls;
         fun_decls = crate.fun_decls;
         global_decls = crate.global_decls;
         trait_decls = crate.trait_decls;
         trait_impls = crate.trait_impls;
       }
        : GAst.crate)
