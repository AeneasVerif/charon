open OfPostcardBasic
open Types
include Generated_OfPostcard

let crate_of_postcard_file (file : string) : (GAst.crate, string) result =
  with_state_of_file file @@ fun st ->
  let* charon_version = string_of_postcard () st in
  if not (String.equal charon_version CharonVersion.supported_charon_version)
  then
    Error
      ("Incompatible version of charon: this program supports llbc emitted by \
        charon v" ^ CharonVersion.supported_charon_version
     ^ " but attempted to read a file emitted by charon v" ^ charon_version
     ^ ".")
  else
    let ctx = empty_of_postcard_ctx in
    let* crate = translated_crate_of_postcard ctx st in
    let* _has_errors = bool_of_postcard ctx st in
    let* () = ensure_eof st in
    let type_decls = TypeDeclId.map_of_indexed_list crate.type_decls in
    let fun_decls = FunDeclId.map_of_indexed_list crate.fun_decls in
    let global_decls = GlobalDeclId.map_of_indexed_list crate.global_decls in
    let trait_decls = TraitDeclId.map_of_indexed_list crate.trait_decls in
    let trait_impls = TraitImplId.map_of_indexed_list crate.trait_impls in
    Ok
      ({
         name = crate.crate_name;
         options = crate.options;
         target_information = crate.target_information;
         declarations = Option.value ~default:[] crate.ordered_decls;
         type_decls;
         fun_decls;
         global_decls;
         trait_decls;
         trait_impls;
         unit_metadata = Option.get crate.unit_metadata;
       }
        : GAst.crate)
