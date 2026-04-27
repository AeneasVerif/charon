open Charon
open Logging
module EL = Easy_logging.Logging

let log = main_log

(** [dir_is_empty dir] is true, if [dir] contains no files except * "." and ".."
*)
let dir_is_empty dir = Array.length (Sys.readdir dir) = 0

(** [dir_contents] returns the paths of all regular files that are * contained
    in [dir]. Each file is a path starting with [dir]. * From
    https://gist.github.com/lindig/be55f453026c65e761f4e7012f8ab9b5 *)
let dir_contents dir =
  let rec loop result = function
    | f :: fs when Sys.is_directory f ->
        Sys.readdir f |> Array.to_list
        |> List.map (Filename.concat f)
        |> List.append fs |> loop result
    | f :: fs -> loop (f :: result) fs
    | [] -> result
  in
  loop [] [ dir ]

let assert_eq x y msg arg_to_string =
  if x <> y then
    raise
      (Failure
         ("Real: " ^ arg_to_string x ^ ", Expected: " ^ arg_to_string y
        ^ " for " ^ msg))

let test_discriminant_roundtrip (crate : LlbcAst.crate) =
  let print_ctx = PrintUtils.of_crate crate in
  let print_var_id_opt = function
    | Some v -> "Some (" ^ Print.variant_id_to_pretty_string v ^ ")"
    | None -> "None"
  in
  let print_scalar_value_opt = function
    | Some v -> "Some " ^ Print.scalar_value_to_string v
    | None -> "None"
  in
  let ptr_size = (snd (List.hd crate.target_information)).target_pointer_size in
  Types.TypeDeclId.Map.iter
    (fun _ (ty_decl : Types.type_decl) ->
      match (ty_decl.kind, ty_decl.Types.layout) with
      | Enum _, [ (_, layout) ] when Option.is_some layout.discriminant_layout
        -> begin
          let name = Print.name_to_string print_ctx ty_decl.item_meta.name in
          Types.VariantId.iteri
            (fun var_id _ ->
              let variant_layout =
                Types.VariantId.nth layout.variant_layouts var_id
              in
              let tag = variant_layout.tag in
              if variant_layout.uninhabited then
                assert_eq tag None name print_scalar_value_opt
              else
                match tag with
                | None -> () (* Must be the untagged variant *)
                | Some tag ->
                    let roundtrip_var_id =
                      TypesUtils.get_variant_from_tag ptr_size ty_decl tag
                    in
                    assert_eq roundtrip_var_id (Some var_id)
                      (name ^ " with tag: " ^ print_scalar_value_opt (Some tag))
                      print_var_id_opt)
            layout.variant_layouts
        end
      | _ -> () (* Not an enum *))
    crate.type_decls

(* Run the tests *)
let run_tests (folder : string) : unit =
  (* List the LLBC files.

     Remark: we do not deserialize the ULLBC files.
  *)
  let llbc_files =
    dir_contents folder
    |> List.filter (fun file -> Filename.check_suffix file ".llbc")
  in
  let postcard_files =
    dir_contents folder
    |> List.filter (fun file -> Filename.check_suffix file ".llbc.postcard")
  in

  let json_time = ref 0.0 in
  let postcard_time = ref 0.0 in

  (* Deserialize LLBC JSON files *)
  let () =
    List.iter
      (fun file ->
        log#ldebug (lazy ("Deserializing LLBC file: " ^ file));
        (* Load the module *)
        let start_time = Unix.gettimeofday () in
        let json = Yojson.Basic.from_file file in
        match OfJson.crate_of_json json with
        | Error s ->
            log#error "Error when deserializing file %s: %s\n" file s;
            exit 1
        | Ok m ->
            json_time := !json_time +. (Unix.gettimeofday () -. start_time);
            log#linfo (lazy ("Deserialized: " ^ file));
            (* Test discriminant/tag roundtrip *)
            test_discriminant_roundtrip m;
            (* Test that pretty-printing doesn't crash *)
            let printed = Print.crate_to_string m in
            log#ldebug (lazy ("\n" ^ printed ^ "\n")))
      llbc_files
  in
  let () =
    List.iter
      (fun file ->
        log#ldebug (lazy ("Deserializing postcard file: " ^ file));
        (* Load the module *)
        let start_time = Unix.gettimeofday () in
        match OfPostcard.crate_of_postcard_file file with
        | Error s ->
            log#error "Error when deserializing postcard file %s: %s\n" file s;
            exit 1
        | Ok _ ->
            postcard_time :=
              !postcard_time +. (Unix.gettimeofday () -. start_time);
            log#linfo (lazy ("Deserialized postcard: " ^ file)))
      postcard_files
  in

  let avg_of time vals =
    if List.length vals > 0 then !time /. float_of_int (List.length vals)
    else 0.0
  in
  let avg_json_time = avg_of json_time llbc_files in
  let avg_postcard_time = avg_of postcard_time postcard_files in
  log#linfo
    (lazy
      (Printf.sprintf
         "Average deserialization time: JSON: %f seconds, Postcard: %f seconds \
          (%f times faster)"
         avg_json_time avg_postcard_time
         (if avg_postcard_time > 0.0 then avg_json_time /. avg_postcard_time
          else 0.0)));

  (* for each JSON and Postcard file pair, check the size of the file and print the ratio *)
  let ratios = ref [] in
  llbc_files
  |> List.iter (fun json_file ->
         let postcard_file = json_file ^ ".postcard" in
         if List.exists (fun f -> f = postcard_file) postcard_files then
           let json_size = (Unix.stat json_file).st_size in
           let postcard_size = (Unix.stat postcard_file).st_size in
           let ratio =
             if postcard_size > 0 then
               float_of_int json_size /. float_of_int postcard_size
             else 0.0
           in
           ratios := ratio :: !ratios);
  (* print min, max, avg and med ratios *)
  if !ratios = [] then ()
  else
    let min_ratio = List.fold_left min max_float !ratios in
    let max_ratio = List.fold_left max 0.0 !ratios in
    let avg_ratio =
      List.fold_left ( +. ) 0.0 !ratios /. float_of_int (List.length !ratios)
    in
    let sorted_ratios = List.sort compare !ratios in
    let med_ratio =
      if List.length sorted_ratios mod 2 = 1 then
        List.nth sorted_ratios (List.length sorted_ratios / 2)
      else
        let mid = List.length sorted_ratios / 2 in
        (List.nth sorted_ratios mid +. List.nth sorted_ratios (mid - 1)) /. 2.0
    in
    log#linfo
      (lazy
        (Printf.sprintf
           "Size ratio (JSON/Postcard): min: %f, max: %f, avg: %f, med: %f"
           min_ratio max_ratio avg_ratio med_ratio));

    (* Done *)
    ()
