let folder_name = Sys.argv.(1)

let files =
  Sys.readdir folder_name |> Array.to_seq
  |> Seq.filter (fun file -> Filename.check_suffix file ".llbc")

let () =
  Seq.iter
    (fun file ->
      let file = Filename.concat folder_name file in
      let ast =
        Llbc.Of_json.llbc_module_of_json (Yojson.Basic.from_file file)
      in
      let () =
        match ast with
        | Ok _ -> Printf.printf "%s parsed correctly" file
        | Error e -> Printf.printf "parsing error: %s" e
      in
      Format.printf "\n@?")
    files
