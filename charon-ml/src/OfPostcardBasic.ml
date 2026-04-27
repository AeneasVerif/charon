(** Basic utilities for postcard deserialization. *)

type postcard_state = { bytes : bytes; len : int; mutable pos : int }

let ( let* ) o f =
  match o with
  | Error e -> Error e
  | Ok x -> f x

let state_of_file (file : string) : (postcard_state, string) result =
  try
    let ic = open_in_bin file in
    Fun.protect
      ~finally:(fun () -> close_in ic)
      (fun () ->
        let len = in_channel_length ic in
        let bytes = Bytes.create len in
        really_input ic bytes 0 len;
        Ok { bytes; len; pos = 0 })
  with Sys_error e -> Error e

let combine_error_msgs (st : postcard_state) (msg : string)
    (res : ('a, string) result) : ('a, string) result =
  match res with
  | Ok x -> Ok x
  | Error e ->
      let rem = st.len - st.pos in
      let n = if rem < 8 then rem else 8 in
      let preview =
        List.init n (fun i -> Char.code (Bytes.get st.bytes (st.pos + i)))
        |> List.map (fun b -> Printf.sprintf "%02x" b)
        |> String.concat " "
      in
      Error
        (msg ^ " failed at byte " ^ string_of_int st.pos ^ " (next: " ^ preview
       ^ "): " ^ e)

let ensure_remaining (st : postcard_state) (needed : int) :
    (unit, string) result =
  let remaining = st.len - st.pos in
  if remaining < needed then
    Error
      ("unexpected end of postcard input (need " ^ string_of_int needed
     ^ " more bytes)")
  else Ok ()

let take_u8 (st : postcard_state) : (int, string) result =
  let* () = ensure_remaining st 1 in
  let b = Char.code (Bytes.get st.bytes st.pos) in
  st.pos <- st.pos + 1;
  Ok b

let take_bytes (st : postcard_state) (len : int) : (bytes, string) result =
  if len < 0 then Error "negative length"
  else
    let* () = ensure_remaining st len in
    let out = Bytes.sub st.bytes st.pos len in
    st.pos <- st.pos + len;
    Ok out

let read_varint_z ~(max_bytes : int) ~(max_last : int) (st : postcard_state) :
    (Z.t, string) result =
  let rec loop (i : int) (shift : int) (acc : Z.t) : (Z.t, string) result =
    if i >= max_bytes then Error "invalid postcard varint"
    else
      let* raw = take_u8 st in
      let payload = raw land 0x7F in
      let acc = Z.logor acc (Z.shift_left (Z.of_int payload) shift) in
      let has_more = raw land 0x80 <> 0 in
      if not has_more then
        if i = max_bytes - 1 && raw > max_last then
          Error "invalid postcard varint terminal byte"
        else Ok acc
      else loop (i + 1) (shift + 7) acc
  in
  loop 0 0 Z.zero

let z_to_int (z : Z.t) : (int, string) result =
  if Z.geq z Z.zero && Z.leq z (Z.of_int max_int) then Ok (Z.to_int z)
  else Error "integer out of OCaml int range"

let z_to_i (z : Z.t) : (Z.t, string) result =
  let one = Z.one in
  if Z.equal (Z.logand z one) Z.zero then Ok (Z.shift_right z 1)
  else Ok Z.(neg (add (shift_right z 1) one))

let usize_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result
    =
  let* z = read_varint_z ~max_bytes:10 ~max_last:1 st in
  z_to_int z

let bool_of_postcard (_ctx : 'ctx) (st : postcard_state) : (bool, string) result
    =
  let* b = take_u8 st in
  match b with
  | 0 -> Ok false
  | 1 -> Ok true
  | _ -> Error "invalid postcard bool"

let int_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* z = read_varint_z ~max_bytes:5 ~max_last:15 st in
  z_to_int z

let u16_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* z = read_varint_z ~max_bytes:3 ~max_last:3 st in
  z_to_int z

let u32_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* z = read_varint_z ~max_bytes:5 ~max_last:15 st in
  z_to_int z

let u64_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* z = read_varint_z ~max_bytes:10 ~max_last:1 st in
  z_to_int z

let i16_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* z = read_varint_z ~max_bytes:3 ~max_last:3 st in
  let* s = z_to_i z in
  z_to_int s

let i32_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* z = read_varint_z ~max_bytes:5 ~max_last:15 st in
  let* s = z_to_i z in
  z_to_int s

let i64_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* z = read_varint_z ~max_bytes:10 ~max_last:1 st in
  let* s = z_to_i z in
  z_to_int s

let isize_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result
    =
  let* z = read_varint_z ~max_bytes:10 ~max_last:1 st in
  let* s = z_to_i z in
  z_to_int s

let u8_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  take_u8 st

let i8_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  let* b = take_u8 st in
  if b < 128 then Ok b else Ok (b - 256)

let string_of_postcard (_ctx : 'ctx) (st : postcard_state) :
    (string, string) result =
  let* len = usize_of_postcard () st in
  let* bytes = take_bytes st len in
  Ok (Bytes.to_string bytes)

let big_uint_of_postcard (ctx : 'ctx) (st : postcard_state) :
    (Z.t, string) result =
  let* raw = string_of_postcard ctx st in
  try
    let z = Z.of_string raw in
    if Z.sign z < 0 then Error "expected non-negative integer string" else Ok z
  with _ -> Error ("invalid integer string: " ^ raw)

let big_int_of_postcard (ctx : 'ctx) (st : postcard_state) :
    (Z.t, string) result =
  let* raw = string_of_postcard ctx st in
  try Ok (Z.of_string raw) with _ -> Error ("invalid integer string: " ^ raw)

let char_of_postcard (_ctx : 'ctx) (st : postcard_state) :
    (Uchar.t, string) result =
  let* len = usize_of_postcard () st in
  if len < 1 || len > 4 then Error "invalid postcard char length"
  else
    let* bytes = take_bytes st len in
    let s = Bytes.to_string bytes in
    let decoded = String.get_utf_8_uchar s 0 in
    if Uchar.utf_decode_is_valid decoded then
      Ok (Uchar.utf_decode_uchar decoded)
    else Error "invalid postcard UTF-8 char"

let f32_of_postcard (_ctx : 'ctx) (st : postcard_state) : (float, string) result
    =
  let* bytes = take_bytes st 4 in
  let b i = Char.code (Bytes.get bytes i) in
  let bits =
    Int32.logor
      (Int32.of_int (b 0))
      (Int32.logor
         (Int32.shift_left (Int32.of_int (b 1)) 8)
         (Int32.logor
            (Int32.shift_left (Int32.of_int (b 2)) 16)
            (Int32.shift_left (Int32.of_int (b 3)) 24)))
  in
  Ok (Int32.float_of_bits bits)

let float_of_postcard (_ctx : 'ctx) (st : postcard_state) :
    (float, string) result =
  let* bytes = take_bytes st 8 in
  let b i = Int64.of_int (Char.code (Bytes.get bytes i)) in
  let bits =
    Int64.logor (b 0)
      (Int64.logor
         (Int64.shift_left (b 1) 8)
         (Int64.logor
            (Int64.shift_left (b 2) 16)
            (Int64.logor
               (Int64.shift_left (b 3) 24)
               (Int64.logor
                  (Int64.shift_left (b 4) 32)
                  (Int64.logor
                     (Int64.shift_left (b 5) 40)
                     (Int64.logor
                        (Int64.shift_left (b 6) 48)
                        (Int64.shift_left (b 7) 56)))))))
  in
  Ok (Int64.float_of_bits bits)

let list_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a list, string) result =
  let* len = usize_of_postcard ctx st in
  if len > 1_000_000 then
    Error
      ("suspicious postcard sequence length " ^ string_of_int len
     ^ " (varint read at byte "
      ^ string_of_int (st.pos - 1)
      ^ ")")
  else
    let rec loop i acc =
      if i <= 0 then Ok (List.rev acc)
      else
        let* x = a_of_postcard ctx st in
        loop (i - 1) (x :: acc)
    in
    loop len []

let option_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a option, string) result =
  let* tag = take_u8 st in
  match tag with
  | 0 -> Ok None
  | 1 ->
      let* v = a_of_postcard ctx st in
      Ok (Some v)
  | _ -> Error "invalid postcard option tag"

let box_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a, string) result =
  a_of_postcard ctx st

let pair_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result)
    (b_of_postcard : 'ctx -> postcard_state -> ('b, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a * 'b, string) result =
  let* a = a_of_postcard ctx st in
  let* b = b_of_postcard ctx st in
  Ok (a, b)

let triple_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result)
    (b_of_postcard : 'ctx -> postcard_state -> ('b, string) result)
    (c_of_postcard : 'ctx -> postcard_state -> ('c, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a * 'b * 'c, string) result =
  let* a = a_of_postcard ctx st in
  let* b = b_of_postcard ctx st in
  let* c = c_of_postcard ctx st in
  Ok (a, b, c)

let key_value_pair_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result)
    (b_of_postcard : 'ctx -> postcard_state -> ('b, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a * 'b, string) result =
  let* key = a_of_postcard ctx st in
  let* value = b_of_postcard ctx st in
  Ok (key, value)

let ensure_eof (st : postcard_state) : (unit, string) result =
  if st.pos = st.len then Ok ()
  else
    Error
      ("postcard input has trailing bytes (pos=" ^ string_of_int st.pos
     ^ ", len=" ^ string_of_int st.len ^ ")")
