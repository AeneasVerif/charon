(** Basic utilities for postcard deserialization. *)

(** We use our own buffer rather than moving the [in_channel], which is more
    performant. *)
type postcard_state = {
  ic : in_channel;
  buf : Bytes.t;
  mutable buf_pos : int;  (** The next byte to read in [buf]. *)
  mutable buf_len : int;  (** The number of bytes read into [buf]. *)
  mutable buf_ofs : int;  (** The position in the input of [buf]'s start. *)
}

let state_of_channel (ic : in_channel) : postcard_state =
  {
    ic;
    buf = Bytes.create 65536;
    buf_pos = 0;
    buf_len = 0;
    buf_ofs = pos_in ic;
  }

(** The position of the next byte to read in the input. *)
let[@inline] pos (st : postcard_state) : int = st.buf_ofs + st.buf_pos

(** Moves to the given position of the input. *)
let[@inline] seek (st : postcard_state) (pos : int) : unit =
  seek_in st.ic pos;
  st.buf_pos <- 0;
  st.buf_len <- 0;
  st.buf_ofs <- pos

(** Reads more input into the buffer; [false] if the end of the input is
    reached. *)
let[@inline] refill (st : postcard_state) : bool =
  st.buf_ofs <- st.buf_ofs + st.buf_len;
  st.buf_pos <- 0;
  st.buf_len <- input st.ic st.buf 0 (Bytes.length st.buf);
  st.buf_len > 0

type input_format_hint = Json | Postcard | Empty

(** Attempts detecting the format of a string, which corresponds to the first N
    bytes of a file. *)
let format_hint_of_string (s : string) : input_format_hint =
  let len = String.length s in
  let rec loop i =
    if i >= len then Empty
    else
      match String.get s i with
      | ' ' | '\t' | '\n' | '\r' -> loop (i + 1)
      | '{' -> Json
      | _ -> Postcard
  in
  loop 0

(** Attempts to detect the format of a file by reading a sample of its initial
    bytes. Returns an error if the file cannot be read. *)
let format_hint_of_file (file : string) : (input_format_hint, string) result =
  try
    In_channel.with_open_bin file (fun ic ->
        let sample_len = Stdlib.min (in_channel_length ic) 64 in
        let sample = really_input_string ic sample_len in
        Ok (format_hint_of_string sample))
  with Sys_error e -> Error e

(** Same as [format_hint_of_file], but operates on an already-opened in_channel
    and restores the position after reading the sample. *)
let format_hint_of_postcard (st : postcard_state) : input_format_hint =
  let pos = pos st in
  seek st 0;
  let sample_len = min 64 (in_channel_length st.ic) in
  let sample = really_input_string st.ic sample_len in
  let hint = format_hint_of_string sample in
  seek st pos;
  hint

let ( let* ) o f =
  match o with
  | Error e -> Error e
  | Ok x -> f x

let with_state_of_file (file : string)
    (f : postcard_state -> ('a, string) result) : ('a, string) result =
  try In_channel.with_open_bin file (fun ic -> f (state_of_channel ic))
  with Sys_error e -> Error e

let combine_error_msgs (st : postcard_state) (msg : string)
    (res : ('a, string) result) : ('a, string) result =
  match res with
  | Ok x -> Ok x
  | Error e ->
      let pos = pos st in
      let rem = in_channel_length st.ic - pos in
      let n = if rem < 8 then rem else 8 in
      seek st pos;
      let preview =
        List.init n (fun _ -> try input_byte st.ic with End_of_file -> 0)
        |> List.map (fun b -> Printf.sprintf "%02x" b)
        |> String.concat " "
      in
      seek st pos;
      Error
        (msg ^ " failed at byte " ^ string_of_int pos ^ " (next: " ^ preview
       ^ "): " ^ e)

let take_u8 (st : postcard_state) : (int, string) result =
  if st.buf_pos < st.buf_len || refill st then (
    let b = Bytes.unsafe_get st.buf st.buf_pos in
    st.buf_pos <- st.buf_pos + 1;
    Ok (Char.code b))
  else Error "unexpected end of postcard input, expected 1 more byte"

let take_bytes (st : postcard_state) (len : int) : (bytes, string) result =
  let bytes = Bytes.create len in
  let rec loop ofs =
    if ofs >= len then Ok bytes
    else if st.buf_pos < st.buf_len || refill st then (
      let n = min (len - ofs) (st.buf_len - st.buf_pos) in
      Bytes.blit st.buf st.buf_pos bytes ofs n;
      st.buf_pos <- st.buf_pos + n;
      loop (ofs + n))
    else
      Error
        ("unexpected end of postcard input, expected " ^ string_of_int len
       ^ " more bytes")
  in
  loop 0

(** Reads a varint of at most [max_bytes] bytes, whose last byte is at most
    [max_last], as an OCaml int of at most [bits] bits (taken as unsigned). *)
let read_varint ~(max_bytes : int) ~(max_last : int) ~(bits : int)
    (st : postcard_state) : (int, string) result =
  let rec loop (i : int) (shift : int) (acc : int) : (int, string) result =
    if i >= max_bytes then Error "invalid postcard varint"
    else
      let* raw = take_u8 st in
      let payload = raw land 0x7F in
      if payload <> 0 && (shift >= bits || payload lsr (bits - shift) <> 0) then
        Error "integer out of OCaml int range"
      else
        let acc = acc lor (payload lsl shift) in
        let has_more = raw land 0x80 <> 0 in
        if not has_more then
          if i = max_bytes - 1 && raw > max_last then
            Error "invalid postcard varint terminal byte"
          else Ok acc
        else loop (i + 1) (shift + 7) acc
  in
  loop 0 0 0

(** Unsigned integers, of at most 62 bits. *)
let read_unsigned ~max_bytes ~max_last st =
  read_varint ~max_bytes ~max_last ~bits:62 st

(** Zigzag-encoded signed integers, of at most 63 bits. *)
let read_signed ~max_bytes ~max_last st =
  let* z = read_varint ~max_bytes ~max_last ~bits:63 st in
  Ok ((z lsr 1) lxor -(z land 1))

let usize_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result
    =
  read_unsigned ~max_bytes:10 ~max_last:1 st

let bool_of_postcard (_ctx : 'ctx) (st : postcard_state) : (bool, string) result
    =
  let* b = take_u8 st in
  match b with
  | 0 -> Ok false
  | 1 -> Ok true
  | _ -> Error "invalid postcard bool"

let int_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  read_unsigned ~max_bytes:5 ~max_last:15 st

let u16_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  read_unsigned ~max_bytes:3 ~max_last:3 st

let u32_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  read_unsigned ~max_bytes:5 ~max_last:15 st

let u64_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  read_unsigned ~max_bytes:10 ~max_last:1 st

let i16_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  read_signed ~max_bytes:3 ~max_last:3 st

let i32_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  read_signed ~max_bytes:5 ~max_last:15 st

let i64_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result =
  read_signed ~max_bytes:10 ~max_last:1 st

let isize_of_postcard (_ctx : 'ctx) (st : postcard_state) : (int, string) result
    =
  read_signed ~max_bytes:10 ~max_last:1 st

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
  (* this is a little scary, but we never access the array unless we have
     computed all indices, so it's fine. going through an array is more memory
     efficient than a list, which we would have to reverse. *)
  let arr = Array.make len (Obj.magic 0) in
  let rec loop i =
    if i == len then Ok (Array.to_list arr)
    else
      let* x = a_of_postcard ctx st in
      Array.set arr i x;
      loop (i + 1)
  in
  loop 0

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

let range_inclusive_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a * 'a, string) result =
  let* a = a_of_postcard ctx st in
  let* b = a_of_postcard ctx st in
  Ok (a, b)

let key_value_pair_of_postcard
    (a_of_postcard : 'ctx -> postcard_state -> ('a, string) result)
    (b_of_postcard : 'ctx -> postcard_state -> ('b, string) result) (ctx : 'ctx)
    (st : postcard_state) : ('a * 'b, string) result =
  let* key = a_of_postcard ctx st in
  let* value = b_of_postcard ctx st in
  Ok (key, value)

let ensure_eof (st : postcard_state) : (unit, string) result =
  let len = in_channel_length st.ic in
  let pos = pos st in
  if pos >= len then Ok ()
  else
    Format.kasprintf Result.error
      "postcard input has trailing bytes (pos=%d, len=%d)" pos len
