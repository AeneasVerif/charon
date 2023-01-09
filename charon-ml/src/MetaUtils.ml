open Meta

let loc_min (l0 : loc) (l1 : loc) : loc =
  if l0.line = l1.line then { line = l0.line; col = Int.min l0.col l1.col }
  else if l0.line < l1.line then l0
  else l1

let loc_max (l0 : loc) (l1 : loc) : loc =
  if l0.line = l1.line then { line = l0.line; col = Int.max l0.col l1.col }
  else if l0.line > l1.line then l0
  else l1

(** See the comments in [meta_utils.rs] in Charon. *)
let combine_meta (m0 : meta) (m1 : meta) : meta =
  assert (m0.span.file = m1.span.file);
  let span =
    {
      file = m0.span.file;
      beg_loc = loc_min m0.span.beg_loc m1.span.beg_loc;
      end_loc = loc_max m0.span.end_loc m1.span.end_loc;
    }
  in
  { span; generated_from_span = None }
