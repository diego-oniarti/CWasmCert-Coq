(** Small OCaml-facing wrapper around the extracted CWasm definitions. *)

let rec positive_of_int n =
  if n <= 1 then Extract.XH
  else if n land 1 = 0 then Extract.XO (positive_of_int (n / 2))
  else Extract.XI (positive_of_int (n / 2))

let n_value_of_int n =
  if n <= 0 then Extract.N0 else Extract.Npos (positive_of_int n)

let z_of_n = function
  | Extract.N0 -> Extract.Z0
  | Extract.Npos p -> Extract.Zpos p

let n_value_of_z = function
  | Extract.Z0 -> Extract.N0
  | Extract.Zpos p -> Extract.Npos p
  | Extract.Zneg _ -> Extract.N0

let rec zarith_of_positive = function
  | Extract.XH -> Z.one
  | Extract.XO p -> Z.shift_left (zarith_of_positive p) 1
  | Extract.XI p -> Z.succ (Z.shift_left (zarith_of_positive p) 1)

let zarith_of_n = function
  | Extract.N0 -> Z.zero
  | Extract.Npos p -> zarith_of_positive p

let zarith_of_z = function
  | Extract.Z0 -> Z.zero
  | Extract.Zpos p -> zarith_of_positive p
  | Extract.Zneg p -> Z.neg (zarith_of_positive p)

let nat8 = Convert.to_nat 8
let zero_byte = Extract.encode Extract.O
let one_byte = Extract.encode (Extract.S Extract.O)

let byte_is_zero b = b = zero_byte

let serialise_pointer (p : Extract.pointer) =
  let color_present, color =
    match p.ptr_col with
    | None -> zero_byte, Extract.N0
    | Some c -> one_byte, c
  in
  let freeable = if p.ptr_freeable then one_byte else zero_byte in
  Extract.encode_int nat8 (z_of_n p.ptr_addr)
  @ [color_present]
  @ Extract.encode_int nat8 (z_of_n color)
  @ [freeable]

let pointer_of_bytes bytes =
  let padded = bytes @ List.init 18 (fun _ -> zero_byte) in
  let address = Extract.decode_int (List.filteri (fun i _ -> i < 8) padded) in
  let color_present = List.nth padded 8 in
  let color_bytes =
    List.filteri (fun i _ -> 9 <= i && i < 17) padded
  in
  let color =
    if byte_is_zero color_present then None
    else Some (n_value_of_z (Extract.decode_int color_bytes))
  in
  let freeable = not (byte_is_zero (List.nth padded 17)) in
  {
    Extract.ptr_addr = n_value_of_z address;
    ptr_col = color;
    ptr_freeable = freeable;
  }

let pointer_bytes : Extract.pointerBytes = {
  Extract.pointer_size = n_value_of_int 18;
  serialise_pointer;
  pointer_of_bytes;
}

type store_record = Extract.store_record
type config_tuple = Extract.config_tuple
type res_tuple = Extract.res_tuple
type administrative_instruction = Extract.administrative_instruction

let run_v fuel cfg =
  Extract.Interpreter_func_extract.run_v pointer_bytes fuel Extract.O cfg

let run_step cfg =
  Extract.Interpreter_func_extract.run_step pointer_bytes Extract.O cfg

let is_const_list = Extract.Interpreter_func_extract.is_const_list

let lookup_exported_function name =
  Extract.Instantiation_func_extract.lookup_exported_function
    (Utils.explode name)

let interp_instantiate_wrapper m =
  Extract.Instantiation_func_extract.interp_instantiate_wrapper pointer_bytes m

let run_parse_module m = Extract.run_parse_module (Utils.explode m)

let pp_numerical_value = function
  | Extract.NVAL_int32 value ->
      let value = Extract.Wasm_int.Int32.unsigned (Obj.magic value) in
      "i32.const " ^ Z.to_string (zarith_of_z value)
  | Extract.NVAL_int64 value ->
      let value = Extract.Wasm_int.Int64.unsigned (Obj.magic value) in
      "i64.const " ^ Z.to_string (zarith_of_z value)
  | Extract.NVAL_float32 value ->
      let bits = Extract.Int.unsigned (Extract.Float32.to_bits (Obj.magic value)) in
      let bits = zarith_of_z bits in
      "f32.const " ^ (if Z.equal bits Z.zero then "0" else Z.format "%08x" bits)
  | Extract.NVAL_float64 value ->
      let bits =
        Extract.Int64.unsigned (Extract.Float.to_bits (Obj.magic value))
      in
      let bits = zarith_of_z bits in
      "f64.const " ^ (if Z.equal bits Z.zero then "0" else Z.format "%016x" bits)

let pp_pointer pointer =
  let color =
    match pointer.Extract.ptr_col with
    | None -> "None"
    | Some color -> Z.to_string (zarith_of_n color)
  in
  Printf.sprintf "ptr.const addr = %s, col = %s, freeable = %b"
    (Z.to_string (zarith_of_n pointer.Extract.ptr_addr))
    color pointer.Extract.ptr_freeable

let pp_value = function
  | Extract.VAL_numeric value -> pp_numerical_value value
  | Extract.VAL_pointer pointer -> pp_pointer pointer

let pp_values values =
  match values with
  | [] -> ""
  | _ -> String.concat "\n " (List.map pp_value values) ^ "\n"

let pp_store indentation store =
  Utils.implode (Extract.pp_store (Convert.to_nat indentation) store)

let pp_res_tuple_except_store result =
  Utils.implode (Extract.pp_res_tuple_except_store result)

let pp_config_tuple_except_store config =
  Utils.implode (Extract.pp_config_tuple_except_store config)

let pp_es instructions =
  Utils.implode
    (Extract.pp_administrative_instructions Extract.O instructions)
