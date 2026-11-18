(** Extraction to OCaml. **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

From Coq Require Extraction.

From CWasm Require Import
  datatypes_properties
  binary_format_parser
  instantiation_func
  interpreter_func
  type_checker
  pp.

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString.

Extraction Language OCaml.

(** The CWasm interpreter is parameterised by the abstract [PointerBytes]
    interface.  Keep that parameter visible in the extracted API so that the
    OCaml front-end can choose the concrete finite representation used by the
    executable. *)
Module Interpreter_func_extract.

Definition run_v := @interpreter_func.run_v.
Definition run_step := @interpreter_func.run_step.

Definition is_const_list : list administrative_instruction -> option (list value) :=
  fun es => if const_list es then Some (fst (split_vals_e es)) else None.

End Interpreter_func_extract.

Extraction "extract"
  run_parse_module
  Instantiation_func_extract
  Interpreter_func_extract
  value_rec_safe
  pp_values
  pp_store
  pp_res_tuple_except_store
  pp_config_tuple_except_store
  pp_administrative_instructions
  .
