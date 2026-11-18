(** Small OCaml-facing wrapper around the extracted CWasm definitions. *)

val pointer_bytes : Extract.pointerBytes

type store_record = Extract.store_record
type config_tuple = Extract.config_tuple
type res_tuple = Extract.res_tuple
type administrative_instruction = Extract.administrative_instruction

val run_v : Extract.nat -> config_tuple -> store_record * Extract.res
val run_step : config_tuple -> res_tuple
val is_const_list : administrative_instruction list -> Extract.value0 list option

val lookup_exported_function :
  string ->
  ((store_record * Extract.instance) * Extract.module_export list) ->
  config_tuple option

val interp_instantiate_wrapper :
  Extract.module0 ->
  (((store_record * Extract.instance) * Extract.module_export list) *
   Extract.nat option) option

val run_parse_module : string -> Extract.module0 option

val pp_values : Extract.value0 list -> string
val pp_store : int -> store_record -> string
val pp_res_tuple_except_store : res_tuple -> string
val pp_config_tuple_except_store : config_tuple -> string
val pp_es : administrative_instruction list -> string
