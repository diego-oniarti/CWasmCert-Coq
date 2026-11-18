(** Running parsed CWasm modules through the extracted functional interpreter. *)

val repl :
  Output.verbosity ->
  ((Shim.store_record * Extract.instance) * Extract.module_export list) ->
  string -> unit Output.out

val interpret :
  Output.verbosity -> bool ->
  ((Shim.store_record * Extract.instance) * Extract.module_export list) ->
  string -> unit Output.out

val instantiate_interpret :
  Output.verbosity -> bool -> bool -> bool -> Extract.module0 -> string ->
  unit Output.out
