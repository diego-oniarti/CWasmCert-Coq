open Output

let ( let* ) = Out.( let* )
let pure = Out.pure

let error message = Error message

let rec user_input prompt callback state =
  match LNoise.linenoise prompt with
  | None -> pure ()
  | Some input ->
      let* state' = callback input state in
      user_input prompt callback state'

let string_of_crash_reason = function
  | Extract.C_error -> "error"
  | Extract.C_exhaustion -> "fuel exhaustion"

let take_step verbosity config =
  let step_result = Shim.run_step config in
  debug_info verbosity intermediate (fun () ->
    Shim.pp_res_tuple_except_store step_result);
  match step_result with
  | (_, Extract.RS_crash reason) ->
      debug_info verbosity result ~style:red (fun () ->
        "crash: " ^ string_of_crash_reason reason ^ "\n");
      pure config
  | (_, Extract.RS_break _) ->
      debug_info verbosity result ~style:red (fun () -> "break\n");
      pure config
  | (_, Extract.RS_return values) ->
      debug_info verbosity result ~style:green (fun () ->
        "return: " ^ Shim.pp_values values ^ "\n");
      pure config
  | (_, Extract.RS_call_host _) ->
      error "host calls are not supported by the standalone interpreter"
  | ((store, frame), Extract.RS_normal instructions) ->
      pure ((store, frame), instructions)

let repl verbosity store_instance_exports name =
  LNoise.set_hints_callback (fun line ->
    if line <> "git remote add " then None
    else Some (" <this is the remote name> <this is the remote URL>",
               LNoise.Yellow, true));
  ignore (LNoise.history_load ~filename:"history.txt");
  ignore (LNoise.history_set ~max_length:100);
  LNoise.set_completion_callback (fun line completions ->
    (if line = "" || line.[0] = 's' then ["step"; "store"] else [])
    |> List.iter (LNoise.add_completion completions));
  ["interactive CWasm interpreter";
   "get tab completion with <TAB>";
   "type quit to exit gracefully"]
  |> List.iter print_endline;
  let ((store, _), _) = store_instance_exports in
  match Shim.lookup_exported_function name store_instance_exports with
  | None -> error ("unknown function `" ^ name ^ "`")
  | Some initial_config ->
      debug_info verbosity result (fun () ->
        Printf.sprintf "\n%sand store\n%s\n%!"
          (Shim.pp_config_tuple_except_store initial_config)
          (Shim.pp_store 1 store));
      let callback input config =
        if input = "quit" then exit 0;
        ignore (LNoise.history_add input);
        ignore (LNoise.history_save ~filename:"history.txt");
        if input = "" || input = "step" then take_step verbosity config
        else if input = "s" || input = "store" then begin
          let ((current_store, _), _) = config in
          print_endline (Shim.pp_store 0 current_store);
          pure config
        end else if input = "help" then begin
          print_endline
            "commands:\nstep: take a step\nstore: display the store\nquit: quit\nhelp: display this message";
          pure config
        end else begin
          print_endline "unknown command";
          pure config
        end
      in
      user_input "> " callback initial_config

let interpret verbosity error_code_on_crash store_instance_exports name =
  let* initial_config =
    ovpending verbosity stage "interpreting" (fun () ->
      match Shim.lookup_exported_function name store_instance_exports with
      | None -> Error ("unknown function `" ^ name ^ "`")
      | Some config -> OK config)
  in
  let print_step_header generation =
    debug_info verbosity intermediate ~style:bold (fun () ->
      Printf.sprintf "step %d:\n" generation)
  in
  let rec evaluate generation (((_current_store, _frame), instructions) as config) =
    match Shim.is_const_list instructions with
    | Some values ->
        debug_info verbosity stage ~style:green (fun () ->
          Printf.sprintf "success after %d steps\n" generation);
        pure (Some values)
    | None ->
        let step_result = Shim.run_step config in
        print_step_header generation;
        debug_info verbosity intermediate (fun () ->
          Shim.pp_res_tuple_except_store step_result);
        debug_info verbosity store (fun () ->
          let ((store', _), _) = step_result in
          Printf.sprintf "and store\n%s" (Shim.pp_store 1 store'));
        match step_result with
        | (_, Extract.RS_crash reason) ->
            wait_message verbosity;
            debug_info verbosity result ~style:red (fun () ->
              "crash: " ^ string_of_crash_reason reason ^ "\n");
            pure None
        | (_, Extract.RS_break _) ->
            wait_message verbosity;
            debug_info verbosity result ~style:red (fun () -> "break\n");
            pure None
        | (_, Extract.RS_return values) ->
            wait_message verbosity;
            debug_info verbosity result ~style:green (fun () ->
              "return " ^ Shim.pp_values values ^ "\n");
            pure (Some values)
        | (_, Extract.RS_call_host _) ->
            error "host calls are not supported by the standalone interpreter"
        | ((store', frame'), Extract.RS_normal instructions') ->
            evaluate (generation + 1) ((store', frame'), instructions')
  in
  print_step_header 0;
  debug_info verbosity intermediate (fun () ->
    "\n" ^ Shim.pp_config_tuple_except_store initial_config ^ "\n");
  let* result_values = evaluate 1 initial_config in
  debug_info_span verbosity result stage (fun () ->
    match result_values with
    | Some values -> Shim.pp_values values
    | None -> "");
  if error_code_on_crash && result_values = None then exit 1 else pure ()

let instantiate_interpret verbosity interactive _no_context_optimisation
    error_code_on_crash parsed_module name =
  let* store_instance_exports =
    ovpending verbosity stage "instantiation" (fun () ->
      match Shim.interp_instantiate_wrapper parsed_module with
      | None -> Error "instantiation error"
      | Some (result, _) -> OK result)
  in
  if interactive then repl verbosity store_instance_exports name
  else interpret verbosity error_code_on_crash store_instance_exports name
