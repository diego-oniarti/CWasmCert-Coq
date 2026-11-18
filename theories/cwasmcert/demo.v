From CWasm Require Import datatypes operations colored_memory color_ptr interpreter_func.
From stdpp Require Import gmap.

#[export] Instance demo_PointerBytes : PointerBytes.
Proof.
  refine ({|
    pointer_size := 1%N;
    serialise_pointer := fun _ => [Integers.Byte.zero];
    pointer_of_bytes := fun _ => dummy_pointer;
    size_is_not_zero := _;
    length_serialise := _;
    pointer_of_serialise := _;
    serialise_pointer_of := _;
  |}).
  - by compute.
  - intro h; compute; reflexivity.
  - admit.
  - admit.
Admitted.

Definition init_store : store_record :=
  Build_store_record
    []                              (* s_funcs  *)
    []                              (* s_tables *)
    []                              (* s_mems   *)
    dummy_cmem                      (* s_cmems  *)
    {| allocated := gmap.gmap_empty; next_free := 0%N |}  (* s_alls *)
    [].                             (* s_globals *)

(** Frame with three local slots for seg/get. *)
Definition init_frame : frame :=
  Build_frame [VAL_int32 (Wasm_int.Int32.repr 0); VAL_int32 (Wasm_int.Int32.repr 0); VAL_int32 (Wasm_int.Int32.repr 0)] empty_instance.

(**
  Demo 1 - success
*)
Definition demo_success : list administrative_instruction :=
  [ AI_const (VAL_int32 (Wasm_int.Int32.repr 8));
      AI_basic BI_colalloc;
      AI_const (VAL_int32 (Wasm_int.Int32.repr 4));
      AI_basic BI_colalloc;
      AI_basic BI_drop;
      AI_basic (BI_set_local 0);
      AI_basic (BI_get_local 0);
      AI_const (VAL_int32 (Wasm_int.Int32.repr 42));
      AI_basic (BI_colstore T_i32);
      AI_const (VAL_int32 (Wasm_int.Int32.repr 4));
      AI_basic (BI_get_local 0);
      AI_basic BI_pointeradd;
      AI_const (VAL_int32 (Wasm_int.Int32.repr 7));
      AI_basic (BI_colstore T_i32);
      AI_basic (BI_get_local 0);
      AI_basic (BI_colload T_i32);
      AI_const (VAL_int32 (Wasm_int.Int32.repr 4));
      AI_basic (BI_get_local 0);
      AI_basic BI_pointeradd;
      AI_basic (BI_colload T_i32);
      AI_basic (BI_binop T_i32 (Binop_i BOI_add))].

(*
Compute run_v 1000 0 (init_store, init_frame, demo_success).
 *)

(**
  Demo 2 - trap
*)
Definition demo_trap : list administrative_instruction :=
  [ AI_const (VAL_int32 (Wasm_int.Int32.repr 8));
      AI_basic BI_colalloc;
      AI_basic (BI_set_local 0);
      AI_const (VAL_int32 (Wasm_int.Int32.repr 8));
      AI_basic (BI_get_local 0);
      AI_basic BI_pointeradd;
      AI_basic (BI_colload T_i32)].

(*
Compute run_v 1000 0 (init_store, init_frame, demo_trap).
 *)

(*
Eval compute in run_step 0 (init_store, init_frame, demo_success).
 *)

