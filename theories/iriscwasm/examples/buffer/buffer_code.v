From mathcomp Require Import ssreflect eqtype seq ssrbool.
From Coq Require Import ZArith.

From CWasm Require Import stdpp_aux color_ptr datatypes operations typing
  type_checker_reflects_typing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Buffer_code.

  Context {HPB : PointerBytes}.

  (* The client keeps both allocating pointers private.  It passes only a
     freshly demoted copy of [local_p2] to the imported function [fun_adv]. *)
  Definition local_p1 := 0.
  Definition local_p2 := 1.
  Definition fun_adv := 0.
  Definition global_result := 0.

  Definition buffer_size : numerical_value :=
    NVAL_int32 (Wasm_int.int_of_Z i32m 4%Z).
  Definition buffer_value : numerical_value :=
    NVAL_int32 (Wasm_int.int_of_Z i32m 42%Z).

  (*
     p1 := colalloc(4);
     p2 := colalloc(4);
     colstore_i32(p1, 42);
     adversary(demote(p2));
     result := colload_i32(p1);
     colfree(p2)

     The original freeable [p2] remains in [local_p2].  The adversary sees
     only its demoted copy.  The fractional logical relation keeps half of
     [p2]'s cancellation authority private across the call, so the halves can
     be recombined when the original pointer is freed afterwards.
   *)
  Definition buffer_setup : list basic_instruction :=
    [:: BI_const buffer_size;
      BI_colalloc;
      BI_set_local local_p1;

      BI_const buffer_size;
      BI_colalloc;
      BI_set_local local_p2;

      BI_get_local local_p1;
      BI_const buffer_value;
      BI_colstore T_i32
    ].

  Definition buffer_suffix : list basic_instruction :=
    [:: BI_get_local local_p2;
      BI_demote;
      BI_call fun_adv;

      BI_get_local local_p1;
      BI_colload T_i32;
      BI_set_global global_result;

      BI_get_local local_p2;
      BI_colfree
    ].

  Definition buffer_program : list basic_instruction :=
    buffer_setup ++ buffer_suffix.

  Definition buffer_context : t_context :=
    {| tc_types_t := [::];
       tc_func_t := [:: Tf [:: T_pointer] [::]];
       tc_global := [:: {| tg_mut := MUT_mut; tg_t := T_i32 |}];
       tc_table := [::];
       tc_memory := [::];
       tc_local := [:: T_pointer; T_pointer];
       tc_label := [:: [::]];
       tc_return := Some [::] |}.

  Lemma buffer_program_typing :
    be_typing buffer_context buffer_program (Tf [::] [::]).
  Proof.
    apply/b_e_type_checker_reflects_typing => /=.
    by apply/eqP.
  Qed.

End Buffer_code.
