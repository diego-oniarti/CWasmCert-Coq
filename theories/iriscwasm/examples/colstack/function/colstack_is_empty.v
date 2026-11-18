From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From CWasm.iriscwasm.examples.colstack Require Export colstack_common.
From CWasm.iriscwasm.logrel Require Import iris_fundamental.
From CWasm.iriscwasm.rules Require Import proofmode iris_rules.
From CWasm.iriscwasm.language Require Import iris_wp_def.
From CWasm.iriscwasm.helpers.prelude Require Import iris_reduce_properties.
From CWasm Require Import opsem stdpp_aux common.

Close Scope byte_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section stack.

 Context `{!wasmG Σ, HPB: PointerBytes}. 
 
Section code.

(*
  is_empty: [pointer] -> [i32]
  locals declared: []

  Given a stack pointer, determine if the stack is empty.

  Implemented by comparing the stored top offset against zero.


  Returns 1 if the stack is empty, 0 otherwise.

  Parameters/Locals:
  0 (input)     stack pointer
*)
Definition is_empty :=
  [
    i32const 0;
    BI_get_local 0 ;
    BI_colload T_i32;
    BI_relop T_i32 (Relop_i ROI_eq)
  ].



End code.



Section specs.
  Set Bullet Behavior "Strict Subproofs".
  
Lemma spec_is_empty f0 v s E: 
  ⊢ {{{ 
        ⌜ (f_locs f0) !! 0 = Some (value_of_pointer v) ⌝ ∗ 
        ↪[frame] f0 ∗
        isStack v s }}}
    to_e_list is_empty @  E
    {{{ w, ∃ k, ⌜ w = immV [value_of_int k] ⌝ ∗ isStack v s ∗
                           ⌜ (k = 1 /\ s = []) \/
                  (k = 0 /\ s <> []) ⌝ ∗
           ↪[frame] f0}}}.
Proof.
  iIntros "!>" (Φ) "(%Hlocv & Hf & Hstack) HΦ" => /=.

  iDestruct (stack_pure with "Hstack") as (c) "(%Hcol & %Hfree & %Hstack)". 
  
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 0; value_of_pointer v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR.
  by iIntros "[%Habs _]".
  iSplitL "Hf".
  { rewrite separate1.
    iApply wp_val_app => //=.
    iSplitR. by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=. }
  iIntros (w) "[-> Hf]".
  iSimpl. 
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_int 0; value_of_int (length s * 4)] ⌝ ∗ ↪[frame] f0 ∗ isStack v s )%I).
  iSplitR.
  by iIntros "[%Habs _]".
  iSplitL "Hf Hstack".
  { rewrite separate1.
    iApply wp_val_app => //=.
    iSplitR.
    by iIntros "!> [%Habs _]".
    iApply (wp_wand with "[Hf Hstack]").
    { iApply (stack_load_0 with "Hstack Hf"). }
    iIntros (w) "(-> & Hstack & Hf)". iFrame.
    iPureIntro. unfold value_of_int, value_of_uint.
    assert (Z.of_N (N.of_nat (length s) * 4) = length s * 4)%Z as -> by lia.
    done.
  }
  iIntros (w) "(-> & Hf & Hstack)".
  iSimpl. 
  iApply wp_wand_r.
  iSplitL "Hf". 
  fold_const; iApply (wp_relop with "Hf") => //=.
  by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
  { iIntros (w) "[-> Hf]".
    iApply "HΦ".
    iExists _.
    iSplitR.
    iPureIntro.
    unfold value_of_int.
    unfold wasm_bool.
    repeat f_equal.
    instantiate (1 := if (Wasm_int.Int32.eq (Wasm_int.Int32.repr 0)
                            (Wasm_int.Int32.repr (length s * 4)))
                           then 1%Z else 0%Z). 
    remember (Wasm_int.Int32.eq (Wasm_int.Int32.repr 0)
                (Wasm_int.Int32.repr (length s * 4))) as cmpres.
    rewrite - Heqcmpres. by destruct cmpres => //=.
    iFrame "Hstack Hf".
    iPureIntro.
    destruct s.
    left.
    split => //=.
    right.
    split => //=.
    rewrite Wasm_int.Int32.eq_false => //=.
    intro.
    apply Wasm_int.Int32.repr_inv in H. lia.
    rewrite u32_modulus. lia. rewrite u32_modulus. unfold two14 in Hstack.
    simpl in Hstack. lia. }
Qed.



End specs.


End stack.    
      

