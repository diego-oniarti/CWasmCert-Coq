From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From CWasm.iriscwasm.examples.colstack Require Export colstack_common colstack_is_empty.
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

 Context `{!wasmG Σ, HPB:PointerBytes}. 

Section code.


(*
  pop: [pointer] -> [i32]
  locals declared: [i32]

  Given a stack pointer, pop the top i32 value from the stack.

  Implementation contains the is_empty check which results in a trap if the stack is empty. Otherwise, load the 
  stack top pointer from the stack pointer address, retrieve the value to be popped, then decrement the stack
  top pointer address by 4 and update it.
  
  Returns the popped value of type i32. Can trap only if the stack pointer is invalid or the stack is empty.

  Parameters/Locals:
  0 (input)     stack pointer
  1             temporary variable storing the new address of the stack top pointer
*)
Definition pop :=
  is_empty ++
  [
    BI_if (Tf [] []) [BI_unreachable] [];
    BI_get_local 0 ;
    BI_colload T_i32 ;
    BI_tee_local 1 ;
    BI_get_local 0 ;
    BI_pointeradd ;
    BI_colload T_i32 ;
    BI_get_local 0 ;
    BI_get_local 1 ;
    i32const 4 ;
    BI_binop T_i32 (Binop_i BOI_sub) ;
    BI_colstore T_i32 
  ].

End code.

Section specs.

Lemma spec_pop f0 (v: pointer) (a : i32) s E:
  ⊢ {{{ 
          ⌜ f0.(f_locs) !! 0 = Some (value_of_pointer v) ⌝
         ∗ ⌜ length f0.(f_locs) >= 2 ⌝
         ∗ isStack v (a :: s)
         ∗ ↪[frame] f0 }}}
    to_e_list pop @ E
    {{{ w, ⌜ w = immV [VAL_int32 a] ⌝ ∗
                      isStack v s ∗
                      ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hlocv & %Hlocs & Hstack & Hf) HΦ" => /=.
  
  iDestruct (stack_pure with "Hstack") as (c) "(%Hcol & %Hfree & %Hlen)".
  
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ x,  (⌜x = immV [value_of_int 0]⌝ ∗ isStack v (a :: s) ∗ ↪[frame] f0)%I).
  iSplitR; last iSplitL "Hstack Hf".
  2: { iApply (spec_is_empty with "[$Hstack $Hf]") => //.
       iIntros (w) "H".
       iDestruct "H" as (k) "(-> & Hstack & %Hk & Hf)".
       iFrame "Hstack Hf".
       by destruct Hk as [[-> ?] | [-> _]] => //.
  }
  { by iIntros "(%Habs & ?)". }
  
  iIntros (w) "(-> & Hstack & Hf)".
  simpl.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV [ ]⌝ ∗ ↪[frame] f0)%I).
  iSplitR; first by iIntros "(%H & _)".
  iSplitL "Hf".
  iApply (wp_if_false with "Hf") => //.
  { iIntros "!> Hf".
    take_drop_app_rewrite 0.
    iApply (wp_block with "Hf") => //.
    iIntros "!> Hf /=".
      by iApply (wp_label_value with "Hf").
  }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ x, (⌜ x = immV [value_of_pointer v] ⌝ ∗ ↪[frame] f0)%I).
  iSplitR ; first by iIntros "[%Habs _]".
  iSplitL "Hf".
  - iApply (wp_get_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite separate2.
    iApply wp_seq.
    iSplitR ; last iSplitL "Hstack Hf".
    2: { by iApply (stack_load_0 with "[$] [$]") => //. }
    { by iIntros "(%Habs & _)". }
    
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    rewrite separate2.
    iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [_] ⌝
                                           ∗ ↪[frame] _)%I)).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - fold_const; iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "[]Hf") => //.
    
  - iIntros (w) "[-> Hf]".
    iSimpl. 
    rewrite separate2.
    iApply wp_seq.
    iSplitR; last iSplitL "Hf".
    2: {
      rewrite (separate1 (AI_basic _)).
      iApply wp_val_app => //.
      iSplitR; last first.
      iApply wp_wand_r. iSplitL. iApply (wp_get_local with "[] Hf").
      simpl. unfold set_nth. destruct (f_locs f0); first by inversion Hlocs.
      simpl. done.
      
      by instantiate (1 := λ x, (⌜ x = immV [value_of_pointer v] ⌝)%I).
      iIntros (w) "[-> Hf]".
      instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
      iFrame. done.
      by iIntros "!> [% _]". }
    { by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.
    rewrite separate4.
    iApply wp_seq.
    iSplitR; last iSplitL "Hf Hstack".
    2:{
      iApply (stack_load_j_alt with "[] [] [] [$Hstack] [$Hf]") => //.
      { iPureIntro => /=.
        instantiate (1 := 0%N). lia. }
      { by instantiate (1 := a) => /=. }
      { done. } 
    }
    { by iIntros "(%Habs & _)". }
    
  - iIntros (w) "(-> & Hstack & Hf)" => /=.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate1.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    subst.
    iApply (wp_get_local with "[] [$Hf]") => //=.
    unfold set_nth.
    destruct (f_locs f0); first by inversion Hlocs.
    done.
    
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                    ↪[frame] _)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
  - rewrite separate2.
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] [$Hf]") => //=.
    by rewrite set_nth_read.
      
  - iIntros (w) "[-> Hf]".
    iSimpl.
    rewrite separate5.
    iApply wp_seq.
    instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗
                                       ↪[frame] _)%I).
    iSplitR ; first by iIntros "[%Habs _]".
    iSplitL "Hf".
    rewrite (separate2 (AI_basic _)).
    iApply wp_val_app => //.
    iSplitR ; first by iIntros "!> [%Habs _]".
    unfold i32const; fold_const; iApply (wp_binop with "Hf") => //.
    simpl.
  - iIntros (w) "[-> Hf]".
    iSimpl.
    iDestruct "Hstack" as (col)
      "(%Hcol' & %Hfree' & %Hlen' & Hwall & Hlive & Hbase & Helems & Htail)".
    have Hsub : Wasm_int.Int32.isub
        (Wasm_int.Int32.repr (Z.of_N (N.of_nat (length (a :: s)) * 4)))
        (Wasm_int.Int32.repr 4) =
      Wasm_int.Int32.repr (Z.of_N (N.of_nat (length s) * 4)).
    { unfold Wasm_int.Int32.isub, Wasm_int.Int32.sub.
      rewrite !wasm_int_unsigned; try (unfold two14 in Hlen'; simpl in Hlen'; lia).
      f_equal. simpl. lia.
      unfold two14 in Hlen'. rewrite cons_length in Hlen'.
      rewrite cons_length. lia.
    }
    iApply wp_wand_r.
    iSplitL "Hwall Hbase Hf".
  - rewrite (separate1 (AI_basic _)).
    iApply wp_val_app => //.
    iSplit; last first.
    fold_const.
    change (Wasm_int.Int32.isub _ _) with
      (Wasm_int.Int32.isub
        (Wasm_int.Int32.repr (Z.of_N (N.of_nat (length (a :: s)) * 4)))
        (Wasm_int.Int32.repr 4)).
    rewrite Hsub.
    iApply (wp_wand with "[-]").
    { iApply (stack_store_i32 (ptr_addr v) two16
      (Wasm_int.Int32.repr (Z.of_N (N.of_nat (length (a :: s)) * 4)))
      (Wasm_int.Int32.repr (Z.of_N (N.of_nat (length s) * 4)))
      _ E Hcol' with "Hwall Hbase Hf"). }
    iIntros (w) "(-> & Hwall & Hbase & Hf)".
    instantiate (1 := λ w, (⌜w = immV [VAL_int32 a]⌝ ∗
      wall col (ptr_addr v) two16 ∗
      points_to_i32 (ptr_addr v) col
        (Wasm_int.Int32.repr (Z.of_N (N.of_nat (length s) * 4))) ∗
      ↪[frame] _)%I).
    iFrame. done.
    by iIntros "!> [%Htrap _]".
  - iIntros (w) "(-> & Hwall & Hbase & Hf)".
    iApply "HΦ". iSplit; first done.
    iSplitR "Hf"; last by iExists _; iFrame.
    iExists col.
    iSplit; first done.
    iSplit; first done.
    iSplit; first (iPureIntro; rewrite cons_length in Hlen'; lia).
    iFrame "Hwall Hlive Hbase".
    iDestruct "Helems" as "[Ha Hs]".
    iSplitL "Hs".
    { iApply (big_sepL_impl with "Hs").
      iIntros "!>" (k y Hk) "Hy".
      iApply (points_to_i32_eq with "Hy") => //.
      rewrite cons_length. lia. }
    iDestruct "Htail" as (bs) "[%Hbs Htail]".
    iExists (serialise_i32 a ++ bs).
    iSplit.
    { iPureIntro. rewrite app_length Nat2N.inj_add Hbs.
      have Hfour : length (serialise_i32 a) = 4 by done.
      rewrite Hfour cons_length. unfold two16, two14 in *.
      rewrite cons_length in Hlen'. lia. }
    iApply (wcs_app (ptr_addr v + N.of_nat (length s) * 4 + 4)%N
      col Numeric (serialise_i32 a) bs).
    iSplitL "Ha".
    { unfold points_to_i32. rewrite N.mul_0_r N.sub_0_r.
      replace (ptr_addr v + N.of_nat (length s) * 4 + 4)%N
        with (ptr_addr v + N.of_nat (length (a :: s)) * 4)%N by
          (rewrite cons_length; lia).
      iExact "Ha". }
    have Hfour : length (serialise_i32 a) = 4 by done.
    rewrite Hfour.
    replace (ptr_addr v + N.of_nat (length s) * 4 + 4 + N.of_nat 4)%N
      with (ptr_addr v + N.of_nat (length (a :: s)) * 4 + 4)%N by
        (rewrite cons_length; lia).
    iExact "Htail".

Qed.    



End specs.

End stack.    
      
