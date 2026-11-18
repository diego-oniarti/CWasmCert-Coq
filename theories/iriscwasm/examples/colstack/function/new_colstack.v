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
  new_stack: [] -> [pointer]
  locals declared: [pointer]

  Attempts to create a new stack of i32s, by allocating a new pointer.

  Can fail non-deterministically if segalloc fails.
  Upon successful segalloc, store the offset to the top element of the stack at the start of stack (0th cell).
  The maximum number of elements that can be stored is therefore 2^14-1.

  Returns the pointer to the start of stack as i32, or dummy_pointer if memory allocation fails. Cannot trap.

  Parameters/Locals:
  0     local variable, storing the address to the start of the page for return
 *)

Definition new_stack :=
  [
    i32const 65536 ;
    BI_colalloc ;
    BI_tee_local 0 ;
    BI_isnull ;
    BI_if (Tf [] [T_pointer]) [
        BI_get_local 0
      ] [
        BI_get_local 0 ;
        i32const 0;
        BI_colstore T_i32 ;
        BI_get_local 0 
      ]                             
  ].

  
End code.

Section specs.

Lemma spec_new_stack f0 E: 
  ⊢ {{{
          ⌜ length (f_locs f0) >= 1 ⌝ ∗
            ↪[frame] f0 
    }}}
    to_e_list new_stack @ E
    {{{ v , ((∃ p, ⌜ v = immV [value_of_pointer p] ⌝ ∗ ⌜is_null p⌝) ∨
               (∃ h, ⌜ v = immV [value_of_pointer h]⌝ ∗
                             isStack h [] 
            )) ∗
              ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f1 = f_inst f0 ⌝ }}}.
Proof.
  iIntros "!>" (Φ) "(%Hflocs & Hframe) HΦ".
  simpl. rewrite separate2.
  iApply wp_seq => /=.
  iDestruct (wp_colalloc with "[$Hframe]") as "HWP" => //.
  iIntros "!>" (w) "H". iExact "H".
  iSplitR; last first.
  
  iSplitL "HWP".
  by iApply "HWP".
  2:{ iIntros "[Habs _]". iDestruct "Habs" as (?) "[% _]".  done. }
  - iIntros (w) "(H & Hf)".
    iDestruct "H" as (h) "(-> & H)".
    iSimpl. 
    rewrite separate2.
    iApply (wp_seq _ E _ (λ x, (⌜ x = immV [_] ⌝
                                        ∗ ↪[frame] {|
                                          f_locs := set_nth _ (f_locs f0) 0 _;
                                          f_inst := f_inst f0
                                        |} )%I) ).
    iSplitR.
  - iIntros "[%Habs _]" ; done.
  - iSplitL "Hf". 
    fold_const; iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite list_extra.cons_app.
    iApply wp_val_app => //=.
    iSplitR => //=.
    iIntros "!> [%Habs _]" ; done.
    fold_const; iApply (wp_set_local with "[] [$Hf]") => //=.
  - iIntros (w) "[-> Hf]".
    unfold of_val, fmap, list_fmap.
    rewrite - separate1.
    rewrite separate2.
    iApply wp_seq.
    iSplitR.
    instantiate (1 := (λ x, (⌜ if (is_null h) then
                                 x = immV [value_of_int 1]
                               else x = immV [value_of_int 0] ⌝ ∗
                                          ↪[frame] {| f_locs := set_nth _
                                                                  (f_locs f0) 0 _ ;
                                                     f_inst := f_inst f0 |})%I)).
    iIntros "[%Habs _]".
    by destruct (is_null h). 
  - instantiate (1 := VAL_pointer h). iSplitL "Hf".
    iApply (wp_isnull with "Hf").
    iNext. iPureIntro. by destruct (is_null h).

  (* If *)
  - iIntros (w) "[%Hw Hf]".
    destruct w ; try by destruct (is_null h).
    destruct l ; first by destruct (is_null h).
    destruct l ; last by destruct (is_null h).
    iSimpl.
    destruct (is_null h) eqn:Hv. 
    + (* segalloc failed *)
      inversion Hw ; subst v.
      iApply (wp_if_true with "Hf").
      intro.
      done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
      iApply wp_wand_r. 
      iSplitL "Hf".
      iApply wp_wasm_empty_ctx.
      iApply (wp_block_ctx with "Hf"). done. done. done. done.
      iIntros "!> Hf".
      iApply (wp_label_push_nil _ _ _ _ 0 (LH_base [] []) with "[Hf]") ;
        last unfold lfilled, lfill.
      simpl.
      rewrite (separate1 (AI_basic (BI_get_local 0))).
      iApply wp_seq_ctx; eauto.
      iSplitL ""; last first.
      iSplitL. 
      iApply (wp_get_local with "[] Hf").
      simpl. by rewrite set_nth_read.
      by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
      iIntros (w) "[-> Hf]". iSimpl.
      fold_const.
      iApply (wp_val_return with "Hf") => //.
      iIntros "Hf". iApply wp_value.
      unfold IntoVal. erewrite language.of_to_val => //.
      instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
      by iFrame. by iIntros "[% _]".
      iIntros (v) "[-> Hf]".
      iApply "HΦ". iSplitR "Hf"; last by iExists _; iFrame.
      iLeft. iExists h. iSplit; first done. by rewrite Hv.
    + (* grow_memory succeeded *)
      inversion Hw ; subst v.
      iApply (wp_if_false with "Hf"). done.
      iIntros "!> Hf".
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).

      iDestruct "H" as "[%Hnull | Halloc]".
      { done. }
      iDestruct "Halloc" as (c) "(%Hcol & %Hfree & Hwall & Hlive & Hs)".
      assert (Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m 65536) = 65536%N); first done.
      rewrite H.
      assert (N.to_nat 65536 = 4 + N.to_nat 65532); first done.
      rewrite H0.
      rewrite repeat_app.
      unfold repeat at 1. 
      rewrite - separate4.
      iDestruct (wcs_app (ptr_addr h) c Numeric
        [:: #00%byte; #00%byte; #00%byte; #00%byte]
        (repeat #00%byte (N.to_nat 65532)) with "Hs") as "[Hbs Hb]".
      iEval (rewrite /alloc_result_base /=) in "Hwall".
      iApply wp_wand_r.        
      iSplitL "Hf Hbs Hwall".
      * { iApply wp_wasm_empty_ctx.
          iApply (wp_block_ctx with "Hf"). done. done. done. done.
          iIntros "!> Hf".
          iApply (wp_label_push_nil _ _ _ _ 0 (LH_base [] []) with "[Hf Hbs Hwall]") ;
            last unfold lfilled, lfill.
          simpl.
          rewrite (separate1 (AI_basic (BI_get_local 0))).
          iApply wp_seq_ctx; eauto.
          iSplitL ""; last first.
          - iSplitL "Hf".
            iApply (wp_get_local with "[] [$Hf]") => /=; first by rewrite set_nth_read.
            instantiate (1 := (λ x, ( ⌜x = immV [_] ⌝)%I)) => //=.
          - 2: { simpl. by iIntros "(%HContra & _ )". }
            iIntros (w) "[-> Hf]".
            unfold of_val, fmap, list_fmap.
            simpl. 
            rewrite (separate3 (AI_pointer _)).
            iApply wp_seq_ctx.
            iSplitL ""; last first.
          - iSplitL.
            unfold i32const; fold_const.
            iApply (stack_store_i32 (p := h) (c := c)
              (ptr_addr h) 65536
              (Wasm_int.int_of_Z i32m 0)
              (Wasm_int.int_of_Z i32m 0)
              {| f_locs := set_nth (VAL_pointer h) (f_locs f0) 0
                    (VAL_pointer h);
                 f_inst := f_inst f0 |} E Hcol with
              "Hwall Hbs Hf").
          - 2: { simpl. by iIntros "[%HContra _]". }
            iIntros (w) "(-> & Hwall & Hbs & Hf)".
            unfold of_val, fmap, list_fmap.
            iSimpl.
            rewrite (separate1 (AI_basic _)).
            iApply wp_seq_ctx.
            iSplitR; last first.
            iSplitL "Hf".
            iApply (wp_get_local with "[] [$Hf]").
            simpl. rewrite set_nth_read. done.
            instantiate (1 := (λ x, (⌜ x = immV _ ⌝)%I)). done.
            2: by iIntros "[% _]".
          - iIntros (w) "[-> Hf]".
            simpl.
            iApply (wp_val_return with "Hf").
            done.
            iIntros "Hf".
            rewrite app_nil_r app_nil_l.
            iApply wp_value.
            unfold IntoVal.
            apply language.of_to_val.
            done.
            instantiate (1 := λ x, (⌜ x = immV [value_of_pointer h] ⌝ ∗ wall c (ptr_addr h) two16 ∗ points_to_i32 (ptr_addr h) c (Wasm_int.Int32.repr 0) ∗ ↪[frame] _)%I).
            iFrame. done. }
      * iIntros (w) "(-> & Hwall & Hbs & Hf)".
        iApply "HΦ".
        iSplitR "Hf"; last first.
        { iExists _.
          by iSplitL "Hf" => //.
        }
        iRight.
        iExists _. 
        iSplit; first done.
        iExists c.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iFrame "Hwall Hlive Hbs".
        iSplitR; first done.
        iExists (repeat #00%byte (N.to_nat 65532)).
        iSplit.
        { iPureIntro. rewrite repeat_length N2Nat.id. done. }
        change (N.of_nat (length []) * 4)%N with 0%N.
        rewrite N.add_0_r. iExact "Hb".

Qed.
        
End specs.

Section valid.
  Context `{!logrel_na_invs Σ, !cinvG Σ, cancelg: cancelG Σ}.
  Set Bullet Behavior "Strict Subproofs".

  Lemma interp_value_of_int i :
    ⊢ @interp_value Σ _ _ _ _ T_i32 (value_of_int i).
  Proof.
    iIntros "". unfold interp_value. simpl.
    iExists _. eauto. Qed.

  Lemma interp_value_of_uint i :
    ⊢ @interp_value Σ _ _ _ _ T_i32 (value_of_uint i).
  Proof.
    iIntros "". unfold interp_value. simpl.
    iExists _. eauto. Qed.


End valid.


End stack.    
      
