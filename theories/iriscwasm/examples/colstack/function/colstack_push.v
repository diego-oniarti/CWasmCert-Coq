From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From CWasm.iriscwasm.examples.colstack Require Export colstack_common colstack_is_full.
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
  push: [pointer, i32] -> []
  locals declared: [i32]

  Given a stack pointer and an i32, push the i32 to the top of the stack.

  Implementation contains the is_full check which results in a trap if the stack is full. Otherwise, load the 
  stack top pointer from the stack pointer address, increment it by 4, store the given i32 to the new cell and 
  update the stack top pointer. Does not cause u32 overflow when the stack pointer is at the last page 
  of memory.
  
  Returns nothing. Can trap only if the stack pointer is invalid or the stack is full.

  Parameters/Locals:
  0 (input)     stack pointer
  1 (input)     i32 value to be pushed
  2             temporary variable storing the new address of the stack top pointer
*)
    Definition push :=
      is_full ++ 
     [
       BI_if (Tf [] []) [BI_unreachable] [];
       BI_get_local 0 ;
       BI_colload T_i32;
       i32const 4 ;
       BI_binop T_i32 (Binop_i BOI_add) ;
       BI_tee_local 2 ;
       BI_get_local 0 ;
       BI_pointeradd ;
       BI_get_local 1 ;
       BI_colstore T_i32;
       BI_get_local 0 ;
       BI_get_local 2 ;
       BI_colstore T_i32 
      ].
        
  End code.

  Section specs.
    
    Lemma spec_push f0 (v: pointer) (a : i32) s E :
      ⊢ {{{ 
           ⌜ f0.(f_locs) !! 0 = Some (value_of_pointer v) ⌝
          ∗ ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 a) ⌝ 
          ∗ ⌜ length f0.(f_locs) >= 3 ⌝
          ∗ ⌜ (N.of_nat (length s) < two14 - 1)%N ⌝
          ∗ isStack v s
          ∗ ↪[frame] f0 }}}
        to_e_list push @ E
        {{{ w, ⌜ w = immV [] ⌝ ∗
                       isStack v (a :: s) ∗
                       ∃ f1, ↪[frame] f1 ∗ ⌜ f_inst f0 = f_inst f1 ⌝ }}}. 
    Proof.
      iIntros "!>" (Φ) "(%Hlocv & %Hloca & %Hlocs & %Hlens & Hstack & Hf) HΦ" => /=.
      
      iDestruct (stack_pure with "Hstack") as (c) "(%Hcol & %Hfree & %Hlen)".
      
      rewrite (separate4 (AI_basic _)).
      iApply wp_seq.
      iSplitR; last iSplitL "Hf Hstack".
      2: { iApply (spec_is_full with "[$Hf $Hstack] []") => //.
           iIntros (w) "H".
           by iApply "H".
      }
      { iIntros "H".
        by iDestruct "H" as (k) "(%Habs & ?)".
      }           

      iIntros (w) "H".
      iDestruct "H" as (k) "(-> & Hstack & %Hret & Hf)".
      destruct Hret as [Hret | Hret] => //.
      { destruct Hret as [-> Hlens'].
        rewrite Hlens' in Hlens. lia.
      }

      destruct Hret as [-> _] => /=.

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
      
      instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] f0)%I).
      iSplitR ; first by iIntros "[%Habs _]".
      iSplitL "Hf".
      - iApply (wp_get_local with "[] [$Hf]") => //=.
      - iIntros (w) "[-> Hf]".
        simpl.
        rewrite separate2.
        iApply wp_seq.
        instantiate ( 1 := λ x, ((⌜ x = immV [value_of_uint (N.of_nat (length s) * 4)] ⌝ ∗ isStack v s ∗ ↪[frame] f0)%I)).
        iSplitR ; first by iIntros "(%Habs & _)".
        iSplitR "HΦ".
        { by iApply (stack_load_0 with "[$] [$]") => //. }

      - iIntros (w) "(-> & Hstack & Hf)" => /=.
        rewrite separate3.
        iApply (wp_seq _ _ _ (λ x, (⌜ x = immV [value_of_uint (4 + N.of_nat (length s) * 4)] ⌝
                                            ∗ ↪[frame] _)%I)).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
        unfold i32const; fold_const; iApply (wp_binop with "Hf") => //.
        iIntros "!>".
        iPureIntro.
        unfold value_of_int, value_of_uint => /=.
        repeat f_equal.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add => /=.
        f_equal.
        rewrite Wasm_int.Int32.Z_mod_modulus_eq.
        rewrite Z.mod_small ; first by lias.
        rewrite u32_modulus. unfold two14 in Hlen. 
        remember (length s) as x.
        rewrite -Heqx.
        by lias. 
      - iIntros (w) "[-> Hf]".
        simpl.
        rewrite separate2.
        iApply wp_seq; iSplitR; last iSplitL "Hf".
        instantiate (1 := λ w, (⌜ w = immV [value_of_uint (4 + N.of_nat (length s) * 4)] ⌝ ∗ ↪[frame] _) %I).
        2: {
          fold_const; iApply (wp_tee_local with "Hf").
             iIntros "!> Hf".
             rewrite separate1.
             iApply wp_val_app => //.
             iSplitR; first by iIntros "!> [%Habs _]".
             iApply (wp_set_local with "[] [$Hf]") => //=.
        }
        { by iIntros "(%Habs & _)". }
        
      - iIntros (w) "[-> Hf]".
        iSimpl.

        remember {| f_locs := set_nth (value_of_uint (4 + N.of_nat (length s) * 4))
                                (f_locs f0) 2 (value_of_uint (4 + N.of_nat (length s) * 4)) ;
                   f_inst := f_inst f0 |} as f1.
        rewrite - Heqf1.
        rewrite separate2.
        iApply wp_seq.
        instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
        iSplitR; first by iIntros "[% _]".
        iSplitL "Hf".
      - rewrite separate1. iApply wp_val_app => //.
        iSplitR; first by iIntros "!> [% _]".
        subst f1; iApply (wp_get_local with "[] [$Hf]") => //=.
        rewrite - fmap_insert_set_nth; last lia.
        rewrite list_lookup_insert_ne => //.
      - iIntros (w) "[-> Hf]".
        iSimpl.
        rewrite separate3.
        iApply wp_seq.
        instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
        iSplitR; first by iIntros "[% _]".
        iSplitL "Hf".
      - iApply (wp_pointeradd NotStuck E _ v
          (upd_pointer_addr v (ptr_addr v + N.of_nat (length s) * 4 + 4))
          _ f1 with "Hf").
        { unfold pointer_arith. simpl.
          rewrite wasm_int_signed.
          2: { unfold two14 in Hlen.
               remember (length s) as n. rewrite -Heqn. lia. }
          have Hnonneg : (0 <=? Z.of_N (ptr_addr v) +
            Z.of_N (4 + N.of_nat (length s) * 4))%Z = true.
          { apply Z.leb_le. lia. }
          rewrite Hnonneg.
          unfold upd_pointer_addr. f_equal. f_equal. lia. }
        done.
      - iIntros (w) "[-> Hf]".
        iSimpl.
        rewrite separate2.
        iApply wp_seq.
        instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - rewrite separate1.
        iApply wp_val_app => //.
        iSplitR ; first by iIntros "!> [%Habs _]".
        subst f1 ; iApply (wp_get_local with "[] [$Hf]") => //.
        simpl.
        rewrite - fmap_insert_set_nth; last by lias.
        rewrite list_lookup_insert_ne => //.
      - iIntros (w) "[-> Hf]".
        iDestruct "Hstack" as (col)
          "(%Hcol' & %Hfree' & %Hlen' & Hwall & Hlive & Hbase & Hs & Htail)".
        iDestruct "Htail" as (bs) "[%Hbs Htail]".
        have Hspace : (4 <= N.of_nat (length bs))%N.
        { rewrite Hbs. unfold two16, two14 in *. lia. }
        do 4 (destruct bs as [|? bs]; first (simpl in Hspace; lia)).
        iDestruct (wcs_app _ _ _ [:: b; b0; b1; b2] bs with "Htail")
          as "[Hslot Htail]".
        iSimpl. rewrite (separate3 (AI_pointer _)).
        iApply (wp_seq _ E _
          (λ w, (⌜w = immV []⌝ ∗ wall col (ptr_addr v) two16 ∗
             points_to_i32 (ptr_addr v + N.of_nat (length s) * 4 + 4)
               col a ∗ ↪[frame] f1)%I)).
        iSplitR; first by iIntros "[%Htrap _]".
        iSplitL "Hslot Hwall Hf".
        { iDestruct (wcs_wblock with "Hslot") as "Hblock".
          iApply (wp_wand with "[-]").
          - fold_const. iApply (wp_colstore NotStuck E
              (λ w, (⌜w = immV []⌝ ∗ wall col (ptr_addr v) two16 ∗
                 points_to_i32 (ptr_addr v + N.of_nat (length s) * 4 + 4)
                   col a)%I)
              (upd_pointer_addr v (ptr_addr v + N.of_nat (length s) * 4 + 4))
              T_i32 col (ptr_addr v) two16
              (map (λ b, {| tb_value := b; tb_color := Some col;
                           tb_tag := Numeric |}) [:: b; b0; b1; b2])
              (VAL_int32 a) f1 with "[-]").
            + done.
            + exact Hcol'.
            + done.
            + by simpl; rewrite !eqxx.
            + done.
            + iSplitR "Hf Hwall Hblock".
              * iNext. iIntros "[Ha Hwall]". iFrame. done.
              * iFrame.
          - iIntros (w) "[[Hw [Hwall Ha]] Hf]". iFrame. }
      - iIntros (w) "(-> & Hwall & Ha & Hf)".
        iSimpl.
        rewrite (separate1 (AI_basic _)).
        iApply wp_seq.
        instantiate (1 := λ x, ( ⌜ x = immV _ ⌝ ∗ ↪[frame]f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - iApply (wp_get_local with "[] [$Hf]") => //.
        subst f1 => //.
        rewrite - fmap_insert_set_nth; last by lias.
        by rewrite list_lookup_insert_ne => //.
          
      - iIntros (w) "[-> Hf]".
        iSimpl.
        rewrite (separate2 (AI_pointer _)).
        iApply wp_seq.
        instantiate (1 := λ x, ( ⌜ x = immV _ ⌝
                                         ∗ ↪[frame] f1)%I).
        iSplitR ; first by iIntros "[%Habs _]".
        iSplitL "Hf".
      - rewrite (separate1 (AI_pointer _)).
        iApply wp_val_app => //.
        iSplitR ; first by iIntros "!> [%Habs _]".
        iApply (wp_get_local with "[] [$Hf]") => //.
        subst f1 => //.
        rewrite set_nth_read => //=.
                  
      - iIntros (w) "[-> Hf]".
        iSimpl.
        iApply wp_wand_r.
        iSplitL "Hf Hbase Hwall".
      - fold_const.
        iApply (wp_wand with "[-]").
        { iApply (stack_store_i32 (ptr_addr v) two16
            (Wasm_int.Int32.repr (Z.of_N (N.of_nat (length s) * 4)))
            (Wasm_int.Int32.repr (Z.of_N (4 + N.of_nat (length s) * 4)))
            f1 E Hcol' with "Hwall Hbase Hf"). }
        iIntros (w) "(-> & Hwall & Hbase & Hf)".
        instantiate (1 := λ w, (⌜w = immV []⌝ ∗ wall col (ptr_addr v) two16 ∗
          points_to_i32 (ptr_addr v) col
            (Wasm_int.Int32.repr (Z.of_N (4 + N.of_nat (length s) * 4))) ∗
          ↪[frame] f1)%I). iFrame. done.
      - iIntros (w) "(-> & Hwall & Hbase & Hf)".
        iApply "HΦ". iSplit; first done.
        iSplitR "Hf"; last by iExists f1; subst f1; iFrame.
        iExists col.
        iSplit; first done.
        iSplit; first done.
        iSplit; first (iPureIntro; rewrite cons_length; unfold two14 in *; lia).
        iFrame "Hwall Hlive".
        iSplitL "Hbase".
        { iApply (points_to_i32_eq with "Hbase") => //.
          f_equal. rewrite cons_length. lia. }
        iSplitL "Ha Hs".
        { rewrite big_sepL_cons.
          iSplitL "Ha".
          - iApply (points_to_i32_eq with "Ha") => //.
            rewrite cons_length. lia.
          - iApply (big_sepL_impl with "Hs").
            iIntros "!>" (k y Hk) "Hy".
            iApply (points_to_i32_eq with "Hy") => //.
            rewrite cons_length. lia. }
        iExists bs. iSplit.
        { iPureIntro. rewrite !cons_length in Hbs.
          rewrite cons_length. unfold two16, two14 in *. lia. }
        iApply (wcs_eq with "Htail") => //.
        rewrite cons_length; simpl length; lia.

    Qed.

      
  End specs.



End stack.    
