From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From CWasm.iriscwasm.examples.colstack Require Export colstack_map.
From CWasm.iriscwasm.logrel Require Import iris_fundamental.
From CWasm.iriscwasm.rules Require Import proofmode iris_rules.
From CWasm.iriscwasm.language Require Import iris_wp_def.
From CWasm.iriscwasm.helpers.prelude Require Import iris_reduce_properties.
From CWasm.iriscwasm.helpers.lfill_prelude Require Import lfill_extension.
From CWasm Require Import opsem stdpp_aux common.

Close Scope byte_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section stack.

 Context `{!wasmG Σ, logrel_na_invs Σ, HPB: PointerBytes, cancelg: cancelG Σ, !cinvG Σ}. 

Section specs.

  Set Bullet Behavior "Strict Subproofs".
  
Lemma spec_map_loop_body_continue_trap f (s: list i32) v E hj j fn (sv: i32) j0 a cl
  (Φ : i32 -> iPropI Σ) (Ψ: i32 -> i32 -> iPropI Σ) (γ1 : namespace) :
  ↑γ1 ⊆ E ->
  ⊢ {{{
        ⌜ f.(f_locs) !! 0 = Some (value_of_pointer v) ⌝ ∗
        ⌜ f.(f_locs) !! 1 = Some (VAL_int32 fn) ⌝  ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_pointer hj) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_uint (N.of_nat (length s) * 4)) ⌝ ∗
        ⌜ pointer_arith v ((length s) * 4 - 4 * Z.of_N j - 4) = Some hj ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        ⌜ (0 <= j < N.of_nat (length s))%N ⌝ ∗
        ⌜ s !! (N.to_nat j) = Some sv ⌝ ∗
        isStack v s ∗
        Φ sv ∗
            ⌜ f.(f_inst).(inst_types) !! 3 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] a) ∗
            (match a with
             | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
                          ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
                                           (∀ (u : i32) (fc : frame),
                                               {{{ Φ u ∗
                                                     ⌜ f_inst f = f_inst fc ⌝ ∗
                                                                    ↪[frame] fc ∗ interp_allocator ∗
                                                                    na_own logrel_nais ⊤
                                               }}}
                                                 [ AI_basic (BI_const (NVAL_int32 u)) ;
                                                   AI_invoke a ] @ E
                                                 {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                                                          ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc ∗ (interp_allocator)}}})
             | None => True
             end) ∗ 
        na_own logrel_nais ⊤ ∗ ↪[frame] f ∗ interp_allocator }}}
    to_e_list map_loop_body @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ ⌜ w = brV (VH_base 0 [] []) ⌝ ∗
           (∃ (sv': i32), isStack v (<[N.to_nat j := sv']> s) ∗ Ψ sv sv')) ∗
             na_own logrel_nais ⊤ ∗  ∃ hj', ⌜ pointer_arith v ((length s) * 4 - 4 * Z.of_N j)%Z = Some hj' ⌝ ∗
            ↪[frame]
            {| f_locs := <[ 2 := value_of_pointer hj' ]> f.(f_locs);
               f_inst := f.(f_inst)
            |} ∗ (interp_allocator) 
    }}}.
Proof.
  intros Hsub1.
  iIntros "!>" (Ξ) "(%Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hhj & %Hlocs & %Hjbound & %Hslookup & Hs & HΦ & %Htypes & %Htab & #Htab & Hcl & Hown & Hf & Hall) HΞ" => /=.

  iDestruct (stack_pure with "Hs") as (c) "(%Hcol & %Hfree & %Hlens)".
  have Hlookup_bound := lookup_lt_Some _ _ _ Hslookup.
  have Hdelta_nonneg :
      (0 <= length s * 4 - 4 * Z.of_N j - 4)%Z by lia.
  have Htop_bound : (length s * 4 < 4294967296)%Z.
  { unfold two14 in Hlens. lia. }
  have Hdelta_lt :
      (length s * 4 - 4 * Z.of_N j - 4 < length s * 4)%Z by lia.
  have Horig := pointer_arith_same_origin Hhj.
  have Haddr_diff := pointer_arith_diff Hhj.

  remember (upd_pointer_addr hj (ptr_addr hj + 4)) as hj' eqn:Heqhj'.
  have Hstep : pointer_arith hj 4 = Some hj'.
  { subst hj'. unfold pointer_arith. simpl.
    have Hnonneg : (0 <=? Z.of_N (ptr_addr hj) + 4)%Z = true.
    { apply Z.leb_le. lia. }
    rewrite Hnonneg. unfold upd_pointer_addr. f_equal. f_equal. lia. }
  have Hadd :
      pointer_arith v (length s * 4 - 4 * Z.of_N j) = Some hj'.
  { replace (length s * 4 - 4 * Z.of_N j)%Z with
      ((length s * 4 - 4 * Z.of_N j - 4) + 4)%Z by lia.
    rewrite -(pointer_arith_compose (p := v) (p' := hj)
      (d1 := length s * 4 - 4 * Z.of_N j - 4) 4 Hhj).
    exact Hstep. }

  
  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [value_of_pointer hj; value_of_pointer v]⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  - by iIntros "(%Habs & _)".
  - rewrite (separate1 (AI_pointer _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] Hf") => //.
  - iIntros (w) "[-> Hf]". iSimpl.
    rewrite separate3.
    iApply wp_seq.
    instantiate (1 := λ w,
      (⌜w = immV [VAL_int32 (Wasm_int.int_of_Z i32m
        (length s * 4 - 4 * Z.of_N j - 4))]⌝ ∗ ↪[frame] f)%I).
    iSplitR; last iSplitL "Hf".
    + by iIntros "(%Habs & _)".
    + iApply (wp_pointerdiff NotStuck E _ hj v
        (length s * 4 - 4 * Z.of_N j - 4) f with "Hf") => //.
    + iIntros (w) "[-> Hf]". iSimpl.
    rewrite separate2.
    iApply wp_seq.
    instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ ↪[frame] f )%I).
    iSplitR; last iSplitL "Hf".
    * by iIntros "[% _]".
    * rewrite (separate1 (AI_basic _)).
      iApply wp_val_app => //.
      iSplit; first by iIntros "!> (%Habs & _)".
      by iApply wp_get_local => //.
    * iIntros (w) "(-> & Hf)" => /=.
      rewrite separate3.
      iApply wp_seq.
      iSplitR; last iSplitL "Hf".
      2: { fold_const; iApply (wp_relop with "Hf") => //=.
           rewrite Wasm_int.Int32.eq_false => /=.
           - by instantiate (1 := λ w, ⌜w = immV _⌝%I).
           - move=> Heq.
             apply Wasm_int.Int32.repr_inv in Heq.
             + lia.
             + rewrite u32_modulus. split.
               * have Hminus : (-1 < 0)%Z by done.
                 exact (Z.lt_le_trans _ _ _ Hminus Hdelta_nonneg).
               * exact (Z.lt_trans _ _ _ Hdelta_lt Htop_bound).
             + rewrite u32_modulus.
               have Htop_eq :
                 Z.of_N (N.of_nat (length s) * 4) = (length s * 4)%Z by lia.
               rewrite Htop_eq. split; first lia. exact Htop_bound.
      }
      { by iIntros "(%Habs & _)". }
      iIntros (w) "(-> & Hf)" => /=.
      rewrite separate2.
      iApply wp_seq.
      iSplitR; last iSplitL "Hf".
      2: { iApply (wp_br_if_false with "Hf") => //=.
           by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
      }
      { by iIntros "(%Habs & _)". }
      iIntros (w) "(-> & Hf)" => /=.
      rewrite (separate2 (AI_basic _)).
      iApply wp_seq.
      iSplitR; last iSplitL "Hf".
      2: { rewrite separate1. iApply wp_val_app => //.
           iSplitR; last first. iApply wp_wand_r. iSplitL.
           iApply wp_get_local => //.
           by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
           iIntros (w) "[-> Hf]" => /=.
           instantiate (1 := λ x, (⌜ x = immV _ ⌝ ∗ ↪[frame] _)%I).
           iFrame. done.
           by iIntros "!> [% _]".
      }
  { by iIntros "(%Habs & _)". }
  
  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [value_of_pointer hj']⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_pointeradd NotStuck E _ hj hj'
          (Wasm_int.Int32.repr (Z.of_N 4)) f with "Hf").
       - simpl. rewrite wasm_int_signed; last lia. exact Hstep.
       - done. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "[-> Hf]" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  2: { fold_const; iApply (wp_tee_local with "Hf").
       iIntros "!> Hf".
       rewrite (separate1 (AI_const _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_set_local with "[] [$Hf]"); first lia.
       done.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  2: { rewrite (separate1 (AI_pointer _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_get_local with "[] [$Hf]").
       - rewrite - fmap_insert_set_nth => /=; last lia.
         by rewrite list_lookup_insert; last lia.
       - done.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ isStack v s ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf Hs".
  2: { rewrite (separate1 (AI_pointer _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_wand with "[Hf Hs]").
       - iApply (stack_load_j with "[] [] [$Hs] [$Hf]") => //. 
       - iIntros (w) "(-> & Hs & Hf)" => /=.
         iSplit => //.
         by iFrame.
  }
  { by iIntros "(%Habs & _)". }
  
  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜ w = immV _ ⌝ ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  2: { rewrite (separate2 (AI_pointer _)).
       iApply wp_val_app => //.
       iSplit; first by iIntros "!> (%Habs & _)" => /=.
       iApply (wp_get_local with "[] [$Hf]").
       { rewrite - fmap_insert_set_nth => /=; last lia.
         by rewrite list_lookup_insert_ne; last lia.
       }
       done.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate4.
  iApply (wp_wand with "[-HΞ] HΞ").
  set (f' := {| f_locs := <[2 := value_of_pointer hj']> (f_locs f);
               f_inst := f_inst f |}).
  iApply wp_wasm_empty_ctx.  
  iApply wp_seq_can_trap_ctx.
  instantiate (1 := λ f, (⌜ f = f'⌝ ∗ na_own logrel_nais ⊤ ∗ (interp_allocator))%I).
  instantiate (2 := λ w, (∃ v0, ⌜ w = immV _ ⌝ ∗ Ψ sv v0 ∗ isStack v s)%I).  
  iSplitR; last iSplitR.
  { by iIntros "H"; iDestruct "H" as (v0) "(%Habs & _)". }
  { iIntros (f0) "(Hf & -> & Hown & Hall)". subst f'. iFrame. iSplitR. iLeft. done.
    iExists _ ; iSplit; first done. iFrame. 
  }
  iFrame "Hf". iSplitL.
  { rewrite (separate1 (AI_pointer _)).
    iIntros "Hf".
    iApply wp_val_can_trap_app => //. iFrame "Hf".
    iSplit; first by iIntros "!> H" => /=; iDestruct "H" as (v0) "(%Habs & _)".
    iIntros "Hf".
    iApply fupd_wp.
    iMod (na_inv_acc with "Htab Hown") as "(>Htab' & Hown & Hcls')";[solve_ndisj..|].
    destruct a.
    - iDestruct "Hcl" as (γ2) "(%Hsub & #Hcl & %Hclt & #Hspec)".
      destruct Hsub as [Hsub2 Hdiff].
      iMod (na_inv_acc with "Hcl Hown") as "(>Hcl' & Hown & Hcls)";[auto|solve_ndisj|].      
      iApply (wp_call_indirect_success_ctx with "[$Htab'] [$Hcl'] [$Hf] [HΦ Hs Hcls Hown Hcls' Hall]") => /=.
      { by rewrite Hclt. }
      { done. }
      2: { iPureIntro.
           instantiate (1 := (LH_base [AI_basic (BI_const (NVAL_int32 sv))] [])).
           instantiate (1 := 0).
           unfold lfilled, lfill.
           simpl.
           by apply/eqP.
      }
      { iIntros "!> (Htab' & Hcl' & Hf)".
        iApply wp_base_pull.
        iApply wp_wasm_empty_ctx.
        iApply fupd_wp.
        iMod ("Hcls" with "[$]") as "Hown".
        iMod ("Hcls'" with "[$]") as "Hown".
        iModIntro.
        iApply ("Hspec" with "[$HΦ $Hown $Hf $Hall]"); first done.
        iIntros (w) "(Hret & Hown & Hf & Hall)".
        iSplitR "Htab Hf Hown Hall";[|iExists _;iFrame;subst f';simpl;auto].
        iDestruct "Hret" as "[-> | Hret]";auto.
        iDestruct "Hret" as (v0) "(-> & HΨ)".
        iRight. iExists v0.
        iSplit => //. iFrame.
        rewrite - fmap_insert_set_nth;auto.
        lia.
      }
    - take_drop_app_rewrite 1.
      iApply (wp_val_can_trap_app);auto.
      iFrame "Hf".
      iSplitR.
      { simpl. iModIntro. iModIntro. iIntros "HH";iDestruct "HH" as (v0 Hcontr) "_";done. }
      iModIntro. iIntros "Hf".
      iApply wp_fupd.
      iApply (wp_wand _ _ _ (λ v, (⌜v = trapV⌝ ∗ _) ∗ _)%I with "[Hf Htab']").
      iApply (wp_call_indirect_failure_noindex with "Htab' Hf");auto.
      iIntros (v0) "[[-> Htab'] Hf]".
      iMod ("Hcls'" with "[$]") as "Hown". iModIntro.
      iSplitR "Hf Hown Hall";[|iExists _; iFrame;subst f';rewrite - fmap_insert_set_nth;auto;lia].
      iLeft. auto.
  }

  iIntros (w f0) "(H & Hf & -> & Hown & Hall)".
  iDestruct "H" as (v0) "(-> & HΨ & Hs)" => /=.
  deconstruct_ctx.
  iApply (wp_wand _ _ _
            (λ v1, (⌜v1 = brV (VH_base 0 [] [])⌝ ∗ (∃ sv' : Wasm_int.Int32.T, isStack v (<[N.to_nat j:=sv']> s) ∗ Ψ sv sv')) ∗ _)%I
           with "[-]").
  2: { iIntros (v') "[? HH]". iSplitR "HH"; [|iExact "HH"]. iRight. iFrame. }
  rewrite separate3.  
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { iApply (stack_store_j with "Hs Hf"); done. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  { iApply wp_value; last iFrame.
    - by instantiate (1 := brV (VH_base 0 [] [])). 
    - by instantiate (1 := λ w, (⌜ w = brV _ ⌝ ∗ ↪[frame] _)%I); iFrame. 
  }
  
  iIntros (w) "(-> & Hf)" => /=.
  iFrame. iSplitR "Hf".
  iSplit => //.
  iExists _. iFrame. iExists _ ; iSplit => //.
Qed.

Lemma spec_map_loop_j_trap f (s: list i32) v E j hj fn j0 a cl
  (Φ : i32 -> iPropI Σ) (Ψ: i32 -> i32 -> iPropI Σ) (s': list i32) γ1 :
  ↑γ1 ⊆ E ->
  ⊢ ( 
        ⌜ f.(f_locs) !! 0 = Some (value_of_pointer v) ⌝ ∗
        ⌜ f.(f_locs) !! 1 = Some (VAL_int32 fn) ⌝  ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_pointer hj) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_uint (N.of_nat (length s) * 4)) ⌝ ∗
        ⌜ pointer_arith v (length s * 4 - 4 * Z.of_N j) = Some hj ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        ⌜ (0 <= j <= N.of_nat (length s))%N ⌝ ∗
        ⌜ (j + N.of_nat (length s') = N.of_nat (length s))%N ⌝ ∗
        isStack v (take (N.to_nat j) s ++ s') ∗
        stackAll (take (N.to_nat j) s) Φ ∗
        stackAll2 (drop (N.to_nat j) s) s' Ψ ∗
            ⌜ f.(f_inst).(inst_types) !! 3 = Some (Tf [T_i32] [T_i32]) ⌝ ∗
            ⌜ f.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m fn) ] a) ∗
            (match a with
             | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
                          ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗ 
                                           (∀ (u : i32) (fc : frame),
                                               {{{ Φ u ∗
                                                     ⌜ f_inst f = f_inst fc ⌝ ∗
                                                                    ↪[frame] fc ∗ interp_allocator ∗
                                                                    na_own logrel_nais ⊤
                                               }}}
                                                 [ AI_basic (BI_const (NVAL_int32 u)) ;
                                                   AI_invoke a ] @ E
                                                 {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                                                          ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc ∗ (interp_allocator) }}})
             | None => True
             end)  ∗   
            na_own logrel_nais ⊤ ∗ ↪[frame] f ∗ interp_allocator ) -∗
  WP (to_e_list map_loop_body) @ E CTX 2;
  push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
    [AI_basic
       (BI_loop (Tf [] [])
          map_loop_body)] [] []
    {{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                                        (∃ s', isStack v s' ∗ stackAll2 s s' Ψ)))
            ∗ (∃ f1, ↪[frame] f1 ∗ na_own logrel_nais ⊤ ∗ ⌜ f_inst f = f_inst f1 ⌝ )
            ∗ (interp_allocator)
    }}.
Proof.
  remember (N.to_nat j) as k.
  iRevert (Heqk).
  iRevert (j hj s' s f).
  iInduction k as [|k] "IHk".
  
  - iIntros (j hj s' s f Habs Hsub1).
    iIntros "(%Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hhj & %Hlocs & %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & #Htab & Hcl & Hown & Hf & Hall)" => /=.

    iDestruct (stack_pure with "Hs") as "(%Hoff & %Hbound & %Hvalid & %Hlens)".
    
    assert (j=0)%N as ->; first lia.
    iApply wp_ctx_bind => //.
    iApply (spec_map_loop_body_terminate with "[Hs Hf]").
    + iFrame.
      repeat iSplit => //.
      iPureIntro.
      replace (Z.of_N (N.of_nat (length s) * 4))%Z with
        (length s * 4)%Z by lia.
      replace (length s * 4 - 4 * Z.of_N 0)%Z with
        (length s * 4)%Z in Hhj by lia.
      exact Hhj.
    + iIntros (w) "(%Hes & Hs & Hf)".
      destruct Hes as [es ->] => /=.
      rewrite (separate1 (AI_basic _)).
      replace ([AI_basic (BI_br 1)] ++ es) with ([] ++ [AI_basic (BI_br 1)] ++ es) => //.
      iApply wp_base_push => //.
      replace ([AI_basic (BI_br 1)]) with ([] ++ [AI_basic (BI_br 1)]) => //.
      iApply (wp_br_ctx with "Hf") => //.
      iIntros "!> Hf" => /=.
      iApply wp_value; first by instantiate (1 := immV []).
      iSplitL "HΨ Hs".
      * iRight. iSplit => //.
        iExists s'. rewrite drop_0. iFrame.
      * iSplitL "Hf Hown".
        -- iExists f. iFrame. done.
        -- iExact "Hall".
  - iIntros (j hj s' s f Habs Hsub1).
    iIntros "(%Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hhj & %Hlocs & %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & #Htab & #Hcl & Hown & Hf)" => /=.
    
    iDestruct (stack_pure with "Hs") as "(%Hoff & %Hbound & %Hvalid & %Hlens)".

    assert (j = N.of_nat (k+1)) as ->; first lia.

    assert (exists sv, s !! k = Some sv) as Hsvlookup.
    { destruct (s !! k) eqn:Hol => //; first by eexists.
      apply lookup_ge_None in Hol.
      lia.
    }
    destruct Hsvlookup as [sv Hsvlookup].

    assert (take (S k) s = take k s ++ [sv]) as HStake; first by erewrite take_S_r.
    rewrite HStake.

    iDestruct (stackAll_app with "HΦ") as "(HΦ & HsvΦ)".
    simpl.
    iDestruct "HsvΦ" as "(HsvΦ & _)".

    rewrite - HStake.

    iApply wp_ctx_bind => //.
    iApply (spec_map_loop_body_continue_trap with "[Hs HsvΦ Hf Hown Hcl]");[apply Hsub1|..].
    + iFrame "Htab Hcl". iFrame.
      repeat rewrite app_length take_length.
      replace (S k `min` length s) with (S k); last lia.
      replace (S k + length s') with (length s); last lia.
      instantiate (4 := hj). instantiate (4 := N.of_nat k).
      repeat iSplit => //.
      * iPureIntro.
        replace (length s * 4 - 4 * Z.of_N (N.of_nat k) - 4)%Z
          with (length s * 4 - 4 * Z.of_N (N.of_nat (k + 1)))%Z.
        done. lia.
      * iPureIntro. lia. 
      * iPureIntro. lia. 
      * iPureIntro.
        rewrite lookup_app.
        rewrite Nat2N.id.
        replace (take _ _ !! k) with (Some sv) => //.
        rewrite lookup_take; last lia.
        done.
    + iIntros (w) "(Hres & Hown & Hf)" => /=.
      iDestruct "Hf" as (hj') "(%Hhj' & Hf & Hall)".
      iDestruct "Hres" as "[-> | Hres]".
      * iApply (wp_wand_ctx _ _ _ (λ w, ⌜w = trapV⌝ ∗ _)%I with "[Hf]"). iClear "IHk".
        take_drop_app_rewrite_twice 0 0. iApply (wp_trap_ctx with "[$]");auto.
        iIntros (v0) "[-> Hf]".
        iSplitR "Hf Hown Hall"; first by iLeft.
        iSplitL "Hf Hown".
        -- iExists _. iFrame. done.
        -- iExact "Hall".
      * iDestruct "Hres" as "(-> & HsvΨ)".
        iDestruct "HsvΨ" as (sv') "(Hs & HΨ')".
        replace ([AI_basic (BI_br 0)]) with ([] ++ [AI_basic (BI_br 0)]) => //.
        iApply (wp_br_ctx_nested with "Hf") => //; first lia.
        -- by instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []) => //=. 
        -- iIntros "!> Hf".
           rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
           iApply (wp_loop_ctx with "Hf") => //.
           iIntros "!> Hf".
           replace (cat [] (to_e_list map_loop_body)) with ([] ++ to_e_list map_loop_body ++ []); last done.
           iApply wp_label_push => //.
           simpl.
           remember ({| f_locs := <[2:=value_of_pointer hj' ]> (f_locs f);
                       f_inst := f_inst f |}) as f'.
           replace (f_inst f) with (f_inst f'); last by rewrite Heqf'.
           iApply "IHk"; auto; first by iPureIntro; instantiate (1 := N.of_nat k); rewrite Nat2N.id.
           rewrite Heqf' => /=.
           iCombine "HΨ HΨ'" as "HΨcomb".
           iFrame.
           instantiate (1 := (sv' :: s')).
           rewrite app_length take_length in Hhj'.
           assert (S k `min` length s = S k) as Hmin; first lia.
           rewrite Hmin in Hhj'.
           rewrite - Nat2N.inj_add in Hlen.
           apply Nat2N.inj in Hlen.
           assert (S k + length s' = k + 1 + length s')%nat; first lia.
           rewrite H0 Hlen in Hhj'.
           repeat iSplit => //.
           ++ by rewrite list_lookup_insert_ne. 
           ++ by rewrite list_lookup_insert_ne. 
           ++ rewrite list_lookup_insert; last lia.
              iPureIntro.
              do 2 f_equal.
           ++ by rewrite list_lookup_insert_ne.
           ++ rewrite insert_length. iPureIntro; lia.
           ++ iPureIntro. lia. 
           ++ iPureIntro. clear H.
              assert (k+1 <= length s)%Z as H; first lias. clear - H.
              remember (length s) as x.
              rewrite - Heqx.
              lia.
           ++ iPureIntro.
              simpl.
              clear - Hlen.
              remember (length s) as x; rewrite - Heqx.
              remember (length s') as x'; rewrite - Heqx'.
              lia.
           ++ iSplitL "Hs".
              ** replace (<[_ := _]> _) with (take k s ++ sv' :: s'); first done.
                 erewrite take_S_r => //.
                 rewrite insert_app_l; last first.
                 --- rewrite app_length take_length => /=.
                     remember (length s) as x.
                     rewrite - Heqx.
                     lia.
                 --- rewrite insert_app_r_alt; last first.
                     +++ rewrite take_length => /=.
                         remember (length s) as x.
                         rewrite - Heqx.
                         lia.
                     +++ rewrite take_length.
                         remember (length s) as x.
                         rewrite - Heqx Nat2N.id.
                         replace (k `min` x) with k; last lia.
                         replace (k - k) with 0; last lia.
                         simpl.
                         rewrite - app_assoc.
                         done.
              ** iSplitL "HΨcomb".
                 --- assert ((drop k s) = (sv :: (drop (S k) s))) as Hdeq; first by erewrite drop_S.
                     rewrite Hdeq => /=.
                     by iDestruct "HΨcomb" as "(? & ?)"; iFrame.
                 --- by repeat iSplit => //.
Qed.
  
Lemma spec_stack_map_trap (f0 : frame) (f : i32) (v: pointer) (s : seq.seq i32) E
      j0 a cl γ1
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ↑γ1 ⊆ E ->
  ⊢ {{{ 
            ⌜ f0.(f_locs) !! 0 = Some (value_of_pointer v) ⌝ ∗
            ⌜ f0.(f_locs) !! 1 = Some (VAL_int32 f) ⌝  ∗
            ⌜ length f0.(f_locs) >= 4 ⌝ ∗
            isStack v s ∗
            stackAll s Φ ∗
            ⌜ f0.(f_inst).(inst_types) !! 3 = Some (Tf [T_i32] [T_i32]) ⌝ ∗

            ⌜ f0.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
            na_inv logrel_nais γ1 ((N.of_nat j0) ↦[wt][ N.of_nat (Wasm_int.nat_of_uint i32m f) ] a) ∗
            match a with
            | Some a => ∃ γ2, ⌜↑γ2 ⊆ E ∧ @up_close _ coPset _ γ2 ⊆ ⊤ ∖ ↑γ1⌝ ∗ na_inv logrel_nais γ2 ((N.of_nat a) ↦[wf] cl) ∗
             ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗  
            (∀ (u : i32) (fc : frame),
                {{{ Φ u ∗
                      ⌜ f_inst f0 = f_inst fc ⌝ ∗
                       ↪[frame] fc ∗ interp_allocator ∗
                       na_own logrel_nais ⊤
                  }}}
                  [ AI_basic (BI_const (NVAL_int32 u)) ;
                    AI_invoke a ] @ E
                  {{{ w, (⌜ w = trapV ⌝ ∨ ((∃ v, ⌜ w = immV [VAL_int32 v] ⌝ ∗ Ψ u v)))
                           ∗ na_own logrel_nais ⊤ ∗ ↪[frame] fc ∗ (interp_allocator)}}})
            | None => True
            end ∗
            na_own logrel_nais ⊤ ∗ ↪[frame] f0 ∗ interp_allocator }}}
    to_e_list stack_map @ E
    {{{ w, (⌜ w = trapV ⌝ ∨ (⌜ w = immV [] ⌝ ∗
                                        (∃ s', isStack v s' ∗ stackAll2 s s' Ψ)))
             ∗ (∃ f1, ↪[frame] f1 ∗ na_own logrel_nais ⊤ ∗ ⌜ f_inst f0 = f_inst f1 ⌝ )
             ∗ (interp_allocator)
    }}}.
Proof.
  intros Hsub1.
  iIntros "!>" (Ξ) "(%Hlocs0 & %Hlocs1 & %Hlocs & Hs & HΦ & %Htypes & %Htab & #Htab & #Hcl & Hinv & Hf & Hall) HΞ" => /=.
  
  rewrite separate5.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { iApply (spec_map_initialise with "[$Hf $Hs]") => //.
       iIntros (w) "(-> & Hs & Hf)".
       instantiate (1 := λ w, (⌜w = immV []⌝ ∗ _)%I).
       iSplit => //.
       iCombine "Hs Hf" as "H".
       by iApply "H".
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
  iApply (wp_block with "Hf") => //.
  iIntros "!> Hf".
  iSimpl.
  
  iApply wp_wasm_empty_ctx.
  rewrite - (cat0s [AI_basic (BI_loop _ _)]) - (cats0 [AI_basic (BI_loop _ _)]).
  
  iApply wp_label_push ; first done.
  rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite - (cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite - (cats0 [AI_basic _;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_]). 
  iApply wp_label_push ; first done.
  iApply (wp_wand_ctx with "[HΦ Htab Hs Hf Hinv Hall]").
  - iApply spec_map_loop_j_trap;[apply Hsub1|].
    iFrame "∗ #".
    repeat iSplit => /=.
    + rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite Hlocs0.
    + rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite Hlocs1.
    + rewrite list_lookup_insert; last by rewrite insert_length; lia.
      done. 
    + rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert; last lia.
      done.
    + iPureIntro. instantiate (1 := N.of_nat (length s)).
      rewrite nat_N_Z.
      rewrite Z.mul_comm.
      rewrite Z.sub_diag.
      rewrite /pointer_arith Z.add_0_r.
      have Hnonneg : (0 <=? Z.of_N (ptr_addr v))%Z = true.
      { apply Z.leb_le. lia. }
      rewrite Hnonneg N2Z.id. by destruct v.
    + by repeat rewrite insert_length. 
    + iPureIntro. lia. 
    + done. 
    + instantiate (1 := []) => /=.
      iPureIntro. lia. 
    + rewrite Nat2N.id.
      rewrite firstn_all cats0.
      iFrame.
      rewrite drop_all.
      repeat iSplit => //.
  - iFrame.
Qed.


End specs.


End stack.    
      
