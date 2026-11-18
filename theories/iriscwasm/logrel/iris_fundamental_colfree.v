From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

From CWasm.iriscwasm.language.iris Require Import iris iris_locations.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm.iriscwasm.language Require Import iris_atomicity iris_wp_def.
From CWasm Require Import stdpp_aux datatypes operations properties opsem typing.
From CWasm.iriscwasm.rules Require Import iris_rules. 
From CWasm.iriscwasm.logrel Require Export iris_logrel iris_fundamental_helpers.
Import uPred.
  
Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ, HPB: PointerBytes, cancelg : cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

 
    
  (* ----------------------------------------- COLFREE ---------------------------------------- *)


  Lemma typing_colfree C : 
    ⊢ semantic_typing C (to_e_list [BI_colfree]) (Tf [T_pointer] []).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|wh ws];[done|destruct ws; last done].  
    iSimpl in "Hv". iDestruct "Hv" as "(Hv & _)".
     
    iDestruct "Hv" as (p ->) "#Hp".
    rewrite pointer_interp_unfold /pointer_interp_pre.
    iDestruct "Hp" as "[%Hnull | Hptr]".
    { iApply (wp_wand with "[Hf]").
      { iApply (wp_colfree_fail_null with "[$Hf]").
        { by rewrite /is_null Hnull. }
        by instantiate (1 := λ x, ⌜x = trapV⌝%I). }
      iIntros (v) "[-> Hf]".
      iSplitR; first by do 2 iLeft.
      iExists _. iFrame. }

    iDestruct "Hptr" as (c r Hcol) "(#Hregistered & #Hinv & %Hfraction)".
    destruct (ptr_freeable p) eqn:Hfree.
    2:{ iApply (wp_wand with "[Hf]").
        { iApply (wp_colfree_fail_freeable with "[$Hf]"); first done.
          by instantiate (1 := λ x, ⌜x = trapV⌝%I). }
        iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _. iFrame. }

    iDestruct (interp_allocator_lookup_status c r with
      "Hregistered Hall") as "[#Hinv' Hstatus]".
    iDestruct "Hstatus" as "[(Hlive & Htok & Hclose) | (#Hdead & Hall)]".
    2:{ iApply (wp_wand with "[Hf Hdead]").
        { iApply (wp_colfree_fail_dead with "[$Hf $Hdead]"); first exact Hcol.
          instantiate (1 := λ v, ⌜v = trapV⌝%I).
          iNext. iIntros "_". done. }
        iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists _. iFrame. }

    have Hfull : preg_fraction r = 1%Qp := Hfraction (Logic.eq_refl true).
    iEval (rewrite Hfull) in "Hlive Htok".
    iApply fupd_wp.
    iMod (cinv_cancel with "Hinv Htok") as "Hbody"; first solve_ndisj.
    iDestruct "Hbody" as (tbs) "(>%Htbslen & >%Hcolors & >Hwall & >Hblock & Hslots)".
    iModIntro.
    iAssert (▷ (dead_color c -∗
      (⌜immV [] = immV []⌝ ∗ interp_allocator)))%I
      with "[Hclose]" as "Hpost".
    { iNext. iIntros "#Hdead".
      iSplitR "Hclose"; first done. by iApply "Hclose". }
    iApply (wp_wand with "[Hf Hwall Hlive Hblock Hpost]").
    { instantiate (1 := λ v,
        ((⌜v = immV []⌝ ∗ interp_allocator) ∗ ↪[frame] f)%I).
      iApply wp_colfree; [exact Hcol | exact Hfree | exact Htbslen | exact Hcolors |].
      iFrame. }
    iIntros (v) "[[-> Hall] Hf]".
    iSplitR "Hf Hfv Hall".
    { iLeft. iRight. iExists _. iSplit => //. }
    iExists _. iFrame.
  Qed. 

End fundamental.
