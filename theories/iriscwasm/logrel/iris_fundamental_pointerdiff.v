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


  Context `{!wasmG Σ, !logrel_na_invs Σ, HPB: PointerBytes, cancelg: cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* -------------------------------------- POINTERDIFF ----------------------------------- *)



  Lemma typing_pointerdiff C : ⊢ semantic_typing C (to_e_list [BI_pointerdiff]) (Tf [T_pointer; T_pointer] [T_i32]).
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
    destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[done|destruct ws;[|done]]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 [Hv2 _]]".
    iDestruct "Hv1" as (p1) "(-> & #Hp1)".
    iDestruct "Hv2" as (p2) "(-> & #Hp2)".
    iSimpl.
    destruct (same_origin_b p1 p2) eqn:Hsameb.
    - have Hsame : same_origin p1 p2.
      { unfold same_origin, same_origin_b in *. by move/eqP: Hsameb. }
      iApply (wp_wand _ _ _ (λne vs, interp_val [T_i32] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_pointerdiff _ _ _ p1 p2
          (Z.of_N (ptr_addr p1) - Z.of_N (ptr_addr p2))%Z with "Hf") => //.
        iNext. iSimpl. iRight. iExists _; iSplit; first done. iSimpl. iSplit; last done.
        iExists _. done.
      + iIntros (v) "[$ Hf]".
        iExists _;iFrame.
    - have Hdifferent : ~ same_origin p1 p2.
      { unfold same_origin, same_origin_b in *.
        move=> Heq. by rewrite Heq eq_refl in Hsameb. }
      iApply (wp_wand _ _ _ (λne vs, interp_val [T_i32] vs ∗ ↪[frame] f )%I with "[Hf]").
	      + iApply (wp_pointerdiff_failure with "Hf") => //.
	        iNext. iSimpl. iLeft. done. 
	      + iIntros (v) "[$ Hf]".
	        iExists _;iFrame.
	    Unshelve.   
	  Qed. 
    
End fundamental.
