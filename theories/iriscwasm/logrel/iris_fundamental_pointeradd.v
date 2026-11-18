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

  (* --------------------------------------- POINTERADD ------------------------------------- *)



  Lemma typing_pointeradd C : ⊢ semantic_typing C (to_e_list [BI_pointeradd]) (Tf [T_i32; T_pointer] [T_pointer]).
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
    iDestruct "Hv1" as (z) "->".
    iDestruct "Hv2" as (p) "(-> & #Hv)".
    iSimpl.
    destruct (pointer_arith p (Wasm_int.Z_of_sint i32m z)) as [p'|] eqn:Hadd.
    - (* Sucessful adding *)
      iApply (wp_wand _ _ _ (λne vs, interp_val [T_pointer] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_pointeradd with "Hf") => //.
        iNext. iSimpl. iRight. iExists _; iSplit; first done. iSimpl. iSplit; last done.
        iExists p'.
        iSplit; first done.
        by iApply (pointer_interp_arith p p' (Wasm_int.Z_of_sint i32m z) Hadd).
      + iIntros (v) "[$ Hf]".
        iExists _;iFrame.
    - (* Failed slicing *)
       iApply (wp_wand _ _ _ (λne vs, interp_val [T_pointer] vs ∗ ↪[frame] f )%I with "[Hf]").
      + iApply (wp_pointeradd_failure with "Hf") => //.
        iNext. iSimpl. iLeft. done. 
	      + iIntros (v) "[$ Hf]".
	        iExists _;iFrame.
	    Unshelve.   
	  Qed. 
    
End fundamental.
