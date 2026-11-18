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
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- SELECT -------------------------------------- *)

  Lemma typing_select C t : ⊢ semantic_typing C (to_e_list [BI_select]) (Tf [t; t; T_i32] [t]).
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
    destruct ws as [|w1 ws];[done|destruct ws as [|w2 ws];[done|destruct ws as [|w3 ws];[done|destruct ws;[|done]]]].
    iSimpl in "Hv".
    iDestruct "Hv" as "[Hv1 [Hv2 [Hv3 _]]]".
    iDestruct "Hv3" as (z) "->".
    iSimpl.
    iApply (wp_wand _ _ _ (λne vs, interp_val [t] vs ∗ ↪[frame] f )%I with "[Hf]").
    { destruct (Wasm_int.Int32.eq_eqP z (Wasm_int.int_zero i32m)).
      { iApply (wp_select_false with "Hf");auto.
        iRight. iSimpl. iExists _. iSplit;eauto. iNext.
        iSplit;done. }
      { iApply (wp_select_true with "Hf");auto.
        iRight. iSimpl. iExists _. iSplit;eauto. iNext.
        iSplit;done. }
    }
	    iIntros (v) "[$ Hf]".
	    iExists _;iFrame.
	    Unshelve.   
	  Qed.
    
End fundamental.
