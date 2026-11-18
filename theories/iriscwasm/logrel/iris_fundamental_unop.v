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

  (* ----------------------------------------- UNOP ---------------------------------------- *)

  Lemma unop_type_agree_interp t op w :
    unop_type_agree t op ->
    ⊢ interp_value t w -∗
      interp_value (Σ:=Σ) t (app_unop op w).
  Proof.
    iIntros (Hunop) "Hv".
    inversion Hunop;subst.
    all: iDestruct "Hv" as (w') "->"; eauto.
  Qed.    
  
  Lemma typing_unop C t op : unop_type_agree t op ->
                             ⊢ semantic_typing C (to_e_list [BI_unop t op]) (Tf [t] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Hunop i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]".
    iIntros (f vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    { iDestruct "Hv" as (ws ->) "Hv".
      iDestruct (big_sepL2_length with "Hv") as %Hlen.
      destruct ws as [|w ws];[done|destruct ws;[|done]].
      iSimpl in "Hv".
      iDestruct "Hv" as "[Hv _]".
      iSimpl.
      iApply (wp_wand _ _ _ (λ v, ⌜v = immV [app_unop op w]⌝ ∗ ↪[frame] f)%I with "[Hf]").
      { iApply (wp_unop with "Hf");eauto. }
      iIntros (w0) "[-> Hf]".
      iSplitR;[|iExists _;iFrame].
      iLeft. iRight.
      iExists [app_unop op w]. iSplit;auto.
      iSimpl. iSplit;auto.
      iApply unop_type_agree_interp;auto.
    }
    Unshelve.   
  Qed.

End fundamental.
