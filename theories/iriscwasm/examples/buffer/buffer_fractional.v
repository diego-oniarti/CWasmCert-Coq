From iris.proofmode Require Import tactics.

From CWasm Require Import color_ptr datatypes.
From CWasm.iriscwasm.language Require Import iris_wp_def.
From CWasm.iriscwasm.logrel Require Import iris_logrel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Buffer_fractional.
  Context `{!wasmG Σ, !logrel_na_invs Σ, cancelg : cancelG Σ,
      !cinvG Σ, HPB : PointerBytes}.

  (** The logical step used at the adversary boundary in the buffer example.
      The original pointer [p] stays private.  The allocator world receives
      one half of both the live-colour evidence and the cancellation token;
      the caller keeps the other halves, and only the demoted copy is put in
      the value relation. *)
  Lemma buffer_publish_demoted (p : pointer) (c base size : N) :
    ptr_col p = Some c ->
    live_color c -∗
    ▷ pointer_allocation_body pointer_interp c base size -∗
    interp_allocator ={ ⊤ }=∗
      ∃ γ : gname,
        let r := PointerRegistration γ base size (1/2)%Qp in
        interp_value_pointer
          (VAL_pointer (new_pointer (ptr_addr p) (ptr_col p) false)) ∗
        pointer_registered c r ∗
        pointer_allocation_inv pointer_interp c r ∗
        interp_allocator ∗ live_color_frac c (1/2)%Qp ∗
        cinv_own γ (1/2)%Qp.
  Proof.
    iIntros (Hcolor) "Hlive Hbody Hall".
    iMod (interp_allocator_publish_half c base size with
      "Hlive Hbody Hall")
      as (γ) "(#Hregistered & #Hinv & Hall & Hlive_private & Hprivate)".
    iModIntro. iExists γ.
    iFrame "Hregistered Hinv Hall Hlive_private Hprivate".
    rewrite /interp_value_pointer.
    iExists (new_pointer (ptr_addr p) (ptr_col p) false).
    iSplit; first done.
    iApply (pointer_interp_nonfreeable _ c
      (PointerRegistration γ base size (1/2)%Qp) with
      "Hregistered Hinv").
    - exact Hcolor.
    - done.
  Qed.

End Buffer_fractional.
