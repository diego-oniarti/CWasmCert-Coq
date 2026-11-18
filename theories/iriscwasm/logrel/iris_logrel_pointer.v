From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import ghost_map cancelable_invariants.

(** Supporting registration data and ghost-map lemmas.  The core pointer
    logical relation, its guarded fixed point, and proofs live in iris_logrel.v. *)

Record pointer_registration := PointerRegistration {
  preg_name : gname;
  preg_base : N;
  preg_size : N;
  preg_fraction : Qp
}.

Definition pointer_registry := gmap N pointer_registration.

Class pointer_logrelG (Σ : gFunctors) := PointerLogrelG {
  pointer_registryG :: ghost_mapG Σ N pointer_registration;
  pointer_registry_name : gname
}.

Definition pointer_inv_namespace (c : N) : namespace := nroot .@ "cptr" .@ c.

Section pointer_registration_helpers.
  Context `{!pointer_logrelG Σ}.

  Definition pointer_registered (c : N) (r : pointer_registration) : iProp Σ :=
    ghost_map_elem pointer_registry_name c DfracDiscarded r.

  Definition pointer_registry_auth (R : pointer_registry) : iProp Σ :=
    ghost_map_auth pointer_registry_name 1 R.

  Lemma pointer_registered_lookup (c : N) (r : pointer_registration)
      (R : pointer_registry) :
    pointer_registry_auth R -∗ pointer_registered c r -∗ ⌜ R !! c = Some r ⌝.
  Proof.
    apply ghost_map_lookup.
  Qed.

  Lemma pointer_registered_agree (c : N)
      (r1 r2 : pointer_registration) :
    pointer_registered c r1 -∗ pointer_registered c r2 -∗ ⌜ r1 = r2 ⌝.
  Proof.
    apply ghost_map_elem_agree.
  Qed.

End pointer_registration_helpers.
