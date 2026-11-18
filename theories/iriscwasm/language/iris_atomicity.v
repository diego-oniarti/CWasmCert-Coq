From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm.iriscwasm.language Require Export iris iris_locations.
From CWasm Require Import datatypes operations properties opsem.

Section atomicity.
  Context `{HPB : PointerBytes}.

Local Definition reducible := @reducible wasm_lang.

Local Definition expr := iris.expr.
Local Definition val := iris.val.
Local Definition to_val := iris.to_val.


(* The following atomicity definition will be useful for opening invariants *)
Definition is_atomic (e : expr) : Prop :=
  match e with
  | [::AI_basic (BI_const (NVAL_int32 _)); AI_basic (BI_load _ _ _ _)] => True
  | [::AI_pointer _; AI_basic (BI_colload _)] => True
  | [::AI_basic (BI_const (NVAL_int32 _)); AI_pointer _; AI_basic (BI_store _ _ _ _)] => True
  | [::AI_basic (BI_const (NVAL_int32 _)); AI_basic (BI_const _); AI_basic (BI_store _ _ _ _)] => True
  | [::AI_pointer _; AI_pointer _; AI_basic (BI_colstore _)] => True
  | [::AI_pointer _; AI_basic (BI_const _); AI_basic (BI_colstore _)] => True
  | [::AI_pointer _; AI_basic BI_colfree] => True
  | [::AI_basic (BI_const (NVAL_int32 _)); AI_basic BI_colalloc] => True
  | [::AI_basic (BI_const _); AI_basic (BI_set_global _)] => True
  | [::AI_pointer _; AI_basic (BI_set_global _)] => True
  | [::AI_basic (BI_get_global _)] => True
  | [::AI_trap] => True
  | _ => False
  end.

Ltac destruct_match_goal :=
  let x := fresh "x" in 
  match goal with
                | _ : _ |- (match ?x with | _ => _ end -> _) => case: x => x //=
  end.
Lemma is_atomic_eq (e : expr) :
  is_atomic e ->
  (∃ k x1 x2 x3 x4, e = [::AI_const (VAL_int32 k); AI_basic (BI_load x1 x2 x3 x4)]) ∨
      (∃ k x1, e = [::AI_const (VAL_pointer k); AI_basic (BI_colload x1)]) ∨
    (∃ k v x1 x2 x3 x4, e = [::AI_const (VAL_int32 k); AI_const v; AI_basic (BI_store x1 x2 x3 x4)]) ∨
    (∃ k v x1, e = [::AI_const (VAL_pointer k); AI_const v; AI_basic (BI_colstore x1)]) ∨
    (∃ k, e = [::AI_const (VAL_pointer k); AI_basic BI_colfree]) ∨
            (∃ k, e = [::AI_const (VAL_int32 k); AI_basic BI_colalloc]) \/
  (∃ v g, e = [::AI_const v; AI_basic (BI_set_global g)]) ∨
  (∃ g, e = [::AI_basic (BI_get_global g)]) ∨
  (e = [::AI_trap]).
Proof.
  intros He.
  do 2 (destruct e;try done).
  { destruct a;try done.
    destruct b;try done. right. right. right. right. right. eauto.
    destruct n; try done.
    right. right. right. right. right. right. right. by right. }
  do 1 (destruct e;try done).
  { revert He. cbn. repeat destruct_match_goal.

    all: try by (move => *; right; right; right; right; right; right; left; eexists (VAL_numeric ( _)),_).
    move => *. left. repeat eexists. move => *. right; right; right; right; right; left. repeat eexists.
    move => *. right. right. right. right. right. right. left. eexists (VAL_pointer _), _. done.
    move => *. right; left. repeat eexists. right; right; right; right; left. by eexists.
  } 
  { destruct e.
    2: { exfalso. cbn in He. revert He.
         repeat destruct_match_goal. }
    revert He. cbn. repeat destruct_match_goal.
    move => *. right; right; left. eexists _,(VAL_numeric _); repeat eexists.
    do 2 right; left. by eexists _, (VAL_pointer _); repeat eexists. 
    right; right; right; left.
    eexists _, (VAL_numeric _); repeat eexists. do 3 right; left.
    by eexists _, (VAL_pointer _); repeat eexists. 
  }
Qed.

Lemma atomic_no_hole_load s0 f es me s' f' es' k lh k0 x0 x1 x2 x3 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_const (VAL_int32 k0); AI_basic (BI_load x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.  
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_load_false;eauto. }
Qed.

Lemma atomic_no_hole_colload s0 f es me s' f' es' k lh k0 x0:
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_const (VAL_pointer k0); AI_basic (BI_colload x0)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.  
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_colload_false;eauto. }
Qed.
    
Lemma atomic_no_hole_store s0 f es me s' f' es' k lh k0 v x0 x1 x2 x3 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_const (VAL_int32 k0); AI_const v; AI_basic (BI_store x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0; try destruct v => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_store_false_2;eauto.  instantiate (9 := VAL_numeric n). done. }
    { inversion H;subst. exfalso.
    eapply reduce_store_false_2;eauto.  instantiate (9 := VAL_pointer p). done. }

  { inversion H;subst. exfalso.
    eapply reduce_store_false;eauto. }
    { inversion H;subst. exfalso.
    eapply reduce_store_false;eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. } 
    { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
Qed.


Lemma atomic_no_hole_colstore s0 f es me s' f' es' k lh k0 v x0 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_const (VAL_pointer k0); AI_const v; AI_basic (BI_colstore x0 )] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0; try destruct v => //=;simplify_eq).
  1-4: inversion H;subst; exfalso;
  eapply reduce_val_false;eauto; eauto. 
  { inversion H;subst. exfalso.
    eapply reduce_colstore_false_2;eauto. instantiate (6 := VAL_numeric n) => //. }
    { inversion H;subst. exfalso.
      eapply reduce_colstore_false_2;eauto. instantiate (6 := VAL_pointer p) => //. }
  1-2: inversion H;subst; exfalso;
    eapply reduce_colstore_false;eauto. 
  1-2: inversion H;subst; exfalso;
    eapply reduce_val_false;eauto; eauto. 
Qed.

Lemma atomic_no_hole_colfree s0 f es me s' f' es' k lh k0 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_const (VAL_pointer k0);  AI_basic (BI_colfree)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0; try destruct v => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_colfree_false;eauto. }
Qed.

Lemma atomic_no_hole_colalloc s0 f es me s' f' es' k lh k0 :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_const (VAL_int32 k0); AI_basic BI_colalloc] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_colalloc_false;eauto. }
Qed.

Lemma atomic_no_hole_trap s0 f es me s' f' es' k lh :
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_trap] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
Qed.

Lemma reduce_set_global_false s0 f me s' f' es es' g :
  es = [AI_basic (BI_set_global g)] ->
  reduce s0 f es me s' f' es' -> False.
Proof.
  intros Heq Hred.
  apply Logic.eq_sym in Heq.
  no_reduce Heq Hred.
Qed.

Lemma atomic_no_hole_set_global s0 f es me s' f' es' k lh v g :
  reduce s0 f es me s' f' es' ->
  lfilled k lh es [::AI_const v; AI_basic (BI_set_global g)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0 ; try destruct v => //=;simplify_eq).
  { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
    { inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. }
  { inversion H;subst. exfalso.
    eapply reduce_set_global_false;eauto. }
    { inversion H;subst. exfalso.
    eapply reduce_set_global_false;eauto. }
Qed.

Lemma atomic_no_hole_get_global s0 f es me s' f' es' k lh g:
  reduce s0 f es me s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_get_global g)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  destruct k;inversion Hfill;subst;[split;auto|repeat destruct vs => //=].
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
Qed.
  

Global Instance is_atomic_correct s e : is_atomic e → @Atomic wasm_lang s e.
Proof.
  intros Ha; apply strongly_atomic_atomic.
  move => σ e' K σ' e'' /= Hstep.
  unfold iris.prim_step in Hstep.
  destruct σ as [[[hs ws] locs] inst].
  destruct σ' as [[[hs' ws'] locs'] inst'].
  destruct K => //. destruct K => //.
  destruct Hstep as [Hstep ->].
  induction Hstep. 
  destruct H.
  all: apply is_atomic_eq in Ha as Heq. 
  all: destruct Heq as [(?&?&?&?&?&?)|[(?&?&?)|[(?&?&?&?&?&?&?)|[(?&?&?&?)|[(?&?)|[(?&?)|[(?&?&?)|[(?&?)|?]]]]]]]];simplify_eq; eauto.
  all: try by (do 2 (destruct vcs;try (by destruct x0); try done)).
  all: try by (do 4 (destruct vcs;try (by destruct x0); try done)).
  { inversion H;subst;eauto.
    1,2: do 3 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 3 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). }
    { inversion H;subst;eauto.
      1,2: do 4 (destruct vs;try done). }
  { inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). }
  { inversion H;simpl;eauto; subst; exfalso.
    - do 3 (destruct vs;inversion H0;try done).
    - do 3 (destruct vs;inversion H0;try done). }
   { inversion H;simpl;eauto; subst; exfalso.
    - do 3 (destruct vs;inversion H0;try done).
    - do 3 (destruct vs;inversion H0;try done). }
    { inversion H;simpl;eauto; subst; exfalso.
    - do 3 (destruct vs;inversion H0;try done).
    - do 3 (destruct vs;inversion H0;try done). }
    { destruct v => //. }
    { destruct (wasm_deserialise _ _) => //. }
    { destruct (wasm_deserialise _ _) => //. }
        { destruct (wasm_deserialise _ _) => //. } 
  { eapply atomic_no_hole_load in Hstep as HH;eauto. destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { eapply atomic_no_hole_colload in Hstep as HH;eauto. destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_store as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_colstore as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
   { eapply atomic_no_hole_colfree in Hstep as HH;eauto. destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
    { eapply atomic_no_hole_colalloc in Hstep as HH;eauto. destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_set_global as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
  { edestruct atomic_no_hole_get_global as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }  
  { edestruct atomic_no_hole_trap as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. }
Qed.

End atomicity. 

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.



Global Hint Extern 0 (Atomic _ _) => solve_atomic : core.
Global Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.


