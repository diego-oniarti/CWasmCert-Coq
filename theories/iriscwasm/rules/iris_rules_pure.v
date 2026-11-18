From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From CWasm.iriscwasm.language Require Import iris_wp_def.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm Require Import datatypes operations opsem properties color_ptr.

(* Like iris_wp_def.only_one_reduction, but takes an explicit second reduction
   Hred2 (built by hand) instead of constructing it by repeat econstructor,
   which loops when econstructor picks the wrong reduce_simple rule. *)
Ltac only_one_reduction_with H Hred2 :=
  let Hstart := fresh "Hstart" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in
  eapply reduce_det in H
      as [H | [ [i0 Hstart] | [[i0 Hstart] | (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]] ;
  last (exact Hred2) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart; try rewrite first_instr_instr_const in Hstart) ; inversion Hstart.


(* basic instructions with simple(pure) reductions *)
Section iris_rules_pure.
Context `{HPB: PointerBytes}.
Context `{!wasmG Σ}.

Close Scope byte_scope.


(* numerics *)
Lemma wp_unop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v v' : value) (t: value_type) (op: unop) f0:
  app_unop op v = v' ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [v']) -∗
  WP [AI_const v; AI_basic (BI_unop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hunop) "Hf HΦ".
  iApply wp_lift_atomic_step. destruct v => //=. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [Eempty], [AI_const v'], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply rm_silent, r_simple. rewrite <- Hunop. apply rs_unop.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ ws' locs'] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame. by destruct (app_unop op v).
Qed.
 
Lemma wp_binop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v1 v2 v : value) (t: value_type) (op: binop) f0:
  app_binop op v1 v2 = Some v ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [v]) -∗
  WP [AI_const v1; AI_const v2; AI_basic (BI_binop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=. destruct v1, v2 => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_const v], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    by apply rs_binop_success.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame. destruct v => //.
Qed.
                                                                  

Lemma wp_binop_failure (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v1 v2 : value) (t: value_type) (op: binop) f0:
  app_binop op v1 v2 = None ->
  ▷ Φ trapV -∗
  ↪[frame] f0 -∗
  WP [AI_const v1; AI_const v2; AI_basic (BI_binop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=. destruct v1, v2 => //. 
  iIntros (σ ns κ κs nt) "Hσ".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    by apply rs_binop_failure.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.
    
Lemma wp_relop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v1 v2 : value) (b: bool) (t: value_type) (op: relop) f0:
  app_relop op v1 v2 = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
  WP [AI_const v1; AI_const v2; AI_basic (BI_relop t op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hrelop) "Hf HΦ".
  iApply wp_lift_atomic_step => //=. destruct v1, v2 => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_const (VAL_int32 (wasm_bool b))], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    subst.
    by apply rs_relop.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_testop_i32 (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v : i32) (b: bool) (op: testop) f0:
  app_testop_i (e:=i32t) op v = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
    WP [AI_const (VAL_int32 v); AI_basic (BI_testop T_i32 op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_const (VAL_int32 (wasm_bool b))], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    subst.
    by apply rs_testop_i32.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_testop_i64 (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v : i64) (b: bool) (op: testop) f0:
  app_testop_i (e:=i64t) op v = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [(VAL_int32 (wasm_bool b))]) -∗
    WP [AI_const (VAL_int64 v); AI_basic (BI_testop T_i64 op)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_const (VAL_int32 (wasm_bool b))], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    subst.
    by apply rs_testop_i64.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_cvtop_convert (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v v': value) (t1 t2: value_type) (sx: option sx) f0:
  cvt t2 sx v = Some v' ->
  types_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v']) -∗
    WP [AI_const v; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=. destruct v => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_const v'], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    
    by apply rs_convert_success.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame. destruct v' => //. 
Qed.

Lemma wp_cvtop_convert_failure (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v : value) (t1 t2: value_type) (sx: option sx) f0:
  cvt t2 sx v = None ->
  types_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (trapV) -∗
    WP [AI_const v; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htypes) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=. destruct v => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    
    by apply rs_convert_failure.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_cvtop_reinterpret (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) (v v': value) (t1 t2: value_type) f0:
  wasm_deserialise (bits v) t2 = v' ->
  types_agree t1 v ->
  t1 <> T_pointer ->
  t2 <> T_pointer ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v']) -∗
    WP [AI_const v; AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype Ht1 Ht2) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=. destruct v => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_const v'], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    subst.
    by apply rs_reinterpret.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame. destruct (wasm_deserialise _ _) => //. 
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma wp_unreachable (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) f0 :
  ↪[frame] f0 -∗
  ▷Φ (trapV) -∗
  WP [AI_basic BI_unreachable] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    
    by apply rs_unreachable.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_nop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) f0:
  ↪[frame] f0 -∗
  ▷Φ (immV []) -∗
    WP [AI_basic (BI_nop)] @ s; E {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    exists [Eempty], [], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple.
    
    by apply rs_nop.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_drop (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) v f0 :
  ↪[frame] f0 -∗
  ▷Φ (immV []) -∗
    WP [AI_const v ; AI_basic BI_drop] @ s; E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial. destruct v => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [Eempty], [], σ, [].
    destruct σ as [[ws  locs ] inst ].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply rm_silent, r_simple ; apply rs_drop.
  - destruct σ as [[ws  locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws'  locs' ] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_select_false (s: stuckness) (E :coPset) (Φ : iris.val -> iProp Σ) n v1 v2 f0 :
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v2]) -∗ WP [AI_const v1 ; AI_const v2 ;
                      AI_const (VAL_int32 n) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step. simpl ; trivial. destruct v1, v2 => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    exists [Eempty], [AI_const v2], σ, [].
    destruct σ as [[ws  locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple ; by apply rs_select_false.
  - destruct σ as [[ws  locs ] inst ].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws'  locs' ] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame. destruct v2 => //. 
Qed.

Lemma wp_select_true (s: stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) n v1 v2 f0 :
  n <> Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v1]) -∗ WP [AI_const v1 ; AI_const v2 ;
                      AI_const (VAL_int32 n) ; AI_basic (BI_select) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=. destruct v1, v2 => //. 
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    exists [Eempty], [AI_const v1], σ, [].
    destruct σ as [[ws  locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple ; by apply rs_select_true.
  - destruct σ as [[ ws  locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ ws'  locs' ] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame. destruct v1 => //.
Qed.



Lemma wp_pointeradd (s: stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) p p' c f0 :
  pointer_arith p (Wasm_int.Z_of_sint i32m c) = Some p' ->
  ↪[frame] f0 -∗
    ▷Φ (immV [VAL_pointer p']) -∗
    WP [AI_const (VAL_int32 c) ; 
        AI_const (VAL_pointer p) ; AI_basic (BI_pointeradd) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hp) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_const (VAL_pointer _)], σ, [].
    destruct σ as [[ws  locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple ; by eapply rs_pointeradd_success.
  - destruct σ as [[ ws  locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ ws'  locs' ] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.


Lemma wp_pointeradd_failure (s: stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) p c f0 :
  pointer_arith p (Wasm_int.Z_of_sint i32m c) = None ->
  ↪[frame] f0 -∗
    ▷Φ (trapV) -∗
    WP [AI_const (VAL_int32 c) ; 
        AI_const (VAL_pointer p) ; AI_basic (BI_pointeradd) ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hp) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_trap], σ, [].
    destruct σ as [[ws  locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple ; by eapply rs_pointeradd_failure.
  - destruct σ as [[ ws  locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ ws'  locs' ] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_pointersub (s : stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) p p' c f0 :
  pointer_arith p (- (Wasm_int.Z_of_sint i32m c))%Z = Some p' ->
  ↪[frame] f0 -∗ ▷Φ (immV [VAL_pointer p']) -∗
    WP [AI_const (VAL_int32 c); AI_const (VAL_pointer p); AI_basic BI_pointersub ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hp) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_const (VAL_pointer _)], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple; by eapply rs_pointersub_success.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_pointersub_failure (s : stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) p c f0 :
  pointer_arith p (- (Wasm_int.Z_of_sint i32m c))%Z = None ->
  ↪[frame] f0 -∗ ▷Φ (trapV) -∗
    WP [AI_const (VAL_int32 c); AI_const (VAL_pointer p); AI_basic BI_pointersub ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hp) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple; by eapply rs_pointersub_failure.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_pointerdiff (s : stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) p1 p2 d f0 :
  same_origin p1 p2 ->
  d = (Z.of_N p1.(ptr_addr) - Z.of_N p2.(ptr_addr))%Z ->
  ↪[frame] f0 -∗ ▷Φ (immV [VAL_int32 (Wasm_int.int_of_Z i32m d)]) -∗
    WP [AI_const (VAL_pointer p1); AI_const (VAL_pointer p2); AI_basic BI_pointerdiff ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hs Hd) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_const (VAL_int32 _)], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple; by eapply rs_pointerdiff_success.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_pointerdiff_failure (s : stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) p1 p2 f0 :
  ~ same_origin p1 p2 ->
  ↪[frame] f0 -∗ ▷Φ (trapV) -∗
    WP [AI_const (VAL_pointer p1); AI_const (VAL_pointer p2); AI_basic BI_pointerdiff ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hs) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple; by eapply rs_pointerdiff_failure.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_isnull_true s E Φ p f0:
  is_null p ->
  ↪[frame] f0 -∗ ▷Φ (immV [VAL_int32 (Wasm_int.Int32.repr 1)]) -∗
    WP [AI_const (VAL_pointer p); AI_basic BI_isnull ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hp) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_const (VAL_int32 _)], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple; by eapply rs_isnull_true.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_isnull_false s E Φ p f0:
  ~~ is_null p -> 
  ↪[frame] f0 -∗ ▷Φ (immV [VAL_int32 (Wasm_int.Int32.repr 0)]) -∗
    WP [AI_const (VAL_pointer p); AI_basic BI_isnull ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hp) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_const (VAL_int32 _)], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple; by eapply rs_isnull_false.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    prim_split κ HStep H.
    iris_wp_def.only_one_reduction H. iFrame.
Qed.

Lemma wp_isnull s E Φ p f0:
  ↪[frame] f0 -∗ ▷Φ (immV [VAL_int32 (Wasm_int.Int32.repr (if (is_null p) then 1 else 0))]) -∗
    WP [AI_const (VAL_pointer p); AI_basic BI_isnull ] @ s;
E {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_const (VAL_int32 _)], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=. repeat split => //.
    instantiate (1 := Wasm_int.Int32.repr (if (is_null p) then 1 else 0)). 
    destruct (is_null p) eqn:Hp.
    + apply rm_silent, r_simple, rs_isnull_true; by rewrite Hp.
    + apply rm_silent, r_simple, rs_isnull_false; by rewrite Hp.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    prim_split κ HStep H.
    destruct (is_null p) eqn:Hp.
    + iris_wp_def.only_one_reduction H. iFrame.
    + assert (Hred2 : reduce ws {| f_locs := locs; f_inst := inst |} [AI_pointer p; AI_basic BI_isnull] Eempty ws {| f_locs := locs; f_inst := inst |}
                      [AI_const (VAL_int32 (Wasm_int.Int32.repr 0))]).
      { apply rm_silent, r_simple, rs_isnull_false; by rewrite Hp. }
      only_one_reduction_with H Hred2. iFrame.
Qed. 

Lemma wp_demote (s : stuckness) (E : coPset) (Φ: iris.val -> iProp Σ) p p' f0 :
  ptr_addr p = ptr_addr p' ->
  ptr_col p = ptr_col p' ->
  ptr_freeable p' = false ->
  ↪[frame] f0 -∗
  ▷Φ (immV [VAL_pointer p']) -∗
  WP [AI_const (VAL_pointer p); AI_basic BI_demote] @ s;
E {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Ha Hc Hf) "Hf0 HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. destruct s => //=. unfold language.reducible, language.prim_step => /=.
    eexists [Eempty], [AI_const (VAL_pointer _)], σ, [].
    destruct σ as [[ws  locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply rm_silent, r_simple ; by eapply rs_demote.
  - destruct σ as [[ ws  locs ] inst].
    iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ ws'  locs' ] inst'].
    prim_split κ HStep H.
    assert (Hred2 : reduce ws {| f_locs := locs; f_inst := inst |} [AI_pointer p; AI_basic BI_demote] Eempty ws {| f_locs := locs; f_inst := inst |}
                    [AI_const (VAL_pointer p')]).
    { apply rm_silent, r_simple; by eapply rs_demote. }
    only_one_reduction_with H Hred2. iFrame.
Qed.


End iris_rules_pure.
