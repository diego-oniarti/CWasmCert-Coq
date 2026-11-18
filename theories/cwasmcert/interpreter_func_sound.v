(** soundness of the Wasm interpreter **)
(* adapted from (C) J. Pichon, M. Bodin, Rao Xiaojia *)

From CWasm Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
(* From StrongInduction Require Import StrongInduction Inductions. *)
Require Import Lia BinNat.
Require Import Lia Arith.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import PeanoNat Even NAxioms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From CWasm Require Import operations properties opsem properties stdpp_aux type_preservation type_progress.
From CWasm Require Import interpreter_func.


Global Hint Constructors reduce_simple : core.
Global Hint Constructors reduce : core.


Local Definition RS_crash := interpreter_func.RS_crash.
Local Definition RS_break := interpreter_func.RS_break.
Local Definition RS_return := interpreter_func.RS_return.
Local Definition RS_normal := interpreter_func.RS_normal.


Section interpreter_func_sound.
  Set Bullet Behavior "Strict Subproofs".
  Context `{HPB : PointerBytes}.

(** The lemmas [r_eliml] and [r_elimr] are the fundamental framing lemmas.
  They enable to focus on parts of the stack, ignoring the context. **)



(** [r_eliml_empty] and [r_elimr_empty] are useful instantiations on empty stacks. **)

Lemma r_eliml_empty: forall s f es me s' f' lconst,
    const_list lconst ->
    reduce s f es me s' f' [::] ->
    reduce s f (lconst ++ es) me s' f' lconst.
Proof.
  move => s f es me s' f' lconst HConst H.
  assert (reduce s f (lconst++es) me s' f' (lconst++[::])); first by apply: r_eliml.
  by rewrite cats0 in H0.
Qed.

Lemma r_elimr_empty: forall s f es me s' f' les,
    reduce s f es me s' f' [::] ->
    reduce s f (es ++ les) me s' f' les.
Proof.
  move => s f es me s' f' les H.
  assert (reduce s f (es++les) me s' f' ([::] ++les)); first by apply: r_elimr.
  by rewrite cat0s in H0.
Qed.

Lemma run_step_fuel_not_zero : forall tt,
  run_step_fuel tt <> 0.
Proof.
  move=> [[st vs] es].
  rewrite/run_step_fuel.
   
  destruct st.
  by lias.
Qed.

Local Lemma ves_projection: forall vs e es vs' e' es',
  const_list vs ->
  const_list vs' ->
  ~ is_const e ->
  ~ is_const e' ->
  vs ++ e :: es = vs' ++ e' :: es' ->
  e = e'.
Proof.
  move => vs. induction vs => //=.
  - move => e es vs' e' es' _ HConstList HNConst HNConst'.
    destruct vs' => //=.
    + move => H. by inversion H.
    + simpl in HConstList. move => H. inversion H. subst.
      move/andP in HConstList. destruct HConstList as [Ha _].
      rewrite Ha in HNConst. exfalso. by apply HNConst.
  - move => e es vs' e' es' HConstList HConstList' HNConst HNConst'.
    destruct vs' => //=.
    + move => H. inversion H. subst.
      move/andP in HConstList. destruct HConstList as [He' _].
      exfalso. by apply HNConst'.
    + simpl in HConstList'. move => H. inversion H. subst.
      move/andP in HConstList. move/andP in HConstList'.
      destruct HConstList as [Ha Hvs]. destruct HConstList' as [Ha' Hvs'].
      eapply IHvs => //=.
      * by apply Hvs'.
      * by apply H2.
Qed.

Lemma lfilled0: forall es,
  lfilledInd 0 (LH_base [::] [::]) es es.
Proof.
  move => es.
  assert (lfilledInd 0 (LH_base [::] [::]) es ([::]++es++[::])) as H; first by apply LfilledBase.
  simpl in H. by rewrite cats0 in H.
Qed.

Lemma lfilled0_frame_l: forall vs es es' LI vs',
  lfilledInd 0 (LH_base vs es') es LI ->
  const_list vs' ->
  lfilledInd 0 (LH_base (vs' ++ vs) es') es (vs' ++ LI).
Proof.
  move => vs es es' LI vs' HLF HConst. inversion HLF; subst; clear HLF.
  assert (HList: vs' ++ vs ++ es ++ es' = (vs' ++ vs) ++ es ++ es'); first by repeat rewrite catA.
  rewrite HList.
  apply LfilledBase. by rewrite const_list_concat.
Qed.

Lemma lfilled0_frame_l_empty: forall es es' LI vs',
  lfilledInd 0 (LH_base [::] es') es LI ->
  const_list vs' ->
  lfilledInd 0 (LH_base vs' es') es (vs' ++ LI).
Proof.
  move => es es' LI vs' HLF HConst. inversion HLF; subst; clear HLF.
  repeat rewrite catA.
  rewrite cats0.
  rewrite -catA.
  by apply LfilledBase.
Qed.

Lemma lfilled0_frame_r: forall vs es es' LI es'',
  lfilledInd 0 (LH_base vs es') es LI ->
  lfilledInd 0 (LH_base vs (es' ++ es'')) es (LI ++ es'').
Proof.
  move => vs es es' LI es'' HLF. inversion HLF; subst; clear HLF.
  repeat rewrite -catA.
  by apply LfilledBase.
Qed.

Lemma lfilled0_frame_r_empty: forall vs es LI es'',
  lfilledInd 0 (LH_base vs [::]) es LI ->
  lfilledInd 0 (LH_base vs es'') es (LI ++ es'').
Proof.
  move => vs es LI es'' HLF. inversion HLF; subst; clear HLF.
  repeat rewrite -catA.
  by apply LfilledBase.
Qed.

Lemma lfilled0_take_drop: forall vs es n es',
  const_list vs ->
  n <= size vs ->
  lfilledInd 0 (LH_base (take n vs) es') (drop n vs ++ es) (vs ++ es ++ es').
Proof.
  move => vs es n es' HConst HSize.
  replace (vs++es++es') with (take n vs ++ (drop n vs ++ es) ++ es').
  apply LfilledBase. by apply const_list_take.
  { repeat rewrite catA. by rewrite cat_take_drop. }
Qed.

(** The following tactics are meant to help the proof of [run_step_soundness] below. **)

(** Simplify an hypothesis, possibly rewriting it everywhere. **)
Ltac simplify_hypothesis Hb :=
  repeat rewrite length_is_size in Hb;
  repeat match type of Hb with
  | is_true (es_is_trap _) => move/es_is_trapP: Hb => Hb
  | is_true (const_list (_ :: _)) => rewrite const_list_cons in Hb
  | ?b = true => fold (is_true b) in Hb
  | (_ == _) = false => move/eqP in Hb
  | context C [size (rev _)] => rewrite size_rev in Hb
  | context C [take _ (rev _)] => rewrite take_rev in Hb
  | context C [rev (rev _)] => rewrite revK in Hb
  | context C [true && _] => rewrite Bool.andb_true_l in Hb
  | context C [_ && true] => rewrite Bool.andb_true_r in Hb
  | context C [false || _] => rewrite Bool.orb_false_l in Hb
  | context C [_ || false] => rewrite Bool.orb_false_r in Hb
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | ?x = ?x => clear Hb
  | _ = _ => rewrite Hb in *
  end.

(** Apply [simplify_hypothesis] to all hypotheses. **)
Ltac simplify_goal :=
  repeat match goal with H: _ |- _ => progress simplify_hypothesis H end.

(** A common pattern in the proof: using an hypothesis on the form [rev l = l'] to rewrite [l]. **)
Ltac subst_rev_const_list :=
 repeat lazymatch goal with
 | HRevConst: rev ?lconst = ?h :: ?t |- _ =>
   apply rev_move in HRevConst; rewrite HRevConst; rewrite -cat1s; rewrite rev_cat;
   rewrite -v_to_e_cat; rewrite -catA
 end.

(** Simplify the lists in the goal. **)
Ltac simplify_lists :=
  (** Common rewriting rules. **)
  repeat first [
      rewrite drop_rev
    | rewrite take_rev
    | rewrite revK
    | rewrite length_is_size
    | rewrite size_take
    | rewrite size_drop
    | rewrite size_rev
    | rewrite v_to_e_size
    | rewrite rev_cat
    | rewrite rev_cons -cats1
    | rewrite -v_to_e_cat
    | rewrite -v_to_e_rev
    | rewrite -v_to_e_take
    | rewrite -v_to_e_drop];
  (** Putting all the lists into a normal form, as concatenations of as many things.
    Because [cat1s] conflicts with [cats0], replacing any occurence of [[X]] to
    [[X] ++ [::]], it has to be done separately.
    Rewrite with the associated [math goal with] is avoid to deal with existential
    vairables. **)
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end;
  repeat lazymatch goal with
  | |- context C [[::] ++ _] => rewrite cat0s
  | |- context C [_ ++ [::]] => rewrite cats0
  | |- context C [rcons _ _] => rewrite -cats1
  | |- context C [(_ ++ _) ++ _] => rewrite -catA
  | |- context C [rev [::]] => rewrite rev0
  | |- context C [v_to_e_list [::]] => rewrite v_to_e_list0
  | |- context C [v_to_e_list [:: _]] => rewrite v_to_e_list1
  end;
  try subst_rev_const_list.

(** Explode a tuple into all its components. **)
Ltac explode_value v :=
  lazymatch type of v with
  | (_ * _)%type =>
    let v1 := fresh "v1" in
    let v2 := fresh "v2" in
    destruct v as [v1 v2];
    explode_value v1;
    explode_value v2
  | _ => idtac
  end.

(** Try to find which variable to pattern match on, destruct it,
  then simplify the destructing equality. **)
Ltac explode_and_simplify :=
  repeat lazymatch goal with
  | |- ?T = _ -> _ =>
      lazymatch T with
      | PointerBytes => idtac
    | context C [split_n ?l ?n] => rewrite (split_n_is_take_drop l n)
    | context C [vs_to_es ?l] => rewrite/vs_to_es
(*    | context C [host_application_impl _ _ _ _ _ _] =>
      destruct host_application_impl *)
    | context C [match ?b with true => ?v1 | false => ?v2 end] =>
      let Hb := fresh "if_expr" in
      destruct b eqn:Hb;
      simplify_hypothesis Hb;
      try by [|apply: Hb]
    | context C [match rev ?lconst with
                 | _ :: _ => _
                 | _ => _
                 end] =>
      let HRevConst := fresh "HRevConst" in
      destruct (rev lconst) eqn:HRevConst;
      simplify_hypothesis HRevConst;
      try by [|apply: HRevConst]
    | context C [match ?v with
                 | VAL_numeric _ => _
                 | _ => _
                 end] =>
      let Hb := fresh "Ev" in
      destruct v eqn:Hb;
      simplify_hypothesis Hb;
      try by []
    | context C [match ?v with
                 | Some _ => _
                 | _ => _
                 end] =>
      let Hv := fresh "option_expr" in
      let v' := fresh "v" in
      destruct v as [v'|] eqn:Hv; [ explode_value v' |];
      simplify_hypothesis Hv;
      try by [|apply: Hv]
    | context C [match ?cl with
                 | FC_func_native _ _ _ _ => _
                 | FC_func_host _ _ => _
                 end] =>
      let Hcl := fresh "Hcl" in
      destruct cl eqn:Hcl;
      simplify_hypothesis Hcl;
      try by []
    | context C [match ?tf with
                 | Tf _ _ => _
                 end] =>
      let Hcl := fresh "Htf" in
      destruct tf eqn:Htf;
      simplify_hypothesis Htf;
      try by []
    | context C [match ?v with
                 | T_i32 => _
                 | T_i64 => _
                 | T_f32 => _
                 | T_f64 => _
                 | T_pointer => _
                 end] =>
      let Hv := fresh "Ev" in
      destruct v eqn:Hv;
      simplify_hypothesis Hv;
      try by []
    | context C [match ?v with
                 | CVO_convert => _
                 | CVO_reinterpret => _
                 end] =>
      let Hv := fresh "Ecvtop" in
      destruct v eqn:Hv;
      simplify_hypothesis Hv;
      try by []
    | context C [match ?v with
                 | Tf _ _ => _
                 end] =>
      let vs1 := fresh "vs" in
      let vs2 := fresh "vs" in
      let Hv := fresh "Eft" in
      destruct v as [vs1 vs2] eqn:Hv;
      simplify_hypothesis Hv;
      try by []
    | context C [expect ?X ?f ?err] =>
       let HExpect := fresh "HExpect" in
       destruct X eqn:HExpect;
       simplify_hypothesis HExpect;
       simpl;
       try by [|apply: HExpect]
    | context C [match ?l with
                 | _ :: _ => _
                 | _ => _
                 end] =>
      destruct l;
      try by []
    end
  end;
  simplify_lists.

(** If the goal is on the form [c1 = c2 -> property] where [c1] and [c2] are two configurations,
  then invert it. **)
Ltac pattern_match := let H := fresh "H" in intro H ; inversion H.

(** Eliminate the stack frame, by applying [r_elimr] and [r_eliml] according to some heuristics. **)
Ltac stack_frame :=
  repeat lazymatch goal with
  | |- reduce _ _ _ (_ :: ?l) _ _ _ _ =>
    rewrite -cat1s
  | |- reduce _ _ _ (?l1 ++ ?l2 :: ?l3) _ _ _ ((?l5 ++ ?l4) ++ ?l3) =>
    rewrite -cat1s; rewrite catA;
    apply: r_elimr; try apply: r_eliml; try apply: v_to_e_is_const_list
  | |- reduce _ _ _ (?l1 ++ ?l2 :: ?l3) _ _ _ (?l5 ++ ?l3) =>
    rewrite -cat1s; rewrite catA;
    apply: r_elimr; try apply: r_eliml_empty; try apply: v_to_e_is_const_list
  | |- reduce _ _ _ (operations.v_to_e_list ?l1 ++ _) _ _ _ (operations.v_to_e_list (take ?n ?l1) ++ _) =>
    rewrite (v_to_e_take_drop_split l1 n); rewrite -catA;
    apply: r_eliml; try apply: v_to_e_is_const_list
  end.

(** Try to solve a goal of the form [const_list _]. **)
Ltac solve_const_list :=
  repeat rewrite const_list_concat;
  repeat rewrite const_list_cons;
  by [| apply: v_to_e_is_const_list ].

(** Try to solve a goal of the form [l1 = l2] where [l1] and [l2] are two lists. **)
Ltac show_list_equality :=
  simplify_lists; simplify_goal;
  by [| repeat f_equal
      | repeat rewrite catA; repeat f_equal
      | repeat rewrite -catA; repeat f_equal
      | eauto
      | erewrite cats0; eauto
      | erewrite cat0s; eauto
      | repeat (repeat rewrite catA; f_equal; repeat rewrite -catA; f_equal)
      | repeat (repeat rewrite -catA; f_equal; repeat rewrite catA; f_equal) ].

(** Given a left and a right frame, rewrite the goal to move these frames out. **)
Ltac frame_out l r :=
  lazymatch goal with
  | |- reduce _ _ _ ?st1 _ _ _ ?st2 =>
    let sta := fresh "st1" in
    evar (sta : seq administrative_instruction);
    let stb := fresh "st2" in
    evar (stb : seq administrative_instruction);
    let Est1 := fresh "E_before" in
    assert (Est1: st1 = (l ++ sta) ++ r); [
        rewrite/sta {sta stb}; try show_list_equality
      | let Est2 := fresh "E_after" in
        assert (Est2: st2 = (l ++ stb) ++ r); [
            rewrite/stb {Est1 sta stb}; try show_list_equality
          | rewrite Est1 Est2;
            apply r_elimr with (les := r);
            apply r_eliml with (lconst := l); first try solve_const_list;
            rewrite /sta /stb {Est1 Est2 sta stb};
            try by repeat constructor ] ]
  end.

(** Same as [frame_out], by the frames are inferred (syntactically). **)
Ltac auto_frame :=
  simplify_lists;
  let empty := constr:([::] : list administrative_instruction) in
  let left _ :=
    repeat rewrite -catA;
    repeat lazymatch goal with
    | |- reduce _ _ _ (?l ++ _) _ _ _ (?l ++ _) =>
      frame_out l empty
    | |- reduce _ _ _ (?l ++ _) _ _ _ ?l =>
      frame_out l empty
    | |- reduce _ _ _ ?l _ _ _ (?l ++ _) =>
      frame_out l empty
    end in
  let right _ :=
    repeat rewrite catA;
    repeat lazymatch goal with
    | |- reduce _ _ _ (_ ++ ?r) _ _ _ (_ ++ ?r) =>
      frame_out empty r
    | |- reduce _ _ _ (_ ++ ?r) _ _ _ ?r =>
      frame_out empty r
    | |- reduce _ _ _ ?r _ _ _ (_ ++ ?r) =>
      frame_out empty r
    end;
    (** Renormalising back. **)
    repeat (rewrite -catA) in
  repeat first [ progress left tt | progress right tt ].

(** Same as [frame_out], by the frames are existential variables. **)
Ltac eframe :=
  let l := fresh "l" in
  evar (l : seq administrative_instruction);
  let r := fresh "r" in
  evar (r : seq administrative_instruction);
  frame_out l r.

Local Lemma run_step_fuel_increase_aux : forall d es s f s' f' r' fuel fuel',
  fuel <= fuel' ->
  TProp.Forall (fun e => forall d tt s f r fuel fuel',
     fuel <= fuel' ->
     run_one_step fuel d tt e = (s, f, r) ->
     r = RS_crash C_exhaustion \/ run_one_step fuel' d tt e = (s, f, r)) es ->
  run_step_with_fuel fuel d (s, f, es) = (s', f', r') ->
  r' = RS_crash C_exhaustion
  \/ run_step_with_fuel fuel' d (s, f, es) = (s', f', r').
Proof.
  move => d es s f s' f' r' fuel fuel' I F. destruct fuel as [|fuel].
  - unfold run_step_with_fuel; unfold interpreter_func.run_step_with_fuel.
    intro H ; inversion H ; by left.
  - unfold run_step_with_fuel.  
    destruct fuel' as [|fuel'] => /=.
    + by inversion I.
    + destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
      apply split_vals_e_v_to_e_duality in HSplitVals.
      destruct les as [|e les'] eqn:Hles.
      * intro H ; inversion H ; by right.
      * explode_and_simplify; try by intro H ; inversion H ; right.
        apply TProp.Forall_forall with (e := e) in F.
        -- destruct (run_one_step fuel d (s, f, rev lconst) e) as [[[hs'' s''] vs''] r''] eqn:E.  unfold run_one_step in E.     rewrite E.
           eapply F in E; [|by apply I|..]. destruct E as [E|E].
           ++ subst. intro H ; inversion H; by left.
           ++ unfold run_one_step in E.    
              rewrite E. by right.
        -- rewrite HSplitVals. apply Coqlib.in_app. right. by left.
Qed.

Lemma run_one_step_fuel_increase : forall d tt e s f r fuel fuel',
  fuel <= fuel' ->
  run_one_step fuel d tt e = (s, f, r) ->
  r = RS_crash C_exhaustion \/ run_one_step fuel' d tt e = (s, f, r).
Proof.
  move => + + e. induction e using administrative_instruction_ind' ;
    move => d [[tt_s tt_f] tt_es] s' f' r ;
    (case; first by move => ? ?; intro H ; inversion H; left) => fuel ;
    (case; first by []) => fuel' I /=.
  - by destruct b; explode_and_simplify; try intro H ; inversion H ; right.
  - intro H ; inversion H ;  by right.
  - intro H; by right.
  - by destruct f; explode_and_simplify; try intro H ; inversion H ; right.
  - explode_and_simplify; try by intro H ; inversion H ; right.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn: E.
    eapply run_step_fuel_increase_aux in E; [|by apply I|..] => //. destruct E as [E|E].
    + subst. intro H ; inversion H. by left.
    + rewrite E. by right. 
  - explode_and_simplify; try by intro H ; inversion H ; right.
    destruct run_step_with_fuel as [[s'' vs''] r''] eqn: E.
    eapply run_step_fuel_increase_aux in E; [|by apply I|..] => //. destruct E as [E|E].
    + subst. intro H ; inversion H. by left.
    + rewrite E. by right.
  - intro H ; inversion H ; by right.
Qed.

Lemma run_step_fuel_increase : forall d tt s f r fuel fuel',
  fuel <= fuel' ->
  run_step_with_fuel fuel d tt = (s, f, r) ->
  r = RS_crash C_exhaustion
  \/ run_step_with_fuel fuel' d tt = (s, f, r).
Proof.
  move=> d [[s f] es] s' f' r' fuel fuel' I. apply: run_step_fuel_increase_aux => //.
  apply: TProp.forall_Forall => e Ie.
  move=> > I' E'. apply: run_one_step_fuel_increase.
  + by apply: I'.
  + by apply: E'.
Qed.

Local Lemma max_fold_left_run_step_fuel : forall es,
  List.fold_left Init.Nat.max (List.map run_one_step_fuel es) 0
  <= TProp.max
       ((fix rect_list (es : seq administrative_instruction) : TProp.Forall (fun=> nat) es :=
          match es as es' return (TProp.Forall (fun=> nat) es') with
          | [::] => TProp.Forall_nil (fun=> nat)
          | e :: l => TProp.Forall_cons (run_one_step_fuel e) (rect_list l)
          end) es).
Proof.
  move=> es. match goal with |- is_true (_ <= TProp.max ?F) => set Fm := F end.
  rewrite -(PeanoNat.Nat.max_0_l (TProp.max Fm)). move: 0. induction es => n /=.
  - by lias.
  - rewrite maxn_nat_max PeanoNat.Nat.max_assoc. by apply: IHes.
Qed.

Local Lemma run_step_fuel_enough_aux : forall d s f es s' f' r',
  TProp.Forall (fun e => forall d tt s f r,
    run_one_step (run_one_step_fuel e) d tt e = (s, f, r) ->
    r <> RS_crash C_exhaustion) es ->
  run_step d (s, f, es) = (s', f', r') ->
  r' <> RS_crash C_exhaustion.
Proof.
  move => d s f es s' f' r' F. rewrite/run_step/interpreter_func.run_step.
  destruct interpreter_func.run_step_fuel eqn: E => //=.
   
  destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
  apply split_vals_e_v_to_e_duality in HSplitVals.
  
  destruct les as [|e les'] eqn:Hles.
  - by intro H ; inversion H.
  - explode_and_simplify; try by intro H ; inversion H.
    apply TProp.Forall_forall with (e := e) in F.
    + destruct (run_one_step (run_one_step_fuel e) d (s, f, rev lconst) e)
        as [[s'' f''] r''] eqn:E1.
      move: (E1) => E2. apply F in E2.
      apply run_one_step_fuel_increase with (fuel' := n) in E1.
      * destruct E1 as [E1|E1] => //.
        rewrite E1.
        by destruct r'' as [|[|]| | | ] => //; intro H ; inversion H.
      * move: E. rewrite /interpreter_func.run_step_fuel HSplitVals.
        rewrite List.map_app List.fold_left_app => /=.
        move=> E. have: exists v, n = PeanoNat.Nat.max (run_one_step_fuel e) v.
        {
          move: E. clear. move: (List.fold_left _ _ 0). induction les' => /=.
          - move=> v E. exists v. by lias.
          - move=> v E. apply: IHles'.
            rewrite PeanoNat.Nat.max_comm in E. rewrite PeanoNat.Nat.max_assoc in E. by apply: E.
        }
        move=> [v E']. by lias.
    + rewrite HSplitVals. apply Coqlib.in_app. right. by left.
Qed.

(** [run_one_step_fuel] is indeed enough fuel to run [run_one_step]. **)
Lemma run_one_step_fuel_enough : forall d tt e s f r,
  run_one_step (run_one_step_fuel e) d tt e = (s, f, r) ->
  r <> RS_crash C_exhaustion.
Proof.
  move=> + + e. induction e using administrative_instruction_ind';
    move=> d [[tt_s tt_f] tt_es] s' f' r //.
  - simpl. destruct b ; (try destruct v); explode_and_simplify; (try destruct n); (try destruct n0); explode_and_simplify; pattern_match => //.
  - by pattern_match.
  - simpl. explode_and_simplify; try pattern_match => //.
  - simpl. explode_and_simplify; try pattern_match => //.
  - rename l0 into es2.
    set fu := (run_one_step_fuel (AI_label n l es2)) .-1.
    simpl in fu.
    assert ((run_step_fuel (tt_s, tt_f, es2)) <= fu).
    {
      rewrite/fu /=.
      move: (max_fold_left_run_step_fuel es2). clear.
      unfold run_one_step_fuel.
      (* lias needs some help to establish the inequality here. *)
      match goal with |- context [?a <= ?b] => set x := a; set y := b end.
      by lias.
    }
    simpl.
    explode_and_simplify; try by pattern_match.
    destruct (run_step d (tt_s, tt_f, es2)) as [[s'' f''] r''] eqn:E1.
    move: (E1) => E2. unfold run_step, interpreter_func.run_step in E2.
    apply run_step_fuel_increase with (fuel' := fu) in E2.
    move: (E1) => D. apply run_step_fuel_enough_aux in D => //.
    + destruct E2 as [E2|E2] => //.

      rewrite E2.
      by destruct r'' as [|[|]| | | ] => //; explode_and_simplify; pattern_match.
    + by [].
  - rename l into es. 
    set fu := (run_one_step_fuel (AI_local n f es)) .-1.
    simpl in fu.
    assert (run_step_fuel (tt_s, f, es) <= fu).
    {
      apply/leP. rewrite/fu /=.
      move: (max_fold_left_run_step_fuel es). clear.
      unfold run_one_step_fuel.
      (* Same as above, lias needs some help to establish the inequality here too. *)
      match goal with |- context [?a <= ?b] => set x := a; set y := b end.
      by lias.
    }
    simpl.
    explode_and_simplify; try by pattern_match.
    destruct (run_step d (tt_s, f, es)) as [[s'' f''] r''] eqn:E1.
    move: (E1) => D. apply run_step_fuel_enough_aux in D => //.
    move: (E1) => E2. apply run_step_fuel_increase with (fuel' := fu) in E2.
    + destruct E2 as [E2|E2] => //.

      rewrite E2.
      by destruct r'' as [|[|]| | |] => //; explode_and_simplify; pattern_match.
    + by [].
  - simpl. by pattern_match.
Qed.

(** [run_step_fuel] is indeed enough fuel to run [run_step]. **)
Lemma run_step_fuel_enough : forall d tt s f r,
  run_step d tt = (s, f, r) ->
  r <> RS_crash C_exhaustion.
Proof.
  move=> d [[s f] r] s' f' r'. apply: run_step_fuel_enough_aux.
  apply: TProp.forall_Forall => e Ie.
  move=> >. by apply: run_one_step_fuel_enough.
Qed.

(** If the result of the interpreter is a [RS_break], then we were executing
  either a [Br] or a [Label] instruction, which itself returned a [RS_break]. **)
Local Lemma rs_break_trace_bool: forall fuel d s f es s' f' n es',
  run_step_with_fuel fuel.+2 d (s, f, es)
  = (s', f', RS_break n es') ->
  let: (ves, es'') := split_vals_e es in
  exists e es2 ln les es3, (es'' == e :: es2) &&
   ((e == AI_basic (BI_br n)) && ((s', f', es') == (s, f, rev ves)) ||
    (e == AI_label ln les es3) &&
     ((run_step_with_fuel fuel d (s, f, es3))
      == (s', f', RS_break n.+1 es'))).
Proof.
  move => fuel d s f es s' f' n es' /= H.
  unfold run_step_with_fuel in H.    
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2']=> //.
  destruct e as [b| | | |n0 l l0|n0 l l0| ]=> //; unfold e_is_trap in H.
  - destruct b => //; (try destruct v); move:H; try explode_and_simplify; try destruct n0; try destruct n1; try explode_and_simplify; try done.
    + (* AI_basic (Br i0) *)
      pattern_match.
      exists (AI_basic (BI_br n)). exists es2'.
      (* unused ones *) exists 0. exists [::]. exists [::].
      move. apply/andP. split; first done. apply/orP. left. apply/andP. by split => //=.
  - move:H. by explode_and_simplify.
  - move:H. by explode_and_simplify;
    destruct host_application_impl; by explode_and_simplify.
  - (* Label *) exists (AI_label n0 l l0). exists es2'. exists n0. exists l. exists l0.
    apply/andP. split => //.
    apply/andP. split => //.
    apply/eqP.
    move:H. explode_and_simplify.
    destruct run_step_with_fuel as [[[hs'' s''] f''] r''] eqn:HDestruct.
    unfold run_one_step, run_step_with_fuel in HDestruct.
    rewrite HDestruct.
    destruct r'' as [ |n' rvs'| | |]=> //. destruct n' ; last by pattern_match.
    by destruct (Nat.leb n0 (length rvs')).
  - (* Local *)
    move:H. explode_and_simplify.
    destruct (run_step_with_fuel fuel d (s, l, l0)) as [[[hs'' s''] f''] r''] eqn:HDestruct.
    unfold run_step_with_fuel in HDestruct. rewrite HDestruct.
    destruct r'' as [ | |rvs'| |]=> //. by destruct (Nat.leb n0 (length rvs')).
Qed.

(** Similar to [rs_break_trace_bool], but in [Prop]. **)
Lemma rs_break_trace: forall fuel d s f es s' f' n es',
  run_step_with_fuel fuel.+2 d (s, f, es)
  = (s', f', RS_break n es') ->
  let: (ves, es'') := split_vals_e es in
  exists e es2 ln les es3, (es'' = e :: es2) /\
    ((e = AI_basic (BI_br n)) /\ ((s, f, es') = (s', f', rev ves)) \/
    (e = AI_label ln les es3) /\
    ((run_step_with_fuel fuel d (s, f, es3))
     = (s', f', RS_break n.+1 es'))).
Proof.
  move => fuel d s f es s' f' n es' H.
  apply rs_break_trace_bool in H.
  destruct (split_vals_e es) as [lconst les'] eqn:HSplitVals.
  destruct H as [e [es2 [ln [les [es3 EH]]]]].
  exists e. exists es2. exists ln. exists les. exists es3.
  move/andP in EH. destruct EH as [HES EH2]. split; first by move/eqP in HES.
  move/orP in EH2. destruct EH2 as [HAI_basic|HLabel].
  - left. move/andP in HAI_basic. destruct HAI_basic as [HAI_basicE HAI_basicR].
    move/eqP in HAI_basicE. move/eqP in HAI_basicR. split => //. by inversion HAI_basicR.
  - right. move/andP in HLabel. destruct HLabel as [HLabelE HLabelR].
    move/eqP in HLabelE. move/eqP in HLabelR. by split => //.
Qed.

(** If the result of the interpreter is a [RS_return], then we were executing
  either a [AI_basic Return] or [Label] instruction, which itself returned a [RS_return]. **)
Lemma rs_return_trace: forall fuel d s f es s' f' rvs,
  run_step_with_fuel fuel.+2 d (s, f, es)
  = (s', f', RS_return rvs) ->
  let: (ves, es') := split_vals_e es in
  exists e es'' ln les es2,
    (es' = e :: es'') /\
    (e = AI_basic BI_return /\ (s, f, rvs) = (s', f', rev ves) \/
     (e = AI_label ln les es2 /\
      run_step_with_fuel fuel d (s, f, es2)
      = (s', f', RS_return rvs))).
Proof.
  move => fuel d s f es s' f' rvs /= H.
  unfold run_step_with_fuel in H.    
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2']=> //.
  destruct e as [b| | | | | |]=> //; unfold e_is_trap in H.
  - destruct b => //; (try destruct v); move:H; try explode_and_simplify; try destruct n0; try destruct n; try explode_and_simplify; try done.
    + (* AI_basic Return *)
      exists (AI_basic BI_return). exists es2'.
      exists 0. exists [::]. exists [::].
      split => //. left. split => //. by inversion H.
  - move:H. by explode_and_simplify.
  - move:H. by explode_and_simplify;
              destruct host_application_impl; explode_and_simplify.
  - (* Label *)
    exists (AI_label n l l0). exists es2'. exists n. exists l. exists l0.
    split => //. right. split => //.
    move:H. explode_and_simplify.
    destruct run_step_with_fuel as [[[hs'' s''] f''] r''] eqn:HDestruct => //.
    unfold run_step_with_fuel in HDestruct; rewrite HDestruct.
    destruct r'' as [ |n' rvs'| | |]=> //; try pattern_match.
    destruct n' => //.
    by destruct (Nat.leb n (length rvs')).
  - (* Local *)
    move:H. explode_and_simplify.
    destruct (run_step_with_fuel fuel d (s, f0, l)) as [[[hs'' s''] f''] r''] eqn:HDestruct => //.
    unfold run_step_with_fuel in HDestruct; rewrite HDestruct.
    destruct r'' as [ | |rvs'| |]=> //; try pattern_match.
    by destruct (Nat.leb n (length rvs')).
Qed.

(** If the result of the interpreter is a [RS_break], then we must have
  started with at least 2 fuel.
    The lemma is stated in this way to make application of other lemmas
  easier. **)
Lemma rs_break_takes_2_fuel: forall fuel d s f es s' f' n es',
  run_step_with_fuel fuel d (s, f, es)
  = (s', f', RS_break n es') ->
  exists fuel', fuel = fuel'.+2 .
Proof.
  destruct fuel; first by [].
  move => d s f es s' f' n es'.
  unfold run_step_with_fuel.  
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2'] => //.
  destruct e => //=; try (destruct fuel => //; by exists fuel).
  by explode_and_simplify.
Qed.

Lemma rs_return_takes_2_fuel: forall fuel d s f es s' f' rvs,
  run_step_with_fuel fuel d (s, f, es)
  = (s', f', RS_return rvs) ->
  exists fuel', fuel = fuel'.+2 .
Proof.
  destruct fuel; first by [].
  move => d s f es s' f' rvs.
  unfold run_step_with_fuel.  
  destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
  apply split_vals_e_v_to_e_duality in HSplit.
  destruct es2 as [|e es2'] => //.
  destruct e => //=; try (destruct fuel => //; by exists fuel).
  by explode_and_simplify.
Qed.

(** A sequence of labels with a break/return inside the inner most level. This
  characterises the stack when the interpreter ends execution with an
  [RS_break] or [RS_return]. **)
Inductive Label_sequence: nat -> seq administrative_instruction -> administrative_instruction -> seq administrative_instruction -> Prop :=
  | LS_Break: forall n vs es,
           const_list vs ->
           Label_sequence 0 vs (AI_basic (BI_br n)) (vs ++ [::AI_basic (BI_br n)] ++ es)
  | LS_Return: forall vs es,
           const_list vs ->
           Label_sequence 0 vs (AI_basic BI_return) (vs ++ [::AI_basic BI_return] ++ es)
  | LS_Label: forall k m vs0 e0 vs es bs es',
           const_list vs ->
           Label_sequence k vs0 e0 bs ->
           Label_sequence (k.+1) vs0 e0 (vs ++ [::AI_label m es' bs] ++ es).

(** [Label_sequence] is in fact very similar to lfilled. **)
Lemma Label_sequence_lfilled_exists: forall k vs e bs,
  Label_sequence k vs e bs ->
  exists lh es, lfilledInd k lh es bs.
Proof.
  elim.
  - move => vs0 e0 bs H. inversion H; subst.
    + exists (LH_base vs0 es). exists [::AI_basic (BI_br n)]. apply LfilledBase => //.
    + exists (LH_base vs0 es). exists [::AI_basic BI_return]. apply LfilledBase => //.
  -  move => k IHk vs0 e0 bs H. inversion H. subst.
    apply IHk in H2. destruct H2 as [lh [es2 HLF]].
    repeat eexists. apply LfilledRec => //.
    eassumption.
Qed.

Lemma Label_sequence_lfilledk: forall k vs e bs m,
  Label_sequence k vs e bs ->
  m <= size vs ->
  exists lh, lfilledInd k lh (drop m vs ++ [::e]) bs.
Proof.
  move => k. induction k.
  - move => vs e bs m HLS HSize.
    inversion HLS; subst; exists (LH_base (take m vs) es); by apply lfilled0_take_drop.
  - move => vs e bs m HLS HSize. inversion HLS. subst.
    eapply IHk in H1. destruct H1 as [lh EH].
    eexists. apply LfilledRec => //.
    apply EH.
    assumption.
Qed.

(** If the interpreter successfully finishes execution given stack [es] and ends
  up with [RS_break n es'], then [es] is well-founded, i.e. the recursive case
  [Label _ _ _] cannot take place infinitely often. In fact we even know exactly
  how many times the recursive case takes place. **)
Lemma rs_break_wellfounded: forall fuel d s f es s' f' n es',
  run_step_with_fuel fuel d (s, f, es)
  = (s', f', RS_break n es') ->
  s = s' /\ f = f' /\
  (exists k m vs0, k+n=m /\ Label_sequence k vs0 (AI_basic (BI_br m)) es /\
  v_to_e_list es' = rev vs0).
Proof.
  intros fuel.
  remember fuel as fuel'.
  assert (fuel' <= fuel) as Hfuel; first by subst; lias.
  clear Heqfuel'.
  destruct fuel.
  { destruct fuel'; last lias.
    move => d s f es s' f' n es' H.
    inversion H. }
  generalize dependent fuel'. 
  induction fuel; intros fuel' Hfuel.
  - (* fuel = 1 *)
    move => d s f es s' f' n es' H.
    destruct fuel'; first by inversion H. destruct fuel'; last lias.
    apply rs_break_takes_2_fuel in H. by inversion H.
  - (* fuel >= 2 *)
    move => d s f es s' f' n es' H.
    destruct fuel'; first by inversion H.
    destruct fuel'; first by apply rs_break_takes_2_fuel in H; inversion H.
    eapply rs_break_trace in H.
    destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
    apply split_vals_e_v_to_e_duality in HSplit.
    destruct H as [e [es3 [ln [les [es4 EH]]]]].
    destruct EH as [HES [[HAI_basicE HAI_basicR] | [HLabelE HLabelR]]].
    + inversion HAI_basicR. subst. repeat split => //.
      exists 0. exists n. exists (v_to_e_list vs2). repeat split => //.
      * apply LS_Break. by apply v_to_e_is_const_list.
      * by apply v_to_e_rev.
    + apply IHfuel in HLabelR.
      destruct HLabelR as [Hs [Hvs [k [m [vs0 [HSum [HLS HES']]]]]]]. subst.
      repeat split => //.
      exists (k.+1). exists (k.+1+n). exists vs0. repeat split => //.
      apply LS_Label => //. by apply v_to_e_is_const_list.
      replace (k.+1+n) with (k+n.+1) => //.
      by lias.
      lias.
Qed.

Lemma rs_return_wellfounded: forall fuel d s f es s' f' es',
  run_step_with_fuel fuel d (s, f, es)
  = (s', f', RS_return es') ->
  s = s' /\ f = f' /\ (exists k vs0, Label_sequence k vs0 (AI_basic BI_return) es /\
  v_to_e_list es' = rev vs0).
Proof.
  intros fuel.
  remember fuel as fuel'.
  assert (fuel' <= fuel) as Hfuel; first by subst; lias.
  clear Heqfuel'.
  destruct fuel.
  { destruct fuel'; last lias.
    move => d s f es s' f' es' H.
    inversion H. }
  generalize dependent fuel'. 
  induction fuel; intros fuel' Hfuel.
  - (* fuel = 1 *)
    move => d s f es s' f' es' H.
    destruct fuel'; first by inversion H.
    destruct fuel'; last lias.
    apply rs_return_takes_2_fuel in H. by inversion H.
  - (* fuel >= 2 *)
    move => d s f es s' f' es' H.
    destruct fuel'; first by inversion H.
    destruct fuel'; first by apply rs_return_takes_2_fuel in H; inversion H.
    eapply rs_return_trace in H.
    destruct (split_vals_e es) as [vs2 es2] eqn:HSplit.
    apply split_vals_e_v_to_e_duality in HSplit.
    destruct H as [e [es3 [ln [les [es4 EH]]]]].
    destruct EH as [HES [[HAI_basicE HAI_basicR] | [HLabelE HLabelR]]].
    + inversion HAI_basicR. subst. repeat split => //.
      exists 0. exists (v_to_e_list vs2). repeat split => //.
      * apply LS_Return. by apply v_to_e_is_const_list.
      * by apply v_to_e_rev.
    + apply IHfuel in HLabelR.
      destruct HLabelR as [Hs [Hvs [k [vs0 [HLS HES']]]]]. subst.
      repeat split => //.
      exists (k.+1). exists vs0. repeat split => //.
      apply LS_Label => //. by apply v_to_e_is_const_list.
      lias.
Qed.

(** Main proof for the [RS_break] case. **)
Lemma reduce_label_break: forall fuel d s f es es' s' f' es'' n,
  run_step_with_fuel fuel d (s, f, es') =
  (s', f', RS_break 0 es'') ->
  n <= size es'' ->
  reduce s f ([:: AI_label n es es']) Eempty s' f'
   (v_to_e_list (rev (take n es'')) ++ es).
Proof.
  move => fuel d s f es es' s' f' es'' n H HSize.
  apply rs_break_wellfounded in H.
  destruct H as [Hs [Hvs [k [m [vs0 [HSum [HLS HES']]]]]]]. subst.
  rewrite addn0 in HLS.
  destruct k.
  - inversion HLS as [n1 vs1 es1 HConst| |]. subst.
    apply rm_silent, r_simple. eapply rs_br; first by apply v_to_e_is_const_list.
    + simplify_lists.
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize as [H|H].
      * move/eqP in H. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H.
    + apply/lfilledP.
      symmetry in HES'. apply rev_move in HES'. rewrite HES'.
      simplify_lists.
      replace (rev es'') with (rev (drop n es'') ++ rev (take n es'')).
      simplify_lists.
         apply lfilled0_frame_l_empty; last by apply v_to_e_is_const_list.
      repeat rewrite catA. apply lfilled0_frame_r_empty.
      by apply lfilled0.
      { rewrite -rev_cat. by rewrite cat_take_drop. }
  - eapply Label_sequence_lfilledk in HLS.
    destruct HLS as [lh EH].
    apply rm_silent, r_simple. eapply rs_br; first by apply v_to_e_is_const_list.
    + simplify_lists.
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize as [H|H].
      * move/eqP in H. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H.
    + apply/lfilledP.
      replace (v_to_e_list (rev (take n es''))) with (drop (size vs0 - n) vs0).
      apply EH.
      {
        symmetry in HES'. apply rev_move in HES'. rewrite HES'.
        simplify_lists.
        by rewrite subKn.
      }
    + { by lias. }
Qed.




Lemma rev_cons_app {A} (x : A) (l : seq A) :
  rev (x :: l) = rev l ++ [:: x].
Proof. generalize dependent x. induction l => //= ; intro x.
       unfold rev. remember (a :: l) as l'.
       simpl. subst. do 2 rewrite catrevE.
       rewrite IHl.
       by rewrite cats0. Qed.

Lemma take_drop {A} n (l : list A) : n <= length l -> l = seq.take n l ++ seq.drop n l.
Proof.
  intros. generalize dependent n. induction l ; intros.  by inversion H.
  destruct n. by unfold take, drop.
  simpl. rewrite <- (IHl n) => //=.
Qed.

Lemma rev_rev {A} (l : seq A) : rev (rev l) = l.
Proof. induction l => //=. unfold rev => /=. do 2 rewrite catrevE.
       rewrite rev_cat. rewrite cats0.
       by rewrite IHl. Qed.



Lemma reduce_label_return: forall fuel d s f ess s' f' f2 vs n,
  run_step_with_fuel fuel d (s, f, ess) =
  (s', f', RS_return vs) ->
  n <= size vs ->
  reduce s f2 ([:: AI_local n f ess]) Eempty s' f2
   (v_to_e_list (rev (take n vs))).
Proof.
  move => fuel d s f ess s' f' f2 vs n H HSize.
  apply rs_return_wellfounded in H.
  destruct H as [Hs [Hvs [k [vs0 [HLS HES']]]]]. subst.
  destruct k.
  - inversion HLS as [|vs' es HConst|]. subst. apply rm_silent, r_simple.
    eapply rs_return; first by apply v_to_e_is_const_list.
    + simplify_lists.
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize as [H|H].
      * move/eqP in H. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H.
    + apply/lfilledP.
      symmetry in HES'. apply rev_move in HES'. rewrite HES'.
      rewrite -v_to_e_rev. replace (rev vs) with (rev (drop n vs) ++ rev (take n vs)).
      rewrite -v_to_e_cat. repeat rewrite v_to_e_rev.
      repeat rewrite -catA. apply lfilled0_frame_l_empty.
      repeat rewrite catA. apply lfilled0_frame_r_empty.
      simplify_lists. by apply lfilled0.
      { rewrite -v_to_e_rev.  by apply v_to_e_is_const_list. }
      { rewrite -rev_cat. by rewrite cat_take_drop. }
  - 
    eapply Label_sequence_lfilledk in HLS.
    destruct HLS as [lh EH].
    apply rm_silent, r_simple. eapply rs_return; first by apply v_to_e_is_const_list.
    + simplify_lists.
      rewrite leq_eqVlt in HSize. move/orP in HSize. destruct HSize as [H|H].
      * move/eqP in H. subst. apply /eqP. by rewrite ltnn.
      * by rewrite H.
    + apply/lfilledP.
      replace (v_to_e_list (rev (take n vs))) with (drop (size vs0 - n) vs0).
      apply EH.
      * symmetry in HES'.
        apply rev_move in HES'. rewrite HES'.
        simplify_lists.
        by rewrite subKn.
    +  by lias.
Qed.

Ltac frame_cat :=
  lazymatch goal with
  | |- reduce _ _ _ (v_to_e_list ?l1 ++ _) _ _ _ (v_to_e_list (take ?n ?l1) ++ _) =>
    rewrite (v_to_e_take_drop_split l1 n); rewrite -catA;
    apply: r_eliml; try apply: v_to_e_is_const_list
  end.

Lemma plus_binnat_leq : forall x z y, BinNat.N.le (BinNat.N.add x (BinNat.N_of_nat z)) y -> nat_of_bin (x) + z <= nat_of_bin y.
Proof.
  intros x z y.
  repeat rewrite nat_bin.
  lias.
Qed.

Lemma plus_binnat_lt : forall x y z, BinNat.N.lt x (BinNat.N.add y (BinNat.N_of_nat z)) -> nat_of_bin x < nat_of_bin y + z.
Proof.
  intros x y z. repeat rewrite nat_bin. lias.
Qed.

Lemma binnat_lt : forall a b, BinNat.N.lt a b -> nat_of_bin a < nat_of_bin b.
Proof.
  intros x y z. repeat rewrite nat_bin. lias.
Qed.







Local Lemma run_step_soundness_aux : forall fuel d s f es s' f' es',
    wellFormedState s ->
    run_step_with_fuel fuel d (s, f, es)
  = (s', f', RS_normal es') ->
    (exists me, reduce s f es me s' f' es') /\ wellFormedState s'.
Proof.
  intros fuel.
  remember fuel as fuel'.
  assert (fuel' <= fuel) as Hfuel; first by subst; lias.
  clear Heqfuel'.
  destruct fuel.
  { destruct fuel'; last lias.
    move => d s f es s' f' es' x H.
    inversion H. }
  generalize dependent fuel'. 
  induction fuel; intros fuel' Hfuel.
  {
     move=> d s f es s' f' es' HWF /=.
  destruct fuel' as [|fuel'] => //=.
     
  destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
  apply split_vals_e_v_to_e_duality in HSplitVals. rewrite {} HSplitVals.
  destruct les as [|e les'] eqn:Hles => //.
  explode_and_simplify.
  {
    pattern_match. destruct e => //. subst; split => //. exists Eempty. apply: rm_silent. apply: r_simple.
    apply rs_trap with (lh := LH_base (v_to_e_list lconst) les').
    - move/orP in if_expr0. inversion if_expr0 => //=.
      + move/eqP in H0. destruct lconst => //=. by destruct les'. destruct v => //.
      + move/eqP in H0. destruct lconst => //. destruct v => //.
    - rewrite/operations.lfilled/operations.lfill. rewrite v_to_e_is_const_list. show_list_equality.
  }
  destruct fuel' as [|fuel'] => //. 
  }
  move=> d s f es s' f' es' HWF /=.
  destruct fuel' as [|fuel'] => //=.
     
  destruct (split_vals_e es) as [lconst les] eqn:HSplitVals.
  apply split_vals_e_v_to_e_duality in HSplitVals. rewrite {} HSplitVals.
  destruct les as [|e les'] eqn:Hles => //.
  explode_and_simplify.
  {
    pattern_match. destruct e => //. subst; split => //. exists Eempty. apply: rm_silent. apply: r_simple.
    apply rs_trap with (lh := LH_base (v_to_e_list lconst) les').
    - move/orP in if_expr0. inversion if_expr0 => //=.
      + move/eqP in H0. destruct lconst => //=. by destruct les'. destruct v => //.
      + move/eqP in H0. destruct lconst => //. destruct v => //.
    - rewrite/operations.lfilled/operations.lfill. rewrite v_to_e_is_const_list. show_list_equality.
  }
  destruct fuel' as [|fuel'] => //. destruct e as [b| | |cl|n es1 es2|n f0 ess|].
    { (** [AI_basic b] **) 
      destruct b.
      - (** [AI_basic Unreachable] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        subst; split => //.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        by repeat econstructor.

      - (** [AI_basic Nop] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        subst; split => //. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::]) => /=.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        by repeat econstructor.

      - (** [AI_basic Drop] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        subst; split => //.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::]) => /=.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        rewrite (catA [:: AI_const _]).
        done.
        by repeat econstructor.

      - (** [AI_basic Select] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.

        subst; split => //.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        do 2 rewrite rev_cons_app.
        do 2 rewrite - v_to_e_cat.
        repeat rewrite - catA.
        rewrite (catA (v_to_e_list [:: v1])).
        rewrite (catA (v_to_e_list [:: v1] ++ _)).
        rewrite (catA ((_ ++ _) ++ _)).
        done.
        by repeat econstructor.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        do 2 rewrite rev_cons_app.
        do 2 rewrite - v_to_e_cat.
        repeat rewrite - catA.
        rewrite (catA (v_to_e_list [:: v1])).
        rewrite (catA (v_to_e_list [:: v1] ++ _)).
        rewrite (catA ((_ ++ _) ++ _)).
        done.
        by repeat econstructor.


      - (** [AI_basic Block] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        erewrite (take_drop (l := lconst)) at 1.
        rewrite - v_to_e_cat.
        rewrite - catA.
        rewrite (catA (v_to_e_list (drop _ _))).
        done.
        rewrite length_is_size.
        by apply leq_subr.
        apply: rm_silent. apply: r_simple. apply: rs_block; first by apply: v_to_e_is_const_list.
        + by eauto.
        + repeat rewrite length_is_size.
          rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
          rewrite subKn. done. apply Compare_dec.leb_complete in if_expr0.
          lias.
        + done.

      - (** [AI_basic loop] **)
        simpl. explode_and_simplify. pattern_match. auto_frame.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        erewrite (take_drop (l := lconst)) at 1.
        rewrite - v_to_e_cat.
        rewrite - catA.
        rewrite (catA (v_to_e_list (drop _ _))).
        done.
        rewrite length_is_size.
        by apply leq_subr.
        apply: rm_silent. apply: r_simple. apply: rs_loop => //=.
        +(*1*) by apply: v_to_e_is_const_list.
        +(*2*) repeat rewrite length_is_size.
          rewrite v_to_e_drop_exchange. rewrite size_drop. rewrite v_to_e_size.
          rewrite subKn => //.
          apply Compare_dec.leb_complete in if_expr0. lias.

      - (** [AI_basic If] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; stack_frame; subst_rev_const_list; auto_frame.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        rewrite (catA [:: AI_const _]).
        done.
        by repeat econstructor.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        rewrite (catA [:: AI_const _]).
        done.
        by repeat econstructor.

      - (** [AI_basic (Br i0)] **)
        by pattern_match.

      - (** [AI_basic Br_if] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::]) => /=.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        rewrite (catA [:: AI_const _]).
        done.
        by repeat econstructor.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        rewrite (catA [:: AI_const _]).
        done.
        by repeat econstructor.

      - (** [AI_basic Br_table] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        rewrite (catA [:: AI_const _]).
        done.
        econstructor.
        econstructor.
        econstructor => //.
        apply Compare_dec.leb_complete in if_expr0. lias.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        rewrite (catA [:: AI_const _]).
        done.

        + apply: rm_silent. apply: r_simple. apply: rs_br_table_length.
          rewrite length_is_size.
          apply Nat.ltb_ge in if_expr0; lias.


      - (** [AI_basic Return] **)
        by pattern_match.

      - (** [AI_basic (Call i0)] **)
        simpl. explode_and_simplify. pattern_match. auto_frame.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        subst.

        by eapply rm_silent, r_call.

      - (** [AI_basic (Call_indirect i0)] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        + split; last by subst. exists Eempty.
          eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          done.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_call_indirect_success; eauto.

        + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          done.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_call_indirect_failure1; eauto.
        + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          done.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_call_indirect_failure2; eauto.

      - (** [AI_basic (Get_local i0)] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          done.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ]) => //=.
          subst.
          by eapply rm_silent, r_get_local.

      - (** [AI_basic (Set_local i0)] **)
        simpl. explode_and_simplify. pattern_match.
        rewrite -update_list_at_is_set_nth => //=.
        auto_frame. split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ; _]) => //=.
        subst.
        apply Nat.ltb_lt in if_expr0.
        apply: rm_silent; apply: r_set_local => //.
        lias.
        apply Nat.ltb_lt in if_expr0. lias.
      - (** [AI_basic (Tee_local i0)] **)
        simpl. explode_and_simplify. pattern_match. subst_rev_const_list.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _; _; _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ; _]) => //=.
        subst.
        econstructor. econstructor. econstructor. by apply const_const.

      - (** [AI_basic (Get_global i0)] **)
        simpl. explode_and_simplify. pattern_match. auto_frame. 
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _]) => //=.
        subst.
        by eapply rm_silent, r_get_global.

      - (** [AI_basic (Set_global i0)] **)
        simpl. explode_and_simplify. pattern_match.
        split.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: ]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ; _]) => //=.
        subst.
        by eapply rm_silent, r_set_global.
        subst.
        unfold wellFormedState in HWF.
        unfold supdate_glob in option_expr.
        unfold option_bind in option_expr.
        destruct (sglob_ind _ _ _) eqn:Hglob => //.
        unfold supdate_glob_s in option_expr.
        unfold option_map in option_expr.
        destruct (List.nth_error _ n) => //.
        inversion option_expr; subst => //=.


      - (** [AI_basic (Load v o a0 s0)] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; try (pattern_match; auto_frame).
        + split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_load_packed_success; eassumption.
        + split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_load_packed_failure; eassumption.
        + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_load_success; try eassumption.

        + split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          apply: rm_silent; apply: r_load_failure; try eassumption.
          by right.
              + split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_load_success; try eassumption.
        + split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          apply: rm_silent; apply: r_load_failure; try eassumption.
          by right.
        + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_load_success; try eassumption.

        + split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          apply: rm_silent; apply: r_load_failure; try eassumption.
          by right.
              + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_load_success; try eassumption.

        + split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _]) => //=.
          subst.
          apply: rm_silent; apply: r_load_failure; try eassumption.
          by right.


      - (** [AI_basic (Colload t)] **)
        unfold run_one_step.
        destruct (v == T_pointer) eqn:Hv.
        simpl; explode_and_simplify; pattern_match; auto_frame.

        + exfalso. move /andP in if_expr0. destruct if_expr0 as [_ Hz] => //=.
        + exfalso. move /andP in if_expr0. destruct if_expr0 as [_ Hz] => //=.
        + exfalso. move /andP in if_expr0. destruct if_expr0 as [_ Hz] => //=.
        + exfalso. move /andP in if_expr0. destruct if_expr0 as [_ Hz] => //=.

        + rewrite <- H1. rewrite <- H2. split.
          * eexists (Eread T_pointer p). eapply (rm_label (k := 0)
              (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            --
              move /andP in if_expr1.
              destruct if_expr1 as [Halloc Halign].
              apply: rm_colload_ptr_success; eauto.
              ++ apply isAlloc_eq => //=.
              ++ apply isAlign_eq => //=.
              ++ unfold colload in HExpect.
                 case Htmp: (ptr_addr p + N.of_nat pointer_size <=? cmem_length (s_cmems s))%N; rewrite Htmp in HExpect => //=.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list.
               show_list_equality.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list //=.
          * exact HWF.

        + rewrite <- H1. rewrite <- H2. split.
          * eexists (Etrap). eapply (rm_label (k := 0)
              (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            --
              move /andP in if_expr1.
              destruct if_expr1 as [Halloc Halign].
              eapply rm_colload_failure. eauto. eauto.
              right. right. right. right.
              intros.
              apply /eqP.
              unfold colload in HExpect. case Htmp: (ptr_addr p + N.of_nat pointer_size <=? cmem_length (s_cmems s))%N; rewrite Htmp in HExpect => //=.
              assert (Some tbs = Some l0). rewrite <- H4. rewrite <- HExpect.   simpl. auto.
              assert (tbs = l0). by injection H5.
              subst tbs.
              rewrite option_expr in H0; inversion H0; subst c.
              rewrite if_expr2.
              auto.
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list //=.
          * exact HWF.

        + rewrite <- H1. rewrite <- H2. split.
          * eexists (Etrap). eapply (rm_label (k := 0)
              (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            --
              move /andP in if_expr1.
              destruct if_expr1 as [Halloc Halign].
              eapply rm_colload_failure. eauto. eauto.
              right. right. left.
              case Htmp: (ptr_addr p + N.of_nat pointer_size <=? cmem_length (s_cmems s))%N.
              { unfold colload in HExpect. rewrite Htmp in HExpect. exact HExpect. }
              eapply colload_None_read_colbytes_None.
              apply size_is_not_zero.
              exact HExpect.
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list //=.
          * exact HWF.

        + rewrite <- H1. rewrite <- H2. split.
          * eexists (Etrap). eapply (rm_label (k := 0)
              (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            --
              eapply rm_colload_failure. eauto. eauto.
              right.
              destruct (isAllocb v1 (s_alls s)) eqn:Halloc.
              ++ left.
                 rewrite isAlign_eq. move: if_expr1. by move /negP.
              ++ right. right. left. rewrite isAlloc_eq.
                 rewrite option_expr in H0; inversion H0; subst c. rewrite Halloc. by [].
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list //=.
          * exact HWF.

        + rewrite <- H1. rewrite <- H2. split.
          * eexists (Etrap). eapply (rm_label (k := 0)
              (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            --
              eapply rm_colload_failure. eauto. eauto.
              left.
              unfold is_null. apply /eqP. exact option_expr.
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
            -- unfold lfilled, lfill. rewrite v_to_e_is_const_list //=.
          * exact HWF.

        + split.
          * subst.
            destruct v => //=; simpl in H. (* here it destructs into i32, i64, f32, f64, pointer. Although I would really like for it to just split into pointer and non-pointer *)

            -- (* i32 *)
              case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []).
              destruct v eqn:Hvp => //=; rewrite Hrev in H.
              { (* v = VAL_numeric n *)
                unfold crash_error in H; by case: H.
              }
              (* v = VAL_pointer p *)
              case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H.
              { (* ptr_col p = Some c *)
                case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H.
                { (* isAllocb c (s_alls s) *)
                  case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H; simpl in H.
                  { (* read_colbytes = Some tbs *)
                    case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H.
                    {
                      case: H => <- <- Hes.
                      eexists (Eread T_i32 p).
                      eapply (rm_label (k := 0)
                        (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i32)])
                        (lh := LH_base (v_to_e_list (rev ves')) les')).
                      - eapply rm_colload_success; eauto.
                        rewrite isAlloc_eq. by rewrite if_expr2.
                      - unfold lfilled, lfill.
                        rewrite v_to_e_is_const_list.
                        show_list_equality.
                      - unfold lfilled, lfill.
                        rewrite v_to_e_is_const_list //=.
                        rewrite -Hes.
                        rewrite /vs_to_es /v_to_e_list rev_cons -cats1 map_cat map_cons /AI_const //=.
                        show_list_equality.
                    }
                      eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                      ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto.
                        right. right. right. right. move => tb0 H3 Hread.
                        rewrite if_expr1 in H. inversion H. subst c0.
                        assert (Some tbs = Some tb0). rewrite <- if_expr3. simpl in H3. exact H3.
                        assert (tbs = tb0). by injection H0. subst.
                        by rewrite Hread in if_expr4.
                      ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                      ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
                  }
                  (* read_colbytes = None *)
                  eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                  ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto.
                    right. right. left. exact if_expr3.
                  ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                  ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
                }
                (* ~isAllocb c (s_alls s) *)
                eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto.
                  right. right. right. left. rewrite isAlloc_eq.
                  rewrite if_expr1 in H; inversion H; subst c.
                  by rewrite if_expr2.
                ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
              }
              (* ptr_col p = None *)
              eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
              ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto.
                left. unfold is_null. by rewrite if_expr1.
              ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
              ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.

            -- (* i64 *) case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []). destruct v eqn:Hvp => //=; rewrite Hrev in H. { (* v = VAL_numeric n *) unfold crash_error in H; by case: H. } (* v = VAL_pointer p *) case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. { (* ptr_col p = Some c *) case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H. { (* isAllocb c (s_alls s) *) case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H; simpl in H. { (* read_colbytes = Some tbs *) case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H. { case: H => <- <- Hes. eexists (Eread T_i64 p). eapply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i64)]) (lh := LH_base (v_to_e_list (rev ves')) les')). - eapply rm_colload_success; eauto. rewrite isAlloc_eq. by rewrite if_expr2. - unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. - unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. rewrite -Hes. rewrite /vs_to_es /v_to_e_list rev_cons -cats1 map_cat map_cons /AI_const //=. show_list_equality. } eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. right. right. move => tb0 H3 Hread. rewrite if_expr1 in H. inversion H. subst c0. assert (Some tbs = Some tb0). rewrite <- if_expr3. simpl in H3. exact H3. assert (tbs = tb0). by injection H0. subst. by rewrite Hread in if_expr4. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* read_colbytes = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. left. exact if_expr3. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ~isAllocb c (s_alls s) *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. right. left. rewrite isAlloc_eq. rewrite if_expr1 in H; inversion H; subst c. by rewrite if_expr2. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ptr_col p = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. left. unfold is_null. by rewrite if_expr1. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
            -- (* f32 *) case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []). destruct v eqn:Hvp => //=; rewrite Hrev in H. { (* v = VAL_numeric n *) unfold crash_error in H; by case: H. } (* v = VAL_pointer p *) case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. { (* ptr_col p = Some c *) case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H. { (* isAllocb c (s_alls s) *) case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H; simpl in H. { (* read_colbytes = Some tbs *) case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H. { case: H => <- <- Hes. eexists (Eread T_f32 p). eapply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f32)]) (lh := LH_base (v_to_e_list (rev ves')) les')). - eapply rm_colload_success; eauto. rewrite isAlloc_eq. by rewrite if_expr2. - unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. - unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. rewrite -Hes. rewrite /vs_to_es /v_to_e_list rev_cons -cats1 map_cat map_cons /AI_const //=. show_list_equality. } eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. right. right. move => tb0 H3 Hread. rewrite if_expr1 in H. inversion H. subst c0. assert (Some tbs = Some tb0). rewrite <- if_expr3. simpl in H3. exact H3. assert (tbs = tb0). by injection H0. subst. by rewrite Hread in if_expr4. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* read_colbytes = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. left. exact if_expr3. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ~isAllocb c (s_alls s) *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. right. left. rewrite isAlloc_eq. rewrite if_expr1 in H; inversion H; subst c. by rewrite if_expr2. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ptr_col p = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. left. unfold is_null. by rewrite if_expr1. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
            -- (* f64 *) case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []). destruct v eqn:Hvp => //=; rewrite Hrev in H. { (* v = VAL_numeric n *) unfold crash_error in H; by case: H. } (* v = VAL_pointer p *) case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. { (* ptr_col p = Some c *) case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H. { (* isAllocb c (s_alls s) *) case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H; simpl in H. { (* read_colbytes = Some tbs *) case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H. { case: H => <- <- Hes. eexists (Eread T_f64 p). eapply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f64)]) (lh := LH_base (v_to_e_list (rev ves')) les')). - eapply rm_colload_success; eauto. rewrite isAlloc_eq. by rewrite if_expr2. - unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. - unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. rewrite -Hes. rewrite /vs_to_es /v_to_e_list rev_cons -cats1 map_cat map_cons /AI_const //=. show_list_equality. } eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. right. right. move => tb0 H3 Hread. rewrite if_expr1 in H. inversion H. subst c0. assert (Some tbs = Some tb0). rewrite <- if_expr3. simpl in H3. exact H3. assert (tbs = tb0). by injection H0. subst. by rewrite Hread in if_expr4. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* read_colbytes = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. left. exact if_expr3. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ~isAllocb c (s_alls s) *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. right. right. right. left. rewrite isAlloc_eq. rewrite if_expr1 in H; inversion H; subst c. by rewrite if_expr2. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ptr_col p = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_basic (BI_colload T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colload_failure. eauto. eauto. left. unfold is_null. by rewrite if_expr1. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.

          * unfold wellFormedState, isSound in HWF.
            destruct HWF as [HSound_a HSound_b].
            unfold wellFormedState.
            destruct v => //=. (* here it destructs into i32, i64, f32, f64, pointer. Although I would really like for it to just split into pointer and non-pointer *)
            ** (* i32 *)
              case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []).
              have Hlconst : lconst = rev [:: v & ves'].
              by rewrite -[lconst]revK Hrev => //=.
              rewrite Hrev in H. simpl in *. subst.
              destruct v => //=.
              case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H.
              case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H.
              case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H; simpl in H.
              case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H.
              {
                injection H as Hs Hf Hes.
                subst s'.
                unfold isSound.
                split; by [].
              }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }

            ** (* i64 *) case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v => //=. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H. case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H; simpl in H. case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H. { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
            ** (* f32 *) case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v => //=. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H. case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H; simpl in H. case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H. { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
            ** (* f64 *) case Hrev: (rev lconst) => [| v ves'] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v => //=. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H; simpl in H. case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H; simpl in H. case if_expr4: (all (fun tb : tagged_byte => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs); rewrite if_expr4 in H. { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. } { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }

      - (** [AI_basic (Store v o a0 s0)] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        + split; last by subst.
          exists Eempty; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [::]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_store_packed_success => //=; try eassumption; try apply/eqP; eauto.
        + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          rewrite rev_cons_app.
          rewrite - v_to_e_cat.
          repeat rewrite - catA.
          instantiate (1 := [:: _ ; _ ; _ ]) => //=.
          subst.
          by apply: rm_silent; apply: r_store_packed_failure => //=; eauto.
        + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [::]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ; _ ; _]) => //=.
          subst.
          by apply: rm_silent; apply: r_store_success => //=; eauto.
        + split; last by subst.
          exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          rewrite rev_cons_app.
          rewrite - v_to_e_cat.
          repeat rewrite - catA.
          instantiate (1 := [:: _ ; _ ; _ ]) => //=.
          subst.
          by apply: rm_silent; apply: r_store_failure => //=; eassumption.

      - (** [AI_basic (Colstore t)] **)
        unfold run_one_step.
        destruct (v == T_pointer) eqn:Hv.
        simpl; explode_and_simplify; pattern_match; auto_frame.

        + split.
          * eexists; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)); last first.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list.
               instantiate (2 := [::]) => //=.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list => /=.
               instantiate (1 := [:: AI_pointer p; AI_const v0; AI_basic (BI_colstore T_pointer)]) => //=.
            -- subst.
               apply: rm_colstore_ptr_success; eauto.
               move /andP in if_expr1.
               destruct if_expr1 as [Hagree Hnotpointer].
               apply isAlloc_eq => //=.
               move /andP in if_expr1.
               destruct if_expr1 as [Halloc Halign].
               apply isAlign_eq => //=.
          * subst.
            unfold wellFormedState, isSound.
            unfold wellFormedState, isSound in HWF.
            destruct HWF as [HSound_a Hsound_b].
            split; first by [].
            simpl.
            apply: write_cmembytes_preserves_isSound_b; eauto.
            move /andP in if_expr1.
            destruct if_expr1 as [Halloc Halign].
            by [].

        + split.
          * subst.
            eexists Etrap.
            apply (rm_label (k := 0)
              (es := [:: AI_pointer p; AI_const v0; AI_basic (BI_colstore T_pointer)])
              (es' := [:: AI_trap])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            -- apply: rm_colstore_failure; eauto.
               right; right; right; right.
               move=> tbs Hcol Hread.
               right.
               rewrite option_expr.
               exact: HExpect0.
              -- unfold lfilled, lfill.
                 rewrite v_to_e_is_const_list.
                 show_list_equality.
              -- unfold lfilled, lfill.
                 rewrite v_to_e_is_const_list cat1s //=.
          * subst; exact: HWF.

        + split.
          * subst.
            eexists Etrap.
            apply (rm_label (k := 0)
              (es := [:: AI_pointer p; AI_const v0; AI_basic (BI_colstore T_pointer)])
              (es' := [:: AI_trap])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            -- apply: rm_colstore_failure; eauto.
               right; right; right; right.
               intro tbs'.
               intro Hcol.
               intro Hread.
               left.
               have Hc : ptr_col p = Some v2 := option_expr.
               rewrite Hc in Hcol; injection Hcol => ?; subst.
               rewrite HExpect in Hread; injection Hread => ?; subst.
               destruct if_expr1; eauto.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list.
               show_list_equality.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list cat1s //=.
          * subst; exact: HWF.

        + split.
          * subst.
            eexists Etrap.
            apply (rm_label (k := 0)
              (es := [:: AI_pointer p; AI_const v0; AI_basic (BI_colstore T_pointer)])
              (es' := [:: AI_trap])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            -- apply: rm_colstore_failure.
               ++ by [].
               ++ by [].
               ++ right; right; left; exact: HExpect.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list.
               show_list_equality.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list cat1s //=.
          * subst; exact: HWF.

        + split.
          * subst.
            eexists Etrap.
            apply (rm_label (k := 0)
              (es := [:: AI_pointer p; AI_const v0; AI_basic (BI_colstore T_pointer)])
              (es' := [:: AI_trap])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            -- eapply rm_colstore_failure.
               ++ reflexivity.
               ++ reflexivity.
               ++ case: (boolP (isAllocb v2 (s_alls s'))) => H_alloc_b.
                  ** right. left.
                     move /eqP in Hv. split. exact Hv.
                     have H_align_false : isAlignb p = false.
                       move: if_expr1; rewrite H_alloc_b => H_and; simpl in H_and; exact: H_and.
                     apply/isAlignP; rewrite H_align_false; by [].
                  ** right. right. right. left.
                        rewrite option_expr in H0. inversion H0. subst v2.
                        rewrite isAlloc_eq. move : H_alloc_b.
                        apply contraNnot. auto.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list.
               show_list_equality.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list cat1s //=.
          * subst; exact: HWF.

        + split.
          * subst.
            eexists Etrap.
            apply (rm_label (k := 0)
              (es := [:: AI_pointer p; AI_const v0; AI_basic (BI_colstore T_pointer)])
              (es' := [:: AI_trap])
              (lh := LH_base (v_to_e_list (rev l)) les')).
            -- apply: rm_colstore_failure; eauto.
               left; rewrite /is_null option_expr; done.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list.
               show_list_equality.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list cat1s //=.
          * subst; exact: HWF.

        + split.
          * subst.
            destruct v => //=. (* here it destructs into i32, i64, f32, f64, pointer. Although I would really like for it to just split into pointer and non-pointer *)
            -- (* i32 *)
              case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []).
              have Hlconst : lconst = rev [:: v, v0 & ves'].
              by rewrite -[lconst]revK Hrev => //=.
              rewrite Hrev in H. simpl in *. subst.
              destruct v0 => //=.
              case if_expr0: (types_agree T_i32 v); last by rewrite if_expr0 in H; discriminate H.
              rewrite if_expr0 in H.
              simpl in H.
              case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H.
              { (* ptr_col = Some c*)
                case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H.
                { (* isAlloc c *)
                  case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H.
                  { (* readBytes *)
                    simpl in H.
                    case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H.
                    { (* all tagged correct *)
                      case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H.
                      { (* did write *)
                        simpl in H.
                        eexists. eapply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i32)]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                        ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_success; try eauto.
                           rewrite isAlloc_eq. by [].
                        ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                        ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
                      }
                      (* did not write *)
                      eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                      ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto.
                        right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread.
                        assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). simpl in Hread. rewrite if_expr3 in Hread. by injection Htbs0. subst.
                        right. rewrite if_expr1. apply if_expr5.
                      ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                      ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
                    }
                    (* not all tagged correct *)
                    eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                    ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto.
                      right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread.
                      assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). by injection Htbs0. subst.
                      left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite if_expr4. auto.
                    ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                    ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
                  }
                  (* not read bytes *)
                  eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                  ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto.
                     right. right. left. simpl. exact if_expr3.
                  ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                  ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
                }
                (* !isAlloc c *)
                eexists.
                apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
                ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto.
                   right. right. right. move => ccol Hccol. left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite isAlloc_eq. rewrite if_expr2. auto.
                ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality.
                ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
              }
              (* ptr_col = None *)
              eexists.
              apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')).
              ++
                 injection H as Hs Hf Hes.
                 subst f' s'.
                 eapply rm_colstore_failure.
                 eauto. eauto.
                 left. unfold is_null. rewrite if_expr1. reflexivity.
              ++ unfold lfilled, lfill.
                 rewrite v_to_e_is_const_list.
                 show_list_equality.
              ++ unfold lfilled, lfill.
                 rewrite v_to_e_is_const_list //=.
                 injection H as Hs Hf Hes.
                 rewrite <- Hes.
                 show_list_equality.

            (* This is really ugly. It's the previous block inlined for the rest of the cases *)
            -- (* i64 *) case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v, v0 & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v0 => //=. case if_expr0: (types_agree T_i64 v); last by rewrite if_expr0 in H; discriminate H. rewrite if_expr0 in H. simpl in H. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. { (* ptr_col = Some c*) case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H. { (* isAlloc c *) case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H. { (* readBytes *) simpl in H. case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H. { (* all tagged correct *) case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H. { (* did write *) simpl in H. eexists. eapply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i64)]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_success; try eauto. rewrite isAlloc_eq. by []. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* did not write *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread. assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). simpl in Hread. rewrite if_expr3 in Hread. by injection Htbs0. subst. right. rewrite if_expr1. apply if_expr5. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* not all tagged correct *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread. assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). by injection Htbs0. subst. left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite if_expr4. auto. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* not read bytes *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. left. simpl. exact if_expr3. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* !isAlloc c *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite isAlloc_eq. rewrite if_expr2. auto. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ptr_col = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_i64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. left. unfold is_null. rewrite if_expr1. reflexivity. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
            -- (* f32 *) case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v, v0 & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v0 => //=. case if_expr0: (types_agree T_f32 v); last by rewrite if_expr0 in H; discriminate H. rewrite if_expr0 in H. simpl in H. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. { (* ptr_col = Some c*) case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H. { (* isAlloc c *) case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H. { (* readBytes *) simpl in H. case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H. { (* all tagged correct *) case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H. { (* did write *) simpl in H. eexists. eapply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f32)]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_success; try eauto. rewrite isAlloc_eq. by []. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* did not write *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread. assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). simpl in Hread. rewrite if_expr3 in Hread. by injection Htbs0. subst. right. rewrite if_expr1. apply if_expr5. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* not all tagged correct *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread. assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). by injection Htbs0. subst. left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite if_expr4. auto. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* not read bytes *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. left. simpl. exact if_expr3. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* !isAlloc c *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite isAlloc_eq. rewrite if_expr2. auto. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ptr_col = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f32)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. left. unfold is_null. rewrite if_expr1. reflexivity. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.
            -- (* f64 *) case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v, v0 & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v0 => //=. case if_expr0: (types_agree T_f64 v); last by rewrite if_expr0 in H; discriminate H. rewrite if_expr0 in H. simpl in H. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. { (* ptr_col = Some c*) case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H. { (* isAlloc c *) case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H. { (* readBytes *) simpl in H. case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H. { (* all tagged correct *) case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H. { (* did write *) simpl in H. eexists. eapply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f64)]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_success; try eauto. rewrite isAlloc_eq. by []. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* did not write *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread. assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). simpl in Hread. rewrite if_expr3 in Hread. by injection Htbs0. subst. right. rewrite if_expr1. apply if_expr5. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* not all tagged correct *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. right. move => tb0 Hccol' Hread. assert (Htbs0 : Some tbs = Some tb0). rewrite <- if_expr3. exact Hread. assert (Htbs_eq : tbs = tb0). by injection Htbs0. subst. left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite if_expr4. auto. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* not read bytes *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. left. simpl. exact if_expr3. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* !isAlloc c *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. right. right. right. move => ccol Hccol. left. rewrite if_expr1 in Hccol. inversion Hccol. subst ccol. rewrite isAlloc_eq. rewrite if_expr2. auto. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality. } (* ptr_col = None *) eexists. apply (rm_label (k := 0) (es := [:: AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_f64)]) (es' := [:: AI_trap]) (lh := LH_base (v_to_e_list (rev ves')) les')). ++ injection H as Hs Hf Hes. subst f' s'. eapply rm_colstore_failure. eauto. eauto. left. unfold is_null. rewrite if_expr1. reflexivity. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list. show_list_equality. ++ unfold lfilled, lfill. rewrite v_to_e_is_const_list //=. injection H as Hs Hf Hes. rewrite <- Hes. show_list_equality.

          * unfold wellFormedState, isSound in HWF.
            destruct HWF as [HSound_a HSound_b].
            unfold wellFormedState.
            destruct v => //=. (* here it destructs into i32, i64, f32, f64, pointer. Although I would really like for it to just split into pointer and non-pointer *)
            ** (* i32 *)
              case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []).
              have Hlconst : lconst = rev [:: v, v0 & ves'].
              by rewrite -[lconst]revK Hrev => //=.
              rewrite Hrev in H. simpl in *. subst.
              destruct v0 => //=.
              case if_expr0: (types_agree T_i32 v); last by rewrite if_expr0 in H; discriminate H. rewrite if_expr0 in H. simpl in H.
              case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H.
              case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H.
              case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H. simpl in H.
              case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H.
              case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H. simpl in H.
              { injection H as Hs Hf Hes.
                unfold upd_s_cmem in Hs.
                have Hs': (s_alls s' = s_alls s) by inversion Hs.
                rewrite Hs'.
                split; first by exact HSound_a.
                eapply write_cmembytes_preserves_isSound_b.
                - instantiate (1 := s_cmems s). eauto.
                - instantiate (1 := Some c).
                  simpl. by rewrite if_expr2.
                - subst s'. simpl. exact if_expr5.
              }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
              { injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. }
            ** (* i64 *) case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v, v0 & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v0 => //=. case if_expr0: (types_agree T_i64 v); last by rewrite if_expr0 in H; discriminate H. rewrite if_expr0 in H. simpl in H. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H. case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H. simpl in H. case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H. case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H. simpl in H. injection H as Hs Hf Hes. unfold upd_s_cmem in Hs. have Hs': (s_alls s' = s_alls s) by inversion Hs. rewrite Hs'. split; first by exact HSound_a. eapply write_cmembytes_preserves_isSound_b. instantiate (1 := s_cmems s). eauto. instantiate (1 := Some c). simpl. by rewrite if_expr2. subst s'. simpl. exact if_expr5. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by [].
            ** (* f32 *) case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v, v0 & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v0 => //=. case if_expr0: (types_agree T_f32 v); last by rewrite if_expr0 in H; discriminate H. rewrite if_expr0 in H. simpl in H. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H. case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 4) => [tbs|]; rewrite if_expr3 in H. simpl in H. case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H. case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H. simpl in H. injection H as Hs Hf Hes. unfold upd_s_cmem in Hs. have Hs': (s_alls s' = s_alls s) by inversion Hs. rewrite Hs'. split; first by exact HSound_a. eapply write_cmembytes_preserves_isSound_b. instantiate (1 := s_cmems s). eauto. instantiate (1 := Some c). simpl. by rewrite if_expr2. subst s'. simpl. exact if_expr5. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by [].
            ** (* f64 *) case Hrev: (rev lconst) => [| v [| v0 ves'] ] //=; try (rewrite Hrev in H; by []). have Hlconst : lconst = rev [:: v, v0 & ves']. by rewrite -[lconst]revK Hrev => //=. rewrite Hrev in H. simpl in *. subst. destruct v0 => //=. case if_expr0: (types_agree T_f64 v); last by rewrite if_expr0 in H; discriminate H. rewrite if_expr0 in H. simpl in H. case if_expr1: (ptr_col p) => [c|]; rewrite if_expr1 in H. case if_expr2: (isAllocb c (s_alls s)); rewrite if_expr2 in H. case if_expr3: (read_colbytes (s_cmems s) (ptr_addr p) 8) => [tbs|]; rewrite if_expr3 in H. simpl in H. case if_expr4: (all (fun tb : tagged_byte => tb_color tb == Some c) tbs); rewrite if_expr4 in H. case if_expr5: (write_cmembytes (s_cmems s) (ptr_addr p) (bits v) (Some c) Numeric) => [cm'|]; rewrite if_expr5 in H. simpl in H. injection H as Hs Hf Hes. unfold upd_s_cmem in Hs. have Hs': (s_alls s' = s_alls s) by inversion Hs. rewrite Hs'. split; first by exact HSound_a. eapply write_cmembytes_preserves_isSound_b. instantiate (1 := s_cmems s). eauto. instantiate (1 := Some c). simpl. by rewrite if_expr2. subst s'. simpl. exact if_expr5. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by []. injection H as Hs Hf Hes. subst s'. unfold isSound. split; by [].



      - (** [AI_basic BI_colalloc] **)
        simpl; explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        + subst; split.
          * eexists.
            apply: r_eliml; first by apply v_to_e_is_const_list.
            eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)).
            --
              apply: rm_colalloc_success; eauto.
              instantiate (1 := next_free (s_alls s)).
              instantiate (2 := cmem_length (s_cmems s)).
              instantiate (1 := s0).
              apply: Alloc; eauto.
              ++ have compare_not_Gt_le (a b : nat) : Nat.compare a b <> Gt -> a <= b.
                 move=> H0; apply/leP; apply: (proj1 (PeanoNat.Nat.compare_le_iff a b)); exact H0.
                 move => a_off [Hle _].
                 unfold isfree; rewrite /cm_lookup.
                 have Hlen : List.length (cml_data (cmem_data (s_cmems s))) =
                            N.to_nat (cmem_length (s_cmems s)).
                 by rewrite /cmem_length /cm_length; destruct (s_cmems s); simpl;
                             rewrite Nnat.Nat2N.id.
                 have H_nge : List.length (cml_data (cmem_data (s_cmems s))) <= N.to_nat a_off.
                   rewrite Hlen.
                   have Hmono (x y : N) (Hle' : (x <= y)%N) : (N.to_nat x <= N.to_nat y).
                     move: x y Hle' => [|p] [|q] Hle' //=; first
                       [ exfalso; move: Hle' => /(proj1 (N.le_0_r (N.pos p))) Heq; discriminate Heq
                       | apply: compare_not_Gt_le; rewrite -N2Nat.inj_compare; exact Hle' ].
                   exact: Hmono Hle.
                 move: H_nge.
                 elim: (cml_data (cmem_data (s_cmems s))) (N.to_nat a_off) => [|x xs IH] [|m] //= Hlen'.
                 by apply: (IH m); move: Hlen' => /leP /(proj1 (Nat.succ_le_mono _ _)) /leP.
              ++ unfold isfreshcol; eauto.
              ++ have Hsize_eq : BinInt.Z.to_N (Wasm_int.Int32.unsigned s0) = Wasm_int.N_of_uint i32m s0.
                 by rewrite /Wasm_int.N_of_uint.
                 move: HExpect; rewrite /cmem_grow Hsize_eq.
                 set new_size := (cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N.
                 destruct (N.leb (new_size / page_size) page_limit) eqn:Hpage_leb.
                 ** have Hle : (new_size / page_size <= page_limit)%N
                      by case: (N.leb_spec0 (new_size / page_size) page_limit) Hpage_leb => [Htemp _ | _ Hfalse].
                    move => _; exact: Hle.
                 ** move => H_eq; discriminate.
              ++ have Hsize_eq' : BinInt.Z.to_N (Wasm_int.Int32.unsigned s0) = Wasm_int.N_of_uint i32m s0
                  by rewrite /Wasm_int.N_of_uint.
                 have Hmax : match cmem_max_opt (s_cmems s) with
                                | Some lim => ((cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N / page_size <= lim)%N
                                | None => True end.
                 have Hc := HExpect.
                 rewrite /cmem_grow Hsize_eq' in Hc; cbv zeta in Hc.
                 move: Hc; case: (N.leb ((cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N / page_size) page_limit) => [Hc|] ; last by [].
                 move: Hc; case: (cmem_max_opt (s_cmems s)) => [maxlim Hc | Hc]; [| by case: Hc].
                 case: (N.leb_spec0 ((cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N / page_size) maxlim) Hc => [Hle Hc | Hnle Hc];
                        [exact: Hle | by case: Hc].
                 case H_max_opt: (cmem_max_opt (s_cmems s)) => //=.
                 rewrite H_max_opt in Hmax.
                 exact Hmax.
              ++ f_equal. f_equal.
                 have Hsize_eq' : BinInt.Z.to_N (Wasm_int.Int32.unsigned s0) = Wasm_int.N_of_uint i32m s0
                 by rewrite /Wasm_int.N_of_uint.
                 have Hsize_eq_nat : N.to_nat (BinInt.Z.to_N (Wasm_int.Int32.unsigned s0)) = N.to_nat (Wasm_int.N_of_uint i32m s0)
                 by rewrite Hsize_eq'.
                 have Hlen : N.to_nat (cmem_length (s_cmems s)) =
                 size (cml_data (cmem_data (s_cmems s))).
                 rewrite /cmem_length /cm_length.
                 by destruct (s_cmems s); simpl; rewrite Nnat.Nat2N.id.
                 rewrite Hsize_eq_nat.
                 have Htake : take (N.to_nat (cmem_length (s_cmems s)))
                 (cml_data (cmem_data (s_cmems s))) =
                 cml_data (cmem_data (s_cmems s)).
                 apply: take_oversize. rewrite -Hlen. exact: leqnn.
                 have Hdrop' : drop (N.to_nat (cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0))
                 (cml_data (cmem_data (s_cmems s))) = [::].
                 apply: drop_oversize. rewrite N2Nat.inj_add Hlen.
                 exact: (leq_addr (N.to_nat (Wasm_int.N_of_uint i32m s0))
                 (size (cml_data (cmem_data (s_cmems s))))).
                 have Hfirstn_take: forall (A : Type) (n : nat) (l : list A), List.firstn n l = take n l.
                 { intros A n l0; revert n; induction l0; destruct n; simpl; try reflexivity. f_equal. apply IHl0. }
                 have Hskipn_drop: forall (A : Type) (n : nat) (l : list A), List.skipn n l = drop n l.
                 { intros A n l0; revert n; induction l0; destruct n; simpl; try reflexivity. apply IHl0. }
                 have Happ_nil: forall (A : Type) (l : list A), (l ++ [::])%list = l.
                 { intros A l0; induction l0; simpl; try reflexivity. f_equal; apply IHl0. }
                 rewrite Hfirstn_take Hskipn_drop.
                 rewrite Htake Hdrop'.
                 rewrite Happ_nil.
                 reflexivity.
            -- unfold lfilled, lfill; rewrite v_to_e_is_const_list => //=.
               instantiate (1 := les').
               instantiate (1 := [::]).
               eauto.
            -- unfold lfilled, lfill.
               rewrite v_to_e_is_const_list.
               eauto.
          * unfold wellFormedState.
            apply: calloc_sound; first exact HWF.
            apply: Alloc; eauto 10.
      (* The following points are a copy-paste of the previous `++` bullets. *)
      (* TODO: Find a less verbose way *)
            --
              have compare_not_Gt_le (a b : nat) : Nat.compare a b <> Gt -> a <= b.
              move=> H0; apply/leP; apply: (proj1 (PeanoNat.Nat.compare_le_iff a b)); exact H0.
              move => a_off [Hle _].
              unfold isfree; rewrite /cm_lookup.
              have Hlen : List.length (cml_data (cmem_data (s_cmems s))) =
                         N.to_nat (cmem_length (s_cmems s)).
              by rewrite /cmem_length /cm_length; destruct (s_cmems s); simpl;
                          rewrite Nnat.Nat2N.id.
              have H_nge : List.length (cml_data (cmem_data (s_cmems s))) <= N.to_nat a_off.
                rewrite Hlen.
                have Hmono (x y : N) (Hle' : (x <= y)%N) : (N.to_nat x <= N.to_nat y).
                  move: x y Hle' => [|p] [|q] Hle' //=; first
                    [ exfalso; move: Hle' => /(proj1 (N.le_0_r (N.pos p))) Heq; discriminate Heq
                    | apply: compare_not_Gt_le; rewrite -N2Nat.inj_compare; exact Hle' ].
                exact: Hmono Hle.
              move: H_nge.
              elim: (cml_data (cmem_data (s_cmems s))) (N.to_nat a_off) => [|x xs IH] [|m] //= Hlen'.
              by apply: (IH m); move: Hlen' => /leP /(proj1 (Nat.succ_le_mono _ _)) /leP.
            -- unfold isfreshcol; eauto.
            -- have Hsize_eq : BinInt.Z.to_N (Wasm_int.Int32.unsigned s0) = Wasm_int.N_of_uint i32m s0.
               by rewrite /Wasm_int.N_of_uint.
               move: HExpect; rewrite /cmem_grow Hsize_eq.
               set new_size := (cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N.
               destruct (N.leb (new_size / page_size) page_limit) eqn:Hpage_leb.
               ** have Hle : (new_size / page_size <= page_limit)%N
                    by case: (N.leb_spec0 (new_size / page_size) page_limit) Hpage_leb => [Htemp _ | _ Hfalse].
                  move => _; exact: Hle.
               ** move => H_eq; discriminate.
            -- have Hsize_eq' : BinInt.Z.to_N (Wasm_int.Int32.unsigned s0) = Wasm_int.N_of_uint i32m s0
                by rewrite /Wasm_int.N_of_uint.
               have Hmax : match cmem_max_opt (s_cmems s) with
                              | Some lim => ((cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N / page_size <= lim)%N
                              | None => True end.
               have Hc := HExpect.
               rewrite /cmem_grow Hsize_eq' in Hc; cbv zeta in Hc.
               move: Hc; case: (N.leb ((cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N / page_size) page_limit) => [Hc|] ; last by [].
               move: Hc; case: (cmem_max_opt (s_cmems s)) => [maxlim Hc | Hc]; [| by case: Hc].
               case: (N.leb_spec0 ((cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0)%N / page_size) maxlim) Hc => [Hle Hc | Hnle Hc];
                      [exact: Hle | by case: Hc].
               case H_max_opt: (cmem_max_opt (s_cmems s)) => //=.
               rewrite H_max_opt in Hmax.
               exact Hmax.
            --  
               have Hsize_eq' : BinInt.Z.to_N (Wasm_int.Int32.unsigned s0) = Wasm_int.N_of_uint i32m s0
               by rewrite /Wasm_int.N_of_uint.
               have Hsize_eq_nat : N.to_nat (BinInt.Z.to_N (Wasm_int.Int32.unsigned s0)) = N.to_nat (Wasm_int.N_of_uint i32m s0)
               by rewrite Hsize_eq'.
               have Hlen : N.to_nat (cmem_length (s_cmems s)) =
               size (cml_data (cmem_data (s_cmems s))).
               rewrite /cmem_length /cm_length.
               by destruct (s_cmems s); simpl; rewrite Nnat.Nat2N.id.
               rewrite Hsize_eq_nat.
               have Htake : take (N.to_nat (cmem_length (s_cmems s)))
               (cml_data (cmem_data (s_cmems s))) =
               cml_data (cmem_data (s_cmems s)).
               apply: take_oversize. rewrite -Hlen. exact: leqnn.
               have Hdrop' : drop (N.to_nat (cmem_length (s_cmems s) + Wasm_int.N_of_uint i32m s0))
               (cml_data (cmem_data (s_cmems s))) = [::].
               apply: drop_oversize. rewrite N2Nat.inj_add Hlen.
               exact: (leq_addr (N.to_nat (Wasm_int.N_of_uint i32m s0))
               (size (cml_data (cmem_data (s_cmems s))))).
               have Hfirstn_take: forall (A : Type) (n : nat) (l : list A), List.firstn n l = take n l.
               { intros A n l0; revert n; induction l0; destruct n; simpl; try reflexivity. f_equal. apply IHl0. }
               have Hskipn_drop: forall (A : Type) (n : nat) (l : list A), List.skipn n l = drop n l.
               { intros A n l0; revert n; induction l0; destruct n; simpl; try reflexivity. apply IHl0. }
               have Happ_nil: forall (A : Type) (l : list A), (l ++ [::])%list = l.
               { intros A l0; induction l0; simpl; try reflexivity. f_equal; apply IHl0. }
               rewrite Hfirstn_take Hskipn_drop.
               rewrite Htake Hdrop'.
               rewrite Happ_nil.
               reflexivity.
        + subst; split; last exact HWF.
          exists Eempty.
          eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list (rev l)) les')); last first.
          * unfold lfilled, lfill; rewrite v_to_e_is_const_list; eauto.
          * unfold lfilled, lfill; rewrite v_to_e_is_const_list => //=.
            instantiate (1 := [:: AI_basic (BI_const (NVAL_int32 s0)) ; AI_basic BI_colalloc]); eauto.
          * eapply rm_colalloc_failure. eauto. eauto.

      - (** [AI_basic BI_pointeradd] **)
        simpl; explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        split; last by subst.
        exists Eempty; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)); last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::_]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => //=.
        rewrite rev_cons_app.
        rewrite - v_to_e_cat.
        repeat rewrite - catA.
        instantiate (1 := [:: _ ;_;_]) => //=.
        eapply rm_silent, r_simple, rs_pointeradd_success => //=.
        split; last by subst.
        exists Eempty; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)); last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::_]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => //=.
        rewrite rev_cons_app.
        rewrite - v_to_e_cat.
        repeat rewrite - catA.
        instantiate (1 := [:: _ ;_;_]) => //=.
        eapply rm_silent, r_simple, rs_pointeradd_failure => //=.
      - (** [AI_basic BI_pointersub] **)
        simpl; explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        split; last by subst.
        exists Eempty; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)); last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::_]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => //=.
        rewrite rev_cons_app.
        rewrite - v_to_e_cat.
        repeat rewrite - catA.
        instantiate (1 := [:: _ ;_;_]) => //=.
        eapply rm_silent, r_simple, rs_pointersub_success => //=.
        split; last by subst.
        exists Eempty; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)); last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate (2 := [::_]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => //=.
        rewrite rev_cons_app.
        rewrite - v_to_e_cat.
        repeat rewrite - catA.
        instantiate (1 := [:: _ ;_;_]) => //=.
        eapply rm_silent, r_simple, rs_pointersub_failure => //=.
      - (** [AI_basic BI_pointerdiff] **)
        simpl; explode_and_simplify; pattern_match; auto_frame.
        case: (same_origin_andP p p0) => [Hso | Hnso].
        + split; last by subst.
          exists Eempty; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)); last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate (2 := [::_]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => //=.
          rewrite rev_cons_app.
          rewrite - v_to_e_cat.
          repeat rewrite - catA.
          instantiate (1 := [:: _ ;_;_]) => //=.
          apply: rm_silent; apply: r_simple.
          eapply rs_pointerdiff_success; first by rewrite /same_origin; symmetry; apply: Hso.
          reflexivity.
        + move: if_expr0 => /eqP Heq.
          have Hso : same_origin p p0 by rewrite /same_origin Heq.
          exfalso; exact: Hnso Hso.
        + move: if_expr0 => /eqP Heq.
          split; last by subst; auto.
          exists Eempty; eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)); last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate (2 := [::_]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => //=.
          rewrite rev_cons_app.
          rewrite - v_to_e_cat.
          repeat rewrite - catA.
          instantiate (1 := [:: _ ;_;_]) => //=.
          apply: rm_silent; apply: r_simple.
          apply: rs_pointerdiff_failure.
          by rewrite /same_origin.

      - (** [AI_basic BI_colfree] **)
        simpl; explode_and_simplify; pattern_match; auto_frame.
        + (* success *)
          subst; split.
          * exists (Ecfree v0).
            eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list (rev l)) les')); last first.
            -- unfold lfilled, lfill; rewrite v_to_e_is_const_list; eauto.
               instantiate (1:=[::]). eauto.
            -- unfold lfilled, lfill; rewrite v_to_e_is_const_list => //=;
               instantiate (1 := [:: AI_const (VAL_pointer p); AI_basic BI_colfree]); eauto.
            -- have Hfree : ptr_freeable p by move/andP: if_expr0 => [Hfree _].
               have Hallocb : isAllocb v0 (s_alls s) by move/andP: if_expr0 => [_ Hallocb].
               have Halloc' : isAlloc v0 (s_alls s).
                 by unfold isAlloc; apply/eqP; exact Hallocb.
               have Hcfree' : cfree (s_cmems s) (s_alls s) v0 (allocator_remove v0 (s_alls s)).
                 by apply: Free; [apply: Halloc' |].
               apply: rm_colfree_success; eauto; try apply/eqP; eauto.
          * have Hallocb : isAllocb v0 (s_alls s) by move/andP: if_expr0 => [_ Hallocb].
            have Halloc' : isAlloc v0 (s_alls s).
              by unfold isAlloc; apply/eqP; exact Hallocb.
            have Hcfree' : cfree (s_cmems s) (s_alls s) v0 (allocator_remove v0 (s_alls s)).
              by apply: Free; [apply: Halloc' |].
            unfold wellFormedState; apply: cfree_sound Hcfree'; apply HWF.
        + (* failure: color = None *)
          split; last by subst.
          exists Etrap.
          eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list (rev l)) les')); last first.
          * unfold lfilled, lfill.
            rewrite v_to_e_is_const_list.
            eauto.
          * unfold lfilled, lfill.
            rewrite v_to_e_is_const_list.
            instantiate (1 := [::_;_]) => //=.
          * subst; simpl.
            eapply rm_colfree_failure => //. right.
            move /andP in if_expr0.
            apply Classical_Prop.not_and_or in if_expr0.
            destruct if_expr0 as [Hnotfreeable | Hnotalloc].
            --
              left.
              apply /eqP.
              case H_free: (ptr_freeable p); by [].
            --
              right.
              intros.
              unfold isAlloc. unfold isAllocb in Hnotalloc.
              intro Heq.
              apply: Hnotalloc.
              rewrite option_expr in H0; injection H0 as ->.
              by move/eqP: Heq.
        + (* failure: find_and_remove = None *)
          split; last by subst.
          exists Etrap.
          eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list (rev l)) les')); last first.
          * unfold lfilled, lfill.
            rewrite v_to_e_is_const_list.
            eauto.
          * unfold lfilled, lfill.
            rewrite v_to_e_is_const_list.
            instantiate (1 := [::_;_]) => //=.
          * subst; simpl.
            eapply rm_colfree_failure => //.
            left.
            unfold is_null.
            apply /eqP. exact option_expr.

      - (** [AI_basic BI_isnull] **)
        simpl; explode_and_simplify; pattern_match; auto_frame.
        subst; split; last exact HWF.
        exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list (rev l)) les')); last first.
        * unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate (1 := [:: AI_basic (BI_const (NVAL_int32 (wasm_bool (is_null p))))]) => //=.
        * unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => //=.
          instantiate (1 := [:: AI_pointer p; AI_basic (BI_isnull)]) => //=.
        * case H_null: (is_null p).
          + apply rm_silent, r_simple, rs_isnull_true; by rewrite H_null.
          + apply rm_silent, r_simple, rs_isnull_false; by rewrite H_null.

      - (** [AI_basic BI_demote] **)
        simpl; explode_and_simplify; pattern_match; auto_frame.
        subst; split; last exact HWF.
        exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list (rev l)) les')); last first.
        * apply/lfilledP; apply: LfilledBase; apply: v_to_e_is_const_list.
        * unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          apply/eqP.
          instantiate (1:=v_to_e_list (rev [:: VAL_pointer p]) ++ [:: AI_basic BI_demote]); reflexivity.
        * apply rm_silent, r_simple, rs_demote => //=.

      - (** [AI_basic Current_memory] **)
        simpl. explode_and_simplify. pattern_match. auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ]) => //=.
        subst.
        apply: rm_silent. rewrite - nat_bin.
        eapply r_current_memory => //. exact HExpect. done.
      - (** [AI_basic Grow_memory] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst. rewrite - nat_bin.
        by apply rm_silent; apply: r_grow_memory_success => //=.
      - (** [AI_basic (Econst _)] **)
        by pattern_match.
      - (** [AI_basic Unop v u] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst.
        by repeat econstructor.
      - (** [AI_basic Binop v2 v1 b] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        rewrite rev_cons_app.
        rewrite - v_to_e_cat.
        repeat rewrite - catA.
        instantiate (1 := [:: _ ;_;_]) => //=.
        subst.
        by repeat econstructor.
        split; last by subst.
        exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        rewrite rev_cons_app.
        rewrite - v_to_e_cat.
        repeat rewrite - catA.
        instantiate (1 := [:: _ ;_;_]) => //=.
        subst.
        by repeat econstructor.
      - (** [AI_basic (Testop v t)] **)
        simpl. explode_and_simplify; destruct n; explode_and_simplify; pattern_match; auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst.
        by repeat econstructor.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst.
        by repeat econstructor.
      - (** [AI_basic (Relop v2 v1 r)] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        rewrite rev_cons_app.
        rewrite - v_to_e_cat.
        repeat rewrite - catA.
        instantiate (1 := [:: _ ;_;_]) => //=.
        subst.
        apply: rm_silent; apply: r_simple; exact: rs_relop.

      - (** [AI_basic (Cvtop v c v0 o)] **)
        simpl. explode_and_simplify; pattern_match; auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst.
        by repeat econstructor.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst.
        by repeat econstructor.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst. apply andb_prop in if_expr1 as [??].
        apply andb_prop in H0 as [??]. destruct o => //.
        econstructor. econstructor. apply rs_reinterpret.
        intros -> => //. intros -> => //. done.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ;_]) => //=.
        subst.
        by repeat econstructor.
      split; last by subst. exists Eempty.
      eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
      unfold lfilled, lfill.
      rewrite v_to_e_is_const_list.
      instantiate ( 2 := [:: _]) => //=.
      unfold lfilled, lfill.
      rewrite v_to_e_is_const_list => /=.
      instantiate (1 := [:: _ ;_]) => //=.
      subst.
      by repeat econstructor.
    }
    { (** [Const] **)
      by pattern_match.
    }
    { (** [Trap] **)
      by pattern_match.
    }
    { (** [Invoke] **)
      simpl. explode_and_simplify.
      - (** [Func_native] **)
        pattern_match; auto_frame.
        split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
         erewrite (take_drop (l := lconst)) at 1.
        rewrite - v_to_e_cat.
        rewrite - catA.
        rewrite (catA (v_to_e_list (drop _ _))).
        done.
        rewrite length_is_size.
        by apply leq_subr.

        subst.
        apply: rm_silent; apply: r_invoke_native => //=; eauto.
        simplify_lists. rewrite subKn => //.
        apply Compare_dec.leb_complete in if_expr0.  lias. }

    { (** [Label] **)
      simpl. explode_and_simplify; try (pattern_match; auto_frame).
      split; last by subst. exists Eempty. eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ]) => //=.

        econstructor. econstructor. 
           
        destruct es2 => //.
        destruct es2 => //. destruct a => //. 
        split; last by subst. exists Eempty.
         eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ]) => //=.
        subst.
        by repeat econstructor.

      + destruct run_step_with_fuel as [[s'' f''] r] eqn: EH.
        destruct r as [|nd es''| |es'' |] => //.
        * (** [RS_break] **)
          destruct nd => //. simpl. explode_and_simplify.
          destruct (Nat.leb n (length es'')) eqn:Hn => //.
          inversion H1 ; subst.
          split. exists Eempty.
          eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          2:{
            unfold lfilled, lfill.
            rewrite v_to_e_is_const_list => /=.
            instantiate (2 := [:: _ ]) => //=. }
            rewrite rev_cat.
          rewrite rev_rev.
          rewrite - v_to_e_cat.
          repeat rewrite - catA.
          rewrite (catA _ es1).
          done.
          
          apply Compare_dec.leb_complete in Hn.
          eapply reduce_label_break => // ; by eauto; lias.
          apply rs_break_wellfounded in EH as (-> & -> & _). done.

        * (** [RS_normal] **)
          inversion H1 ; subst.
          (* We actually want to keep the frame here for later use in lfilled.*)
          apply IHfuel in EH as [??]; try by lias.
          split; last done.
          destruct H0 as [me EH]. exists me. eapply rm_label.
          - by eauto.
          - apply/lfilledP.
            eapply LfilledRec; first by apply v_to_e_is_const_list.
            by apply lfilled0.
          - apply/lfilledP.
            rewrite -catA.
            apply LfilledRec; first by apply v_to_e_is_const_list.
            by apply lfilled0.
    }
    { (** [Local] **)
      simpl. explode_and_simplify; try (pattern_match; auto_frame).
      - split; last by subst.
        exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        instantiate ( 2 := [:: _]) => //=.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ]) => //=.
        subst.
        do 2 econstructor.
        apply rs_local_trap. 
      - split; last by subst. exists Eempty.
        eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list.
        done.
        unfold lfilled, lfill.
        rewrite v_to_e_is_const_list => /=.
        instantiate (1 := [:: _ ]) => //=.
        subst.
        do 2 econstructor.
        constructor.
        done. apply Nat.eqb_eq in if_expr2. done.
      - destruct run_step_with_fuel as [[s'' f''] r] eqn: EH.
        destruct r as [| |vs'''|es''| ] => //.
        * (** [RS_return] **)
          
          destruct (Nat.leb n (length vs''')) eqn:Hn => //.
          inversion H1 ; subst.
          split.
          exists Eempty.
          eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          2:{
            unfold lfilled, lfill.
            rewrite v_to_e_is_const_list => /=.
            instantiate (2 := [:: _ ]) => //=. }
          rewrite rev_cat.
          rewrite rev_rev.
          rewrite - v_to_e_cat.
          repeat rewrite - catA.
          done.
          
          apply Compare_dec.leb_complete in Hn.
          eapply reduce_label_return => //; by eauto; lias.
          apply rs_return_wellfounded in EH as (-> & -> & _) => //.
        * (** [RS_normal] **)
          inversion H1 ; subst. auto_frame.
          apply IHfuel in EH as [??]; try by lias.
          split.
          destruct H0 as [me EH]. exists me.
          eapply (rm_label (k := 0) (lh := LH_base (v_to_e_list _) _)) ; last first.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list.
          instantiate ( 2 := [:: _]) => //=.
          unfold lfilled, lfill.
          rewrite v_to_e_is_const_list => /=.
          instantiate (1 := [:: _ ]) => //=.
          
          by apply rm_local.
          done.
    }
    { by pattern_match. }
    Unshelve.
    all: by apply HPB.
Qed.

Theorem run_step_soundness : forall d s f es s' f' es',
    wellFormedState s ->
  run_step d (s, f, es) = (s', f', RS_normal es') ->
  (exists me, reduce s f es me s' f' es') /\ wellFormedState s'.
Proof.
  move=> d s f es s' f' es'.
  by apply: run_step_soundness_aux.
Qed.


End interpreter_func_sound.
