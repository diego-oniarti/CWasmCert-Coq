From mathcomp Require Import ssreflect ssrbool eqtype seq.
Require Import BinNat Lia.
From CWasm Require Import common.
From CWasm Require Import numerics bytes memory.
From stdpp Require Import gmap.

Inductive btag := Numeric | Pointer.

Scheme Equality for btag.
Definition btag_eqb (x y : btag) := is_left (btag_eq_dec x y).
Definition eqbtagP : Equality.axiom btag_eqb :=
  eq_dec_Equality_axiom btag_eq_dec.
Canonical Structure btag_eqMixin := EqMixin eqbtagP.
Canonical Structure btag_eqType := Eval hnf in EqType btag btag_eqMixin.

Record tagged_byte : Type := {
  tb_value : byte ;
  tb_color : option N ;
  tb_tag : btag ;
}.

Definition zerotbyte := {|
  tb_value := #00;
  tb_color := None;
  tb_tag   := Numeric;
|}.

Record colored_memory_list : Type := { (* segment_list equivalent *)
  cml_data : list tagged_byte ;    (* segl_data equivalent *)
}.

Record allocator : Type := {
  allocated: gmap N bool;
  next_free : N;
}.

Definition cmem_make v len := {|
  cml_data := List.repeat {|
    tb_value := v;
    tb_color := None;
    tb_tag   := Numeric;
  |} (N.to_nat len);
|}.

(* Define the rest as needed *)

Definition cm_lookup a cm :=
  List.nth_error cm.(cml_data) (N.to_nat a).

(* Allocation metadata recovered from the concrete colored memory.  The
   allocator stores only liveness; the Iris [wall] resource additionally
   records the first address and total number of bytes carrying a live color. *)
Definition tbc_is_color (c : N) (tb : tagged_byte) : bool :=
  match tb.(tb_color) with
  | Some c' => N.eqb c' c
  | None => false
  end.

Fixpoint count_color_list (c : N) (l : list tagged_byte) : N :=
  match l with
  | [::] => 0%N
  | tb :: l' =>
      if tbc_is_color c tb
      then (1 + count_color_list c l')%N
      else count_color_list c l'
  end.

Definition count_color (c : N) (cm : colored_memory_list) : N :=
  count_color_list c cm.(cml_data).

Fixpoint base_color_index (c : N) (l : list tagged_byte) : option nat :=
  match l with
  | [::] => None
  | tb :: l' =>
      if tbc_is_color c tb
      then Some 0
      else option_map S (base_color_index c l')
  end.

Definition base_color (c : N) (cm : colored_memory_list) : option N :=
  option_map N.of_nat (base_color_index c cm.(cml_data)).

Lemma tbc_is_color_eq (c : N) (tb : tagged_byte) :
  tbc_is_color c tb = true <-> tb.(tb_color) = Some c.
Proof.
  destruct tb as [v [c'|] tag] => /=.
  - rewrite N.eqb_eq. split.
    + by move=> ->.
    + move=> H. by inversion H.
  - split; by move=> H.
Qed.

Lemma base_color_index_lookup (c : N) (l : list tagged_byte) (i : nat) :
  base_color_index c l = Some i ->
  exists tb, List.nth_error l i = Some tb /\ tb.(tb_color) = Some c.
Proof.
  revert i.
  induction l as [|tb l IH]; intros i Hbase; first discriminate.
  simpl in Hbase.
  destruct (tbc_is_color c tb) eqn:Hcol.
  - inversion Hbase; subst i.
    exists tb. split; first done.
    by apply tbc_is_color_eq.
  - destruct (base_color_index c l) as [j|] eqn:Htail;
      simpl in Hbase; last discriminate.
    inversion Hbase; subst i.
    destruct (IH j Logic.eq_refl) as [tb' [Hlookup Hcolor]].
    exists tb'. split; done.
Qed.

Lemma base_color_lookup (c a : N) (cm : colored_memory_list) :
  base_color c cm = Some a ->
  exists tb, cm_lookup a cm = Some tb /\ tb.(tb_color) = Some c.
Proof.
  unfold base_color.
  destruct (base_color_index c cm.(cml_data)) as [i|] eqn:Hindex;
    simpl; intros Hbase; last discriminate.
  inversion Hbase; subst a.
  destruct (base_color_index_lookup c cm.(cml_data) i Hindex)
    as [tb [Hlookup Hcolor]].
  exists tb. split; last done.
  unfold cm_lookup. by rewrite Nat2N.id.
Qed.

Lemma base_color_index_none_iff_count_color_list_zero
    (c : N) (l : list tagged_byte) :
  base_color_index c l = None <-> count_color_list c l = 0%N.
Proof.
  induction l as [|tb l IH]; first done.
  simpl.
  destruct (tbc_is_color c tb) eqn:Hcolor.
  - split; first discriminate. move=> Hzero. lia.
  - split.
    + move=> Hnone.
      destruct (base_color_index c l) eqn:Hbase; first discriminate.
      by apply IH.
    + move=> Hzero.
      have Hbase : base_color_index c l = None.
      { apply IH. exact Hzero. }
      by rewrite Hbase.
Qed.

Lemma base_color_none_iff_count_color_zero
    (c : N) (cm : colored_memory_list) :
  base_color c cm = None <-> count_color c cm = 0%N.
Proof.
  unfold base_color, count_color.
  rewrite <- base_color_index_none_iff_count_color_list_zero.
  destruct (base_color_index c (cml_data cm)); done.
Qed.

Lemma tbc_is_color_ext (c : N) (tb1 tb2 : tagged_byte) :
  tb1.(tb_color) = tb2.(tb_color) ->
  tbc_is_color c tb1 = tbc_is_color c tb2.
Proof.
  destruct tb1 as [v1 col1 tag1], tb2 as [v2 col2 tag2] => /=.
  by move=> ->.
Qed.

Lemma count_color_list_ext (c : N) (l1 l2 : list tagged_byte) :
  map tb_color l1 = map tb_color l2 ->
  count_color_list c l1 = count_color_list c l2.
Proof.
  revert l2.
  induction l1 as [|tb1 l1 IH]; intros [|tb2 l2] Hcolors;
    try discriminate; first done.
  simpl in Hcolors. inversion Hcolors as [[Hhead Htail]].
  simpl. rewrite (tbc_is_color_ext c tb1 tb2 Hhead).
  by rewrite (IH l2 Htail).
Qed.

Lemma base_color_index_ext (c : N) (l1 l2 : list tagged_byte) :
  map tb_color l1 = map tb_color l2 ->
  base_color_index c l1 = base_color_index c l2.
Proof.
  revert l2.
  induction l1 as [|tb1 l1 IH]; intros [|tb2 l2] Hcolors;
    try discriminate; first done.
  simpl in Hcolors. inversion Hcolors as [[Hhead Htail]].
  simpl. rewrite (tbc_is_color_ext c tb1 tb2 Hhead).
  by rewrite (IH l2 Htail).
Qed.

Definition cmem_update (addr : N) (tb : tagged_byte) (cm : colored_memory_list) : option colored_memory_list :=
  if N.ltb addr (N.of_nat (List.length cm.(cml_data)))
  then Some {|
    cml_data :=
    take (N.to_nat addr) cm.(cml_data) ++
    [::tb] ++
    drop (N.to_nat addr+1) cm.(cml_data)
  |}
  else None.

Lemma cm_lookup_in_bounds (a : N) (cm : colored_memory_list) :
  (exists tb, cm_lookup a cm = Some tb) ->
  N.to_nat a < length cm.(cml_data).
Proof.
  move=> [tb Htb].
  unfold cm_lookup in Htb.
  have Hne : List.nth_error cm.(cml_data) (N.to_nat a) <> None.
  { intro Hne. rewrite Htb in Hne. done. }
  exact (proj1 (List.nth_error_Some (cml_data cm) (N.to_nat a)) Hne).
Qed.

Lemma cmem_update_in_bounds (a : N) (tb : tagged_byte) (cm : colored_memory_list) :
  N.to_nat a < length cm.(cml_data) ->
  exists cm',
    cmem_update a tb cm = Some cm' /\
    length cm'.(cml_data) = length cm.(cml_data).
Proof.
  move=> Hlt.
  unfold cmem_update.
  case Hbr: (a <? N.of_nat (length cm.(cml_data)))%N.
  - eexists; split; first by reflexivity.
    simpl.
    have Hcat : forall (T : Type) (l l' : list T), length (l ++ l') = length l + length l'.
    { move=> T. elim => [|x xs IH] => //=; move=> l'; by rewrite IH. }
    have Hfirstn : length (List.firstn (N.to_nat a) cm.(cml_data)) = N.to_nat a.
    { apply List.firstn_length_le. lia. }
    have Hskipn : length (List.skipn (N.to_nat a + 1) cm.(cml_data)) =
                  length cm.(cml_data) - (N.to_nat a + 1).
    { apply List.skipn_length. }
    rewrite !Hcat Hfirstn /= Hskipn. lia.
  - exfalso. apply N.ltb_ge in Hbr. lia.
Qed.

Definition cm_length cm :=
  N.of_nat (List.length cm.(cml_data)).

Definition cm_grow len_delta cm := {|
  cml_data := cm.(cml_data) ++
    List.repeat zerotbyte (N.to_nat len_delta)
|}.

(*
These definition would be closer to the one in the spec, but it is harder
to reason with. `fresh_col_none` lemma states that the new definition implies
this one.

Definition isfreshcol (c : N) (A : allocator) : Prop :=
  A.(allocated) !! c = None.

Definition isfreshcolb (c : N) (A : allocator) : bool :=
  A.(allocated) !! c == None.
 *)

Definition isfreshcol (c : N) (A : allocator) : Prop :=
  N.le (next_free A) c.
Definition isfreshcolb (c : N) (A : allocator) : bool :=
  N.leb (next_free A) c.

Definition isfreeb (addr : N) (M : colored_memory_list) (A : allocator) : bool :=
  match cm_lookup addr M with
  | None => true (* the byte is not in memory *)
  | Some tb =>
      match tb.(tb_color) with
      | None => true
      | Some c => A.(allocated) !! c == Some false
      end
  end.

Definition isfree (addr : N) (M : colored_memory_list) (A : allocator) : Prop :=
  match cm_lookup addr M with
  | None => True
  | Some tb =>
      match tb.(tb_color) with
      | None => True
      | Some c => A.(allocated) !! c == Some false
      end
  end.

Definition isAlloc (c : N) (A : allocator) : Prop :=
  A.(allocated) !! c = Some true.

Definition isAllocb (c : N) (A : allocator) : bool :=
  A.(allocated) !! c == Some true.

Lemma isAlloc_eq (c : N) (A : allocator):
  isAlloc c A <-> isAllocb c A.
Proof.
  unfold isAlloc, isAllocb.
  split; move /eqP; auto.
Qed.

Definition isAllocOpt (oc : option N) (A : allocator) :Prop :=
  match oc with
  | None => false
  | Some c => isAlloc c A
end.

Definition isAllocOptb (oc : option N) (A : allocator) : bool :=
  match oc with
  | None => false
  | Some c => isAllocb c A
end.

Lemma isAllocOpt_eq (c : option N) (A : allocator):
  isAllocOpt c A <-> isAllocOptb c A.
Proof.
  unfold isAllocOpt, isAllocOptb.
  destruct c.
  split; move /eqP; auto.
  auto.
Qed.


Definition isFreed (c : N) (A : allocator) : Prop :=
  A.(allocated) !! c = Some false.

(* no cols greater than next_free are allocated *)
Definition isSound_a (A : allocator) : Prop :=
  forall c, (c >= A.(next_free))%N -> A.(allocated) !! c = None.

(* all colors in memory are tracked by the allocator *)
Definition isSound_b (A : allocator) (cm: colored_memory_list) : Prop :=
  List.Forall (fun tb =>
    forall c, tb.(tb_color) = Some c -> A.(allocated) !! c <> None
  ) cm.(cml_data).

Definition isSound (A : allocator) (cm: colored_memory_list) : Prop :=
  isSound_a A /\ isSound_b A cm.

Definition allocated_eq_dec : forall v1 v2 : gmap N bool, {v1 = v2} + {v1 <> v2}.
Proof. intros m1 m2. solve_decision. Qed. 


Definition allocated_lookup (A : allocator) (c : N) : option bool := A.(allocated) !! c.

Lemma fresh_col_none (c:N) (A:allocator) :
  isSound_a A ->
  isfreshcol c A ->
  allocated A !! c = None.
Proof.
  move => Hsound Hfresh.
  unfold isSound_a in Hsound.
  unfold isfreshcol in Hfresh.
  apply Hsound.
  lias.
Qed.
