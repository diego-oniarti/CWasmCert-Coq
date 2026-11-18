(** Iris state interp predicates and lemmas **)

From mathcomp Require Import ssreflect ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From CWasm Require Import common operations datatypes datatypes_properties memory_list stdpp_aux colored_memory.
From stdpp Require Import gmap.

Definition create_table (len: N) : tableinst :=
  Build_tableinst (List.repeat None (N.to_nat len)) (Some len).

Definition create_memory (sz: N) (sz_lim: N) (init_b: byte) :=
  Build_memory (mem_make init_b sz) (Some sz_lim).

Global Instance inhabited_table : Inhabited tableinst := populate (create_table 0).

Global Instance inhabited_memory : Inhabited memory := populate (create_memory 0 0 #00).

Definition lookup_2d {T: Type} (l: list (list T)) (n: nat) (i: nat) : option T :=
  match (l !! n) with
  | Some x => x !! i
  | None => None
  end.

Definition flatten_list {T: Type} (l: list T) : list (N * T) :=
  imap (fun n x => (N.of_nat n, x)) l.

Lemma flatten_list_nodup {T: Type} (l: list T):
  NoDup (flatten_list l).
Proof.
  unfold flatten_list.
  apply nodup_imap_inj1.
  intros.
  inversion H.
  lia.
Qed.

Lemma flatten_list_lookup_Some {T: Type} (l: list T) (i: nat) x:
  l !! i = Some x ->
  (flatten_list l) !! i = Some (N.of_nat i, x).
Proof.
  move => H.
  unfold flatten_list.
  rewrite list_lookup_imap.
  by rewrite H.
Qed.

Definition gmap_of_list {T: Type} (l: list T) : gmap N T :=
  list_to_map (flatten_list l).

Fixpoint flatten_2d_list_i {T: Type} (l: list (list T)) (i: N) : list ((N*N) * T) :=
  match l with
  | [::] => [::]
  | l1 :: l' =>
    let lf := flatten_list l1 in
    (fmap (fun x => match x with | (n, b) => ((i, n), b) end) lf) ++ (flatten_2d_list_i l' (i+1))
  end.

Definition flatten_2d_list {T: Type} (l: list (list T)) : list ((N*N) * T) :=
  flatten_2d_list_i l 0.

Definition gmap_of_list_2d {T: Type} (l: list (list T)) : gmap (N*N) T :=
  list_to_map (flatten_2d_list l).

Definition gmap_of_list_2d_offset {T: Type} (l: list (list T)) (offset: N) : gmap (N*N) T :=
  list_to_map (fmap (fun '(i,j,x) => ((i+offset)%N, j, x)) (flatten_2d_list l)).

Definition memory_to_list (m: memory) : list byte :=
  (m.(mem_data)).(memory_list.ml_data).

Definition gmap_of_memory (l: list memory) : gmap (N*N) byte :=
  gmap_of_list_2d (fmap memory_to_list l).


Definition live_fold (a : allocator) (i : N) (tb : tagged_byte) (res : gmap N ()) : gmap N () :=
  match tb.(tb_color) with
  | Some c => if a.(allocated) !! c is Some true then <[i := ()]> res else res
  | None => res
  end.

Definition live_locations (cm : colored_memory_list) (a: allocator) : gmap N () :=
  map_fold (λ i tb res,
    match tb.(tb_color) with
    | Some c => if a.(allocated) !! c is Some true then <[i := ()]> res else res
    | None => res
    end) ∅ (gmap_of_list (cml_data cm)).

Lemma live_fold_lookup_ne (a : allocator) (j i : N) (x : tagged_byte) (r : gmap N ()) :
  j ≠ i ->
  (live_fold a j x r) !! i = r !! i.
Proof.
  move => Hneq.
  unfold live_fold.
  destruct (tb_color x) as [c|] eqn:Hc => /=.
  - destruct (a.(allocated) !! c) as [b|] eqn:Ha => /=.
    + destruct b => /=.
      * by rewrite lookup_insert_ne.
      * done.
    + done.
  - done.
Qed.

Lemma live_fold_commutes (a : allocator) (j1 j2 : N) (z1 z2 : tagged_byte) (y : gmap N ()) :
  j1 ≠ j2 ->
  live_fold a j1 z1 (live_fold a j2 z2 y) =
  live_fold a j2 z2 (live_fold a j1 z1 y).
Proof.
  move => Hneq.
  unfold live_fold.
  destruct (tb_color z1) as [c1|] eqn:Hc1 => /=.
  - destruct (tb_color z2) as [c2|] eqn:Hc2 => /=.
    + destruct (a.(allocated) !! c1) as [b1|] eqn:Ha1 => /=.
      * destruct (a.(allocated) !! c2) as [b2|] eqn:Ha2 => /=.
        -- destruct b1 => /=.
           ++ destruct b2 => /=.
              ** by rewrite insert_commute.
              ** done.
           ++ destruct b2 => /=.
              ** done.
              ** done.
        -- destruct b1 => /=.
           ++ done.
           ++ done.
      * destruct (a.(allocated) !! c2) as [b2|] eqn:Ha2 => /=.
        -- destruct b2 => /=.
           ++ done.
           ++ done.
        -- done.
    + done.
  - done.
Qed.

Lemma live_fold_live (a : allocator) (old : tagged_byte) (i : N) (r : gmap N ()) :
  r !! i = None ->
  live_fold a i old r !! i = Some () ->
  live_fold a i old r = <[i:=()]> r.
Proof.
  move => Hr_none Hsome.
  unfold live_fold in *.
  destruct (tb_color old) as [c|] eqn:Hc => /=.
  - destruct (a.(allocated) !! c) as [b|] eqn:Ha => /=.
    + destruct b => /=.
      * done.
      * by rewrite Hr_none in Hsome.
    + by rewrite Hr_none in Hsome.
  - by rewrite Hr_none in Hsome.
Qed.

Lemma map_fold_keys_subset (a : allocator) (m : gmap N tagged_byte) (i : N) :
  m !! i = None ->
  map_fold (live_fold a) ∅ m !! i = None.
Proof.
  move => Hnone.
  generalize i Hnone.
  apply (map_fold_ind (λ r m, ∀ j, m !! j = None → r !! j = None) (live_fold a) ∅).
  - move => j H. done.
  - move => i0 x0 m0 r Hfold_None IH j Hj.
    destruct (decide (j = i0)).
    + subst. rewrite lookup_insert in Hj. by inversion Hj.
    + rewrite lookup_insert_None in Hj. destruct Hj as [Hm Hij].
      rewrite (@live_fold_lookup_ne a i0 j x0 r Hij).
      apply IH. done.
Qed.



Definition gmap_of_cmem (cm : cmem) (a: allocator) : gmap N tagged_byte :=
  let locs := live_locations (cmem_data cm) a in
  filter (fun '(i,_) => locs !! i = Some ()) (gmap_of_list (cml_data (cmem_data cm))).


Definition alloc_base (cm : cmem) (c : N) : N :=
  match base_color c (cmem_data cm) with
  | Some b => b
  | None => 0
  end.

Definition alloc_size (cm : cmem) (c : N) : N :=
  count_color c (cmem_data cm).

Definition alloc_map_fold (cm : cmem) (c : N) (b : bool) (r : gmap N (N * N)) : gmap N (N * N) :=
  if b then <[ c := (alloc_base cm c, alloc_size cm c) ]> r else r.

Definition gmap_of_allocator (cm : cmem) (a: allocator) : gmap N (N * N) :=
  map_fold (alloc_map_fold cm) ∅ a.(allocated).

(** The color-status map mirrors every concrete allocator entry.  Live
    entries use an exclusive fragment that is consumed by free; retired
    entries use a persistent discarded fragment. *)
Definition gmap_of_retired (a : allocator) : gmap N bool :=
  a.(allocated).

Lemma gmap_of_retired_lookup_false (a : allocator) (c : N) :
  a.(allocated) !! c = Some false ->
  gmap_of_retired a !! c = Some false.
Proof.
  done.
Qed.

Lemma gmap_of_retired_lookup (a : allocator) (c : N) (b : bool) :
  gmap_of_retired a !! c = Some b <->
  a.(allocated) !! c = Some b.
Proof.
  done.
Qed.

Lemma gmap_of_retired_insert_true (a : allocator) (c : N) :
  a.(allocated) !! c = None ->
  gmap_of_retired (allocator_insert c a) =
  <[c := true]> (gmap_of_retired a).
Proof.
  done.
Qed.

Lemma gmap_of_retired_remove (a : allocator) (c : N) :
  gmap_of_retired (allocator_remove c a) =
  <[c := false]> (gmap_of_retired a).
Proof.
  done.
Qed.

Lemma alloc_map_fold_lookup_ne (cm : cmem) (j i : N) (bv : bool) (r : gmap N (N * N)) :
  j <> i ->
  alloc_map_fold cm j bv r !! i = r !! i.
Proof.
  move => Hneq. unfold alloc_map_fold.
  destruct bv => //=.
  by rewrite lookup_insert_ne.
Qed.

Lemma alloc_map_fold_lookup_self (cm : cmem) (i : N) (bv : bool) (r : gmap N (N * N)) :
  bv = true ->
  alloc_map_fold cm i bv r !! i = Some (alloc_base cm i, alloc_size cm i).
Proof.
  move => Hbv. unfold alloc_map_fold.
  rewrite Hbv.
  rewrite lookup_insert.
  reflexivity.
Qed.

(* A color that is allocated (true) is mapped to its (base, count) metadata. *)
Lemma gmap_of_allocator_lookup_true (cm : cmem) (a : allocator) (c : N) :
  a.(allocated) !! c = Some true ->
  gmap_of_allocator cm a !! c = Some (alloc_base cm c, alloc_size cm c).
Proof.
  move => Hc.
  unfold gmap_of_allocator.
  generalize c Hc.
  apply (map_fold_ind
    (fun r m => forall c : N, m !! c = Some true ->
      r !! c = Some (alloc_base cm c, alloc_size cm c))
    (alloc_map_fold cm) ∅).
  - move => c0 Hb. rewrite lookup_empty in Hb. by inversion Hb.
  - move => i x m r Hmnone IH c0 Hc'.
    destruct (decide (c0 = i)).
    + subst.
      have Hx : x = true.
      { rewrite lookup_insert in Hc'. by inversion Hc'. }
      rewrite Hx /alloc_map_fold lookup_insert.
      reflexivity.
    + rewrite (alloc_map_fold_lookup_ne cm x r (sym_not_eq n)).
      apply IH.
      rewrite (lookup_insert_ne m i c0 x (sym_not_eq n)) in Hc'.
      exact Hc'.
Qed.

(* A color that is not allocated (true) is not present in the metadata map. *)
Lemma gmap_of_allocator_lookup_not_true (cm : cmem) (a : allocator) (c : N) :
  a.(allocated) !! c <> Some true ->
  gmap_of_allocator cm a !! c = None.
Proof.
  move => Hc.
  unfold gmap_of_allocator.
  generalize c Hc.
  apply (map_fold_ind
    (fun r m => forall c : N, m !! c <> Some true ->
      r !! c = None)
    (alloc_map_fold cm) ∅).
  - move => c0 _. by rewrite lookup_empty.
  - move => i x m r Hmnone IH c0 Hc'.
    destruct (decide (c0 = i)).
    + subst.
      destruct x => //=.
      * exfalso. apply Hc'. rewrite lookup_insert. done.
      * apply IH. rewrite Hmnone. by inversion 1.
    + rewrite (alloc_map_fold_lookup_ne cm x r (sym_not_eq n)).
      apply IH.
      rewrite (lookup_insert_ne m i c0 x (sym_not_eq n)) in Hc'.
      exact Hc'.
Qed.

(* A color that is None in the allocator is not present in the metadata map. *)
Lemma gmap_of_allocator_lookup_None (cm : cmem) (a : allocator) (c : N) :
  a.(allocated) !! c = None ->
  gmap_of_allocator cm a !! c = None.
Proof.
  move => Hc. apply gmap_of_allocator_lookup_not_true.
  rewrite Hc. by inversion 1.
Qed.

(* Converse: an entry with (base,size) metadata implies the color is allocated. *)
Lemma gmap_of_allocator_elem_lookup (cm : cmem) (a : allocator) (c base size : N) :
  gmap_of_allocator cm a !! c = Some (base, size) ->
  a.(allocated) !! c = Some true.
Proof.
  move => Hc.
  destruct (a.(allocated) !! c) as [b|] eqn:Ha.
  - destruct b; first done.
    exfalso.
    have Hb : a.(allocated) !! c <> Some true by rewrite Ha.
    rewrite (gmap_of_allocator_lookup_not_true cm Hb) in Hc.
    by inversion Hc.
  - exfalso.
    rewrite (gmap_of_allocator_lookup_None cm Ha) in Hc.
    by inversion Hc.
Qed.

Definition table_to_list (tab: tableinst) : list funcelem :=
  tab.(table_data).

Definition gmap_of_table (l: list tableinst) : gmap (N*N) funcelem :=
  gmap_of_list_2d (fmap table_to_list l).

Lemma gmap_of_list_lookup {T: Type} (l: list T) n:
  (gmap_of_list l) !! n = l !! (N.to_nat n).
Proof with resolve_finmap.
  unfold gmap_of_list, flatten_list.
  remember_lookup.
  destruct lookup_res...
  - rewrite Nat2N.id. by rewrite Helem.
  - apply Nat2N.inj in H1. subst. rewrite Helem in Helem0. by inversion Helem0.
  - apply nodup_imap_inj1. move => n1 n2 t1 t2 Heq.
    inversion Heq.
    by apply Nat2N.inj in H1.
  - destruct (l !! (N.to_nat n)) eqn: Hlookup => //.
    exfalso. apply H2. clear H2.
    apply elem_of_list_fmap.
    exists (n, t). split => //.
    apply elem_of_lookup_imap.
    exists (N.to_nat n), t. split => //.
    by rewrite N2Nat.id.
Qed.

(* Commutativity between gmap_of_list and list_insert. *)
Lemma gmap_of_list_insert {T: Type} (l: list T) (v: T) n:
  N.to_nat n < length l ->
  gmap_of_list (<[N.to_nat n:=v]> l) = <[n:=v]> (gmap_of_list l).
Proof with resolve_finmap.
  move => Hlen.
  apply map_eq. move => i.
  rewrite gmap_of_list_lookup.
  destruct (decide (i = n)).
  - subst. rewrite lookup_insert. by rewrite list_lookup_insert.
  - rewrite lookup_insert_ne => //.
    rewrite list_lookup_insert_ne => //.
    + by rewrite gmap_of_list_lookup.
    + move => HContra. apply n0.
      by apply N2Nat.inj.    
Qed.

Lemma gmap_of_list_append {T: Type} (l: list T) (v: T):
  gmap_of_list (l ++ [:: v]) = <[N.of_nat (length l) := v]> (gmap_of_list l).
Proof with resolve_finmap.
  apply map_eq. move => i.
  repeat rewrite gmap_of_list_lookup.
  destruct (decide (i = N.of_nat (length l))).
  - subst. rewrite Nat2N.id. rewrite lookup_insert.
    rewrite lookup_app_r => //=.
    by replace (length l - length l) with 0; last lia.
  - remember_lookup. symmetry.
    destruct lookup_res...
    + assert (N.to_nat i < length l) as HLength.
      { apply lookup_lt_Some in Hlookup.
        rewrite app_length in Hlookup. simpl in Hlookup.
        lia. }
      rewrite lookup_insert_ne => //.
      rewrite gmap_of_list_lookup.
      by rewrite lookup_app_l in Hlookup => //.
    + apply lookup_ge_None in Hlookup.
      rewrite lookup_insert_ne => //.
      rewrite gmap_of_list_lookup.
      apply lookup_ge_None.
      rewrite app_length in Hlookup; simpl in Hlookup.
      lia.
Qed.

Lemma flatten_2d_list_i_acc_shift_spec {T: Type} (l: list (list T)) (acc: N):
  flatten_2d_list_i l (acc+1) = (fun x => match x with
                                            | (n, i, t) => ((n+1)%N, i, t)
                                            end) <$>
                                                 (flatten_2d_list_i l acc).
Proof.
  move: l acc.
  induction l => //.
  move => acc.
  simpl.
  rewrite fmap_app.
  rewrite IHl.
  f_equal.
  clear IHl.
  apply list_eq.
  move => i.
  repeat rewrite list_lookup_fmap.
  destruct (a !! i) eqn:Hl.
  - apply flatten_list_lookup_Some in Hl.
    by rewrite Hl.
  - assert (flatten_list a !! i = None) as H; last by rewrite H.
    unfold flatten_list.
    apply lookup_ge_None.
    apply lookup_ge_None in Hl.
    by rewrite imap_length.
Qed.
  
Lemma flatten_2d_list_i_acc_shift {T: Type} (l: list (list T)) n i t acc:
  (N.of_nat (n+1), i, t) ∈ flatten_2d_list_i l (acc+1) <->
  (N.of_nat n, i, t) ∈ flatten_2d_list_i l acc.
Proof.
  rewrite flatten_2d_list_i_acc_shift_spec.
  rewrite elem_of_list_fmap.
  split.
  - move => [[[n' i'] t'] [Heq Helem]].
    inversion Heq; subst; clear Heq.
    replace (N.of_nat n) with n' => //.
    lia.
  - move => Helem.
    exists (N.of_nat n, i, t).
    split => //.
    repeat f_equal.
    lia.
Qed.
    
Lemma flatten_2d_list_i_acc_domain1 {T: Type} (l: list (list T)) n i t acc:
  (n, i, t) ∈ flatten_2d_list_i l acc ->
  (n >= acc)%N.
Proof.
  rewrite - (N2Nat.id n).
  remember (N.to_nat n) as n0. clear Heqn0 n.
  rewrite - (N2Nat.id acc).
  remember (N.to_nat acc) as acc0. clear Heqacc0 acc.
  move: n0 i t acc0.
  induction n0 => //; move => i t acc0 Helem.
  - destruct acc0 => //.
    replace (N.of_nat (S acc0)) with (N.of_nat acc0 + 1)%N in Helem; last lia.
    rewrite flatten_2d_list_i_acc_shift_spec in Helem.
    resolve_finmap.
    destruct x.
    destruct p.
    inversion Heq.
    lia.
  - destruct acc0 => //.
    replace (N.of_nat (S acc0)) with (N.of_nat acc0 + 1)%N in Helem; last lia.
    assert (N.of_nat n0 >= N.of_nat acc0)%N; last lia.
    eapply IHn0.
    apply flatten_2d_list_i_acc_shift.
    replace (n0+1) with (S n0) => //.
    lia.
Qed.
    
Lemma flatten_2d_list_lookup {T: Type} (l: list (list T)) n i t:
  (n, i, t) ∈ flatten_2d_list l <->
  match l !! (N.to_nat n) with
  | Some l' => l' !! (N.to_nat i)
  | None => None
  end = Some t.
Proof.
  unfold flatten_2d_list.
  split.
  - move: n i t.
    induction l => //=; move => n i t Helem.
    + by apply elem_of_nil in Helem.
    + destruct (N.to_nat n) eqn: Hn => //=.
      * unfold flatten_list in Helem.
        assert (n = 0%N); first lia. subst; clear Hn.
        apply elem_of_app in Helem.
        destruct Helem as [Helem|Helem]; resolve_finmap; subst.
        -- inversion Heq. subst.
          by rewrite Nat2N.id.
        -- apply elem_of_list_lookup_2 in Helem0.
          apply flatten_2d_list_i_acc_domain1 in Helem0.
          lia.
      * assert (n = N.of_nat (S n0)); first lia; subst; clear Hn.
        rewrite - (Nat2N.id n0).
        apply IHl.
        apply flatten_2d_list_i_acc_shift.
        apply elem_of_app in Helem.
        destruct Helem as [Helem|Helem]; resolve_finmap; subst; first by destruct x.
        apply elem_of_list_lookup_2 in Helem0.
        replace (N.of_nat (n0+1)) with (N.pos (Pos.of_succ_nat n0)) => //.
        lia.
  - move: n i t.
    induction l => //=; move => n i t Hl.
    destruct (N.to_nat n) eqn:Hn => //=.
    + assert (n=0%N); first lia. subst; clear Hn.
      simpl in Hl.
      apply elem_of_app; left.
      apply elem_of_list_fmap.
      exists (i, t).
      split => //.
      unfold flatten_list.
      apply elem_of_lookup_imap.
      exists (N.to_nat i), t.
      split => //.
      f_equal.
      lia.
    + simpl in Hl.
      replace n with (N.of_nat (n0+1)); last lia.
      rewrite - (Nat2N.id n0) in Hl.
      apply IHl in Hl.
      unfold flatten_list.
      apply flatten_2d_list_i_acc_shift in Hl.
      apply elem_of_app; by right.
Qed.
      
Lemma flatten_2d_list_inj12 {T: Type} (l: list (list T)) x1 x2 p t1 t2:
  flatten_2d_list l !! x1 = Some (p, t1) ->
  flatten_2d_list l !! x2 = Some (p, t2) ->
  t1 = t2.
Proof.
  destruct p as [n i].
  move => Hl1 Hl2.
  apply elem_of_list_lookup_2 in Hl1, Hl2.
  apply flatten_2d_list_lookup in Hl1, Hl2.
  rewrite Hl1 in Hl2.
  by inversion Hl2.
Qed.
  
Lemma flatten_2d_list_nodup {T: Type} (l: list (list T)):
  NoDup (flatten_2d_list l).
Proof.
  unfold flatten_2d_list.
  induction l => //=.
  - by apply NoDup_nil.
  - apply NoDup_app => //=.
    split.
    + apply NoDup_fmap.
      * move => x1 x2 Heq.
        destruct x1, x2.
        by inversion Heq.
      * by apply flatten_list_nodup.
    + split.
      * move => [[n i] t] Helem.
        resolve_finmap.
        destruct x.
        inversion Heq; subst; clear Heq.
        move => HContra.
        apply flatten_2d_list_i_acc_domain1 in HContra.
        lia.
      * rewrite flatten_2d_list_i_acc_shift_spec => //.
        apply NoDup_fmap => //.
        move => x1 x2 Heq.
        destruct x1, x2.
        destruct p, p0.
        inversion Heq; subst; clear Heq.
        repeat f_equal.
        lia.
Qed.

Lemma gmap_of_list_2d_offset_lookup {T: Type} (l: list (list T)) (off: N) n i:
  (n >= off)%N ->
  (gmap_of_list_2d_offset l off) !! (n, i) =
  match l !! (N.to_nat (n-off)) with
  | Some l' => l' !! (N.to_nat i)
  | None => None
  end.
Proof with resolve_finmap.
  move => Hge.
  unfold gmap_of_list_2d_offset.
  remember_lookup.
  destruct lookup_res...
  - symmetry. apply flatten_2d_list_lookup.
    apply elem_of_list_lookup.
    destruct x as [[j k] x].
    inversion Heq; subst; clear Heq.
    exists x0.
    rewrite Helem0.
    repeat f_equal.
    by lias.
  - destruct x0 as [[j0 k0] x0].
    destruct x1 as [[j1 k1] x1].
    destruct x as [j k].
    inversion Heq0; subst; clear Heq0.
    inversion Heq; subst; clear Heq.
    eapply flatten_2d_list_inj12 => //.
    replace j1 with j0 => //.
    by lias.
  - fold (flatten_2d_list l).
    apply NoDup_fmap; last by apply flatten_2d_list_nodup.
    unfold Inj.
    intros.
    destruct x as [[j0 k0] x0].
    destruct y as [[j1 k1] x1].
    inversion H0; subst; clear H0.
    repeat f_equal.
    by lias.
  - destruct (l !! (N.to_nat (n-off))) eqn: Hlookup => //.
    destruct (l0 !! (N.to_nat i)) eqn: Hlookup2 => //.
    exfalso. apply H2. clear H2.
    apply elem_of_list_fmap.
    exists (n, i, t). split => //.
    apply elem_of_list_fmap.
    exists ((n-off)%N, i, t).
    split => //; first ((repeat f_equal); by lias).
    apply flatten_2d_list_lookup.
    by rewrite Hlookup Hlookup2.
Qed.

Lemma gmap_of_list_2d_offset_lookup_None {T: Type} (l: list (list T)) (off: N) n i:
  (n < off)%N ->
  (gmap_of_list_2d_offset l off) !! (n, i) = None.
Proof with resolve_finmap.
  move => Hge.
  unfold gmap_of_list_2d_offset.
  remember_lookup.
  destruct lookup_res...
  - destruct x as [[j k] x].
    inversion Heq; subst; clear Heq.
    by lias.
  - destruct x0 as [[j0 k0] x0].
    destruct x1 as [[j1 k1] x1].
    destruct x as [j k].
    inversion Heq0; subst; clear Heq0.
    inversion Heq; subst; clear Heq.
    eapply flatten_2d_list_inj12 => //.
    replace j1 with j0 => //.
    by lias.
  - fold (flatten_2d_list l).
    apply NoDup_fmap; last by apply flatten_2d_list_nodup.
    unfold Inj.
    intros.
    destruct x as [[j0 k0] x0].
    destruct y as [[j1 k1] x1].
    inversion H0; subst; clear H0.
    repeat f_equal.
    by lias.
Qed.

Lemma gmap_of_list_2d_offset_0 {T: Type} (l: list (list T)):
  gmap_of_list_2d l = gmap_of_list_2d_offset l 0.
Proof.
  unfold gmap_of_list_2d, gmap_of_list_2d_offset.
  f_equal.
  apply list_eq.
  move => i.
  rewrite list_lookup_fmap.
  destruct (flatten_2d_list l !! i) eqn: Hl => //=.
  destruct p as [[? ?] ?].
  repeat f_equal.
  by lias.
Qed.

Lemma gmap_of_list_2d_lookup {T: Type} (l: list (list T)) n i:
  (gmap_of_list_2d l) !! (n, i) = match l !! (N.to_nat n) with
                                  | Some l' => l' !! (N.to_nat i)
                                  | None => None
                                  end.
Proof.
  rewrite gmap_of_list_2d_offset_0.
  rewrite gmap_of_list_2d_offset_lookup; last by lias.
  by rewrite N.sub_0_r.
Qed.

Definition new_2d_gmap_at_n {T: Type} (n: N) (l: list T) : gmap (N*N) T :=
  list_to_map (imap (fun i x => ((n, N.of_nat i), x)) l).

Lemma new_2d_gmap_at_n_lookup {T: Type} n (i: N) (l: list T):
  (new_2d_gmap_at_n n l) !! (n, i) = l !! (N.to_nat i).
Proof.
  unfold new_2d_gmap_at_n.
  destruct (l !! N.to_nat i) eqn:Hlookup.
  { apply elem_of_list_to_map; resolve_finmap.
    - apply Nat2N.inj in H0. subst.
      rewrite Helem0 in Helem.
      by inversion Helem.
    - apply nodup_imap_inj1.
      move => n1 n2 t1 t2 Heq.
      inversion Heq.
      by apply Nat2N.inj in H0.
    - apply elem_of_lookup_imap.
      exists (N.to_nat i), t.
      split => //.
      + repeat f_equal.
        lia.
  }
  { apply not_elem_of_list_to_map.
    move => H.
    resolve_finmap; subst => /=.
    simpl in Heq.
    inversion Heq; subst; clear Heq.
    rewrite Nat2N.id in Hlookup.
    by rewrite Hlookup in Helem0.
  }
Qed.

Lemma new_2d_gmap_at_n_lookup_None {T: Type} n m (i: N) (l: list T):
  n <> m ->
  new_2d_gmap_at_n n l !! (m, i) = None.
Proof.
  move => Hneq.
  unfold new_2d_gmap_at_n.
  apply not_elem_of_list_to_map. move => HContra. resolve_finmap. subst => //=.
  by inversion Heq.
Qed.

Lemma gmap_of_list_2d_offset_append_disjoint {T: Type} l (l': list T) (off k: N):
  (k >= N.of_nat (length l) + off)%N ->
  new_2d_gmap_at_n k l' ##ₘ gmap_of_list_2d_offset l off. 
Proof.
  move => Hge.
  apply map_disjoint_spec.
  move => [n i] f1 f2 H1 H2.
  unfold new_2d_gmap_at_n in H1.
  resolve_finmap.
  - rewrite gmap_of_list_2d_offset_lookup in H2; last by lias.
    rewrite Nat2N.id in H2.
    destruct (l !! N.to_nat (k-off)) eqn: HContra => //. clear H2.
    assert (Some l0 = None) => //.
    rewrite - HContra. clear HContra.
    apply lookup_ge_None.
    lia.
  - apply Nat2N.inj in H1. subst.
    rewrite Helem0 in Helem.
    by inversion Helem.
  - apply nodup_imap_inj1.
    move => n1 n2 t1 t2 Heq.
    inversion Heq.
    by apply Nat2N.inj in H1.
Qed.
  
Lemma gmap_of_list_2d_append_disjoint {T: Type} l (l': list T):
  new_2d_gmap_at_n (N.of_nat (length l)) l' ##ₘ gmap_of_list_2d l.
Proof.
  rewrite gmap_of_list_2d_offset_0.
  apply gmap_of_list_2d_offset_append_disjoint.
  by lias.
Qed.

Lemma gmap_of_list_2d_offset_append_general {T: Type} l (x: list T) (off: N):
  gmap_of_list_2d_offset (l ++ [::x]) off =
  new_2d_gmap_at_n (N.of_nat (length l) + off) x ∪ gmap_of_list_2d_offset l off.
Proof.
  apply map_eq.
  move => [n i].
  destruct (decide (n>=off)%N); last first.
  { rewrite gmap_of_list_2d_offset_lookup_None; last by lias.
    rewrite lookup_union_r.
    - rewrite gmap_of_list_2d_offset_lookup_None => //.
      by lias.
    - rewrite new_2d_gmap_at_n_lookup_None => //.
      by lias.
  }
  remember_lookup; rewrite gmap_of_list_2d_offset_lookup in Hlookup; last by lias.
  destruct lookup_res => //=.
  - destruct (_ !! N.to_nat (n-off)) eqn:Hlookup2 => //.
    assert (N.to_nat (n-off) <= length l) as Hlen.
    {
      apply lookup_lt_Some in Hlookup2.
      rewrite app_length in Hlookup2.
      simpl in Hlookup2.
      lia.
    }
    destruct (decide (N.to_nat (n-off) = length l)) => //.
    + rewrite e in Hlookup2.
      rewrite lookup_app_r in Hlookup2; last lia.
      replace (length l - length l) with 0 in Hlookup2; last lia.
      simpl in Hlookup2.
      inversion Hlookup2; subst; clear Hlookup2.
      assert (N.to_nat i < length l0).
      { by apply lookup_lt_Some in Hlookup. }
      symmetry.
      apply lookup_union_Some_l.
      rewrite - e.
      rewrite N2Nat.id.
      rewrite N.sub_add; last by lias.
      by rewrite new_2d_gmap_at_n_lookup.
    + assert (N.to_nat (n-off) < length l) as Hlenlt; first lia.
      symmetry.
      apply lookup_union_Some_r; first by apply gmap_of_list_2d_offset_append_disjoint; lias.
      rewrite gmap_of_list_2d_offset_lookup => //.
      rewrite lookup_app_l in Hlookup2; last lia.
      by rewrite Hlookup2.
  - destruct (_ !! N.to_nat (n-off)) eqn:Hlookup2 => //.
    + assert (N.to_nat (n-off) <= length l) as Hlen.
      {
        apply lookup_lt_Some in Hlookup2.
        rewrite app_length in Hlookup2.
        simpl in Hlookup2.
        lia.
      }
      destruct (decide (N.to_nat (n-off) = length l)) => //.
      * rewrite e in Hlookup2.
        rewrite lookup_app_r in Hlookup2; last lia.
        replace (length l - length l) with 0 in Hlookup2; last lia.
        simpl in Hlookup2.
        inversion Hlookup2; subst; clear Hlookup2.
        assert (N.to_nat i >= length l0).
        { by apply lookup_ge_None in Hlookup. }
        symmetry.
        apply lookup_union_None.
        split.
        -- rewrite - e.
           rewrite N2Nat.id.
           rewrite N.sub_add; last by lias.
          by rewrite new_2d_gmap_at_n_lookup.
        -- rewrite gmap_of_list_2d_offset_lookup => //.
          assert (N.to_nat (n-off) ≥ length l) as Hlen2; first lia.
          apply lookup_ge_None in Hlen2.
          by rewrite Hlen2.
      * symmetry.
        apply lookup_union_None.
        split.
        -- rewrite new_2d_gmap_at_n_lookup_None => //.
          lia.
        -- rewrite gmap_of_list_2d_offset_lookup => //.
           rewrite lookup_app_l in Hlookup2; last lia.
           by rewrite Hlookup2.
    + clear Hlookup.
      destruct (_ !! N.to_nat (n-off)) eqn:Hlookup => //.
      clear Hlookup2.
      apply lookup_ge_None in Hlookup.
      rewrite app_length in Hlookup.
      simpl in Hlookup.
      symmetry.
      apply lookup_union_None.
      split.
      * apply new_2d_gmap_at_n_lookup_None => //.
        lia.
      * rewrite gmap_of_list_2d_offset_lookup => //.
        assert (N.to_nat (n-off) >= length l) as Hlen; first lia.
        apply lookup_ge_None in Hlen.
        by rewrite Hlen.
Qed.

Lemma gmap_of_list_2d_append_general {T: Type} l (x: list T):
  gmap_of_list_2d (l ++ [::x]) =
  new_2d_gmap_at_n (N.of_nat (length l)) x ∪ gmap_of_list_2d l.
Proof.
  repeat rewrite gmap_of_list_2d_offset_0.
  rewrite gmap_of_list_2d_offset_append_general.
  by rewrite N.add_0_r.
Qed.  
  
Lemma gmap_of_list_2d_append {T: Type} l len (x: T):
  gmap_of_list_2d (l ++ [::repeat x len]) =
  new_2d_gmap_at_n (N.of_nat (length l)) (repeat x len) ∪ gmap_of_list_2d l.
Proof.
  by apply gmap_of_list_2d_append_general.
Qed.

Lemma gmap_of_list_2d_insert {T: Type} n i (x: T) (l: list (list T)) (t: list T):
  l !! (N.to_nat n) = Some t ->
  N.to_nat i < length t ->
  <[(n, i) := x]> (gmap_of_list_2d l) = gmap_of_list_2d (<[N.to_nat n := (<[N.to_nat i := x]> t)]> l).
Proof.
  move => HLookup HLen.
  apply map_eq.
  move => [m j].
  unfold gmap_of_table.
  remember_lookup. rewrite gmap_of_list_2d_lookup. symmetry.
  destruct (decide ((n, i) = (m,j))).
  - inversion e; subst; clear e.
    repeat rewrite Nat2N.id.
    rewrite lookup_insert.
    rewrite list_lookup_insert => /=; last by apply lookup_lt_Some in HLookup.
    by rewrite list_lookup_insert.
  - rewrite lookup_insert_ne in Hlookup => //.
    destruct (decide (n = m)); subst.
    + rewrite list_lookup_insert => /=; last by apply lookup_lt_Some in HLookup.
      destruct (decide (i = j)).
      * exfalso. apply n0. subst.
        by repeat rewrite N2Nat.id.
      * rewrite list_lookup_insert_ne; last lia.
        rewrite gmap_of_list_2d_lookup.
        by rewrite HLookup.
    + rewrite list_lookup_insert_ne; last lia.
      by rewrite gmap_of_list_2d_lookup.
Qed.

Lemma gmap_of_table_append_disjoint l len:
  new_2d_gmap_at_n (N.of_nat (length l)) (repeat None len) ##ₘ gmap_of_table l.
Proof.
  unfold gmap_of_table.
  replace (length l) with (length (table_to_list <$> l)); first by apply gmap_of_list_2d_append_disjoint.
  by rewrite fmap_length.
Qed.

Lemma gmap_of_memory_append_disjoint l len init_b:
  new_2d_gmap_at_n (N.of_nat (length l)) (repeat init_b len) ##ₘ gmap_of_memory l.
Proof.
  unfold gmap_of_memory.
  replace (length l) with (length (memory_to_list <$> l)); first by apply gmap_of_list_2d_append_disjoint.
  by rewrite fmap_length.
Qed.

Lemma gmap_of_table_append l len:
  gmap_of_table (l ++ [::create_table len]) =
  new_2d_gmap_at_n (N.of_nat (length l)) (repeat None (N.to_nat len)) ∪ gmap_of_table l.
Proof.
  unfold gmap_of_table, create_table.
  replace (length l) with (length (table_to_list <$> l)); last by rewrite fmap_length.
  rewrite fmap_app => /=.
  by apply gmap_of_list_2d_append.
Qed.

Lemma gmap_of_memory_append l sz sz_lim init_b:
  gmap_of_memory (l ++ [::create_memory sz sz_lim init_b]) =
  new_2d_gmap_at_n (N.of_nat (length l)) (repeat init_b (N.to_nat sz)) ∪ gmap_of_memory l.
Proof.
  unfold gmap_of_memory, create_memory.
  replace (length l) with (length (memory_to_list <$> l)); last by rewrite fmap_length.
  rewrite fmap_app => /=.
  by apply gmap_of_list_2d_append.
Qed.

Lemma gmap_of_table_insert n i x l t:
  l !! (N.to_nat n) = Some t ->
  N.to_nat i < length t.(table_data) ->
  <[(n, i) := x]> (gmap_of_table l) = gmap_of_table (<[N.to_nat n := {| table_data := (<[N.to_nat i := x]> t.(table_data)); table_max_opt := t.(table_max_opt) |}]> l).
Proof.
  unfold gmap_of_table.
  move => HLookup HLen.
  rewrite list_fmap_insert => /=.
  apply gmap_of_list_2d_insert; last lia.
  rewrite list_lookup_fmap.
  by rewrite HLookup.
Qed.

Lemma insert_take_drop {T: Type} i (l: list T) (x: T):
  i < length l ->
  <[i := x]> l = seq.take i l ++ [::x] ++ seq.drop (i+1) l.  
Proof.
  move: i. induction l => //=; move => i HLen; first lia.
  destruct i => //=; f_equal.
  - by rewrite drop0.
  - assert (i < length l) as H; first lia.
    apply IHl in H.
    by rewrite H.
Qed.
    
Lemma gmap_of_memory_insert n i x l m md':
  l !! (N.to_nat n) = Some m ->
  N.to_nat i < length m.(mem_data).(memory_list.ml_data) ->
  memory_list.mem_update i x m.(mem_data) = Some md' ->
  <[(n, i) := x]> (gmap_of_memory l) = gmap_of_memory (<[ N.to_nat n := {| mem_data := md'; mem_max_opt := m.(mem_max_opt)|} ]> l).
Proof.
  unfold gmap_of_memory.
  move => HLookup HLen Hmemupd.
  unfold memory_list.mem_update in Hmemupd.
  destruct (i <? _)%N eqn:HiLen => //; clear HiLen.
  inversion Hmemupd; subst; clear Hmemupd => /=.
  rewrite list_fmap_insert => /=.
  erewrite gmap_of_list_2d_insert; eauto.
  + repeat f_equal.
    unfold memory_to_list => /=.
    by apply insert_take_drop.
  + rewrite list_lookup_fmap.
    by rewrite HLookup.
Qed.

Lemma gmap_of_memory_insert_block (n: nat) (m mem :memory) l:
  l !! n = Some mem ->
  length m.(mem_data).(ml_data) >= length mem.(mem_data).(ml_data) ->
  gmap_of_memory (<[n := m]> l) = (new_2d_gmap_at_n (N.of_nat n) m.(mem_data).(ml_data)) ∪ (gmap_of_memory l).
Proof.
  move => Hmem Hlen.
  unfold gmap_of_memory.
  apply map_eq.
  move => [i j].
  rewrite gmap_of_list_2d_lookup lookup_union gmap_of_list_2d_lookup.
  unfold union_with, option_union_with.
  unfold memory_to_list => /=.
  repeat rewrite list_lookup_fmap.
  destruct (decide (n = N.to_nat i)) eqn:Hn; subst.
  - clear Hn.
    rewrite N2Nat.id new_2d_gmap_at_n_lookup list_lookup_insert => /=; last by eapply lookup_lt_Some.
    rewrite Hmem.
    destruct (ml_data (mem_data m) !! N.to_nat j) eqn:Hlookup => //=.
    + by repeat destruct (_ !! _) => //=.
    + destruct (ml_data (mem_data mem) !! (N.to_nat j)) eqn:Hlookup2 => //=.
      apply lookup_ge_None in Hlookup.
      apply lookup_lt_Some in Hlookup2.
      lia.
  - rewrite list_lookup_insert_ne => //.
    rewrite new_2d_gmap_at_n_lookup_None; last by lias.
    by repeat destruct (_ !! _) => //=.
Qed.


Lemma take_seq_take {A} n (l: list A) : take n l = seq.take n l.
Proof.
  generalize dependent n. induction l => //=. destruct n => //.
  destruct n => //=. by rewrite IHl.
Qed.

Lemma drop_seq_drop {A} n (l: list A) : drop n l = seq.drop n l.
Proof.
  generalize dependent n. induction l => //=. destruct n => //.
  destruct n => //=. 
Qed. 


Lemma update_preserve_insert (cm : colored_memory_list) (a: allocator) (x: tagged_byte) i :
  live_locations cm a !! i = Some () ->
  isAllocOpt (tb_color x) a ->
  live_locations cm a = live_locations {| cml_data := <[N.to_nat i:=x]> (cml_data cm) |} a.
Proof.
  intros Hilive Hallocx.
  unfold live_locations.
  fold (live_fold a).
  unfold live_locations in Hilive.
  fold (live_fold a) in Hilive.
  unfold isAllocOpt, isAlloc in Hallocx.
  cbn in Hallocx.
  destruct (tb_color x) eqn:Hcx; last by done.
  destruct (gmap_of_list (cml_data cm) !! i) as [old|] eqn:Hold.
  - assert (Hold_len : cml_data cm !! N.to_nat i = Some old).
    { rewrite <- gmap_of_list_lookup. exact Hold. }
    apply lookup_lt_Some in Hold_len.
    cbn [cml_data].
    erewrite gmap_of_list_insert; last exact Hold_len.
    rewrite (map_fold_delete_L (live_fold a) ∅ i old (gmap_of_list (cml_data cm))); last first.
    { exact Hold. }
    { intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes. }
    rewrite (map_fold_delete_L (live_fold a) ∅ i x (<[i:=x]> (gmap_of_list (cml_data cm)))); last first.
    { rewrite lookup_insert. done. }
    { intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes. }
    rewrite delete_insert_delete.
    rewrite (map_fold_delete_L (live_fold a) ∅ i old (gmap_of_list (cml_data cm))) in Hilive; last first.
    { exact Hold. }
    { intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes. }
    set r := map_fold (live_fold a) ∅ (delete i (gmap_of_list (cml_data cm))).
    change (live_fold a i old r !! i = Some ()) in Hilive.
    have Hr_none : r !! i = None.
    { subst r. apply (@map_fold_keys_subset a (delete i (gmap_of_list (cml_data cm))) i).
      rewrite lookup_delete. done. }
    have Hx_live : live_fold a i x r = <[i:=()]> r.
    { unfold live_fold. rewrite Hcx. simpl. rewrite Hallocx. simpl. done. }
    rewrite (@live_fold_live a old i r Hr_none Hilive).
    rewrite Hx_live.
    done.
  - rewrite (@map_fold_keys_subset a (gmap_of_list (cml_data cm)) i Hold) in Hilive.
    discriminate.
Qed.




Lemma gmap_of_cmem_insert (cm : cmem) (i : N) (x : tagged_byte) a cm' :
  N.to_nat i < length (cml_data (cmem_data cm)) ->
  colored_memory.cmem_update i x (cmem_data cm) = Some (cmem_data cm') ->
  isAllocOpt (tb_color x) a ->
  live_locations (cmem_data cm) a !! i = Some () ->
  <[i := x]> (gmap_of_cmem cm a) = gmap_of_cmem cm' a.
Proof.
  unfold gmap_of_cmem.
  move => HLen Hmemupd Hallocx Hlive.
  unfold colored_memory.cmem_update in Hmemupd.
  destruct (i <? _)%N eqn:HiLen => //; clear HiLen.
  inversion Hmemupd; subst; clear Hmemupd => /=.
  rewrite - map_filter_insert_True => //.
  erewrite <- gmap_of_list_insert; last done.
  rewrite take_seq_take drop_seq_drop.

  rewrite separate1.
  erewrite app_assoc.
  rewrite app_assoc_reverse.
  rewrite - insert_take_drop; last by exact HLen.

  rewrite - update_preserve_insert.
  reflexivity.
  exact Hlive.
  exact Hallocx.
Qed.


Lemma mem_length_divisible (m: memory_list):
  ml_valid m ->
  ((N.div (mem_length m) page_size) * page_size)%N = mem_length m.
Proof.
  move => Hmlvalid.
  unfold ml_valid in Hmlvalid.
  rewrite N.mul_comm.
  specialize (N.div_mod (mem_length m) page_size) as Hdm.
  rewrite Hmlvalid in Hdm.
  rewrite N.add_0_r in Hdm.
  symmetry.
  by apply Hdm.
Qed.

Lemma mem_grow_data m n m':
  operations.mem_grow m n = Some m' ->
  m'.(mem_data).(memory_list.ml_data) = (m.(mem_data).(memory_list.ml_data) ++ (repeat m.(mem_data).(ml_init) (N.to_nat (n*page_size))))%SEQ.
Proof.
  unfold operations.mem_grow, mem_size, mem_length, memory_list.mem_length, memory_list.mem_grow => //=.
  destruct (_ <=? page_limit)%N => //=.
  move => H.
  destruct (mem_max_opt m) in H => //=.
  - destruct (_ <=? n0)%N => //=.
    by inversion H; subst.
  - by inversion H.
Qed.

Lemma mem_grow_length m n m':
  operations.mem_grow m n = Some m' ->
  operations.mem_length m' = (operations.mem_length m + n * page_size)%N.
Proof.
  move => H.
  apply mem_grow_data in H.
  unfold mem_size, operations.mem_length, memory_list.mem_length.
  rewrite H.
  rewrite app_length repeat_length.
  by rewrite Nat2N.inj_add N2Nat.id.
Qed.

Definition mem_grow_appendix (m:memory) (mn: nat) (n:N) : gmap (N*N) byte := list_to_map (imap (fun i x => ((N.of_nat mn, ((N.of_nat i) + (mem_size m) * page_size)%N), x)) (repeat (ml_init (mem_data m)) (N.to_nat (n * page_size)))).

Lemma mem_grow_appendix_disjoint m n mn m' mems:
  mn < length mems ->
  mems !! mn = Some m ->
  ml_valid m.(mem_data) ->
  operations.mem_grow m n = Some m' ->
  (mem_grow_appendix m mn n) ##ₘ gmap_of_memory mems.
Proof.
  move => HLen Hmem Hmlvalid Hmemgrow.
  unfold mem_grow_appendix.
  apply map_disjoint_spec.
  move => [i j] x y Hlookup1 Hlookup2.
  unfold gmap_of_memory in Hlookup2.
  resolve_finmap.
  - rewrite gmap_of_list_2d_lookup in Hlookup2.
    rewrite Nat2N.id in Hlookup2.
    destruct ((_ <$> _) !! mn) eqn: HContra => //.
    rewrite list_lookup_fmap in HContra.
    rewrite Hmem in HContra.
    simpl in HContra.
    inversion HContra; subst; clear HContra.
    assert (Some y = None) => //.
    rewrite - Hlookup2. clear Hlookup2.
    apply lookup_ge_None.
    unfold memory_to_list, mem_size.
    rewrite mem_length_divisible => //.
    unfold mem_length, memory_list.mem_length.
    lia.
  - assert (x1 = x3); first lia.
    subst.
    rewrite Helem0 in Helem.
    by inversion Helem.
  - apply nodup_imap_inj1.
    move => n1 n2 t1 t2 Heq.
    inversion Heq.
    lia.
Qed.

Set Bullet Behavior "Strict Subproofs".

Lemma gmap_of_memory_grow m n m' mn mems:
  mn < length mems ->
  mems !! mn = Some m ->
  ml_valid m.(mem_data) ->
  operations.mem_grow m n = Some m' ->
  (mem_grow_appendix m mn n) ∪ gmap_of_memory mems =
  gmap_of_memory (<[ mn := m' ]> mems).
Proof.
  move => Hlen Hmemlookup Hmlvalid Hmemgrow.
  remember (mem_grow_length Hmemgrow) as Hmemlen; clear HeqHmemlen.
  unfold operations.mem_length, mem_length in Hmemlen.
  remember (mem_grow_data Hmemgrow) as Hmemgrowdata; clear HeqHmemgrowdata.
  apply map_eq.
  move => [i j].
  unfold gmap_of_memory, mem_grow_appendix.
  rewrite gmap_of_list_2d_lookup.
  rewrite list_lookup_fmap.
  unfold memory_to_list.
  destruct (decide (N.to_nat i = mn)); subst.
  - rewrite list_lookup_insert => //=.
    destruct (decide (N.to_nat j < length m.(mem_data).(memory_list.ml_data))).
    + destruct (_ !! N.to_nat j) eqn:Hl; last by apply lookup_ge_None in Hl; lia.
      apply lookup_union_Some_r; first by eapply mem_grow_appendix_disjoint.
      rewrite gmap_of_list_2d_lookup.
      rewrite list_lookup_fmap.
      rewrite Hmemlookup => //=.
      rewrite Hmemgrowdata in Hl.
      by rewrite lookup_app_l in Hl.
    + destruct (decide (N.to_nat j < length m'.(mem_data).(memory_list.ml_data))).
      * destruct (_ !! N.to_nat j) eqn:Hl; last by apply lookup_ge_None in Hl; lia.
        apply lookup_union_Some_l.
        apply elem_of_list_to_map; resolve_finmap.
        -- assert (x0 = x2); first lia.
           subst.
           by rewrite Helem0 in Helem; inversion Helem.
        -- apply nodup_imap_inj1.
           move => n1 n2 t1 t2 Heq.
           inversion Heq.
           lia.
        -- apply elem_of_lookup_imap.
           rewrite N2Nat.id.
           exists (N.to_nat (j - (mem_size m * page_size))%N), b.
           split.
           ++ repeat f_equal.
              rewrite N2Nat.id.
              unfold mem_size.
              rewrite mem_length_divisible => //.
              unfold mem_length, memory_list.mem_length.
              lia.
           ++ rewrite Hmemgrowdata in Hl.
              rewrite lookup_app_r in Hl; last lia.
              rewrite - Hl.
              f_equal.
              unfold mem_size.
              rewrite mem_length_divisible => //.
              unfold mem_length, memory_list.mem_length.
              lia.
      * destruct (_ !! N.to_nat j) eqn:Hl2; first by apply lookup_lt_Some in Hl2; lia.
        apply lookup_union_None.
        split.
        -- apply not_elem_of_list_to_map.
           move => HContra.
           resolve_finmap; subst => //=.
           inversion Heq; subst; clear Heq.
           apply lookup_lt_Some in Helem0.
           rewrite repeat_length in Helem0.
           apply n1.
           rewrite N2Nat.inj_add Nat2N.id.
           apply N2Nat.inj_iff in Hmemlen.
           rewrite N2Nat.inj_add in Hmemlen.
           repeat rewrite Nat2N.id in Hmemlen.
           rewrite Hmemlen.
           unfold mem_size.
           rewrite mem_length_divisible => //.
           unfold mem_length, memory_list.mem_length.
           lia.
        -- rewrite gmap_of_list_2d_lookup list_lookup_fmap Hmemlookup => /=.
           apply lookup_ge_None.
           lia.
  - rewrite list_lookup_insert_ne => //=.
    rewrite lookup_union_r.
    + rewrite gmap_of_list_2d_lookup.
      by rewrite list_lookup_fmap.
    + apply not_elem_of_list_to_map.
      move => HContra.
      resolve_finmap; subst => //=.
      inversion Heq; subst; clear Heq.
      lia.
Qed.

Lemma gmap_of_list_append_big {T: Type} (l1 l2: list T):
  let gtmap := (list_to_map (imap (fun i x => (N.of_nat (length l1 + i), x)) l2)) in
  gmap_of_list (l1 ++ l2) = (gmap_of_list l1) ∪ gtmap /\
  map_disjoint (gmap_of_list l1) gtmap.
Proof.
  move: l1.
  induction l2 using List.rev_ind; move => l1 => /=.
  - rewrite cats0.
    split.
    + by rewrite map_union_empty.
    + by apply map_disjoint_empty_r.
  - rewrite catA.
    rewrite gmap_of_list_append.
    specialize (IHl2 l1).
    destruct IHl2 as [Hgmap Hdisj].
    rewrite Hgmap.
    split.
    + rewrite imap_app.
      rewrite list_to_map_app => /=.
      rewrite -> insert_union_singleton_r.
      * rewrite map_union_assoc.
        f_equal.
        rewrite insert_empty.
        f_equal.
        rewrite app_length.
        by lias.
      * rewrite lookup_union_r.
        { rewrite <- not_elem_of_list_to_map.
          move => Hcontra.
          rewrite -> elem_of_list_fmap in Hcontra.
          destruct Hcontra as [[n t] [Heq Helem]].
          apply elem_of_lookup_imap in Helem.
          destruct Helem as [i [y [Heq2 Hlookup]]].
          simpl in Heq.
          inversion Heq2; subst; clear Heq2.
          apply lookup_lt_Some in Hlookup.
          apply Nat2N.inj in H0.
          rewrite app_length in H0.
          by lias.
        }
        { rewrite gmap_of_list_lookup.
          rewrite Nat2N.id.
          apply lookup_ge_None.
          rewrite app_length.
          by lias.
        }
    + apply map_disjoint_spec.
      move => i y1 y2 Hl1 Hl2.
      rewrite gmap_of_list_lookup in Hl1.
      apply elem_of_list_to_map in Hl2.
      * rewrite -> elem_of_lookup_imap in Hl2.
        destruct Hl2 as [j [y [Heq Hl]]].
        inversion Heq; subst; clear Heq.
        apply lookup_lt_Some in Hl1.
        apply lookup_lt_Some in Hl.
        rewrite Nat2N.id in Hl1.
        by lias.
      *  apply NoDup_fmap_fst.
         { move => x0 y3 z4 Hin1 Hin2.
           apply elem_of_lookup_imap in Hin1 as [i1 [z1 [Heq3 Hl3]]].
           apply elem_of_lookup_imap in Hin2 as [i2 [z2 [Heq4 Hl4]]].
           inversion Heq3; subst; clear Heq3.
           inversion Heq4; subst; clear Heq4.
           replace i2 with i1 in Hl4; last by lias.
           rewrite Hl3 in Hl4.
           by inversion Hl4.
         }
         {
           apply nodup_imap_inj1.
           move => n1 n2 t1 t2 H2.
           inversion H2; subst; clear H2.
           by lias.
         }
Qed.

Lemma gmap_of_list_2d_append_big {T: Type} (l1 l2: list (list T)):
  let gtmap := gmap_of_list_2d_offset l2 (N.of_nat (length l1)) in
  gmap_of_list_2d (l1 ++ l2) = (gmap_of_list_2d l1) ∪ gtmap /\
  map_disjoint (gmap_of_list_2d l1) gtmap.
Proof.
  repeat rewrite gmap_of_list_2d_offset_0.
  move: l1.
  induction l2 using List.rev_ind; move => l1 => /=.
  - rewrite cats0.
    split.
    + by rewrite map_union_empty.
    + by apply map_disjoint_empty_r.
  - rewrite catA.
    repeat rewrite gmap_of_list_2d_offset_append_general.
    specialize (IHl2 l1).
    destruct IHl2 as [Hgmap Hdisj].
    rewrite Hgmap.
    assert (map_disjoint (new_2d_gmap_at_n (N.of_nat (length l1 + length l2)) x) (gmap_of_list_2d_offset l1 0)) as Hndisj.
    {
      apply map_disjoint_spec.
      move => [i j] x1 x2 Hl1 Hl2.
      rewrite gmap_of_list_2d_offset_lookup in Hl2; last lia.
      rewrite N.sub_0_r in Hl2.
      destruct (l1 !! (N.to_nat i)) eqn:Hli => //.
      apply lookup_lt_Some in Hli.
      rewrite new_2d_gmap_at_n_lookup_None in Hl1 => //.
      by lias.
    }
    split.
    + repeat rewrite map_union_assoc.
      rewrite N.add_0_r.
      rewrite <- Nat2N.inj_add.
      rewrite app_length.
      replace (length l2 + length l1) with (length l1 + length l2); last lia.
      by rewrite (map_union_comm (new_2d_gmap_at_n (N.of_nat (length l1 + length l2)) x) (gmap_of_list_2d_offset l1 0)) => //.
    + apply map_disjoint_union_r.
      split => //.
      apply map_disjoint_spec.
      move => [i j] x1 x2 Hl1 Hl2.
      rewrite gmap_of_list_2d_offset_lookup in Hl1; last lia.
      rewrite N.sub_0_r in Hl1.
      destruct (l1 !! (N.to_nat i)) eqn:Hli => //.
      apply lookup_lt_Some in Hli.
      rewrite new_2d_gmap_at_n_lookup_None in Hl2 => //.
      by lias.
Qed.

Lemma no_memory_no_memories ws n :
  s_mems ws !! n = None ->
  forall k, gmap_of_memory (s_mems ws) !! (N.of_nat n, k) = None.
Proof.
  intros.
  unfold gmap_of_memory.
  rewrite gmap_of_list_2d_lookup => //=.
  rewrite Nat2N.id. 
  rewrite list_lookup_fmap H => //=.
Qed.

Ltac simplify_lookup :=
  repeat match goal with
  | H: gmap_of_table _ !! _ = _ |- _ =>
       unfold gmap_of_table in H
  | H: gmap_of_memory _ !! _ = _ |- _ =>
       unfold gmap_of_memory in H
  | H: gmap_of_list_2d _ !! _ = _ |- _ =>
       rewrite gmap_of_list_2d_lookup in H
  | H: gmap_of_list_lookup _ !! _ = _ |- _ =>
       rewrite gmap_of_list_lookup in H
  | H: match ?term with
       | Some _ => _
       | None => None
       end = Some _ |- _ =>
       let Heq := fresh "Heq" in
       destruct term eqn: Heq => //
  | H: context C [N.of_nat (N.to_nat _)] |- _ =>
    rewrite N2Nat.id in H
  | H: context C [N.to_nat (N.of_nat _)] |- _ =>
    rewrite Nat2N.id in H
  | _ => resolve_finmap
end.
