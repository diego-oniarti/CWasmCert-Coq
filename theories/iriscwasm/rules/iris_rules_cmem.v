From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Import Coq.Program.Equality.
From CWasm.iriscwasm.language Require Import iris_wp_def.
From CWasm.iriscwasm.rules Require Export iris_rules_resources iris_rules_structural.
From Coq Require Import BinNat.
From CWasm Require Import opsem operations datatypes properties color_ptr list_extra.
From CWasm.iriscwasm.helpers Require Import iris_properties iris_reduce_properties.
From CWasm.iriscwasm.language.iris Require Import iris.
From CWasm.iriscwasm.helpers Require Import iris_wasm_determ.

Import uPred.
Close Scope byte_scope.

Set Default Proof Using "Type".

Section iris_rules_cmem.
Context `{HPB : PointerBytes}.
Let reducible := @reducible wasm_lang.

Context `{!wasmG Σ}.
Set Bullet Behavior "Strict Subproofs".

(* ================================================================= *)
(* Bridging lemma: allocator ghost element → isAlloc                   *)
(* ================================================================= *)

Lemma allocated_implies_is_in_allocator (a : allocator) (cm : cmem) (i base size : N) :
  ghost_map_auth allGName 1 (gmap_of_allocator cm a) -∗
  ghost_map_elem allGName i (DfracOwn 1) (base, size) -∗
  ⌜a.(allocated) !! i = Some true⌝.
Proof.
  iIntros "Ha Hi".
  iDestruct (ghost_map_lookup with "Ha Hi") as "%H".
  iPureIntro. exact (gmap_of_allocator_elem_lookup H).
Qed.

Lemma allocator_insert_wall (cm : cmem) (A : allocator) (c base size : N) :
  A.(allocated) !! c = None ->
  ghost_map_auth allGName 1 (gmap_of_allocator cm A) ==∗
  ghost_map_auth allGName 1 (<[ c := (base, size) ]> (gmap_of_allocator cm A)) ∗ wall c base size.
Proof.
  intros Hnone.
  iIntros "Hall".
  iMod (ghost_map_insert c (base, size) with "Hall") as "[Hall Hwall]";
    first by apply: gmap_of_allocator_lookup_None.
  iModIntro.
  rewrite /wall.
  iFrame.
Qed.

Lemma allocator_remove_wall (cm : cmem) (A : allocator) (c base size : N) :
  ghost_map_auth allGName 1 (gmap_of_allocator cm A) -∗ wall c base size ==∗
  ghost_map_auth allGName 1 (delete c (gmap_of_allocator cm A)).
Proof.
  iIntros "Hall Hwall".
  iMod (ghost_map_delete with "Hall Hwall") as "Hall".
  iModIntro.
  rewrite /wall.
  iExact "Hall".
Qed.

Lemma gmap_of_allocator_cmem_ext (cm1 cm2 : cmem) (A : allocator) :
  (forall c, alloc_base cm1 c = alloc_base cm2 c) ->
  (forall c, alloc_size cm1 c = alloc_size cm2 c) ->
  gmap_of_allocator cm1 A = gmap_of_allocator cm2 A.
Proof.
  move=> Hbase Hsize.
  apply map_eq. move=> c.
  destruct (A.(allocated) !! c) as [b|] eqn:Halloc.
  - destruct b.
    + rewrite (@gmap_of_allocator_lookup_true cm1 A c Halloc).
      rewrite (@gmap_of_allocator_lookup_true cm2 A c Halloc).
      by rewrite Hbase Hsize.
    + have Hnot : A.(allocated) !! c <> Some true.
      { rewrite Halloc. discriminate. }
      rewrite (@gmap_of_allocator_lookup_not_true cm1 A c Hnot).
      by rewrite (@gmap_of_allocator_lookup_not_true cm2 A c Hnot).
  - rewrite (@gmap_of_allocator_lookup_None cm1 A c Halloc).
    by rewrite (@gmap_of_allocator_lookup_None cm2 A c Halloc).
Qed.

Lemma gmap_of_allocator_write_preserved (cm cm' : cmem) (A : allocator)
    (addr : N) (bs : bytes) (col : option N) (tag : btag) :
  write_cmembytes cm addr bs col tag = Some cm' ->
  (forall i tb, i < length bs ->
    cm_lookup (addr + N.of_nat i) cm.(cmem_data) = Some tb ->
    tb.(tb_color) = col) ->
  gmap_of_allocator cm A = gmap_of_allocator cm' A.
Proof.
  move=> Hwrite Hcolor.
  have Hmeta := @write_cmembytes_preserves_colors
    cm addr bs col tag cm' Hwrite Hcolor.
  apply gmap_of_allocator_cmem_ext.
  - move=> c. rewrite /alloc_base.
    by rewrite (proj2 (Hmeta c)).
  - move=> c. rewrite /alloc_size.
    exact (proj1 (Hmeta c)).
Qed.

(* ----------------------------------------------------------------- *)
(* Helper: an allocated zero byte                                      *)
(* ----------------------------------------------------------------- *)

Definition tb_alloc (c : N) : tagged_byte :=
  {| tb_value := #00%byte; tb_color := Some c; tb_tag := Numeric |}.

Definition alloc_result_base (addr size : N) : N :=
  if N.eqb size 0%N then 0%N else addr.

(* An empty allocation has no byte from which to recover its address. *)
Lemma calloc_alloc_base (cm cm' : cmem) (A A' : allocator) (a n c : N) :
  isSound A (cmem_data cm) ->
  calloc cm A a n c cm' A' ->
  alloc_base cm' c = alloc_result_base a n.
Proof.
  move=> Hsound Halloc.
  unfold alloc_base, alloc_result_base.
  destruct (N.eqb n 0) eqn:Hn.
  - apply N.eqb_eq in Hn. subst n.
    have Hcount := @calloc_count_color cm A a 0 c cm' A' Hsound Halloc.
    have Hnone := (proj2 (base_color_none_iff_count_color_zero c (cmem_data cm'))) Hcount.
    by rewrite Hnone.
  - apply N.eqb_neq in Hn.
    have Hpos : (0 < n)%N by lia.
    by rewrite (@calloc_base_color cm A a n c cm' A' Hpos Hsound Halloc).
Qed.

(* ----------------------------------------------------------------- *)
(* A byte that is free in the allocator is not a live location         *)
(* ----------------------------------------------------------------- *)

Lemma gmap_of_allocator_calloc (cm cm' : cmem) (A A' : allocator) (a n c : N) :
  isSound A (cmem_data cm) ->
  calloc cm A a n c cm' A' ->
  gmap_of_allocator cm' A' =
    <[c := (alloc_result_base a n, n)]> (gmap_of_allocator cm A).
Proof.
  move=> Hsound Halloc.
  have HA : A' = allocator_insert c A by inversion Halloc.
  subst A'. apply map_eq. move=> d.
  destruct (decide (c = d)) as [<-|Hne].
  - rewrite lookup_insert.
    have Hlive : allocated (allocator_insert c A) !! c = Some true.
    { by rewrite /allocator_insert /= lookup_insert. }
    rewrite (gmap_of_allocator_lookup_true cm' Hlive).
    rewrite (calloc_alloc_base cm cm' A (allocator_insert c A) a n c Hsound Halloc) /alloc_size.
    by rewrite (@calloc_count_color cm A a n c cm' (allocator_insert c A) Hsound Halloc).
  - rewrite lookup_insert_ne; last exact Hne.
    have Hlookup : allocated (allocator_insert c A) !! d = allocated A !! d.
    { by rewrite /allocator_insert /= lookup_insert_ne. }
    destruct (decide (allocated A !! d = Some true)) as [Hd|Hd].
    + rewrite (gmap_of_allocator_lookup_true cm Hd).
      have Hd' : allocated (allocator_insert c A) !! d = Some true by rewrite Hlookup.
      rewrite (gmap_of_allocator_lookup_true cm' Hd').
      have Hdc : d <> c by congruence.
      rewrite /alloc_base /alloc_size.
      rewrite (@calloc_base_color_preserved cm A a n c d cm' (allocator_insert c A) Hsound Halloc Hd Hdc).
      by rewrite (@calloc_count_color_preserved cm A a n c d cm' (allocator_insert c A) Hsound Halloc Hd Hdc).
    + have Hd' : allocated (allocator_insert c A) !! d <> Some true by rewrite Hlookup.
      by rewrite (gmap_of_allocator_lookup_not_true cm Hd)
        (gmap_of_allocator_lookup_not_true cm' Hd').
Qed.

Lemma gmap_of_allocator_remove (cm : cmem) (A : allocator) (c : N) :
  gmap_of_allocator cm (allocator_remove c A) = delete c (gmap_of_allocator cm A).
Proof.
  apply map_eq. move=> d.
  destruct (decide (c = d)) as [<-|Hne].
  - rewrite lookup_delete. apply gmap_of_allocator_lookup_not_true.
    by rewrite /allocator_remove /= lookup_insert.
  - rewrite lookup_delete_ne; last exact Hne.
    have Hlookup : allocated (allocator_remove c A) !! d = allocated A !! d.
    { by rewrite /allocator_remove /= lookup_insert_ne. }
    destruct (decide (allocated A !! d = Some true)) as [Hd|Hd].
    + have Hd' : allocated (allocator_remove c A) !! d = Some true by rewrite Hlookup.
      by rewrite (gmap_of_allocator_lookup_true cm Hd)
        (gmap_of_allocator_lookup_true cm Hd').
    + have Hd' : allocated (allocator_remove c A) !! d <> Some true by rewrite Hlookup.
      by rewrite (gmap_of_allocator_lookup_not_true cm Hd)
        (gmap_of_allocator_lookup_not_true cm Hd').
Qed.

Lemma live_locations_lookup_byte (cm : colored_memory_list) (A : allocator)
    (addr : N) (tb : tagged_byte) :
  gmap_of_list (cml_data cm) !! addr = Some tb ->
  live_locations cm A !! addr =
    if isAllocOptb (tb_color tb) A then Some () else None.
Proof.
  move=> Hlookup.
  have Hfold : forall m : gmap N tagged_byte, forall i,
      map_fold (live_fold A) ∅ m !! i =
        match m !! i with
        | Some x => if isAllocOptb (tb_color x) A then Some () else None
        | None => None
        end.
  { move=> m. apply (map_fold_ind (fun r m => forall i,
      r !! i = match m !! i with
        | Some x => if isAllocOptb (tb_color x) A then Some () else None
        | None => None end) (live_fold A) ∅).
    - move=> i. by rewrite lookup_empty.
    - move=> j x m0 r Hnone IH i.
      destruct (decide (j = i)) as [->|Hne].
      + rewrite lookup_insert. have Hr : r !! i = None by rewrite IH Hnone.
        unfold live_fold, isAllocOptb, isAllocb.
        destruct (tb_color x) as [c|]; last exact Hr.
        destruct (allocated A !! c) as [[|]|]; simpl;
          try exact Hr; by rewrite lookup_insert.
      + rewrite live_fold_lookup_ne; last exact Hne.
        rewrite lookup_insert_ne; last exact Hne. apply IH. }
  unfold live_locations.
  change (map_fold (live_fold A) ∅ (gmap_of_list (cml_data cm)) !! addr =
    if isAllocOptb (tb_color tb) A then Some () else None).
  by rewrite Hfold Hlookup.
Qed.

Fixpoint delete_block (base : N) (tbs : list tagged_byte)
    (m : gmap N tagged_byte) : gmap N tagged_byte :=
  match tbs with
  | [::] => m
  | _ :: tbs' => delete_block (base + 1)%N tbs' (delete base m)
  end.

Lemma ghost_map_delete_wblock (m : gmap N tagged_byte) (base : N)
    (tbs : list tagged_byte) :
  ghost_map_auth cmemGName 1 m -∗
  wblock base tbs ==∗
  ghost_map_auth cmemGName 1 (delete_block base tbs m).
Proof.
  iIntros "Hauth Hblock".
  iInduction tbs as [|tb tbs] "IH" forall (base m).
  - rewrite wblock_nil. iModIntro. iExact "Hauth".
  - rewrite wblock_cons. iDestruct "Hblock" as "[Hhead Htail]".
    iMod (ghost_map_delete with "Hauth Hhead") as "Hauth".
    iApply ("IH" with "Hauth Htail").
Qed.

Lemma count_color_list_all_color (c : N) (tbs : list tagged_byte) :
  all (fun tb => tb_color tb == Some c) tbs ->
  count_color_list c tbs = N.of_nat (length tbs).
Proof.
  induction tbs as [|tb tbs IH]; first done.
  move=> /= /andP [/eqP Hcolor Hall].
  rewrite (proj2 (tbc_is_color_eq c tb) Hcolor) (IH Hall).
  rewrite Nat2N.inj_succ. lia.
Qed.

Lemma base_color_index_prefix_zero (c : N) (l : list tagged_byte) (base : nat) :
  base_color_index c l = Some base ->
  count_color_list c (take base l) = 0%N.
Proof.
  revert base.
  induction l as [|tb l IH]; intros base Hbase; first discriminate.
  simpl in Hbase.
  destruct (tbc_is_color c tb) eqn:Hhead.
  - inversion Hbase; subst base. done.
  - destruct (base_color_index c l) as [base'|] eqn:Htail;
      simpl in Hbase; last discriminate.
    inversion Hbase; subst base.
    simpl. rewrite Hhead. exact (IH base' Logic.eq_refl).
Qed.

Lemma wblock_matches_cmem (cm : cmem) (A : allocator) (base : N)
    (tbs : list tagged_byte) :
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm A) -∗
  wblock base tbs -∗
  ⌜forall i tb, tbs !! i = Some tb ->
      gmap_of_list (cml_data (cmem_data cm)) !! (base + N.of_nat i)%N = Some tb⌝.
Proof.
  iIntros "Hauth Hblock" (i tb Htb).
  iDestruct (big_sepL_lookup with "Hblock") as "Helem"; first exact Htb.
  iDestruct (ghost_map_lookup with "Hauth Helem") as %Hlookup.
  apply map_lookup_filter_Some in Hlookup as [Hphysical _].
  iPureIntro.
  replace (N.of_nat (N.to_nat base + i)) with (base + N.of_nat i)%N in Hphysical;
    [exact Hphysical | lia].
Qed.

Lemma block_lookups_determine_slice (l tbs : list tagged_byte) (base : nat) :
  (forall i tb, tbs !! i = Some tb -> l !! (base + i) = Some tb) ->
  take (length tbs) (drop base l) = tbs.
Proof.
  move=> Hlookup. apply list_eq. move=> i.
  destruct (decide (i < length tbs)) as [Hi|Hi].
  - rewrite lookup_take; last exact Hi. rewrite lookup_drop.
    destruct (lookup_lt_is_Some_2 tbs i Hi) as [tb Htb].
    by rewrite Htb (Hlookup i tb Htb).
  - rewrite lookup_take_ge; last lia.
    by rewrite lookup_ge_None_2; last lia.
Qed.

Lemma count_color_list_zero_lookup (c : N) (l : list tagged_byte)
    (i : nat) (tb : tagged_byte) :
  count_color_list c l = 0%N ->
  l !! i = Some tb ->
  tb_color tb <> Some c.
Proof.
  move=> Hzero Hlookup Hcolor.
  have Hfalse : tbc_is_color c tb = false.
  { apply (count_color_list_zero_forall_in c l Hzero tb).
    apply (List.nth_error_In l i). by rewrite nth_error_lookup. }
  have Htrue : tbc_is_color c tb = true.
  { exact (proj2 (tbc_is_color_eq c tb) Hcolor). }
  by rewrite Htrue in Hfalse.
Qed.

Lemma all_color_lookup (c : N) (tbs : list tagged_byte) (i : nat)
    (tb : tagged_byte) :
  all (fun x => tb_color x == Some c) tbs ->
  tbs !! i = Some tb ->
  tb_color tb = Some c.
Proof.
  revert i.
  induction tbs as [|tb0 tbs IH]; intros [|i] Hall Hlookup;
    try discriminate.
  - move: Hall => /= /andP [/eqP Hcolor _].
    by inversion Hlookup; subst tb0.
  - move: Hall => /= /andP [_ Hall].
    exact (IH i Hall Hlookup).
Qed.

Lemma color_extent_exact (cm : cmem) (c base : N)
    (tbs : list tagged_byte) :
  alloc_base cm c = base ->
  alloc_size cm c = N.of_nat (length tbs) ->
  all (fun tb => tb_color tb == Some c) tbs ->
  take (length tbs) (drop (N.to_nat base) (cml_data (cmem_data cm))) = tbs ->
  forall i tb, cml_data (cmem_data cm) !! i = Some tb ->
    (tb_color tb = Some c <->
      N.to_nat base <= i < N.to_nat base + length tbs).
Proof.
  move=> Hbase Hsize Hall Hslice i tb Hlookup.
  destruct tbs as [|tb0 tbs].
  - unfold alloc_size, count_color in Hsize. simpl in Hsize.
    simpl. split; last (move=> H; lia).
    move=> Hcolor.
    exfalso.
    apply (count_color_list_zero_lookup c (cml_data (cmem_data cm)) i tb);
      [exact Hsize | exact Hlookup | exact Hcolor].
  - have Hlenpos : 0 < length (tb0 :: tbs) by simpl; lia.
    have Hcountpos : (0 < count_color c (cmem_data cm))%N.
    { rewrite /alloc_size in Hsize. rewrite Hsize. lia. }
    have Hbase_some : base_color c (cmem_data cm) = Some base.
    { unfold alloc_base in Hbase.
      destruct (base_color c (cmem_data cm)) as [b|] eqn:Hbc.
      - by rewrite Hbase.
      - have Hz := (proj1 (base_color_none_iff_count_color_zero c (cmem_data cm))) Hbc.
        lia. }
    have Hbase_index : base_color_index c (cml_data (cmem_data cm)) =
        Some (N.to_nat base).
    { unfold base_color in Hbase_some.
      destruct (base_color_index c (cml_data (cmem_data cm))) as [j|] eqn:Hbi;
        simpl in Hbase_some; last discriminate.
      inversion Hbase_some.
      f_equal. lia. }
    have Hprefix : count_color_list c
        (take (N.to_nat base) (cml_data (cmem_data cm))) = 0%N.
    { exact (base_color_index_prefix_zero c _ _ Hbase_index). }
    have Hmiddle : count_color_list c (tb0 :: tbs) =
        N.of_nat (length (tb0 :: tbs)).
    { exact (count_color_list_all_color c (tb0 :: tbs) Hall). }
    have Hdecomp := count_color_list_middle_decomp c
      (cml_data (cmem_data cm)) (N.to_nat base) (length (tb0 :: tbs)).
    rewrite Hslice in Hdecomp.
    have Hsuffix : count_color_list c
        (drop (N.to_nat base + length (tb0 :: tbs))
          (cml_data (cmem_data cm))) = 0%N.
    { unfold alloc_size, count_color in Hsize. lia. }
    split.
    + move=> Hcolor. split.
      * destruct (decide (i < N.to_nat base)) as [Hlt|Hlt]; last lia.
        exfalso. apply (count_color_list_zero_lookup c
          (take (N.to_nat base) (cml_data (cmem_data cm))) i tb Hprefix).
        -- rewrite lookup_take; [exact Hlookup | exact Hlt].
        -- exact Hcolor.
      * destruct (decide (N.to_nat base + length (tb0 :: tbs) <= i)) as [Hge|Hge]; last lia.
        exfalso. apply (count_color_list_zero_lookup c
          (drop (N.to_nat base + length (tb0 :: tbs))
            (cml_data (cmem_data cm)))
          (i - (N.to_nat base + length (tb0 :: tbs))) tb Hsuffix).
        -- rewrite lookup_drop. replace (N.to_nat base + length (tb0 :: tbs) +
              (i - (N.to_nat base + length (tb0 :: tbs)))) with i by lia.
           exact Hlookup.
        -- exact Hcolor.
    + move=> [Hlo Hhi].
      have Hmidlookup : (tb0 :: tbs) !! (i - N.to_nat base) = Some tb.
      { rewrite -Hslice. rewrite lookup_take; last lia. rewrite lookup_drop.
        replace (N.to_nat base + (i - N.to_nat base)) with i by lia.
        exact Hlookup. }
      exact (all_color_lookup c (tb0 :: tbs) (i - N.to_nat base) tb Hall Hmidlookup).
Qed.

Lemma delete_block_lookup (base addr : N) (tbs : list tagged_byte)
    (m : gmap N tagged_byte) :
  delete_block base tbs m !! addr =
    if decide ((base <= addr < base + N.of_nat (length tbs))%N)
    then None else m !! addr.
Proof.
  revert base m.
  induction tbs as [|tb tbs IH]; intros base m; simpl.
  - destruct (decide ((base <= addr < base + N.of_nat 0)%N)); [lia | done].
  - rewrite IH Nat2N.inj_succ.
    destruct (decide (addr = base)) as [->|Hne].
    + rewrite lookup_delete.
      destruct (decide (((base + 1)%N <= base <
        (base + 1 + N.of_nat (length tbs))%N)%N)); first lia.
      destruct (decide ((base <= base < base + N.succ (N.of_nat (length tbs)))%N));
        [done | lia].
    + rewrite lookup_delete_ne; last by congruence.
      destruct (decide (((base + 1)%N <= addr <
        (base + 1 + N.of_nat (length tbs))%N)%N));
      destruct (decide ((base <= addr < base + N.succ (N.of_nat (length tbs)))%N));
        try done; lia.
Qed.

Lemma isAllocOptb_remove_ne (A : allocator) (c : N) (col : option N) :
  col <> Some c ->
  isAllocOptb col (allocator_remove c A) = isAllocOptb col A.
Proof.
  destruct col as [d|]; last done.
  move=> Hne. unfold isAllocOptb, isAllocb, allocator_remove; simpl.
  rewrite lookup_insert_ne; [done | congruence].
Qed.

Lemma gmap_of_cmem_lookup_byte (cm : cmem) (A : allocator)
    (addr : N) (tb : tagged_byte) :
  gmap_of_list (cml_data (cmem_data cm)) !! addr = Some tb ->
  gmap_of_cmem cm A !! addr =
    if isAllocOptb (tb_color tb) A then Some tb else None.
Proof.
  move=> Hphysical. unfold gmap_of_cmem.
  rewrite map_lookup_filter Hphysical /=.
  rewrite (live_locations_lookup_byte (cmem_data cm) A addr tb Hphysical).
  destruct (isAllocOptb (tb_color tb) A); simpl.
  - done.
  - done.
Qed.

Lemma gmap_of_cmem_remove_exact (cm : cmem) (A : allocator)
    (c base : N) (tbs : list tagged_byte) :
  A.(allocated) !! c = Some true ->
  alloc_base cm c = base ->
  alloc_size cm c = N.of_nat (length tbs) ->
  all (fun tb => tb_color tb == Some c) tbs ->
  take (length tbs) (drop (N.to_nat base) (cml_data (cmem_data cm))) = tbs ->
  delete_block base tbs (gmap_of_cmem cm A) =
    gmap_of_cmem cm (allocator_remove c A).
Proof.
  move=> Halloc Hbase Hsize Hall Hslice.
  apply map_eq. move=> addr. rewrite delete_block_lookup.
  destruct (gmap_of_list (cml_data (cmem_data cm)) !! addr) as [tb|]
    eqn:Hphysical.
  - have Hlist : cml_data (cmem_data cm) !! N.to_nat addr = Some tb.
    { rewrite gmap_of_list_lookup in Hphysical. exact Hphysical. }
    have Hextent := color_extent_exact cm c base tbs Hbase Hsize Hall Hslice
      (N.to_nat addr) tb Hlist.
    destruct (decide (tb_color tb = Some c)) as [Hcolor|Hcolor].
    + have Hrange_nat := (proj1 Hextent) Hcolor.
      have Hrange_N : (base <= addr < base + N.of_nat (length tbs))%N by lia.
      destruct (decide ((base <= addr < base + N.of_nat (length tbs))%N));
        last contradiction.
      rewrite (gmap_of_cmem_lookup_byte cm (allocator_remove c A) addr tb Hphysical).
      unfold isAllocOptb, isAllocb. rewrite Hcolor /=.
      rewrite /allocator_remove /= lookup_insert. done.
    + have Hnotrange_nat : ~ (N.to_nat base <= N.to_nat addr <
          N.to_nat base + length tbs).
      { intro Hr. apply Hcolor. exact (proj2 Hextent Hr). }
      have Hnotrange_N : ~ (base <= addr < base + N.of_nat (length tbs))%N by lia.
      destruct (decide ((base <= addr < base + N.of_nat (length tbs))%N));
        first contradiction.
      rewrite (gmap_of_cmem_lookup_byte cm A addr tb Hphysical).
      rewrite (gmap_of_cmem_lookup_byte cm (allocator_remove c A) addr tb Hphysical).
      by rewrite (isAllocOptb_remove_ne A c (tb_color tb) Hcolor).
  - have Holdnone : gmap_of_cmem cm A !! addr = None.
    { unfold gmap_of_cmem. apply map_lookup_filter_None_2. by left. }
    have Hnewnone : gmap_of_cmem cm (allocator_remove c A) !! addr = None.
    { unfold gmap_of_cmem. apply map_lookup_filter_None_2. by left. }
    destruct (decide ((base <= addr < base + N.of_nat (length tbs))%N));
      by rewrite ?Holdnone ?Hnewnone.
Qed.

Lemma ghost_map_free_color (cm : cmem) (A : allocator)
    (c base size : N) (tbs : list tagged_byte) :
  A.(allocated) !! c = Some true ->
  N.of_nat (length tbs) = size ->
  all (fun tb => tb_color tb == Some c) tbs ->
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm A) -∗
  ghost_map_auth allGName 1 (gmap_of_allocator cm A) -∗
  wall c base size -∗
  wblock base tbs ==∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm (allocator_remove c A)) ∗
  ghost_map_auth allGName 1 (gmap_of_allocator cm (allocator_remove c A)).
Proof.
  iIntros (Halloc Hlen Hall) "Hcm Hallauth Hwall Hblock".
  iDestruct (ghost_map_lookup with "Hallauth Hwall") as %Hmetadata.
  rewrite (gmap_of_allocator_lookup_true cm Halloc) in Hmetadata.
  inversion Hmetadata; subst base size; clear Hmetadata.
  iDestruct (wblock_matches_cmem with "Hcm Hblock") as %Hmatches.
  have Hslice : take (length tbs)
      (drop (N.to_nat (alloc_base cm c)) (cml_data (cmem_data cm))) = tbs.
  { apply block_lookups_determine_slice. move=> i tb Htb.
    have Hphysical := Hmatches i tb Htb.
    rewrite gmap_of_list_lookup in Hphysical.
    replace (N.to_nat (alloc_base cm c) + i) with
      (N.to_nat (alloc_base cm c + N.of_nat i)) by lia.
    exact Hphysical. }
  have Hcmmap := gmap_of_cmem_remove_exact cm A c (alloc_base cm c) tbs
    Halloc Logic.eq_refl H1 Hall Hslice.
  iMod (ghost_map_delete_wblock with "Hcm Hblock") as "Hcm".
  iMod (allocator_remove_wall with "Hallauth Hwall") as "Hallauth".
  iModIntro. rewrite Hcmmap -gmap_of_allocator_remove. iFrame.
Qed.

Lemma live_fold_none_identity (a : allocator) (old : tagged_byte) (i : N) (r : gmap N ()) :
  (live_fold a i old r) !! i = None ->
  live_fold a i old r = r.
Proof.
  move => Hnon.
  unfold live_fold in Hnon.
  unfold live_fold.
  destruct (tb_color old) as [c|] eqn:Hco => /=.
  - destruct (a.(allocated) !! c) as [b|] eqn:Ha => /=.
    + destruct b.
      * rewrite lookup_insert in Hnon. done.
      * done.
    + done.
  - done.
Qed.

Lemma isfree_not_live (x : N) (cm : colored_memory_list) (a : allocator) :
  isfree x cm a ->
  live_locations cm a !! x = None.
Proof.
  unfold isfree, live_locations.
  case (cm_lookup x cm) as [tb|] eqn:Hcm.
  - move => Hf.
    have Hkey : gmap_of_list (cml_data cm) !! x = Some tb.
    { rewrite gmap_of_list_lookup. rewrite -nth_error_lookup. exact Hcm. }
    rewrite (map_fold_delete_L (live_fold a) ∅ x tb (gmap_of_list (cml_data cm))); last first.
    { exact Hkey. }
    { intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes. }
    unfold live_fold.
    destruct (tb_color tb) as [c|] eqn:Hc => /=.
    + have Hf' : a.(allocated) !! c = Some false.
      { move/eqP: Hf. done. }
      rewrite Hf'. simpl.
      apply (@map_fold_keys_subset a (delete x (gmap_of_list (cml_data cm))) x).
      rewrite lookup_delete. done.
    + apply (@map_fold_keys_subset a (delete x (gmap_of_list (cml_data cm))) x).
      rewrite lookup_delete. done.
  - move => _. apply (@map_fold_keys_subset a (gmap_of_list (cml_data cm)) x).
    rewrite gmap_of_list_lookup. rewrite -nth_error_lookup. exact Hcm.
Qed.

Lemma isfree_insert_allocator (x c : N) (cm : colored_memory_list) (A : allocator) :
  isfree x cm A ->
  A.(allocated) !! c = None ->
  isfree x cm (allocator_insert c A).
Proof.
  unfold isfree.
  case (cm_lookup x cm) as [tb|] eqn:Hcm => //.
  destruct (tb_color tb) as [c'|] eqn:Hco => //.
  move => Hf Hnone.
  have Hf' : A.(allocated) !! c' = Some false.
  { move/eqP: Hf. done. }
  have Hc' : c' <> c.
  { intro Hcc. subst. rewrite Hnone in Hf'. done. }
  have Hcne : c <> c'.
  { intro Hcc. apply Hc'. exact (Logic.eq_sym Hcc). }
  rewrite (lookup_insert_ne (allocated A) c c' true Hcne).
  rewrite Hf'. done.
Qed.

Lemma map_fold_cmem_alloc_insert (m : gmap N tagged_byte) (A : allocator) (c : N) :
  (forall i b, m !! i = Some b -> tb_color b <> Some c) ->
  map_fold (live_fold (allocator_insert c A)) ∅ m = map_fold (live_fold A) ∅ m.
Proof.
  move => Hcolor.
  revert Hcolor.
  induction m using map_ind.
  - move => _. rewrite map_fold_empty map_fold_empty. done.
  - move => Hcol.
    have Hx : tb_color x <> Some c.
    { apply (Hcol i x). rewrite lookup_insert. done. }
    have IHfold : map_fold (live_fold (allocator_insert c A)) ∅ m = map_fold (live_fold A) ∅ m.
    { apply IHm. move => j b Hb.
      have Hjni : j <> i.
      { intro Hjeq. subst. rewrite H in Hb. discriminate. }
      apply (Hcol j b). rewrite lookup_insert_ne; [ exact Hb | move => Hce; subst; exact (Hjni Logic.eq_refl) ].
    }
    have HfoldA : map_fold (live_fold A) ∅ (<[i := x]> m) = live_fold A i x (map_fold (live_fold A) ∅ m).
    { apply (map_fold_insert_L (live_fold A) ∅ i x m).
      intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes.
      done. }
    have HfoldAi : map_fold (live_fold (allocator_insert c A)) ∅ (<[i := x]> m) =
      live_fold (allocator_insert c A) i x (map_fold (live_fold (allocator_insert c A)) ∅ m).
    { apply (map_fold_insert_L (live_fold (allocator_insert c A)) ∅ i x m).
      intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes.
      done. }
    rewrite HfoldAi HfoldA IHfold.
    unfold live_fold.
    destruct (tb_color x) as [c'|] eqn:Hxc => //=.
    have Hcne : c <> c'.
    { intro Hcc. apply Hx. rewrite -Hcc. done. }
    rewrite (lookup_insert_ne (allocated A) c c' true Hcne). done.
Qed.

Lemma live_locations_insert_allocator_ne (cm : colored_memory_list) (A : allocator) (c : N) :
  isSound_b A cm ->
  A.(allocated) !! c = None ->
  live_locations cm (allocator_insert c A) = live_locations cm A.
Proof.
  move => Hsound Hnone.
  unfold live_locations.
  apply map_fold_cmem_alloc_insert.
  move => i0 b0 Hb0 Hcb.
  have Hb0_in : List.In b0 (cml_data cm).
  { rewrite gmap_of_list_lookup in Hb0.
    rewrite -nth_error_lookup in Hb0.
    eapply (List.nth_error_In (cml_data cm) (N.to_nat i0)). exact Hb0. }
  have Hc' : forall c0 : N, tb_color b0 = Some c0 -> allocated A !! c0 <> None.
  { unfold isSound_b in Hsound.
    exact (proj1 (List.Forall_forall _ _) Hsound b0 Hb0_in). }
  apply (Hc' c Hcb).
  rewrite Hnone. done.
Qed.

Lemma map_filter_insert_permute (m : gmap N tagged_byte) (i : N) (x : tagged_byte)
    (P Q : (N * tagged_byte) -> Prop) `{forall x : N * tagged_byte, Decision (Q x)}
    `{forall x : N * tagged_byte, Decision (P x)} :
  Q (i, x) -> ~ P (i, x) ->
  (forall j y, j <> i -> (Q (j, y) <-> P (j, y))) ->
  filter Q (<[i := x]> m) = <[i := x]> (filter P m).
Proof.
  move => HQ HnotP Hoodd.
  apply map_eq. intros j. apply option_eq; intros y.
  case (decide (j = i)).
  - move => Hji. subst j.
    setoid_rewrite map_lookup_filter_Some. rewrite !lookup_insert. naive_solver.
  - move => Hjni.
    have Hijn : i <> j.
    { intro Hij. apply Hjni. exact (Logic.eq_sym Hij). }
    setoid_rewrite map_lookup_filter_Some. rewrite !(lookup_insert_ne _ i j x Hijn).
    rewrite map_lookup_filter_Some.
    split.
    + move => [Hmb Hq]. split => //. destruct (Hoodd j y Hjni) as [Hqf Hpf]. exact (Hqf Hq).
    + move => [Hmb Hp]. split => //. destruct (Hoodd j y Hjni) as [Hqf Hpf]. exact (Hpf Hp).
Qed.

Lemma isfree_not_alloc_opt (x : N) (cm : colored_memory_list) (A : allocator) (tb : tagged_byte) :
  cm_lookup x cm = Some tb ->
  isfree x cm A ->
  ~ isAllocOpt (tb_color tb) A.
Proof.
  move => Hlook Hfree.
  unfold isfree in Hfree.
  rewrite Hlook in Hfree.
  destruct (tb_color tb) as [c|] eqn:Hc => //=.
  - move/eqP: Hfree => Hfree'.
    unfold isAllocOpt, isAlloc.
    intro Hall. rewrite Hfree' in Hall. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* tmemb: the colored-memory list overwritten by k repeated bytes      *)
(* ------------------------------------------------------------------ *)

Definition tmemb (cm : colored_memory_list) (a0 : nat) (tb : tagged_byte) (k : nat) :
  colored_memory_list :=
  {| cml_data := take a0 (cml_data cm) ++ repeat tb k ++ drop (a0 + k) (cml_data cm) |}.

Lemma take_drop_app (T : Type) : forall (l : list T) (n : nat), take n l ++ drop n l = l.
Proof.
  intros l. induction l; intros [|n]; simpl; try done.
  rewrite IHl. done.
Qed.

Lemma cat_firstn_skipn (T : Type) (n : nat) (l : list T) : cat (firstn n l) (skipn n l) = l.
Proof. elim: l n => [|x l IH] [|n]; simpl; try done. rewrite IH. done. Qed.

Lemma nth_error_lookup (T : Type) (l : list T) (i : nat) : (List.nth_error l i) = l !! i.
Proof.
  elim: l i => [i | x l IH [|i]].
  - case: i; simpl; done.
  - simpl; done.
  - simpl. apply: IH.
Qed.

Lemma repeat_S_app (T : Type) (x : T) : forall n : nat, repeat x (S n) = repeat x n ++ [x].
Proof.
  induction n; simpl; first done.
  apply (f_equal (cons x)). exact IHn.
Qed.

Lemma tmemb_length (cm : colored_memory_list) (a0 k : nat) (tb : tagged_byte) :
  a0 <= length (cml_data cm) ->
  length (cml_data (tmemb cm a0 tb k)) = a0 + k + (length (cml_data cm) - (a0 + k)).
Proof.
  move => Ha0.
  rewrite /tmemb. repeat rewrite app_length. rewrite repeat_length.
  rewrite (take_length_le (cml_data cm) a0 Ha0). rewrite drop_length. lia.
Qed.

Lemma tmemb_length_eq (cm : colored_memory_list) (a0 k : nat) (tb : tagged_byte) :
  a0 <= length (cml_data cm) ->
  a0 + k < length (cml_data cm) ->
  length (cml_data (tmemb cm a0 tb k)) = length (cml_data cm).
Proof.
  move => Ha0 Hlen. rewrite (tmemb_length cm a0 k tb Ha0). lia.
Qed.

Lemma tmemb_length_oob (cm : colored_memory_list) (a0 k : nat) (tb : tagged_byte) :
  a0 <= length (cml_data cm) ->
  length (cml_data cm) <= a0 + k ->
  length (cml_data (tmemb cm a0 tb k)) = a0 + k.
Proof.
  move => Ha0 Hlen. rewrite (tmemb_length cm a0 k tb Ha0). lia.
Qed.

Lemma tmemb_frontier_byte (cm : colored_memory_list) (a0 k : nat) (tb : tagged_byte) :
  a0 <= length (cml_data cm) ->
  a0 + k < length (cml_data cm) ->
  cml_data (tmemb cm a0 tb k) !! (a0 + k) = cml_data cm !! (a0 + k).
Proof.
  move => Ha0 Hlen.
  rewrite /tmemb.
  rewrite (lookup_app_r (take a0 (cml_data cm))
      (repeat tb k ++ drop (a0 + k) (cml_data cm)) (a0 + k));
    [ | rewrite (take_length_le (cml_data cm) a0 Ha0); lia ].
  rewrite (take_length_le (cml_data cm) a0 Ha0).
  replace (a0 + k - a0) with k; [ | lia ].
  rewrite (lookup_app_r (repeat tb k) (drop (a0 + k) (cml_data cm)) k);
    [ | rewrite repeat_length; lia ].
  replace (k - length (repeat tb k)) with 0; [ | rewrite repeat_length; lia ].
  rewrite (lookup_drop (cml_data cm) (a0 + k) 0).
  replace (a0 + k + 0) with (a0 + k); [ | lia ]. done.
Qed.

Lemma seq_cat_app (T : Type) : forall (l1 l2 : list T), cat l1 l2 = app l1 l2.
Proof.
  induction l1; simpl; intros l2.
  - done.
  - apply (f_equal (cons a)). exact (IHl1 l2).
Qed.

Lemma tmemb_step_in (cm : colored_memory_list) (a0 k : nat) (tb : tagged_byte) :
  a0 <= length (cml_data cm) ->
  a0 + k < length (cml_data cm) ->
  cml_data (tmemb cm a0 tb (S k)) = <[a0 + k := tb]> (cml_data (tmemb cm a0 tb k)).
Proof.
  move => Ha0 Hlen.
  rewrite /tmemb. rewrite repeat_S_app.
  rewrite (insert_take_drop (cml_data (tmemb cm a0 tb k)) (a0 + k) tb).
  - unfold tmemb.
    replace (a0 + k) with (length (take a0 (cml_data cm)) + k);
      [ | rewrite (take_length_le (cml_data cm) a0 Ha0); lia ].
    rewrite (take_app_add (take a0 (cml_data cm))
        (repeat tb k ++ drop (length (take a0 (cml_data cm)) + k) (cml_data cm)) k).
    rewrite (take_app_le (repeat tb k)
        (drop (length (take a0 (cml_data cm)) + k) (cml_data cm)) k);
      [ | rewrite repeat_length; lia ].
    rewrite (take_ge (repeat tb k) k); [ | rewrite repeat_length; lia ].
    replace (S (length (take a0 (cml_data cm)) + k))
      with (length (take a0 (cml_data cm)) + (k + 1)); [ | lia ].
    rewrite (drop_app_add (take a0 (cml_data cm))
        (repeat tb k ++ drop (length (take a0 (cml_data cm)) + k) (cml_data cm)) (k + 1)).
    rewrite (drop_app (repeat tb k)
        (drop (length (take a0 (cml_data cm)) + k) (cml_data cm)) (k + 1)).
    rewrite (drop_ge (repeat tb k) (k + 1)); [ | rewrite repeat_length; lia ].
    rewrite (left_id_L [] (++)).
    replace ((k + 1) - length (repeat tb k)) with 1; [ | rewrite repeat_length; lia ].
    rewrite (drop_drop (cml_data cm) 1 (length (take a0 (cml_data cm)) + k)).
    replace (length (take a0 (cml_data cm)) + k) with (a0 + k);
      [ | rewrite (take_length_le (cml_data cm) a0 Ha0); lia ].
    replace (a0 + k + 1) with (a0 + S k); [ | lia ].
    rewrite !(@seq_cat_app tagged_byte _ _).
    rewrite (app_assoc_reverse (take a0 (cml_data cm)) (repeat tb k)
        ([tb] ++ drop (a0 + S k) (cml_data cm))).
    rewrite (app_assoc_reverse (repeat tb k) [tb]
        (drop (a0 + S k) (cml_data cm))).
    done.
  - rewrite (tmemb_length cm a0 k tb Ha0). lia.
Qed.

Lemma tmemb_step_oob (cm : colored_memory_list) (a0 k : nat) (tb : tagged_byte) :
  a0 <= length (cml_data cm) ->
  length (cml_data cm) <= a0 + k ->
  cml_data (tmemb cm a0 tb (S k)) = cml_data (tmemb cm a0 tb k) ++ [tb].
Proof.
  move => Ha0 Hlen.
  rewrite /tmemb. rewrite repeat_S_app.
  rewrite (drop_ge (cml_data cm) (a0 + S k)); [ | lia ].
  rewrite (drop_ge (cml_data cm) (a0 + k)); [ | exact Hlen ].
  rewrite !(@seq_cat_app tagged_byte _ _).
  rewrite !(right_id_L [] (++)).
  rewrite (app_assoc_reverse (firstn a0 (cml_data cm)) (repeat tb k) [tb]).
  done.
Qed.

Lemma live_fold_live_insert (A : allocator) (tb : tagged_byte) (i : N) (r : gmap N ()) :
  isAllocOpt (tb_color tb) A ->
  live_fold A i tb r = <[i := ()]> r.
Proof.
  move => Hlive.
  unfold live_fold.
  destruct (tb_color tb) as [c|] eqn:Hc.
  - unfold isAllocOpt in Hlive.
    destruct (A.(allocated) !! c) as [b|] eqn:Ha.
    + destruct b.
      * done.
      * unfold isAlloc in Hlive. rewrite Ha in Hlive. discriminate.
    + unfold isAlloc in Hlive. rewrite Ha in Hlive. discriminate.
  - cbv in Hlive. discriminate.
Qed.

Lemma live_fold_frontier_not_live (A : allocator) (old : tagged_byte) (i : N) (r : gmap N ()) :
  ~ isAllocOpt (tb_color old) A ->
  r !! i = None ->
  live_fold A i old r !! i = None.
Proof.
  move => Hnot Hr.
  unfold live_fold.
  destruct (tb_color old) as [c|] eqn:Hc.
  - unfold isAllocOpt in Hnot. unfold isAlloc in Hnot.
    destruct (A.(allocated) !! c) as [b|] eqn:Ha.
    + destruct b.
      * exfalso. apply Hnot. done.
      * rewrite Hr. done.
    + rewrite Hr. done.
  - rewrite Hr. done.
Qed.

Lemma live_locations_frontier_add_live (d : colored_memory_list) (A : allocator)
    (i : N) (old tb : tagged_byte) :
  cml_data d !! N.to_nat i = Some old ->
  ~ isAllocOpt (tb_color old) A ->
  isAllocOpt (tb_color tb) A ->
  live_locations {| cml_data := <[N.to_nat i := tb]> (cml_data d) |} A =
  <[i := ()]> (live_locations d A).
Proof.
  move => Haddr Holdnot Htblive.
  unfold live_locations.
  have Hlen_i : N.to_nat i < length (cml_data d).
  { exact (lookup_lt_Some (cml_data d) (N.to_nat i) old Haddr). }
  have Hgo : gmap_of_list (<[N.to_nat i := tb]> (cml_data d)) = <[i := tb]> (gmap_of_list (cml_data d)).
  { erewrite gmap_of_list_insert; last exact Hlen_i. done. }
  rewrite Hgo.
  have Hkey : gmap_of_list (cml_data d) !! i = Some old.
  { rewrite gmap_of_list_lookup. rewrite Haddr. done. }
  have Hfold_old : map_fold (live_fold A) ∅ (gmap_of_list (cml_data d)) =
    live_fold A i old (map_fold (live_fold A) ∅ (delete i (gmap_of_list (cml_data d)))).
  { apply (map_fold_delete_L (live_fold A) ∅ i old (gmap_of_list (cml_data d))).
    intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes.
    exact Hkey. }
  have Hfold_new : map_fold (live_fold A) ∅ (<[i := tb]> (gmap_of_list (cml_data d))) =
    live_fold A i tb (map_fold (live_fold A) ∅ (delete i (<[i := tb]> (gmap_of_list (cml_data d))))).
  { apply (map_fold_delete_L (live_fold A) ∅ i tb (<[i := tb]> (gmap_of_list (cml_data d)))).
    intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes.
    rewrite lookup_insert. done. }
  have Hdel : delete i (<[i := tb]> (gmap_of_list (cml_data d))) =
    delete i (gmap_of_list (cml_data d)).
  { rewrite delete_insert_delete. done. }
  have HF : map_fold (live_fold A) ∅ (delete i (gmap_of_list (cml_data d))) !! i = None.
  { apply (@map_fold_keys_subset A (delete i (gmap_of_list (cml_data d))) i).
    rewrite lookup_delete. done. }
  have Hold_id : live_fold A i old (map_fold (live_fold A) ∅ (delete i (gmap_of_list (cml_data d)))) =
    map_fold (live_fold A) ∅ (delete i (gmap_of_list (cml_data d))).
  { apply live_fold_none_identity.
    apply (@live_fold_frontier_not_live A old i _ Holdnot HF). }
  have Htb : live_fold A i tb (map_fold (live_fold A) ∅ (delete i (gmap_of_list (cml_data d)))) =
    <[i := ()]> (map_fold (live_fold A) ∅ (delete i (gmap_of_list (cml_data d)))).
  { apply live_fold_live_insert. exact Htblive. }
  rewrite Hfold_new Hfold_old Hdel.
  rewrite Hold_id Htb.
  done.
Qed.

Lemma live_locations_append_live (d : colored_memory_list) (A : allocator) (tb : tagged_byte) :
  isAllocOpt (tb_color tb) A ->
  live_locations {| cml_data := cml_data d ++ [tb] |} A =
  <[N.of_nat (length (cml_data d)) := ()]> (live_locations d A).
Proof.
  move => Hlive.
  unfold live_locations.
  rewrite (gmap_of_list_append (cml_data d) tb).
  have Hfoldtb : map_fold (live_fold A) ∅ (<[N.of_nat (length (cml_data d)) := tb]> (gmap_of_list (cml_data d))) =
    live_fold A (N.of_nat (length (cml_data d))) tb (map_fold (live_fold A) ∅ (gmap_of_list (cml_data d))).
  { apply (map_fold_insert_L (live_fold A) ∅ (N.of_nat (length (cml_data d))) tb (gmap_of_list (cml_data d))).
    intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes.
    rewrite gmap_of_list_lookup. apply lookup_ge_None. rewrite Nat2N.id. lia. }
  have Htb : live_fold A (N.of_nat (length (cml_data d))) tb (map_fold (live_fold A) ∅ (gmap_of_list (cml_data d))) =
    <[N.of_nat (length (cml_data d)) := ()]> (map_fold (live_fold A) ∅ (gmap_of_list (cml_data d))).
  { apply live_fold_live_insert. exact Hlive. }
  rewrite Hfoldtb Htb. done.
Qed.

Lemma wcs_repeat_S (addr col : N) (tag : btag) (b : byte) (k : nat) :
  wcs addr col tag (repeat b (S k)) ⊣⊢
  wcs addr col tag (repeat b k) ∗ (N.of_nat (N.to_nat addr + k)) ↦[wc]{col}{tag} b.
Proof.
  unfold wcs.
  rewrite repeat_S_app.
  rewrite big_sepL_app big_sepL_singleton.
  rewrite repeat_length. simpl.
  replace (N.of_nat (N.to_nat addr + length (repeat b k))) with (N.of_nat (N.to_nat addr + k));
    last first.
  { rewrite repeat_length. done. }
  rewrite Nat.add_0_r. done.
Qed.

Lemma colalloc_transfer_rec (cm : cmem) (A : allocator) (addr c : N) :
  isSound_b A (cmem_data cm) ->
  A.(allocated) !! c = None ->
  N.to_nat addr <= length (cml_data (cmem_data cm)) ->
  forall sz : nat,
  (forall a_off, (addr <= a_off < addr + N.of_nat sz)%N -> isfree a_off (cmem_data cm) A) ->
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm A) ==∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem {|
    cmem_data := tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz;
    cmem_max_opt := cm.(cmem_max_opt) |} (allocator_insert c A)) ∗
  wcs addr c Numeric (repeat #00%byte sz).
Proof.
  intros Hsound Hnone Haddr.
  iIntros (sz Hfree) "Hcmem".
  iInduction sz as [|sz IH] "IH".
  - destruct cm as [cd mo]. destruct cd as [cdd].
    have Htm0 : tmemb {| cml_data := cdd |} (N.to_nat addr) (tb_alloc c) 0 = {| cml_data := cdd |}.
    { unfold tmemb. replace (N.to_nat addr + 0) with (N.to_nat addr) by lia. simpl.
      apply (f_equal (fun x => {| cml_data := x |})).
      rewrite (cat_firstn_skipn tagged_byte (N.to_nat addr) cdd). done. }
    have Hgo_base : gmap_of_cmem {| cmem_data := tmemb {| cml_data := cdd |} (N.to_nat addr) (tb_alloc c) 0; cmem_max_opt := mo |} (allocator_insert c A) =
                    gmap_of_cmem {| cmem_data := {| cml_data := cdd |}; cmem_max_opt := mo |} A.
    { unfold gmap_of_cmem. rewrite Htm0.
      rewrite (live_locations_insert_allocator_ne {| cml_data := cdd |} A c Hsound Hnone). done. }
    rewrite Hgo_base. simpl. iFrame. simpl. iModIntro. unfold wcs. simpl. done.
  - have Hlt_sz : (addr + N.of_nat sz < addr + N.of_nat (S sz))%N.
    { rewrite Nat2N.inj_succ.
      rewrite (N.add_comm addr (N.of_nat sz)).
      rewrite (N.add_comm addr (N.succ (N.of_nat sz))).
      apply (N.add_lt_mono_r (N.of_nat sz) (N.succ (N.of_nat sz)) addr).
      apply N.lt_succ_diag_r. }
    have Hfree_sub : (forall a_off, (addr <= a_off < addr + N.of_nat sz)%N -> isfree a_off (cmem_data cm) A).
    { move => a_off Ha. apply Hfree. destruct Ha as [Hge Hlt].
      split; first exact Hge.
      exact: (N.lt_trans a_off (addr + N.of_nat sz) (addr + N.of_nat (S sz)) Hlt Hlt_sz). }
    iSpecialize ("IH" $! Hfree_sub).
    iMod ("IH" with "Hcmem") as "[Hcmem Hwcs]".
    set i0 := N.of_nat (N.to_nat addr + sz).
    rewrite wcs_repeat_S.
    destruct (Nat.lt_ge_cases (N.to_nat addr + sz) (length (cml_data (cmem_data cm)))) as [Hin | Hoob].
    { (* in-bounds *)
      have Hlen_sk : length (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)) = length (cml_data (cmem_data cm)).
      { exact (tmemb_length_eq (cmem_data cm) (N.to_nat addr) sz (tb_alloc c) Haddr Hin). }
      have Hold_some : is_Some (cml_data (cmem_data cm) !! (N.to_nat addr + sz)).
      { exact (lookup_lt_is_Some_2 (cml_data (cmem_data cm)) (N.to_nat addr + sz) Hin). }
      destruct Hold_some as [old Hold].
      have Hold_frontier : cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) !! (N.to_nat addr + sz) = Some old.
      { rewrite (tmemb_frontier_byte (cmem_data cm) (N.to_nat addr) sz (tb_alloc c) Haddr Hin). exact Hold. }
      have Hfree_frontier : isfree (addr + N.of_nat sz) (cmem_data cm) A.
      { apply Hfree. split; [ apply N.le_add_r | exact Hlt_sz ]. }
      have Hfree_frontier' : isfree (addr + N.of_nat sz) (cmem_data cm) (allocator_insert c A).
      { apply (isfree_insert_allocator (addr + N.of_nat sz) c (cmem_data cm) A).
        exact Hfree_frontier. exact Hnone. }
      have Hlook_frontier_cm : cm_lookup (addr + N.of_nat sz) (cmem_data cm) = Some old.
      { unfold cm_lookup. rewrite (N2Nat.inj_add addr (N.of_nat sz)). rewrite Nat2N.id. rewrite nth_error_lookup. exact Hold. }
      have Hnot_alloc : ~ isAllocOpt (tb_color old) (allocator_insert c A).
      { apply (isfree_not_alloc_opt (addr + N.of_nat sz) (cmem_data cm) (allocator_insert c A) old).
        exact Hlook_frontier_cm. exact Hfree_frontier'. }
      have Hlive_none : live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A) !! i0 = None.
      { unfold live_locations.
        have Hkey' : gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)) !! i0 = Some old.
        { rewrite gmap_of_list_lookup. unfold i0. rewrite Nat2N.id. exact Hold_frontier. }
        rewrite (map_fold_delete_L (live_fold (allocator_insert c A)) ∅ i0 old (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)))); last first.
        { exact Hkey'. }
        { intros j1 j2 z1 z2 y Hneq _ _; by apply live_fold_commutes. }
        have HF' : map_fold (live_fold (allocator_insert c A)) ∅ (delete i0 (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)))) !! i0 = None.
        { apply (@map_fold_keys_subset (allocator_insert c A) (delete i0 (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)))) i0).
          rewrite lookup_delete. done. }
        unfold live_fold.
        destruct (tb_color old) as [c'|] eqn:Hco.
        - unfold isAllocOpt in Hnot_alloc. unfold isAlloc in Hnot_alloc.
          destruct ((allocator_insert c A).(allocated) !! c') as [b'|] eqn:Haio.
          + destruct b'.
            * exfalso. apply Hnot_alloc. unfold isAllocOpt, isAlloc. done.
            * rewrite HF'. done.
          + rewrite HF'. done.
        - rewrite HF'. done. }
      have HliveS : live_locations {| cml_data := <[N.to_nat i0 := tb_alloc c]> (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)) |} (allocator_insert c A) =
        <[i0 := ()]> (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A)).
      { apply (live_locations_frontier_add_live (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A) i0 old (tb_alloc c)).
        { unfold i0. rewrite Nat2N.id. exact Hold_frontier. }
        { exact Hnot_alloc. }
        { unfold isAllocOpt, isAlloc, allocator_insert. simpl. rewrite lookup_insert. done. } }
      have Hgo_data : gmap_of_list (<[N.to_nat i0 := tb_alloc c]> (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))) =
        <[i0 := tb_alloc c]> (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))).
      { apply gmap_of_list_insert.
        unfold i0. rewrite Nat2N.id. rewrite Hlen_sk. exact Hin. }
      have Hdata_in : cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) (S sz)) =
        <[N.to_nat addr + sz := tb_alloc c]> (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)).
      { exact (tmemb_step_in (cmem_data cm) (N.to_nat addr) sz (tb_alloc c) Haddr Hin). }
      have Hgofilter : filter (fun '(j, _) => (<[i0 := ()]> (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A))) !! j = Some ())
                             (gmap_of_list (<[N.to_nat i0 := tb_alloc c]> (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)))) =
        <[i0 := tb_alloc c]>
          (filter (fun '(j, _) => (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A)) !! j = Some ())
             (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)))).
      { rewrite Hgo_data.
        apply (map_filter_insert_permute (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))) i0 (tb_alloc c)
          (fun '(j, _) => (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A)) !! j = Some ())
          (fun '(j, _) => (<[i0 := ()]> (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A))) !! j = Some ())).
        { rewrite lookup_insert. done. }
        { intro Hp. rewrite Hlive_none in Hp. discriminate. }
        { move => j y Hjne.
          have Hjni : i0 <> j. { intro Hcc. apply Hjne. symmetry. exact Hcc. }
          split; intro Heq.
          - rewrite lookup_insert_ne in Heq; [ done | exact Hjni ].
          - rewrite lookup_insert_ne; [ exact Heq | exact Hjni ]. } }
      have Hgo_step : gmap_of_cmem {| cmem_data := tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) (S sz); cmem_max_opt := cm.(cmem_max_opt) |} (allocator_insert c A) =
                      <[i0 := tb_alloc c]> (gmap_of_cmem {| cmem_data := tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz; cmem_max_opt := cm.(cmem_max_opt) |} (allocator_insert c A)).
      { unfold gmap_of_cmem.
        cbn [cmem_data cml_data].
        rewrite Hdata_in.
        have Hdata_rec : tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) (S sz) =
          {| cml_data := <[N.to_nat addr + sz := tb_alloc c]> (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)) |}.
        { rewrite /tmemb.
          apply (f_equal (fun (l0 : list tagged_byte) => {| cml_data := l0 |})).
          exact Hdata_in. }
        rewrite Hdata_rec.
        rewrite - (Nat2N.id (N.to_nat addr + sz)).
        rewrite HliveS.
        exact Hgofilter. }
      rewrite Hgo_step.
      iMod (ghost_map_insert i0 (tb_alloc c) with "Hcmem") as "[Hcmem Helem]".
      { apply map_lookup_filter_None_2. right.
        move => x0 Hx0 Hp. cbn in Hp. rewrite Hlive_none in Hp. discriminate. }
      iModIntro. iFrame. }
    { (* out-of-bounds *)
      have Hlen_app : length (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)) = N.to_nat addr + sz.
      { exact (tmemb_length_oob (cmem_data cm) (N.to_nat addr) sz (tb_alloc c) Haddr Hoob). }
      have Hdata_oob : cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) (S sz)) =
        cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) ++ [tb_alloc c].
      { exact (tmemb_step_oob (cmem_data cm) (N.to_nat addr) sz (tb_alloc c) Haddr Hoob). }
      have HliveS_oob : live_locations {| cml_data := cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) ++ [tb_alloc c] |} (allocator_insert c A) =
        <[N.of_nat (length (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))) := ()]> (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A)).
      { apply (live_locations_append_live (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A) (tb_alloc c)).
        unfold isAllocOpt, isAlloc, allocator_insert. simpl. rewrite lookup_insert. done. }
      have Hgo_data_oob : gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) ++ [tb_alloc c]) =
        <[N.of_nat (length (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))) := tb_alloc c]> (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))).
      { exact (gmap_of_list_append (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)) (tb_alloc c)). }
      have Hlive_none_oob : live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A) !! i0 = None.
      { unfold live_locations.
        apply (@map_fold_keys_subset (allocator_insert c A) (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))) i0).
        rewrite gmap_of_list_lookup. unfold i0. rewrite Nat2N.id.
        apply lookup_ge_None_2. rewrite Hlen_app. lia. }
      have Hgofilter_oob : filter (fun '(j, _) => (<[i0 := ()]> (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A))) !! j = Some ())
                                 (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) ++ [tb_alloc c])) =
        <[i0 := tb_alloc c]>
          (filter (fun '(j, _) => (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A)) !! j = Some ())
             (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz)))).
      { rewrite Hgo_data_oob.
        have Hlen2 : N.of_nat (length (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))) = N.of_nat (N.to_nat addr + sz).
        { apply (f_equal N.of_nat). exact Hlen_app. }
        rewrite Hlen2.
        apply (map_filter_insert_permute (gmap_of_list (cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz))) i0 (tb_alloc c)
          (fun '(j, _) => (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A)) !! j = Some ())
          (fun '(j, _) => (<[i0 := ()]> (live_locations (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) (allocator_insert c A))) !! j = Some ())).
        { rewrite lookup_insert. done. }
        { intro Hp. rewrite Hlive_none_oob in Hp. discriminate. }
        { move => j y Hjne.
          have Hjni : i0 <> j. { intro Hcc. apply Hjne. symmetry. exact Hcc. }
          split; intro Heq.
          - rewrite lookup_insert_ne in Heq; [ done | exact Hjni ].
          - rewrite lookup_insert_ne; [ exact Heq | exact Hjni ]. } }
      have Hgo_step_oob : gmap_of_cmem {| cmem_data := tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) (S sz); cmem_max_opt := cm.(cmem_max_opt) |} (allocator_insert c A) =
                      <[i0 := tb_alloc c]> (gmap_of_cmem {| cmem_data := tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz; cmem_max_opt := cm.(cmem_max_opt) |} (allocator_insert c A)).
      { unfold gmap_of_cmem.
        cbn [cmem_data cml_data].
        rewrite Hdata_oob.
        have Hdata_rec_oob : tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) (S sz) =
          {| cml_data := cml_data (tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) sz) ++ [tb_alloc c] |}.
        { rewrite /tmemb.
          apply (f_equal (fun (l0 : list tagged_byte) => {| cml_data := l0 |})).
          exact Hdata_oob. }
        rewrite Hdata_rec_oob.
        rewrite HliveS_oob.
        rewrite Hlen_app.
        exact Hgofilter_oob. }
      rewrite Hgo_step_oob.
      iMod (ghost_map_insert i0 (tb_alloc c) with "Hcmem") as "[Hcmem Helem]".
      { apply map_lookup_filter_None_2. left.
        rewrite gmap_of_list_lookup. unfold i0. rewrite Nat2N.id.
        apply lookup_ge_None_2. rewrite Hlen_app. lia. }
      iModIntro. iFrame.
    }
Qed.

Lemma ghost_map_alloc_block (cm : cmem) (A : allocator) (addr c n : N) :
  isSound_b A (cmem_data cm) ->
  A.(allocated) !! c = None ->
  (forall a_off, (addr <= a_off < addr + n)%N -> isfree a_off (cmem_data cm) A) ->
  N.to_nat addr <= length (cml_data (cmem_data cm)) ->
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm A) ==∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem {|
    cmem_data := {| cml_data := take (N.to_nat addr) (cml_data (cmem_data cm)) ++
        repeat {| tb_value := #00%byte; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n) ++
        drop (N.to_nat (addr + n)) (cml_data (cmem_data cm)) |};
    cmem_max_opt := cmem_max_opt cm |} (allocator_insert c A)) ∗
  wcs addr c Numeric (repeat #00%byte (N.to_nat n)).
Proof.
  intros Hsound Hfresh Hfree Hbound.
  iIntros "Hcmem".
  iMod (colalloc_transfer_rec cm A addr c Hsound Hfresh Hbound (N.to_nat n) with "Hcmem") as "[Hcmem Hwcs]".
  { intros a_off Ha. apply Hfree.
    destruct Ha as [Hge Hlt].
    split; [ exact Hge | ].
    rewrite (N2Nat.id n) in Hlt. exact Hlt. }
  have Hgo_end : gmap_of_cmem {| cmem_data := {| cml_data := take (N.to_nat addr) (cml_data (cmem_data cm)) ++
        repeat {| tb_value := #00%byte; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n) ++
        drop (N.to_nat (addr + n)) (cml_data (cmem_data cm)) |};
    cmem_max_opt := cm.(cmem_max_opt) |} (allocator_insert c A) =
    gmap_of_cmem {| cmem_data := tmemb (cmem_data cm) (N.to_nat addr) (tb_alloc c) (N.to_nat n);
      cmem_max_opt := cm.(cmem_max_opt) |} (allocator_insert c A).
  { unfold gmap_of_cmem.
    rewrite (N2Nat.inj_add addr n).
    unfold tmemb. unfold tb_alloc.
    done. }
  rewrite Hgo_end.
  iModIntro. iFrame.
Qed.

Lemma wcs_is_colload (ws : store_record) (addr : N) (col : N) (tag : btag) (bs : list byte) :
  length bs > 0 ->
  wcs addr col tag bs -∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem (s_cmems ws) (s_alls ws)) -∗
  ⌜read_colbytes (s_cmems ws) addr (length bs) =
    Some (map (λ b, {| tb_value := b; tb_color := Some col; tb_tag := tag |}) bs)⌝.
Proof.
  iIntros (Hlen) "Hwcs Hg".
  iAssert (∀ i, ⌜ i < length bs ⌝ -∗
    ⌜ cml_data (cmem_data (s_cmems ws)) !! N.to_nat (addr + N.of_nat i) =
      Some {| tb_value := nth i bs #00%byte; tb_color := Some col; tb_tag := tag |} ⌝)%I
    as "%Hseq".
  { iIntros (i) "%Hi".
    iDestruct (big_sepL_lookup with "Hwcs") as "Hwc" => //.
    destruct (nth_lookup_or_length bs i #00%byte) => //=; lia.
    iDestruct (ghost_map_lookup with "Hg Hwc") as "%Hlook".
    apply map_lookup_filter_Some in Hlook as [Hgmap _].
    rewrite gmap_of_list_lookup in Hgmap.
    iPureIntro.
    replace (N.to_nat (addr + N.of_nat i)) with (N.to_nat (N.of_nat (N.to_nat addr + i))); last by lia.
    rewrite Hgmap.
    reflexivity.
  }
  iPureIntro.
  unfold read_colbytes.
  set (n := length bs).
  replace n with (length (map (λ b, {| tb_value := b; tb_color := Some col; tb_tag := tag |}) bs)).
  2: { rewrite map_length. done. }
  apply those_map_Some. intros x Hx.
  rewrite map_length in Hx.
  unfold cm_lookup. rewrite nth_error_lookup.
  rewrite (Hseq x Hx). symmetry.
  rewrite list_lookup_fmap.
  destruct (nth_lookup_or_length bs x #00%byte) as [Hsome | Hle].
  - by rewrite Hsome /=.
  - exfalso; lia.
Qed.

Lemma wblock_is_read_colbytes (ws : store_record) (addr : N)
    (tbs : list tagged_byte) :
  length tbs > 0 ->
  wblock addr tbs -∗
  ghost_map_auth cmemGName 1
    (gmap_of_cmem (s_cmems ws) (s_alls ws)) -∗
  ⌜read_colbytes (s_cmems ws) addr (length tbs) = Some tbs⌝.
Proof.
  iIntros (Hlen) "Hblock Hg".
  iAssert (∀ i tb, ⌜tbs !! i = Some tb⌝ -∗
    ⌜cml_data (cmem_data (s_cmems ws)) !! N.to_nat (addr + N.of_nat i) =
      Some tb⌝)%I as "%Hseq".
  { iIntros (i tb) "%Htb".
    iDestruct (big_sepL_lookup with "Hblock") as "Helem"; first exact Htb.
    iDestruct (ghost_map_lookup with "Hg Helem") as "%Hlook".
    apply map_lookup_filter_Some in Hlook as [Hphysical _].
    rewrite gmap_of_list_lookup in Hphysical.
    iPureIntro.
    replace (N.to_nat (addr + N.of_nat i)) with
      (N.to_nat (N.of_nat (N.to_nat addr + i))); last by lia.
    exact Hphysical. }
  iPureIntro. unfold read_colbytes.
  apply those_map_Some. intros i Hi.
  destruct (lookup_lt_is_Some_2 tbs i Hi) as [tb Htb].
  unfold cm_lookup. rewrite nth_error_lookup (Hseq i tb Htb).
  by rewrite Htb.
Qed.

Lemma fold_lefti_data_cmem_update_some (orig : colored_memory_list) (addr : N) (col : N) (tag : btag)
    (k n : nat) (cm : colored_memory_list) (bs : bytes) :
  length cm.(cml_data) = length orig.(cml_data) ->
  (forall i, i < length bs ->
     exists tb, cm_lookup (addr + N.of_nat (k + n + i)) orig = Some tb) ->
  exists cm', fold_lefti_data
    (fun off dat_o b =>
       match dat_o with
       | None => None
       | Some dat => cmem_update (addr + N.of_nat (k + off))
                       {| tb_value := b; tb_color := Some col; tb_tag := tag |} dat
       end)
    bs n (Some cm) = Some cm'.
Proof.
  elim: bs k n cm => [|b bs IH] k n cm Hlen Hlook.
  - exists cm; by simpl.
  - have Hk0 := Hlook 0 (Nat.lt_0_succ (length bs)).
    have Hadd : k + n + 0 = k + n by lia.
    rewrite Hadd in Hk0.
    have Hlt0 : N.to_nat (addr + N.of_nat (k + n)) < length orig.(cml_data)
      := cm_lookup_in_bounds _ _ Hk0.
    have Hlt : N.to_nat (addr + N.of_nat (k + n)) < length cm.(cml_data).
    { rewrite Hlen; exact Hlt0. }
    have [cm0 [Hupd Hlen0]] :=
      cmem_update_in_bounds (addr + N.of_nat (k + n))
        {| tb_value := b; tb_color := Some col; tb_tag := tag |} cm Hlt.
    simpl.
    rewrite Hupd.
    apply (IH k (S n) cm0).
    + transitivity (length cm.(cml_data)); [exact Hlen0 | exact Hlen].
    + move=> j Hj.
      have Hsj := Hlook (S j) ltac:(simpl; lia).
      have Hshift : k + n + S j = k + S n + j by lia.
      rewrite Hshift in Hsj.
      exact Hsj.
Qed.

Lemma write_cmembytes_some (cm : cmem) (addr : N) (col : N) (tag : btag)
    (bs_old bs_new : bytes) :
  length bs_old = length bs_new ->
  (forall i, i < length bs_old ->
     exists tb, cm_lookup (addr + N.of_nat i) cm.(cmem_data) = Some tb) ->
  exists cm', write_cmembytes cm addr bs_new (Some col) tag = Some cm'.
Proof.
  move=> Hlen Hlook.
  unfold write_cmembytes.
  rewrite fold_lefti_eq_fold_lefti_data.
  have Hexists : exists cm', fold_lefti_data
      (fun off dat_o b =>
         match dat_o with
         | None => None
         | Some dat => cmem_update (addr + N.of_nat off)
                         {| tb_value := b; tb_color := Some col; tb_tag := tag |} dat
         end) bs_new 0 (Some (cmem_data cm)) = Some cm'.
  { apply (fold_lefti_data_cmem_update_some (cmem_data cm) addr col tag 0 0 (cmem_data cm) bs_new).
    - reflexivity.
    - move=> i Hi.
      have Hlt : i < length bs_old.
      { rewrite Hlen; exact Hi. }
      have Hadd : 0 + 0 + i = i by lia.
      rewrite Hadd.
      exact (Hlook i Hlt).
  }
  destruct Hexists as [dat Hfold].
  exists {| cmem_data := dat; cmem_max_opt := cm.(cmem_max_opt) |}.
  simpl in Hfold.
  rewrite Hfold.
  reflexivity.
Qed.

Lemma ghost_update_single (cm cm1 : cmem) (i : N) (x tb : tagged_byte) (a : allocator) :
  N.to_nat i < length (cml_data (cmem_data cm)) ->
  cmem_update i x (cmem_data cm) = Some (cmem_data cm1) ->
  isAllocOpt (tb_color x) a ->
  live_locations (cmem_data cm) a !! i = Some () ->
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm a) -∗
  ghost_map_elem cmemGName i (DfracOwn 1) tb ==∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm1 a) ∗
  ghost_map_elem cmemGName i (DfracOwn 1) x.
Proof.
  move=> Hlen Hupd Hallocx Hlive.
  iIntros "Hcmem Ht".
  have Hg : <[i := x]> (gmap_of_cmem cm a) = gmap_of_cmem cm1 a.
  { eapply gmap_of_cmem_insert.
    - exact Hlen.
    - exact Hupd.
    - exact Hallocx.
    - exact Hlive. }
  iMod (ghost_map_update x with "Hcmem Ht") as "[Hcmem Ht]".
  iModIntro.
  rewrite Hg.
  iFrame.
Qed.

Lemma wcs_is_colstore (ws : store_record) (addr : N) (col : N) (tag_old tag_new : btag)
    (bs_old bs_new : bytes) :
  length bs_old > 0 ->
  length bs_old = length bs_new ->
  wcs addr col tag_old bs_old -∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem (s_cmems ws) (s_alls ws)) -∗
  ⌜exists cm', write_cmembytes (s_cmems ws) addr bs_new (Some col) tag_new = Some cm'⌝.
Proof.
  iIntros (Hlen Heq) "Hwcs Hg".
  have Hlen' : (length bs_new > 0). lias.
  iAssert (∀ i, ⌜ i < length bs_old ⌝ -∗
    ⌜ cml_data (cmem_data (s_cmems ws)) !! N.to_nat (addr + N.of_nat i) =
      Some {| tb_value := nth i bs_old #00%byte; tb_color := Some col; tb_tag := tag_old |} ⌝)%I
    as "%Hseq".
  { iIntros (i) "%Hi".
    iDestruct (big_sepL_lookup with "Hwcs") as "Hwc" => //.
    instantiate (2 := i).
    instantiate (1 := nth i bs_old #00%byte).
    destruct (nth_lookup_or_length bs_old i #00%byte) => //=. lia.
    iDestruct (ghost_map_lookup with "Hg Hwc") as "%Hlook".
    apply map_lookup_filter_Some in Hlook as [Hgmap _].
    rewrite gmap_of_list_lookup in Hgmap.
    iPureIntro.
    replace (N.to_nat (addr + N.of_nat i)) with (N.to_nat (N.of_nat (N.to_nat addr + i))); last by lia.
    rewrite Hgmap.
    reflexivity.
  }
  iPureIntro.
  apply/write_cmembytes_some.
  { rewrite -Heq. reflexivity. }
  move=> i Hi.
  have Hseq' := Hseq i Hi.
  unfold cm_lookup.
  rewrite nth_error_lookup.
  eexists; exact Hseq'.
Qed.

Lemma wblock_is_colstore (ws : store_record) (addr : N)
    (tbs_old : list tagged_byte) (col : N) (tag_new : btag)
    (bs_new : bytes) :
  length tbs_old > 0 ->
  length tbs_old = length bs_new ->
  wblock addr tbs_old -∗
  ghost_map_auth cmemGName 1
    (gmap_of_cmem (s_cmems ws) (s_alls ws)) -∗
  ⌜exists cm', write_cmembytes (s_cmems ws) addr bs_new
      (Some col) tag_new = Some cm'⌝.
Proof.
  iIntros (Hpos Hlen) "Hblock Hcmem".
  iDestruct (wblock_is_read_colbytes with "Hblock Hcmem") as %Hread;
    first exact Hpos.
  iPureIntro. apply/(write_cmembytes_some (s_cmems ws) addr col tag_new
    (map tb_value tbs_old) bs_new); first by rewrite map_length.
  move=> i Hi.
  rewrite map_length in Hi.
  destruct (lookup_lt_is_Some_2 tbs_old i Hi) as [tb Htb].
  exists tb. eapply read_colbytes_nth_error; eauto.
  by rewrite nth_error_lookup.
Qed.

Lemma bits_length_t_length t v :
  types_agree t v -> length (bits v) = t_length t.
Proof.
  intros.
  destruct t => //=.
  1-4: unfold bits; destruct v => //=; destruct n => //=.
  unfold bits. destruct v => //=.
  unfold types_agree in H. destruct n => //=.
  by destruct HPB.
Qed.

Lemma wcs_cons addr col tag b bs :
  wcs addr col tag (b :: bs) ⊣⊢ (addr ↦[wc]{col}{tag} b ∗ wcs (addr + 1)%N col tag bs).
Proof.
  unfold wcs.
  iSplit.
  - iIntros "H". iDestruct (big_sepL_cons with "H") as "[Hb Hbs]".
    iEval (rewrite Nat.add_0_r N2Nat.id) in "Hb".
    iSplitL "Hb"; first iExact "Hb".
    iApply (big_sepL_impl with "Hbs").
    iIntros "!>" (k y Hk) "Hy".
    replace (N.to_nat addr + S k) with (N.to_nat (addr + 1)%N + k) by lia.
    iExact "Hy".
  - iIntros "[Hb Hbs]". rewrite big_sepL_cons.
    iSplitL "Hb".
    + iEval (rewrite Nat.add_0_r N2Nat.id).
      iExact "Hb".
    + iApply (big_sepL_impl with "Hbs").
      iIntros "!>" (k y Hk) "Hy".
      replace (N.to_nat (addr + 1)%N + k) with (N.to_nat addr + S k) by lia.
      iExact "Hy".
Qed.


Lemma ghost_map_update_big_cmem addr col old_tag new_tag bs_old bs_new cm cm' a :
  length bs_old = length bs_new ->
  write_cmembytes cm addr bs_new (Some col) new_tag = Some cm' ->
  isAlloc col a ->
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm a) -∗
  wcs addr col old_tag bs_old ==∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm' a) ∗ wcs addr col new_tag bs_new.
Proof.
  move: cm' cm addr bs_new.
  induction bs_old as [| b0 bs_old IH]; intros cm' cm addr bs_new Hlen Hwrite Halloc.
  - destruct bs_new as [| b' bs_new]; [ | by simpl in Hlen; discriminate ].
    iIntros "Hcmem Hws".
    unfold write_cmembytes in Hwrite.
    rewrite fold_lefti_eq_fold_lefti_data in Hwrite.
    cbn in Hwrite.
    inversion Hwrite; subst.
    have Hcm_eq : {| cmem_data := cmem_data cm; cmem_max_opt := cmem_max_opt cm |} = cm.
    { destruct cm. reflexivity. }
    rewrite Hcm_eq.
    iSplitL "Hcmem".
    + iModIntro. iFrame.
    + iModIntro. done.
  - destruct bs_new as [| b' bs_new]; [ by simpl in Hlen; discriminate | ].
    simpl in Hlen. injection Hlen as Hlen'.
    have [cm_mid [Hupd_head [Hmax Hwrite_tail]]] := write_cmembytes_cons_inv cm addr b' bs_new (Some col) new_tag cm' Hwrite.
    iIntros "Hcmem Hws".
    iDestruct (wcs_cons with "Hws") as "[Hhead Hws]".
    iDestruct (ghost_map_lookup with "Hcmem Hhead") as "%Hlook".
    apply map_lookup_filter_Some in Hlook.
    destruct Hlook as [_ Hlive].
    have Hinb : N.to_nat addr < length (cml_data (cmem_data cm)).
    { unfold cmem_update in Hupd_head.
      move: Hupd_head.
      case Hleb : (addr <? N.of_nat (length (cml_data (cmem_data cm))))%N.
      - move=> Hupd_head.
        apply N.ltb_lt in Hleb.
        apply (proj2 (N.compare_lt_iff addr (N.of_nat (length (cml_data (cmem_data cm)))))) in Hleb.
        apply Nat.compare_lt_iff.
        by rewrite -Hleb N2Nat.inj_compare Nat2N.id.
      - move=> Hupd_head. lias. }
    set (xnew := {| tb_value := b'; tb_color := Some col; tb_tag := new_tag |}).
    iMod (ghost_update_single cm cm_mid addr xnew {| tb_value := b0; tb_color := Some col; tb_tag := old_tag |} a Hinb Hupd_head Halloc Hlive with "Hcmem Hhead") as "[Hcmem Hhead]".
    iMod (IH cm' cm_mid (addr + 1)%N bs_new Hlen' Hwrite_tail Halloc with "Hcmem Hws") as "[Hcmem Hws]".
    iSplitR "Hhead Hws".
    + iModIntro. iFrame "Hcmem".
    + iModIntro. rewrite wcs_cons. iFrame.
Qed.

Lemma ghost_map_update_big_cmem_block addr col new_tag tbs_old bs_new cm cm' a :
  length tbs_old = length bs_new ->
  write_cmembytes cm addr bs_new (Some col) new_tag = Some cm' ->
  isAlloc col a ->
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm a) -∗
  wblock addr tbs_old ==∗
  ghost_map_auth cmemGName 1 (gmap_of_cmem cm' a) ∗
  wcs addr col new_tag bs_new.
Proof.
  move: cm' cm addr bs_new.
  induction tbs_old as [|tb tbs_old IH];
    intros cm' cm addr bs_new Hlen Hwrite Halloc.
  - destruct bs_new as [|b bs_new]; [|by simpl in Hlen; discriminate].
    iIntros "Hcmem Hblock".
    unfold write_cmembytes in Hwrite.
    rewrite fold_lefti_eq_fold_lefti_data in Hwrite.
    cbn in Hwrite. inversion Hwrite; subst.
    have Hcm_eq :
        {| cmem_data := cmem_data cm; cmem_max_opt := cmem_max_opt cm |} = cm.
    { destruct cm. reflexivity. }
    rewrite Hcm_eq. iModIntro. iFrame. done.
  - destruct bs_new as [|b bs_new]; [by simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen'.
    have [cm_mid [Hupd_head [Hmax Hwrite_tail]]] :=
      write_cmembytes_cons_inv cm addr b bs_new (Some col) new_tag cm' Hwrite.
    iIntros "Hcmem Hblock".
    iDestruct (wblock_cons with "Hblock") as "[Hhead Hblock]".
    iDestruct (ghost_map_lookup with "Hcmem Hhead") as %Hlook.
    apply map_lookup_filter_Some in Hlook as [_ Hlive].
    have Hinb : N.to_nat addr < length (cml_data (cmem_data cm)).
    { unfold cmem_update in Hupd_head.
      move: Hupd_head.
      case Hleb : (addr <? N.of_nat (length (cml_data (cmem_data cm))))%N.
      - move=> _. apply N.ltb_lt in Hleb. lia.
      - move=> Hcontra. discriminate. }
    set (xnew := {| tb_value := b; tb_color := Some col;
                    tb_tag := new_tag |}).
    iMod (ghost_update_single cm cm_mid addr xnew tb a Hinb Hupd_head
      Halloc Hlive with "Hcmem Hhead") as "[Hcmem Hhead]".
    iMod (IH cm' cm_mid (addr + 1)%N bs_new Hlen' Hwrite_tail Halloc
      with "Hcmem Hblock") as "[Hcmem Hblock]".
    iModIntro. iFrame "Hcmem". rewrite wcs_cons. iFrame.
Qed.

(* ================================================================= *)
(* wp_colload: numeric load (τ ≠ ptrt)                                *)
(* ================================================================= *)

Lemma wp_colload (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (col base size : N) (bs : list byte)
    (v : value) (f0 : frame) :
  t <> T_pointer ->
  length bs = t_length t ->
  wasm_deserialise bs t = v ->
  (ptr_col p = Some col) ->
  (▷ (wcs (ptr_addr p) col Numeric bs ∗ wall col base size -∗ Φ (immV [v])))%I ∗
  ↪[frame] f0 ∗ wcs (ptr_addr p) col Numeric bs ∗ wall col base size ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload t)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Ht Hlen Hdes Hc) "(HΦ & Hf0 & Hwcs & Hwall)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmem & Hall & ? & Hframe & ?)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Hall Hwall") as "%Hwall".

  have Hall_tbs : all (λ tb, (tb_color tb == Some col) && (tb_tag tb == Numeric))
    (map (λ b, {| tb_value := b; tb_color := Some col; tb_tag := Numeric |}) bs).
  { rewrite all_map; apply /allP => x; rewrite /preim /= => Hx; apply andb_true_iff; split; by apply /eqP. }

  iDestruct (wcs_is_colload with "Hwcs Hcmem") as "%Hcload".
  destruct (t); simpl in Hlen; destruct HPB; lias.

  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_const _], (ws, locs, winst), [].
    repeat split => //.
    eapply rm_colload_success; eauto.
    rewrite <- Hlen. apply Hcload.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.

    have Hcload_t : read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) =
      Some (map (λ b, {| tb_value := b; tb_color := Some col; tb_tag := Numeric |}) bs).
    { by rewrite <- Hlen. }

    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colload_success => //=);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst.
    iSpecialize ("HΦ" with "[$Hwcs $Hwall]").
    iFrame. simpl. iSplit; last done.

    assert ( [seq tb_value i | i <- map (λ b : byte, {| tb_value := b; tb_color := Some col; tb_tag := Numeric |}) bs] = bs) as Hbid.
    { erewrite map_map => //=.
      simpl.
      by rewrite map_id. }
    rewrite Hbid.

    destruct (wasm_deserialise bs t); simpl; iExact "HΦ".
Qed.

(* ================================================================= *)
(* wp_colload_ptr: pointer load (τ = ptrt)                            *)
(* ================================================================= *)

Lemma wp_colload_ptr (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (col base size : N) (bs : list byte)
    (v : value) (f0 : frame) :
  length bs = t_length T_pointer ->
  isAlign p ->
  ptr_col p = Some col ->
  wasm_deserialise bs T_pointer = v ->
  (▷ (wcs (ptr_addr p) col Pointer bs ∗ wall col base size -∗ Φ (immV [v])))%I ∗
  ↪[frame] f0 ∗ wcs (ptr_addr p) col Pointer bs ∗ wall col base size ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hlen Halign Hc Hdes) "(HΦ & Hf0 & Hwcs & Hwall)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmem & Hall & ? & Hframe & ?)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Hall Hwall") as "%Hwall".

  have Hall_tbs : all (λ tb, (tb_color tb == Some col) && (tb_tag tb == Pointer))
    (map (λ b, {| tb_value := b; tb_color := Some col; tb_tag := Pointer |}) bs).
  { rewrite all_map; apply /allP => x; rewrite /preim /= => Hx; apply andb_true_iff; split; by apply /eqP. }

  iDestruct (wcs_is_colload with "Hwcs Hcmem") as "%Hcload".
  { simpl in Hlen; destruct HPB; rewrite Hlen; clear - size_is_not_zero;
    rewrite /color_ptr.pointer_size; move /eqP in size_is_not_zero; lias. }

  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_const _], (ws, locs, winst), [].
    repeat split => //.
    eapply rm_colload_ptr_success; eauto.
    rewrite <- Hlen. apply Hcload.

  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.

    have Hcload_t : read_colbytes (s_cmems ws) (ptr_addr p) (t_length T_pointer) =
      Some (map (λ b, {| tb_value := b; tb_color := Some col; tb_tag := Pointer |}) bs).
    { by rewrite <- Hlen. }

    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colload_ptr_success => //=);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst.
    iSpecialize ("HΦ" with "[$Hwcs $Hwall]").
    iFrame. simpl. iSplit; last done.

    assert ( [seq tb_value i | i <- map (λ b : byte, {| tb_value := b; tb_color := Some col; tb_tag := Pointer |}) bs] = bs) as Hbid.
    { erewrite map_map => //=.
      simpl.
      by rewrite map_id. }
    rewrite Hbid.

    destruct (wasm_deserialise bs T_pointer); simpl; iExact "HΦ".
Qed.

(* ================================================================= *)
(* Failure rules for colload                                           *)
(* ================================================================= *)

Lemma wp_colload_fail_null (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (f0 : frame) :
  is_null p ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload t)] @ s; E
  {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hnull) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmems & Hall & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colload_failure => //.
    left. done.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
        last (eapply rm_colload_failure => //; left; done);
        try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

Lemma dead_color_is_freed (A : allocator) (c : N) :
  retired_auth A -∗ dead_color c -∗ ⌜ isFreed c A ⌝.
Proof.
  iIntros "Hret Hdead".
  iDestruct (ghost_map_lookup with "Hret Hdead") as %Hlookup.
  apply gmap_of_retired_lookup in Hlookup.
  done.
Qed.

Lemma wp_colload_fail_dead (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (col : N) (f0 : frame) :
  ptr_col p = Some col ->
  (▷ (dead_color col -∗ Φ trapV) ∗ ↪[frame] f0 ∗ dead_color col ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload t)] @ s; E
  {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hcol) "(HΦ & Hf0 & #Hdead)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as
    "(? & ? & ? & ? & ? & ? & Hframe & ? & ? & ? & ? & Hret & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (dead_color_is_freed with "Hret Hdead") as %Hfreed.
  have Hnotalloc : ~ isAlloc col (s_alls ws).
  { unfold isFreed in Hfreed. unfold isAlloc. congruence. }
  have Hfailure : forall c, ptr_col p = Some c ->
      ~ isAlloc c (s_alls ws) \/
      (forall tbs,
        read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) = Some tbs ->
        ~ all (fun tb => (tb_color tb == Some c) &&
          (tb_tag tb == match t with T_pointer => Pointer | _ => Numeric end)) tbs).
  { move=> c Hc. left. have -> : c = col by congruence. exact Hnotalloc. }
  iSplit.
  - iPureIntro. destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colload_failure => //. by do 3 right.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & Hme) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colload_failure => //; by do 3 right);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst. iFrame. simpl.
    iSplit; first done. iSplit; last done.
    iApply "HΦ". iExact "Hdead".
Qed.

Lemma wp_colload_fail_tag (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (col : N) (tbs : list tagged_byte)
    (f0 : frame) :
  ptr_col p = Some col ->
  length tbs = t_length t ->
  length tbs > 0 ->
  ~ all (fun tb => (tb_color tb == Some col) &&
    (tb_tag tb == match t with T_pointer => Pointer | _ => Numeric end)) tbs ->
  (▷ (wblock (ptr_addr p) tbs -∗ Φ trapV) ∗ ↪[frame] f0 ∗
     wblock (ptr_addr p) tbs ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload t)] @ s; E
  {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hcol Hlen Hpos Hbad) "(HΦ & Hf0 & Hblock)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as
    "(? & ? & ? & Hcm & ? & ? & Hframe & ? & ? & ? & ? & ? & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (wblock_is_read_colbytes with "Hblock Hcm") as %Hread;
    first exact Hpos.
  have Hfailure : forall c, ptr_col p = Some c ->
      ~ isAlloc c (s_alls ws) \/
      (forall tbs',
        read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) = Some tbs' ->
        ~ all (fun tb => (tb_color tb == Some c) &&
          (tb_tag tb == match t with T_pointer => Pointer | _ => Numeric end)) tbs').
  { move=> c Hc. right. move=> tbs' Hread'.
    have -> : c = col by congruence.
    rewrite -Hlen in Hread'. rewrite Hread in Hread'.
    by inversion Hread'; subst tbs'. }
  iSplit.
  - iPureIntro. destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colload_failure => //. by do 3 right.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & Hme) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colload_failure => //; by do 3 right);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst. iFrame. simpl.
    iSplit; first done. iSplit; last done.
    iApply "HΦ". iExact "Hblock".
Qed.

Lemma wp_colload_fail_bounds (s : stuckness) (E : coPset)
    (Φ : val -> iProp Σ) (p : pointer) (t : value_type) (col base size : N)
    (tbs : list tagged_byte) (f0 : frame) :
  ptr_col p = Some col ->
  N.of_nat (length tbs) = size ->
  all (fun tb => tb_color tb == Some col) tbs ->
  t_length t > 0 ->
  ~ (base <= ptr_addr p /\
     ptr_addr p + N.of_nat (t_length t) <= base + size)%N ->
  (▷ (wall col base size -∗ wblock base tbs -∗ Φ trapV) ∗
     ↪[frame] f0 ∗ wall col base size ∗ wblock base tbs ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload t)] @ s; E
  {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hcol Hlen Hcolors Hpos Hbounds)
    "(HΦ & Hf0 & Hwall & Hblock)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as
    "(? & ? & ? & Hcm & Hall & ? & Hframe & ? & ? & ? & ? & ? & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Hall Hwall") as %Halloc.
  iDestruct (ghost_map_lookup with "Hall Hwall") as %Hmetadata.
  rewrite (gmap_of_allocator_lookup_true (s_cmems ws) Halloc) in Hmetadata.
  have Halloc_base : alloc_base (s_cmems ws) col = base by congruence.
  have Halloc_size : alloc_size (s_cmems ws) col = N.of_nat (length tbs)
    by congruence.
  iDestruct (wblock_matches_cmem with "Hcm Hblock") as %Hmatches.
  have Hslice : take (length tbs)
      (drop (N.to_nat base) (cml_data (cmem_data (s_cmems ws)))) = tbs.
  { apply block_lookups_determine_slice. move=> j tb Htb.
    have Hphysical := Hmatches j tb Htb.
    rewrite gmap_of_list_lookup in Hphysical.
    replace (N.to_nat base + j) with
      (N.to_nat (base + N.of_nat j)) by lia.
    exact Hphysical. }
  have Hextent := color_extent_exact (s_cmems ws) col base tbs
    Halloc_base Halloc_size Hcolors Hslice.
  have Hfailure :
      read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) = None \/
      (forall c, ptr_col p = Some c ->
        ~ isAlloc c (s_alls ws) \/
        (forall loaded,
          read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) = Some loaded ->
          ~ all (fun tb => (tb_color tb == Some c) &&
            (tb_tag tb == match t with T_pointer => Pointer | _ => Numeric end)) loaded)).
  { destruct (read_colbytes (s_cmems ws) (ptr_addr p) (t_length t))
      as [loaded|] eqn:Hread; last by left.
    right. move=> c Hc. right. move=> loaded' Hread'.
    have -> : c = col by congruence.
    inversion Hread'; subst loaded'; clear Hread'.
    move=> Hloaded.
    have Hloaded_colors : all (fun tb => tb_color tb == Some col) loaded.
    { have Hproject : forall xs : list tagged_byte,
          all (fun tb => (tb_color tb == Some col) &&
            (tb_tag tb == match t with T_pointer => Pointer | _ => Numeric end)) xs ->
          all (fun tb => tb_color tb == Some col) xs.
      { move=> xs. induction xs as [|tb xs IH] => //=.
        move=> /andP [/andP [Hcolor _] Htail].
        apply/andP. split; first exact Hcolor. exact (IH Htail). }
      exact (Hproject loaded Hloaded). }
    have Hloaded_len : length loaded = t_length t.
    { unfold read_colbytes in Hread.
      have Hthose := those_length
        (fun off => cm_lookup (ptr_addr p + N.of_nat off)
          (cmem_data (s_cmems ws))) (iota 0 (t_length t)) loaded Hread.
      by rewrite iota_length in Hthose. }
    destruct (decide ((ptr_addr p < base \/
      base + N.of_nat (length tbs) <= ptr_addr p)%N))
      as [Houtside|Hinside].
    - destruct (lookup_lt_is_Some_2 loaded 0) as [tb Htb]; first lia.
      have Hphysical := read_colbytes_nth_error (s_cmems ws)
        (ptr_addr p) (t_length t) 0 loaded tb Hread Hpos.
      specialize (Hphysical ltac:(by rewrite nth_error_lookup; exact Htb)).
      unfold cm_lookup in Hphysical. rewrite nth_error_lookup in Hphysical.
      have Hcolor := all_color_lookup col loaded 0 tb Hloaded_colors Htb.
      have Hrange := (proj1 (Hextent _ _ Hphysical)) Hcolor.
      simpl in Hrange. lia.
    - have Hinside' :
        (base <= ptr_addr p < base + N.of_nat (length tbs))%N by lia.
      set (j := N.to_nat (base + N.of_nat (length tbs) - ptr_addr p)).
      have Hj : j < t_length t by subst j; lia.
      destruct (lookup_lt_is_Some_2 loaded j) as [tb Htb]; first by rewrite Hloaded_len.
      have Hphysical := read_colbytes_nth_error (s_cmems ws)
        (ptr_addr p) (t_length t) j loaded tb Hread Hj.
      specialize (Hphysical ltac:(by rewrite nth_error_lookup; exact Htb)).
      unfold cm_lookup in Hphysical. rewrite nth_error_lookup in Hphysical.
      have Hcolor := all_color_lookup col loaded j tb Hloaded_colors Htb.
      have Hrange := (proj1 (Hextent _ _ Hphysical)) Hcolor.
      subst j. lia. }
  iSplit.
  - iPureIntro. destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colload_failure => //. by do 2 right.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & Hme) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colload_failure => //; by do 2 right);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst. iFrame. simpl.
    iSplit; first done. iSplit; last done.
    iApply ("HΦ" with "Hwall Hblock").
Qed.

Lemma wp_colload_fail_oob (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
  (p : pointer) (t : value_type) (f0 : frame) :
  (∀ (ws : store_record), (ptr_addr p + N.of_nat (t_length t) > cmem_length (s_cmems ws))%N) ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload t)] @ s; E
  {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hoob) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmems & Hall & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colload_failure => //.

    right; right; left;
    unfold read_colbytes;
    specialize (Hoob ws);
    apply: colload_None_read_colbytes_None; [
     destruct t; [ .. | destruct HPB; simpl; exact size_is_not_zero ] ; simpl; lias |
     unfold colload;
      case Hl: (ptr_addr p + N.of_nat (t_length t) <=? cmem_length (s_cmems ws))%N; [ apply N.leb_le in Hl; lia | reflexivity ] ].

  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
        try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.

    2: eapply rm_colload_failure => //;
    right; right; left;
    unfold read_colbytes;
    specialize (Hoob ws);
    apply: colload_None_read_colbytes_None; [
    destruct t; [ .. | destruct HPB; simpl; exact size_is_not_zero ] ; simpl; lias |
        unfold colload;
        case Hl: (ptr_addr p + N.of_nat (t_length t) <=? cmem_length (s_cmems ws))%N; [ apply N.leb_le in Hl; lia | reflexivity ] ].

    inversion H; subst;
    iFrame; simpl;
    iDestruct "HΦ" as "[HΦ Hf0]"; iFrame.
Qed.

Lemma wp_colload_fail_align (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (f0 : frame) :
  ~ isAlign p ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)] @ s; E
  {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hnull) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmems & Hall & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colload_failure => //.
    right. left. done.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
        last (eapply rm_colload_failure => //; right; left; done);
        try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

(* ================================================================= *)
(* wp_colstore: numeric store (τ ≠ ptrt)                              *)
(* ================================================================= *)

Lemma wp_colstore (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (col base size : N)
    (old_tbs : list tagged_byte) (v : value) (f0 : frame) :
  t <> T_pointer ->
  ptr_col p = Some col ->
  length old_tbs = t_length t ->
  all (fun tb => tb_color tb == Some col) old_tbs ->
  types_agree t v -> (* implies length |v| = length old_bytes *)
  (▷ (wcs (ptr_addr p) col Numeric (bits v) ∗ wall col base size -∗ Φ (immV [])))%I ∗
  ↪[frame] f0 ∗ wblock (ptr_addr p) old_tbs ∗ wall col base size ⊢
  WP [AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore t)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Ht Hcol Hlen Hcolors Hty) "(HΦ & Hf0 & Hblock & Hwall)".
  iApply wp_lift_atomic_step => //=. destruct v => //.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmem & Hall & ? & Hframe & ? & ? & ? & ? & Hret & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Hall Hwall") as "%Hwall".

  iDestruct (wblock_is_read_colbytes with "Hblock Hcmem") as %Hcload.
  { rewrite Hlen. destruct t; simpl; try lia. exfalso. by apply Ht. }
  iDestruct (wblock_is_colstore with "Hblock Hcmem") as %Hcstore.
  { rewrite Hlen. destruct t; simpl; try lia. exfalso. by apply Ht. }
  { rewrite Hlen. symmetry. erewrite length_bits; eauto. }

  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    destruct Hcstore as [cm' Hcstore'].
    eexists [_], [], (upd_s_cmem ws cm', locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colstore_success; eauto;
    rewrite <- Hlen; exact Hcload.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct Hcstore as [cm' Hcstore'].
    have Hbitslen : length (bits v) = length old_tbs.
    { rewrite (length_bits v t Hty). exact (Logic.eq_sym Hlen). }
    have Hallocmap :
        gmap_of_allocator (s_cmems ws) (s_alls ws) =
        gmap_of_allocator cm' (s_alls ws).
    { eapply gmap_of_allocator_write_preserved; first exact Hcstore'.
      move=> i tb Hi Hlookup.
      have Hiold : i < length old_tbs by rewrite -Hbitslen; exact Hi.
      destruct (lookup_lt_is_Some_2 old_tbs i Hiold) as [oldtb Htb].
      have Hexpected :
          cm_lookup (ptr_addr p + N.of_nat i) (cmem_data (s_cmems ws)) =
          Some oldtb.
      { eapply read_colbytes_nth_error.
        - exact Hcload.
        - exact Hiold.
        - by rewrite nth_error_lookup. }
      rewrite Hlookup in Hexpected. inversion Hexpected; subst oldtb.
      exact (all_color_lookup col old_tbs i _ Hcolors Htb). }
    iMod (ghost_map_update_big_cmem_block (ptr_addr p) col Numeric old_tbs (bits v)
            (s_cmems ws) cm' (s_alls ws) with "Hcmem Hblock") as "[Hcmem Hwcs]".
    { rewrite Hlen. symmetry. erewrite length_bits; eauto. }
    { exact Hcstore'. }
    { exact Hwall. }
    iModIntro. prim_split κ HStep H.
    eapply reduce_det in H as [Hc | [(? & Hfirst & ?) | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                              Hfirst3 & Hσ0 & Hme)]]];
                                              last (eapply rm_colstore_success => //=);
                                              try by rewrite first_instr_colstore in Hfirst;
    discriminate.
    inversion Hc ; subst; clear Hc => /=.
    rewrite -Hallocmap.
    iFrame.
    iSplit.
    iPureIntro.
    eapply (reduce_preserves_wellformedness (f := {| f_inst := inst'; f_locs := locs' |})).
    exact HWF. eapply rm_colstore_success => //=; eauto.
    rewrite <- Hlen; exact Hcload.
    iApply "HΦ"; iFrame.
    rewrite <- Hlen; exact Hcload.
Qed.

(* ================================================================= *)
(* wp_colstore_ptr: pointer store (τ = ptrt)                          *)
(* ================================================================= *)

Lemma wp_colstore_ptr (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (col base size : N)
    (old_tbs : list tagged_byte) (v : value) (f0 : frame) :
  isAlign p ->
  ptr_col p = Some col ->
  length old_tbs = t_length T_pointer ->
  all (fun tb => tb_color tb == Some col) old_tbs ->
  types_agree T_pointer v -> (* implies length |v| = length old_bytes *)
  (▷ (wcs (ptr_addr p) col Pointer (bits v) ∗ wall col base size -∗ Φ (immV [])))%I ∗
  ↪[frame] f0 ∗ wblock (ptr_addr p) old_tbs ∗ wall col base size ⊢
  WP [AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_pointer)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Halign Hcol Hlen Hcolors Hty) "(HΦ & Hf0 & Hblock & Hwall)".
  iApply wp_lift_atomic_step => //=. destruct v => //.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmem & Hall & ? & Hframe & ? & ? & ? & ? & Hret & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Hall Hwall") as "%Hwall".
  iDestruct (wblock_is_read_colbytes with "Hblock Hcmem") as %Hcload.
  { rewrite Hlen. have Hpos := @size_is_not_zero HPB.
    rewrite nat_bin in Hpos. move/ssrnat.ltP in Hpos.
    unfold t_length. by rewrite nat_bin. }
  iDestruct (wblock_is_colstore with "Hblock Hcmem") as %Hcstore.
  { rewrite Hlen. have Hpos := @size_is_not_zero HPB.
    rewrite nat_bin in Hpos. move/ssrnat.ltP in Hpos.
    unfold t_length. by rewrite nat_bin. }
  { rewrite Hlen. symmetry. erewrite length_bits; eauto. }
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    destruct Hcstore as [cm' Hcstore'].
    eexists [_], [], (upd_s_cmem ws cm', locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colstore_ptr_success; eauto.
    rewrite <- Hlen; exact Hcload.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct Hcstore as [cm' Hcstore'].
    have Hbitslen : length (bits v) = length old_tbs.
    { rewrite (length_bits v T_pointer Hty). exact (Logic.eq_sym Hlen). }
    have Hallocmap :
        gmap_of_allocator (s_cmems ws) (s_alls ws) =
        gmap_of_allocator cm' (s_alls ws).
    { eapply gmap_of_allocator_write_preserved; first exact Hcstore'.
      move=> i tb Hi Hlookup.
      have Hiold : i < length old_tbs by rewrite -Hbitslen; exact Hi.
      destruct (lookup_lt_is_Some_2 old_tbs i Hiold) as [oldtb Htb].
      have Hexpected :
          cm_lookup (ptr_addr p + N.of_nat i) (cmem_data (s_cmems ws)) =
          Some oldtb.
      { eapply read_colbytes_nth_error.
        - exact Hcload.
        - exact Hiold.
        - by rewrite nth_error_lookup. }
      rewrite Hlookup in Hexpected. inversion Hexpected; subst oldtb.
      exact (all_color_lookup col old_tbs i _ Hcolors Htb). }
    iMod (ghost_map_update_big_cmem_block (ptr_addr p) col Pointer old_tbs (bits v)
            (s_cmems ws) cm' (s_alls ws) with "Hcmem Hblock") as "[Hcmem Hwcs]".
    { rewrite Hlen. symmetry. erewrite length_bits; eauto. }
    { exact Hcstore'. }
    { exact Hwall. }
    iModIntro. prim_split κ HStep H.
    eapply reduce_det in H as [Hc | [(? & Hfirst & ?) | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                              Hfirst3 & Hσ0 & Hme)]]];
                                              last (eapply rm_colstore_ptr_success => //=);
                                              try by rewrite first_instr_colstore in Hfirst;
    discriminate.
    inversion Hc ; subst; clear Hc => /=.
    rewrite -Hallocmap.
    iFrame.
    iSplit.
    iPureIntro.
    eapply (reduce_preserves_wellformedness (f := {| f_inst := inst'; f_locs := locs' |})).
    exact HWF. eapply rm_colstore_ptr_success => //=; eauto; destruct HPB.
    simpl in Hlen |- *; rewrite <- Hlen; exact Hcload.
    iApply "HΦ"; iFrame.
    simpl in Hlen |- *; rewrite <- Hlen; exact Hcload.
Qed.

(* ================================================================= *)
(* Failure rules for colstore                                          *)
(* ================================================================= *)

Lemma wp_colstore_fail_bounds (s : stuckness) (E : coPset)
    (Φ : val -> iProp Σ) (p : pointer) (t : value_type) (v : value)
    (col base size : N) (tbs : list tagged_byte) (f0 : frame) :
  ptr_col p = Some col ->
  N.of_nat (length tbs) = size ->
  all (fun tb => tb_color tb == Some col) tbs ->
  t_length t > 0 ->
  ~ (base <= ptr_addr p /\
     ptr_addr p + N.of_nat (t_length t) <= base + size)%N ->
  (▷ (wall col base size -∗ wblock base tbs -∗ Φ trapV) ∗
     ↪[frame] f0 ∗ wall col base size ∗ wblock base tbs ⊢
  WP [AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore t)] @ s; E
  {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hcol Hlen Hcolors Hpos Hbounds)
    "(HΦ & Hf0 & Hwall & Hblock)".
  iApply wp_lift_atomic_step => //=. destruct v => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as
    "(? & ? & ? & Hcm & Hall & ? & Hframe & ? & ? & ? & ? & ? & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hf0.
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Hall Hwall") as %Halloc.
  iDestruct (ghost_map_lookup with "Hall Hwall") as %Hmetadata.
  rewrite (gmap_of_allocator_lookup_true (s_cmems ws) Halloc) in Hmetadata.
  have Halloc_base : alloc_base (s_cmems ws) col = base by congruence.
  have Halloc_size : alloc_size (s_cmems ws) col = N.of_nat (length tbs)
    by congruence.
  iDestruct (wblock_matches_cmem with "Hcm Hblock") as %Hmatches.
  have Hslice : take (length tbs)
      (drop (N.to_nat base) (cml_data (cmem_data (s_cmems ws)))) = tbs.
  { apply block_lookups_determine_slice. move=> j tb Htb.
    have Hphysical := Hmatches j tb Htb.
    rewrite gmap_of_list_lookup in Hphysical.
    replace (N.to_nat base + j) with
      (N.to_nat (base + N.of_nat j)) by lia.
    exact Hphysical. }
  have Hextent := color_extent_exact (s_cmems ws) col base tbs
    Halloc_base Halloc_size Hcolors Hslice.
  have Hfailure :
      read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) = None \/
      (forall c, ptr_col p = Some c ->
        ~ isAlloc c (s_alls ws) \/
        (forall loaded,
          ptr_col p = Some c ->
          read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) = Some loaded ->
          ~ all (fun tb => tb_color tb == Some c) loaded \/
          write_cmembytes (s_cmems ws) (ptr_addr p) (bits v)
            (ptr_col p)
            (match t with T_pointer => Pointer | _ => Numeric end) = None)).
  { destruct (read_colbytes (s_cmems ws) (ptr_addr p) (t_length t))
      as [loaded|] eqn:Hread; last by left.
    right. move=> c Hc. right. move=> loaded' _ Hread'. left.
    have -> : c = col by congruence.
    inversion Hread'; subst loaded'; clear Hread'.
    move=> Hloaded.
    have Hloaded_len : length loaded = t_length t.
    { unfold read_colbytes in Hread.
      have Hthose := those_length
        (fun off => cm_lookup (ptr_addr p + N.of_nat off)
          (cmem_data (s_cmems ws))) (iota 0 (t_length t)) loaded Hread.
      by rewrite iota_length in Hthose. }
    destruct (decide ((ptr_addr p < base \/
      base + N.of_nat (length tbs) <= ptr_addr p)%N))
      as [Houtside|Hinside].
    - destruct (lookup_lt_is_Some_2 loaded 0) as [tb Htb]; first lia.
      have Hphysical := read_colbytes_nth_error (s_cmems ws)
        (ptr_addr p) (t_length t) 0 loaded tb Hread Hpos.
      specialize (Hphysical ltac:(by rewrite nth_error_lookup; exact Htb)).
      unfold cm_lookup in Hphysical. rewrite nth_error_lookup in Hphysical.
      have Hcolor := all_color_lookup col loaded 0 tb Hloaded Htb.
      have Hrange := (proj1 (Hextent _ _ Hphysical)) Hcolor.
      simpl in Hrange. lia.
    - have Hinside' :
        (base <= ptr_addr p < base + N.of_nat (length tbs))%N by lia.
      set (j := N.to_nat (base + N.of_nat (length tbs) - ptr_addr p)).
      have Hj : j < t_length t by subst j; lia.
      destruct (lookup_lt_is_Some_2 loaded j) as [tb Htb];
        first by rewrite Hloaded_len.
      have Hphysical := read_colbytes_nth_error (s_cmems ws)
        (ptr_addr p) (t_length t) j loaded tb Hread Hj.
      specialize (Hphysical ltac:(by rewrite nth_error_lookup; exact Htb)).
      unfold cm_lookup in Hphysical. rewrite nth_error_lookup in Hphysical.
      have Hcolor := all_color_lookup col loaded j tb Hloaded Htb.
      have Hrange := (proj1 (Hextent _ _ Hphysical)) Hcolor.
      subst j. lia. }
  iSplit.
  - iPureIntro. destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=. repeat split => //.
    eapply rm_colstore_failure => //. by do 2 right.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & Hme) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colstore_failure => //; by do 2 right);
      try by rewrite first_instr_colstore in Hfirst; discriminate.
    inversion H; subst. iFrame. simpl.
    iSplit; first done. iSplit; last done.
    iApply ("HΦ" with "Hwall Hblock").
Qed.

Lemma wp_colstore_fail_null (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (v : value) (f0 : frame) :
  is_null p ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore t)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hnull) "HΦ".
  iApply wp_lift_atomic_step => //=. destruct v => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colstore_failure => //.
    left. done.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colstore_failure => //; left; done);
      try by (rewrite first_instr_colstore in Hfirst; discriminate).
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

Lemma wp_colstore_fail_oob (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (v : value) (f0 : frame) :
  (∀ (ws : store_record), (ptr_addr p + N.of_nat (t_length t) > cmem_length (s_cmems ws))%N) ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore t)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hoob) "HΦ".
  iApply wp_lift_atomic_step => //=. destruct v => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colstore_failure => //.
    right; right; left.
    specialize (Hoob ws).
    apply: colload_None_read_colbytes_None; [
    destruct t; [ .. | destruct HPB; simpl; exact size_is_not_zero ] ; simpl; lias |
        unfold colload;
        case Hl: (ptr_addr p + N.of_nat (t_length t) <=? cmem_length (s_cmems ws))%N; [ apply N.leb_le in Hl; lia | reflexivity ] ].
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colstore_failure => //; right; right; left;
        specialize (Hoob ws);
        apply: colload_None_read_colbytes_None; [
        destruct t; [ .. | destruct HPB; simpl; exact size_is_not_zero ] ; simpl; lias |
            unfold colload;
            case Hl: (ptr_addr p + N.of_nat (t_length t) <=? cmem_length (s_cmems ws))%N; [ apply N.leb_le in Hl; lia | reflexivity ] ]);
      try by rewrite first_instr_colstore in Hfirst; discriminate.
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

Lemma wp_colstore_fail_align (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (v : value) (f0 : frame) :
  ~ isAlign p ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_pointer)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Halign) "HΦ".
  iApply wp_lift_atomic_step => //=. destruct v => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold reducible, language.prim_step => /=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colstore_failure => //.
    right. left. split; done.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [ H | [ (? & Hfirst & Hme) | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colstore_failure => //; right; left; split; done);
      try by rewrite first_instr_colstore in Hfirst; discriminate.
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

Lemma wp_colstore_fail_dead (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (t : value_type) (v : value) (col : N) (f0 : frame) :
  ptr_col p = Some col ->
  (▷ (dead_color col -∗ Φ trapV) ∗ ↪[frame] f0 ∗ dead_color col ⊢
  WP [AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore t)] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hcol) "(HΦ & Hf0 & #Hdead)".
  iApply wp_lift_atomic_step => //=. destruct v => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as
    "(? & ? & ? & ? & ? & ? & Hframe & ? & ? & ? & ? & Hret & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (dead_color_is_freed with "Hret Hdead") as %Hfreed.
  have Hnotalloc : ~ isAlloc col (s_alls ws).
  { unfold isFreed in Hfreed. unfold isAlloc. congruence. }
  have Hfailure : forall c, ptr_col p = Some c ->
      ~ isAlloc c (s_alls ws) \/
      (forall tbs,
        ptr_col p = Some c ->
        read_colbytes (s_cmems ws) (ptr_addr p) (t_length t) = Some tbs ->
        ~ all (fun tb => tb_color tb == Some c) tbs \/
        write_cmembytes (s_cmems ws) (ptr_addr p) (bits v) (ptr_col p)
          (match t with T_pointer => Pointer | _ => Numeric end) = None).
  { move=> c Hc. left. have -> : c = col by congruence. exact Hnotalloc. }
  iSplit.
  - iPureIntro. destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colstore_failure => //. by do 3 right.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & Hme) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colstore_failure => //; by do 3 right);
      try by rewrite first_instr_colstore in Hfirst; discriminate.
    inversion H; subst. iFrame. simpl.
    iSplit; first done. iSplit; last done.
    iApply "HΦ". iExact "Hdead".
Qed.

(* ================================================================= *)
(* wp_colalloc                                                        *)
(* ================================================================= *)

Lemma wp_colalloc (s : stuckness) (E : coPset) (n : i32) (Φ : val -> iProp Σ)
    (f0 : frame) :
  (▷ (∀ w, (∃ p, ⌜w = immV [VAL_pointer p]⌝ ∗
    (⌜is_null p⌝ ∨
     (∃ col, ⌜ptr_col p = Some col⌝ ∗ ⌜ptr_freeable p = true⌝ ∗
       wall col
         (alloc_result_base (ptr_addr p) (Wasm_int.N_of_uint i32m n))
         (Wasm_int.N_of_uint i32m n) ∗
        live_color col ∗
        wcs (ptr_addr p) col Numeric (repeat #00%byte (N.to_nat (Wasm_int.N_of_uint i32m n))))))
    -∗ Φ w))%I ∗
  ↪[frame] f0 ⊢
  WP [AI_const (VAL_int32 n); AI_basic BI_colalloc] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }}.
Proof.
  iIntros "(HΦ & Hf0)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcmem & Hall & ? & Hframe & ? & ? & ? & ? & Hret & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.

  iSplit.
  - iPureIntro.
    destruct s => //=.
    unfold language.reducible, language.prim_step => /=.
    eexists [_], [AI_const _], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by eapply rm_colalloc_failure.
  - iIntros "!>" (es σ2 efs HStep).
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.

    remember [AI_basic (BI_const (NVAL_int32 n)) ; AI_basic BI_colalloc] as es0.
    remember {| f_locs := locs ; f_inst := winst |} as f.
    remember {| f_locs := locs' ; f_inst := inst' |} as f'.
    rewrite (separate1 (AI_basic _)) in Heqes0. 
    induction H ; try by inversion Heqes0 ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    destruct H ; try by inversion Heqes0 ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    { destruct H ; try by inversion Heqes0 ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      rewrite Heqes0 in H0.
      filled_trap H0 Hxl1. }
    { (* success *)
      inversion Heqes0 ; subst n0 ; clear Heqes0.
      subst.
      inversion H2. subst. simpl.
      have Hsoundb : isSound_b (s_alls s0) (cmem_data (s_cmems s0)).
      { exact (proj2 HWF). }
      have Hfreshb : (s_alls s0).(allocated) !! c = None.
      { eapply fresh_col_none; [ exact (proj1 HWF) | exact H0 ]. }
      iFrame.
      iMod (ghost_map_alloc_block (s_cmems s0) (s_alls s0) a c (Wasm_int.N_of_uint i32m n) with "Hcmem") as "[Hcmem Hwcs]".
      { exact Hsoundb. }
      { exact Hfreshb. }
      { exact H. }
      { rewrite /cmem_length /cm_length in H1. simpl in H1. lia. }
      iMod (allocator_insert_wall (s_cmems s0) (s_alls s0) c
              (alloc_result_base a (Wasm_int.N_of_uint i32m n))
              (Wasm_int.N_of_uint i32m n) Hfreshb with "Hall")
        as "[Hall Hwall]".
      iMod (ghost_map_insert c true with "Hret") as "[Hret Hlive]";
        first exact Hfreshb.
      iModIntro.
      iSplitL "Hcmem Hall Hret".
      - iSplitL "Hcmem".
        + iExact "Hcmem".
        + iSplitL "Hall".
          * rewrite (gmap_of_allocator_calloc _ _ _ _ _ _ _ HWF H2). iExact "Hall".
          * iSplitL "Hret".
            { iExact "Hret". }
            iPureIntro.
            eapply (reduce_preserves_wellformedness (f := {| f_locs := locs'; f_inst := inst' |})).
            exact HWF. eapply rm_colalloc_success => //.
      - iApply "HΦ".
        iExists (new_pointer a (Some c) true).
        iSplitR. done.
        iRight. iExists c.
        iSplitR. done.
        iSplit. done.
        iFrame "Hwall Hlive".
        iFrame "Hwcs".
      }
    { (* failed *)
      inversion Heqes0; subst n0; clear Heqes0.
      subst.
      iFrame.
      simpl.
      iModIntro.
      iSplit; first done. iSplit; last done.
      iApply "HΦ". iExists _.
      iSplitL; first done.
      iLeft.
      done.
    }
    rewrite Heqes0 in H0.
    simple_filled H0 k lh bef aft nn ll ll'.
    destruct bef.
    { destruct es ; first by exfalso ; eapply empty_no_reduce.
      inversion H0.
      apply Logic.eq_sym, app_eq_unit in H4 as [[ -> _ ] | [-> ->]].
      by subst ; exfalso ; eapply values_no_reduce.
      subst.
      unfold lfilled, lfill in H1.
      simpl in H1.
      rewrite app_nil_r in H1.
      move/eqP in H1 ; subst.
      apply IHreduce => //=. }
    exfalso.
    inversion H0.
    apply Logic.eq_sym, app_eq_unit in H4 as [[ _ Hes ] | [ _ Hes]].
    apply app_eq_unit in Hes as [[ -> _ ] | [Hes _ ]].
    by eapply empty_no_reduce.
    rewrite <- app_nil_l in Hes.
    clear IHreduce H1 Heqes0 H0.
    induction H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
      inversion Habs.
     induction H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
      inversion Habs.
    { destruct H ; try by inversion Hes ; try by apply app_inj_tail in Hes as [_ Habs] ;
        inversion Habs.
      rewrite Hes in H0 ; filled_trap H0 Hxl1. }
    rewrite Hes in H0.
    simple_filled H0 k lh bef0 aft0 nnn lll lll'.
    apply Logic.eq_sym, app_eq_unit in H0 as [[ -> H0 ] | [_ H0]].
    apply app_eq_unit in H0 as [[ -> _ ] | [ -> -> ]].
    by eapply empty_no_reduce.
    apply IHreduce => //=.
    apply app_eq_nil in H0 as [ -> _].
    by eapply empty_no_reduce.
    apply app_eq_nil in Hes as [-> _].
    by eapply empty_no_reduce.
Qed.

(* ================================================================= *)
(* wp_colfree                                                         *)
(* ================================================================= *)
Lemma retire_color (A : allocator) (c : N) :
  A.(allocated) !! c = Some true ->
  retired_auth A -∗ live_color c ==∗
    retired_auth (allocator_remove c A) ∗ dead_color c.
Proof.
  iIntros (Hlive) "Hret Hlive".
  iMod (ghost_map_update false with "Hret Hlive") as "[Hret Hdead]".
  iMod (ghost_map_elem_persist with "Hdead") as "#Hdead".
  rewrite -gmap_of_retired_remove.
  iFrame.
  iModIntro. done.
Qed.

Lemma dead_color_not_live (cm : cmem) (A : allocator)
    (c base size : N) :
  retired_auth A -∗
  ghost_map_auth allGName 1 (gmap_of_allocator cm A) -∗
  dead_color c -∗ wall c base size -∗ False.
Proof.
  iIntros "Hret Hall Hdead Hwall".
  iDestruct (dead_color_is_freed with "Hret Hdead") as %Hfreed.
  iDestruct (allocated_implies_is_in_allocator with "Hall Hwall") as %Hlive.
  unfold isFreed in Hfreed. by rewrite Hlive in Hfreed.
Qed.

Lemma wp_colfree (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (col base size : N) (tbs : list tagged_byte) (f0 : frame) :
  ptr_col p = Some col ->
  ptr_freeable p = true ->
  N.of_nat (length tbs) = size ->
  all (fun tb => tb_color tb == Some col) tbs ->
  (▷ (dead_color col -∗ Φ (immV [])) ∗ ↪[frame] f0 ∗
     wall col base size ∗ live_color col ∗ wblock base tbs ⊢
  WP [AI_const (VAL_pointer p); AI_basic BI_colfree] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hcol Hfree Hlen Hall) "(HΦ & Hf0 & Hwall & Hlive & Hblock)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & Hcm & Hallocauth & ? & Hframe & ? & ? & ? & ? & Hret & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hf0.
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (allocated_implies_is_in_allocator with "Hallocauth Hwall") as %Halloc.
  iSplit.
  - iPureIntro. destruct s => //=.
    eexists [_], [], (upd_s_all ws (allocator_remove col (s_alls ws)), locs, winst), [].
    repeat split => //.
    eapply rm_colfree_success => //.
  - iIntros "!>" (es σ2 efs HStep).
    iMod (ghost_map_free_color (s_cmems ws) (s_alls ws) col base
      (N.of_nat (length tbs)) tbs Halloc Logic.eq_refl Hall with
      "Hcm Hallocauth Hwall Hblock") as "[Hcm Hallocauth]".
    iMod (retire_color (s_alls ws) col Halloc with "Hret Hlive")
      as "[Hret Hdead]".
    iIntros "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & ?) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    2:{ eapply rm_colfree_success => //. }
    inversion H; subst; clear H => /=.
    iFrame. iSplit.
    + iPureIntro.
      eapply (reduce_preserves_wellformedness
        (f := {| f_locs := locs'; f_inst := inst' |})).
      exact HWF. eapply rm_colfree_success => //.
    + iApply "HΦ". iExact "Hdead".
Qed.

(* ================================================================= *)
(* Failure rules for colfree                                           *)
(* ================================================================= *)

Lemma wp_colfree_fail_null (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (f0 : frame) :
  is_null p ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_basic BI_colfree] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hnull) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colfree_failure => //.
    left. done.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & ?) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colfree_failure => //; left; done);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

Lemma wp_colfree_fail_freeable (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (f0 : frame) :
  ptr_freeable p = false ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_basic BI_colfree] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hfreeable) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colfree_failure => //.
    right. left. done.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & ?) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colfree_failure => //; right; left; done);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

Lemma wp_colfree_fail_unallocated (s : stuckness) (E : coPset)
    (Φ : val -> iProp Σ) (p : pointer) (f0 : frame) :
  (forall (ws : store_record) c, ptr_col p = Some c -> ~ isAlloc c (s_alls ws)) ->
  (▷ Φ trapV ∗ ↪[frame] f0 ⊢
  WP [AI_const (VAL_pointer p); AI_basic BI_colfree] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hunallocated) "HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & ? & Hframe & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colfree_failure => //.
    right. right. move=> c Hcol.
    exact (Hunallocated ws c Hcol).
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & ?) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colfree_failure => //; right; right;
        move=> c Hcol; exact (Hunallocated ws c Hcol));
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst.
    iFrame. simpl.
    iDestruct "HΦ" as "[HΦ Hf0]". iFrame.
Qed.

Lemma wp_colfree_fail_dead (s : stuckness) (E : coPset) (Φ : val -> iProp Σ)
    (p : pointer) (col : N) (f0 : frame) :
  ptr_col p = Some col ->
  (▷ (dead_color col -∗ Φ trapV) ∗ ↪[frame] f0 ∗ dead_color col ⊢
  WP [AI_const (VAL_pointer p); AI_basic BI_colfree] @ s; E
    {{ w, Φ w ∗ ↪[frame] f0 }})%I.
Proof.
  iIntros (Hcol) "(HΦ & Hf0 & #Hdead)".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[ws locs] winst].
  iDestruct "Hσ" as
    "(? & ? & ? & ? & ? & ? & Hframe & ? & ? & ? & ? & Hret & %HWF)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as "%Hf0".
  rewrite lookup_insert in Hf0. inversion Hf0; subst; clear Hf0.
  iDestruct (dead_color_is_freed with "Hret Hdead") as %Hfreed.
  have Hnotalloc : ~ isAlloc col (s_alls ws).
  { unfold isFreed in Hfreed. unfold isAlloc. congruence. }
  have Hfailure : forall c, ptr_col p = Some c -> ~ isAlloc c (s_alls ws).
  { move=> c Hc. have -> : c = col by congruence. exact Hnotalloc. }
  iSplit.
  - iPureIntro. destruct s => //=.
    eexists [_], [AI_trap], (ws, locs, winst), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply rm_colfree_failure => //. right; right.
    exact Hfailure.
  - iIntros "!>" (es σ2 efs HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    prim_split κ HStep H.
    eapply reduce_det in H as [H | [(? & Hfirst & ?) |
      [[? Hfirst] | (? & ? & ? & Hfirst & Hfirst2 & Hfirst3 & Hσ & Hme)]]];
      last (eapply rm_colfree_failure => //; right; right; exact Hfailure);
      try by unfold first_instr in Hfirst; simpl in Hfirst; inversion Hfirst.
    inversion H; subst. iFrame. simpl.
    iSplit.
    + iPureIntro. exact HWF.
    + iSpecialize ("HΦ" with "Hdead").
      iFrame "HΦ".
Qed.

End iris_rules_cmem.
