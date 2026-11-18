(** Basic operations over Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From CWasm Require Import common memory_list color_ptr colored_memory.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq ssrnat .
From compcert Require lib.Floats.
From CWasm Require Export datatypes_properties list_extra.
From Coq Require Import ZArith.BinInt BinNat NArith Eqdep_dec.
Require Import Lia Coq.Program.Equality.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




(** read `len` bytes from `m` starting at `start_idx` *)
Definition read_bytes (m : memory) (start_idx : N) (len : nat) : option bytes :=
  those
    (List.map
      (fun off =>
        let idx := BinNatDef.N.add start_idx (N.of_nat off) in
        mem_lookup idx m.(mem_data))
      (iota 0 len)).

Definition read_colbytes (m : cmem) (start_idx : N) (len : nat) :=
  those
    (List.map
       (fun off =>
          let idx := BinNatDef.N.add start_idx (N.of_nat off) in
          cm_lookup idx m.(cmem_data))
       (iota 0 len)).

(** write bytes `bs` to `m` starting at `start_idx` *)
Definition write_bytes (m : memory) (start_idx : N) (bs : bytes) : option memory :=
  let x :=
    list_extra.fold_lefti
      (fun off dat_o b =>
        match dat_o with
        | None => None
        | Some dat =>
          let idx := BinNatDef.N.add start_idx (N.of_nat off) in
          mem_update idx b dat
        end)
      bs
      (Some m.(mem_data)) in
  match x with
  | Some dat => Some {| mem_data := dat; mem_max_opt := m.(mem_max_opt); |}
  | None => None
  end.

Definition write_cmembytes (cm : cmem) (start_idx : N) (bs : bytes) (col : option N) (tag : btag) : option cmem :=
  let x :=
    list_extra.fold_lefti
      (fun off dat_o b =>
        match dat_o with
        | None => None
        | Some dat =>
          let idx := BinNatDef.N.add start_idx (N.of_nat off) in
          cmem_update idx {| tb_value := b; tb_color := col; tb_tag := tag |} dat
        end)
      bs
      (Some cm.(cmem_data)) in
  match x with
  | Some dat => Some {| cmem_data := dat; cmem_max_opt := cm.(cmem_max_opt) |}
  | None => None
  end.


Definition upd_s_mem (s : store_record) (m : list memory) : store_record := {|
  s_funcs   := s.(s_funcs);
  s_tables  := s.(s_tables);
  s_mems    := m;
  s_cmems   := s.(s_cmems);
  s_alls    := s.(s_alls);
  s_globals := s.(s_globals);
|}.

Definition upd_s_cmem (s : store_record) (m : cmem) : store_record :=
  {|
    s_funcs   := s.(s_funcs) ;
    s_tables  := s.(s_tables) ;
    s_mems    := s.(s_mems) ;
    s_cmems   := m ;
    s_alls    := s.(s_alls);
    s_globals := s.(s_globals);
  |}.

Definition upd_s_all s a :=
  {|
    s_funcs   := s.(s_funcs) ;
    s_tables  := s.(s_tables) ;
    s_mems    := s.(s_mems) ;
    s_cmems   := s.(s_cmems) ;
    s_alls    := a ;
    s_globals := s.(s_globals)
  |}.


Definition upd_cmem_data cmem data := {|
  cmem_data := data ;
  cmem_max_opt := cmem.(cmem_max_opt)
|}.




Definition page_size : N := (64 % N) * (1024 % N).

Definition page_limit : N := 65536%N.

Definition ml_valid (m: memory_list) : Prop :=
  N.modulo (memory_list.mem_length m) page_size = 0%N.

Definition mem_length (m : memory) : N :=
  mem_length m.(mem_data).

Definition mem_size (m : memory) : N :=
  N.div (mem_length m) page_size.

Definition cm_valid (m: colored_memory_list) : Prop :=
  N.modulo (colored_memory.cm_length m) page_size = 0%N.

Definition cmem_length m :=
  cm_length m.(cmem_data).

Definition cmem_size (m: cmem) : N :=
  N.div (cm_length m.(cmem_data)) page_size.

(** Grow the memory a given number of pages.
  * @param len_delta: the number of pages to grow the memory by
  *)

Definition mem_grow (m : memory) (len_delta : N) : option memory :=
  let new_size := N.add (mem_size m) len_delta in
  let new_mem_data := mem_grow (N.mul len_delta page_size) m.(mem_data) in
  if N.leb new_size page_limit then
  match m.(mem_max_opt) with
  | Some maxlim =>
    if N.leb new_size maxlim then
        Some {|
          mem_data := new_mem_data;
          mem_max_opt := m.(mem_max_opt);
          |}
    else None
  | None =>
    Some {|
      mem_data := new_mem_data;
      mem_max_opt := m.(mem_max_opt);
      |}
  end
  else None.


(* seg_grow uses length, where mem_grow uses size *)
Definition cmem_grow (m : cmem) (len_delta : N) : option cmem :=
  let new_size := N.add (cmem_length m) len_delta in
  let new_seg_data := cm_grow len_delta m.(cmem_data) in
  if N.leb (N.div new_size page_size) page_limit then
  match m.(cmem_max_opt) with
  | Some maxlim =>
    if N.leb (N.div new_size page_size) maxlim then
        Some {|
          cmem_data := new_seg_data;
          cmem_max_opt := m.(cmem_max_opt);
          |}
    else None
  | None =>
    Some {|
      cmem_data := new_seg_data;
      cmem_max_opt := m.(cmem_max_opt);
      |}
  end
  else None.

Section alloc.
  Import gmap.

  Definition allocator_insert (c : N) (A : allocator) := {|
    allocated := <[ c := true ]> A.(allocated);
    next_free := (N.max A.(next_free) c) + 1;
  |}.

  Definition allocator_remove (c : N) (A : allocator) := {|
    allocated := <[ c := false ]> A.(allocated);
    next_free := A.(next_free);
  |}.

  Inductive calloc : cmem -> allocator -> N (*addr*) -> N (*size*) -> N (*color*) -> cmem -> allocator -> Prop :=
    | Alloc : forall M A a n c M' A',
        (forall a_off, (a <= a_off < a + n)%N ->
        isfree a_off (cmem_data M) A) ->
        isfreshcol c A ->
        (a <= cmem_length M)%N ->
        ((a + n) / page_size <= page_limit)%N ->
        (match M.(cmem_max_opt) with
         | Some lim => ((a + n) / page_size <= lim)%N
         | None => True end) ->
        let new_data := take (N.to_nat a) M.(cmem_data).(cml_data) ++
                        List.repeat ({| tb_value := #00; tb_color := Some c; tb_tag := Numeric |}) (N.to_nat n) ++
                        drop (N.to_nat (a + n)) M.(cmem_data).(cml_data) in
        M' = {| cmem_data := {| cml_data := new_data |}; cmem_max_opt := M.(cmem_max_opt) |} ->
        A' = allocator_insert c A ->
        calloc M A a n c M' A'.

  Inductive cfree : cmem -> allocator -> N (*c*) -> allocator -> Prop :=
    | Free : forall M A c A',
      A.(allocated) !! c = Some(true) ->
      A' = allocator_remove c A ->
      cfree M A c A'.

End alloc.

Section free_scan.
  Import ssrnat.

  Definition range_free (M : colored_memory_list) (A : allocator) (addr n : N) : bool :=
    all (fun off : nat => isfreeb (addr + N.of_nat off) M A) (iota 0 (N.to_nat n)).

  Definition first_free (M : colored_memory_list) (A : allocator) (n : N) : option N :=
    let addrs := filter (fun a : N => range_free M A a n)
                        (map (fun i : nat => N.of_nat i) (iota 0 (N.to_nat (colored_memory.cm_length M)))) in
    match addrs with
    | [::] => None
    | a :: _ => Some a
    end.

End free_scan.

Section l_is_s.
  Import ssrnat.

Lemma length_is_size {A} (l : list A) : length l = size l.
Proof. done. Qed.

End l_is_s.


Section color_preservation.

Require Import List.
From stdpp Require Import list.

Unset Implicit Arguments.

Lemma fold_lefti_data_shift (addr : N) (col : option N) (tag : btag) (bs : bytes)
      (k : nat) (acc : option colored_memory_list) :
  fold_lefti_data
    (fun off dat_o x =>
       match dat_o with
       | Some dat => cmem_update (addr + N.of_nat off)
                        {| tb_value := x; tb_color := col; tb_tag := tag |} dat
       | None => None
       end) bs (S k) acc =
  fold_lefti_data
    (fun off dat_o x =>
       match dat_o with
       | Some dat => cmem_update (addr + 1 + N.of_nat off)
                        {| tb_value := x; tb_color := col; tb_tag := tag |} dat
       | None => None
       end) bs k acc.
Proof.
  revert k acc.
  induction bs as [|b2 bs IH]; intros k acc; simpl.
  - reflexivity.
  - assert (Hcell : forall (off : nat) (d : option colored_memory_list) (x : byte),
      match d with
      | Some dat => cmem_update (addr + N.of_nat (S off))
                       {| tb_value := x; tb_color := col; tb_tag := tag |} dat
      | None => None
      end =
      match d with
      | Some dat => cmem_update (addr + 1 + N.of_nat off)
                       {| tb_value := x; tb_color := col; tb_tag := tag |} dat
      | None => None
      end).
    { intros off d x. destruct d as [dat|]; simpl.
      - assert (Hi : (addr + N.of_nat (S off))%N = (addr + 1 + N.of_nat off)%N).
        { rewrite Nat2N.inj_succ. rewrite <- N.add_1_l. rewrite N.add_assoc.
          reflexivity. }
        rewrite Hi. reflexivity.
      - reflexivity. }
    rewrite (Hcell k acc b2). eapply (IH (S k)).
Qed.

Lemma write_cmembytes_cons cm addr b bs col tag cm'' cm' :
  cmem_update addr {| tb_value := b; tb_color := col; tb_tag := tag |} (cmem_data cm) = Some (cmem_data cm') ->
  cmem_max_opt cm' = cmem_max_opt cm ->
  write_cmembytes cm' (addr + 1)%N bs col tag = Some cm'' ->
  write_cmembytes cm addr (b :: bs) col tag = Some cm''.
Proof.
  intros Hupd Hmax Hrest.
  rewrite /write_cmembytes in Hrest |- *.
  rewrite !fold_lefti_eq_fold_lefti_data in Hrest |- *.
  rewrite /cmem_update in Hupd. simpl in Hupd.
  case Hif : (addr <? N.of_nat (length (cml_data (cmem_data cm))))%N;
    rewrite Hif in Hupd; last by discriminate.
  cbn [fold_lefti_data] in Hrest |- *.
  assert (H0n : N.of_nat 0 = 0%N) by reflexivity.
  assert (Hhead : cmem_update (addr + N.of_nat 0)
                    {| tb_value := b; tb_color := col; tb_tag := tag |}
                    (cmem_data cm) = Some (cmem_data cm')).
  { rewrite H0n N.add_0_r /cmem_update Hif. simpl. exact Hupd. }
  rewrite Hhead in |- *.
  rewrite (fold_lefti_data_shift addr col tag bs 0 (Some (cmem_data cm'))).
  rewrite <- Hmax.
  rewrite Hrest. done.
Qed.

Lemma fold_lefti_data_none {A B} (f : nat -> option A -> B -> option A) (xs : list B) :
  (forall i x, f i None x = None) ->
  forall k, fold_lefti_data f xs k None = None.
Proof.
  intros Hf.
  induction xs as [|x xs IH]; simpl; [done | intros k; rewrite Hf; rewrite (IH (S k)); done].
Qed.

Lemma write_cmembytes_cons_inv cm addr b bs col tag cm'' :
  write_cmembytes cm addr (b :: bs) col tag = Some cm'' ->
  exists cm_mid,
    cmem_update addr {| tb_value := b; tb_color := col; tb_tag := tag |} (cmem_data cm) = Some (cmem_data cm_mid) /\
    cmem_max_opt cm_mid = cmem_max_opt cm /\
    write_cmembytes cm_mid (addr + 1)%N bs col tag = Some cm''.
Proof.
  intro Hw.
  rewrite /write_cmembytes in Hw.
  rewrite fold_lefti_eq_fold_lefti_data in Hw.
  cbn [fold_lefti_data] in Hw.
  change (N.of_nat 0) with 0%N in Hw.
  rewrite N.add_0_r in Hw.
  destruct (cmem_update addr {| tb_value := b; tb_color := col; tb_tag := tag |} (cmem_data cm)) as [dat0|] eqn:Hupd.
  - set (g := (fun (off : nat) (dat_o : option colored_memory_list) (xb : byte) =>
              match dat_o with
              | Some dat => cmem_update (addr + 1 + N.of_nat off) {| tb_value := xb; tb_color := col; tb_tag := tag |} dat
              | None => None
              end)).
    rewrite (fold_lefti_data_shift addr col tag bs 0 (Some dat0)) in Hw.
    destruct (fold_lefti_data g bs 0 (Some dat0)) as [cmdata|] eqn:Hrest.
    + exists {| cmem_data := dat0; cmem_max_opt := cmem_max_opt cm |}.
      split; [| split].
      * reflexivity.
      * reflexivity.
      * rewrite /write_cmembytes. rewrite fold_lefti_eq_fold_lefti_data.
         rewrite Hrest. simpl. rewrite Hrest in Hw.    exact Hw.
    + rewrite Hrest in Hw.    discriminate Hw.
  - have Hfold : fold_lefti_data
        (λ (off : nat) (dat_o : option colored_memory_list) (b : byte),
           match dat_o with
           | Some dat => cmem_update (addr + N.of_nat off) {| tb_value := b; tb_color := col; tb_tag := tag |} dat
           | None => None end) bs 1 None = None.
    { apply fold_lefti_data_none. move=> i x. reflexivity. }
    rewrite Hfold in Hw.    discriminate Hw.
Qed.

Lemma nth_error_split_take_drop {T : Type} (l : list T) (i : nat) (x : T) :
  List.nth_error l i = Some x ->
  take i l ++ x :: drop (i + 1) l = l.
Proof.
  revert i.
  induction l as [|y l IH]; intros i Hnth.
  - case: i Hnth => [Hnth | i Hnth]; simpl in Hnth; discriminate Hnth.
  - destruct i as [|i]; simpl in Hnth.
    + inversion Hnth. subst x. simpl. reflexivity.
    + simpl. f_equal. exact (IH i Hnth).
Qed.

Lemma nth_error_left_middle_eq {T : Type} (l1 l3 : list T) (x1 x2 : T) (j : nat) :
  length l1 <> j ->
  List.nth_error (l1 ++ x1 :: l3) j = List.nth_error (l1 ++ x2 :: l3) j.
Proof.
  revert j.
  induction l1 as [|y l1 IH]; intros j Hneq.
  - simpl. destruct j as [|j].
    + exfalso. exact (Hneq Logic.eq_refl).
    + reflexivity.
  - simpl. destruct j as [|j].
    + reflexivity.
    + have Hneql : length l1 <> j.
      { move=> Habs. exact (Hneq (f_equal S Habs)). }
      exact (IH j Hneql).
Qed.

Lemma cmem_update_preserves_color_map (m : colored_memory_list) (addr : N) (tb_new : tagged_byte) (m' : colored_memory_list) :
  cmem_update addr tb_new m = Some m' ->
  (forall old : tagged_byte, cm_lookup addr m = Some old -> tb_color old = tb_color tb_new) ->
  map tb_color m'.(cml_data) = map tb_color m.(cml_data).
Proof.
  move=> Hupd Hcol.
  unfold cmem_update in Hupd.
  case Hbr : (addr <? N.of_nat (List.length m.(cml_data)))%N.
  - rewrite Hbr in Hupd. simpl in Hupd.
    inversion Hupd; subst m'.
  have Hlt : N.to_nat addr < List.length (cml_data m).
  { apply Nat.compare_lt_iff.
    rewrite -(Nat2N.id (List.length (cml_data m))).
    rewrite <- N2Nat.inj_compare.
    exact (proj2 (N.compare_lt_iff addr (N.of_nat (List.length (cml_data m))))
                 (proj1 (N.ltb_lt addr (N.of_nat (List.length (cml_data m)))) Hbr)). }
  set l := cml_data m.
  set a := N.to_nat addr.
  destruct (List.nth_error l a) as [old|] eqn:Hnth.
  - have Hlook : cm_lookup addr m = Some old.
    { rewrite /cm_lookup. rewrite -/a -/l. exact Hnth. }
    have Hsplit := nth_error_split_take_drop l a old Hnth.
    rewrite <- (f_equal (map tb_color) Hsplit).
    rewrite !List.map_app. simpl.
    rewrite (Hcol old Hlook). reflexivity.
  - exfalso.
    exact ((proj2 (List.nth_error_Some l a) Hlt) Hnth).
  - rewrite Hbr in Hupd.    discriminate Hupd.
Qed.

Lemma cmem_update_preserves_colors (m : colored_memory_list) (addr : N) (tb_new : tagged_byte) (m' : colored_memory_list) (c : N) :
  cmem_update addr tb_new m = Some m' ->
  (forall old : tagged_byte, cm_lookup addr m = Some old -> tb_color old = tb_color tb_new) ->
  count_color c m = count_color c m' /\ base_color c m = base_color c m'.
Proof.
  move=> Hupd Hcol.
  have Hmap : map tb_color m'.(cml_data) = map tb_color m.(cml_data) :=
    cmem_update_preserves_color_map m addr tb_new m' Hupd Hcol.
  split.
  - rewrite /count_color. symmetry. apply count_color_list_ext. exact Hmap.
  - rewrite /base_color. symmetry. apply (f_equal (option_map N.of_nat)). apply base_color_index_ext. exact Hmap.
Qed.

Lemma cmem_update_lookup_ne (m : colored_memory_list) (addr addr' : N) (tb_new : tagged_byte) (m' : colored_memory_list) :
  cmem_update addr tb_new m = Some m' ->
  addr <> addr' ->
  cm_lookup addr' m' = cm_lookup addr' m.
Proof.
  move=> Hupd Hneq.
  unfold cmem_update in Hupd.
  case Hbr : (addr <? N.of_nat (List.length m.(cml_data)))%N.
  - rewrite Hbr in Hupd. simpl in Hupd.
    inversion Hupd; subst m'.
  unfold cm_lookup. simpl.
  set l := cml_data m.
  set a := N.to_nat addr.
  have Hlt : N.to_nat addr < List.length (cml_data m).
  { apply Nat.compare_lt_iff.
    rewrite -(Nat2N.id (List.length (cml_data m))).
    rewrite <- N2Nat.inj_compare.
    exact (proj2 (N.compare_lt_iff addr (N.of_nat (List.length (cml_data m))))
                 (proj1 (N.ltb_lt addr (N.of_nat (List.length (cml_data m)))) Hbr)). }
  have Hle : a <= length l by rewrite /a /l; lia.
  destruct (List.nth_error l a) as [old|] eqn:Hnth.
  - have Hsplit : take a l ++ old :: drop (a + 1) l = l := nth_error_split_take_drop l a old Hnth.
    set j := N.to_nat addr'.
    have Haj : a <> j.
    { intro Habs. apply Hneq. apply N2Nat.inj_iff. exact Habs. }
    have Htakel : length (take a l) = a := take_length_le l a Hle.
    have Hj : length (take a l) <> j.
    { rewrite Htakel. exact Haj. }
    rewrite <- (f_equal (fun l0 => List.nth_error l0 j) Hsplit).
    exact (nth_error_left_middle_eq (take a l) (drop (a + 1) l) tb_new old j Hj).
  - exfalso.
    exact ((proj2 (List.nth_error_Some l a) Hlt) Hnth).
  - rewrite Hbr in Hupd.    discriminate Hupd.
Qed.

Lemma write_cmembytes_preserves_colors (cm : cmem) (a : N) (bs : bytes) (col : option N) (tag : btag) (cm' : cmem) :
  write_cmembytes cm a bs col tag = Some cm' ->
  (forall i tb, i < length bs -> cm_lookup (a + N.of_nat i) cm.(cmem_data) = Some tb -> tb.(tb_color) = col) ->
  forall c, count_color c cm.(cmem_data) = count_color c cm'.(cmem_data) /\ base_color c cm.(cmem_data) = base_color c cm'.(cmem_data).
Proof.
  move=> Hwrite Hcolor.
  move: cm a cm' Hwrite Hcolor.
  elim: bs => [|b bs IH]; intros cm a cm' Hwrite Hcolor c.
  - destruct cm as [cmdata cmmax].    inversion Hwrite; subst. split; reflexivity.
  - destruct (write_cmembytes_cons_inv cm a b bs col tag cm' Hwrite)
      as [cm_mid [Hupd [Hmax Hrest]]].
    have Hcmid_col : forall c0,
        count_color c0 cm.(cmem_data) = count_color c0 cm_mid.(cmem_data) /\
        base_color c0 cm.(cmem_data) = base_color c0 cm_mid.(cmem_data).
    { move=> c0.
      apply (cmem_update_preserves_colors cm.(cmem_data) a {| tb_value := b; tb_color := col; tb_tag := tag |} cm_mid.(cmem_data) c0 Hupd).
      move=> old Hlook.
      apply (Hcolor 0 old).
      - simpl. lia.
      - change (N.of_nat 0) with 0%N. rewrite N.add_0_r. exact Hlook. }
    have Htail : forall i tb, i < length bs ->
        cm_lookup (a + 1 + N.of_nat i) cm_mid.(cmem_data) = Some tb ->
        tb.(tb_color) = col.
    { move=> i tb Hi Hlook.
      apply (Hcolor (S i) tb).
      - simpl. lia.
      - have Hneq : a <> (a + 1 + N.of_nat i)%N.
        { intro Habs.
          apply (f_equal N.to_nat) in Habs.
          rewrite !N2Nat.inj_add in Habs.
          rewrite Nat2N.id in Habs.
            
          lia. }
        have Hpos : (a + N.of_nat (S i))%N = (a + 1 + N.of_nat i)%N.
        { rewrite Nat2N.inj_succ. rewrite <- N.add_1_l. rewrite N.add_assoc. reflexivity. }
        have Hlook' : cm_lookup (a + N.of_nat (S i)) cm.(cmem_data) = Some tb.
        { rewrite Hpos.
          exact (Logic.eq_trans (Logic.eq_sym (cmem_update_lookup_ne cm.(cmem_data) a (a + 1 + N.of_nat i)
                                   {| tb_value := b; tb_color := col; tb_tag := tag |}
                                   cm_mid.(cmem_data) Hupd Hneq)) Hlook). }
        exact Hlook'. }
    have Hrest_col : forall c0,
        count_color c0 cm_mid.(cmem_data) = count_color c0 cm'.(cmem_data) /\
        base_color c0 cm_mid.(cmem_data) = base_color c0 cm'.(cmem_data).
    { move=> c0. apply (IH cm_mid (a + 1)%N cm' Hrest Htail). }
    split.
    - rewrite (proj1 (Hcmid_col c)) (proj1 (Hrest_col c)). reflexivity.
    - rewrite (proj2 (Hcmid_col c)) (proj2 (Hrest_col c)). reflexivity.
Qed.

Set Implicit Arguments.

End color_preservation.

Section calloc_colors.

Require Import List.
From stdpp Require Import list.

Unset Implicit Arguments.

(* --- ordering bridges between N and nat --- *)

Lemma N_of_nat_lt_mono (i j : nat) : i < j -> (N.of_nat i < N.of_nat j)%N.
Proof. intro Hij. lia. Qed.

Lemma N_of_nat_le_mono (i j : nat) : i <= j -> (N.of_nat i <= N.of_nat j)%N.
Proof. intro Hij. lia. Qed.

Lemma N_to_nat_lt_mono (i j : N) : (i < j)%N -> N.to_nat i < N.to_nat j.
Proof. intro Hij. lia. Qed.

Lemma N_to_nat_le_mono (i j : N) : (i <= j)%N -> N.to_nat i <= N.to_nat j.
Proof. intro Hij. lia. Qed.

(* --- count_color auxiliary lemmas --- *)

Lemma count_color_list_app (c : N) (l1 l2 : list tagged_byte) :
  count_color_list c (l1 ++ l2) = (count_color_list c l1 + count_color_list c l2)%N.
Proof.
  induction l1 as [|tb1 l1 IH]; simpl.
  - lia.
  - destruct (tbc_is_color c tb1); [ lia | exact IH ].
Qed.

Lemma count_color_list_repeat (c : N) (tb : tagged_byte) (n : nat) :
  tbc_is_color c tb = true ->
  count_color_list c (List.repeat tb n) = N.of_nat n.
Proof.
  induction n as [|n IHn]; intros Hcol; simpl.
  - done.
  - rewrite Hcol. rewrite (IHn Hcol). rewrite Nat2N.inj_succ. lia.
Qed.

Lemma count_color_list_repeat_false (c : N) (tb : tagged_byte) (n : nat) :
  tbc_is_color c tb = false ->
  count_color_list c (List.repeat tb n) = 0%N.
Proof.
  induction n as [|n IHn]; intros Hcol; simpl; first done.
  rewrite Hcol. exact (IHn Hcol).
Qed.

Lemma count_color_list_forall_false (c : N) (l : list tagged_byte) :
  List.Forall (fun tb : tagged_byte => tbc_is_color c tb = false) l ->
  count_color_list c l = 0%N.
Proof.
  induction l as [|tb l IH]; intros Hf; simpl; first done.
  inversion Hf as [| hd tl Hthin Htail]. rewrite Hthin. exact (IH Htail).
Qed.

Lemma count_color_list_cat3 (c : N) (l1 l2 l3 : list tagged_byte) :
  count_color_list c (l1 ++ l2 ++ l3) = (count_color_list c l1 + count_color_list c l2 + count_color_list c l3)%N.
Proof.
  rewrite !count_color_list_app. lia.
Qed.

Lemma fresh_sound_no_color (c : N) (A : allocator) (cm : colored_memory_list) :
  isSound A cm ->
  isfreshcol c A ->
  count_color c cm = 0%N.
Proof.
  intros [Hsounda Hsoundb] Hfresh.
  have Hnone : A.(allocated) !! c = None.
  { exact (fresh_col_none c A Hsounda Hfresh). }
  unfold count_color.
  have Hall : List.Forall (fun tb : tagged_byte => tbc_is_color c tb = false) cm.(cml_data).
  { apply (List.Forall_impl
                            (P := fun tb : tagged_byte => forall c0 : N, tb.(tb_color) = Some c0 -> A.(allocated) !! c0 <> None)).
    * intros tb Htb.
      destruct tb as [v col tag] => /=.
      destruct col as [c'|]; last by [].
      rewrite N.eqb_neq.
      intro Hc'c. (* c' = c *)
      subst c'.
      have Hallocc : A.(allocated) !! c <> None.
      { exact (Htb c Logic.eq_refl). }
      rewrite Hnone in Hallocc.
      by [].
    * exact Hsoundb. }
  exact (count_color_list_forall_false c cm.(cml_data) Hall).
Qed.

Lemma nth_error_lookup {T : Type} (l : list T) (i : nat) :
  List.nth_error l i = l !! i.
Proof.
  elim: l i => [i | x l IH [|i]].
  - case: i; simpl; done.
  - simpl; done.
  - simpl. apply: IH.
Qed.

Lemma those_nth_error_Some {T : Type} (l0 : list (option T))
    (l1 : list T) (i : nat) (x : T) :
  those l0 = Some l1 ->
  List.nth_error l1 i = Some x ->
  List.nth_error l0 i = Some (Some x).
Proof.
  rewrite -those_those0.
  revert l1 i.
  induction l0 as [|o l0 IH]; intros l1 i Hthose Hlookup.
  - simpl in Hthose. inversion Hthose; subst l1.
    destruct i; discriminate.
  - destruct o as [x0|].
    + simpl in Hthose.
      destruct (those0 l0) as [l0'|] eqn:Htail;
        simpl in Hthose; try discriminate.
      inversion Hthose; subst l1.
      destruct i as [|i].
      * simpl in Hlookup. inversion Hlookup; subst x. reflexivity.
      * simpl in Hlookup. simpl. eapply IH; eauto.
    + simpl in Hthose. discriminate.
Qed.

Lemma nth_error_iota (start len i : nat) :
  i < len ->
  List.nth_error (iota start len) i = Some (start + i).
Proof.
  revert start len.
  induction i as [|i IH]; intros start len Hlt.
  - destruct len as [|len]; first lia.
    simpl. f_equal. lia.
  - destruct len as [|len]; first lia.
    simpl. rewrite (IH (S start) len); last lia.
    f_equal. lia.
Qed.

Lemma read_colbytes_nth_error (m : cmem) (start : N) (len i : nat)
    (tbs : list tagged_byte) (tb : tagged_byte) :
  read_colbytes m start len = Some tbs ->
  i < len ->
  List.nth_error tbs i = Some tb ->
  cm_lookup (start + N.of_nat i) m.(cmem_data) = Some tb.
Proof.
  rewrite /read_colbytes.
  move=> Hread Hlt Hlookup.
  have Hinput :
      List.nth_error
        (List.map (fun off => cm_lookup (start + N.of_nat off) m.(cmem_data))
          (iota 0 len)) i = Some (Some tb).
  { eapply those_nth_error_Some; eauto. }
  rewrite List.nth_error_map (nth_error_iota 0 len i Hlt) /= in Hinput.
  by inversion Hinput.
Qed.

Lemma take_drop_middle_decomp {T : Type} (l : list T) (m sz : nat) :
  l = take m l ++ (take sz (drop m l) ++ drop (m + sz) l).
Proof.
  have H1 : take m l ++ drop m l = l := take_drop m l.
  have H2 : take sz (drop m l) ++ drop sz (drop m l) = drop m l := take_drop sz (drop m l).
  have H3 : drop sz (drop m l) = drop (m + sz) l := drop_drop l sz m.
  have H2' : take sz (drop m l) ++ drop (m + sz) l = drop m l.
  { rewrite H3 in H2. exact H2. }
  rewrite H2'.
  by symmetry; exact H1.
Qed.

Lemma count_color_list_take_zero (c : N) (l : list tagged_byte) (sz : nat) :
  (forall i tb, i < sz -> l !! i = Some tb -> tbc_is_color c tb = false) ->
  count_color_list c (take sz l) = 0%N.
Proof.
  elim: sz l => [|sz IH] l H.
  - simpl. done.
  - case: l H => [|tb l] H.
    + simpl. done.
    + simpl.
      have Htb : tbc_is_color c tb = false.
      { apply: (H 0 tb); first by lia. simpl. done. }
      rewrite Htb.
      apply IH.
      move=> i tb' Hi Hlook.
      apply: (H (S i) tb'); first by lia.
      simpl. exact Hlook.
Qed.

Lemma tbc_is_color_ne (c d : N) (tb : tagged_byte) :
  tb.(tb_color) = Some d ->
  d <> c ->
  tbc_is_color c tb = false.
Proof.
  intros Hd Hnc.
  destruct tb as [v col tag] => /=.
  destruct col as [d'|]; last by discriminate.
  have Hdd' : d' = d.
  { inversion Hd. done. }
  rewrite Hdd'. (* : d' = d, so tbc_is_color c tb = N.eqb d c *)
  apply (proj2 (N.eqb_neq d c)). exact Hnc.
Qed.

Lemma isfree_not_color (cm : colored_memory_list) (A : allocator) (c' : N) (tb : tagged_byte) (a : N) :
  cm_lookup a cm = Some tb ->
  isfree a cm A ->
  isAlloc c' A ->
  tbc_is_color c' tb = false.
Proof.
  intros Hlook Hfree Halloc.
  unfold isfree in Hfree. rewrite Hlook in Hfree.
  destruct (tb_color tb) as [d|] eqn:Hco.
  - have Hdne : d <> c'.
    { intro Hdc'.
      unfold isAlloc in Halloc.
      have Htrue : A.(allocated) !! c' = Some true := Halloc.
      rewrite -Hdc' in Htrue.
      have Hdfalse : A.(allocated) !! d = Some false.
      { by move/eqP: Hfree. }
      rewrite Hdfalse in Htrue.
      discriminate. }
    exact (tbc_is_color_ne c' d tb Hco Hdne).
  - rewrite /tbc_is_color Hco. done.
Qed.

(* --- base_color auxiliary lemmas --- *)

Lemma base_color_index_app_general (c : N) (l1 l2 : list tagged_byte) :
  base_color_index c (l1 ++ l2) =
  match base_color_index c l1 with
  | Some j => Some j
  | None => option_map (Nat.add (length l1)) (base_color_index c l2)
  end.
Proof.
  induction l1 as [|tb l1 IH]; simpl.
  - destruct (base_color_index c l2); reflexivity.
  - destruct (tbc_is_color c tb) eqn:Hcol.
    + reflexivity.
    +  rewrite IH.
      destruct (base_color_index c l1) as [j1|] eqn:H1; simpl.
      * reflexivity.
      * destruct (base_color_index c l2) as [j2|]; simpl; done.
Qed.

Lemma base_color_index_repeat (c : N) (tb : tagged_byte) (n : nat) :
  0 < n ->
  tbc_is_color c tb = true ->
  base_color_index c (List.repeat tb n) = Some 0.
Proof.
  case: n => [|n] Hpos Hcol; first by lia.
  simpl. rewrite Hcol. done.
Qed.

(* --- more helpers --- *)

Lemma count_color_list_zero_forall (c : N) (l : list tagged_byte) :
  count_color_list c l = 0%N ->
  List.Forall (fun tb : tagged_byte => tbc_is_color c tb = false) l.
Proof.
  induction l as [|tb l IH]; simpl; first by constructor.
  destruct (tbc_is_color c tb) eqn:Hcol.
  - move=> Hz. exfalso. lia.
  - move=> Hz. constructor; [done | exact (IH Hz)].
Qed.

Lemma count_color_list_drop_zero (c : N) (l : list tagged_byte) (sz : nat) :
  (forall i tb, sz + i < length l -> l !! (sz + i) = Some tb -> tbc_is_color c tb = false) ->
  count_color_list c (drop sz l) = 0%N.
Proof.
  elim: sz l => [|sz IH].
  - move=> l H. 
    have Hall : forall tb : tagged_byte, List.In tb l -> tbc_is_color c tb = false.
    { move=> tb Hin.
      destruct (List.In_nth_error l tb Hin) as [i Hnth].
      have Hlt : i < length l.
      { apply (proj1 (List.nth_error_Some l i)).
        intro Hnone. rewrite Hnth in Hnone. discriminate. }
      have Hlook : l !! i = Some tb.
      { rewrite -nth_error_lookup. exact Hnth. }
      exact: (H i tb Hlt Hlook). }
    exact (count_color_list_forall_false c l (proj2 (@List.Forall_forall tagged_byte (fun tb : tagged_byte => tbc_is_color c tb = false) l) Hall)).
  - move=> l H. case: l H => [|tb tl] H.
    + simpl. done.
    + simpl.
      apply IH.
      move=> i tb' Hi Hlook.
      have Hij : S (sz + i) < length (tb :: tl).
      { simpl. lia. }
      have Hlookj : (tb :: tl) !! (S (sz + i)) = Some tb'.
      { simpl. exact Hlook. }
      exact: (H i tb' Hij Hlookj).
Qed.

Lemma count_color_list_zero_forall_in (c : N) (l : list tagged_byte) :
  count_color_list c l = 0%N ->
  forall tb : tagged_byte, List.In tb l -> tbc_is_color c tb = false.
Proof.
  move=> Hz tb Hin.
  exact (proj1 (@List.Forall_forall tagged_byte (fun tb : tagged_byte => tbc_is_color c tb = false) l) (count_color_list_zero_forall c l Hz) tb Hin).
Qed.

(* --- main calloc lemmas --- *)

Lemma calloc_count_color (M : cmem) (A : allocator) (a n c : N) (M' : cmem) (A' : allocator) :
  isSound A (cmem_data M) ->
  calloc M A a n c M' A' ->
  count_color c (cmem_data M') = n.
Proof.
  intros Hsound Hcalloc.
  inversion Hcalloc; subst.
  rewrite /new_data.
  unfold count_color.
  simpl.
  rewrite count_color_list_cat3.
  have Hzero : count_color c (cmem_data M) = 0%N := fresh_sound_no_color c A (cmem_data M) Hsound H0.
  unfold count_color in Hzero.
  have Hall : forall tb : tagged_byte, List.In tb (cml_data (cmem_data M)) -> tbc_is_color c tb = false.
  { move=> tb Hin. exact: (count_color_list_zero_forall_in c (cml_data (cmem_data M)) Hzero tb Hin). }
  have Htake0 : count_color_list c (take (N.to_nat a) (cml_data (cmem_data M))) = 0%N.
  { apply: (count_color_list_take_zero c (cml_data (cmem_data M)) (N.to_nat a)).
    move=> i tb Hi Hlook.
    have Hin : List.In tb (cml_data (cmem_data M)).
    { apply (@List.nth_error_In tagged_byte (cml_data (cmem_data M)) i tb).
      rewrite nth_error_lookup. exact Hlook. }
    exact: (Hall tb Hin). }
  have Hdrop0 : count_color_list c (drop (N.to_nat (a + n)) (cml_data (cmem_data M))) = 0%N.
  { apply: (count_color_list_drop_zero c (cml_data (cmem_data M)) (N.to_nat (a + n))).
    move=> i tb Hi Hlook.
    have Hin : List.In tb (cml_data (cmem_data M)).
    { apply (@List.nth_error_In tagged_byte (cml_data (cmem_data M)) (N.to_nat (a + n) + i) tb).
      rewrite nth_error_lookup. exact Hlook. }
    exact: (Hall tb Hin). }
  have Hrep : count_color_list c (List.repeat {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)) = N.of_nat (N.to_nat n).
  { apply count_color_list_repeat.
    rewrite /tbc_is_color. simpl.
    apply (proj2 (N.eqb_eq c c)). by []. }
  rewrite Htake0 Hdrop0 Hrep. lia.
Qed.

Lemma tbc_is_color_self (c : N) :
  tbc_is_color c {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} = true.
Proof.
  rewrite /tbc_is_color. simpl. apply (proj2 (N.eqb_eq c c)). by [].
Qed.

Lemma count_color_list_take_zero_in (c : N) (l : list tagged_byte) (sz : nat) :
  (forall tb : tagged_byte, List.In tb l -> tbc_is_color c tb = false) ->
  count_color_list c (take sz l) = 0%N.
Proof.
  move=> Hall.
  apply: (count_color_list_take_zero c l sz).
  move=> i tb Hi Hlook.
  have Hin : List.In tb l.
  { apply (@List.nth_error_In tagged_byte l i tb).
    rewrite nth_error_lookup. exact Hlook. }
  exact: (Hall tb Hin).
Qed.

Lemma count_color_list_drop_zero_in (c : N) (l : list tagged_byte) (sz : nat) :
  (forall tb : tagged_byte, List.In tb l -> tbc_is_color c tb = false) ->
  count_color_list c (drop sz l) = 0%N.
Proof.
  move=> Hall.
  apply: (count_color_list_drop_zero c l sz).
  move=> i tb Hi Hlook.
  have Hin : List.In tb l.
  { apply (@List.nth_error_In tagged_byte l (sz + i) tb).
    rewrite nth_error_lookup. exact Hlook. }
  exact: (Hall tb Hin).
Qed.

Lemma drop_lookup {T : Type} (l : list T) (n i : nat) (x : T) :
  drop n l !! i = Some x -> l !! (n + i) = Some x.
Proof.
  intro Hdi.
  have Hd : drop n l !! i = l !! (n + i) := lookup_drop l n i.
  rewrite Hd in Hdi.
  exact Hdi.
Qed.

Lemma cmem_index_region_zero (cm : colored_memory_list) (a n : N) (A : allocator) (d : N) :
  (forall a_off : N, (a <= a_off < a + n)%N -> isfree a_off cm A) ->
  isAlloc d A ->
  count_color_list d (take (N.to_nat n) (drop (N.to_nat a) (cml_data cm))) = 0%N.
Proof.
  intros Hfree Hdalloc.
  set l := cml_data cm.
  apply: (count_color_list_take_zero d (drop (N.to_nat a) l) (N.to_nat n)).
  move=> i tb Hi Hlookd.
  have Hlookl : l !! (N.to_nat a + i) = Some tb.
  { apply (drop_lookup l (N.to_nat a) i tb). exact Hlookd. }
  have HiN : (N.of_nat i < N.of_nat (N.to_nat n))%N := N_of_nat_lt_mono i (N.to_nat n) Hi.
  rewrite (N2Nat.id n) in HiN.
  have HfreeA : isfree (a + N.of_nat i)%N cm A.
  { apply Hfree. split; [lia | lia]. }
  have HlookA : cm_lookup (a + N.of_nat i)%N cm = Some tb.
  { unfold cm_lookup.
    rewrite N2Nat.inj_add. rewrite Nat2N.id. rewrite nth_error_lookup. exact Hlookl. }
  exact: (isfree_not_color cm A d tb (a + N.of_nat i)%N HlookA HfreeA Hdalloc).
Qed.

Lemma calloc_base_color (M : cmem) (A : allocator) (a n c : N) (M' : cmem) (A' : allocator) :
  (0 < n)%N ->
  isSound A (cmem_data M) ->
  calloc M A a n c M' A' ->
  base_color c (cmem_data M') = Some a.
Proof.
  intros Hpos Hsound Hcalloc.
  inversion Hcalloc; subst.
  rewrite /new_data.
  unfold base_color.
  simpl.
  rewrite base_color_index_app_general.
  have Hzero : count_color c (cmem_data M) = 0%N := fresh_sound_no_color c A (cmem_data M) Hsound H0.
  unfold count_color in Hzero.
  have Hall : forall tb : tagged_byte, List.In tb (cml_data (cmem_data M)) -> tbc_is_color c tb = false
    := count_color_list_zero_forall_in c (cml_data (cmem_data M)) Hzero.
  have Htak0 : count_color_list c (take (N.to_nat a) (cml_data (cmem_data M))) = 0%N.
  { apply: (count_color_list_take_zero_in c (cml_data (cmem_data M)) (N.to_nat a)). exact Hall. }
  have Hbt0 : base_color_index c (take (N.to_nat a) (cml_data (cmem_data M))) = None.
  { apply (proj2 (base_color_index_none_iff_count_color_list_zero c (take (N.to_nat a) (cml_data (cmem_data M))))). exact Htak0. }
  rewrite Hbt0.
  rewrite base_color_index_app_general.
  have Hpos' : 0 < N.to_nat n.
  { exact (N_to_nat_lt_mono 0 n Hpos). }
  have Hrep : base_color_index c (List.repeat {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)) = Some 0.
  { apply (base_color_index_repeat c {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)).
    - exact Hpos'.
    - exact (tbc_is_color_self c). }
  rewrite Hrep.
  simpl.
  have Hlen : length (take (N.to_nat a) (cml_data (cmem_data M))) = N.to_nat a.
  { apply take_length_le.
    have H1' : N.to_nat a <= N.to_nat (cmem_length M).
    { apply N_to_nat_le_mono. exact H1. }
    rewrite /cmem_length /cm_length in H1'.
    rewrite Nat2N.id in H1'.
    exact H1'.
  }
  rewrite Hlen.
  rewrite Nat.add_0_r.
  rewrite (N2Nat.id a).
  reflexivity.
Qed.

Lemma count_color_list_middle_decomp (c : N) (l : list tagged_byte) (m sz : nat) :
  count_color_list c l = (count_color_list c (take m l) + count_color_list c (take sz (drop m l)) + count_color_list c (drop (m + sz) l))%N.
Proof.
  rewrite {1}(take_drop_middle_decomp l m sz).
  rewrite count_color_list_cat3.
  done.
Qed.

Lemma calloc_count_color_preserved (M : cmem) (A : allocator) (a n c d : N) (M' : cmem) (A' : allocator) :
  isSound A (cmem_data M) ->
  calloc M A a n c M' A' ->
  isAlloc d A ->
  d <> c ->
  count_color d (cmem_data M') = count_color d (cmem_data M).
Proof.
  intros Hsound Hcalloc Hdalloc Hdc.
  inversion Hcalloc; subst.
  rewrite /new_data.
  unfold count_color.
  simpl.
  set l := cml_data (cmem_data M).
  have Hadd : N.to_nat (a + n) = N.to_nat a + N.to_nat n.
  { exact (N2Nat.inj_add a n). }
  rewrite Hadd.
  have Hdecomp : count_color_list d l = (count_color_list d (take (N.to_nat a) l) + count_color_list d (take (N.to_nat n) (drop (N.to_nat a) l)) + count_color_list d (drop (N.to_nat a + N.to_nat n) l))%N.
  { apply: (count_color_list_middle_decomp d l (N.to_nat a) (N.to_nat n)). }
  rewrite Hdecomp.
  rewrite !count_color_list_cat3.
  have Hrep0 : count_color_list d (List.repeat {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)) = 0%N.
  { apply count_color_list_repeat_false.
    apply (tbc_is_color_ne d c {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |}).
    - reflexivity.
    - intro Hcd. apply Hdc. exact (Logic.eq_sym Hcd). }
  have Hmid0 : count_color_list d (take (N.to_nat n) (drop (N.to_nat a) l)) = 0%N.
  { apply: (cmem_index_region_zero (cmem_data M) a n A d).
    - exact H.
    - exact Hdalloc. }
  rewrite Hrep0 Hmid0. lia.
Qed.

Lemma calloc_base_color_preserved (M : cmem) (A : allocator) (a n c d : N) (M' : cmem) (A' : allocator) :
  isSound A (cmem_data M) ->
  calloc M A a n c M' A' ->
  isAlloc d A ->
  d <> c ->
  base_color d (cmem_data M') = base_color d (cmem_data M).
Proof.
  intros Hsound Hcalloc Hdalloc Hdc.
  inversion Hcalloc; subst.
  rewrite /new_data.
  unfold base_color.
  simpl.
  set l := cml_data (cmem_data M).
  have Hadd : N.to_nat (a + n) = N.to_nat a + N.to_nat n.
  { exact (N2Nat.inj_add a n). }
  rewrite Hadd.
  have HdecompI : base_color_index d l =
                  base_color_index d (take (N.to_nat a) l ++ take (N.to_nat n) (drop (N.to_nat a) l) ++ drop (N.to_nat a + N.to_nat n) l).
  { rewrite {1}(take_drop_middle_decomp l (N.to_nat a) (N.to_nat n)). done. }
  rewrite HdecompI.
  rewrite !base_color_index_app_general.
  destruct (base_color_index d (take (N.to_nat a) l)) as [j |] eqn:Hbt.
  - simpl. done.
  - 
    have Hrep0 : count_color_list d (List.repeat {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)) = 0%N.
    { apply count_color_list_repeat_false.
      apply (tbc_is_color_ne d c {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |}).
      - reflexivity.
      - intro Hcd. apply Hdc. exact (Logic.eq_sym Hcd). }
    have Hrep_none : base_color_index d (List.repeat {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)) = None.
    { apply (proj2 (base_color_index_none_iff_count_color_list_zero d (List.repeat {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)))). exact Hrep0. }
    have Hmid0 : count_color_list d (take (N.to_nat n) (drop (N.to_nat a) l)) = 0%N.
    { apply: (cmem_index_region_zero (cmem_data M) a n A d).
      - exact H.
      - exact Hdalloc. }
    have Hmid_none : base_color_index d (take (N.to_nat n) (drop (N.to_nat a) l)) = None.
    { apply (proj2 (base_color_index_none_iff_count_color_list_zero d (take (N.to_nat n) (drop (N.to_nat a) l)))). exact Hmid0. }
    rewrite Hrep_none Hmid_none.
    destruct (base_color_index d (drop (N.to_nat a + N.to_nat n) l)) as [j |] eqn:HJ.
    + simpl.
      have Hlenrep : length (List.repeat {| tb_value := #00; tb_color := Some c; tb_tag := Numeric |} (N.to_nat n)) = N.to_nat n.
      { apply List.repeat_length. }
      have Hlenmid : length (take (N.to_nat n) (drop (N.to_nat a) l)) = N.to_nat n.
      { apply take_length_le.
        destruct (base_color_index_lookup d (drop (N.to_nat a + N.to_nat n) l) j HJ) as [tb [Hnth _]].
        have Hjlen : j < length (drop (N.to_nat a + N.to_nat n) l).
        { apply (proj1 (List.nth_error_Some _ j)).
          intro Hnone. rewrite Hnth in Hnone. discriminate. }
        rewrite drop_length in Hjlen.
        rewrite drop_length. lia. }
      rewrite Hlenrep Hlenmid. done.
    + simpl. done.
Qed.

Set Implicit Arguments.

End calloc_colors.


Definition load (m : memory) (n : N) (off : static_offset) (l : nat) : option bytes :=
  if N.leb (N.add n (N.add off (N.of_nat l))) (mem_length m)
  then read_bytes m (N.add n off) l
  else None.

Definition colload (cm : cmem) (p : pointer) (l : nat) :=
    if N.leb (N.add (ptr_addr p) (N.of_nat l)) (cmem_length cm)
    then read_colbytes cm (ptr_addr p) l
    else None
.


Lemma colload_read_colbytes_eq cm p l :
  ((N.leb (ptr_addr p + N.of_nat l) (cmem_length cm)) = true) ->
  colload cm p l = read_colbytes cm (ptr_addr p) l.
Proof.
  move => H.
  by rewrite /colload H.
Qed.

Lemma mem_iota_In (n i k : nat) : n \in iota i k -> List.In n (iota i k).
Proof.
  elim: k n i => [|k IH] n i H.
    by [simpl in H].
  simpl in H.
  move: H => /orP [/eqP -> | H].
  - by left.
  - right; exact: IH n i.+1 H.
Qed.

Lemma N2Nat_inj_le (a b : N) : (a <= b)%N -> N.to_nat a <= N.to_nat b.
Proof.
  move => Hle.
  apply/leP.
  lia.
Qed.

Lemma cm_lookup_oob (a : N) (cm : colored_memory_list) :
  (cm_length cm <= a)%N -> cm_lookup a cm = None.
Proof.
  rewrite /cm_lookup /cm_length => Hle.
  rewrite List.nth_error_None.
  have H : N.to_nat (N.of_nat (List.length (cml_data cm))) <= N.to_nat a :=
    N2Nat_inj_le (a := N.of_nat (List.length (cml_data cm))) (b := a) Hle.
    lias.
Qed.

Lemma mem_iota_pred (l : nat) : 0 < l -> (l - 1) \in iota 0 l.
Proof.
  move=> Hl.
  rewrite mem_iota.
  apply/andP; split.
  - exact: leq0n.
  - case: l Hl => [| n] Hl; first by move: (ltn0 0).
    by rewrite subn1; exact: ltnSn.
Qed.

Lemma colload_None_read_colbytes_None cm p l :
  0 < l -> colload cm p l = None -> read_colbytes cm (ptr_addr p) l = None.
Proof.
  intros.

  unfold read_colbytes.
  unfold colload in H0.
  case Hleb: ((ptr_addr p + N.of_nat l <=? cmem_length cm)%N) => //=.
  - rewrite Hleb in H0.
    unfold read_colbytes in H0 => //=.
  - rewrite Hleb in H0.
    assert (Hgt : (cmem_length cm < ptr_addr p + N.of_nat l)%N).
    { by rewrite N.leb_gt in Hleb. }
    assert (Hoob : (cmem_length cm <= ptr_addr p + N.of_nat (l - 1))%N). lias.
    assert (Hlast : cm_lookup (ptr_addr p + N.of_nat (l - 1)) (cmem_data cm) = None).
    { apply: cm_lookup_oob. exact: Hoob. }

    have Hmem : (l - 1) \in iota 0 l := mem_iota_pred H.
    have Hnin : List.In (l - 1) (iota 0 l) := mem_iota_In Hmem.
    have Hthose0_none : those0
      (map (fun off => cm_lookup (ptr_addr p + N.of_nat off) (cmem_data cm)) (iota 0 l)) = None.
    {
      elim: (iota 0 l) Hnin => [| x xs IH] //= Hnin2.
      simpl in Hnin2; case: Hnin2 => [-> | Hxs]; first by rewrite Hlast /=.
      case: (cm_lookup (ptr_addr p + N.of_nat x) (cmem_data cm)) => [y |]; last by [].
      by rewrite (IH Hxs) /=.
    }
    rewrite -(those_those0 (map _ _)).
    exact: Hthose0_none.
Qed.

Definition sign_extend (s : sx) (l : nat) (bs : bytes) : bytes :=
  (* To be implemented later *) bs.


Definition load_packed (s : sx) (m : memory) (n : N) (off : static_offset) (lp : nat) (l : nat) : option bytes :=
  option_map (sign_extend s l) (load m n off lp).

Definition store (m : memory) (n : N) (off : static_offset) (bs : bytes) (l : nat) : option memory :=
  if N.leb (n + off + N.of_nat l) (mem_length m)
  then write_bytes m (n + off) (bytes_takefill #00 l bs)
  else None.

Definition colstore (cm : cmem) (p : pointer) (bs : bytes) (col : option N) (tag : btag) (l : nat) : option cmem :=
  if N.leb (ptr_addr p + (N.of_nat l)) (cmem_length cm)
  then write_cmembytes cm (ptr_addr p) (bytes_takefill #00 l bs) col tag
  else None
.


Definition store_packed := store.
Section WasmBytes.
  Import ssrnat.
  Context `{PointerBytes}.

Definition wasm_deserialise (bs : bytes) (vt : value_type) : value :=
  match vt with
  | T_i32 => VAL_int32 (Wasm_int.Int32.repr (common.Memdata.decode_int bs))
  | T_i64 => VAL_int64 (Wasm_int.Int64.repr (common.Memdata.decode_int bs))
  | T_f32 => VAL_float32 (Floats.Float32.of_bits (Integers.Int.repr (common.Memdata.decode_int bs)))
  | T_f64 => VAL_float64 (Floats.Float.of_bits (Integers.Int64.repr (common.Memdata.decode_int bs)))
  | T_pointer => VAL_pointer (pointer_of_bytes bs)
  end.

Definition bits (v : value) : bytes :=
  match v with
  | VAL_numeric (NVAL_int32 c) => serialise_i32 c
  | VAL_numeric (NVAL_int64 c) => serialise_i64 c
  | VAL_numeric (NVAL_float32 c) => serialise_f32 c
  | VAL_numeric (NVAL_float64 c) => serialise_f64 c
  | VAL_pointer h => serialise_pointer h
  end.

Definition t_length (t : value_type) : nat :=
  match t with
  | T_i32 => 4
  | T_i64 => 8
  | T_f32 => 4
  | T_f64 => 8
  | T_pointer => pointer_size
  end.


Definition tp_length (tp : packed_type) : nat :=
  match tp with
  | Tp_i8 => 1
  | Tp_i16 => 2
  | Tp_i32 => 4
  end.

Definition is_int_t (t : value_type) : bool :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  | T_pointer => false
  end.

Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : value_type) : bool :=
  match tp with
  | None => Nat.pow 2 a <= t_length t
  | Some tp' => (Nat.pow 2 a <= tp_length tp') && (tp_length tp' < t_length t) && (is_int_t t)
  end.

Definition isAlign p :=
  (N.modulo (ptr_addr p) (N.of_nat (t_length T_pointer)) = N.of_nat 0)%N.

Definition isAlignb p : bool :=
  N.eqb (N.modulo (ptr_addr p) (N.of_nat (t_length T_pointer))) (N.of_nat 0).

Lemma isAlignP p : reflect (isAlign p) (isAlignb p).
Proof.
  rewrite /isAlign /isAlignb. exact: N.eqb_spec.
Qed.

Lemma isAlign_eq (p : pointer):
  isAlign p <-> isAlignb p.
Proof.
  unfold isAlign, isAlignb.
  split; first by move /eqP; auto.
  simpl.
  apply N.eqb_eq.
Qed.

End WasmBytes.


Definition typeof_numerical (v : numerical_value) : value_type :=
  match v with
  | (NVAL_int32 _) => T_i32
  | (NVAL_int64 _) => T_i64
  | (NVAL_float32 _) => T_f32
  | (NVAL_float64 _) => T_f64
  end.
Definition typeof (v : value) : value_type :=
  match v with
  | VAL_numeric v => typeof_numerical v
  | VAL_pointer _ => T_pointer
  end.

Definition option_projl (A B : Type) (x : option (A * B)) : option A :=
  option_map fst x.

Definition option_projr (A B : Type) (x : option (A * B)) : option B :=
  option_map snd x.






Definition is_float_t (t : value_type) : bool :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  | T_pointer => false
  end.

Definition is_pointer_t t :=
  match t with
  | T_pointer => true
  | _ => false end.

Definition is_mut (tg : global_type) : bool :=
  tg_mut tg == MUT_mut.


Definition app_unop_i (e : Wasm_int.type) (iop : unop_i) : Wasm_int.sort e -> Wasm_int.sort e :=
  let: Wasm_int.Pack u (Wasm_int.Class eqmx intmx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' in
  match iop with
  | UOI_ctz => Wasm_int.int_ctz intmx
  | UOI_clz => Wasm_int.int_clz intmx
  | UOI_popcnt => Wasm_int.int_popcnt intmx
  end.

Definition app_unop_f (e : Wasm_float.type) (fop : unop_f) : Wasm_float.sort e -> Wasm_float.sort e :=
  let: Wasm_float.Pack u (Wasm_float.Class eqmx mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' in
  match fop with
  | UOF_neg => Wasm_float.float_neg mx
  | UOF_abs => Wasm_float.float_abs mx
  | UOF_ceil => Wasm_float.float_ceil mx
  | UOF_floor => Wasm_float.float_floor mx
  | UOF_trunc => Wasm_float.float_trunc mx
  | UOF_nearest => Wasm_float.float_nearest mx
  | UOF_sqrt => Wasm_float.float_sqrt mx
  end.

Definition app_unop (op: unop) (v: value) :=
  match op with
  | Unop_i iop =>
    match v with
    | VAL_numeric (NVAL_int32 c) => VAL_int32 (@app_unop_i i32t iop c)
    | VAL_numeric (NVAL_int64 c) => VAL_int64 (@app_unop_i i64t iop c)
    | _ => v
    end
  | Unop_f fop =>
    match v with
    | VAL_numeric (NVAL_float32 c) => VAL_float32 (@app_unop_f f32t fop c)
    | VAL_numeric (NVAL_float64 c) => VAL_float64 (@app_unop_f f64t fop c)
    | _ => v
    end
  end.

Definition app_binop_i (e : Wasm_int.type) (iop : binop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> option (Wasm_int.sort e) :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> option (Wasm_int.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match iop with
  | BOI_add => add_some (Wasm_int.int_add mx)
  | BOI_sub => add_some (Wasm_int.int_sub mx)
  | BOI_mul => add_some (Wasm_int.int_mul mx)
  | BOI_div SX_U => Wasm_int.int_div_u mx
  | BOI_div SX_S => Wasm_int.int_div_s mx
  | BOI_rem SX_U => Wasm_int.int_rem_u mx
  | BOI_rem SX_S => Wasm_int.int_rem_s mx
  | BOI_and => add_some (Wasm_int.int_and mx)
  | BOI_or => add_some (Wasm_int.int_or mx)
  | BOI_xor => add_some (Wasm_int.int_xor mx)
  | BOI_shl => add_some (Wasm_int.int_shl mx)
  | BOI_shr SX_U => add_some (Wasm_int.int_shr_u mx)
  | BOI_shr SX_S => add_some (Wasm_int.int_shr_s mx)
  | BOI_rotl => add_some (Wasm_int.int_rotl mx)
  | BOI_rotr => add_some (Wasm_int.int_rotr mx)
  end.

Definition app_binop_f (e : Wasm_float.type) (fop : binop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> option (Wasm_float.sort e) :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> option (Wasm_float.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match fop with
  | BOF_add => add_some (Wasm_float.float_add mx)
  | BOF_sub => add_some (Wasm_float.float_sub mx)
  | BOF_mul => add_some (Wasm_float.float_mul mx)
  | BOF_div => add_some (Wasm_float.float_div mx)
  | BOF_min => add_some (Wasm_float.float_min mx)
  | BOF_max => add_some (Wasm_float.float_max mx)
  | BOF_copysign => add_some (Wasm_float.float_copysign mx)
  end.

Definition app_binop (op: binop) (v1: value) (v2: value) :=
  match op with
  | Binop_i iop =>
    match v1 with
    | VAL_numeric (NVAL_int32 c1) =>
      match v2 with
      | VAL_numeric (NVAL_int32 c2) => option_map (fun v => VAL_int32 v) (@app_binop_i i32t iop c1 c2)
      |  _ => None
      end
    | VAL_numeric (NVAL_int64 c1) =>
      match v2 with
      | VAL_numeric (NVAL_int64 c2) => option_map (fun v => VAL_int64 v) (@app_binop_i i64t iop c1 c2)
      |  _ => None
      end
    | _ => None
    end
  | Binop_f fop =>
    match v1 with
    | VAL_numeric (NVAL_float32 c1) =>
      match v2 with
      | VAL_numeric (NVAL_float32 c2) => option_map (fun v => VAL_float32 v) (@app_binop_f f32t fop c1 c2)
      |  _ => None
      end
    | VAL_numeric (NVAL_float64 c1) =>
      match v2 with
      | VAL_numeric (NVAL_float64 c2) => option_map (fun v => VAL_float64 v) (@app_binop_f f64t fop c1 c2)
      |  _ => None
      end
    | _ => None
    end
  end.

Definition app_testop_i (e : Wasm_int.type) (o : testop) : Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> bool in
  match o with
  | Eqz => Wasm_int.int_eqz mx
  end.

Definition app_relop_i (e : Wasm_int.type) (rop : relop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> bool in
  match rop with
  | ROI_eq => Wasm_int.int_eq mx
  | ROI_ne => @Wasm_int.int_ne _
  | ROI_lt SX_U => Wasm_int.int_lt_u mx
  | ROI_lt SX_S => Wasm_int.int_lt_s mx
  | ROI_gt SX_U => Wasm_int.int_gt_u mx
  | ROI_gt SX_S => Wasm_int.int_gt_s mx
  | ROI_le SX_U => Wasm_int.int_le_u mx
  | ROI_le SX_S => Wasm_int.int_le_s mx
  | ROI_ge SX_U => Wasm_int.int_ge_u mx
  | ROI_ge SX_S => Wasm_int.int_ge_s mx
  end.

Definition app_relop_f (e : Wasm_float.type) (rop : relop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> bool :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> bool in
  match rop with
  | ROF_eq => Wasm_float.float_eq mx
  | ROF_ne => @Wasm_float.float_ne _
  | ROF_lt => Wasm_float.float_lt mx
  | ROF_gt => Wasm_float.float_gt mx
  | ROF_le => Wasm_float.float_le mx
  | ROF_ge => Wasm_float.float_ge mx
  end.

Definition app_relop_p rop (p1 p2 : pointer) :=
  match rop with
  | ROP_eq => (ptr_addr p1) == (ptr_addr p2)
  | ROP_ne => (ptr_addr p1) != (ptr_addr p2)
  | ROP_lt => pointer_ltb p1 p2
  | ROP_gt => pointer_gtb p1 p2
  | ROP_le => pointer_leb p1 p2
  | ROP_ge => pointer_geb p1 p2
  end.

Definition app_relop (op: relop) (v1: value) (v2: value) :=
  match op with
  | Relop_i iop =>
    match v1 with
    | VAL_numeric (NVAL_int32 c1) =>
      match v2 with
      | VAL_numeric (NVAL_int32 c2) => @app_relop_i i32t iop c1 c2
      |  _ => false
      end
    | VAL_numeric (NVAL_int64 c1) =>
      match v2 with
      | VAL_numeric (NVAL_int64 c2) => @app_relop_i i64t iop c1 c2
      |  _ => false
      end
    | _ => false
    end
  | Relop_f fop =>
    match v1 with
    | VAL_numeric (NVAL_float32 c1) =>
      match v2 with
      | VAL_numeric (NVAL_float32 c2) => @app_relop_f f32t fop c1 c2
      |  _ => false
      end
    | VAL_numeric (NVAL_float64 c1) =>
      match v2 with
      | VAL_numeric (NVAL_float64 c2) => @app_relop_f f64t fop c1 c2
      |  _ => false
      end
    | _ => false
    end
  | Relop_p pop =>
      match v1 with
      | VAL_pointer p1 =>
          match v2 with
          | VAL_pointer p2 => app_relop_p pop p1 p2
          | _ => false
          end
      | _ => false
      end
  end.

Definition types_agree (t : value_type) (v : value) : bool :=
  (typeof v) == t.

Definition cl_type (cl : function_closure) : function_type :=
  match cl with
  | FC_func_native _ tf _ _ => tf
  | FC_func_host tf _ => tf
  end.

Definition rglob_is_mut (g : global) : bool :=
  g_mut g == MUT_mut.

Definition option_bind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some y => f y
  end.



Definition empty_instance := Build_instance [::] [::] [::] [::] [::].

Definition stypes (s : store_record) (i : instance) (j : nat) : option function_type :=
  List.nth_error (inst_types i) j.

Definition sfunc_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  List.nth_error (inst_funcs i) j.

Definition sfunc (s : store_record) (i : instance) (j : nat) : option function_closure :=
  option_bind (List.nth_error (s_funcs s)) (sfunc_ind s i j).

Definition sglob_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  List.nth_error (inst_globs i) j.

Definition sglob (s : store_record) (i : instance) (j : nat) : option global :=
  option_bind (List.nth_error (s_globals s))
    (sglob_ind s i j).

Definition sglob_val (s : store_record) (i : instance) (j : nat) : option value :=
  option_map g_val (sglob s i j).

Definition smem_ind (s : store_record) (i : instance) : option nat :=
  match i.(inst_memory) with
  | nil => None
  | cons k _ => Some k
  end.

Definition tab_size (t: tableinst) : nat :=
  length (table_data t).

(**
  Get the ith table in the store s, and then get the jth index in the table;
  in the end, retrieve the corresponding function closure from the store.
 **)
(**
  There is the interesting use of option_bind (fun x => x) to convert an element
  of type option (option x) to just option x.
**)
Definition stab_index (s: store_record) (i j: nat) : option nat :=
  let: stabinst := List.nth_error (s_tables s) i in
  option_bind (fun x => x) (
    option_bind
      (fun stab_i => List.nth_error (table_data stab_i) j)
  stabinst).

Definition stab_addr (s: store_record) (f: frame) (c: nat) : option nat :=
  match f.(f_inst).(inst_tab) with
  | nil => None
  | ta :: _ => stab_index s ta c
  end.


Definition stab_s (s : store_record) (i j : nat) : option function_closure :=
  let n := stab_index s i j in
  option_bind
    (fun id => List.nth_error (s_funcs s) id)
  n.

Definition stab (s : store_record) (i : instance) (j : nat) : option function_closure :=
  match i.(inst_tab) with
  | nil => None
  | k :: _ => stab_s s k j
  end.

Definition update_list_at {A : Type} (l : seq A) (k : nat) (a : A) :=
  take k l ++ [::a] ++ List.skipn (k + 1) l.

Definition supdate_glob_s (s : store_record) (k : nat) (v : value) : option store_record :=
  option_map
    (fun g =>
      let: g' := Build_global (g_mut g) v in
      let: gs' := update_list_at (s_globals s) k g' in
      Build_store_record (s_funcs s) (s_tables s) (s_mems s) (s_cmems s) (s_alls s) gs')
    (List.nth_error (s_globals s) k).

Definition supdate_glob (s : store_record) (i : instance) (j : nat) (v : value) : option store_record :=
  option_bind
    (fun k => supdate_glob_s s k v)
    (sglob_ind s i j).

Definition is_const (e : administrative_instruction) : bool :=
  match e with
  | AI_basic (BI_const _) => true
  | AI_pointer _ => true
  | _ => false
  end.


Definition const_list (es : seq administrative_instruction) : bool :=
  List.forallb is_const es.

(* The expected terminal instructions *)
Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap].

(* Take a list of administrative instructions, extract the consts and turn them into values *)
Definition those_const_list (es : list administrative_instruction) : option (list value) :=
  those (List.map (fun e => match e with | AI_pointer v => Some (VAL_pointer v) | AI_basic (BI_const v) => Some (VAL_numeric v) | _ => None end) es).

(* TODO: understand this *)
Definition glob_extension (g1 g2: global) : bool.
Proof.
  destruct (g_mut g1).
  - (* Immut *)
    exact ((g_mut g2 == MUT_immut) && (g_val g1 == g_val g2)).
  - (* Mut *)
    destruct (g_mut g2).
    + exact false.
    + destruct (g_val g1) as [n | ?] eqn:T1 ;
        try destruct n;
      lazymatch goal with
      | H1: g_val g1 = VAL_numeric (?T3 _) |- _ =>
          destruct (g_val g2) as [ n | ?] eqn:T2;
          try destruct n;
          lazymatch goal with
          | H2: g_val g2 = VAL_numeric (T3 _) |- _ => exact true
          | _ => exact false
          end
      | H1: g_val g1 = VAL_pointer _ |- _ =>
          destruct (g_val g2) eqn:T2;
          lazymatch goal with
          | H2: g_val g2 = VAL_pointer _ |- _ => exact true
          | _ => exact false
          end 
      | _ => exact false
      end.
Defined.

Section extensions.
  Import ssrnat.
Definition tab_extension (t1 t2 : tableinst) :=
  (tab_size t1 <= tab_size t2) &&
  (t1.(table_max_opt) == t2.(table_max_opt)).

Definition mem_extension (m1 m2 : memory) :=
  (N.leb (mem_size m1) (mem_size m2)) && (mem_max_opt m1 == mem_max_opt m2).

Definition cmem_extension (cm1 cm2 : cmem) :=
  (N.leb (cmem_size cm1) (cmem_size cm2)) && (cmem_max_opt cm1 == cmem_max_opt cm2).

Definition all_extension (a1 a2 : allocator) :=
  true.

Definition comp_extension {T: Type} (l1 l2: list T) (f: T -> T -> bool) : bool :=
  (length l1 <= length l2) &&
  (all2 f l1 (take (length l1) l2)).

Definition store_extension (s s' : store_record) : bool :=
  (s_funcs s == s_funcs s') &&
  (all2 tab_extension s.(s_tables) s'.(s_tables)) &&
    (all2 mem_extension s.(s_mems) s'.(s_mems)) &&
    (cmem_extension s.(s_cmems) s'.(s_cmems)) &&
    (all_extension s.(s_alls) s'.(s_alls)) &&
    (all2 glob_extension s.(s_globals) s'.(s_globals)).



Definition vs_to_vts (vs : seq value) := map typeof vs.

Definition to_e_list (bes : seq basic_instruction) : seq administrative_instruction :=
  map AI_basic bes.

(* Two versions of converting admin instructions back to basic *)
Definition to_b_single (e: administrative_instruction) : basic_instruction :=
  match e with
  | AI_basic x => x
  | _ => BI_const (NVAL_int32 (Wasm_int.Int32.zero))
  end.

Definition to_b_list (es: seq administrative_instruction) : seq basic_instruction :=
  map to_b_single es.

Definition to_b_single_opt (e: administrative_instruction) : option basic_instruction :=
  match e with
  | AI_basic x => Some x
  | _ => None
  end.

Definition to_b_list_opt (es: seq administrative_instruction) : option (seq basic_instruction) :=
  those (map to_b_single_opt es).

Definition e_is_basic (e: administrative_instruction) :=
  exists be, e = AI_basic be.

Fixpoint es_is_basic (es: seq administrative_instruction) :=
  match es with
  | [::] => True
  | e :: es' =>
    e_is_basic e /\ es_is_basic es'
  end.

Definition v_to_e (v: numerical_value) : administrative_instruction :=
  AI_basic (BI_const v).

(** [v_to_e_list]: 
    takes a list of [v] and gives back a list where each [v] is mapped to [Basic (EConst v)]. **)
Definition v_to_e_list (ves : seq value) : seq administrative_instruction :=
  map (fun v => AI_const v) ves.

(* interpreter related *)

Fixpoint split_vals (es : seq administrative_instruction) : seq value * seq administrative_instruction :=
  match es with
  | (AI_pointer v) :: es' =>
    let: (vs', es'') := split_vals es' in
    (VAL_pointer v :: vs', es'')
  | (AI_basic (BI_const v)) :: es' =>
      let: (vs', es'') := split_vals es' in
      (VAL_numeric v :: vs', es'')
  | _ => ([::], es)
  end.



(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [Basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
(* This is identical to split_vals_e *)
Fixpoint split_vals_e (es : seq administrative_instruction) : seq value * seq administrative_instruction :=
  match es with
  | (AI_pointer v) :: es' =>
      let: (vs', es'') := split_vals_e es' in
      (VAL_pointer v :: vs', es'')
  | (AI_basic (BI_const v)) :: es' =>
      let: (vs', es'') := split_vals_e es' in
      (VAL_numeric v :: vs', es'')
  | _ => ([::], es)
  end.

Lemma split_vals_not_empty_res : forall es v vs es',
  split_vals_e es = (v :: vs, es') -> es <> [::].
Proof. by case. Qed.

Lemma split_vals_e_not_const es vs e es' :
  split_vals_e es = (vs, e :: es') -> is_const e -> False.
Proof.
  generalize dependent vs . generalize dependent e . generalize dependent es'.
  induction es => //= . intros.
  destruct a => //= ; try by inversion H ; subst.
  destruct b => //= ; try by inversion H ; subst.
  all: destruct (split_vals_e es) as [??] eqn:Hes.
  all: destruct l0 => //=.
  all: inversion H ; subst.
  all: by eapply IHes.
Qed.




Fixpoint split_n (es : seq value) (n : nat) : seq value * seq value :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.


Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao with
  | Some a => f a
  | None => b
  end.

Definition expect' {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao as ao0 return (ao = ao0) -> B with
  | Some a => (fun _ => f a)
  | None => fun _ => b
  end (Logic.eq_refl ao).

Definition vs_to_es (vs : seq value) : seq administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  match e with
  | AI_trap => true
  | _ => false
  end.

(** [es_is_trap es] is equivalent to [es == [:: Trap]]. **)
Definition es_is_trap (es : seq administrative_instruction) : bool :=
  match es with
  | [::e] => e_is_trap e
  | _ => false
  end.



(** Converting a result into a stack. **)
Definition result_to_stack (r : result) :=
  match r with
  | result_values vs => v_to_e_list vs
  | result_trap => [:: AI_trap]
  end.

(* TODO: Check this whole section out *)
Fixpoint lfill (k : nat) (lh : lholed) (es : seq administrative_instruction) : option (seq administrative_instruction) :=
  match k with
  | 0 =>
    if lh is LH_base vs es' then
      if const_list vs then Some (app vs (app es es')) else None
    else None
  | k'.+1 =>
    if lh is LH_rec vs n es' lh' es'' then
      if const_list vs then
        if lfill k' lh' es is Some lfilledk then
          Some (app vs (cons (AI_label n es' lfilledk) es''))
        else None
      else None
    else None
  end.

Definition lfilled (k : nat) (lh : lholed) (es : seq administrative_instruction) (es' : seq administrative_instruction) : bool :=
  if lfill k lh es is Some es'' then es' == es'' else false.

Inductive lfilledInd : nat -> lholed -> seq administrative_instruction -> seq administrative_instruction -> Prop :=
| LfilledBase: forall vs es es',
    const_list vs ->
    lfilledInd 0 (LH_base vs es') es (vs ++ es ++ es')
| LfilledRec: forall k vs n es' lh' es'' es LI,
    const_list vs ->
    lfilledInd k lh' es LI ->
    lfilledInd (k.+1) (LH_rec vs n es' lh' es'') es (vs ++ [ :: (AI_label n es' LI) ] ++ es'').

Lemma lfilled_Ind_Equivalent: forall k lh es LI,
    lfilled k lh es LI <-> lfilledInd k lh es LI.
Proof.
  move => k. split.
  - move: lh es LI. induction k; move => lh es LI HFix.
    + unfold lfilled in HFix. simpl in HFix. destruct lh => //=.
      * destruct (const_list l) eqn:HConst => //=.
        { replace LI with (l++es++l0); first by apply LfilledBase.
          symmetry. move: HFix. by apply/eqseqP. }
    + unfold lfilled in HFix. simpl in HFix. destruct lh => //=.
      * destruct (const_list l) eqn:HConst => //=.
        { destruct (lfill k lh es) eqn:HLF => //=.
          { replace LI with (l ++ [ :: (AI_label n l0 l2)] ++ l1).
          apply LfilledRec; first by [].
          apply IHk. unfold lfilled; first by rewrite HLF.
          symmetry. move: HFix. by apply/eqseqP. }
        }
  - move => HLF. induction HLF.
    + unfold lfilled. unfold lfill. by rewrite H.
    + unfold lfilled. unfold lfill. rewrite H. fold lfill.
      unfold lfilled in IHHLF. destruct (lfill k lh' es) => //=.
      * replace LI with l => //=.
        symmetry. by apply/eqseqP.
Qed.

Lemma lfilledP: forall k lh es LI,
    reflect (lfilledInd k lh es LI) (lfilled k lh es LI).
Proof.
  move => k lh es LI. destruct (lfilled k lh es LI) eqn:HLFBool.
  - apply ReflectT. by apply lfilled_Ind_Equivalent.
  - apply ReflectF. move=> HContra. apply lfilled_Ind_Equivalent in HContra.
    by rewrite HLFBool in HContra.
Qed.

Fixpoint lfill_exact (k : nat) (lh : lholed) (es : seq administrative_instruction) : option (seq administrative_instruction) :=
  match k with
  | 0 =>
    if lh is LH_base nil nil then Some es else None
  | k'.+1 =>
    if lh is LH_rec vs n es' lh' es'' then
      if const_list vs then
        if lfill_exact k' lh' es is Some lfilledk then
          Some (app vs (cons (AI_label n es' lfilledk) es''))
        else None
      else None
    else None
  end.

End extensions.

Definition lfilled_exact (k : nat) (lh : lholed) (es : seq administrative_instruction) (es' : seq administrative_instruction) : bool :=
  if lfill_exact k lh es is Some es'' then es' == es'' else false.

Fixpoint lh_depth lh :=
  match lh with
  | LH_base _ _ => 0
  | LH_rec _ _ _ lh _ => S (lh_depth lh)
  end.


Definition result_types_agree (ts : result_type) r :=
  match r with
  | result_values vs => all2 types_agree ts vs
  | result_trap => true
  end.





Definition cvt_i32 (s : option sx) (v : value) : option i32 :=
  match v with
  | VAL_numeric (NVAL_int32 _) => None
  | VAL_numeric (NVAL_int64 c) => Some (wasm_wrap c)
  | VAL_numeric (NVAL_float32 c) =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f32m c
    | Some SX_S => Wasm_float.float_ui32_trunc f32m c
    | None => None
    end
  | VAL_numeric (NVAL_float64 c) =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f64m c
    | Some SX_S => Wasm_float.float_ui32_trunc f64m c
    | None => None
    end
  | VAL_pointer p => None
  end.

Definition cvt_i64 (s : option sx) (v : value) : option i64 :=
  match v with
  | VAL_numeric (NVAL_int32 c) =>
    match s with
    | Some SX_U => Some (wasm_extend_u c)
    | Some SX_S => Some (wasm_extend_s c)
    | None => None
    end
  | VAL_numeric (NVAL_int64 c) => None
  | VAL_numeric (NVAL_float32 c) =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f32m c
    | Some SX_S => Wasm_float.float_si64_trunc f32m c
    | None => None
    end
  | VAL_numeric (NVAL_float64 c) =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f64m c
    | Some SX_S => Wasm_float.float_si64_trunc f64m c
    | None => None
    end
  | VAL_pointer _ => None
  end.

Definition cvt_f32 (s : option sx) (v : value) : option f32 :=
  match v with
  | VAL_numeric (NVAL_int32 c) =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f32m c)
    | None => None
    end
  | VAL_numeric (NVAL_int64 c) =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f32m c)
    | None => None
    end
  | VAL_numeric (NVAL_float32 c) => None
  | VAL_numeric (NVAL_float64 c) => Some (wasm_demote c)
  | VAL_pointer _ => None
  end.

Definition cvt_f64 (s : option sx) (v : value) : option f64 :=
  match v with
  | VAL_numeric (NVAL_int32 c) =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f64m c)
    | None => None
    end
  | VAL_numeric (NVAL_int64 c) =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f64m c)
    | None => None
    end
  | VAL_numeric (NVAL_float32 c) => Some (wasm_promote c)
  | VAL_numeric (NVAL_float64 c) => None
  | VAL_pointer _ => None
  end.


Definition cvt (t : value_type) (s : option sx) (v : value) : option value :=
  match t with
  | T_i32 => option_map VAL_int32 (cvt_i32 s v)
  | T_i64 => option_map VAL_int64 (cvt_i64 s v)
  | T_f32 => option_map VAL_float32 (cvt_f32 s v)
  | T_f64 => option_map VAL_float64 (cvt_f64 s v)
  | T_pointer => None
  end.



Definition bitzero (t : value_type) : value :=
  match t with
  | T_i32 => VAL_int32 (Wasm_int.int_zero i32m)
  | T_i64 => VAL_int64 (Wasm_int.int_zero i64m)
  | T_f32 => VAL_float32 (Wasm_float.float_zero f32m)
  | T_f64 => VAL_float64 (Wasm_float.float_zero f64m)
  | T_pointer => VAL_pointer dummy_pointer
  end.

Definition n_zeros (ts : seq value_type) : seq value :=
  map bitzero ts.



Definition is_none_or {A : Type} (p : A -> bool) (x : option A) : bool :=
  match x with
  | None => true
  | Some y => p y
  end.

Lemma b2p: forall {T:eqType} (a b:T), a==b -> a=b.
Proof. move => T a b Hb. by move/eqP in Hb. Qed.


Lemma cat_app {A} (l1 : list A) l2 :
  cat l1 l2 = app l1 l2.
Proof. done. Qed.









Lemma first_values vs1 e1 es1 vs2 e2 es2 :
  (is_const e1 = false) ->
  (is_const e2 = false) ->
  const_list vs1 ->
  const_list vs2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  intros He1 He2 Hvs1 Hvs2 Heq.
  generalize dependent vs2. induction vs1 ; intros.
  { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
    simpl in Hvs2. apply Bool.andb_true_iff in Hvs2 as [ Habs _ ].
    rewrite Habs in He1 => //.
  }
  destruct vs2 ; inversion Heq.
  { rewrite H0 in Hvs1.
    simpl in Hvs1. apply Bool.andb_true_iff in Hvs1 as [ Habs _ ].
    rewrite Habs in He2 => //.
  }
  assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
  apply IHvs1 => //=.
  - by apply Bool.andb_true_iff in Hvs1 as [ _ Hvs1 ].
  - by apply Bool.andb_true_iff in Hvs2 as [ _ Hvs2 ].
Qed.

Definition is_pointer (v : value) :=
  match v with
  | VAL_pointer _ => true
  | VAL_numeric _ => false
  end.
