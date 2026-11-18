From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From CWasm.iriscwasm.rules Require Import iris_rules proofmode iris_example_helper.
From CWasm.iriscwasm.language Require Import iris_wp_def.
From CWasm Require Import opsem common stdpp_aux.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Notation "{{{ P }}} es {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗
    WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

Notation "{{{ P }}} es @ E {{{ v , Q }}}" :=
  (□ ∀ Φ, P -∗ (∀ v : iris.val, Q -∗ Φ v) -∗
    WP (es : iris.expr) @ NotStuck ; E {{ v, Φ v }})%I (at level 50).

Definition i32const (n : Z) :=
  BI_const (NVAL_int32 (Wasm_int.int_of_Z i32m n)).
Definition value_of_int (n : Z) :=
  VAL_int32 (Wasm_int.int_of_Z i32m n).
Definition nvalue_of_int (n : Z) :=
  NVAL_int32 (Wasm_int.int_of_Z i32m n).

Definition u32const (n : N) :=
  BI_const (NVAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n))).
Definition value_of_uint (n : N) :=
  VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n)).
Definition value_of_pointer (p : pointer) := VAL_pointer p.

Definition two14 := 16384%N.
Definition two16 := 65536%N.
Definition two32 := 4294967296%N.
Definition ffff0000 := 4294901760%N.

(** Four consecutive numeric-tagged bytes containing an i32. *)
Definition points_to_i32 `{!wasmG Σ} (a c : N) (v : i32) : iProp Σ :=
  wcs a c Numeric (serialise_i32 v).

Notation "a ↦[i32]{ c } v" := (points_to_i32 a c v)
  (at level 50) : bi_scope.

Lemma u32_modulus : Wasm_int.Int32.modulus = 4294967296%Z.
Proof. by lias. Qed.

Lemma of_nat_to_nat_plus a b :
  N.of_nat (N.to_nat a + b) = (a + N.of_nat b)%N.
Proof. lia. Qed.

Lemma drop_is_nil {A} n (s : seq.seq A) :
  drop n s = [] -> n >= length s.
Proof.
  move=> Hdrop.
  assert (length s - n = 0) as Hdroplen.
  { by rewrite -drop_length Hdrop. }
  by lias.
Qed.

Lemma in_take {A} n s (x : A) :
  In x (take n s) -> In x s.
Proof.
  move=> Hin.
  apply elem_of_list_In, elem_of_take in Hin as [i [? ?]].
  apply elem_of_list_In, elem_of_list_lookup.
  by eexists.
Qed.

Lemma two16_div_i32 :
  (Z.of_N two16 | Wasm_int.Int32.modulus)%Z.
Proof.
  rewrite u32_modulus.
  unfold two16. exists 65536%Z. lia.
Qed.

Lemma wasm_int_signed x :
  (-2147483648 <= x <= 2147483647)%Z ->
  Wasm_int.Int32.signed (Wasm_int.Int32.repr x) = x.
Proof.
  move=> Hbound.
  rewrite Wasm_int.Int32.signed_repr; first by lias.
  unfold Wasm_int.Int32.min_signed, Wasm_int.Int32.max_signed,
    Wasm_int.Int32.half_modulus.
  rewrite u32_modulus.
  replace (4294967296 `div` 2)%Z with 2147483648%Z; by lias.
Qed.

Lemma wasm_int_unsigned x :
  (0 <= x <= 4294967295)%Z ->
  Wasm_int.Int32.unsigned (Wasm_int.Int32.repr x) = x.
Proof.
  move=> Hbound.
  rewrite Wasm_int.Int32.unsigned_repr; first by lias.
  unfold Wasm_int.Int32.max_unsigned.
  rewrite u32_modulus.
  by lias.
Qed.

Lemma value_of_int_repr a :
  exists v, VAL_int32 a = value_of_int v.
Proof.
  exists (Wasm_int.Z_of_uint i32m a).
  unfold value_of_int. simpl.
  by rewrite Wasm_int.Int32.repr_unsigned.
Qed.

Lemma value_of_uint_repr a :
  exists v, VAL_int32 a = value_of_uint v.
Proof.
  exists (Z.to_N (Wasm_int.Z_of_uint i32m a)).
  unfold value_of_uint. simpl.
  rewrite Z2N.id.
  - by rewrite Wasm_int.Int32.repr_unsigned.
  - pose proof (Wasm_int.Int32.unsigned_range a). lia.
Qed.

Lemma div_mod_i32 v :
  let k := Wasm_int.N_of_uint i32m
    (Wasm_int.int_of_Z i32m (Z.of_N v)) in
  (65536 | v)%N -> (65536 | k)%N.
Proof.
  intros k Hdiv. subst k.
  simpl. destruct Hdiv as [x ->].
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  replace Wasm_int.Int32.modulus with (65536 * 65536)%Z => //.
  rewrite Z2N.inj_mod; try lia.
  rewrite N2Z.id Z2N.inj_mul; try lia.
  simpl Z.to_N.
  apply N.Lcm0.mod_divide.
  rewrite N.Div0.mul_mod_distr_r; try lia.
  rewrite N.Div0.mul_mod_idemp_l; try lia.
  rewrite N.Div0.mod_mul; lia.
Qed.

Lemma int_of_Z_mod v :
  Wasm_int.int_of_Z i32m (Z.of_N v) =
  Wasm_int.int_of_Z i32m
    (Z.of_N (Z.to_N (Wasm_int.Int32.Z_mod_modulus (Z.of_N v)))).
Proof.
  simpl.
  rewrite Z2N.id;
    [|pose proof (Wasm_int.Int32.Z_mod_modulus_range (Z.of_N v)); lia].
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  rewrite -Wasm_int.Int32.unsigned_repr_eq.
  by rewrite Wasm_int.Int32.repr_unsigned.
Qed.

Section Stack.
  Set Bullet Behavior "Strict Subproofs".
  Context `{!wasmG Σ}.

  Lemma points_to_i32_eq a1 c1 v1 a2 c2 v2 :
    a1 = a2 -> c1 = c2 -> v1 = v2 ->
    a1 ↦[i32]{c1} v1 -∗ a2 ↦[i32]{c2} v2.
  Proof. intros -> -> ->. by iIntros. Qed.

  Lemma wcs_eq a1 c1 tag1 bs1 a2 c2 tag2 bs2 :
    a1 = a2 -> c1 = c2 -> tag1 = tag2 -> bs1 = bs2 ->
    wcs a1 c1 tag1 bs1 -∗ wcs a2 c2 tag2 bs2.
  Proof. intros -> -> -> ->. by iIntros. Qed.

  Lemma wcs_app a c tag (bs1 bs2 : list byte) :
    wcs a c tag (bs1 ++ bs2) ⊣⊢
      (wcs a c tag bs1 ∗
       wcs (a + N.of_nat (length bs1))%N c tag bs2).
  Proof.
    rewrite /wcs big_sepL_app.
    apply bi.sep_proper; first done.
    apply big_sepL_proper. intros i b Hb.
    replace (N.of_nat (N.to_nat a + (length bs1 + i)))
      with (N.of_nat (N.to_nat (a + N.of_nat (length bs1)) + i));
      [done|lia].
  Qed.

  (** [isStack p s] describes a one-page colored allocation rooted at [p].
      Its first i32 stores the stack height in bytes.  The list is ordered
      from the top of the stack downwards; the remainder of the allocation is
      owned as numeric-tagged bytes. *)
  Definition isStack (p : pointer) (s : seq.seq i32) : iProp Σ :=
    let st_p := (N.of_nat (length s) * 4)%N in
    ∃ c : N,
      ⌜ptr_col p = Some c⌝ ∗
      ⌜ptr_freeable p = true⌝ ∗
      ⌜(N.of_nat (length s) < two14)%N⌝ ∗
      wall c (ptr_addr p) two16 ∗
      live_color c ∗
      ptr_addr p ↦[i32]{c}
        (Wasm_int.Int32.repr (Z.of_N st_p)) ∗
      ([∗ list] i ↦ w ∈ s,
        (ptr_addr p + st_p - (4 * N.of_nat i))%N ↦[i32]{c} w) ∗
      ∃ bs : list byte,
        ⌜N.of_nat (length bs) =
          (two16 - 4 - N.of_nat (length s) * 4)%N⌝ ∗
        wcs (ptr_addr p + st_p + 4)%N c Numeric bs.

  Definition stk : string := "STACK".
  Definition stkN : namespace := nroot .@ stk.

  Lemma N_divide_dec : ∀ a b : N, {(a | b)%N} + {¬ (a | b)%N}.
  Proof.
    intros. destruct (decide ((N.to_nat a) | (N.to_nat b))).
    - left. destruct d. exists (N.of_nat x). lia.
    - right. intros Hcontr. apply n.
      destruct Hcontr. exists (N.to_nat x). lia.
  Qed.

  Inductive multiples_upto : N -> N -> list N -> Prop :=
  | mu_base_nil n : (n > 0)%N -> multiples_upto n 0 []
  | mu_ind n m l : multiples_upto n m l ->
      multiples_upto n (m + n) (m :: l).

  Lemma multiples_upto_nil n m l :
    multiples_upto n m l -> (n > 0)%N.
  Proof. intros H. induction H; auto. Qed.

  Lemma multiples_upto_le n m l :
    (m > 0)%N -> multiples_upto n m l -> (n <= m)%N.
  Proof. intros Hm. induction 1; by lias. Qed.

  Lemma le_mul x n :
    (2 <= x)%N -> (0 < n)%N -> (n < x * n)%N.
  Proof. by lias. Qed.

  Lemma lt_mul x n : (x * n < n)%N -> x = 0%N.
  Proof. by lias. Qed.

  Lemma multiples_upto_div :
    forall n m l, multiples_upto n m l -> (n | m)%N.
  Proof.
    induction 1.
    - apply N.divide_0_r.
    - apply N.divide_add_r; auto. apply N.divide_refl.
  Qed.

  Lemma multiples_upto_in_lt :
    forall n m l i, multiples_upto n m l -> i ∈ l -> (i < m)%N.
  Proof.
    induction 1; intros Hin.
    - inversion Hin.
    - inversion Hin; subst.
      + apply multiples_upto_nil in H. lia.
      + apply IHmultiples_upto in H2. lia.
  Qed.

  Lemma multiples_upto_in_div :
    forall n m l i, multiples_upto n m l -> i ∈ l -> (n | i)%N.
  Proof.
    induction 1; intros Hin.
    - inversion Hin.
    - inversion Hin; subst.
      + apply multiples_upto_div in H. auto.
      + apply IHmultiples_upto in H2. auto.
  Qed.

  Lemma times_lt n1 n2 n3 : n1 * n3 < n2 * n3 -> n1 < n2.
  Proof. by lias. Qed.

  Lemma times_lt_plus x x0 n :
    n > 0 -> x * n < x0 * n + n -> x <= x0.
  Proof. by lias. Qed.

  Lemma Nat2N_le_inj n1 n2 :
    n1 <= n2 <-> (N.of_nat n1 <= N.of_nat n2)%N.
  Proof. lia. Qed.

  Lemma Nat2N_lt_inj n1 n2 :
    n1 < n2 <-> (N.of_nat n1 < N.of_nat n2)%N.
  Proof. lia. Qed.

  Lemma N2Nat_le_inj n1 n2 :
    N.to_nat n1 <= N.to_nat n2 <-> (n1 <= n2)%N.
  Proof. lia. Qed.

  Lemma N2Nat_lt_inj n1 n2 :
    N.to_nat n1 < N.to_nat n2 <-> (n1 < n2)%N.
  Proof. lia. Qed.

  Lemma multiples_upto_in :
    forall n m l i, multiples_upto n m l ->
      (i < m)%N -> (n | i)%N -> i ∈ l.
  Proof.
    intros n m l i H lt.
    assert (0 <= m)%N as lm by lia.
    revert H lm lt.
    generalize dependent i.
    generalize dependent l.
    generalize dependent m.
    generalize dependent n.
    induction 1.
    - lia.
    - intros lm lt div.
      apply multiples_upto_div in H as div'.
      destruct (decide (i = m)); subst.
      + constructor.
      + constructor. apply IHmultiples_upto; auto.
        * destruct m; [|lia]. lias.
        * destruct div, div'; subst.
          apply N2Nat_lt_inj in lt.
          rewrite !N2Nat.inj_add !N2Nat.inj_mul in lt.
          apply times_lt_plus in lt; [|lia].
          apply N2Nat_le_inj in lt.
          apply N.mul_le_mono_r with _ _ n in lt. lia.
  Qed.

  Lemma stack_pure p s :
    isStack p s -∗
      ∃ c, ⌜ptr_col p = Some c⌝ ∗
           ⌜ptr_freeable p = true⌝ ∗
           ⌜(N.of_nat (length s) < two14)%N⌝.
  Proof.
    iIntros "Hs". iDestruct "Hs" as (c) "(% & % & % & _)".
    iExists c. auto.
  Qed.

  Lemma pointer_arith_addr p d p' :
    pointer_arith p d = Some p' ->
    ptr_addr p' = Z.to_N (Z.of_N (ptr_addr p) + d).
  Proof.
    rewrite /pointer_arith.
    destruct (0 <=? Z.of_N (ptr_addr p) + d)%Z eqn:Hnonneg => //.
    by move=> [<-].
  Qed.

  Lemma pointer_arith_col p d p' :
    pointer_arith p d = Some p' -> ptr_col p' = ptr_col p.
  Proof.
    rewrite /pointer_arith.
    destruct (0 <=? Z.of_N (ptr_addr p) + d)%Z => //.
    by move=> [<-].
  Qed.

  Lemma pointer_arith_freeable p d p' :
    pointer_arith p d = Some p' -> ptr_freeable p' = ptr_freeable p.
  Proof.
    rewrite /pointer_arith.
    destruct (0 <=? Z.of_N (ptr_addr p) + d)%Z => //.
    by move=> [<-].
  Qed.

  Lemma pointer_arith_same_origin p d p' :
    pointer_arith p d = Some p' -> same_origin p' p.
  Proof.
    move=> H. unfold same_origin.
    by rewrite (pointer_arith_col H).
  Qed.

  Lemma pointer_arith_diff p d p' :
    pointer_arith p d = Some p' ->
    (Z.of_N (ptr_addr p') - Z.of_N (ptr_addr p) = d)%Z.
  Proof.
    rewrite /pointer_arith.
    destruct (0 <=? Z.of_N (ptr_addr p) + d)%Z eqn:Hnonneg => //.
    move=> [<-]. apply Z.leb_le in Hnonneg. simpl.
    rewrite Z2N.id; lia.
  Qed.

  Lemma pointer_arith_compose p p' d1 d2 :
    pointer_arith p d1 = Some p' ->
    pointer_arith p' d2 = pointer_arith p (d1 + d2).
  Proof.
    rewrite /pointer_arith.
    destruct (0 <=? Z.of_N (ptr_addr p) + d1)%Z eqn:Hnonneg => //.
    move=> [<-]. apply Z.leb_le in Hnonneg. simpl.
    rewrite Z2N.id; last lia.
    replace (Z.of_N (ptr_addr p) + d1 + d2)%Z
      with (Z.of_N (ptr_addr p) + (d1 + d2))%Z by lia.
    done.
  Qed.

  Section proofs.
    Context `{HPB : PointerBytes}.

    Lemma stack_load_0 p s f E :
      isStack p s -∗
      ↪[frame] f -∗
      WP [AI_pointer p; AI_basic (BI_colload T_i32)] @ E
      {{ w, ⌜w = immV [value_of_uint (N.of_nat (length s) * 4)]⌝ ∗
             isStack p s ∗ ↪[frame] f }}.
    Proof.
      iIntros "Hs Hf" => /=.
      iDestruct "Hs" as (c) "(%Hcol & %Hfree & %Hlen & Hwall & Hlive & Hbase & Helems & Htail)".
      iApply (wp_wand with "[-]").
      - iApply (wp_colload NotStuck E
          (λ w, (⌜w = immV [value_of_uint (N.of_nat (length s) * 4)]⌝ ∗
                 isStack p s)%I)
          p T_i32 c (ptr_addr p) two16
          (bits (value_of_uint (N.of_nat (length s) * 4)))
          (value_of_uint (N.of_nat (length s) * 4)) f with
          "[-]").
        + done.
        + done.
        + apply deserialise_bits. done.
        + exact Hcol.
        + iSplitR "Hf Hbase Hwall".
          * iNext. iIntros "[Hbase Hwall]".
            iSplit; first done.
            iExists c. iFrame. auto.
          * iFrame.
      - iIntros (w) "[[Hw Hs] Hf]". iFrame.
    Qed.

    Lemma stack_load_0_alt p s f E k :
      ⌜k = (N.of_nat (length s) * 4)%N⌝ -∗
      isStack p s -∗
      ↪[frame] f -∗
      WP [AI_pointer p; AI_basic (BI_colload T_i32)] @ E
      {{ w, ⌜w = immV [value_of_uint k]⌝ ∗ isStack p s ∗
             ↪[frame] f }}.
    Proof.
      iIntros "%Hk Hs Hf". subst k.
      by iApply (stack_load_0 with "Hs Hf").
    Qed.

    Lemma stack_load_j p s f E j sv p' :
      ⌜s !! N.to_nat j = Some sv⌝ -∗
      ⌜pointer_arith p (length s * 4 - 4 * Z.of_N j) = Some p'⌝ -∗
      isStack p s -∗ ↪[frame] f -∗
      WP [AI_pointer p'; AI_basic (BI_colload T_i32)] @ E
      {{ w, ⌜w = immV [VAL_int32 sv]⌝ ∗ isStack p s ∗ ↪[frame] f }}.
    Proof.
      iIntros "%Hsv %Hadd Hs Hf".
      have Hj := lookup_lt_Some _ _ _ Hsv.
      have Haddr : ptr_addr p' =
        (ptr_addr p + N.of_nat (length s) * 4 - 4 * j)%N.
      { rewrite (pointer_arith_addr Hadd). lia. }
      iDestruct "Hs" as (c)
        "(%Hcol & %Hfree & %Hlen & Hwall & Hlive & Hbase & Helems & Htail)".
      iDestruct (big_sepL_lookup_acc with "Helems") as "[Hj Hclose]";
        first exact Hsv.
      rewrite N2Nat.id.
      iApply (wp_wand with "[-]").
      - iApply (wp_colload NotStuck E
          (λ w, (⌜w = immV [VAL_int32 sv]⌝ ∗ isStack p s)%I)
          p' T_i32 c (ptr_addr p) two16 (bits (VAL_int32 sv))
          (VAL_int32 sv) f with "[-]").
        + done.
        + done.
        + apply deserialise_bits. done.
        + by rewrite (pointer_arith_col Hadd).
        + rewrite Haddr. iFrame "Hf Hwall Hj".
          iNext. iIntros "[Hj Hwall]".
          iDestruct ("Hclose" with "Hj") as "Helems".
          iSplit; first done. iExists c. iFrame. auto.
      - iIntros (w) "[[Hw Hs] Hf]". iFrame.
    Qed.

    Lemma stack_load_j_pointer_add p s f E j sv :
      ⌜s !! N.to_nat j = Some sv⌝ -∗
      ⌜(j < N.of_nat (length s))%N⌝ -∗
      isStack p s -∗ ↪[frame] f -∗
      WP [AI_basic (BI_const (nvalue_of_int (length s * 4 - 4 * Z.of_N j)));
          AI_pointer p; AI_basic BI_pointeradd; AI_basic (BI_colload T_i32)] @ E
      {{ w, ⌜w = immV [VAL_int32 sv]⌝ ∗ isStack p s ∗ ↪[frame] f }}.
    Proof.
      iIntros "%Hsv %Hj Hs Hf".
      iDestruct (stack_pure with "Hs") as (c) "(%Hcol & %Hfree & %Hlen)".
      have Hd : (-2147483648 <= length s * 4 - 4 * Z.of_N j <= 2147483647)%Z.
      { unfold two14 in Hlen. lia. }
      have Hadd : pointer_arith p (length s * 4 - 4 * Z.of_N j) =
        Some (upd_pointer_addr p
          (Z.to_N (Z.of_N (ptr_addr p) + (length s * 4 - 4 * Z.of_N j)))).
      { unfold pointer_arith.
        destruct (0 <=? Z.of_N (ptr_addr p) +
          (length s * 4 - 4 * Z.of_N j))%Z eqn:Hnonneg; first done.
        apply Z.leb_gt in Hnonneg. lia. }
      rewrite separate3. iApply wp_seq.
      iSplitR; last iSplitL "Hf".
      2: { fold_const. iApply (wp_pointeradd with "Hf").
           { simpl. rewrite wasm_int_signed; [exact Hadd|exact Hd]. }
           by instantiate (1 := λ w, ⌜w = immV [_]⌝%I). }
      { by iIntros "[%Htrap _]". }
      iIntros (w) "[-> Hf]". simpl.
      iApply (stack_load_j with "[] [] Hs Hf"); done.
    Qed.

    Lemma stack_load_j_alt p s f E j k sv :
      ⌜k = (length s * 4 - 4 * Z.of_N j)%Z⌝ -∗
      ⌜s !! N.to_nat j = Some sv⌝ -∗
      ⌜(j < N.of_nat (length s))%N⌝ -∗
      isStack p s -∗ ↪[frame] f -∗
      WP [AI_basic (BI_const (nvalue_of_int k)); AI_pointer p;
          AI_basic BI_pointeradd; AI_basic (BI_colload T_i32)] @ E
      {{ w, ⌜w = immV [VAL_int32 sv]⌝ ∗ isStack p s ∗ ↪[frame] f }}.
    Proof.
      iIntros "%Hk %Hsv %Hj Hs Hf". subst k.
      iApply (stack_load_j_pointer_add with "[] [] Hs Hf"); done.
    Qed.

    Lemma stack_store_i32 p c base size old new f E :
      ptr_col p = Some c ->
      wall c base size -∗
      ptr_addr p ↦[i32]{c} old -∗
      ↪[frame] f -∗
      WP [AI_pointer p; AI_const (VAL_int32 new);
          AI_basic (BI_colstore T_i32)] @ E
      {{ w, ⌜w = immV []⌝ ∗ wall c base size ∗
             ptr_addr p ↦[i32]{c} new ∗ ↪[frame] f }}.
    Proof.
      iIntros (Hcol) "Hwall Hold Hf".
      iDestruct (wcs_wblock with "Hold") as "Hblock".
      iApply (wp_wand with "[-]").
      - iApply (wp_colstore NotStuck E
          (λ w, (⌜w = immV []⌝ ∗ wall c base size ∗
            ptr_addr p ↦[i32]{c} new)%I)
          p T_i32 c base size
          (map (λ b, {| tb_value := b; tb_color := Some c;
                     tb_tag := Numeric |}) (serialise_i32 old))
          (VAL_int32 new) f with "[-]").
        + done.
        + exact Hcol.
        + done.
        + remember (serialise_i32 old) as bs.
          clear Heqbs. induction bs as [|b bs IH] => //=.
          by rewrite eqxx IH.
        + done.
        + iSplitR "Hf Hblock Hwall".
          * iNext. iIntros "[Hnew Hwall]". iFrame. done.
          * iFrame.
      - iIntros (w) "[[Hw [Hwall Hnew]] Hf]". iFrame.
    Qed.

    Lemma stack_store_j p s f E j old new p' :
      s !! N.to_nat j = Some old ->
      pointer_arith p (length s * 4 - 4 * Z.of_N j) = Some p' ->
      isStack p s -∗ ↪[frame] f -∗
      WP [AI_pointer p'; AI_const (VAL_int32 new);
          AI_basic (BI_colstore T_i32)] @ E
      {{ w, ⌜w = immV []⌝ ∗
             isStack p (<[N.to_nat j := new]> s) ∗ ↪[frame] f }}.
    Proof.
      iIntros (Hlookup Harith) "Hs Hf".
      have Hj := lookup_lt_Some _ _ _ Hlookup.
      have Haddr : ptr_addr p' =
        (ptr_addr p + N.of_nat (length s) * 4 - 4 * j)%N.
      { rewrite (pointer_arith_addr Harith). lia. }
      iDestruct "Hs" as (c)
        "(%Hcol & %Hfree & %Hlen & Hwall & Hlive & Hbase & Helems & Htail)".
      iDestruct (big_sepL_insert_acc with "Helems") as "[Hold Hclose]";
        first exact Hlookup.
      rewrite N2Nat.id.
      iApply (wp_wand with "[Hwall Hold Hf]").
      - have Hcol' : ptr_col p' = Some c.
        { by rewrite (pointer_arith_col Harith). }
        iApply (stack_store_i32 (ptr_addr p) two16 old new f E Hcol'
          with "Hwall [Hold] Hf").
        by rewrite Haddr.
      - iIntros (w) "(-> & Hwall & Hnew & Hf)".
        iDestruct ("Hclose" $! new with "[Hnew]") as "Helems".
        { iApply (points_to_i32_eq with "Hnew") => //. }
        iSplit; first done. iSplitR "Hf"; last done.
        iExists c. rewrite insert_length.
        iFrame. auto.
    Qed.

  End proofs.

  Lemma positive_add a b : a + b = ssrnat.NatTrec.add a b.
  Proof. by rewrite ssrnat.NatTrec.addE. Qed.

  Lemma nat_of_bin_to_N x : Z.to_N (ssrnat.nat_of_bin x) = x.
  Proof.
    rewrite nat_bin.
    remember (N.to_nat x) as x'.
    assert (N.of_nat x' = x); first by rewrite Heqx' N2Nat.id.
    subst x. rewrite -Z_nat_N. f_equal. by rewrite Nat2Z.id.
  Qed.

  Lemma divide_and_multiply a b :
    (b > 0)%N -> N.divide b a -> (a `div` b * b = a)%N.
  Proof.
    intros ? [c ->]. rewrite N.div_mul => //. lia.
  Qed.

  Lemma div_lt a b c :
    (a < b)%N -> (c > 0)%N -> N.divide c a -> N.divide c b ->
    (a `div` c < b `div` c)%N.
  Proof.
    intros.
    apply divide_and_multiply in H1, H2 => //=.
    rewrite -H1 in H. rewrite -H2 in H.
    apply N.mul_lt_mono_pos_r in H => //=. lia.
  Qed.

  Fixpoint stackAll {A} (s : seq.seq A) (Φ : A -> iPropI Σ) : iPropI Σ :=
    match s with
    | [] => True%I
    | a :: s => (Φ a ∗ stackAll s Φ)%I
    end.

  Fixpoint stackAll2 {A} s1 s2 (Ψ : A -> A -> iPropI Σ) :=
    match s1, s2 with
    | [], [] => True%I
    | a1 :: s1, a2 :: s2 => (Ψ a1 a2 ∗ stackAll2 s1 s2 Ψ)%I
    | _, _ => False%I
    end.

  Lemma stackAll_app {A} (s : seq.seq A) s' Φ :
    ⊢ stackAll (s ++ s') Φ ∗-∗ stackAll s Φ ∗ stackAll s' Φ.
  Proof.
    iSplit.
    - iIntros "H". iInduction s as [|a s] "IH" => /=.
      + iFrame.
      + iDestruct "H" as "[Ha H]".
        iDestruct ("IH" with "H") as "[Hs Hs']". iFrame.
    - iIntros "[Hs Hs']". iInduction s as [|a s] "IH" => /=.
      + iFrame.
      + iDestruct "Hs" as "[Ha Hs]".
        iFrame "Ha". iApply ("IH" with "Hs Hs'").
  Qed.

End Stack.
