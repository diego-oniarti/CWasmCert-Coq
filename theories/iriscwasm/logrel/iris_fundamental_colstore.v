From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list.
From iris.prelude Require Import options.

From CWasm.iriscwasm.language.iris Require Import iris iris_locations.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm.iriscwasm.language Require Import iris_atomicity iris_wp_def.
From CWasm Require Import stdpp_aux datatypes operations properties opsem typing inj_div.
From CWasm.iriscwasm.rules Require Import iris_rules. 
From CWasm.iriscwasm.logrel Require Export iris_logrel iris_fundamental_helpers.
Import uPred.
  
Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ, HPB: PointerBytes, cancelg : cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  
  Lemma lookup_map {A B} (f: A -> B) l k:
    map f l !! k = match l !! k with Some x => Some (f x) | None => None end.
  Proof.
    generalize dependent k.
    induction l => //=; intros.
    destruct k => //=.
  Qed. 
  

  Lemma take_drop_take {A} lo hi lo' (l: list A) :
    lo + hi <= lo' ->
    take hi (drop lo (take lo' l)) = take hi (drop lo l).
  Proof.
    intros H. generalize dependent lo'; generalize dependent hi; generalize dependent lo.
    induction l => //=; intros.
    { rewrite take_nil drop_nil take_nil. done. }
    destruct hi => //=.
    destruct lo' => //=; first lia.
    destruct lo => //=.
    { specialize (IHl 0). rewrite drop_0 in IHl. erewrite <- IHl.
      - rewrite drop_0. rewrite take_take.
        replace (hi `min` lo') with hi; last lia.
        rewrite take_take.
        instantiate (1 := lo').
        replace (hi `min` lo') with hi; last lia.
        done.
      - lia. }
    rewrite IHl; last lia. done.
  Qed.

  Lemma overlap_nat a b a' b':
    a + S b > a' -> a' + S b' > a -> exists x, a <= x /\ x < a + S b /\ a' <= x /\ x < a' + S b'.
  Proof.
    intros H H'.
    induction b.
    { exists a. repeat split; lia. }
    destruct (a + S b =? a') eqn:Ha.
    { apply Nat.eqb_eq in Ha.
      exists a'. repeat split; lia. }
    apply Nat.eqb_neq in Ha.
    assert (a + S b > a') as Ha'.
    { lia. }
    apply IHb in Ha' as (x & ? & ? & ? & ?).
    exists x. repeat split; lia. 
  Qed.

  Lemma overlap a b a' b':
    (b > 0 -> b' > 0 ->
     a + b > a' -> a' + b' > a -> exists x, a <= x /\ x < a + b /\ a' <= x /\ x < a' + b')%N.
  Proof.
    intros Hb Hb' H H'.
    destruct (overlap_nat (N.to_nat a) ((N.to_nat b - 1)) (N.to_nat a') ((N.to_nat b' - 1))) as (x & ? & ? & ? & ?); try lia.
    exists (N.of_nat x). repeat split; lia.
  Qed.

  Lemma lookup_lt_Some_inv {A} i (l: list A):
    i < length l -> exists x, l !! i = Some x.
  Proof.
    generalize dependent i.
    induction l; intros; first by simpl in *; lia.
    destruct i; first by eexists a.
    simpl in H. assert (i < length l) as Hi; first lia.
    apply IHl in Hi as [x Hx].
    exists x. simpl. done.
  Qed. 


  Lemma modulo_divisible a m:
    (a `mod` m = 0 -> (a / m) * m = a)%N.
  Proof.
    unfold N.modulo, N.div.
    specialize (N.div_eucl_spec a m) as H. 
    destruct (N.div_eucl a m) eqn:Hdivmod.
    simpl.
    intros ->.
    lia.
  Qed. 
    

  
  Lemma modulo_trapped a b m :
    (a `mod` m = 0 -> b `mod` m = 0 -> a > b - m -> a < b + m -> a = b)%N.
  Proof.
    intros Ha Hb Hlo Hhi.
    apply modulo_divisible in Ha, Hb => //.
    remember (a `div` m)%N as ka; clear Heqka.
    remember (b `div` m)%N as kb; clear Heqkb.
    remember (N.to_nat a) as a'.
    remember (N.to_nat b) as b'.
    remember (N.to_nat m) as m'.
    remember (N.to_nat ka) as ka'.
    remember (N.to_nat kb) as kb'.
    assert (ka' * m' = a') as Ha'; first lia.
    assert (kb' * m' = b') as Hb'; first lia.
    assert (a' > b' - m') as Hlo'; first lia.
    assert (a' < b' + m') as Hhi'; first lia.
    assert (a' = b'); last lia.
    assert (b' - a' = (kb' - ka') * m') as Hamb.
    { rewrite - Ha' - Hb'. 
      rewrite Nat.mul_sub_distr_r.
      done. }
    remember (kb' - ka') as k; clear Heqk.
    assert (b' - a' < m'); first lia.
    destruct k; last lia. 
    assert (b' <= a'); first lia.
    assert (a' - b' = (ka' - kb') * m') as Hbma.
    { rewrite - Ha' - Hb'. 
      rewrite Nat.mul_sub_distr_r.
      done. }
     remember (ka' - kb') as k; clear Heqk.
     assert (a' - b' < m'); first lia.
     destruct k; last lia.
     lia.
  Qed.

  Lemma modulo_leq a m:
    (a `mod` m = 0 -> a = 0 \/ a >= m)%N.
  Proof.
    intro H; apply modulo_divisible in H.
    remember (a `div` m)%N as k; clear Heqk.
    remember (N.to_nat a) as a'.
    remember (N.to_nat m) as m'.
    remember (N.to_nat k) as k'.
    assert (k' * m' = a') as H'; first lia.
    assert (a' = 0 \/ a' >= m') as [?|?]; [|lia|lia].
    destruct k'; first by left.
    right; lia.
  Qed. 


  Lemma lt_plus : forall a b c, c <= a -> a < b + c -> a - c < b.
  Proof. lia. Qed.
  Lemma lt_minus : forall a b c, a < b - c -> a + c < b.
  Proof. lia. Qed.
  
  Lemma arith: forall a b c d, (d <= a -> a < b - c + d -> b > c + a - d)%N.
  Proof. lia. Qed. 

  Definition replace_slice {A} (off : nat) (new old : list A) : list A :=
    take off old ++ new ++ drop (off + length new) old.

  Lemma replace_slice_length {A} off (new old : list A) :
    off + length new <= length old ->
    length (replace_slice off new old) = length old.
  Proof.
    move=> Hbound. rewrite /replace_slice !app_length drop_length.
    rewrite take_length_le; lia.
  Qed.

  Lemma replace_slice_before {A} off j n (new old : list A) :
    off + length new <= length old ->
    j + n <= off ->
    take n (drop j (replace_slice off new old)) = take n (drop j old).
  Proof.
    move=> Hbound Hbefore. rewrite /replace_slice.
    rewrite drop_app_le; last by rewrite take_length_le; lia.
    rewrite take_app_le; last by rewrite drop_length take_length_le; lia.
    apply take_drop_take. lia.
  Qed.

  Lemma replace_slice_after {A} off j n (new old : list A) :
    off + length new <= j ->
    j + n <= length old ->
    take n (drop j (replace_slice off new old)) = take n (drop j old).
  Proof.
    move=> Hafter Hbound. rewrite /replace_slice catA.
    rewrite drop_app_ge.
    2:{ rewrite app_length take_length_le; lia. }
    rewrite drop_drop app_length take_length_le; last lia.
    replace (off + length new + (j - (off + length new))) with j by lia.
    done.
  Qed.

  Lemma replace_slice_at {A} off (new old : list A) :
    off + length new <= length old ->
    take (length new) (drop off (replace_slice off new old)) = new.
  Proof.
    move=> Hbound. rewrite /replace_slice.
    rewrite drop_app_ge; last by rewrite take_length_le; lia.
    rewrite take_length_le; last lia. rewrite Nat.sub_diag drop_0.
    rewrite take_app_le; last lia.
    apply take_all_alt. lia.
  Qed.

  Lemma all_lookup_true {A} (f : A -> bool) (l : list A) i x :
    all f l -> l !! i = Some x -> f x.
  Proof.
    move: i. induction l as [|y l IH] => i //=.
    move=> /andP [Hy Hl]. destruct i as [|i].
    - move=> Hlook. inversion Hlook; subst. exact Hy.
    - apply IH. exact Hl.
  Qed.

  Lemma replace_slice_lookup_middle {A} off (new old : list A) k x :
    off + length new <= length old ->
    new !! k = Some x ->
    replace_slice off new old !! (off + k) = Some x.
  Proof.
    move=> Hbound Hlookup. rewrite /replace_slice lookup_app.
    rewrite lookup_take_ge; last lia.
    rewrite lookup_app take_length_le; last lia.
    replace (off + k - off) with (k); last lia.
    by rewrite Hlookup.
  Qed.

  Lemma slice_lookup {A} (l : list A) j n k x :
    k < n -> l !! (j + k) = Some x ->
    take n (drop j l) !! k = Some x.
  Proof.
    move=> Hk Hlookup. rewrite lookup_take; last exact Hk.
    by rewrite lookup_drop.
  Qed.

  Lemma pointer_slots_store_numeric
      (I : leibnizO pointer -n> iPropO Σ) base tbs off col bs :
    off + length bs <= length tbs ->
    length bs > 0 ->
    pointer_slots I base tbs -∗
    pointer_slots I base
      (replace_slice off
        (map (fun b => {| tb_value := b; tb_color := Some col;
                          tb_tag := Numeric |}) bs) tbs).
  Proof.
    move=> Hbound Hbspos. iIntros "Hslots".
    rewrite /pointer_slots. iIntros (j) "%Hrange %Hpointer".
    destruct Hrange as [Halign Hjbound].
    have Hnewlen :
        length (map (fun b => {| tb_value := b; tb_color := Some col;
                                tb_tag := Numeric |}) bs) = length bs
      by rewrite map_length.
    have Hreplen : length
        (replace_slice off
          (map (fun b => {| tb_value := b; tb_color := Some col;
                            tb_tag := Numeric |}) bs) tbs) = length tbs.
    { apply replace_slice_length. by rewrite Hnewlen. }
    destruct (decide (off + length bs <= j)) as [Hafter|Hafter].
    - have Hjold : j + N.to_nat pointer_size <= length tbs by
        rewrite -Hreplen; exact Hjbound.
      have Heq := replace_slice_after off j (N.to_nat pointer_size)
        (map (fun b => {| tb_value := b; tb_color := Some col;
                         tb_tag := Numeric |}) bs) tbs.
      rewrite Heq in Hpointer *; [|by rewrite map_length|exact Hjold].
      iApply ("Hslots" $! j).
      + iPureIntro. split; first exact Halign. rewrite Hreplen in Hjbound.
        exact Hjbound.
      + iPureIntro. exact Hpointer.
    - destruct (decide (j + N.to_nat pointer_size <= off))
        as [Hbefore|Hbefore].
      + have Heq := replace_slice_before off j (N.to_nat pointer_size)
          (map (fun b => {| tb_value := b; tb_color := Some col;
                           tb_tag := Numeric |}) bs) tbs.
        rewrite Heq in Hpointer *; [|by rewrite map_length|exact Hbefore].
        iApply ("Hslots" $! j).
        * iPureIntro. split; first exact Halign. rewrite Hreplen in Hjbound.
          exact Hjbound.
        * iPureIntro. exact Hpointer.
      + iExFalso. iPureIntro.
        have Hpspos := @size_is_not_zero HPB.
        rewrite nat_bin in Hpspos. move/ssrnat.ltP in Hpspos.
        destruct (overlap_nat j (N.to_nat pointer_size - 1)
          off (length bs - 1)) as (y & Hyj & Hyj' & Hyo & Hyo'); try lia.
        set (k := y - off).
        have Hk : k < length bs by rewrite /k; lia.
        destruct (lookup_lt_is_Some_2 bs k Hk) as [b Hb].
        have Hmapped :
            map (fun b => {| tb_value := b; tb_color := Some col;
                             tb_tag := Numeric |}) bs !! k =
              Some {| tb_value := b; tb_color := Some col; tb_tag := Numeric |}.
        { by rewrite list_lookup_fmap Hb. }
        have Habsolute := replace_slice_lookup_middle off
          (map (fun b => {| tb_value := b; tb_color := Some col;
                            tb_tag := Numeric |}) bs) tbs k _
          ltac:(by rewrite map_length) Hmapped.
        have Hyoff : off + k = y by rewrite /k; lia.
        rewrite Hyoff in Habsolute.
        set (q := y - j).
        have Hq : q < N.to_nat pointer_size by rewrite /q; lia.
        have Hjq : j + q = y by rewrite /q; lia.
        have Hquery := slice_lookup _ j (N.to_nat pointer_size) q _
          Hq ltac:(by rewrite Hjq).
        have Htag := all_lookup_true
          (fun tb => tb_tag tb == Pointer) _ q _ Hpointer Hquery.
        done.
  Qed.

  Lemma replace_slice_colors off c (new old : list tagged_byte) :
    all (fun tb => tb_color tb == Some c) old ->
    all (fun tb => tb_color tb == Some c) new ->
    all (fun tb => tb_color tb == Some c) (replace_slice off new old).
  Proof.
    move=> Hold Hnew.
    have Htake : all (fun tb => tb_color tb == Some c) (take off old).
    { rewrite -(cat_take_drop off old) all_cat in Hold.
      move/andP: Hold => [H _]. by rewrite take_seq_take. }
    have Hdrop : all (fun tb => tb_color tb == Some c)
        (drop (off + length new) old).
    { rewrite -(cat_take_drop (off + length new) old) all_cat in Hold.
      move/andP: Hold => [_ H]. by rewrite drop_seq_drop. }
    by rewrite /replace_slice !all_cat Htake Hnew Hdrop.
  Qed.

  Lemma pointer_slots_store_pointer
      (I : leibnizO pointer -n> iPropO Σ) base tbs off col p :
    off + N.to_nat pointer_size <= length tbs ->
    (N.modulo (base + N.of_nat off) pointer_size = 0)%N ->
    I p -∗ pointer_slots I base tbs -∗
    pointer_slots I base
      (replace_slice off
        (map (fun b => {| tb_value := b; tb_color := Some col;
                          tb_tag := Pointer |}) (serialise_pointer p)) tbs).
  Proof.
    move=> Hbound Halign. iIntros "Hp Hslots".
    rewrite /pointer_slots. iIntros (j) "%Hrange %Hpointer".
    destruct Hrange as [Hjalign Hjbound].
    have Hserlen : length (serialise_pointer p) = N.to_nat pointer_size.
    { destruct HPB. simpl. by rewrite length_serialise nat_bin. }
    have Hnewlen : length
        (map (fun b => {| tb_value := b; tb_color := Some col;
                         tb_tag := Pointer |}) (serialise_pointer p)) =
        N.to_nat pointer_size by rewrite map_length Hserlen.
    have Hreplen : length
        (replace_slice off
          (map (fun b => {| tb_value := b; tb_color := Some col;
                           tb_tag := Pointer |}) (serialise_pointer p)) tbs) =
        length tbs.
    { apply replace_slice_length. by rewrite Hnewlen. }
    destruct (decide (off + N.to_nat pointer_size <= j)) as [Hafter|Hafter].
    - have Hjold : j + N.to_nat pointer_size <= length tbs by
        rewrite -Hreplen; exact Hjbound.
      have Heq := replace_slice_after off j (N.to_nat pointer_size)
        (map (fun b => {| tb_value := b; tb_color := Some col;
                         tb_tag := Pointer |}) (serialise_pointer p)) tbs.
      rewrite Heq in Hpointer *; [|by rewrite Hnewlen|exact Hjold].
      iApply ("Hslots" $! j); iPureIntro; done.
    - destruct (decide (j + N.to_nat pointer_size <= off))
        as [Hbefore|Hbefore].
      + have Heq := replace_slice_before off j (N.to_nat pointer_size)
          (map (fun b => {| tb_value := b; tb_color := Some col;
                           tb_tag := Pointer |}) (serialise_pointer p)) tbs.
        rewrite Heq in Hpointer *; [|by rewrite Hnewlen|exact Hbefore].
        iApply ("Hslots" $! j).
        * iPureIntro. split; first exact Hjalign.
          rewrite Hreplen in Hjbound. exact Hjbound.
        * iPureIntro. exact Hpointer.
      + have Hpspos := @size_is_not_zero HPB.
        rewrite nat_bin in Hpspos. move/ssrnat.ltP in Hpspos.
        have Hjlt : j < off + N.to_nat pointer_size by lia.
        have Hofflt : off < j + N.to_nat pointer_size by lia.
        have HsizeN : N.of_nat (N.to_nat pointer_size) = pointer_size
          by apply N2Nat.id.
        have HjltN : (N.of_nat j < N.of_nat off + pointer_size)%N by lia.
        have HoffltN : (N.of_nat off < N.of_nat j + pointer_size)%N by lia.
        have Haddr : (base + N.of_nat j = base + N.of_nat off)%N.
        { destruct (N.eq_dec (base + N.of_nat j)%N 0%N) as [Hz|Hz].
          - have Hjzero := modulo_leq (base + N.of_nat j)%N pointer_size Hjalign.
            have Hoffzero := modulo_leq (base + N.of_nat off)%N pointer_size Halign.
            lia.
          - apply modulo_trapped with (m := pointer_size); try done; lia. }
        have Hjo : j = off by lia.
        subst j.
        rewrite -Hnewlen.
        rewrite replace_slice_at; last by rewrite Hnewlen.
        rewrite map_map /= map_id.
        destruct HPB. simpl. by rewrite pointer_of_serialise.
  Qed.

    
    
    
    

    

  (* ----------------------------------------- COLSTORE ---------------------------------------- *)

  Lemma typing_colstore_numeric C t :
    t <> T_pointer ->
    ⊢ semantic_typing C (to_e_list [BI_colstore t])
        (Tf [T_pointer; t] []).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Ht i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]"
      (f vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ ↪[frame] f)%I
        with "[Hf]").
      { iApply (wp_trap with "[] [$]"); auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|wp ws]; [done|
      destruct ws as [|w ws]; [done|destruct ws; [|done]]].
    iSimpl in "Hv". iDestruct "Hv" as "(Hvp & Hvw & _)".
    iDestruct (interp_value_agree with "Hvw") as %Hagree.
    iDestruct "Hvp" as (p ->) "Hp".
    iEval (rewrite pointer_interp_unfold /pointer_interp_pre) in "Hp".
    iDestruct "Hp" as "[%Hnull | Hp]".
    { iApply (wp_wand with "[Hf]").
      - iApply (wp_colstore_fail_null with "[$Hf]").
        + by apply /eqP.
        + by instantiate (1 := λ x, ⌜x = trapV⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists f. iFrame. }
    iDestruct "Hp" as (c r) "(%Hcol & #Hreg & #Hinv & %Hfraction)".
    iDestruct (interp_allocator_lookup_acc with "Hreg Hall") as
      "[Hentry Hclose]".
    iDestruct "Hentry" as "[_ [[Hlive Htok] | #Hdead]]".
    2:{ iApply (wp_wand with "[Hf Hdead]").
        - iApply (wp_colstore_fail_dead NotStuck ⊤
            (λ x, (⌜x = trapV⌝ ∗ pointer_world_entry c r)%I)
            p t w c f with "[$Hf $Hdead]"); first exact Hcol.
          iNext. iIntros "#Hdead'". iSplit; first done.
          rewrite /pointer_world_entry. iFrame "Hinv".
        - iIntros (v) "[[-> Hentry] Hf]".
          iDestruct ("Hclose" with "Hentry") as "Hall".
          iSplitR; first by do 2 iLeft.
          iExists f. iFrame. }
    destruct (decide ((preg_base r <= ptr_addr p /\
      ptr_addr p + N.of_nat (t_length t) <=
        preg_base r + preg_size r)%N)) as [Hbounds|Hbounds].
    2:{ iApply (wp_wand _ _ _
          (λ v, ((⌜v = trapV⌝ ∗ cinv_own (preg_name r) (preg_fraction r)) ∗
                   ↪[frame] f)%I)
          with "[Hf Htok]").
        { iApply (wp_atomic _ _ (⊤ ∖ ↑(pointer_inv_namespace c))).
          { destruct w; solve_atomic. }
          iMod (cinv_acc with "Hinv Htok") as "(Hbody & Hwon & Hcls)";
            first solve_ndisj.
          iModIntro.
          iDestruct "Hbody" as (tbs)
            "(>%Htbslen & >%Hcolors & >Hwall & >Hblock & Hslots)".
          iAssert (▷ (wall c (preg_base r) (preg_size r) -∗
            wblock (preg_base r) tbs -∗
            (⌜trapV = trapV⌝ ∗
             |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
               cinv_own (preg_name r) (preg_fraction r))))%I
            with "[Hcls Hwon Hslots]" as "Hpost".
          { iNext. iIntros "Hwall Hblock". iSplit; first done.
            iMod ("Hcls" with "[Hwall Hblock Hslots]").
            { iNext. iExists tbs. iFrame. done. }
            iModIntro. iExact "Hwon". }
          iApply (wp_wand _ _ _
            (λ v, ((⌜v = trapV⌝ ∗
              |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
                cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
            with "[Hf Hwall Hblock Hpost]").
          { iApply wp_colstore_fail_bounds;
              [exact Hcol | exact Htbslen | exact Hcolors |
               destruct t => //=; lia | exact Hbounds |].
            iFrame. }
          iIntros (v) "[[-> >Hwon] Hf]".
          iFrame. iModIntro. done. }
        iIntros (v) "[[-> Hwon] Hf]".
        iAssert (pointer_world_entry c r) with "[Hlive Hwon]" as "Hentry".
        { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
          iLeft. iFrame. }
        iDestruct ("Hclose" with "Hentry") as "Hall".
        iSplitR "Hf Hfv Hall"; first by do 2 iLeft.
        iExists _. iFrame. }
    iApply (wp_wand _ _ _
      (λ x, ((⌜x = immV []⌝ ∗ cinv_own (preg_name r) (preg_fraction r)) ∗
               ↪[frame] f)%I)
      with "[Hf Htok]").
{ iApply (wp_atomic _ _ (⊤ ∖ ↑(pointer_inv_namespace c))).
          { destruct w; solve_atomic. }
          iMod (cinv_acc with "Hinv Htok") as "(Hbody & Hwon & Hcls)";
            first solve_ndisj.
          iModIntro.
          iDestruct "Hbody" as (tbs)
            "(>%Htbslen & >%Hcolors & >Hwall & >Hblock & Hslots)".
          have Hlen_nat : length tbs = N.to_nat (preg_size r) by lia.
          iDestruct (wcs_select (N.to_nat (preg_base r))
            (N.to_nat (preg_size r)) (N.to_nat (ptr_addr p))
            (t_length t) tbs with "[Hblock]")
        as "(%Hslice_len & Hslice & Hreconstitute)";
        try rewrite N2Nat.id; try done; try lia.
      remember (take (t_length t)
        (drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs))
        as slice eqn:Hslice.
      have Hslice_colors : all (fun tb => tb_color tb == Some c) slice.
      { have H := Hcolors.
        rewrite -(reconstitute (N.to_nat (preg_base r))
          (N.to_nat (ptr_addr p)) (t_length t) tbs) !all_cat in H.
        move/andP: H => [_ /andP [H _]]. by rewrite -Hslice in H. }
      set (off := N.to_nat (ptr_addr p) - N.to_nat (preg_base r)).
      set (new := map
        (fun b => {| tb_value := b; tb_color := Some c; tb_tag := Numeric |})
        (bits w)).
      have Hbitslen : length (bits w) = t_length t by
        apply length_bits.
      have Hnewlen : length new = t_length t by
        rewrite /new map_length Hbitslen.
      have Hoffbound : off + length new <= length tbs.
      { rewrite Hnewlen /off Hlen_nat. lia. }
      have Hnewcolors :
          all (fun tb => tb_color tb == Some c) new.
      { rewrite /new. induction (bits w) as [|b bs IH] => //=.
        apply /andP. split.
        { apply /eqP. reflexivity. }
        rewrite all_map.
        apply/allP => x _.
        simpl.
        by [].
      }
      iAssert (wblock (ptr_addr p) slice)%I with "[Hslice]" as "Hslice".
      { rewrite /wblock /cmem_block_at_pos. iExact "Hslice". }
      iAssert (▷ (wcs (ptr_addr p) c Numeric (bits w) ∗
        wall c (preg_base r) (preg_size r) -∗
        (⌜immV [] = immV []⌝ ∗
         |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
           cinv_own (preg_name r) (preg_fraction r))))%I
        with "[Hcls Hwon Hslots Hreconstitute]" as "Hpost".
      { iNext. iIntros "[Hslice Hwall]". iSplit; first done.
        iEval (rewrite wcs_wblock /new) in "Hslice".
        iDestruct ("Hreconstitute" $! new Hnewlen with "Hslice")
          as "Hblock".
        iAssert (wblock (preg_base r) (replace_slice off new tbs))%I
          with "[Hblock]" as "Hblock'".
        { rewrite /replace_slice /off /wblock /cmem_block_at_pos N2Nat.id.
          rewrite <- Hnewlen.
          iExact "Hblock". }
        iAssert (pointer_slots pointer_interp (preg_base r)
          (replace_slice off new tbs)) with "[Hslots]" as "Hslots'".
        { iApply pointer_slots_store_numeric ; [rewrite Hbitslen -Hnewlen; exact Hoffbound| |iExact "Hslots"].
          rewrite Hbitslen. rewrite -Hnewlen. destruct t => //=; rewrite Hnewlen; lias.
        }
        iMod ("Hcls" with "[Hwall Hblock' Hslots']").
        { iNext. iExists (replace_slice off new tbs).
          iSplit.
          - rewrite replace_slice_length.
            + iPureIntro. lias.
            + exact Hoffbound.
          - iSplit.
            + iPureIntro. apply replace_slice_colors; done.
            + iFrame. }
        iModIntro. iExact "Hwon". }
      iApply (wp_wand _ _ _
        (λ x, ((⌜x = immV []⌝ ∗
          |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
            cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
        with "[Hf Hslice Hwall Hpost]").
      { iApply wp_colstore;
          [exact Ht | exact Hcol | exact Hslice_len |
           exact Hslice_colors | exact Hagree |].
        iFrame. }
      iIntros (x) "[[-> >Hwon] Hf]".
      iModIntro. iFrame. iPureIntro. done. }
    iIntros (x) "[[-> Hwon] Hf]".
    iAssert (pointer_world_entry c r) with "[Hlive Hwon]" as "Hentry".
    { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
      iLeft. iFrame. }
    iDestruct ("Hclose" with "Hentry") as "Hall".
    iSplitR "Hf Hfv Hall".
    - iLeft. iRight. iExists []. iSplit; done.
    - iExists _. iFrame.
  Qed.

  Lemma typing_colstore_pointer C:
    ⊢ semantic_typing C (to_e_list [BI_colstore T_pointer])
        (Tf [T_pointer; T_pointer] []).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]"
      (f vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗ ↪[frame] f)%I
        with "[Hf]").
      { iApply (wp_trap with "[] [$]"); auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|wp ws]; [done|
      destruct ws as [|w ws]; [done|destruct ws; [|done]]].
    iSimpl in "Hv". iDestruct "Hv" as "(Hvp & Hvw & _)".
    iDestruct "Hvw" as (p' Hw') "Hp'".
    have Hagree : types_agree T_pointer (VAL_pointer p').
    { unfold types_agree, typeof. by apply /eqP. }
    have Hagree_w : types_agree T_pointer w.
    { rewrite Hw'. exact Hagree. }
    iDestruct "Hvp" as (p ->) "Hp".
    iEval (rewrite pointer_interp_unfold /pointer_interp_pre) in "Hp".
    iDestruct "Hp" as "[%Hnull | Hp]".
    { iApply (wp_wand with "[Hf]").
      - iApply (wp_colstore_fail_null with "[$Hf]").
        + by apply /eqP.
        + by instantiate (1 := λ x, ⌜x = trapV⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists f. iFrame. }
    iDestruct "Hp" as (c r) "(%Hcol & #Hreg & #Hinv & %Hfraction)".
    iDestruct (interp_allocator_lookup_acc with "Hreg Hall") as
      "[Hentry Hclose]".
    iDestruct "Hentry" as "[_ [[Hlive Htok] | #Hdead]]".
    2:{ iApply (wp_wand with "[Hf Hdead]").
        - iApply (wp_colstore_fail_dead NotStuck ⊤
            (λ x, (⌜x = trapV⌝ ∗ pointer_world_entry c r)%I)
            p T_pointer w c f with "[$Hf $Hdead]"); first exact Hcol.
          iNext. iIntros "#Hdead'". iSplit; first done.
          rewrite /pointer_world_entry. iFrame "Hinv".
        - iIntros (v) "[[-> Hentry] Hf]".
          iDestruct ("Hclose" with "Hentry") as "Hall".
          iSplitR; first by do 2 iLeft.
          iExists f. iFrame. }
    destruct (decide ((preg_base r <= ptr_addr p /\
      ptr_addr p + N.of_nat (t_length T_pointer) <=
        preg_base r + preg_size r)%N)) as [Hbounds|Hbounds].
    2:{ iApply (wp_wand _ _ _
          (λ v, ((⌜v = trapV⌝ ∗ cinv_own (preg_name r) (preg_fraction r)) ∗
                   ↪[frame] f)%I)
          with "[Hf Htok]").
        { iApply (wp_atomic _ _ (⊤ ∖ ↑(pointer_inv_namespace c))).
          { destruct w; solve_atomic. }
          iMod (cinv_acc with "Hinv Htok") as "(Hbody & Hwon & Hcls)";
            first solve_ndisj.
          iModIntro.
          iDestruct "Hbody" as (tbs)
            "(>%Htbslen & >%Hcolors & >Hwall & >Hblock & Hslots)".
          iAssert (▷ (wall c (preg_base r) (preg_size r) -∗
            wblock (preg_base r) tbs -∗
            (⌜trapV = trapV⌝ ∗
             |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
               cinv_own (preg_name r) (preg_fraction r))))%I
            with "[Hcls Hwon Hslots]" as "Hpost".
          { iNext. iIntros "Hwall Hblock". iSplit; first done.
            iMod ("Hcls" with "[Hwall Hblock Hslots]").
            { iNext. iExists tbs. iFrame. done. }
            iModIntro. iExact "Hwon". }
          iApply (wp_wand _ _ _
            (λ v, ((⌜v = trapV⌝ ∗
              |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
                cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
            with "[Hf Hwall Hblock Hpost]").
            { iApply wp_colstore_fail_bounds;
              [exact Hcol | exact Htbslen | exact Hcolors |
               have Hpos := @size_is_not_zero HPB;
               rewrite nat_bin in Hpos; move/ssrnat.ltP in Hpos;
               unfold t_length; rewrite nat_bin; exact Hpos |
               exact Hbounds |].
            iFrame "Hf Hwall Hblock Hpost". }
          iIntros (v) "[[-> >Hwon] Hf]".
          iFrame. iModIntro. done. }
        iIntros (v) "[[-> Hwon] Hf]".
        iAssert (pointer_world_entry c r) with "[Hlive Hwon]" as "Hentry".
        { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
          iLeft. iFrame. }
        iDestruct ("Hclose" with "Hentry") as "Hall".
        iSplitR "Hf Hfv Hall"; first by do 2 iLeft.
        iExists _. iFrame. }
    destruct (N.eq_dec
      (N.modulo (ptr_addr p) (N.of_nat (t_length T_pointer)))
      (N.of_nat 0)) as [Halign|Halign];
      fold (isAlign p) in Halign.
    2:{ iApply (wp_wand with "[Hf]").
        - iApply (wp_colstore_fail_align with "[$Hf]"); first exact Halign.
          by instantiate (1 := λ x, ⌜x = trapV⌝%I).
        - iIntros (v) "[-> Hf]".
          iAssert (pointer_world_entry c r) with "[Hlive Htok]" as "Hentry".
          { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
            iLeft. iFrame. }
          iDestruct ("Hclose" with "Hentry") as "Hall".
          iSplitR "Hf Hfv Hall"; first by do 2 iLeft.
          iExists _. iFrame. }
    iApply (wp_wand _ _ _
      (λ x, ((⌜x = immV []⌝ ∗ cinv_own (preg_name r) (preg_fraction r)) ∗
               ↪[frame] f)%I)
      with "[Hf Htok]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(pointer_inv_namespace c))).
      { destruct w; solve_atomic. }
      iMod (cinv_acc with "Hinv Htok") as "(Hbody & Hwon & Hcls)";
        first solve_ndisj.
      iModIntro.
      iDestruct "Hbody" as (tbs)
        "(>%Htbslen & >%Hcolors & >Hwall & >Hblock & Hslots)".
      have Hlen_nat : length tbs = N.to_nat (preg_size r) by lia.
      iDestruct (wcs_select (N.to_nat (preg_base r))
        (N.to_nat (preg_size r)) (N.to_nat (ptr_addr p))
        (t_length T_pointer) tbs with "[Hblock]")
        as "(%Hslice_len & Hslice & Hreconstitute)";
        try rewrite N2Nat.id; try done; try lia.
      remember (take (t_length T_pointer)
        (drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs))
        as slice eqn:Hslice.
      have Hslice_colors : all (fun tb => tb_color tb == Some c) slice.
      { have H := Hcolors.
        rewrite -(reconstitute (N.to_nat (preg_base r))
          (N.to_nat (ptr_addr p)) (t_length T_pointer) tbs) !all_cat in H.
        move/andP: H => [_ /andP [H _]]. by rewrite -Hslice in H. }
      set (off := N.to_nat (ptr_addr p) - N.to_nat (preg_base r)).
      set (new := map
        (fun b => {| tb_value := b; tb_color := Some c; tb_tag := Pointer |})
        (bits w)).
      have Hbitslen : length (bits w) = t_length T_pointer.
      { apply length_bits. exact Hagree_w. }
      have Hnewlen : length new = t_length T_pointer by
        rewrite /new map_length Hbitslen.
      have Hoffbound : off + length new <= length tbs.
      { rewrite Hnewlen /off Hlen_nat. lia. }
      have Hnewcolors :
          all (fun tb => tb_color tb == Some c) new.
      { rewrite /new. induction (bits w) as [|b bs IH] => //=.
        apply /andP. split.
        { apply /eqP. reflexivity. }
        rewrite all_map.
        apply/allP => x _.
        simpl.
        by [].
      }
      iAssert (wblock (ptr_addr p) slice)%I with "[Hslice]" as "Hslice".
      { rewrite /wblock /cmem_block_at_pos. iExact "Hslice". }
      iAssert (▷ (wcs (ptr_addr p) c Pointer (bits w) ∗
        wall c (preg_base r) (preg_size r) -∗
        (⌜immV [] = immV []⌝ ∗
         |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
           cinv_own (preg_name r) (preg_fraction r))))%I
        with "[Hcls Hwon Hslots Hreconstitute]" as "Hpost".
      { iNext. iIntros "[Hslice Hwall]". iSplit; first done.
        iEval (rewrite wcs_wblock /new) in "Hslice".
        iDestruct ("Hreconstitute" $! new Hnewlen with "Hslice")
          as "Hblock".
        iAssert (wblock (preg_base r) (replace_slice off new tbs))%I
          with "[Hblock]" as "Hblock'".
        { rewrite /replace_slice /off /wblock /cmem_block_at_pos N2Nat.id.
          rewrite <- Hnewlen.
          iExact "Hblock". }
        iAssert (pointer_slots pointer_interp (preg_base r)
          (replace_slice off new tbs)) with "[Hslots]" as "Hslots'".
        { rewrite /new Hw' /=.
          iApply (pointer_slots_store_pointer pointer_interp
            (preg_base r) tbs off c p').
          - have Hnewps : length new = N.to_nat pointer_size.
            { rewrite Hnewlen. unfold t_length. by rewrite nat_bin. }
            rewrite -Hnewps. exact Hoffbound.
          - unfold isAlign in Halign. unfold t_length in Halign.
            rewrite nat_bin N2Nat.id in Halign.
            replace (preg_base r + N.of_nat off)%N with (ptr_addr p).
            + exact Halign.
            + rewrite /off Nat2N.inj_sub; rewrite ?N2Nat.id; lia.
          - iExact "Hp'".
          - iExact "Hslots". }
        iMod ("Hcls" with "[Hwall Hblock' Hslots']").
        { iNext. iExists (replace_slice off new tbs).
          iSplit.
          - rewrite replace_slice_length.
            + iPureIntro. lias.
            + exact Hoffbound.
          - iSplit.
            + iPureIntro. apply replace_slice_colors; done.
            + iFrame. }
        iModIntro. iExact "Hwon". }
      iApply (wp_wand _ _ _
        (λ x, ((⌜x = immV []⌝ ∗
          |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
            cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
        with "[Hf Hslice Hwall Hpost]").
      { iApply wp_colstore_ptr.
        + exact Halign.
        + exact Hcol.
        + exact Hslice_len.
        + exact Hslice_colors.
        + exact Hagree_w.
        + iFrame. }
      iIntros (x) "[[-> >Hwon] Hf]".
      iModIntro. iFrame. iPureIntro. done. }
    iIntros (x) "[[-> Hwon] Hf]".
    iAssert (pointer_world_entry c r) with "[Hlive Hwon]" as "Hentry".
    { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
      iLeft. iFrame. }
    iDestruct ("Hclose" with "Hentry") as "Hall".
    iSplitR "Hf Hfv Hall".
    - iLeft. iRight. iExists []. iSplit; done.
    - iExists _. iFrame.
  Qed.

  Lemma typing_colstore C t :
    ⊢ semantic_typing C (to_e_list [BI_colstore t]) (Tf [T_pointer; t] []).
  Proof.
    destruct t; [.. | apply typing_colstore_pointer].
    all: apply typing_colstore_numeric; discriminate.
  Qed.
End fundamental.
