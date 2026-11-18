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
From CWasm Require Import stdpp_aux datatypes operations properties opsem typing.
From CWasm.iriscwasm.rules Require Import iris_rules. 
From CWasm.iriscwasm.logrel Require Export iris_logrel iris_fundamental_helpers.
Import uPred.
  
Section fundamental.


  Context `{!wasmG Σ, !logrel_na_invs Σ, HPB: PointerBytes, cancelg : cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".
  
  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)


 
    Lemma tagged_bytes_map c tag (tbs : list tagged_byte) :
      all (fun tb => tb_color tb == Some c) tbs ->
      all (fun tb => tb_tag tb == tag) tbs ->
      tbs = map (fun b => {| tb_value := b; tb_color := Some c;
                             tb_tag := tag |}) (map tb_value tbs).
    Proof.
      induction tbs as [|[b col tag'] tbs IH] => //=.
      move=> /andP [/eqP Hcol Hcols] /andP [/eqP Htag Htags].
      subst col tag'. f_equal. by apply IH.
    Qed.

  
    (* ----------------------------------------- COLLOAD ---------------------------------------- *)

    
    Lemma typing_colload_numeric C t :
      t <> T_pointer ->
    ⊢ semantic_typing C (to_e_list [BI_colload t]) (Tf [T_pointer] [t]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (Ht i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]" (f vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs, ⌜vs = trapV⌝ ∗  ↪[frame]f)%I with "[Hf]").
      { iApply (wp_trap with "[] [$]");auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws];[done|destruct ws;[|done]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    iDestruct "Hv" as (p ->) "Hp".
    iEval (rewrite pointer_interp_unfold /pointer_interp_pre) in "Hp".
    iDestruct "Hp" as "[%Hnull | Hp]".
    { iApply (wp_wand with "[Hf]").
      - iApply (wp_colload_fail_null with "[$Hf]").
        + by apply /eqP.
        + by instantiate (1 := λ x, ⌜ x = trapV ⌝%I).
      - iIntros (v) "[-> Hf]".
        iSplitR; first by do 2 iLeft.
        iExists f. iFrame. }
    iDestruct "Hp" as (c r) "(%Hcol & #Hreg & #Hinv & %Hfraction)".
    iDestruct (interp_allocator_lookup_acc with "Hreg Hall") as
      "[Hentry Hclose]".
    iDestruct "Hentry" as "[_ [[Hlive Htok] | #Hdead]]".
    2:{ iApply (wp_wand with "[Hf Hdead]").
        - iApply (wp_colload_fail_dead NotStuck ⊤
            (λ x, (⌜x = trapV⌝ ∗ pointer_world_entry c r)%I)
            p t c f with "[$Hf $Hdead]"); first exact Hcol.
          iNext. iIntros "#Hdead'". iSplit; first done.
            iFrame "Hinv".
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
        { iApply wp_colload_fail_bounds;
            [exact Hcol | exact Htbslen | exact Hcolors |
             destruct t => //=; lia | exact Hbounds |].
          iFrame "Hf Hwall Hblock Hpost". }
        iIntros (v) "[[-> >Hwon] Hf]". iFrame. iModIntro. done. }
        iIntros (v) "[[-> Hwon] Hf]".
        iAssert (pointer_world_entry c r) with "[Hlive Hwon]" as "Hentry".
        { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
          iLeft. iFrame. }
        iDestruct ("Hclose" with "Hentry") as "Hall".
        iSplitR "Hf Hfv Hall"; first by do 2 iLeft.
        iExists _. iFrame. }
    
    iApply (wp_wand _ _ _
      (λ x, (((⌜x = trapV⌝ ∨
                    ∃ v, ⌜x = immV [v]⌝ ∗ interp_value t v) ∗
                 cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
      with "[Hf Htok]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(pointer_inv_namespace c))).
      iMod (cinv_acc with "Hinv Htok") as "(Hbody & Hwon & Hcls)";
        first solve_ndisj.
      iModIntro.
      iDestruct "Hbody" as (tbs)
        "(>%Htbslen & >%Hcolors & >Hwall & >Hblock & Hslots)".
      iDestruct "Hslots" as "#Hslots".
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
      have Hfull :
          take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
          slice ++
          drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
            t_length t) tbs = tbs.
      { rewrite Hslice. apply reconstitute. }
      have Htagkind :
          (match t with T_pointer => Pointer | _ => Numeric end) = Numeric.
      { by destruct t. }
      have Htpos : t_length t > 0.
      { destruct t; simpl; try lia. exfalso. by apply Ht. }
      have Hslice_pos : length slice > 0 by lia.
      destruct (all (fun tb => tb_tag tb == Numeric) slice) eqn:Htags.
      2:{ have Hbad : ~ all (fun tb =>
              (tb_color tb == Some c) &&
              (tb_tag tb == match t with T_pointer => Pointer | _ => Numeric end))
              slice.
          { rewrite Htagkind.
            move=> Hboth. have Htags' : all (fun tb => tb_tag tb == Numeric) slice.
            { clear -Hboth. induction slice as [|tb slice IH] => //=.
              move/andP: Hboth => [/andP [_ Htag] Htail].
              apply/andP. split; first exact Htag. by apply IH. }
            by rewrite Htags in Htags'. }
          iAssert (▷ (wblock (ptr_addr p) slice -∗
            (⌜trapV = trapV⌝ ∗
             |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
               cinv_own (preg_name r) (preg_fraction r))))%I
            with "[Hcls Hwon Hslots Hreconstitute Hwall]" as "Hpost".
          { iNext. iIntros "Hslice".
            iSplit; first done.
            iDestruct ("Hreconstitute" $! slice Hslice_len with "Hslice")
              as "Hblock".
            iAssert (wblock (preg_base r)
              (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
               slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
                 t_length t) tbs))%I with "[Hblock]" as "Hblock'".
            { rewrite /wblock /cmem_block_at_pos N2Nat.id. iExact "Hblock". }
            iMod ("Hcls" with "[Hwall Hblock' Hslots]").
            { iNext.
              iExists (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
                slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
                  t_length t) tbs).
              iSplit; first by rewrite Hfull.
              iSplit; first by rewrite Hfull.
              iFrame "Hwall Hblock'".
              rewrite Hfull. iExact "Hslots". }
            iModIntro. iFrame. }
          iApply (wp_wand _ _ _
            (λ v, ((⌜v = trapV⌝ ∗
              |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
                cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
            with "[Hf Hslice Hpost]").
          { iApply wp_colload_fail_tag;
              [exact Hcol | exact Hslice_len | exact Hslice_pos |
               exact Hbad |].
            iFrame. }
          iIntros (v) "[[-> >Hwon] Hf]".
          iFrame. iLeft. done. }
      have Hrepr := tagged_bytes_map c Numeric slice Hslice_colors Htags.
      set (bs := map tb_value slice).
      have Hbslen : length bs = t_length t by rewrite /bs map_length.
      remember (wasm_deserialise bs t) as v eqn:Hdes.
      iAssert (wblock (ptr_addr p) slice)%I with "[Hslice]" as "Hslice".
      { rewrite /wblock /cmem_block_at_pos. iExact "Hslice". }
      iAssert (wcs (ptr_addr p) c Numeric bs)%I
        with "[Hslice]" as "Hslice".
      { rewrite wcs_wblock /bs -Hrepr. iExact "Hslice". }
      iAssert (▷ (wcs (ptr_addr p) c Numeric bs ∗
        wall c (preg_base r) (preg_size r) -∗
        ((∃ v0, ⌜immV [v] = immV [v0]⌝ ∗ interp_value t v0) ∗
         |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
           cinv_own (preg_name r) (preg_fraction r))))%I
        with "[Hcls Hwon Hslots Hreconstitute]" as "Hpost".
      { iNext. iIntros "[Hslice Hwall]".
        iSplitR "Hslice Hwall Hcls Hwon Hslots Hreconstitute".
        - iExists v. iSplit; first done.
          destruct t; try done; by iExists _.
        - iEval (rewrite wcs_wblock -Hrepr) in "Hslice".
        iDestruct ("Hreconstitute" $! slice Hslice_len with "Hslice")
          as "Hblock".
        iAssert (wblock (preg_base r)
          (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
           slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
             t_length t) tbs))%I with "[Hblock]" as "Hblock'".
        { rewrite /wblock /cmem_block_at_pos N2Nat.id. iExact "Hblock". }
        iMod ("Hcls" with "[Hwall Hblock' Hslots]").
        { iNext.
          iExists (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
            slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
              t_length t) tbs).
          iSplit; first by rewrite Hfull.
          iSplit; first by rewrite Hfull.
          iFrame "Hwall Hblock'".
          rewrite Hfull. iExact "Hslots". }
        iModIntro. iExact "Hwon". }
      iApply (wp_wand _ _ _
        (λ x, (((∃ v0, ⌜x = immV [v0]⌝ ∗ interp_value t v0) ∗
                  |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
                    cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
        with "[Hf Hslice Hwall Hpost]").
      { iApply wp_colload;
          [exact Ht | exact Hbslen | exact (Logic.eq_sym Hdes) |
           exact Hcol |].
        iFrame. }
      iIntros (x) "[[Hv >Hwon] Hf]".
      iModIntro. iFrame "Hwon Hf". iRight. iExact "Hv". }
    iIntros (x) "[[Hx Hwon] Hf]".
    iAssert (pointer_world_entry c r) with "[Hlive Hwon]" as "Hentry".
    { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
      iLeft. iFrame. }
    iDestruct ("Hclose" with "Hentry") as "Hall".
    iDestruct "Hx" as "[-> | Hv]".
    - iSplitR "Hf Hfv Hall"; first by do 2 iLeft.
      iExists _. iFrame.
    - iDestruct "Hv" as (v ->) "Hv".
      iSplitL "Hv".
      + iLeft. iRight. iExists _. iSplit; first done. iFrame. done.
      + iExists _. iFrame.
  Qed. 
        

  Lemma typing_colload_pointer C :
    ⊢ semantic_typing C (to_e_list [BI_colload T_pointer])
        (Tf [T_pointer] [T_pointer]).
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
    destruct ws as [|w ws]; [done|destruct ws; [|done]].
    iSimpl in "Hv". iDestruct "Hv" as "[Hv _]".
    iDestruct "Hv" as (p ->) "Hp".
    iEval (rewrite pointer_interp_unfold /pointer_interp_pre) in "Hp".
    iDestruct "Hp" as "[%Hnull | Hp]".
    { iApply (wp_wand with "[Hf]").
      - iApply (wp_colload_fail_null with "[$Hf]").
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
        - iApply (wp_colload_fail_dead NotStuck ⊤
            (λ x, (⌜x = trapV⌝ ∗ pointer_world_entry c r)%I)
            p T_pointer c f with "[$Hf $Hdead]"); first exact Hcol.
          iNext. iIntros "#Hdead'". iSplit; first done.
            iFrame "Hinv".
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
          { iApply wp_colload_fail_bounds;
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
        - iApply (wp_colload_fail_align with "[$Hf]"); first exact Halign.
          by instantiate (1 := λ x, ⌜x = trapV⌝%I).
        - iIntros (v) "[-> Hf]".
          iAssert (pointer_world_entry c r) with "[Hlive Htok]" as "Hentry".
          { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
            iLeft. iFrame. }
          iDestruct ("Hclose" with "Hentry") as "Hall".
          iSplitR "Hf Hfv Hall"; first by do 2 iLeft.
          iExists _. iFrame. }

    iApply (wp_wand _ _ _
      (λ x, (((⌜x = trapV⌝ ∨
                    ∃ v, ⌜x = immV [v]⌝ ∗ interp_value T_pointer v) ∗
                 cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
      with "[Hf Htok]").
    { iApply (wp_atomic _ _ (⊤ ∖ ↑(pointer_inv_namespace c))).
      iMod (cinv_acc with "Hinv Htok") as "(Hbody & Hwon & Hcls)";
        first solve_ndisj.
      iModIntro.
      iDestruct "Hbody" as (tbs)
        "(>%Htbslen & >%Hcolors & >Hwall & >Hblock & Hslots)".
      iDestruct "Hslots" as "#Hslots".
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
      have Hfull :
          take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
          slice ++
          drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
            t_length T_pointer) tbs = tbs.
      { rewrite Hslice. apply reconstitute. }
      have Htpos : t_length T_pointer > 0.
      { have Hpos := @size_is_not_zero HPB.
        rewrite nat_bin in Hpos. move/ssrnat.ltP in Hpos.
        unfold t_length. by rewrite nat_bin. }
      have Hslice_pos : length slice > 0 by lia.
      destruct (all (fun tb => tb_tag tb == Pointer) slice) eqn:Htags.
      2:{ have Hbad : ~ all (fun tb =>
              (tb_color tb == Some c) && (tb_tag tb == Pointer)) slice.
          { move=> Hboth.
            have Htags' : all (fun tb => tb_tag tb == Pointer) slice.
            { clear -Hboth. induction slice as [|tb slice IH] => //=.
              move/andP: Hboth => [/andP [_ Htag] Htail].
              apply/andP. split; first exact Htag. by apply IH. }
            by rewrite Htags in Htags'. }
          iAssert (▷ (wblock (ptr_addr p) slice -∗
            (⌜trapV = trapV⌝ ∗
             |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
               cinv_own (preg_name r) (preg_fraction r))))%I
            with "[Hcls Hwon Hslots Hreconstitute Hwall]" as "Hpost".
          { iNext. iIntros "Hslice". iSplit; first done.
            iDestruct ("Hreconstitute" $! slice Hslice_len with "Hslice")
              as "Hblock".
            iAssert (wblock (preg_base r)
              (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
               slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
                 t_length T_pointer) tbs))%I with "[Hblock]" as "Hblock'".
            { rewrite /wblock /cmem_block_at_pos N2Nat.id. iExact "Hblock". }
            iMod ("Hcls" with "[Hwall Hblock' Hslots]").
            { iNext.
              iExists (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
                slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
                  t_length T_pointer) tbs).
              iSplit; first by rewrite Hfull.
              iSplit; first by rewrite Hfull.
              iFrame "Hwall Hblock'". rewrite Hfull. iExact "Hslots". }
            iModIntro. iFrame. }
          iApply (wp_wand _ _ _
            (λ v, ((⌜v = trapV⌝ ∗
              |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
                cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
            with "[Hf Hslice Hpost]").
          { iApply wp_colload_fail_tag;
              [exact Hcol | exact Hslice_len | exact Hslice_pos |
               exact Hbad |].
            iFrame. }
          iIntros (v) "[[-> >Hwon] Hf]". iFrame. iLeft. done. }

      set (j := N.to_nat (ptr_addr p) - N.to_nat (preg_base r)).
      have Hslice_ptr :
          take (N.to_nat pointer_size) (drop j tbs) = slice.
      { rewrite /j Hslice. unfold t_length. by rewrite nat_bin. }
      iDestruct ("Hslots" $! j with "[] []") as "#Hloaded".
      { iPureIntro. split.
        - unfold isAlign in Halign.
          unfold t_length in Halign. rewrite nat_bin N2Nat.id in Halign.
          replace (preg_base r + N.of_nat j)%N with (ptr_addr p).
          + exact Halign.
          + rewrite /j Nat2N.inj_sub; rewrite ?N2Nat.id; lia.
        - rewrite /j Hlen_nat.
          unfold t_length in Hbounds. rewrite nat_bin N2Nat.id in Hbounds.
          lia. }
      { iPureIntro. by rewrite Hslice_ptr. }
      iEval (rewrite Hslice_ptr) in "Hloaded".
      have Hrepr := tagged_bytes_map c Pointer slice Hslice_colors Htags.
      set (bs := map tb_value slice).
      have Hbslen : length bs = t_length T_pointer by rewrite /bs map_length.
      iAssert (wblock (ptr_addr p) slice)%I with "[Hslice]" as "Hslice".
      { rewrite /wblock /cmem_block_at_pos. iExact "Hslice". }
      iAssert (wcs (ptr_addr p) c Pointer bs)%I
        with "[Hslice]" as "Hslice".
      { rewrite wcs_wblock /bs -Hrepr. iExact "Hslice". }
      iAssert (▷ (wcs (ptr_addr p) c Pointer bs ∗
        wall c (preg_base r) (preg_size r) -∗
        ((∃ v0, ⌜immV [VAL_pointer (pointer_of_bytes bs)] = immV [v0]⌝ ∗
             interp_value T_pointer v0) ∗
         |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
           cinv_own (preg_name r) (preg_fraction r))))%I
        with "[Hcls Hwon Hslots Hreconstitute]" as "Hpost".
      { iNext. iIntros "[Hslice Hwall]".
        iSplitR "Hslice Hwall Hcls Hwon Hslots Hreconstitute".
        - iExists (VAL_pointer (pointer_of_bytes bs)). iSplit; first done.
          iExists (pointer_of_bytes bs). iSplit; first done.
          iExact "Hloaded".
        - iEval (rewrite wcs_wblock -Hrepr) in "Hslice".
          iDestruct ("Hreconstitute" $! slice Hslice_len with "Hslice")
            as "Hblock".
          iAssert (wblock (preg_base r)
            (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
             slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
               t_length T_pointer) tbs))%I with "[Hblock]" as "Hblock'".
          { rewrite /wblock /cmem_block_at_pos N2Nat.id. iExact "Hblock". }
          iMod ("Hcls" with "[Hwall Hblock' Hslots]").
          { iNext.
            iExists (take (N.to_nat (ptr_addr p) - N.to_nat (preg_base r)) tbs ++
              slice ++ drop (N.to_nat (ptr_addr p) - N.to_nat (preg_base r) +
                t_length T_pointer) tbs).
            iSplit; first by rewrite Hfull.
            iSplit; first by rewrite Hfull.
            iFrame "Hwall Hblock'". rewrite Hfull. iExact "Hslots". }
          iModIntro. iExact "Hwon". }
      iApply (wp_wand _ _ _
        (λ x, (((∃ v0, ⌜x = immV [v0]⌝ ∗ interp_value T_pointer v0) ∗
                  |={⊤ ∖ ↑(pointer_inv_namespace c),⊤}=>
                    cinv_own (preg_name r) (preg_fraction r)) ∗ ↪[frame] f)%I)
        with "[Hf Hslice Hwall Hpost]").
      { iApply wp_colload_ptr;
          [exact Hbslen | exact Halign | exact Hcol | done |].
        iFrame. }
      iIntros (x) "[[Hv >Hwon] Hf]".
      iModIntro. iFrame "Hwon Hf". iRight. iExact "Hv". }
    iIntros (x) "[[Hx Hwon] Hf]".
    iAssert (pointer_world_entry c r) with "[Hlive Hwon]" as "Hentry".
    { rewrite /pointer_world_entry. iSplit; first iExact "Hinv".
      iLeft. iFrame. }
    iDestruct ("Hclose" with "Hentry") as "Hall".
    iDestruct "Hx" as "[-> | Hv]".
    - iSplitR "Hf Hfv Hall"; first by do 2 iLeft.
      iExists _. iFrame.
    - iDestruct "Hv" as (v ->) "Hv".
      iSplitL "Hv".
      + iLeft. iRight. iExists _. iSplit; first done. iFrame. done.
      + iExists _. iFrame.
  Qed.

  Lemma typing_colload C t :
    ⊢ semantic_typing C (to_e_list [BI_colload t]) (Tf [T_pointer] [t]).
  Proof.
    destruct t; try by apply typing_colload_numeric.
    apply typing_colload_pointer.
  Qed.

End fundamental.
