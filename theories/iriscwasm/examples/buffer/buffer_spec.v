From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.

From CWasm Require Import stdpp_aux color_ptr datatypes operations properties
  opsem typing.
From CWasm.iriscwasm.language.iris Require Import iris iris_locations.
From CWasm.iriscwasm.language Require Import iris_atomicity iris_wp_def.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm.iriscwasm.host Require Import iris_host.
From CWasm.iriscwasm.rules Require Import iris_rules proofmode
  iris_example_helper.
From CWasm.iriscwasm.logrel Require Import iris_fundamental
  iris_interp_instance_alloc.
From CWasm.iriscwasm.examples.buffer Require Import buffer_code
  buffer_fractional.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section Buffer_spec.

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗
      WP (es : iris.expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I
    (at level 50).

  Context `{!wasmG Σ, !logrel_na_invs Σ, HPB : PointerBytes,
      !cinvG Σ, cancelg : cancelG Σ}.

  (** The number of bytes requested by [BI_const buffer_size ; BI_colalloc].
      It is a [Notation] rather than a [Definition] so that it expands to
      literally the same term as the [n] argument of [wp_colalloc], which is
      what lets the two postconditions unify. *)
  Notation buffer_bytes :=
    (Wasm_int.N_of_uint i32m (Wasm_int.int_of_Z i32m 4%Z))%N.

  Lemma buffer_bytes_4 : buffer_bytes = 4%N.
  Proof. done. Qed.

  Lemma buffer_bytes_nat : N.to_nat buffer_bytes = 4%nat.
  Proof. rewrite buffer_bytes_4. done. Qed.

  (** A non-zero allocation starts at the pointer's own address, which is why
      [wall] and [wcs] below are indexed by [ptr_addr p] alone. *)
  Lemma alloc_result_base_4 (a : N) : alloc_result_base a 4%N = a.
  Proof. by rewrite /alloc_result_base. Qed.

  (** [BI_const size ; BI_colalloc] either yields the null pointer or a fresh
      freeable pointer together with the [wall]/[wcs] resources. *)
  Lemma buffer_alloc_one (f0 : frame) :
    ⊢ {{{ ↪[frame] f0 ∗ interp_allocator }}}
      [AI_const (VAL_numeric buffer_size); AI_basic BI_colalloc]
      {{{ w, (∃ p, ⌜w = immV [VAL_pointer p]⌝ ∗
                (⌜is_null p⌝ ∨
                 (∃ col, ⌜ptr_col p = Some col⌝ ∗
                   ⌜ptr_freeable p = true⌝ ∗
                   wall col (alloc_result_base (ptr_addr p) buffer_bytes)
                        buffer_bytes ∗ live_color col ∗
                   wcs (ptr_addr p) col Numeric
                     (repeat #00%byte (N.to_nat buffer_bytes)))))
               ∗ interp_allocator ∗ ↪[frame] f0 }}}.
  Proof.
    iIntros (Φ) "!> (Hf & Hall) HΦ".
    iApply (wp_wand with "[-HΦ]").
    { iApply (wp_colalloc NotStuck ⊤ (Wasm_int.int_of_Z i32m 4%Z)
        (fun w => ((∃ p, ⌜w = immV [VAL_pointer p]⌝ ∗
          (⌜is_null p⌝ ∨
           (∃ col, ⌜ptr_col p = Some col⌝ ∗
            ⌜ptr_freeable p = true⌝ ∗
            wall col (alloc_result_base (ptr_addr p) buffer_bytes)
              buffer_bytes ∗ live_color col ∗
            wcs (ptr_addr p) col Numeric
              (repeat #00%byte (N.to_nat buffer_bytes))))) ∗
          interp_allocator)%I)).
      iSplitR "Hf"; last iExact "Hf".
      iNext. iIntros (w) "Hwp". iFrame "Hall". iExact "Hwp". }
    iIntros (w) "[[Hwp Hall] Hf]".
    iApply "HΦ". iFrame.
  Qed.

  (** The initialising store of [buffer_value] into the first buffer. *)
  Lemma buffer_store_one (f0 : frame) (p : pointer) (c : N) :
    ptr_col p = Some c ->
    ⊢ {{{ ↪[frame] f0 ∗ wall c (ptr_addr p) 4 ∗ live_color c ∗
            wcs (ptr_addr p) c Numeric (repeat #00%byte 4) }}}
      [AI_const (VAL_pointer p); AI_const (VAL_numeric buffer_value);
       AI_basic (BI_colstore T_i32)]
      {{{ w, (⌜w = immV []⌝ ∗
            wall c (ptr_addr p) 4 ∗
            wcs (ptr_addr p) c Numeric (bits (VAL_numeric buffer_value))) ∗
            ↪[frame] f0 }}}.
  Proof.
    iIntros (Hcol Φ) "!> (Hf & Hwall & Hlive & Hwcs) HΦ".
    iAssert (wblock (ptr_addr p)
      (map (fun b : byte => {| tb_value := b; tb_color := Some c;
                tb_tag := Numeric |}) (repeat #00%byte 4)))%I
      with "[Hwcs]" as "Hblock".
    { rewrite -wcs_wblock. iExact "Hwcs". }
    iApply (wp_wand with "[-HΦ]").
    iApply (wp_colstore NotStuck ⊤
      (λ w, (⌜w = immV []⌝ ∗
              wall c (ptr_addr p) 4 ∗
              wcs (ptr_addr p) c Numeric
                (bits (VAL_numeric buffer_value)))%I)
      p T_i32 c (ptr_addr p) 4
      (map (fun b : byte => {| tb_value := b; tb_color := Some c;
                tb_tag := Numeric |}) (repeat #00%byte 4))
      (VAL_numeric buffer_value) f0 with "[Hf Hblock Hwall]").
    { rewrite /=. done. }
    { exact Hcol. }
    { rewrite /=. done. }
    { rewrite /= !eqxx. done. }
    { done. }
    iSplitR "Hwall Hf Hblock".
    { iModIntro. iIntros "[Hwcs' Hwall']".
      iFrame "Hwall' Hwcs'". iPureIntro. done. }
    iFrame "Hf Hblock Hwall".
    iApply "HΦ".
  Qed.

  Lemma buffer_allocation_body (p : pointer) (c : N) :
    wall c (ptr_addr p) 4 -∗
    wcs (ptr_addr p) c Numeric (repeat #00%byte 4) -∗
    ▷ pointer_allocation_body pointer_interp c (ptr_addr p) 4.
  Proof.
    iIntros "Hwall Hwcs". iNext.
    iExists (map (λ b : byte,
      {| tb_value := b; tb_color := Some c; tb_tag := Numeric |})
      (repeat #00%byte 4)).
    iSplit; first done.
    iSplit.
    { iPureIntro. simpl. by rewrite !eq_refl. }
    iFrame "Hwall".
    iSplitL "Hwcs".
    { rewrite -wcs_wblock. iExact "Hwcs". }
    iApply pointer_slots_numeric.
    done.
  Qed.

  (** Calling the imported adversary consumes a related pointer and returns
      the allocator world and the non-atomic-invariant token.  This is the
      reusable call boundary needed by the buffer proof. *)
  Lemma buffer_call_adversary f a i C es locs p :
    tc_label C = [] /\ tc_return C = None ->
    f.(f_inst).(inst_funcs) !! fun_adv = Some a ->
    be_typing (upd_local_label_return C (T_pointer :: locs)
      [[]] (Some [])) es (Tf [] []) ->
    ⊢ {{{ ↪[frame] f ∗ interp_allocator ∗ na_own logrel_nais ⊤ ∗
         na_inv logrel_nais (wfN (N.of_nat a))
           ((N.of_nat a) ↦[wf]
             (FC_func_native i (Tf [T_pointer] []) locs es)) ∗
         interp_instance C [] i ∗
         interp_value_pointer (VAL_pointer p) }}}
      [AI_pointer p; AI_basic (BI_call fun_adv)]
      {{{ w, (⌜w = trapV⌝ ∨
              (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗
                interp_allocator)) ∗ ↪[frame] f }}}.
  Proof.
    iIntros (HC Hfunc Hes Φ) "!> (Hf & Hall & Hown & #Hfinv & #Hi & #Hp) HΦ".
    iApply (wp_wand with "[-HΦ] HΦ").

    rewrite (separate1 (AI_pointer _)).
    rewrite (separate1 (AI_basic _)).
    iApply wp_wasm_empty_ctx.
    iApply wp_base_push; first done.
    iApply (wp_call_ctx with "Hf"); first done.
    iIntros "!> Hf". iApply wp_base_pull. iSimpl.

    rewrite (separate2 (AI_pointer _)).
    iApply (wp_wand_ctx with "[-]").
    iApply (wp_seq_can_trap_ctx with "[-]").
    iSplitR; last first.
    iSplitR; last first. iFrame "Hf".
    iSplitL "Hown Hall".
    iIntros "Hf". rewrite (separate1 (AI_pointer _)).
    iApply fupd_wp.
    iMod (na_inv_acc with "Hfinv Hown") as "(>Haf & Hown & Hcls)";
      try solve_ndisj.
    iModIntro. iApply (wp_invoke_native with "Hf Haf"); try done.
    iIntros "!> [Hf Haf]".
    iApply fupd_wp. iMod ("Hcls" with "[$]") as "Hown".
    iModIntro.

    rewrite -wp_frame_rewrite.
    iApply wp_wasm_empty_ctx_frame.
    take_drop_app_rewrite 0.
    iApply (wp_block_local_ctx with "Hf"); [eauto..|].
    iNext. iIntros "Hf".
    iApply wp_wasm_empty_ctx_frame.
    erewrite wp_frame_rewrite.

    iDestruct (be_fundamental_local _ _ [_] _ locs with "Hi") as "Hl";
      [exact HC | exact Hes |].
    iSpecialize ("Hl" $! _ (VAL_pointer p :: n_zeros locs)
      with "Hf Hown Hall []").
    { iRight. iExists _. iSplit; first done. iSimpl.
      iSplitL "Hp"; first iExact "Hp".
      iApply n_zeros_interp_values. }
    unfold interp_expression_closure_no_host.
    iApply (wp_wand with "Hl").
    iIntros (w) "([Hw Hown] & Hf & Hall)".
    iSplitL "Hw".
    { iDestruct "Hw" as "[Hw | Hw]".
      - iLeft. iExact "Hw".
      - iRight. iDestruct "Hw" as (vs) "[-> Hvs]".
        destruct vs; last done. iClear "Hvs".
        by instantiate (1 := λ x, ⌜x = immV []⌝%I). }
    iExists _. iFrame.

    iCombine "Hown Hall" as "Hresources".
    instantiate (1 := λ x, (⌜x = f⌝ ∗ _)%I).
    iSplitR "Hresources"; first done. iExact "Hresources".

    iIntros (w f') "(-> & Hf & -> & Hown & Hall)".
    iApply wp_wasm_empty_ctx.
    iApply iris_wp.wp_value; eauto.
    { unfold IntoVal. apply language.of_to_val. done. }
    instantiate (1 := λ v,
      ((⌜v = trapV⌝ ∨
        (⌜v = immV []⌝ ∗ na_own logrel_nais ⊤ ∗ interp_allocator)) ∗
       ↪[frame] f)%I).
    iFrame. iRight. iFrame. done.

    iIntros (f') "(Hf & -> & Hown & Hall)".
    iFrame. iLeft. done.
    Unshelve.
    - by iIntros "%".
    - iIntros (v) "H". iExact "H".
  Qed.

  Lemma buffer_suffix_spec f k gv a i C es locs p1 p2 c1 c2 :
    tc_label C = [] /\ tc_return C = None ->
    f.(f_inst).(inst_funcs) !! fun_adv = Some a ->
    f.(f_inst).(inst_globs) !! global_result = Some k ->
    f.(f_locs) !! local_p1 = Some (VAL_pointer p1) ->
    f.(f_locs) !! local_p2 = Some (VAL_pointer p2) ->
    be_typing (upd_local_label_return C (T_pointer :: locs)
      [[]] (Some [])) es (Tf [] []) ->
    ptr_col p1 = Some c1 ->
    ptr_col p2 = Some c2 ->
    ptr_freeable p2 = true ->
    ⊢ {{{ ↪[frame] f ∗ interp_allocator ∗ na_own logrel_nais ⊤ ∗
         na_inv logrel_nais (wfN (N.of_nat a))
           ((N.of_nat a) ↦[wf]
             (FC_func_native i (Tf [T_pointer] []) locs es)) ∗
         interp_instance C [] i ∗
         N.of_nat k ↦[wg]
           {| g_mut := MUT_mut; g_val := gv |} ∗
         wall c1 (ptr_addr p1) 4 ∗
         wcs (ptr_addr p1) c1 Numeric (bits (VAL_numeric buffer_value)) ∗
         wall c2 (ptr_addr p2) 4 ∗ live_color c2 ∗
         wcs (ptr_addr p2) c2 Numeric (repeat #00%byte 4) }}}
      to_e_list buffer_suffix
      {{{ w, (∃ f', ↪[frame] f') ∗
          (⌜w = trapV⌝ ∨
           (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗ interp_allocator ∗
            N.of_nat k ↦[wg]
              {| g_mut := MUT_mut;
                 g_val := VAL_numeric buffer_value |} ∗
            dead_color c2)) }}}.
  Proof.
    iIntros (HC Hfunc Hglob Hp1loc Hp2loc Hes Hcol1 Hcol2 Hfree2 Φ)
      "!> (Hf & Hall & Hown & #Hfinv & #Hi & Hg & Hwall1 & Hwcs1 & Hwall2 & Hlive2 & Hwcs2) HΦ".
    iAssert (▷ pointer_allocation_body pointer_interp c2
      (ptr_addr p2) 4)%I with "[Hwall2 Hwcs2]" as "Hbody2".
    { iApply (buffer_allocation_body with "Hwall2 Hwcs2"). }
    set (p2d := new_pointer (ptr_addr p2) (ptr_col p2) false).
    iApply fupd_wp.
    iMod (buffer_publish_demoted (p := p2) (c := c2) (ptr_addr p2) 4
      Hcol2 with
      "Hlive2 Hbody2 Hall")
      as (γ) "(#Hp2d & #Hregistered & #Hinv2 & Hall & Hlive_private & Htoken_private)".
    set (r := PointerRegistration γ (ptr_addr p2) 4 (1/2)%Qp).
    iModIntro.
    iApply (wp_wand _ _ _ (λ w,
      ((∃ f', ↪[frame] f') ∗
       (⌜w = trapV⌝ ∨
        (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗ interp_allocator ∗
         N.of_nat k ↦[wg]
           {| g_mut := MUT_mut; g_val := VAL_numeric buffer_value |} ∗
         dead_color c2)))%I) with "[-HΦ] HΦ").
    unfold buffer_suffix. iSimpl.

    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_get_local with "[] Hf"); first exact Hp2loc.
      by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p2]⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_pointer _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_demote NotStuck ⊤ _ p2 p2d f with "Hf").
      - rewrite /p2d /=. done.
      - rewrite /p2d /=. done.
      - rewrite /p2d /=. done.
      - by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p2d]⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    take_drop_app_rewrite 2.
    iApply (wp_wand _ _ _ (λ w,
      ((⌜w = trapV⌝ ∨
        (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗ interp_allocator ∗
         N.of_nat k ↦[wg]
           {| g_mut := MUT_mut; g_val := VAL_numeric buffer_value |} ∗
         dead_color c2)) ∗ ↪[frame] f)%I) with "[-]").
    2:{ iIntros (w) "[Hresult Hf]".
        iSplitL "Hf"; first by iExists _. iExact "Hresult". }
    iApply (wp_seq_can_trap_same_empty_ctx
      (λ w, (⌜w = trapV⌝ ∨
        (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗ interp_allocator ∗
         N.of_nat k ↦[wg]
           {| g_mut := MUT_mut; g_val := VAL_numeric buffer_value |} ∗
         dead_color c2))%I)
      (λ w, (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗
        interp_allocator ∗
        N.of_nat k ↦[wg] {| g_mut := MUT_mut; g_val := gv |} ∗
        wall c1 (ptr_addr p1) 4 ∗
        wcs (ptr_addr p1) c1 Numeric (bits (VAL_numeric buffer_value)) ∗
        live_color_frac c2 (1/2)%Qp ∗
        cinv_own γ (1/2)%Qp)%I)
      NotStuck ⊤ _ _ f).
    iSplitR.
    { iIntros "(%Hcontra & _)". done. }
    iSplitR.
    { iLeft. done. }
    iFrame "Hf".
    iSplitL "Hall Hown Hg Hwall1 Hwcs1 Hlive_private Htoken_private".
    { iIntros "Hf".
      iApply (buffer_call_adversary (f := f) (a := a)
        (C := C) (es := es) (locs := locs) i p2d
        HC Hfunc Hes with "[$Hf $Hall $Hown]").
      { iFrame "#". }
      iIntros (v) "[[%Htrap | (-> & Hown & Hall)] Hf]".
      - iFrame "Hf". iLeft. done.
      - iFrame "Hf". iRight. iFrame. done. }
    iIntros (w) "[(-> & Hown & Hall & Hg & Hwall1 & Hwcs1 & Hlive_private & Htoken_private) Hf]".
    iDestruct (interp_allocator_reclaim_half c2 r with
      "Hregistered Hlive_private Htoken_private Hall")
      as "(#Hinv2' & Hlive2 & Htoken2 & Hclose)"; first done.
    iApply fupd_wp.
    iMod (cinv_cancel with "Hinv2' Htoken2") as "Hbody2";
      first solve_ndisj.
    iDestruct "Hbody2" as (tbs2)
      "(>%Htbslen2 & >%Hcolors2 & >Hwall2 & >Hblock2 & Hslots2)".
    iModIntro. iSimpl.

    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_get_local with "[] Hf"); first exact Hp1loc.
      by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p1]⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_pointer _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hwall1 Hwcs1".
    { iApply (wp_colload with "[$Hf $Hwall1 $Hwcs1]").
      - done.
      - apply length_bits. done.
      - apply deserialise_bits. done.
      - exact Hcol1.
      - iIntros "!> Hresources".
        instantiate (1 := λ w,
          (⌜w = immV [VAL_numeric buffer_value]⌝ ∗
           wcs (ptr_addr p1) c1 Numeric
             (bits (VAL_numeric buffer_value)) ∗
           wall c1 (ptr_addr p1) 4)%I).
        iSplitR; first done. iExact "Hresources". }
    2:{ iIntros "[(%Hcontra & _) _]". done. }
    iIntros (w) "[(-> & Hwcs1 & Hwall1) Hf]". iSimpl.

    rewrite (separate2 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hg".
    { fold_const. iApply (wp_set_global with "[] Hf Hg"); first exact Hglob.
      by instantiate (1 := λ w, ⌜w = immV []⌝%I). }
    2:{ by iIntros "(%Hcontra & _ & _)". }
    iIntros (w) "(-> & Hg & Hf)". iSimpl.

    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_get_local with "[] Hf"); first exact Hp2loc.
      by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p2]⌝%I). }
    2:{ by iIntros "[%Hcontra _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    iApply wp_colfree; [exact Hcol2 | exact Hfree2 | exact Htbslen2 | exact Hcolors2 |].
    { iAssert (▷ (dead_color c2 -∗
        (⌜immV [] = trapV⌝ ∨
         (⌜immV [] = immV []⌝ ∗ na_own logrel_nais ⊤ ∗ interp_allocator ∗
          N.of_nat k ↦[wg]
            {| g_mut := MUT_mut;
               g_val := VAL_numeric buffer_value |} ∗
          dead_color c2))))%I
        with "[Hclose Hown Hg]" as "Hpost2".
      { iNext. iIntros "#Hdead2".
        iRight. iFrame "Hown Hg Hdead2".
        iSplitR "Hclose"; first done.
        iApply "Hclose". iExact "Hdead2". }
      iFrame. }
  Qed.

  (** If the second allocation returned the null pointer, the same suffix is
      still safe: the adversary receives a related null pointer and the final
      [colfree] deterministically traps. *)
  Lemma buffer_suffix_null_spec f k gv a i C es locs p1 p2 c1 :
    tc_label C = [] /\ tc_return C = None ->
    f.(f_inst).(inst_funcs) !! fun_adv = Some a ->
    f.(f_inst).(inst_globs) !! global_result = Some k ->
    f.(f_locs) !! local_p1 = Some (VAL_pointer p1) ->
    f.(f_locs) !! local_p2 = Some (VAL_pointer p2) ->
    be_typing (upd_local_label_return C (T_pointer :: locs)
      [[]] (Some [])) es (Tf [] []) ->
    ptr_col p1 = Some c1 ->
    is_null p2 ->
    ⊢ {{{ ↪[frame] f ∗ interp_allocator ∗ na_own logrel_nais ⊤ ∗
         na_inv logrel_nais (wfN (N.of_nat a))
           ((N.of_nat a) ↦[wf]
             (FC_func_native i (Tf [T_pointer] []) locs es)) ∗
         interp_instance C [] i ∗
         N.of_nat k ↦[wg]
           {| g_mut := MUT_mut; g_val := gv |} ∗
         wall c1 (ptr_addr p1) 4 ∗
         wcs (ptr_addr p1) c1 Numeric (bits (VAL_numeric buffer_value)) }}}
      to_e_list buffer_suffix
      {{{ w, (∃ f', ↪[frame] f') ∗ ⌜w = trapV⌝ }}}.
  Proof.
    iIntros (HC Hfunc Hglob Hp1loc Hp2loc Hes Hcol1 Hnull2 Φ)
      "!> (Hf & Hall & Hown & #Hfinv & #Hi & Hg & Hwall1 & Hwcs1) HΦ".
    set (p2d := new_pointer (ptr_addr p2) (ptr_col p2) false).
    have Hnull2col : ptr_col p2 = None.
    { apply/eqP. exact Hnull2. }
    have Hnull2d : is_null p2d.
    { rewrite /is_null /p2d /= Hnull2col. done. }
    iAssert (interp_value_pointer (VAL_pointer p2d))%I as "#Hp2d".
    { rewrite /interp_value_pointer. iExists p2d. iSplit; first done.
      iApply pointer_interp_null. by rewrite /p2d /= Hnull2col. }

    unfold buffer_suffix. iSimpl.
    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_get_local with "[] Hf"); first exact Hp2loc.
      by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p2]⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_pointer _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_demote NotStuck ⊤ _ p2 p2d f with "Hf").
      - rewrite /p2d /=. done.
      - rewrite /p2d /=. done.
      - rewrite /p2d /=. done.
      - by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p2d]⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    take_drop_app_rewrite 2.
    iApply (wp_wand _ _ _ (λ w, (⌜w = trapV⌝ ∗ ↪[frame] f)%I)
      with "[-HΦ]").
    2:{ iIntros (w) "[-> Hf]". iApply "HΦ".
        iSplit; last done. by iExists _. }
    iApply (wp_seq_can_trap_same_empty_ctx
      (λ w, ⌜w = trapV⌝%I)
      (λ w, (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗
        interp_allocator ∗
        N.of_nat k ↦[wg] {| g_mut := MUT_mut; g_val := gv |} ∗
        wall c1 (ptr_addr p1) 4 ∗
        wcs (ptr_addr p1) c1 Numeric
          (bits (VAL_numeric buffer_value)))%I)
      NotStuck ⊤ _ _ f).
    iSplitR.
    { iIntros "(%Hcontra & _)". done. }
    iSplitR.
    { done. }
    iFrame "Hf".
    iSplitL "Hall Hown Hg Hwall1 Hwcs1".
    { iIntros "Hf".
      iApply (buffer_call_adversary (f := f) (a := a)
        (C := C) (es := es) (locs := locs) i p2d
        HC Hfunc Hes with "[$Hf $Hall $Hown]").
      { iFrame "#". }
      iIntros (v) "[[%Htrap | (-> & Hown & Hall)] Hf]".
      - iFrame "Hf". iLeft. done.
      - iFrame "Hf". iRight. iFrame. done. }
    iIntros (w) "[(-> & Hown & Hall & Hg & Hwall1 & Hwcs1) Hf]".
    iSimpl.

    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_get_local with "[] Hf"); first exact Hp1loc.
      by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p1]⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_pointer _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hwall1 Hwcs1".
    { iApply (wp_colload with "[$Hf $Hwall1 $Hwcs1]").
      - done.
      - apply length_bits. done.
      - apply deserialise_bits. done.
      - exact Hcol1.
      - iIntros "!> Hresources".
        instantiate (1 := λ w,
          (⌜w = immV [VAL_numeric buffer_value]⌝ ∗
           wcs (ptr_addr p1) c1 Numeric
             (bits (VAL_numeric buffer_value)) ∗
           wall c1 (ptr_addr p1) 4)%I).
        iSplitR; first done. iExact "Hresources". }
    2:{ iIntros "[(%Hcontra & _) _]". done. }
    iIntros (w) "[(-> & Hwcs1 & Hwall1) Hf]". iSimpl.

    rewrite (separate2 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hg".
    { fold_const. iApply (wp_set_global with "[] Hf Hg"); first exact Hglob.
      by instantiate (1 := λ w, ⌜w = immV []⌝%I). }
    2:{ by iIntros "(%Hcontra & _ & _)". }
    iIntros (w) "(-> & Hg & Hf)". iSimpl.

    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_get_local with "[] Hf"); first exact Hp2loc.
      by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p2]⌝%I). }
    2:{ by iIntros "[%Hcontra _]". }
    iIntros (w) "[-> Hf]". iSimpl.
    iApply (wp_wand with "[Hf]").
    { iApply (wp_colfree_fail_null with "[$Hf]"); first exact Hnull2.
      by instantiate (1 := λ w, ⌜w = trapV⌝%I). }
    iIntros (w) "[-> Hf]". iFrame. done.
  Qed.

  (** Semantic specification of the complete buffer program.  On normal
      return, the value loaded through [p1] is [buffer_value] and the color of
      the original freeable [p2] is dead after the final [colfree]. *)
  Lemma buffer_spec f k gv a es i locs C :
    tc_label C = [] /\ tc_return C = None ->
    f.(f_inst).(inst_globs) !! global_result = Some k ->
    f.(f_inst).(inst_funcs) !! fun_adv = Some a ->
    2 <= length f.(f_locs) ->
    be_typing (upd_local_label_return C (T_pointer :: locs)
      [[]] (Some [])) es (Tf [] []) ->
    ⊢ {{{ ↪[frame] f ∗ interp_allocator ∗ na_own logrel_nais ⊤ ∗
         na_inv logrel_nais (wfN (N.of_nat a))
           ((N.of_nat a) ↦[wf]
             (FC_func_native i (Tf [T_pointer] []) locs es)) ∗
         interp_instance C [] i ∗
         N.of_nat k ↦[wg]
           {| g_mut := MUT_mut; g_val := gv |} }}}
      to_e_list buffer_program
      {{{ w, (∃ f', ↪[frame] f') ∗
          (⌜w = trapV⌝ ∨
           (⌜w = immV []⌝ ∗ na_own logrel_nais ⊤ ∗
            interp_allocator ∗
            N.of_nat k ↦[wg]
              {| g_mut := MUT_mut;
                 g_val := VAL_numeric buffer_value |} ∗
            (∃ p2 c2,
              ⌜ptr_col p2 = Some c2⌝ ∗
              ⌜ptr_freeable p2 = true⌝ ∗ dead_color c2))) }}}.
  Proof.
    iIntros (HC Hglob Hfunc Hlocs Hes Φ)
      "!> (Hf & Hall & Hown & #Hfinv & #Hi & Hg) HΦ".
    destruct (f_locs f) as [|v0 locs0] eqn:Hflocs; simpl in Hlocs; first lia.
    destruct locs0 as [|v1 rest]; simpl in Hlocs; first lia.
    unfold buffer_program, buffer_setup. iSimpl.

    rewrite (separate2 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hall".
    { iApply (buffer_alloc_one with "[$Hf $Hall]").
      iIntros (w) "H". iExact "H". }
    2:{ by iIntros "[(%p & % & _) _]". }
    iIntros (w) "[(%p1 & -> & Hp1) [Hall Hf]]". iSimpl.

    rewrite (separate2 (AI_pointer _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { fold_const. iApply (wp_set_local with "[] Hf").
      - rewrite /local_p1 Hflocs /=. lia.
      - by instantiate (1 := λ w, ⌜w = immV []⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    rewrite (separate2 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hall".
    { iApply (buffer_alloc_one with "[$Hf $Hall]").
      iIntros (w) "H". iExact "H". }
    2:{ by iIntros "[(%p & % & _) _]". }
    iIntros (w) "[(%p2 & -> & Hp2) [Hall Hf]]". iSimpl.

    rewrite (separate2 (AI_pointer _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { fold_const. iApply (wp_set_local with "[] Hf").
      - rewrite /local_p2 /= Hflocs /=. lia.
      - by instantiate (1 := λ w, ⌜w = immV []⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.
    iEval (rewrite /local_p1 /local_p2 Hflocs /=) in "Hf".

    rewrite (separate1 (AI_basic _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf".
    { iApply (wp_get_local with "[] Hf").
      - rewrite /local_p1 /=. done.
      - by instantiate (1 := λ w, ⌜w = immV [VAL_pointer p1]⌝%I). }
    2:{ by iIntros "[% _]". }
    iIntros (w) "[-> Hf]". iSimpl.

    iDestruct "Hp1" as "[Hnull1 | Halloc1]".
    { iDestruct "Hnull1" as %Hnull1.
      rewrite (separate3 (AI_pointer _)).
      iApply (wp_wand with "[Hf]").
      { iApply wp_seq_trap. iFrame.
        iSplitR; last first. iIntros "Hf".
        fold_const.
        iApply (wp_colstore_fail_null with "[$Hf]").
        - exact Hnull1.
        - by instantiate (1 := λ w, ⌜w = trapV⌝%I).
        - by iIntros "!>" (w) "->". }
      iIntros (w) "[-> Hf]". iApply "HΦ".
      iSplitL "Hf"; first by iExists _. iLeft. done. }

    iDestruct "Halloc1" as (c1)
      "(%Hcol1 & %Hfree1 & Hwall1 & Hlive1 & Hwcs1)".
    iEval (rewrite buffer_bytes_4 alloc_result_base_4) in "Hwall1".
    iEval (rewrite buffer_bytes_nat) in "Hwcs1".
    rewrite (separate3 (AI_pointer _)).
    iApply wp_seq. iSplitR; last first.
    iSplitL "Hf Hwall1 Hlive1 Hwcs1".
    { iApply (buffer_store_one _ Hcol1 with
        "[$Hf $Hwall1 $Hlive1 $Hwcs1]").
      iIntros (w) "H". iExact "H". }
    2:{ by iIntros "[(%Hcontra & _) _]". }
    iIntros (w) "[(-> & Hwall1 & Hwcs1) Hf]". iSimpl.

    iDestruct "Hp2" as "[Hnull2 | Halloc2]".
    { iDestruct "Hnull2" as %Hnull2.
      iApply (buffer_suffix_null_spec
        (f := {| f_locs := [:: VAL_pointer p1, VAL_pointer p2 & rest];
                 f_inst := f_inst f |}) (k := k) (a := a)
        (C := C) (es := es) (locs := locs) (p1 := p1) (p2 := p2)
        (c1 := c1) gv i HC Hfunc Hglob with
        "[$Hf $Hall $Hown $Hfinv $Hi $Hg $Hwall1 $Hwcs1]").
      - done.
      - done.
      - exact Hes.
      - exact Hcol1.
      - exact Hnull2.
      - iIntros (w) "[(%f' & Hf) ->]". iApply "HΦ".
        iSplitL "Hf"; first by iExists f'. iLeft. done. }

    iDestruct "Halloc2" as (c2)
      "(%Hcol2 & %Hfree2 & Hwall2 & Hlive2 & Hwcs2)".
    iEval (rewrite buffer_bytes_4 alloc_result_base_4) in "Hwall2".
    iEval (rewrite buffer_bytes_nat) in "Hwcs2".
    iApply (buffer_suffix_spec
      (f := {| f_locs := [:: VAL_pointer p1, VAL_pointer p2 & rest];
               f_inst := f_inst f |}) (k := k) (a := a) (C := C)
      (es := es) (locs := locs) (p1 := p1) (p2 := p2)
      (c1 := c1) (c2 := c2) gv i HC Hfunc Hglob with
      "[$Hf $Hall $Hown $Hfinv $Hi $Hg $Hwall1 $Hwcs1 $Hwall2 $Hlive2 $Hwcs2]").
    - done.
    - done.
    - exact Hes.
    - exact Hcol1.
    - exact Hcol2.
    - exact Hfree2.
    - iIntros (w) "[(%f' & Hf) [-> | (-> & Hown & Hall & Hg & Hdead2)]]".
      + iApply "HΦ". iSplitL "Hf"; first by iExists f'. iLeft. done.
      + iApply "HΦ". iSplitL "Hf"; first by iExists f'.
        iRight. iSplit; first done. iFrame "Hown Hall Hg".
        iExists p2, c2. iSplit; first done. iSplit; first done.
        iExact "Hdead2".
  Qed.

End Buffer_spec.
