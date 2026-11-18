From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants cancelable_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.algebra Require Import list agree auth gmap.
From iris.prelude Require Import options.
From CWasm Require Import datatypes colored_memory color_ptr operations memory_list stdpp_aux.
From CWasm.iriscwasm.logrel Require Export iris_logrel_pointer.
From CWasm.iriscwasm.language Require Import iris_atomicity iris_wp_def.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm.iriscwasm.rules Require Import iris_rules.
Import uPred.

Definition wf : string := "wfN".
Definition wt : string := "wtN".
Definition wm : string := "wmN".
Definition ws : string := "wsN".
Definition wg : string := "wgN".
Definition wfN (a : N) : namespace := nroot .@ wf .@ a.
Definition wtN (a b: N) : namespace := nroot .@ wt .@ a .@ b.
Definition wmN (a: N) : namespace := nroot .@ wm .@ a.
Definition wsN (a: N) : namespace := nroot .@ ws .@ a.
Definition wgN (a: N) : namespace := nroot .@ wg .@ a.

Close Scope byte_scope.


(** Guarded recursive definition used by the pointer case of the CWasm value
    interpretation.  Registration bookkeeping is kept in
    [iris_logrel_pointer.v]; the value and allocator interpretations remain in
    this file alongside the other components of the logical relation. *)
Section pointer_value_interpretation.
  Local Set Bullet Behavior "Strict Subproofs".
  Context `{HPB : PointerBytes, !wasmG Σ, !pointer_logrelG Σ, !cinvG Σ}.

  Notation PR := (leibnizO pointer -n> iPropO Σ).

  Definition pointer_slots (I : PR) (base : N) (tbs : list tagged_byte) : iProp Σ :=
    ∀ j : nat,
      ⌜ (N.modulo (base + N.of_nat j) pointer_size = 0)%N /\
        (j + N.to_nat pointer_size <= length tbs)%nat ⌝ -∗
      ⌜ all (fun tb => tb_tag tb == Pointer)
          (take (N.to_nat pointer_size) (drop j tbs)) ⌝ -∗
      I (pointer_of_bytes
        (map tb_value (take (N.to_nat pointer_size) (drop j tbs)))).

  Definition pointer_allocation_body (I : PR) (c base size : N) : iProp Σ :=
    ∃ tbs : list tagged_byte,
      ⌜ N.of_nat (length tbs) = size ⌝ ∗
      ⌜ all (fun tb => tb_color tb == Some c) tbs ⌝ ∗
      wall c base size ∗ wblock base tbs ∗ pointer_slots I base tbs.

  Definition pointer_allocation_inv (I : PR) (c : N)
      (r : pointer_registration) : iProp Σ :=
    cinv (pointer_inv_namespace c) (preg_name r)
      (pointer_allocation_body I c (preg_base r) (preg_size r)).

  Definition pointer_interp_pre (I : PR) : PR :=
    λne (p : leibnizO pointer),
      (⌜ ptr_col p = None ⌝ ∨
       ∃ (c : N) (r : pointer_registration),
         ⌜ ptr_col p = Some c ⌝ ∗
         pointer_registered c r ∗ pointer_allocation_inv I c r ∗
         ⌜ ptr_freeable p = true -> preg_fraction r = 1%Qp ⌝)%I.

  Global Instance pointer_interp_pre_contractive : Contractive pointer_interp_pre.
  Proof.
    unfold pointer_interp_pre, pointer_allocation_inv,
      pointer_allocation_body, pointer_slots.
    solve_contractive.
  Qed.

  Definition pointer_interp : PR := fixpoint pointer_interp_pre.

  Lemma pointer_interp_unfold (p : pointer) :
    pointer_interp p ≡ pointer_interp_pre pointer_interp p.
  Proof.
    exact (fixpoint_unfold pointer_interp_pre p).
  Qed.

  Global Instance pointer_interp_persistent (p : pointer) :
    Persistent (pointer_interp p).
  Proof.
    rewrite pointer_interp_unfold /pointer_interp_pre
      /pointer_registered /pointer_allocation_inv.
    apply _.
  Qed.

  Lemma pointer_interp_null (p : pointer) :
    ptr_col p = None -> ⊢ pointer_interp p.
  Proof.
    intros Hnull.
    rewrite pointer_interp_unfold /pointer_interp_pre.
    iLeft. done.
  Qed.

  Lemma pointer_interp_registered (p : pointer) (c : N) :
    ptr_col p = Some c ->
    pointer_interp p -∗
      ∃ r : pointer_registration,
        pointer_registered c r ∗
        pointer_allocation_inv pointer_interp c r ∗
        ⌜ ptr_freeable p = true -> preg_fraction r = 1%Qp ⌝.
  Proof.
    intros Hcolor.
    rewrite pointer_interp_unfold /pointer_interp_pre.
    iIntros "[%Hnull | Hptr]"; first congruence.
    iDestruct "Hptr" as (c' r Hcolor')
      "(#Hregistered & #Hinv & %Hfraction)".
    rewrite Hcolor in Hcolor'. inversion Hcolor'; subst c'.
    iExists r. iFrame "Hregistered Hinv". iPureIntro. exact Hfraction.
  Qed.

  Lemma pointer_interp_freeable_full (p : pointer) (c : N) :
    ptr_col p = Some c -> ptr_freeable p = true ->
    pointer_interp p -∗
      ∃ r : pointer_registration,
        pointer_registered c r ∗
        pointer_allocation_inv pointer_interp c r ∗
        ⌜ preg_fraction r = 1%Qp ⌝.
  Proof.
    iIntros (Hcolor Hfree) "Hp".
    iDestruct (pointer_interp_registered p c Hcolor with "Hp")
      as (r) "(#Hregistered & #Hinv & %Hfraction)".
    iExists r. iFrame "Hregistered Hinv".
    iPureIntro. exact (Hfraction Hfree).
  Qed.

  Lemma pointer_interp_half_not_freeable (p : pointer) (c : N)
      (r : pointer_registration) :
    ptr_col p = Some c -> preg_fraction r = (1/2)%Qp ->
    pointer_registered c r -∗ pointer_interp p -∗
      ⌜ ptr_freeable p <> true ⌝.
  Proof.
    iIntros (Hcolor Hhalf) "#Hregistered Hp".
    iIntros (Hfree).
    iDestruct (pointer_interp_freeable_full p c Hcolor Hfree with "Hp")
      as (r') "(#Hregistered' & _ & %Hfull)".
    iDestruct (pointer_registered_agree with
      "Hregistered Hregistered'") as %->.
    rewrite Hhalf in Hfull. done.
  Qed.

  Lemma pointer_interp_nonfreeable (p : pointer) (c : N)
      (r : pointer_registration) :
    ptr_col p = Some c -> ptr_freeable p = false ->
    pointer_registered c r -∗
    pointer_allocation_inv pointer_interp c r -∗ pointer_interp p.
  Proof.
    iIntros (Hcolor Hfree) "#Hregistered #Hinv".
    rewrite pointer_interp_unfold /pointer_interp_pre.
    iRight. iExists c, r. iSplit; first done.
    iFrame "Hregistered Hinv". iPureIntro.
    intros Htrue. rewrite Hfree in Htrue. done.
  Qed.

  Lemma cinv_own_halves (γ : gname) :
    cinv_own γ (1/2)%Qp -∗ cinv_own γ (1/2)%Qp -∗ cinv_own γ 1%Qp.
  Proof.
    iIntros "Hleft Hright".
    iCombine "Hleft Hright" as "Htoken".
    iExact "Htoken".
  Qed.

  Lemma pointer_allocation_cancel_halves (c : N)
      (r : pointer_registration) :
    pointer_allocation_inv pointer_interp c r -∗
    cinv_own (preg_name r) (1/2)%Qp -∗
    cinv_own (preg_name r) (1/2)%Qp ={ ⊤ }=∗
      ▷ pointer_allocation_body pointer_interp c
        (preg_base r) (preg_size r).
  Proof.
    iIntros "#Hinv Hleft Hright".
    iPoseProof (cinv_own_halves with "Hleft Hright") as "Htoken".
    iMod (cinv_cancel with "Hinv Htoken") as "Hbody";
      first solve_ndisj.
    iModIntro. iExact "Hbody".
  Qed.

  Lemma pointer_interp_preserve (p p' : pointer) :
    ptr_col p' = ptr_col p ->
    (ptr_freeable p' = true -> ptr_freeable p = true) ->
    pointer_interp p ⊢ pointer_interp p'.
  Proof.
    intros Hcolor Hfreeable.
    rewrite !pointer_interp_unfold /pointer_interp_pre.
    iIntros "[Hnull | Hptr]".
    - iLeft. by rewrite Hcolor.
    - iRight.
      iDestruct "Hptr" as (c r) "(%Hc & Hreg & Hinv & %Hfraction)".
      iExists c, r. iFrame. iSplit.
      { iPureIntro. by rewrite Hcolor. }
      iPureIntro. intros Hfree. apply Hfraction, Hfreeable, Hfree.
  Qed.

  Lemma pointer_interp_addr (p : pointer) (addr : N) :
    pointer_interp p ⊢ pointer_interp (upd_pointer_addr p addr).
  Proof.
    apply pointer_interp_preserve; done.
  Qed.

  Lemma pointer_interp_demote (p : pointer) :
    pointer_interp p ⊢
      pointer_interp (new_pointer (ptr_addr p) (ptr_col p) false).
  Proof.
    apply pointer_interp_preserve; done.
  Qed.

  Lemma pointer_interp_arith (p p' : pointer) (delta : Z) :
    pointer_arith p delta = Some p' ->
    pointer_interp p ⊢ pointer_interp p'.
  Proof.
    unfold pointer_arith.
    destruct (0 <=? Z.of_N (ptr_addr p) + delta)%Z;
      intros Hresult; inversion Hresult; subst.
    apply pointer_interp_addr.
  Qed.

  Lemma pointer_slots_numeric (I : PR) (base : N) (tbs : list tagged_byte) :
    all (fun tb => tb_tag tb == Numeric) tbs ->
    ⊢ pointer_slots I base tbs.
  Proof.
    intros Hnumeric. rewrite /pointer_slots.
    iIntros (j) "%Hrange %Hpointer".
    iExFalso. iPureIntro.
    destruct Hrange as [Halign Hbound].
    have Hnumeric_drop : all (fun tb => tb_tag tb == Numeric) (drop j tbs).
    { rewrite -(cat_take_drop j tbs) all_cat in Hnumeric.
      rewrite drop_seq_drop.
      by move/andP: Hnumeric => [_ H]. }
    have Hnumeric_slice : all (fun tb => tb_tag tb == Numeric)
        (take (N.to_nat pointer_size) (drop j tbs)).
    { rewrite -(cat_take_drop (N.to_nat pointer_size) (drop j tbs)) all_cat
        in Hnumeric_drop.
      rewrite take_seq_take.
      by move/andP: Hnumeric_drop => [H _]. }
    have Hpositive := @size_is_not_zero HPB.
    rewrite nat_bin in Hpositive.
    have Hlen : length (take (N.to_nat pointer_size) (drop j tbs)) =
        N.to_nat pointer_size.
    { apply take_length_le. rewrite drop_length. lia. }
    move/ssrnat.ltP in Hpositive.
    destruct (take (N.to_nat pointer_size) (drop j tbs)) as [|tb rest];
      simpl in Hlen, Hpointer, Hnumeric_slice; first lia.
    move/andP: Hpointer => [/eqP Hptr _].
    move/andP: Hnumeric_slice => [/eqP Hnum _].
    congruence.
  Qed.
End pointer_value_interpretation.


Class cancelG Σ := CancelG {
                       cancelG_pointer_logrel :: pointer_logrelG Σ
                     }.


Section logrel.

  Context `{!wasmG Σ, !logrel_na_invs Σ, cancelg: cancelG Σ, 
        !cinvG Σ, HPB: PointerBytes}.

  
  Definition xb b := (VAL_int32 (wasm_bool b)).

  Let expr := iris.expr.
  Let val := iris.val.



  Notation VR := ((leibnizO val) -n> iPropO Σ).
  Notation WR := ((leibnizO value) -n> iPropO Σ).
  Notation FR := ((leibnizO frame) -n> iPropO Σ).
  Notation FfR := ((leibnizO N) -n> iPropO Σ).
  Notation ClR := ((leibnizO function_closure) -n> iPropO Σ).
  Notation CtxR := ((leibnizO lholed) -n> iPropO Σ).
  Notation TR := ((leibnizO N) -n> iPropO Σ).
  Notation TeR := ((leibnizO N) -n> (leibnizO N) -n> iPropO Σ).
  Notation MR := ((leibnizO N) -n> iPropO Σ).
  Notation SR := ((leibnizO ()) -n> iPropO Σ).
  Notation GR := ((leibnizO N) -n> iPropO Σ).
  Notation IR := ((leibnizO instance) -n> iPropO Σ).
  Notation BR := ((leibnizO val) -n> (leibnizO lholed) -n> (leibnizO (list (list value_type))) -n> iPropO Σ).
  Notation RR := ((leibnizO val) -n> iPropO Σ).
  Notation HR := ((leibnizO val) -n> (leibnizO lholed) -n> (leibnizO (list (list value_type))) -n> (leibnizO result_type) -n> iPropO Σ).
  Notation HRcls := ((leibnizO val) -n> iPropO Σ).

  Implicit Types w : (leibnizO value).
  Implicit Types ws : (list (leibnizO value)).
  Implicit Types v : (leibnizO val).
  Implicit Types f : (leibnizO frame).
  Implicit Types cl : (leibnizO function_closure).
  Implicit Types lh : (leibnizO lholed).
  Implicit Types n m : (leibnizO N).
  Implicit Types g : (leibnizO global).
  Implicit Types i : (leibnizO instance).

  Implicit Types τ : value_type.
  Implicit Types τs : result_type.
  Implicit Types ηs : result_type.
  Implicit Types τr : result_type.
  Implicit Types τf : function_type.
  Implicit Types τc : list (list value_type).
  Implicit Types τt : table_type.
  Implicit Types τm : memory_type.
  Implicit Types τg : global_type.
  Implicit Types τctx : t_context.

  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- VALUE RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)


  Definition interp_value_i32 : WR := λne w, (∃ z, ⌜w = VAL_int32 z⌝)%I.
  Definition interp_value_i64 : WR := λne w, (∃ z, ⌜w = VAL_int64 z⌝)%I.
  Definition interp_value_f32 : WR := λne w, (∃ z, ⌜w = VAL_float32 z⌝)%I.
  Definition interp_value_f64 : WR := λne w, (∃ z, ⌜w = VAL_float64 z⌝)%I.


  Definition interp_value_pointer : WR :=
    λne w, (∃ p : pointer, ⌜ w = VAL_pointer p ⌝ ∗ pointer_interp p)%I.

  Definition pointer_world_entry (c : N)
      (r : pointer_registration) : iProp Σ :=
    (pointer_allocation_inv pointer_interp c r ∗
      ((live_color_frac c (preg_fraction r) ∗
         cinv_own (preg_name r) (preg_fraction r)) ∨
       dead_color c))%I.

  Definition interp_allocator : iProp Σ :=
    (∃ R : pointer_registry, pointer_registry_auth R ∗
      [∗ map] c ↦ r ∈ R, pointer_world_entry c r)%I.

  Lemma interp_allocator_lookup_acc (c : N)
      (r : pointer_registration) :
    pointer_registered c r -∗ interp_allocator -∗
      pointer_world_entry c r ∗
      (pointer_world_entry c r -∗ interp_allocator).
  Proof.
    iIntros "#Hregistered Hall".
    iDestruct "Hall" as (R) "[Hauth Hentries]".
    iDestruct (pointer_registered_lookup with "Hauth Hregistered") as %Hlookup.
    iDestruct (big_sepM_lookup_acc with "Hentries") as "[Hentry Hclose]";
      first exact Hlookup.
    iFrame "Hentry". iIntros "Hentry".
    iExists R. iFrame "Hauth". by iApply "Hclose".
  Qed.

  Lemma interp_allocator_lookup_status (c : N)
      (r : pointer_registration) :
    pointer_registered c r -∗ interp_allocator -∗
      pointer_allocation_inv pointer_interp c r ∗
      ((live_color_frac c (preg_fraction r) ∗
          cinv_own (preg_name r) (preg_fraction r) ∗
          (dead_color c -∗ interp_allocator)) ∨
       (dead_color c ∗ interp_allocator)).
  Proof.
    iIntros "#Hregistered Hall".
    iDestruct (interp_allocator_lookup_acc c r with
      "Hregistered Hall") as "[Hentry Hclose]".
    iDestruct "Hentry" as "[#Hinv [[Hlive Htoken] | #Hdead]]".
    { iSplit; first iExact "Hinv". iLeft. iFrame "Hlive Htoken".
      iIntros "#Hdead". iApply "Hclose".
      iFrame "Hinv". iRight. iFrame "Hdead". }
    { iSplit; first iExact "Hinv". iRight. iFrame "Hdead".
      iApply "Hclose". iFrame "Hinv". iRight. iFrame "Hdead". }
  Qed.

  Lemma interp_allocator_empty :
    pointer_registry_auth ∅ -∗ interp_allocator.
  Proof.
    iIntros "Hauth". iExists ∅. iFrame. done.
  Qed.

  Lemma interp_allocator_fresh (c : N) :
    live_color c -∗ interp_allocator -∗
      live_color c ∗ ∃ R : pointer_registry, ⌜ R !! c = None ⌝ ∗
        pointer_registry_auth R ∗
        [∗ map] d ↦ r ∈ R, pointer_world_entry d r.
  Proof.
    iIntros "Hnew Hall".
    iDestruct "Hall" as (R) "[Hauth Hentries]".
    destruct (R !! c) as [r|] eqn:Hregistered.
    { iDestruct (big_sepM_lookup _ R c r Hregistered with "Hentries")
        as "Hentry".
      iDestruct "Hentry" as "[_ [[Hold _] | #Hdead]]".
      { by iDestruct (live_color_full_exclusive_frac with "Hnew Hold") as %[]. }
      { by iDestruct (live_color_dead with "Hnew Hdead") as %[]. } }
    { iFrame "Hnew". iExists R. iFrame. done. }
  Qed.

  Lemma interp_allocator_publish_full (c base size : N) :
    live_color c -∗
    ▷ pointer_allocation_body pointer_interp c base size -∗
    interp_allocator ={⊤}=∗
      ∃ γ : gname,
        pointer_registered c (PointerRegistration γ base size 1%Qp) ∗
        pointer_allocation_inv pointer_interp c
          (PointerRegistration γ base size 1%Qp) ∗
        interp_allocator.
  Proof.
    iIntros "Hlive Hbody Hall".
    iDestruct (interp_allocator_fresh c with "Hlive Hall")
      as "[Hlive Hall]".
    iDestruct "Hall" as (R Hnone) "[Hauth Hentries]".
    iMod (cinv_alloc ⊤ (pointer_inv_namespace c) with "Hbody")
      as (γ) "[#Hinv Htoken]".
    set (r := PointerRegistration γ base size 1%Qp).
    iMod (ghost_map_insert_persist c r Hnone with "Hauth")
      as "[Hauth #Hregistered]".
    iModIntro. iExists γ. iFrame "Hregistered Hinv".
    iExists (<[c := r]> R). iFrame "Hauth".
    iApply big_sepM_insert; first exact Hnone.
    iFrame "Hinv Hentries". iLeft. iFrame.
  Qed.

  Lemma interp_allocator_publish_half (c base size : N) :
    live_color c -∗
    ▷ pointer_allocation_body pointer_interp c base size -∗
    interp_allocator ={ ⊤ }=∗
      ∃ γ : gname,
        let r := PointerRegistration γ base size (1/2)%Qp in
        pointer_registered c r ∗
        pointer_allocation_inv pointer_interp c r ∗
        interp_allocator ∗ live_color_frac c (1/2)%Qp ∗
        cinv_own γ (1/2)%Qp.
  Proof.
    iIntros "Hlive Hbody Hall".
    iDestruct (interp_allocator_fresh c with "Hlive Hall")
      as "[Hlive Hall]".
    iDestruct "Hall" as (R Hnone) "[Hauth Hentries]".
    iDestruct "Hlive" as "[Hlive_world Hlive_private]".
    iMod (cinv_alloc ⊤ (pointer_inv_namespace c) with "Hbody")
      as (γ) "[#Hinv Htoken]".
    iDestruct "Htoken" as "[Hworld Hprivate]".
    set (r := PointerRegistration γ base size (1/2)%Qp).
    iMod (ghost_map_insert_persist c r Hnone with "Hauth")
      as "[Hauth #Hregistered]".
    iModIntro. iExists γ.
    iFrame "Hregistered Hinv Hlive_private Hprivate".
    iExists (<[c := r]> R). iFrame "Hauth".
    iApply big_sepM_insert; first exact Hnone.
    iFrame "Hinv Hentries". iLeft. iFrame "Hlive_world Hworld".
  Qed.

  Lemma interp_allocator_reclaim_half (c : N)
      (r : pointer_registration) :
    preg_fraction r = (1/2)%Qp ->
    pointer_registered c r -∗ live_color_frac c (1/2)%Qp -∗
    cinv_own (preg_name r) (1/2)%Qp -∗
    interp_allocator -∗
      pointer_allocation_inv pointer_interp c r ∗
      live_color c ∗ cinv_own (preg_name r) 1%Qp ∗
      (dead_color c -∗ interp_allocator).
  Proof.
    iIntros (Hhalf) "#Hregistered Hlive_private Hprivate Hall".
    iDestruct (interp_allocator_lookup_status c r with
      "Hregistered Hall") as "[#Hinv Hstatus]".
    iDestruct "Hstatus" as "[(Hlive & Hworld & Hclose) | (#Hdead & Hall)]".
    { iFrame "Hinv Hclose".
      iEval (rewrite Hhalf) in "Hlive Hworld".
      iSplitL "Hlive Hlive_private".
      { iApply (live_color_halves with "Hlive Hlive_private"). }
      iApply (cinv_own_halves with "Hworld Hprivate"). }
    { by iDestruct (live_color_frac_dead with
        "Hlive_private Hdead") as %[]. }
  Qed.

   Definition interp_value (τ : value_type) : WR :=
    match τ return _ with
    | T_i32 => interp_value_i32
    | T_i64 => interp_value_i64
    | T_f32 => interp_value_f32
    | T_f64 => interp_value_f64
    | T_pointer => interp_value_pointer
    end.

  Definition interp_values (τs : result_type) : VR :=
    λne v, (∃ ws, ⌜v = immV ws⌝ ∗ [∗ list] w;τ ∈ ws;τs, interp_value τ w)%I.
  Definition interp_val (τs : result_type) : VR :=
    λne v, ((⌜v = trapV⌝) ∨ interp_values τs v)%I.
  

  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- FRAME RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *) 

  (* the frame interpretation includes all resources needed by the currently running frame *)
  Definition interp_frame (τs : result_type) (i : instance): FR :=
    λne f, (∃ vs, ⌜f = Build_frame vs i⌝ ∗ interp_val τs (immV vs) ∗ na_own logrel_nais ⊤)%I.

  
  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- RETURN RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Fixpoint get_base_l {i : nat} (lh : valid_holed i) :=
    match lh with
    | VH_base _ vs _ => vs
    | VH_rec _ _ _ _ lh' _ => get_base_l lh'
    end.
  Fixpoint simple_get_base_l (lh : simple_valid_holed) :=
    match lh with
    | SH_base vs _ => vs
    | SH_rec _ _ _ lh' _ => simple_get_base_l lh'
    end.

  
  Definition interp_return_option (τr : option result_type) (τl : result_type) (i : instance) : RR :=
    λne (w : leibnizO val), (∃ (vh : simple_valid_holed) (v : seq.seq value), ⌜w = retV vh⌝ ∗ ⌜simple_get_base_l vh = v⌝ ∗
                             match τr with 
                             | Some τr => (∃ τs'', interp_val (τs'' ++ τr) (immV v) ∗
                                           ∀ f f', ↪[frame] f' -∗ interp_allocator -∗
                                               WP [AI_local (length τr) f (of_val w)] {{ vs, interp_val τr vs ∗ ↪[frame] f' ∗ interp_allocator }})
                             | None => False
                             end)%I.
  
  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- CLOSURE RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Definition is_basic (a : administrative_instruction) : Prop :=
    match a with
    | AI_basic _ => True
    | _ => False
    end.
  
  Fixpoint is_basic_expr (ai : seq.seq administrative_instruction) : Prop :=
    match ai with
    | [] => True
    | a :: ai => is_basic a ∧ is_basic_expr ai
    end.

  Fixpoint llholed_basic (vh : llholed) : Prop :=
    match vh with
    | LL_base _ ai => is_basic_expr ai
    | LL_label _ _ _ vh ai => is_basic_expr ai ∧ llholed_basic vh
    | LL_local _ _ _ vh ai => is_basic_expr ai ∧ llholed_basic vh
    end.

  (* The following definition is a fixed point for the call host host, in an empty context *)
  Definition interp_call_host_cls_def (host_list : list (hostfuncidx * function_type)) (τ2 : result_type)
             (interp_call_host' : HRcls) : HRcls :=
    (λne (w : leibnizO val),
      (∃ (vh : llholed) (v : seq.seq value) (tf : function_type)
                              (h : hostfuncidx) (τs1 τs2 : result_type),
                               ⌜w = callHostV tf h v vh⌝ ∗
                               ⌜tf = Tf τs1 τs2⌝ ∗
                               ⌜(h,tf) ∈ host_list⌝ ∗
                               ⌜llholed_basic vh⌝ ∗
                               interp_val τs1 (immV v) ∗
                               (* continuation for when the host function reenters *)
                               □ (∀ v2 f, interp_val τs2 v2 -∗
                                                         interp_allocator -∗
                                        ↪[frame] f -∗ na_own logrel_nais ⊤ -∗
                                        WP llfill vh (iris.of_val v2)
                                        {{ vs, (interp_val τ2 vs
                                                ∨ ▷ interp_call_host' vs) ∗ interp_allocator ∗ ↪[frame] f ∗ na_own logrel_nais ⊤ }}
                               ))
    )%I. 

  Global Instance interp_call_host_cls_def_contractive hl t2 : Contractive (interp_call_host_cls_def hl t2).
  Proof.
    solve_proper_prepare.
    repeat (apply exist_ne +
                apply intuitionistically_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
    f_contractive. apply H.
  Defined.

  Definition interp_call_host_cls (host_list : list (hostfuncidx * function_type)) (t2 : result_type)
    := fixpoint (interp_call_host_cls_def host_list t2).

  Lemma fixpoint_interp_call_host_cls_eq (host_list : list (hostfuncidx * function_type)) (t2 : result_type) v :
    interp_call_host_cls host_list t2 v ≡ (interp_call_host_cls_def host_list t2 (interp_call_host_cls host_list t2)) v.
  Proof. exact : (fixpoint_unfold (interp_call_host_cls_def host_list t2)). Qed.

  Definition interp_closure_native i tf1s tf2s tlocs e hl : iProp Σ :=
    ∀ vcs f, interp_val tf1s (immV vcs) -∗
             na_own logrel_nais ⊤ -∗
             ↪[frame] f -∗ interp_allocator -∗
             WP e FRAME (length tf2s); (Build_frame (vcs ++ (n_zeros tlocs)) i)
                  CTX 1; LH_rec [] (length tf2s) [] (LH_base [] []) []
                                {{ v, (interp_val tf2s v
                                       ∨ interp_call_host_cls hl tf2s v)
                                        ∗ na_own logrel_nais ⊤ ∗ ↪[frame] f ∗ interp_allocator }}.

  Definition interp_closure (host_list : list (hostfuncidx * function_type)) (τf : function_type) : ClR :=
      λne cl, (match cl with
               | FC_func_native i (Tf tf1s tf2s) tlocs e => ⌜τf = Tf tf1s tf2s⌝ ∗
                       □ ▷ interp_closure_native i tf1s tf2s tlocs (to_e_list e) host_list
               | FC_func_host (Tf tf1s tf2s) h => ⌜τf = Tf tf1s tf2s⌝ ∗ ⌜(h,τf) ∈ host_list⌝ 
               end)%I. 
  
  Definition interp_function (τf : function_type) (interp_closure' : N -> function_type -> ClR) : FfR :=
    λne n, (∃ (cl : function_closure), na_inv logrel_nais (wfN n) (n ↦[wf] cl)
                                     ∗ interp_closure' n τf cl)%I.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- TABLE RELATION ------------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_table_entry (τf : function_type) (interp_closure' : N -> function_type -> ClR) : TeR :=
    λne n m, (∃ (fe : funcelem), na_inv logrel_nais (wtN n m) (n ↦[wt][m] fe)
                                ∗ from_option ((interp_function τf interp_closure') ∘ N.of_nat) True fe)%I.
  (* ⊤ means failure is allowed in case the table is not populated *)


  (* the table interpretation is a bit tricky: the table size needs to represent the full table, 
     with the capability to increase its size with None entries. A None entry is to describe the 
     out of bounds behaviour of a call indirect (with a trap rather than getting stuck) *)

  Definition interp_table (table_size : nat) (interp_closure' : N -> function_type -> ClR) : TR :=
    λne n, ([∗ list] k ↦ _ ∈ (repeat 0 table_size), ∃ (τf : function_type), interp_table_entry τf interp_closure' n (N.of_nat k))%I.


  (* --------------------------------------------------------------------------------------- *)
  (* ---------------------------------- MEMORY RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)
    
  Definition interp_mem : MR :=
    λne n, (na_inv logrel_nais (wmN n) (∃ (mem : memory),
                                           ([∗ list] k ↦ b ∈ (mem.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat k) ] b) ∗
                                             n ↦[wmlength] operations.mem_length mem))%I.


            
  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- GLOBALS RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_global (τg : global_type) : GR :=
    λne n,
      (match (tg_mut τg) with
      | MUT_immut => ∃ (P : value_type -> WR),
         (□ ∀ w, P (tg_t τg) w -∗ interp_value (tg_t τg) w) ∗ 
         na_inv logrel_nais (wgN n) (∃ w, n ↦[wg] Build_global MUT_immut w ∗ P (tg_t τg) w)
      | MUT_mut => na_inv logrel_nais (wgN n) (∃ w, n ↦[wg] Build_global MUT_mut w ∗ interp_value (tg_t τg) w)
      end)%I.

  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- INSTANCE RELATION ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_instance' (τctx : t_context) (interp_closure' : N -> function_type -> ClR) (interp_closure'' : N -> function_type -> ClR) : IR :=
    λne i, let '{| inst_types := ts; inst_funcs := fs; inst_tab := tbs; inst_memory := ms; inst_globs := gs; |} := i in
           let '{| tc_types_t := ts'; tc_func_t := tfs; tc_global := tgs; tc_table := tabs_t; tc_memory := mems_t;
                   tc_local := tl; tc_label := tlabel; tc_return := treturn |} := τctx in 
           ((* Type declarations *)
             ⌜ts = ts'⌝ ∗
            (* Function declarations *)
           ([∗ list] kf;tf ∈ fs;tfs, interp_function tf interp_closure' (N.of_nat kf)) ∗
            (* Function tables *)           
           (match nth_error tabs_t 0 with
            | Some τt => match nth_error tbs 0 with
                        | Some a => (∃ table_size (table_lim : option N),
                                       ⌜ssrnat.leq (ssrnat.nat_of_bool table_lim)
                                        (ssrnat.nat_of_bool (lim_max (tt_limits τt)))⌝
                                       ∗ (N.of_nat a) ↪[wtlimit] table_lim
                                       ∗ (N.of_nat a) ↪[wtsize] table_size
                                       ∗ (interp_table table_size interp_closure'') (N.of_nat a))
                        | None => False
                        end
            | None => True
            end) ∗
            (* Linear Memory *)
           (match nth_error mems_t 0 with
            | Some τm => match nth_error ms 0 with
                        | Some a => (N.of_nat a) ↪[wmlimit] (lim_max τm) ∗ interp_mem (N.of_nat a)
                        | None => False
                        end
            | None => True
            end) ∗
            (* Global declarations *)
           ([∗ list] kg;gt ∈ gs;tgs, interp_global gt (N.of_nat kg)))%I.

   Definition interp_instance (τctx : t_context) (host_list : list (hostfuncidx * function_type)) : IR := interp_instance' τctx (λ n, interp_closure host_list) (λ n, interp_closure host_list). 
  
  
  Global Instance interp_function_persistent τf n (icl : N -> function_type -> ClR) :
    (∀ n τf cl, Persistent (icl n τf cl)) -> Persistent (interp_function τf icl n).
  Proof.
    intros Hpers.
    unfold interp_function. 
    apply exist_persistent =>cl/=.
    apply sep_persistent;[apply _|]. auto.
  Qed.

  Global Instance interp_closure_persistent hf tf cl :
    Persistent (interp_closure hf tf cl).
  Proof.
    unfold interp_closure.
    destruct cl, f => /=; apply sep_persistent; apply _. 
  Qed. 
  
  Global Instance interp_global_persistent τg n : Persistent (interp_global τg n).
  Proof.
    unfold interp_global.
    destruct (tg_mut τg);apply _.
  Qed.
  Global Instance interp_instance_persistent' τctx i (icl icl' : N -> function_type -> ClR) :
    (∀ n τf cl, Persistent (icl n τf cl)) -> (∀ n τf cl, Persistent (icl' n τf cl)) -> Persistent (interp_instance' τctx icl icl' i).
  Proof.
    destruct i, τctx;simpl.
    repeat apply sep_persistent;apply _.
  Qed.

  Global Instance interp_value_pointer_persistent vs :
    Persistent (interp_value_pointer vs).
  Proof.
    apply _.
  Qed.
  
  Global Instance interp_value_persistent τ vs : Persistent (interp_value τ vs).
  Proof.
    unfold interp_value. destruct τ;try apply _.
  Qed. 
  Global Instance interp_val_persistent τr vs : Persistent (interp_val τr vs).
  Proof.
    unfold interp_val, interp_value. apply or_persistent; [apply _|].
    apply exist_persistent =>v/=.
    apply sep_persistent;[apply _|].
    apply big_sepL2_persistent =>n ? xx.
    destruct xx;apply _.
  Qed. 
  Global Instance interp_call_host_cls_persistent hl t v : Persistent (interp_call_host_cls hl t v).
  Proof.
    rewrite fixpoint_interp_call_host_cls_eq. cbn.
         repeat ((apply exist_persistent =>?) +
                   apply sep_persistent + apply or_persistent).
         all: try apply _.
  Qed. 
         

  Global Instance interp_instance_persistent τctx hl i : Persistent (interp_instance τctx hl i).
  Proof. 
    apply interp_instance_persistent'.
    all: intros. all: unfold interp_closure. all: simpl.
    all: destruct cl,f; try apply sep_persistent;apply _.
  Qed.
  
  (* --------------------------------------------------------------------------------------- *)
  (* ------------------------------- EXPRESSION RELATION ----------------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_call_host_br_def (τl : result_type) (i : instance) (τro : option result_type) (host_list : list (hostfuncidx * function_type))
             (interp_call_host_br' : HR * BR) : HR * BR :=
    (λne (w : leibnizO val) (lh : leibnizO lholed) (τc : leibnizO (list (list value_type))) (τ2 : leibnizO result_type),
      (∃ (vh : llholed) (v : seq.seq value) (tf : function_type)
                              (h : hostfuncidx) (τs1 τs2 : result_type),
                               ⌜w = callHostV tf h v vh⌝ ∗
                               ⌜tf = Tf τs1 τs2⌝ ∗
                               ⌜(h,tf) ∈ host_list⌝ ∗
                               ⌜llholed_basic vh⌝ ∗
                               interp_val τs1 (immV v) ∗
                               (* continuation for when the host function reenters *)
                               □ (∀ v2 f, interp_val τs2 v2 -∗
                                                ↪[frame] f ∗ interp_frame τl i f -∗
                                                interp_allocator -∗
                                        WP llfill vh (iris.of_val v2)
                                        {{ vs, (interp_val τ2 vs
                                                ∨ ▷ interp_call_host_br'.2 vs lh τc
                                                ∨ interp_return_option τro τl i vs
                                                ∨ ▷ interp_call_host_br'.1 vs lh τc τ2)
                                                 ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f ∗ interp_allocator }}
                               )
                           )%I
                              
      ,
      
      λne (w : leibnizO val) (lh : leibnizO lholed) (τc : leibnizO (list (list value_type))
                                                    ),
      ((∃ j, ∃ (vh : valid_holed j) (v : seq.seq value) p, ⌜w = brV vh⌝ ∗ ⌜get_base_l vh = v⌝ ∗ ⌜lh_depth (lh_of_vh vh) = p⌝ ∗
                              ∃ τs' vs k es lh' es' lh'' τs'',
                                ⌜τc !! (j - p) = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S (j - p)) = Some (vs,k,es,lh',es')⌝ ∗
                                ⌜lh_depth lh'' = (lh_depth lh) - S (j - p)⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
                                     interp_val (τs'' ++ τs') (immV v) ∗
                                     ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗
                                               interp_allocator -∗
                                           WP of_val (immV (drop (length τs'') v)) ++ [::AI_basic (BI_br (j - p))]
                                           CTX S (lh_depth lh'); LH_rec vs k es lh' es'
                                           {{ vs, ((∃ τs, interp_val τs vs)
                                                   ∨ ▷ interp_call_host_br'.2 vs lh'' (drop (S (j - p)) τc)
                                                   ∨ interp_return_option τro τl i vs
                                                   ∨ ▷ (∃ τs, interp_call_host_br'.1 vs lh'' (drop (S (j - p)) τc) τs))
                              ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f ∗ interp_allocator }}))%I
      
    ).

  Lemma dist_later_prod (o o1 : HR) (o0 o2 : BR) (n : nat) :
    dist_later n (o, o0) (o1, o2) ->
    dist_later n o o1 ∧ dist_later n o0 o2.
  Proof.
    intros Hdist.
    destruct n;auto.
    { split; by constructor; intros n Hn; lia. }
    split.
    { constructor; intros m Hn. destruct Hdist. apply dist_later_lt in Hn.
      inversion Hn. done. }
        { constructor; intros m Hn. destruct Hdist. apply dist_later_lt in Hn.
      inversion Hn. done. } 
  Qed.
  
  Global Instance interp_call_host_br_def_contractive τl i τto hl : Contractive (interp_call_host_br_def τl i τto hl).
  Proof.
    solve_proper_prepare.
    destruct x,y.
    apply dist_later_prod in H as [? ?].
    apply pair_ne.
    { solve_proper_prepare.
      repeat (apply exist_ne +
                apply intuitionistically_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
      { f_contractive. apply H0. }
      { f_contractive. apply H. }
    }
    { solve_proper_prepare.
      repeat (apply exist_ne +
                apply or_ne +
                apply sep_ne +
                apply and_ne +
                apply wp_ne +
                auto +
                (rewrite /pointwise_relation; intros) +
                apply forall_ne + apply wand_ne).
      { f_contractive. apply H0. }
      { f_contractive. apply exist_ne. apply H. }
    }
  Defined.

  Definition interp_call_host_br (τl : result_type) (i : instance) (τto : option result_type) (host_list : list (hostfuncidx * function_type)) : HR * BR :=
    fixpoint (interp_call_host_br_def τl i τto host_list).

  Definition interp_call_host (τl : result_type) (i : instance) (τto : option result_type) (host_list : list (hostfuncidx * function_type))
    := (interp_call_host_br τl i τto host_list).1.
  Definition interp_br (τl : result_type) (i : instance) (τto : option result_type) (host_list : list (hostfuncidx * function_type))
    := (interp_call_host_br τl i τto host_list).2.

  Lemma fixpoint_interp_br_eq (τc : list (list (value_type))) (τl : result_type) (i : instance) (τto : option result_type)
        (host_list : list (hostfuncidx * function_type)) v lh :
    interp_br τl i τto host_list v lh τc ≡ (interp_call_host_br_def τl i τto host_list (interp_call_host_br τl i τto host_list)).2 v lh τc.
  Proof. pose proof (fixpoint_unfold (interp_call_host_br_def τl i τto host_list)). destruct H as [? ?].
         specialize (H0 v lh τc). auto. Qed.

  Lemma fixpoint_interp_call_host_eq lh (τc : list (list (value_type))) (τl : result_type) (i : instance) (τto : option result_type)
        (host_list : list (hostfuncidx * function_type)) v t2 :
    interp_call_host τl i τto host_list v lh τc t2 ≡ (interp_call_host_br_def τl i τto host_list (interp_call_host_br τl i τto host_list)).1 v lh τc t2.
  Proof. pose proof (fixpoint_unfold (interp_call_host_br_def τl i τto host_list)). destruct H as [? ?].
         specialize (H v lh τc t2). auto. Qed.
  
  Definition interp_br_body τc lh j p (w : seq.seq value) τl i τto hl : iProp Σ :=
    ∃ τs' vs k es lh' es' lh'' τs'',
      ⌜τc !! (j - p) = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S (j - p)) = Some (vs,k,es,lh',es')⌝ ∗
                                                                                 ⌜lh_depth lh'' = (lh_depth lh) - S (j - p)⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
                                                                                            
      interp_val (τs'' ++ τs') (immV w) ∗
      ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗ interp_allocator -∗
            WP of_val (immV (drop (length τs'') w)) ++ [::AI_basic (BI_br (j - p))] CTX S (lh_depth lh'); LH_rec vs k es lh' es'
                {{ vs, ((∃ τs, interp_val τs vs) ∨
                          ▷ interp_br τl i τto hl vs lh'' (drop (S (j - p)) τc) ∨
                          interp_return_option τto τl i vs ∨
                          ▷ (∃ τs, interp_call_host τl i τto hl vs lh'' (drop (S (j - p)) τc) τs)) 
                         ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f ∗ interp_allocator }}.

    Definition interp_br_body_equiv τc lh j p (w : seq.seq value) τl i τto hl : iProp Σ :=
    ∃ τs' vs k es lh' es' lh'' τs'',
      ⌜τc !! (j - p) = Some τs'⌝ ∗ ⌜get_layer lh ((lh_depth lh) - S (j - p)) = Some (vs,k,es,lh',es')⌝ ∗
                                                                                 ⌜lh_depth lh'' = (lh_depth lh) - S (j - p)⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∗
                                                                                                                               ⌜ length w = length (τs'' ++ τs') ⌝ ∗ 
      interp_val (τs'' ++ τs') (immV w) ∗
      ∀ f, ↪[frame] f ∗ interp_frame τl i f -∗ interp_allocator -∗
            WP of_val (immV (drop (length τs'') w)) ++ [::AI_basic (BI_br (j - p))] CTX S (lh_depth lh'); LH_rec vs k es lh' es'
                {{ vs, ((∃ τs, interp_val τs vs) ∨
                          ▷ interp_br τl i τto hl vs lh'' (drop (S (j - p)) τc) ∨
                          interp_return_option τto τl i vs ∨
                          ▷ (∃ τs, interp_call_host τl i τto hl vs lh'' (drop (S (j - p)) τc) τs)) 
                         ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f ∗ interp_allocator }}.
  
  Definition interp_expression (τc : list (list (value_type))) (τto : option result_type) (host_list : list (hostfuncidx * function_type))
             (τs : result_type) (lh : lholed) (τl : result_type) (i : instance) (es : expr) : iProp Σ :=
    (WP es {{ vs, (interp_val τs vs
                   ∨ interp_br τl i τto host_list vs lh τc
                   ∨ interp_return_option τto τl i vs
                   ∨ interp_call_host τl i τto host_list vs lh τc τs) ∗ ∃ f, ↪[frame] f ∗ interp_frame τl i f ∗ interp_allocator }})%I. 
  
  
  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------------- CONTEXT RELATION ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  Fixpoint lholed_valid lh : Prop :=
    match lh with
    | LH_base vs es => const_list vs
    | LH_rec vs n es' lh' es'' => const_list vs ∧ lholed_valid lh'
    end.
  Lemma lholed_valid_fill (lh : lholed) :
    ∀ es, lholed_valid lh -> ∃ LI, lfilled (lh_depth lh) lh es LI.
  Proof.
    induction lh;intros es Hval.
    { exists (l ++ es ++ l0). apply lfilled_Ind_Equivalent. constructor. auto. }
    { destruct Hval as [Hconst [LI Hval%lfilled_Ind_Equivalent]%(IHlh es)].
      eexists. apply lfilled_Ind_Equivalent. constructor;eauto. }
  Qed.

  Fixpoint lholed_lengths (τc : list (list value_type)) lh : Prop :=
    match τc, lh with
    | [], LH_base vs es => True
    | τs :: τc, LH_rec _ n _ lh' _ => length τs = n ∧ lholed_lengths τc lh'
    | _,_ => False
    end.

  Definition interp_ctx_continuation (τc : list (list (value_type))) (τto : option result_type) (hl : list (hostfuncidx * function_type)) (lh : lholed) (k : nat) (τs τl : result_type) (i : instance) : iProp Σ :=
    (∃ vs j es lh' es' lh'', ⌜get_layer lh ((lh_depth lh) - S k) = Some (vs,j,es,lh',es')⌝ ∧ ⌜lh_depth lh'' = (lh_depth lh) - S k⌝ ∧ ⌜is_Some (lh_minus lh lh'')⌝ ∧
                          (□ ∀ v f, interp_val τs v -∗ ↪[frame] f ∗ interp_frame τl i f -∗ interp_allocator -∗
                                    ∃ τs2, interp_expression (drop (S k) τc) τto hl τs2 lh'' τl i (vs ++ ((of_val v) ++ es) ++ es')))%I.
  
  Definition interp_ctx_continuations (τc : list (list (value_type))) (τto : option result_type) (hl : list (hostfuncidx * function_type)) (τl : result_type) (i : instance) : CtxR :=
    λne lh, ([∗ list] k↦τs ∈ τc, interp_ctx_continuation τc τto hl lh k τs τl i)%I.
  
  Definition interp_ctx (τc : list (list value_type)) (τto : option result_type) (hl : list (hostfuncidx * function_type)) (τl : result_type) (i : instance) : CtxR :=
    λne lh, (⌜base_is_empty lh⌝ ∗
             ⌜lholed_lengths (rev τc) lh⌝ ∗
             ⌜lholed_valid lh⌝ ∗
             interp_ctx_continuations τc τto hl τl i lh
            )%I.

  Global Instance interp_ctx_continuations_persistent τc τl τto hl i lh : Persistent (interp_ctx_continuations τc τl τto hl i lh).
  Proof. apply _. Qed.
  Global Instance interp_ctx_persistent τc τto hl τl i lh : Persistent (interp_ctx τc τto τl hl i lh).
  Proof. apply _. Qed.

  Notation IctxR := ((leibnizO instance) -n> (leibnizO lholed) -n> (leibnizO frame) -n> iPropO Σ).

  Definition semantic_typing (τctx : t_context) (es : expr) (tf : function_type) : iProp Σ :=
    match tf with
    | Tf τ1 τ2 => ∀ i lh hl, interp_instance τctx hl i -∗
                         interp_ctx (tc_label τctx) (tc_return τctx) hl (tc_local τctx) i lh -∗
                         ∀ f vs, ↪[frame] f ∗ interp_frame (tc_local τctx) i f -∗ interp_allocator -∗
                                       interp_val τ1 vs -∗
                                  interp_expression (tc_label τctx) (tc_return τctx) hl τ2 lh (tc_local τctx) i ((of_val vs) ++ es)
    end.

  (* --------------------------------------------------------------------------------------- *)
  (* --------------------------- RELATIONS FOR CLOSED CONTEXTS ----------------------------- *)
  (* --------------------------------------------------------------------------------------- *)

  Definition interp_expression_closure_stuck_host (hl : list (hostfuncidx * function_type)) (τs : result_type) (f : frame) (es : expr) : iProp Σ :=
    (WP es {{ vs, ((interp_val τs vs ∨ interp_call_host_cls hl τs vs) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f ∗ interp_allocator }})%I. 

  Definition semantic_typing_local_stuck_host (hl : list (hostfuncidx * function_type)) (τctx : t_context) (es : seq.seq basic_instruction) (ts : result_type) (tf : function_type) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx hl i -∗
                      ∀ f vs, ↪[frame] f -∗ na_own logrel_nais ⊤ -∗ interp_allocator -∗
                               interp_val (τ1 ++ ts) (immV vs) -∗
                               interp_expression_closure_stuck_host hl τ2 f [::AI_local (length τ2)
                                                                (Build_frame vs i)
                                                                [::AI_label (length τ2) [] (to_e_list es)]]
    end.
  
  Definition interp_expression_closure_no_host (τs : result_type) (f : frame) (es : expr) : iProp Σ :=
    (WP es {{ vs, (interp_val τs vs ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f ∗ interp_allocator }})%I.

  Definition semantic_typing_local_no_host (τctx : t_context) (es : seq.seq basic_instruction) (ts : result_type) (tf : function_type) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx [] i -∗
                      ∀ f vs, ↪[frame] f -∗ na_own logrel_nais ⊤ -∗ interp_allocator -∗ 
                               interp_val (τ1 ++ ts) (immV vs) -∗
                               interp_expression_closure_no_host τ2 f [::AI_local (length τ2)
                                                                (Build_frame vs i)
                                                                [::AI_label (length τ2) [] (to_e_list es)]]
    end.
  
End logrel.

(* --------------------------------------------------------------------------------------- *)
(* --------------------------------- HOST INTEGRATION ------------------------------------ *)
(* --------------------------------------------------------------------------------------- *)

Reserved Notation "'WPh' h {{ Φ } }" (at level 20, h, Φ at level 200).

Class host_program_logic Σ `{HPB: PointerBytes, wasmG Σ} := {
    host_function : Type ;
    result : Type ;

    (* host context *)
    host_ctx : Type ;
    fill_host : host_ctx -> iris.expr -> host_function ;

    (* we need functions that translates result to a logical wasm value *)
    val_of_host_val : result -> iris.val ;

    (* the host WP *)
    wp_host (s : stuckness) : coPset -d> host_function -d> (result -d> iPropO Σ) -d> iPropO Σ
    where "'WPh' h {{ Φ } }" := (wp_host NotStuck ⊤ h Φ);

    (* host bind lemma *)
    wp_host_bind :
    (∀ hctx es Φ, 
        WP es {{ v, WPh fill_host hctx (iris.of_val v) {{ Φ }} }} -∗
           WPh fill_host hctx es {{ Φ }});

    (* host wand *)
    wp_host_wand :
    (∀ es Φ Ψ, WPh es {{ Φ }} -∗ (∀ r, Φ r -∗ Ψ r) -∗ WPh es {{ Ψ }});

    (* host fupd intro *)
    fupd_wp_host :
    (∀ e Φ, (|={⊤}=> WPh e {{ Φ }}) -∗ WPh e {{ Φ }});
    wp_fupd_host :
    (∀ e Φ, (WPh e {{ λ v, |={⊤}=> Φ v }}) -∗ WPh e {{ Φ }});
  }.

Notation "'WPh' h {{ Φ } }" := (wp_host NotStuck ⊤ h Φ).

Section logrel_host.
  Context `{HPB: PointerBytes, !wasmG Σ, !logrel_na_invs Σ, !host_program_logic Σ, !cinvG Σ, cancelg: cancelG Σ}.

  Let expr := iris.expr.
  Let val := iris.val.

  Definition interp_expression_closure (hctx : host_ctx) (τs : result_type)  (f : frame) (es : expr) : iProp Σ :=
    (WPh fill_host hctx es {{ λ vs, (interp_val τs (val_of_host_val vs) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f ∗ interp_allocator }})%I.

  Definition interp_closure_host (t2 : result_type) (hctx : host_ctx) tf1s tf2s (h : hostfuncidx) : iProp Σ :=
    □ ∀ vcs f llh, ▷ interp_val tf1s (immV vcs) -∗
           na_own logrel_nais ⊤ -∗
           ↪[frame] f -∗ interp_allocator -∗ 
           ▷ (∀ v2, interp_val tf2s v2 -∗ na_own logrel_nais ⊤ -∗ ↪[frame] f -∗ interp_allocator -∗
                               WPh fill_host hctx (llfill llh (iris.of_val v2)) {{ λ r, (interp_val t2 (val_of_host_val r) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f ∗ interp_allocator }}) -∗
           WPh fill_host hctx (llfill llh [AI_call_host (Tf tf1s tf2s) h vcs])
           {{ λ r, (interp_val t2 (val_of_host_val r) ∗ na_own logrel_nais ⊤) ∗ ↪[frame] f ∗ interp_allocator }}. 

  Definition interp_host_calls (t2 : result_type) (hctx : host_ctx) (hl : list (hostfuncidx * function_type)) : iProp Σ :=
    [∗ list] ht ∈ hl, let '(h, t) := ht in
                      let 'Tf tf1s tf2s := t in
                      interp_closure_host t2 hctx tf1s tf2s h.

  Global Instance interp_host_calls_persistent t2 hctx hl : Persistent (interp_host_calls t2 hctx hl).
  Proof. apply big_sepL_persistent =>n x. destruct x,f; apply _. Qed.
         
  Definition interp_host_return (hctx : host_ctx) (τ2 : result_type) : iProp Σ :=
    □ ∀ v f, interp_val τ2 v -∗
             na_own logrel_nais ⊤ -∗          
             ↪[frame] f -∗ interp_allocator -∗
             WPh fill_host hctx (iris.of_val v) {{ λ r, (interp_val τ2 (val_of_host_val r) ∗ na_own logrel_nais ⊤) ∗ ↪[frame]f ∗ interp_allocator }}.
  
  Definition semantic_typing_local (τctx : t_context) (hl : list (hostfuncidx * function_type))
             (es : seq.seq basic_instruction) (ts : result_type) (tf : function_type) (hctx : host_ctx) : iProp Σ :=
    ⌜(tc_label τctx) = [] ∧ (tc_return τctx) = None⌝ ∧
    match tf with
    | Tf τ1 τ2 => ∀ i, interp_instance τctx hl i -∗
                      interp_host_calls τ2 hctx hl -∗
                      interp_host_return hctx τ2 -∗        
                      ∀ f vs, ↪[frame] f -∗ na_own logrel_nais ⊤ -∗ interp_allocator -∗ 
                               interp_val (τ1 ++ ts) (immV vs) -∗
                               interp_expression_closure hctx τ2 f [::AI_local (length τ2)
                                                                (Build_frame vs i)
                                                                [::AI_label (length τ2) [] (to_e_list es)]]
    end.



End logrel_host.
