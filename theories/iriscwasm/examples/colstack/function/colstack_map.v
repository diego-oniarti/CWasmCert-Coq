From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From CWasm.iriscwasm.examples.colstack Require Export colstack_common.
From CWasm.iriscwasm.logrel Require Import iris_logrel.
From CWasm.iriscwasm.language Require Import iris_wp_def.
From CWasm.iriscwasm.rules Require Import iris_rules proofmode.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm Require Import opsem common stdpp_aux.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section stack.

 Context `{!wasmG Σ, HPB: PointerBytes, cancelg: !cancelG Σ, !cinvG Σ }. 

 
Section code.

(*
  map: [pointer, i32] -> []
  locals declared: [i32, i32]

  Given a stack pointer and a function reference from table 0, apply the function to all elements of the stack and
  storing the results in the original stack.

  Implementation is done via looping through the stack, loading each element and call_indirect the function, then
  store the element back to the original address. The loop variable represents the top address that *has* been 
  dealt with, to avoid u32 overflow. The loop upper bound is then simply the stack top pointer, retrieved from the value
  stored in the stack pointer address.

  The spec of the map function allows description of a relationship between the old and the new stack via an arbitrary
  assertion, which is given by the spec of the input function reference.
  
  Returns nothing. Can trap if the stack validation traps, or any of the function application traps.

  Parameters/Locals:
  0 (input)     stack pointer
  1 (input)     function reference from table 0, which must be of type [i32] -> [i32]
  2             temporary variable storing the loop variable: a pointer to the contents
  3             temporary variable storing the loop upper bound
*)
  
Definition map_initialise :=
  [
    BI_get_local 0 ;
    BI_colload T_i32;
    BI_set_local 3 ;
  
    BI_get_local 0;
    BI_set_local 2
  ].

Definition map_loop_body :=
  [
    (* Check if the loop is done *)
    BI_get_local 2 ;
    BI_get_local 0 ;
    BI_pointerdiff ;
    BI_get_local 3 ;
    BI_relop T_i32 (Relop_i ROI_eq) ;
    BI_br_if 1 ;

    (* Update the loop variable and add a copy to the stack (for storing later) *)
    i32const 4 ;
    BI_get_local 2 ;
    BI_pointeradd ;
    BI_tee_local 2 ;

    (* Load the stack element, apply the function and store the result back to the stack *)
    BI_get_local 2 ;
    BI_colload T_i32 ;
    BI_get_local 1 ;
    BI_call_indirect 3 ;
    BI_colstore T_i32 ;

    (* Keep the loop alive *)
    BI_br 0
  ].

Definition stack_map :=
  map_initialise ++
  [
    BI_block (Tf [] [])
             [BI_loop (Tf [] []) map_loop_body]
  ].


End code.


Section specs.
  Set Bullet Behavior "Strict Subproofs".

Lemma spec_map_initialise (f: frame) s v E:
  ⊢ {{{ 
        ⌜ f.(f_locs) !! 0 = Some (value_of_pointer v) ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        isStack v s ∗
        ↪[frame] f }}}
    to_e_list map_initialise @ E
    {{{ w, ⌜ w = immV [] ⌝ ∗
           isStack v s ∗
           ↪[frame] {|
             f_locs := <[ 2 := value_of_pointer v ]>
                       (<[ 3 := value_of_uint (N.of_nat (length s) * 4) ]> f.(f_locs));
             f_inst := f_inst f
           |}
    }}}.
Proof.
  iIntros "!>" (Φ) "(%Hlocs0 & %Hlocs & Hs & Hf) HΦ" => /=.

  iDestruct (stack_pure with "Hs") as "(%Hoff & %Hbound & %Hvalid & %Hlens)".
  
  rewrite separate1.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }
  
  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜w = immV [_]⌝ ∗ isStack v s ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hs Hf".
  2: { by iApply (stack_load_0 with "[$Hs] [$Hf]") => //. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { fold_const; iApply wp_set_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate1.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local; last by iApply "Hf".
       - simpl.
         rewrite - fmap_insert_set_nth; last lia.
         by rewrite list_lookup_insert_ne => //.
       - by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  - fold_const; iApply wp_set_local; last by iApply "Hf".
    + simpl.
      rewrite - fmap_insert_set_nth; last lia.
      rewrite insert_length.
      lia.
    + by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I).
  - iIntros (w) "(-> & f)" => /=.
    iApply "HΦ".
    iFrame.
    iSplit => //.
    
    erewrite fmap_insert_set_nth => /=; last by rewrite insert_length; lia.
    erewrite fmap_insert_set_nth => /=; last lia.
    done.
Qed.

Lemma spec_map_loop_body_terminate f s v E j k :
  ⊢ {{{
        ⌜ f.(f_locs) !! 0 = Some (value_of_pointer v) ⌝ ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_pointer j) ⌝ ∗
        ⌜ f.(f_locs) !! 3 = Some (value_of_uint k) ⌝ ∗
        ⌜ pointer_arith v (Z.of_N k) = Some j ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        isStack v s ∗
        ↪[frame] f }}}
    to_e_list map_loop_body @ E
    {{{ w, ⌜ exists es, w = brV (VH_base 1 [] es) ⌝ ∗
           isStack v s ∗ ↪[frame] f
    }}}.
Proof.
  iIntros "!>" (Φ)
    "(%Hlocs0 & %Hlocs2 & %Hlocs3 & %Harith & %Hlocs & Hs & Hf) HΦ" => /=.

  have Horigdiff : same_origin j v /\
      (Z.of_N (ptr_addr j) - Z.of_N (ptr_addr v) = Z.of_N k)%Z.
  { unfold pointer_arith in Harith.
    destruct (0 <=? Z.of_N (ptr_addr v) + Z.of_N k)%Z eqn:Hnonneg => //.
    inversion Harith; subst j; clear Harith.
    split; first done.
    apply Z.leb_le in Hnonneg. simpl. rewrite Z2N.id; lia. }
  destruct Horigdiff as [Horig Hdiff].

  rewrite separate1.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I). }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [value_of_pointer j; value_of_pointer v]⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { rewrite separate1. iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] Hf") => //. }

  iIntros (w) "[-> Hf]". iSimpl.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜w = immV [_]⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { iApply (wp_pointerdiff NotStuck E _ j v (Z.of_N k) f with "Hf") => //. }

  iIntros (w) "[-> Hf]". iSimpl.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { rewrite separate1.
       iApply wp_val_app => //.
       iSplitR; last first.
       iApply wp_wand_r. iSplitL.
       iApply (wp_get_local with "[] Hf").
       done. by instantiate (1 := λ x, ⌜ x = immV _ ⌝%I).
       iIntros (w) "[-> Hf]".
       iSimpl. by instantiate (1 := λ x, (⌜ x = immV _ ⌝%I ∗ ↪[frame] _)%I); iFrame.
       by iIntros "!> [% _]". }
  { by iIntros "[% _]". }

  iIntros (w) "[-> Hf]". iSimpl.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { fold_const; iApply (wp_relop with "Hf") => //=.
       rewrite Wasm_int.Int32.eq_true => /=.
       by instantiate (1 := λ w, ⌜ w = immV _ ⌝%I). }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_br_if_true with "Hf") => //=.
       iIntros "!> Hf".
       instantiate (1 := λ w, (⌜ w = brV (VH_base 1 [] []) ⌝ ∗ ↪[frame] f)%I).
       iApply wp_value; last by iFrame.
       done. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  - iApply wp_value; last iFrame.
    + instantiate (1 := brV (VH_base 1 [] _)).
      rewrite separate1. unfold IntoVal. simpl. done.
    + by instantiate (1 := λ w, (⌜ w = brV _ ⌝ ∗ ↪[frame] f)%I); iFrame.
  - iIntros (w) "(-> & Hf)" => /=.
    iApply "HΦ". iFrame.
    iPureIntro; by eexists.
Qed.

Lemma spec_map_loop_body_continue f (s : list i32) v hj E j fn
      (sv : i32) j0 a cl
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ⊢ {{{
        ⌜ f.(f_locs) !! 0 = Some (value_of_pointer v) ⌝ ∗
        ⌜ f.(f_locs) !! 1 = Some (VAL_int32 fn) ⌝ ∗
        ⌜ f.(f_locs) !! 2 = Some (value_of_pointer hj) ⌝ ∗
        ⌜ f.(f_locs) !! 3 =
          Some (value_of_uint (N.of_nat (length s) * 4)) ⌝ ∗
        ⌜ pointer_arith v (length s * 4 - 4 * Z.of_N j - 4) = Some hj ⌝ ∗
        ⌜ length f.(f_locs) >= 4 ⌝ ∗
        ⌜ (j < N.of_nat (length s))%N ⌝ ∗
        ⌜ s !! N.to_nat j = Some sv ⌝ ∗
        isStack v s ∗ Φ sv ∗
        ⌜ f.(f_inst).(inst_types) !! 3 = Some (Tf [T_i32] [T_i32]) ⌝ ∗
        ⌜ f.(f_inst).(inst_tab) !! 0 = Some j0 ⌝ ∗
        (N.of_nat j0) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
        (N.of_nat a) ↦[wf] cl ∗
        ⌜ cl_type cl = Tf [T_i32] [T_i32] ⌝ ∗
        (∀ (u : i32) (fc : frame),
          {{{ Φ u ∗ ⌜ f_inst f = f_inst fc ⌝ ∗ ↪[frame] fc ∗
              interp_allocator ∗
              (N.of_nat j0) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m fn)]
                (Some a) ∗
              (N.of_nat a) ↦[wf] cl }}}
          [AI_basic (BI_const (NVAL_int32 u)); AI_invoke a] @ E
          {{{ w, (∃ u', ⌜w = immV [VAL_int32 u']⌝ ∗ Ψ u u') ∗
                  ↪[frame] fc ∗ interp_allocator ∗
                  (N.of_nat j0) ↦[wt][N.of_nat
                    (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
                  (N.of_nat a) ↦[wf] cl }}}) ∗
        ↪[frame] f ∗ interp_allocator }}}
    to_e_list map_loop_body @ E
    {{{ w, ⌜w = brV (VH_base 0 [] [])⌝ ∗
           (∃ sv', isStack v (<[N.to_nat j := sv']> s) ∗ Ψ sv sv') ∗
           (N.of_nat j0) ↦[wt][N.of_nat
             (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
           (N.of_nat a) ↦[wf] cl ∗
           ∃ hj', ⌜pointer_arith v (length s * 4 - 4 * Z.of_N j) =
                         Some hj'⌝ ∗
             ↪[frame] {| f_locs := <[2 := value_of_pointer hj']> f.(f_locs);
                          f_inst := f.(f_inst) |} ∗
             interp_allocator }}}.
Proof.
  iIntros "!>" (Ξ)
    "(%Hlocs0 & %Hlocs1 & %Hlocs2 & %Hlocs3 & %Hhj & %Hlocs &
      %Hjbound & %Hslookup & Hs & HΦ & %Htypes & %Htab & Htab & Hcl &
      %Hclt & #Hspec & Hf & Hall) HΞ" => /=.

  iDestruct (stack_pure with "Hs") as (c) "(%Hcol & %Hfree & %Hlens)".
  have Hlookup_bound := lookup_lt_Some _ _ _ Hslookup.
  have Hdelta_nonneg :
      (0 <= length s * 4 - 4 * Z.of_N j - 4)%Z by lia.
  have Htop_bound :
      (length s * 4 < 4294967296)%Z.
  { unfold two14 in Hlens. lia. }
  have Hdelta_lt :
      (length s * 4 - 4 * Z.of_N j - 4 < length s * 4)%Z by lia.
  have Horig := pointer_arith_same_origin Hhj.
  have Hdiff := pointer_arith_diff Hhj.

  remember (upd_pointer_addr hj (ptr_addr hj + 4)) as hj' eqn:Heqhj'.
  have Hstep : pointer_arith hj 4 = Some hj'.
  { subst hj'. unfold pointer_arith. simpl.
    have Hnonneg : (0 <=? Z.of_N (ptr_addr hj) + 4)%Z = true.
    { apply Z.leb_le. lia. }
    rewrite Hnonneg. unfold upd_pointer_addr. f_equal. f_equal. lia. }
  have Hnext :
      pointer_arith v (length s * 4 - 4 * Z.of_N j) = Some hj'.
  { replace (length s * 4 - 4 * Z.of_N j)%Z with
      ((length s * 4 - 4 * Z.of_N j - 4) + 4)%Z by lia.
    rewrite -(pointer_arith_compose (p := v) (p' := hj)
      (d1 := length s * 4 - 4 * Z.of_N j - 4) 4 Hhj).
    exact Hstep. }

  rewrite (separate1 (AI_basic _)).
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply wp_get_local => //.
       by instantiate (1 := λ w, ⌜w = immV [value_of_pointer hj]⌝%I). }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [value_of_pointer hj; value_of_pointer v]⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { rewrite (separate1 (AI_pointer _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] Hf") => //. }

  iIntros (w) "[-> Hf]". iSimpl.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [VAL_int32 (Wasm_int.int_of_Z i32m
      (length s * 4 - 4 * Z.of_N j - 4))]⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { iApply (wp_pointerdiff NotStuck E _ hj v
      (length s * 4 - 4 * Z.of_N j - 4) f with "Hf") => //. }

  iIntros (w) "[-> Hf]". iSimpl.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜w = immV _⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { rewrite (separate1 (AI_basic _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply wp_get_local => //. }

  iIntros (w) "[-> Hf]". iSimpl.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { fold_const. iApply (wp_relop with "Hf") => //=.
       rewrite Wasm_int.Int32.eq_false => /=.
       - by instantiate (1 := λ w, ⌜w = immV _⌝%I).
       - move=> Heq.
         apply Wasm_int.Int32.repr_inv in Heq.
         + lia.
         + rewrite u32_modulus. split.
           * have Hminus : (-1 < 0)%Z by done.
             exact (Z.lt_le_trans _ _ _ Hminus Hdelta_nonneg).
           * exact (Z.lt_trans _ _ _ Hdelta_lt Htop_bound).
         + rewrite u32_modulus.
           have Htop_eq :
             Z.of_N (N.of_nat (length s) * 4) = (length s * 4)%Z by lia.
           rewrite Htop_eq. split; first lia. exact Htop_bound. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate2.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf".
  2: { iApply (wp_br_if_false with "Hf") => //=.
       by instantiate (1 := λ w, ⌜w = immV []⌝%I). }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite (separate2 (AI_basic _)).
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [value_of_uint 4; value_of_pointer hj]⌝ ∗ ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  2: { rewrite (separate1 (AI_basic _)). fold_const.
       iApply wp_val_app => //=.
       iSplitR; first by iIntros "!> [%Habs _]".
       iApply (wp_get_local with "[] Hf") => //.
  }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜w = immV [value_of_pointer hj']⌝ ∗
                                ↪[frame] f)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { iApply (wp_pointeradd NotStuck E _ hj hj'
      (Wasm_int.Int32.repr (Z.of_N 4)) f with "Hf").
    - simpl. rewrite wasm_int_signed; last lia. exact Hstep.
    - done. }

  iIntros (w) "[-> Hf]" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜w = immV [value_of_pointer hj']⌝ ∗
                                ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { fold_const. iApply (wp_tee_local with "Hf").
    iIntros "!> Hf".
    rewrite (separate1 (AI_pointer _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply (wp_set_local with "[] Hf") => //=.
    lia. }

  iIntros (w) "[-> Hf]" => /=.
  rewrite separate2.
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [value_of_pointer hj'; value_of_pointer hj']⌝ ∗
      ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { rewrite (separate1 (AI_pointer _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] Hf").
    - simpl. rewrite set_nth_read; done.
    - done. }

  iIntros (w) "[-> Hf]" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w,
    (⌜w = immV [value_of_pointer hj'; VAL_int32 sv]⌝ ∗
      isStack v s ∗
      ↪[frame] {| f_locs := <[2 := value_of_pointer hj']> f.(f_locs);
                   f_inst := f.(f_inst) |})%I).
  iSplitR; last iSplitL "Hf Hs".
  { by iIntros "(%Habs & _)". }
  { rewrite (separate1 (AI_pointer _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply (wp_wand with "[Hs Hf]").
    - iApply (stack_load_j v s _ E j sv hj' with "[] [] Hs Hf"); done.
    - iIntros (w) "(-> & Hs & Hf)".
      iSplit; first done. iFrame "Hs".
      rewrite -fmap_insert_set_nth; last lia. iExact "Hf". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite separate3.
  iApply wp_seq.
  instantiate (1 := λ w, (⌜w = immV _⌝ ∗ ↪[frame] _)%I).
  iSplitR; last iSplitL "Hf".
  { by iIntros "(%Habs & _)". }
  { rewrite (separate2 (AI_pointer _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> [%Habs _]".
    iApply (wp_get_local with "[] Hf").
    - simpl. by rewrite list_lookup_insert_ne; last lia.
    - done. }

  iIntros (w) "[-> Hf]" => /=.
  rewrite separate4.
  iApply wp_seq.
  instantiate (1 := λ w,
    (∃ v0, ⌜w = immV [value_of_pointer hj'; VAL_int32 v0]⌝ ∗
            Ψ sv v0 ∗ ↪[frame] _ ∗ interp_allocator ∗
            (N.of_nat j0) ↦[wt][N.of_nat
              (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
            (N.of_nat a) ↦[wf] cl)%I).
  iSplitR; last iSplitL "Hf HΦ Htab Hcl Hall".
  { by iIntros "H"; iDestruct "H" as (v0) "(%Habs & _)". }
  { rewrite (separate1 (AI_pointer _)).
    iApply wp_val_app => //.
    iSplitR; first by iIntros "!> H"; iDestruct "H" as (v0) "(%Habs & _)".
    iApply (wp_call_indirect_success_ctx with "Htab Hcl Hf [HΦ Hall]");
      last first => /=.
    - iPureIntro.
      instantiate (2 := LH_base [AI_basic (BI_const (NVAL_int32 sv))] []).
      instantiate (2 := 0). unfold lfilled, lfill. simpl. by apply/eqP.
    - iIntros "!> (Htab & Hcl & Hf)".
      iApply wp_base_pull. iApply wp_wasm_empty_ctx.
      iApply ("Hspec" with "[$HΦ $Htab $Hcl $Hf $Hall]"); first done.
      iIntros (w) "(Hret & Hf & Hall & Htab & Hcl)".
      iDestruct "Hret" as (v0) "(-> & HΨ)".
      iExists v0. iFrame. done.
    - done.
    - by rewrite Hclt. }

  iIntros (w) "H".
  iDestruct "H" as (v0) "(-> & HΨ & Hf & Hall & Htab & Hcl)" => /=.
  rewrite separate3.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { iApply (stack_store_j with "Hs Hf"); done. }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  iApply (wp_wand with "[Hf]").
  { iApply wp_value; last iFrame.
    - by instantiate (1 := brV (VH_base 0 [] [])).
    - by instantiate (1 := λ w,
        (⌜w = brV (VH_base 0 [] [])⌝ ∗ ↪[frame] _)%I); iFrame. }
  iIntros (w) "(-> & Hf)" => /=.
  iApply "HΞ". iSplit; first done.
  iSplitL "HΨ Hs"; first by iExists v0; iFrame.
  iFrame. iExists hj'. iSplit; first by iPureIntro.
  iExact "Hf".
Qed.

Lemma spec_map_loop_j f (s : list i32) v hj E j fn j0 a cl
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ)
      (s' : list i32) :
  ⊢ (⌜f.(f_locs) !! 0 = Some (value_of_pointer v)⌝ ∗
     ⌜f.(f_locs) !! 1 = Some (VAL_int32 fn)⌝ ∗
     ⌜f.(f_locs) !! 2 = Some (value_of_pointer hj)⌝ ∗
     ⌜f.(f_locs) !! 3 = Some (value_of_uint (N.of_nat (length s) * 4))⌝ ∗
     ⌜pointer_arith v (length s * 4 - 4 * Z.of_N j) = Some hj⌝ ∗
     ⌜length f.(f_locs) >= 4⌝ ∗
     ⌜(j <= N.of_nat (length s))%N⌝ ∗
     ⌜(j + N.of_nat (length s') = N.of_nat (length s))%N⌝ ∗
     isStack v (take (N.to_nat j) s ++ s') ∗
     stackAll (take (N.to_nat j) s) Φ ∗
     stackAll2 (drop (N.to_nat j) s) s' Ψ ∗
     ⌜f.(f_inst).(inst_types) !! 3 = Some (Tf [T_i32] [T_i32])⌝ ∗
     ⌜f.(f_inst).(inst_tab) !! 0 = Some j0⌝ ∗
     (N.of_nat j0) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
     (N.of_nat a) ↦[wf] cl ∗
     ⌜cl_type cl = Tf [T_i32] [T_i32]⌝ ∗
     (∀ (u : i32) (fc : frame),
       {{{ Φ u ∗ ⌜f_inst f = f_inst fc⌝ ∗ ↪[frame] fc ∗
           interp_allocator ∗
           (N.of_nat j0) ↦[wt][N.of_nat
             (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
           (N.of_nat a) ↦[wf] cl }}}
       [AI_basic (BI_const (NVAL_int32 u)); AI_invoke a] @ E
       {{{ w, (∃ u', ⌜w = immV [VAL_int32 u']⌝ ∗ Ψ u u') ∗
               ↪[frame] fc ∗ interp_allocator ∗
               (N.of_nat j0) ↦[wt][N.of_nat
                 (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
               (N.of_nat a) ↦[wf] cl }}}) ∗
     ↪[frame] f ∗ interp_allocator) -∗
  WP (to_e_list map_loop_body) @ E CTX 2;
    push_base (LH_rec [] 0 [] (LH_base [] []) []) 0
      [AI_basic (BI_loop (Tf [] []) map_loop_body)] [] []
  {{ w, ⌜w = immV []⌝ ∗
         (∃ s'', isStack v s'' ∗ stackAll2 s s'' Ψ) ∗
         (∃ f1, ↪[frame] f1 ∗ ⌜f_inst f = f_inst f1⌝) ∗
         interp_allocator ∗
         (N.of_nat j0) ↦[wt][N.of_nat
           (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
         (N.of_nat a) ↦[wf] cl }}.
Proof.
  remember (N.to_nat j) as k.
  iRevert (Heqk). iRevert (j s' s f hj).
  iInduction k as [|k] "IHk".
  - iIntros (j s' s f hj Hk).
    iIntros "(%Hloc0 & %Hloc1 & %Hloc2 & %Hloc3 & %Hhj & %Hlocs &
      %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & Htab & Hcl &
      %Hclt & #Hspec & Hf & Hall)" => /=.
    have Hj : j = 0%N by lia. subst j.
    iApply wp_ctx_bind => //.
    iApply (spec_map_loop_body_terminate with "[Hs Hf]").
    + iFrame. repeat iSplit => //.
      iPureIntro.
      replace (Z.of_N (N.of_nat (length s) * 4))%Z with
        (length s * 4)%Z by lia.
      replace (length s * 4 - 4 * Z.of_N 0)%Z with
        (length s * 4)%Z in Hhj by lia.
      exact Hhj.
    + iIntros (w) "(%Hes & Hs & Hf)".
      destruct Hes as [es ->] => /=.
      rewrite (separate1 (AI_basic _)).
      replace ([AI_basic (BI_br 1)] ++ es) with
        ([] ++ [AI_basic (BI_br 1)] ++ es) => //.
      iApply wp_base_push => //.
      replace [AI_basic (BI_br 1)] with
        ([] ++ [AI_basic (BI_br 1)]) => //.
      iApply (wp_br_ctx with "Hf") => //.
      iIntros "!> Hf" => /=.
      iApply wp_value; first by instantiate (1 := immV []).
      iSplit; first done.
      iSplitL "HΨ Hs".
      * iExists s'. rewrite drop_0. iFrame.
      * iSplitL "Hf"; first by iExists f; iFrame.
        iFrame.
  - iIntros (j s' s f hj Hk).
    iIntros "(%Hloc0 & %Hloc1 & %Hloc2 & %Hloc3 & %Hhj & %Hlocs &
      %Hjbound & %Hlen & Hs & HΦ & HΨ & %Htypes & %Htab & Htab & Hcl &
      %Hclt & #Hspec & Hf & Hall)" => /=.
    have Hj : j = N.of_nat (S k) by lia. subst j.
    have Hsv : ∃ sv, s !! k = Some sv.
    { destruct (s !! k) eqn:Hlookup; first by eexists.
      apply lookup_ge_None in Hlookup. lia. }
    destruct Hsv as [sv Hsv].
    have Htake : take (S k) s = take k s ++ [sv].
    { by erewrite take_S_r. }
    rewrite Htake.
    iDestruct (stackAll_app with "HΦ") as "[HΦ Hlast]".
    iDestruct "Hlast" as "[HsvΦ _]".
    rewrite -Htake.
    iApply wp_ctx_bind => //.
    iApply (spec_map_loop_body_continue with
      "[Hs HsvΦ Htab Hcl Hf Hall]").
    + iFrame. repeat rewrite app_length take_length.
      replace (S k `min` length s) with (S k) by lia.
      replace (S k + length s') with (length s) by lia.
      instantiate (6 := N.of_nat k).
      repeat iSplit => //.
      * iPureIntro. replace
          (length s * 4 - 4 * Z.of_N (N.of_nat k) - 4)%Z with
          (length s * 4 - 4 * Z.of_N (N.of_nat (S k)))%Z by lia.
        exact Hhj.
      * iPureIntro. lia.
      * iPureIntro. rewrite lookup_app Nat2N.id.
        replace (take (S k) s !! k) with (Some sv) => //.
        rewrite lookup_take; last lia. symmetry; exact Hsv.
    + iIntros (w) "(-> & H)" => /=.
      iDestruct "H" as "(HsvΨ & Htab & Hcl & Hrest)".
      iDestruct "Hrest" as (hj') "(%Hhj' & Hf & Hall)".
      iDestruct "HsvΨ" as (sv') "[Hs HΨ']".
      replace [AI_basic (BI_br 0)] with
        ([] ++ [AI_basic (BI_br 0)]) => //.
      iApply (wp_br_ctx_nested with "Hf") => //; first lia.
      { by instantiate (1 := LH_rec [] 0 [] (LH_base [] []) []). }
      iIntros "!> Hf".
      rewrite -(app_nil_l [AI_basic (BI_loop _ _)]).
      iApply (wp_loop_ctx with "Hf") => //.
      iIntros "!> Hf".
      replace (cat [] (to_e_list map_loop_body)) with
        ([] ++ to_e_list map_loop_body ++ []) by done.
      iApply wp_label_push => //=.
      remember {| f_locs := <[2 := value_of_pointer hj']> f.(f_locs);
                  f_inst := f.(f_inst) |} as f'.
      replace (f_inst f) with (f_inst f') by (subst f'; done).
      iApply ("IHk" $! (N.of_nat k) (sv' :: s') s f' hj');
        first by iPureIntro; rewrite Nat2N.id.
      subst f'. iCombine "HΨ HΨ'" as "HΨall".
      iFrame.
      rewrite app_length take_length in Hhj'.
      have Hmin : S k `min` length s = S k by lia.
      rewrite Hmin in Hhj'.
      have Hnat : S k + length s' = length s by lia.
      have Hmin_k : k `min` length s = k by lia.
      repeat iSplit => //.
      * by rewrite list_lookup_insert_ne.
      * by rewrite list_lookup_insert_ne.
      * rewrite list_lookup_insert; last lia. iPureIntro. do 2 f_equal.
      * by rewrite list_lookup_insert_ne.
      * iPureIntro.
        rewrite Hnat in Hhj'.
        exact Hhj'.
      * rewrite insert_length. iPureIntro; lia.
      * iPureIntro.
        eapply N.le_trans; last exact Hjbound.
        lia.
      * iPureIntro. rewrite -Hnat. simpl. lia.
      * iSplitL "Hs".
        -- replace (<[_ := _]> _) with (take k s ++ sv' :: s').
           ++ done.
           ++ rewrite Htake insert_app_l.
              2: { rewrite app_length take_length Nat2N.id /=.
                   rewrite Hmin_k. lia. }
              rewrite insert_app_r_alt; last (rewrite take_length; lia).
              rewrite take_length Nat2N.id.
              rewrite Hmin_k.
              replace (k - k)%nat with 0 by lia.
              simpl.
              rewrite -app_assoc. done.
        -- iSplitL "HΨall".
           ++ have Hdrop : drop k s = sv :: drop (S k) s by erewrite drop_S.
              rewrite Hdrop => /=. iDestruct "HΨall" as "[$ $]".
           ++ repeat iSplit => //.
Qed.

Lemma spec_stack_map (f0 : frame) (fn : i32) (v : pointer)
      (s : seq.seq i32) E j0 a cl
      (Φ : i32 -> iPropI Σ) (Ψ : i32 -> i32 -> iPropI Σ) :
  ⊢ {{{ ⌜f0.(f_locs) !! 0 = Some (value_of_pointer v)⌝ ∗
         ⌜f0.(f_locs) !! 1 = Some (VAL_int32 fn)⌝ ∗
         ⌜length f0.(f_locs) >= 4⌝ ∗
         isStack v s ∗
         stackAll s Φ ∗
         ⌜f0.(f_inst).(inst_types) !! 3 =
           Some (Tf [T_i32] [T_i32])⌝ ∗
         ⌜f0.(f_inst).(inst_tab) !! 0 = Some j0⌝ ∗
         (N.of_nat j0) ↦[wt][N.of_nat
           (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
         (N.of_nat a) ↦[wf] cl ∗
         ⌜cl_type cl = Tf [T_i32] [T_i32]⌝ ∗
         (∀ (u : i32) (fc : frame),
           {{{ Φ u ∗ ⌜f_inst f0 = f_inst fc⌝ ∗ ↪[frame] fc ∗
               interp_allocator ∗
               (N.of_nat j0) ↦[wt][N.of_nat
                 (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
               (N.of_nat a) ↦[wf] cl }}}
           [AI_basic (BI_const (NVAL_int32 u)); AI_invoke a] @ E
           {{{ w, (∃ u', ⌜w = immV [VAL_int32 u']⌝ ∗ Ψ u u') ∗
                   ↪[frame] fc ∗ interp_allocator ∗
                   (N.of_nat j0) ↦[wt][N.of_nat
                     (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
                   (N.of_nat a) ↦[wf] cl }}}) ∗
         ↪[frame] f0 ∗ interp_allocator }}}
    to_e_list stack_map @ E
    {{{ w, ⌜w = immV []⌝ ∗
           (∃ s', isStack v s' ∗ stackAll2 s s' Ψ) ∗
           (∃ f1, ↪[frame] f1 ∗ ⌜f_inst f0 = f_inst f1⌝) ∗
           interp_allocator ∗
           (N.of_nat j0) ↦[wt][N.of_nat
             (Wasm_int.nat_of_uint i32m fn)] (Some a) ∗
           (N.of_nat a) ↦[wf] cl }}}.
Proof.
  iIntros "!>" (Ξ) "(%Hloc0 & %Hloc1 & %Hlocs & Hs & HΦ &
    %Htypes & %Htab & Htab & Hcl & %Hclt & #Hspec & Hf & Hall) HΞ" => /=.

  rewrite separate5.
  iApply wp_seq.
  iSplitR; last iSplitL "Hf Hs".
  2: { iApply (spec_map_initialise with "[$Hf $Hs]") => //.
       iIntros (w) "(-> & Hs & Hf)".
       instantiate (1 := λ w, (⌜w = immV []⌝ ∗ _)%I).
       iSplit => //.
       iCombine "Hs Hf" as "H".
       by iApply "H". }
  { by iIntros "(%Habs & _)". }

  iIntros (w) "(-> & Hs & Hf)" => /=.
  rewrite -(app_nil_l [AI_basic (BI_block _ _)]).
  iApply (wp_block with "Hf") => //.
  iIntros "!> Hf".
  iSimpl.
  iApply wp_wasm_empty_ctx.
  rewrite -(cat0s [AI_basic (BI_loop _ _)])
          -(cats0 [AI_basic (BI_loop _ _)]).
  iApply wp_label_push; first done.
  rewrite -(app_nil_l [AI_basic (BI_loop _ _)]).
  iApply (wp_loop_ctx with "Hf") => //.
  iIntros "!> Hf".
  simpl.
  rewrite -(cat0s (AI_basic (BI_get_local 2) :: _)).
  rewrite -(cats0 [AI_basic _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _]).
  iApply wp_label_push; first done.

  iApply (wp_wand_ctx with "[HΦ Htab Hcl Hs Hf Hall]").
  - iApply spec_map_loop_j.
    iFrame.
    repeat iSplit => /=.
    + rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite Hloc0.
    + rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite Hloc1.
    + rewrite list_lookup_insert; last by rewrite insert_length; lia.
      done.
    + rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert; last lia.
      done.
    + iPureIntro. instantiate (1 := N.of_nat (length s)).
      rewrite nat_N_Z Z.mul_comm Z.sub_diag.
      rewrite /pointer_arith Z.add_0_r.
      have Hnonneg : (0 <=? Z.of_N (ptr_addr v))%Z = true.
      { apply Z.leb_le. lia. }
      rewrite Hnonneg N2Z.id. by destruct v.
    + by repeat rewrite insert_length.
    + done.
    + instantiate (1 := []) => /=. iPureIntro. lia.
    + rewrite Nat2N.id firstn_all cats0.
      iFrame.
      rewrite drop_all.
      instantiate (1 := Ψ).
      by repeat iSplit => //.
  - done.
Qed.

End specs.
End stack.
