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

  Context `{!wasmG Σ, !logrel_na_invs Σ, HPB : PointerBytes,
      cancelg : cancelG Σ, !cinvG Σ}.
  Set Bullet Behavior "Strict Subproofs".

  (* --------------------------------------------------------------------------------------- *)
  (* -------------------------------------- EXPRESSIONS ------------------------------------ *)
  (* --------------------------------------------------------------------------------------- *)

  (* ----------------------------------------- COLALLOC ------------------------------------ *)
  (* Port of MSWasm `iris_fundamental_segalloc.v` (`typing_segalloc`).  On
     failure, [wp_colalloc] returns a null, colourless pointer whose
     [pointer_interp] follows from [pointer_interp_null]; on success the
     fresh-colour resources ([wall col], [live_color col], [wcs]) are combined
     into a [▷ pointer_allocation_body] and published to the allocator
     through `interp_allocator_publish_full` (iris_logrel.v), which registers the
     new world entry for the resulting [Hall]. *)
  Lemma typing_colalloc C :
    ⊢ semantic_typing C (to_e_list [BI_colalloc])
        (Tf [T_i32] [T_pointer]).
  Proof.
    unfold semantic_typing, interp_expression.
    iIntros (i lh hl).
    iIntros "#Hi [%Hlh_base [%Hlh_len [%Hlh_valid #Hcont]]]"
      (f vs) "[Hf Hfv] Hall #Hv".
    iDestruct "Hv" as "[-> | Hv]".
    { take_drop_app_rewrite_twice 0 1.
      iApply (wp_wand _ _ _ (λ vs0, ⌜vs0 = trapV⌝ ∗ ↪[frame] f)%I
        with "[Hf]").
      { iApply (wp_trap with "[] [$]"); auto. }
      iIntros (v0) "[? ?]". iFrame. iExists _. iFrame "∗ #". }
    iDestruct "Hv" as (ws ->) "Hv".
    iDestruct (big_sepL2_length with "Hv") as %Hlen.
    destruct ws as [|w ws]; [done|destruct ws; [|done]].
    iSimpl in "Hv". iDestruct "Hv" as "(Hv & _)".
    iDestruct "Hv" as (z) "->".

    iSimpl.
    iApply wp_fupd.
    iApply (wp_wand with "[Hf]").
    { iApply (wp_colalloc with "[$Hf]") => //.
      iIntros "!>" (w) "H". iExact "H". }
    iIntros (v) "[(%p & Hwp) Hf]".
    iDestruct "Hwp" as "[-> Hwp]".
    iDestruct "Hwp" as "[%Hisnull | Hcol]".
    - (* allocation failed: the returned pointer is the null, colourless one *)
      iSplitR "Hf Hfv Hall".
      + iLeft; iRight. iExists _. iModIntro. iSplit; first done. iSplit; last done.
         
        iExists _. iSplit; first done.
        iApply (pointer_interp_null p). apply/eqP. exact Hisnull.
      + iExists _. iModIntro. iFrame.
    - (* allocation succeeded: [p] has a fresh colour [col] *)
      iDestruct "Hcol" as (col) "[%Hcol Hrest]".
      iDestruct "Hrest" as "[%Hfreeable Hrest]".
      iDestruct "Hrest" as "(Hwall & Hlive & Hwcs)".
      set (sz := Wasm_int.N_of_uint i32m z).
      set (bs := repeat #00%byte (N.to_nat sz)).
      set (tbs := map (fun b : byte => {| tb_value := b; tb_color := Some col;
                          tb_tag := Numeric |}) bs).
      set (base := alloc_result_base (ptr_addr p) sz).
      iAssert (▷ pointer_allocation_body pointer_interp col base sz)%I
        with "[Hwall Hwcs]" as "Hbody".
      { iExists tbs.
        iSplit.
        - iPureIntro. rewrite /tbs /bs map_length repeat_length.
          by apply N2Nat.id.
        - iSplit.
          + iPureIntro. rewrite /tbs all_map.
            apply/allP => b _; simpl; apply/eqP; reflexivity.
          + iFrame "Hwall".
            iAssert (wblock base tbs)%I with "[Hwcs]" as "Hwblock".
            { destruct (N.eqb sz 0%N) eqn:Hsz0.
              - apply N.eqb_eq in Hsz0. subst sz.
                rewrite /base /alloc_result_base /tbs /bs Hsz0. simpl.
                rewrite /wblock. simpl. done.
              - have Hbase' : base = ptr_addr p.
                { rewrite /base /alloc_result_base Hsz0.  done. }
                rewrite Hbase' /tbs /bs -wcs_wblock. iExact "Hwcs". }
            iFrame "Hwblock".
            iApply (pointer_slots_numeric pointer_interp base tbs).
            rewrite /tbs all_map.
            apply/allP => b _; simpl; apply/eqP; reflexivity. }
      iMod (interp_allocator_publish_full col base sz with "Hlive Hbody Hall")
        as (γ) "[#Hreg [#Hinv Hall]]".
      iSplitR "Hf Hfv Hall".
      + iLeft; iRight. iExists _. iModIntro. iSplit; first done. iSplit; last done.
         
        iExists _. iSplit; first done.
        rewrite pointer_interp_unfold /pointer_interp_pre.
        iRight. iExists col, (PointerRegistration γ base sz 1%Qp).
        iSplit; first done.
        iFrame "Hreg". iSplit; first iExact "Hinv". done.
      + iExists _. iModIntro. iFrame.
  Qed.

End fundamental.
