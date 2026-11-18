From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language. 
From iris.proofmode Require Import base tactics classes.
From iris.bi.lib Require Import fractional.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From CWasm.iriscwasm.helpers Require Import iris_properties.
From CWasm Require Import stdpp_aux color_ptr datatypes colored_memory common operations properties memory_list.
From CWasm.iriscwasm.language Require Export iris_locations iris iris_wp.

Import uPred.

Set Default Proof Using "Type".

Close Scope byte_scope.

Definition expr := iris.expr.
Definition val := iris.val.
Definition to_val := iris.to_val.

(* Defining a Wasm-specific WP with frame existence *)
Section wp_def.
  Context `{ HPB : PointerBytes }.

Canonical Structure wasm_lang := Language wasm_mixin.
 
Local Definition reducible := @reducible wasm_lang.

(* Implicit Type σ : state. *)

Class wasmG Σ :=
  WasmG {
      func_invG :: invGS Σ;
      func_gen_hsG :: gen_heapGS N function_closure Σ;

      tab_gen_hsG :: gen_heapGS (N*N) funcelem Σ;

      tabsize_hsG :: gen_heapGS N nat Σ;

      tablimit_hsG :: gen_heapGS N (option N) Σ;

      mem_gen_hsG :: gen_heapGS (N*N) byte Σ;

      memsize_gen_hsG :: gen_heapGS N N Σ;

      memlimit_hsG :: gen_heapGS N (option N) Σ;

      cmemGName : gname;

      cmem_gen_hsG :: ghost_mapG Σ N tagged_byte;

      allGName : gname;

      all_gen_hsG :: ghost_mapG Σ N (N * N);

      colorStatusGName : gname;

      retired_gen_hsG :: ghost_mapG Σ N bool;

      glob_gen_hsG :: gen_heapGS N global Σ;

      locs_gen_hsG :: ghost_mapG Σ unit frame;

      frameGName : gname
    }.

(* functor needed for NA invariants -- those used by the logical
relation have a separate name from general ones *)
Class logrel_na_invs Σ :=
  {
    logrel_na_invG :: na_invG Σ;
    logrel_nais : na_inv_pool_name
  }.

Definition proph_id := positive. 


Instance eqdecision_frame: EqDecision frame.
Proof. intros x y. destruct x, y.
       assert (Decision (f_locs = f_locs0)); first decidable_equality.
       assert (Decision (f_inst = f_inst0)).
       2:{ destruct H, H0; try by right; intros Habs; inversion Habs; subst.
           by subst; left. }
       destruct f_inst, f_inst0.
       assert (Decision (inst_types = inst_types0)); first decidable_equality.
       assert (Decision (inst_funcs = inst_funcs0)); first decidable_equality.
       assert (Decision (inst_tab = inst_tab0)); first decidable_equality.
       assert (Decision (inst_memory = inst_memory0)); first decidable_equality.
       assert (Decision (inst_globs = inst_globs0)); first decidable_equality.
       destruct H0, H1, H2, H3, H4; try by right; intros Habs; inversion Habs; subst.
       subst; by left.
Qed.




Definition gen_heap_wasm_store `{!wasmG Σ} (s: store_record) : iProp Σ :=
  ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
   (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
   (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
   (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
   (gen_heap_interp (gmap_of_list (fmap operations.mem_length s.(s_mems)))) ∗
   (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
   (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
   (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt s.(s_tables)))))%I.



Global Instance heapG_irisG `{!wasmG Σ} : irisGS wasm_lang Σ := {
  iris_invGS := func_invG; 
  state_interp σ _ κs _ :=
    let: (s, locs, inst) := σ in
     ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (ghost_map_auth cmemGName 1 (gmap_of_cmem s.(s_cmems) s.(s_alls))) ∗
      (ghost_map_auth allGName 1 (gmap_of_allocator s.(s_cmems) s.(s_alls))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth frameGName 1 (<[ tt := Build_frame locs inst ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap operations.mem_length s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
      (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
      (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt s.(s_tables)))) ∗
      (ghost_map_auth colorStatusGName 1 (gmap_of_retired s.(s_alls))) ∗
      ⌜ wellFormedState s ⌝
     )%I;
    num_laters_per_step _ := 0;
    fork_post _ := True%I;
    state_interp_mono s0 _ _ _ := fupd_intro _ _
  }. 




End wp_def.


(* Resource ownerships *)
Notation "n ↦[wf]{ q } v" := (pointsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (pointsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wt]{ q } [ i ] v" := (pointsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (pointsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                           (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↪[wtsize] m" := (pointsto (L:=N) (V:=nat) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtsize] m") : bi_scope.
Notation "n ↪[wtlimit] m" := (pointsto (L:=N) (V:=option N) (hG:=tablimit_hsG) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtlimit] m") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (pointsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (pointsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (pointsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↪[wmlimit] v" := (pointsto (L:=N) (V:=option N) (hG:=memlimit_hsG) n (DfracDiscarded) v% V)
                               (at level 20, format "n ↪[wmlimit] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (pointsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v").
Notation "n ↦[wg] v" := (pointsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") .
Notation " ↪[frame]{ q } v" := (ghost_map_elem frameGName tt q v%V)
                           (at level 20, q at level 5, format " ↪[frame]{ q } v") .
Notation " ↪[frame] v" := (ghost_map_elem frameGName tt (DfracOwn 1) v%V)
                           (at level 20, format " ↪[frame] v").




(* Predicates for memory blocks and whole tables *)  
Definition mem_block `{!wasmG Σ} (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] operations.mem_length m ∗ n ↪[wmlimit] (mem_max_opt m))%I.

Definition mem_block_at_pos `{!wasmG Σ} (n: N) (l:bytes) k :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm][ (N.of_nat (N.to_nat k+i)) ] b)%I.

Definition cmem_block `{!wasmG Σ} (s: cmem) :=
  (([∗ list] i ↦ b ∈ (s.(cmem_data).(cml_data)), ghost_map_elem cmemGName (N.of_nat i) (DfracOwn 1) b ))%I.

Definition cmem_block_at_pos `{!wasmG Σ} (l:list tagged_byte) k :=
  ([∗ list] i ↦ b ∈ l, ghost_map_elem cmemGName (N.of_nat (N.to_nat k+i)) (DfracOwn 1) b)%I.

Notation "a ↦[wc]{ col }{ tag } b" :=
  (ghost_map_elem cmemGName a (DfracOwn 1)
    {| tb_value := b; tb_color := Some col; tb_tag := tag |})
  (at level 20, format "a ↦[wc]{ col }{ tag } b"): bi_scope.

Definition wcs `{!wasmG Σ} (addr : N) (col : N) (tag : btag) (bs : list byte) : iProp Σ :=
  [∗ list] i ↦ b ∈ bs,
  (N.of_nat (N.to_nat addr + i)) ↦[wc]{ col }{ tag } b.

Definition wall `{!wasmG Σ} (c base size : N) : iProp Σ :=
  ghost_map_elem allGName c (DfracOwn 1) (base, size).

Definition live_color_frac `{!wasmG Σ} (c : N) (q : Qp) : iProp Σ :=
  ghost_map_elem colorStatusGName c (DfracOwn q) true.

Definition live_color `{!wasmG Σ} (c : N) : iProp Σ :=
  live_color_frac c 1%Qp.

Definition dead_color `{!wasmG Σ} (c : N) : iProp Σ :=
  ghost_map_elem colorStatusGName c DfracDiscarded false.

Global Instance dead_color_persistent `{!wasmG Σ} (c : N) :
  Persistent (dead_color c).
Proof. apply _. Qed.

Definition retired_auth `{!wasmG Σ} (a : allocator) : iProp Σ :=
  ghost_map_auth colorStatusGName 1 (gmap_of_retired a).

Global Instance live_color_frac_fractional `{!wasmG Σ} (c : N) :
  Fractional (live_color_frac c).
Proof. apply _. Qed.

Lemma live_color_halves `{!wasmG Σ} (c : N) :
  live_color_frac c (1/2)%Qp -∗ live_color_frac c (1/2)%Qp -∗
  live_color c.
Proof.
  iIntros "Hleft Hright".
  iCombine "Hleft Hright" as "Hlive".
  iExact "Hlive".
Qed.

Lemma live_color_frac_dead `{!wasmG Σ} (c : N) (q : Qp) :
  live_color_frac c q -∗ dead_color c -∗ False.
Proof.
  iIntros "Hlive Hdead".
  iDestruct (ghost_map_elem_agree with "Hlive Hdead") as %Hfalse.
  done.
Qed.

Lemma live_color_full_exclusive_frac `{!wasmG Σ} (c : N) (q : Qp) :
  live_color c -∗ live_color_frac c q -∗ False.
Proof.
  iIntros "Hlive Hother".
  iDestruct (ghost_map_elem_combine with "Hlive Hother") as "[Hboth _]".
  iDestruct (ghost_map_elem_valid with "Hboth") as %Hvalid.
  apply dfrac_valid_own_l in Hvalid. done.
Qed.

Lemma live_color_dead `{!wasmG Σ} (c : N) :
  live_color c -∗ dead_color c -∗ False.
Proof.
  iApply live_color_frac_dead.
Qed.

Lemma live_color_exclusive `{!wasmG Σ} (c : N) :
  live_color c -∗ live_color c -∗ False.
Proof.
  iApply live_color_full_exclusive_frac.
Qed.

Definition wblock `{!wasmG Σ} (addr : N) (tbs : list tagged_byte) : iProp Σ :=
  [∗ list] i ↦ tb ∈ tbs, ghost_map_elem cmemGName (N.of_nat (N.to_nat addr + i)) (DfracOwn 1) tb.

Definition tab_block `{!wasmG Σ} (n: N) (tab: tableinst) :=
  (([∗ list] i ↦ tabelem ∈ (tab.(table_data)), n ↦[wt][ (N.of_nat i) ] tabelem ) ∗
     (n ↪[wtsize] (tab_size tab)) ∗ (n ↪[wtlimit] (table_max_opt tab)))%I.

Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.

Notation " ↦[wsblock] s" := (cmem_block s)
                              (at level 20, format " ↦[wsblock] s"): bi_scope.
Notation " ↦[wcs][ i ] l" := (cmem_block_at_pos l i)
                               (at level 20, format " ↦[wcs][ i ] l"): bi_scope.

Notation "a ↦[wcs]{ col }{ tag } bs" := (wcs a col tag bs)
  (at level 20, format "a ↦[wcs]{ col }{ tag } bs"): bi_scope.
Notation "c ↣[wall]{ base }{ size }" := (wall c base size)
  (at level 20, format "c ↣[wall]{ base }{ size }"): bi_scope.
Notation "a ↦[wblock] tbs" := (wblock a tbs)
  (at level 20, format "a ↦[wblock] tbs"): bi_scope.


Notation "n ↦[wtblock] t" := (tab_block n t)
                           (at level 20, format "n ↦[wtblock] t"): bi_scope.

Definition mem_equiv (m1 m2: memory): Prop :=
  m1.(mem_max_opt) = m2.(mem_max_opt) /\
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Lemma mem_equiv_wmblock_rewrite `{!wasmG Σ} (m1 m2: memory) n:
  mem_equiv m1 m2 ->
  (n ↦[wmblock] m1)%I ≡ (n ↦[wmblock] m2)%I.
Proof.
  unfold mem_equiv, mem_block.
  destruct m1, m2.
  destruct mem_data, mem_data0 => //=.
  by move => [-> ->] => //.
Qed.

Definition cmem_equiv (s1 s2: cmem) : Prop :=
    s1.(cmem_data).(cml_data) = s2.(cmem_data).(cml_data).

Lemma cmem_equiv_wsblock_rewrite `{!wasmG Σ} (s1 s2: cmem):
  cmem_equiv s1 s2 ->
  ( ↦[wsblock] s1)%I ≡ ( ↦[wsblock] s2)%I.
Proof.
  unfold cmem_equiv, cmem_block.
  destruct s1, s2.
  destruct cmem_data, cmem_data0 => //=.
  by intros ->.
Qed.

Lemma wblock_nil `{!wasmG Σ} (a : N) : (a ↦[wblock] [::])%I ⊣⊢ emp%I.
Proof.
  rewrite /wblock. by rewrite big_sepL_nil.
Qed.

Lemma wblock_cons `{!wasmG Σ} (a : N) (tb : tagged_byte) (tbs : list tagged_byte) :
  (a ↦[wblock] (tb :: tbs))%I ⊣⊢
  (ghost_map_elem cmemGName a (DfracOwn 1) tb ∗ (a + 1) ↦[wblock] tbs)%I.
Proof.
  rewrite /wblock. rewrite big_sepL_cons.
  apply bi.sep_proper.
  - rewrite Nat.add_0_r. rewrite N2Nat.id. done.
  - apply big_sepL_proper. intros i x Hx.
    assert (N.of_nat (N.to_nat a + S i) =
            N.of_nat (N.to_nat (a + 1) + i)) as ->; [lia|done].
Qed.

Lemma wblock_app `{!wasmG Σ} (a : N) (l1 l2 : list tagged_byte) :
  (a ↦[wblock] (l1 ++ l2))%I ⊣⊢
  (a ↦[wblock] l1 ∗ (a + N.of_nat (length l1)) ↦[wblock] l2)%I.
Proof.
  rewrite /wblock. rewrite big_sepL_app.
  apply bi.sep_proper; [done|].
  apply big_sepL_proper. intros i x Hx.
  assert (N.of_nat (N.to_nat a + (length l1 + i)) =
          N.of_nat (N.to_nat (a + N.of_nat (length l1)) + i)) as ->;
    [lia|done].
Qed.

Lemma wcs_wblock `{!wasmG Σ} (a : N) (col : N) (tag : btag) (bs : list byte) :
  (a ↦[wcs]{ col }{ tag } bs)%I ⊣⊢
  a ↦[wblock] (map (fun b => {| tb_value := b; tb_color := Some col; tb_tag := tag |}) bs).
Proof.
  rewrite /wcs /wblock big_sepL_fmap. done.
Qed.

Lemma wblock_wcs `{!wasmG Σ} (a : N) (col : N) (tag : btag) (bs : list byte) :
  (a ↦[wblock] (map (fun b => {| tb_value := b; tb_color := Some col; tb_tag := tag |}) bs))%I ⊣⊢
  a ↦[wcs]{ col }{ tag } bs.
Proof.
  by rewrite wcs_wblock.
Qed.




Section Wasm_wp.
  Context `{!wasmG Σ}.
  Context `{HPB : PointerBytes}.


  Global Instance wp_wasm : Wp (iProp Σ) (expr) (val) stuckness.
  Proof using Σ wasmG0 HPB.
    eapply wp'. Unshelve. exact frame. exact (λ f,  ↪[frame] f)%I. Defined.



(* A Definition of a context dependent WP for WASM expressions *)

Definition wp_wasm_ctx `{!wasmG Σ}
          (s : stuckness) (E : coPset) (e : language.expr wasm_lang)
           (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ WP LI @ s; E {{ Φ }}.


Definition wp_wasm_frame `{!wasmG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  
  WP [AI_local n f es] @ s; E {{ Φ }}.

Definition wp_wasm_ctx_frame `{!wasmG Σ}
          (s : stuckness) (E : coPset) (es : language.expr wasm_lang)
          (Φ : val -> iProp Σ) (n: nat) (f: frame) (i : nat) (lh : lholed) : iProp Σ :=
  
  ∀ LI, ⌜lfilled i lh es LI⌝ -∗ WP [AI_local n f LI] @ s; E {{ Φ }}.
End Wasm_wp.

(* Notations *)

(* Context wps for blocks *)
Notation "'WP' e @ s ; E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx s E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck E e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ Φ } }" := (wp_wasm_ctx NotStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ Φ } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ Φ } }" := (wp_wasm_ctx s E e%E Φ 0 (LH_base [] []))
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.


Notation "'WP' e @ s ; E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx s E e%E (λ v, Q) 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck E e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx NotStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx MaybeStuck ⊤ e%E (λ v, Q) i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Frame wps for Local *)

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ Φ } }" := (wp_wasm_frame s E e%E Φ n f)
  (at level 20, only parsing) : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f {{ v , Q } }" := (wp_wasm_frame s E e%E (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
    format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ s ; E 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q } }" := (wp_wasm_ctx_frame s E e%E (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' s ;  '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @ '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e @ E 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck E e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' @  '[' E  '/' ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (wp_wasm_ctx_frame NotStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP' e 'FRAME' n ; f 'CTX' i ; lh ? {{ v , Q } }" := (wp_wasm_ctx_frame MaybeStuck ⊤ e%E (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'WP'  e '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' ? {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* Tactics *)
Ltac only_one_reduction H :=
  let Hstart := fresh "Hstart" in
  let a := fresh "a" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in 
  eapply reduce_det in H
      as [H | [ [i0 Hstart] | [[i0 Hstart] | (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]] ;
  last (by repeat econstructor; try rewrite const_const) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart; try rewrite first_instr_instr_const in Hstart) ; inversion Hstart.
