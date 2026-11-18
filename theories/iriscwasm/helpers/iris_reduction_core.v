From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From CWasm.iriscwasm.language.iris Require Import iris.
From CWasm Require Import stdpp_aux operations colored_memory opsem properties.
From CWasm.iriscwasm.helpers.prelude Require Import iris_lfilled_properties iris_wasm_lang_properties.
From CWasm.iriscwasm.helpers.lfill_prelude Require Import lfill_prelude.
From CWasm.iriscwasm.helpers Require Export iris_reduce_properties.


Ltac first_not_const Hconst :=
  unfold const_list, forallb in Hconst ;
  subst ; simpl in Hconst ;
  repeat rewrite andb_false_r in Hconst ;
  false_assumption.


Section reduction_core.
  Context `{ HPB : PointerBytes }.
  Let reducible := @iris.program_logic.language.reducible wasm_lang.
  
  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.


  Lemma reduction_core bef0 es0 aft0 bef1 es1 aft1 es0' es1' me0 s f me1 s' f' s0 f0 :
    reduce s f es0 me0 s0 f0 es0' ->
    reduce s f es1 me1 s' f' es1' ->
    const_list bef0 ->
    const_list bef1 ->
    bef0 ++ es0 ++ aft0 = bef1 ++ es1 ++ aft1 ->
    (exists core bc0 ac0 bc1 ac1 core',
        const_list bc0 /\
          const_list bc1 /\
          es0 = bc0 ++ core ++ ac0 /\
          es1 = bc1 ++ core ++ ac1 /\
          bef0 ++ bc0 = bef1 ++ bc1 /\
          ac0 ++ aft0 = ac1 ++ aft1 /\
          reduce s f core me1 s' f' core' /\
          bc1 ++ core' ++ ac1 = es1') \/
      exists lh0 lh1, lfilled 0 lh0 [AI_trap] es0 /\ lfilled 0 lh1 [AI_trap] es1 /\
                   (s,f) = (s', f') /\ me1 = Eempty.
  Proof.
    intros Hred0 Hred1 Hbef0 Hbef1 Heq.
    cut (forall nnnn, length es1 < nnnn ->
                 (∃ core bc0 ac0 bc1 ac1 core',
                     const_list bc0
                     ∧ const_list bc1
                     ∧ es0 = bc0 ++ core ++ ac0
                     ∧ es1 = bc1 ++ core ++ ac1
                     ∧ bef0 ++ bc0 = bef1 ++ bc1
                     ∧ ac0 ++ aft0 = ac1 ++ aft1
                     ∧ reduce s f core me1 s' f' core' ∧ bc1 ++ core' ++ ac1 = es1')
                 ∨ (∃ lh0 lh1 : lholed, lfilled 0 lh0 [AI_trap] es0 ∧ lfilled 0 lh1 [AI_trap] es1 /\ (s,f) = (s',f') /\ me1 = Eempty)).
(* discharge size-bounded cut *)
    { intro Hn ; eapply (Hn (S (length es1))) ; lia. }
    intro nnnn.
    generalize dependent es1.
    generalize dependent es1'.
    generalize dependent es0.
    generalize dependent es0'.
    generalize dependent bef1.
    generalize dependent aft1.
    induction nnnn.
    intros ; lia.
    intros aft1 bef1 Hbef1 es0' es0 Hred0 es1' es1 Hred1 Heq Hlen.
    edestruct first_non_value_reduce as (vs0 & e0 & afte0 & Hvs0 & He0 & Heq0) ;
      try exact Hred0.
    rewrite Heq0 in Heq.
    induction Hred1 as [ | ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8 
                       | ? ? ? ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8 Hr9 Hr10 Hr11 Hr12 
                       | ? ? ? ? ? ? Hr1 Hr2 Hr3 
                       | ? ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8 
                       | ? ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8 Hr9 
                       | ? ? ? ? ? ? ? Hr1 Hr2 Hr3 
                       | ? ? ? ? aaa ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 
                       | ? ? ? ? ? Hr1 Hr2 
                       | ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 
                       | ? ? ? ? ? Hr1 Hr2 Hr3 
                       | ? ? ? ? ? ? ? ? ? ? ? Hr1 IHHred Hr2 Hr3 |
                         ? ? ? ? ? ? ? ? ? Hr IHHred ];
        try (by left ; do 2 rewrite app_assoc in Heq ;
           rewrite - (app_assoc ( _ ++ _)) in Heq ;
           rewrite - app_comm_cons in Heq ;
           apply first_values in Heq as (<- & -> & <-) ;try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
           try (destruct He0 as [-> | ->]; by intros [? ?]) ;
           try (by const_list_app; repeat rewrite const_const) ;
           rewrite separate1 in Heq0 ;
           eexists _, vs0, afte0, [], [], _ ;
           repeat split ; try done ; try (by rewrite app_nil_r) ;
               by econstructor);
      try (by left ; rewrite (separate1 (AI_const _)) in Heq ;
           repeat rewrite app_assoc in Heq ;
           repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
           rewrite - app_comm_cons in Heq ;
           apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
           try (destruct He0 as [-> | ->]; by intros [? ?]);
           try (by const_list_app; repeat rewrite const_const) ;
           destruct vs0 ;
           [ simpl in Heq0 ;
             exfalso ;
             apply Logic.eq_sym in Heq0 ;
             clear Hafts ;
             generalize dependent afte0 ;
             induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
             try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                  assert (const_list (a0 :: ves)) as Hconst ;
                  first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                  first_not_const Hconst) ;
             [  destruct H ; try (by inversion Heq0) ;
                 try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                     assert (const_list (a0 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                destruct H ; try (by inversion Heq0) ;
                 try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
             try (by destruct vs ; inversion Heq0 ;
                  first_not_const H) ; 
             try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
             (* try (by inversion Heq0 ; subst ; destruct He0 ; [simpl; false_assumption | discriminate]) ; *)
             unfold lfilled, lfill in H0 ;
             destruct lh as [bef aft |] ; last (by false_assumption) ;
             destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
             move/eqP in H0 ;
             rewrite H0 in Heq0 ; 
             destruct bef ; inversion Heq0 ;
             first_not_const Hbef
             | rewrite - Heq0 in H ;
               simple_filled2 H k lh bef aft nn ll ll' ;
               [ destruct bef ;
                 [ destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0
                 | inversion H ;
                   first_not_const Hvs ]
               | destruct bef ; inversion H ;
                 first_not_const Hvs ]]
           | get_tail a vs0 ys y Htail ;
             rewrite Htail in Hbefs ;
             repeat rewrite catA in Hbefs ;
             apply app_inj_tail in Hbefs as [Hbefs ->] ;
             rewrite Htail in Heq0 ;
             rewrite - app_assoc in Heq0 ;
             rewrite - separate1 in Heq0 ;
             rewrite separate2 in Heq0 ;
             eexists _, ys, afte0, [], [], _ ;
             repeat split ; try done ; try (by rewrite app_nil_r) ;
             [ rewrite Htail in Hvs0 ;
               unfold const_list in Hvs0 ;
               rewrite forallb_app in Hvs0 ;
               apply andb_true_iff in Hvs0 as [Hys _] ;
                 by unfold const_list 
             | by econstructor ]]) ;
      try by (left ; rewrite separate2 in Heq ;
              repeat rewrite app_assoc in Heq ;
              repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
              rewrite - app_comm_cons in Heq ;
              apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]);
              try (by const_list_app; repeat rewrite const_const) ;
              destruct vs0 ;
              [ simpl in Heq0 ;
                exfalso ;
                apply Logic.eq_sym in Heq0 ;
                clear Hafts ;
                generalize dependent afte0 ;
                induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                 try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                     assert (const_list (a0 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                [  destruct H; try (by inversion Heq0) ;
                    try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                     assert (const_list (a0 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                   destruct H ; try (by inversion Heq0) ;
                    try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                  try (by destruct vs ; inversion Heq0 ;
                       first_not_const H) ; 
                  try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                  unfold lfilled, lfill in H0 ;
                  destruct lh as [bef aft |] ; last (by false_assumption) ;
                  destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                  move/eqP in H0 ;
                  rewrite H0 in Heq0 ; 
                  destruct bef ; inversion Heq0 ;
                  first_not_const Hbef
                | rewrite - Heq0 in H ;
                  simple_filled2 H k lh bef aft nn ll ll' ;
                  [ destruct bef ;
                    [ destruct es ; first empty_list_no_reduce ;
                      inversion H ; subst ;
                        by eapply IHHred0
                    | inversion H ;
                      first_not_const Hvs ]
                  | destruct bef ; inversion H ;
                    first_not_const Hvs ]]
              |] ;
              destruct vs0 ;
              [ exfalso ;
                clear Hafts ;
                generalize dependent afte0 ;
                induction Hred0 ; intros afte0 Heq0 ; 
                try (by inversion Heq0) ;
                 try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                     destruct ves as [| b1 ves] ; inversion Heq0 ;
                     assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                [  destruct H;
                   try (by inversion Heq0) ;
                    try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                     destruct ves as [| b1 ves] ; inversion Heq0 ;
                     assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                   destruct H ;
                   try (by inversion Heq0) ;
                    try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                  try (by destruct vs ; first (by inversion Heq0) ;
                       destruct vs ; inversion Heq0 ;
                       first_not_const H) ;
                  unfold lfilled, lfill in H0 ;
                  destruct lh as [bef aft |] ; last (by false_assumption) ;
                  destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                  move/eqP in H0 ; 
                  rewrite H0 in Heq0 ;
                  destruct bef ; 
                  inversion Heq0 ; subst ;
                  inversion Hvs0 ; 
                  destruct bef ; inversion Heq0 ;
                  first_not_const Hbef 
                | rewrite Heq0 in H ;
                  simple_filled2 H k lh bef aft nn ll ll' ;
                  [ destruct bef ;
                    [ destruct es ; first empty_list_no_reduce ;
                      destruct es ; inversion H ; subst ;
                      [ values_no_reduce 
                      | by eapply IHHred0 ]
                    | destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ;
                        remember (a1 :: es) as es0 ;
                        subst a1 ;
                        clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                        generalize dependent es ;
                        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                         try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                        try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                             assert (const_list (b0 :: ves)) as Hconst ;
                             first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                             first_not_const Hconst) ;
                        [   destruct H; try (by inversion Heq0) ;
                             try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                        try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                             assert (const_list (b0 :: ves)) as Hconst ;
                             first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                             first_not_const Hconst) ;
                            destruct H ; try (by inversion Heq0) ;
                             try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                          try (by destruct vs ; inversion Heq0 ;
                               first_not_const H) ; 
                          try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                          unfold lfilled, lfill in H0 ;
                          destruct lh as [bef aft |] ; last (by false_assumption) ;
                          destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                          move/eqP in H0 ;
                          rewrite H0 in Heq0 ; 
                          destruct bef ; inversion Heq0 ;
                          first_not_const Hbef
                        | rewrite Heq0 in H ;
                          simple_filled2 H k lh bef aft nn ll ll' ;
                          [ destruct bef ;
                            [ destruct es ; first empty_list_no_reduce ;
                              inversion H ; subst ;
                                by eapply IHHred0
                            | inversion H ;
                              first_not_const Hvs ]
                          | destruct bef ; inversion H ;
                            first_not_const Hvs ]]
                      | inversion H ;
                        first_not_const Hvs ]]
                  | destruct bef ; inversion H ;
                    subst ; inversion Hvs0 ;
                    destruct bef ; inversion H ;
                    first_not_const Hvs ]] 
              | get_tail a0 vs0 ys y Htail ;
                rewrite Htail in Hbefs ;
                rewrite app_comm_cons in Hbefs ;
                get_tail a ys ys' y' Htail' ;
                rewrite Htail' in Hbefs ;
                rewrite (separate1 (AI_const _)) in Hbefs ;
                repeat rewrite catA in Hbefs ;
                rewrite assoc_list_seq in Hbefs ;
                apply app_inj_tail in Hbefs as [Hys' ->] ;
                apply app_inj_tail in Hys' as [Hys ->] ;
                rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
                - separate1 separate3 in Heq0 ;
                eexists _, ys', afte0, [], [], _ ;
                repeat split ; try done ; try (by rewrite app_nil_r) ;
                [ rewrite Htail app_comm_cons Htail' in Hvs0 ;
                  unfold const_list in Hvs0 ;
                  repeat rewrite forallb_app in Hvs0 ;
                  repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
                  done
                | by econstructor]]) .
(* destruct first non-value (heavy cases) *)
    { destruct H as [ | ? ? ? aaa Hr | ? ? ? aaa ? ? Hr1 Hr2 Hr3 |
                         ? ? ? aaa ? ? Hr1 Hr2 Hr3 | ? ? ? ? Hr |
                         aaa ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6
                             Hr7 Hr8 Hr9 Hr10 |
                         aaa ? ? ? ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 |

                         ? ? ? ? Hr | ? ? ? ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? Hr | ? ? ? ? ? Hr | ? ? ? ? ? kkk aaa ? ? Hr1 Hr2 Hr3 Hr4 |
                         ? ? ? ? kkk aaa ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? kkk aaa ? ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? kkk aaa ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? ? kkk aaa ? ? Hr1 Hr2 Hr3 Hr4 |
                         ? ? ? ? ? ? kkk ? aaa Hr1 Hr2 Hr3 Hr4 |
                         ? ? ? ? ? ? kkk ? aaa ? ? Hr1 Hr2 Hr3 Hr4 |
                         ? ? ? ? ? ? kkk ? aaa ? Hr1 Hr2 Hr3 Hr4 | ? ? ? ? ? Hr1 Hr2 Hr3 |
                         ? ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 | ? ? ? ? ? ? Hr1 Hr2 Hr3 ];
      try (by left ; do 2 rewrite app_assoc in Heq ;
           rewrite - (app_assoc ( _ ++ _)) in Heq ;
           rewrite - app_comm_cons in Heq ;
           apply first_values in Heq as (<- & -> & <-) ;try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
           try (destruct He0 as [-> | ->]; by intros [? ?]) ;
           try (by const_list_app; repeat rewrite const_const) ;
           rewrite separate1 in Heq0 ; 
           eexists _, vs0, afte0, [], [], _;
           repeat split ; try done ; try (by rewrite app_nil_r) ;
             by econstructor; econstructor);
  try (by left ; rewrite (separate1 (AI_const _)) in Heq ;
           repeat rewrite app_assoc in Heq ;
           repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
           rewrite - app_comm_cons in Heq ;
           apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
           try (destruct He0 as [-> | ->]; by intros [? ?]);
           try (by const_list_app; repeat rewrite const_const) ;
           destruct vs0 ;
           [ simpl in Heq0 ;
             exfalso ;
             apply Logic.eq_sym in Heq0 ;
             clear Hafts ;
             generalize dependent afte0 ;
             induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
             try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                  assert (const_list (a0 :: ves)) as Hconst ;
                  first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                  first_not_const Hconst) ;
             [   destruct H ; try (by inversion Heq0) ;
                  try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                 try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                      assert (const_list (a0 :: ves)) as Hconst ;
                      first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                      first_not_const Hconst) ;
                 destruct H ; try (by inversion Heq0) ;
                 try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef
             | rewrite - Heq0 in H ;
               simple_filled2 H k lh bef aft nn ll ll' ;
               [ destruct bef ;
                 [ destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0
                 | inversion H ;
                   first_not_const Hvs ]
               | destruct bef ; inversion H ;
                 first_not_const Hvs ]]
           | get_tail a vs0 ys y Htail ;
             rewrite Htail in Hbefs ;
             repeat rewrite catA in Hbefs ;
             apply app_inj_tail in Hbefs as [Hbefs ->] ;
             rewrite Htail in Heq0 ;
             rewrite - app_assoc in Heq0 ;
             rewrite - separate1 in Heq0 ;
             rewrite separate2 in Heq0 ;
             eexists _, ys, afte0, [], [], _;
             repeat split ; try done ; try (by rewrite app_nil_r) ;
             [ rewrite Htail in Hvs0 ;
               unfold const_list in Hvs0 ;
               rewrite forallb_app in Hvs0 ;
               apply andb_true_iff in Hvs0 as [Hys _] ;
                 by unfold const_list 
             | by econstructor; econstructor ]]) ;
      try by (left ; rewrite separate2 in Heq ;
              repeat rewrite app_assoc in Heq ;
              repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
              rewrite - app_comm_cons in Heq ;
              apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]);
              try (by const_list_app; repeat rewrite const_const) ;
              destruct vs0 ;
              [ simpl in Heq0 ;
                exfalso ;
                apply Logic.eq_sym in Heq0 ;
                clear Hafts ;
                generalize dependent afte0 ;
                induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                 try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                     assert (const_list (a0 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                [    destruct H; try (by inversion Heq0) ;
                      try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                     try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                          assert (const_list (a0 :: ves)) as Hconst ;
                          first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                          first_not_const Hconst) ;
                     induction H; try (by inversion Heq0) ;
                      try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                     try (by destruct vs as [|a0 ves]; inversion Heq0 ;
                          first_not_const H1) ;
                     try (by inversion Heq0; subst; inversion H);
                     destruct H ; try (by inversion Heq0) ;
                      try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                     try (by destruct vs ; inversion Heq0 ;
                          first_not_const H) ; 
                  try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                  unfold lfilled, lfill in H0 ;
                  destruct lh as [bef aft |] ; last (by false_assumption) ;
                  destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                  move/eqP in H0 ;
                  rewrite H0 in Heq0 ; 
                  destruct bef ; inversion Heq0 ;
                  first_not_const Hbef
                | rewrite - Heq0 in H ;
                  simple_filled2 H k lh bef aft nn ll ll' ;
                  [ destruct bef ;
                    [ destruct es ; first empty_list_no_reduce ;
                      inversion H ; subst ;
                        by eapply IHHred0
                    | inversion H ;
                      first_not_const Hvs ]
                  | destruct bef ; inversion H ;
                    first_not_const Hvs ]]
              |] ;
              destruct vs0 ;
              [ exfalso ;
                clear Hafts ;
                generalize dependent afte0 ;
                induction Hred0 ; intros afte0 Heq0 ; 
                try (by inversion Heq0) ;
                 try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                     destruct ves as [| b1 ves] ; inversion Heq0 ;
                     assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;
                [   destruct H;
                    try (by inversion Heq0) ;
                     try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                     destruct ves as [| b1 ves] ; inversion Heq0 ;
                     assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                     first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                     first_not_const Hconst) ;

                    destruct H ;
                    try (by inversion Heq0) ;
                     try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                  try (by destruct vs ; first (by inversion Heq0) ;
                       destruct vs ; inversion Heq0 ;
                       first_not_const H) ;
                  unfold lfilled, lfill in H0 ;
                  destruct lh as [bef aft |] ; last (by false_assumption) ;
                  destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                  move/eqP in H0 ; 
                  rewrite H0 in Heq0 ;
                  destruct bef ; 
                  inversion Heq0 ; subst ;
                  inversion Hvs0 ; 
                  destruct bef ; inversion Heq0 ;
                  first_not_const Hbef 
                | rewrite Heq0 in H ;
                  simple_filled2 H k lh bef aft nn ll ll' ;
                  [ destruct bef ;
                    [ destruct es ; first empty_list_no_reduce ;
                      destruct es ; inversion H ; subst ;
                      [ values_no_reduce 
                      | by eapply IHHred0 ]
                    | destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ;
                        remember (a1 :: es) as es0 ;
                        subst a1 ;
                        clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                        generalize dependent es ;
                        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                         try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                        try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                             assert (const_list (b0 :: ves)) as Hconst ;
                             first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                             first_not_const Hconst) ;
                        [ destruct H; try (by inversion Heq0) ;
                           try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                        try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                             assert (const_list (b0 :: ves)) as Hconst ;
                             first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                             first_not_const Hconst) ;
                          destruct H ; try (by inversion Heq0) ;
                           try (by destruct v; inversion Heq0);
                 try (by destruct v0; inversion Heq0);
                 try (by destruct v1; inversion Heq0);
                 try (by destruct v2; inversion Heq0);
                 try (by destruct v3; inversion Heq0);
                          try (by destruct vs ; inversion Heq0 ;
                               first_not_const H) ; 
                          try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                          unfold lfilled, lfill in H0 ;
                          destruct lh as [bef aft |] ; last (by false_assumption) ;
                          destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                          move/eqP in H0 ;
                          rewrite H0 in Heq0 ; 
                          destruct bef ; inversion Heq0 ;
                          first_not_const Hbef
                        | rewrite Heq0 in H ;
                          simple_filled2 H k lh bef aft nn ll ll' ;
                          [ destruct bef ;
                            [ destruct es ; first empty_list_no_reduce ;
                              inversion H ; subst ;
                                by eapply IHHred0
                            | inversion H ;
                              first_not_const Hvs ]
                          | destruct bef ; inversion H ;
                            first_not_const Hvs ]]
                      | inversion H ;
                        first_not_const Hvs ]]
                  | destruct bef ; inversion H ;
                    subst ; inversion Hvs0 ;
                    destruct bef ; inversion H ;
                    first_not_const Hvs ]] 
              | get_tail a0 vs0 ys y Htail ;
                rewrite Htail in Hbefs ;
                rewrite app_comm_cons in Hbefs ;
                get_tail a ys ys' y' Htail' ;
                rewrite Htail' in Hbefs ;
                rewrite (separate1 (AI_const _)) in Hbefs ;
                repeat rewrite catA in Hbefs ;
                rewrite assoc_list_seq in Hbefs ;
                apply app_inj_tail in Hbefs as [Hys' ->] ;
                apply app_inj_tail in Hys' as [Hys ->] ;
                rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
                - separate1 separate3 in Heq0 ;
                eexists _, ys', afte0, [], [], _;
                repeat split ; try done ; try (by rewrite app_nil_r) ;
                [ rewrite Htail app_comm_cons Htail' in Hvs0 ;
                  unfold const_list in Hvs0 ;
                  repeat rewrite forallb_app in Hvs0 ;
                  repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
                  done
                | by econstructor; econstructor]]) .



      
(* destruct first non-value (const cases) *)
    { destruct H as [ | ? ? ? ? ? Hr | ? ? ? ? Hr | | | | ? ? ? ? ? Hr1 Hr2 |
                      ? ? ? ? Hr1 Hr2 | ? ? ? Hr1 Hr2 Hr3 | | | | ? ? ? Hr | ? ? ? Hr |
                      ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 | ? ? ? ? ? ? Hr1 Hr2 Hr3 Hr4 |
                      ? ? ? ? Hr | ? ? ? ? Hr | ? ? ? Hr | | ? ? ? ? ? ? Hr1 Hr2 Hr3 |
                      ? ? Hr | ? ? Hr | ? ? ? ? Hr1 Hr2 | ? ? ? Hr | ? ? ? Hr1 Hr2 |
                    | ? ? ? ? ? ? Hr1 Hr2 Hr3 | ? ? Hr | ? ? ? ? Hr1 Hr2 | ? ? ? Hr1 Hr2 |
                      ? ? ? ? ? ? Hr1 Hr2 Hr3 | ? ? ? ? ? Hr1 Hr2 Hr3 |
                      ? | | ? Hr | ? ? Hr1 Hr2 | | ].
      all: try (by left ; do 2 rewrite app_assoc in Heq ;
                rewrite - (app_assoc ( _ ++ _)) in Heq ;
                rewrite - app_comm_cons in Heq;
                apply first_values in Heq as (<- & -> & <-); try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                try (destruct He0 as [-> | ->]; by intros [? ?]);
                try (by const_list_app; try rewrite const_const);
                rewrite separate1 in Heq0;
                eexists _, vs0, afte0, [], [], _;
                repeat split ; try done ; try (by rewrite app_nil_r) ;
                  by repeat econstructor).
      21: try (destruct v ; (try destruct b) ; try by inversion Hr).    


      21: fold (AI_const (VAL_numeric n)) in Heq.
      22: fold (AI_const (VAL_pointer p)) in Heq.
      
      all: try (by  left ; rewrite (separate1 (AI_const _)) in Heq ; 
                repeat rewrite app_assoc in Heq  ;
                repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
                rewrite - app_comm_cons in Heq ;
                apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                try (destruct He0 as [-> | ->]; by intros [? ?]);
                try (by const_list_app; try rewrite const_const) ; 
                destruct vs0 ;
                [ simpl in Heq0 ;
                  exfalso ;
                  apply Logic.eq_sym in Heq0 ;
                  clear Hafts ;
                  generalize dependent afte0 ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                  try (by destruct v2; inversion Heq0);
                  try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                       assert (const_list (a0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [  destruct H; try (by inversion Heq0) ;
                       try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                     try (by destruct v2; inversion Heq0);
                    
                  try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                       assert (const_list (a0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                     destruct H ; try (by inversion Heq0) ;
                       try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                     try (by destruct v2; inversion Heq0);
                   
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite - Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | get_tail a vs0 ys y Htail ;
                  rewrite Htail in Hbefs ;
                  repeat rewrite catA in Hbefs ;
                  apply app_inj_tail in Hbefs as [Hbefs ->] ;
                  rewrite Htail in Heq0 ;
                  rewrite - app_assoc in Heq0 ;
                  rewrite - separate1 in Heq0 ;
                  rewrite separate2 in Heq0 ;
                  eexists _, ys, afte0, [], [], _;
                  repeat split ; try done ; try (by rewrite app_nil_r) ;
                  [ rewrite Htail in Hvs0 ;
                    unfold const_list in Hvs0 ;
                    rewrite forallb_app in Hvs0 ;
                    apply andb_true_iff in Hvs0 as [Hys _] ;
                      by unfold const_list 
                  | by repeat econstructor ]]).
      1-3:try by (left ; rewrite separate2 in Heq ;
                   repeat rewrite app_assoc in Heq ;
                   repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
                   rewrite - app_comm_cons in Heq ;
                   apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                   try (destruct He0 as [-> | ->]; by intros [? ?]);
                   try (by const_list_app; repeat rewrite const_const) ;
                   destruct vs0 ;
                   [ simpl in Heq0 ;
                     exfalso ;
                     apply Logic.eq_sym in Heq0 ;
                     clear Hafts ;
                     generalize dependent afte0 ;
                     induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                       try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                     try (by destruct v2; inversion Heq0);
                                       try (by destruct v3; inversion Heq0);
                     
                     try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                          assert (const_list (a0 :: ves)) as Hconst ;
                          first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                          first_not_const Hconst) ;
                     [  destruct H; try (by inversion Heq0) ;
                          try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                        try (by destruct v2; inversion Heq0);
                          try (by destruct v3; inversion Heq0);
                        
                     try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                          assert (const_list (a0 :: ves)) as Hconst ;
                          first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                          first_not_const Hconst) ;
                        destruct H ; try (by inversion Heq0);
                          try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                        try (by destruct v2; inversion Heq0);
                          try (by destruct v3; inversion Heq0);
                       
                       try (by destruct vs ; inversion Heq0 ;
                            first_not_const H) ; 
                       try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                       unfold lfilled, lfill in H0 ;
                       destruct lh as [bef aft |] ; last (by false_assumption) ;
                       destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                       move/eqP in H0 ;
                       rewrite H0 in Heq0 ; 
                       destruct bef ; inversion Heq0 ;
                       first_not_const Hbef
                     | rewrite - Heq0 in H ;
                       simple_filled2 H k lh bef aft nn ll ll' ;
                       [ destruct bef ;
                         [ destruct es ; first empty_list_no_reduce ;
                           inversion H ; subst ;
                             by eapply IHHred0
                         | inversion H ;
                           first_not_const Hvs ]
                       | destruct bef ; inversion H ;
                         first_not_const Hvs ]]
                   |] ;
                   destruct vs0 ;
                   [ exfalso ;
                     clear Hafts ;
                     generalize dependent afte0 ;
                     induction Hred0 ; intros afte0 Heq0 ; 
                     try (by inversion Heq0) ;
                       try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                     try (by destruct v2; inversion Heq0);
                       try (by destruct v3; inversion Heq0);
                     
                     try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                          destruct ves as [| b1 ves] ; inversion Heq0 ;
                          assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                          first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                          first_not_const Hconst) ;
                     [  destruct H;
                        try (by inversion Heq0) ;
                          try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                        try (by destruct v2; inversion Heq0);
                          try (by destruct v3; inversion Heq0);
             
                     try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                          destruct ves as [| b1 ves] ; inversion Heq0 ;
                          assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                          first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                          first_not_const Hconst) ;
                        destruct H ;
                        try (by inversion Heq0) ;
                          try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                        try (by destruct v2; inversion Heq0);
                          try (by destruct v3; inversion Heq0);
                       
                       try (by destruct vs ; first (by inversion Heq0) ;
                            destruct vs ; inversion Heq0 ;
                            first_not_const H) ;
                       unfold lfilled, lfill in H0 ;
                       destruct lh as [bef aft |] ; last (by false_assumption) ;
                       destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                       move/eqP in H0 ; 
                       rewrite H0 in Heq0 ;
                       destruct bef ; 
                       inversion Heq0 ; subst ;
                       inversion Hvs0 ; 
                       destruct bef ; inversion Heq0 ;
                       first_not_const Hbef 
                     | rewrite Heq0 in H ;
                       simple_filled2 H k lh bef aft nn ll ll' ;
                       [ destruct bef ;
                         [ destruct es ; first empty_list_no_reduce ;
                           destruct es ; inversion H ; subst ;
                           [ values_no_reduce 
                           | by eapply IHHred0 ]
                         | destruct bef ;
                           [ destruct es ; first empty_list_no_reduce ;
                             inversion H ;
                             remember (a1 :: es) as es0 ;
                             subst a1 ;
                             clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                             generalize dependent es ;
                             induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                               try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                             try (by destruct v2; inversion Heq0);
                               try (by destruct v3; inversion Heq0);
                             
                             try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                                  assert (const_list (b0 :: ves)) as Hconst ;
                                  first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                                  first_not_const Hconst) ;
                             [  destruct H; try (by inversion Heq0) ;
                                  try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                                try (by destruct v2; inversion Heq0);
                                  try (by destruct v3; inversion Heq0);
                                
                             try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                                  assert (const_list (b0 :: ves)) as Hconst ;
                                  first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                                  first_not_const Hconst) ;
                                destruct H ; try (by inversion Heq0) ;
                                  try (by destruct v; inversion Heq0);
                  try (by destruct v0; inversion Heq0);
                  try (by destruct v1; inversion Heq0);
                                try (by destruct v2; inversion Heq0);
                                  try (by destruct v3; inversion Heq0);
                                
                               try (by destruct vs ; inversion Heq0 ;
                                    first_not_const H) ; 
                               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                               unfold lfilled, lfill in H0 ;
                               destruct lh as [bef aft |] ; last (by false_assumption) ;
                               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                               move/eqP in H0 ;
                               rewrite H0 in Heq0 ; 
                               destruct bef ; inversion Heq0 ;
                               first_not_const Hbef
                             | rewrite Heq0 in H ;
                               simple_filled2 H k lh bef aft nn ll ll' ;
                               [ destruct bef ;
                                 [ destruct es ; first empty_list_no_reduce ;
                                   inversion H ; subst ;
                                     by eapply IHHred0
                                 | inversion H ;
                                   first_not_const Hvs ]
                               | destruct bef ; inversion H ;
                                 first_not_const Hvs ]]
                           | inversion H ;
                             first_not_const Hvs ]]
                       | destruct bef ; inversion H ;
                         subst ; inversion Hvs0 ;
                         destruct bef ; inversion H ;
                         first_not_const Hvs ]] 
                | get_tail a0 vs0 ys y Htail ;
                  rewrite Htail in Hbefs ;
                  rewrite app_comm_cons in Hbefs ;
                     get_tail a ys ys' y' Htail' ;
                     rewrite Htail' in Hbefs ;
                     rewrite (separate1 (AI_const _)) in Hbefs ;
                     repeat rewrite catA in Hbefs ;
                     rewrite assoc_list_seq in Hbefs ;
                     apply app_inj_tail in Hbefs as [Hys' ->] ;
                     apply app_inj_tail in Hys' as [Hys ->] ;
                     rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
                     - separate1 separate3 in Heq0 ;
                     eexists _, ys', afte0, [], [], _;
                     repeat split ; try done ; try (by rewrite app_nil_r) ;
                     [ rewrite Htail app_comm_cons Htail' in Hvs0 ;
                       unfold const_list in Hvs0 ;
                       repeat rewrite forallb_app in Hvs0 ;
                       repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
                       done
                     | by repeat econstructor]]).
(* 3-const peel subcase *)
      - left ; rewrite separate3 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app; repeat rewrite const_const) ;
          destruct vs0.
         exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
               assert (const_list (a0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [  destruct H ; try (by inversion Heq0) ;
             try (by destruct v; inversion Heq0);
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
               assert (const_list (a0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
             destruct H ; try (by inversion Heq0) ;
             try (by destruct v; inversion Heq0);
             try (by destruct v0; inversion Heq0);
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef
          | rewrite - Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        destruct vs0.
        exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
          try (by inversion Heq0) ;
          try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H;
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
            destruct H ;
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
            try (by destruct v3; inversion Heq0);
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H)  ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a1 :: es) as es0 ;
                  subst a1 ;
                  clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [  destruct H; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                     destruct H ; try (by inversion Heq0) ;
                     try (by destruct v; inversion Heq0);
                     try (by destruct v0; inversion Heq0);
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption)  ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs ]] .
        destruct vs0.
        exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b2 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: b2 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst).
          destruct H; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b2 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: b2 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst). 
        destruct H ; try (by inversion Heq0) ;
          try (by repeat (destruct vs ; first by inversion Heq0) ;
               inversion Heq0 ;
               first_not_const H) ; 
          try (by inversion Heq0 ; subst ; simpl in H ; false_assumption).
        unfold lfilled, lfill in H0 ;
          destruct lh as [bef aft |] ; last (by false_assumption) ;
          destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
          move/eqP in H0 ;
          rewrite H0 in Heq0.
        repeat (destruct bef ; first by inversion Heq0 ; subst ; first_not_const Hvs0).
        inversion Heq0 ; subst. first_not_const Hbef.
        rewrite - Heq0 in H ;
          simple_filled2 H k lh bef aft nn ll ll'.
        destruct bef.
        destruct es ; first empty_list_no_reduce.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [Hvs0 _].
        by rewrite Hvs0.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        inversion H. subst.
        by eapply IHHred0.
        destruct bef. 
        destruct es ; first empty_list_no_reduce. 
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [? Hvs0].
        by rewrite H2.
        inversion H.
        remember (a2 :: a3 :: es) as es0 ;
          subst a2 a3.
        clear Heq0 afte0 H H5 aft H0 IHHred0 ;
          generalize dependent es.
        unfold const_list, forallb in Hvs0.
        apply andb_true_iff in Hvs0 as [_ Hvs0].
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [  destruct H; try (by inversion Heq0) ;
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
             destruct H ;
             try (by inversion Heq0) ;
             try (by destruct v; inversion Heq0);
             try (by destruct v3; inversion Heq0);
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H);
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a3 :: es) as es0 ;
                  subst a3 ;
                  clear Heq0 afte0 H H5 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [  destruct H; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                     destruct H ; try (by inversion Heq0) ;
                     try (by destruct v; inversion Heq0);
                     try (by destruct v0; inversion Heq0);
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption);
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs1 ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs1 ]] .
        destruct bef ; last by inversion H ; first_not_const Hvs.
        destruct es ; first empty_list_no_reduce.
        inversion H.
        remember (a3 :: es) as es0.
        subst a3.
        clear afte0 H5 Heq0 H aft H0 IHHred0.
        generalize dependent es. 
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; inversion Heq0 ;
               assert (const_list (b0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [  destruct H; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; inversion Heq0 ;
               assert (const_list (b0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
             destruct H ; try (by inversion Heq0) ;
             try (by destruct v; inversion Heq0);
             try (by destruct v0; inversion Heq0);
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption)  ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        apply first_values in H as (_ & Habs & _) => //= ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
        get_tail a1 vs0 vs1 b1 Htail1.
        rewrite Htail1 app_comm_cons in Hbefs.
        get_tail a0 vs1 vs2 b2 Htail2.
        rewrite Htail2 app_comm_cons app_comm_cons in Hbefs.
        get_tail a vs2 vs3 b3 Htail3.
        rewrite Htail3 in Hbefs.
        rewrite (separate1 (AI_const _)) in Hbefs.
        rewrite (separate1 _ [_]) in Hbefs.
        repeat rewrite assoc_list_seq in Hbefs.
        repeat rewrite app_assoc in Hbefs.
        repeat apply app_inj_tail in Hbefs as [Hbefs ->].
        rewrite Htail1 app_comm_cons Htail2 app_comm_cons app_comm_cons Htail3 in Heq0.
        repeat rewrite - app_assoc in Heq0.
        simpl in Heq0.
        rewrite separate4 in Heq0.
        eexists _, vs3, afte0, [], [], _.
        repeat split => //= ; try by rewrite app_nil_r.
        rewrite - Hbefs in Hbef1.
        unfold const_list in Hbef1.
        rewrite forallb_app in Hbef1.
        apply andb_true_iff in Hbef1 as [_ Hbef1].
        done.
        by repeat econstructor.
(* 3-const peel subcase (2nd) *)
      - left ; rewrite separate3 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app; repeat rewrite const_const) ;
          destruct vs0.
        exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
               assert (const_list (a0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
               assert (const_list (a0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
            destruct H ; try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
            try (by destruct v0; inversion Heq0);
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption)  ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef
          | rewrite - Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        destruct vs0.
        exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
          try (by inversion Heq0) ;
          try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [ destruct H;
          try (by inversion Heq0) ;
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
            destruct H ;
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
            try (by destruct v3; inversion Heq0);
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a1 :: es) as es0 ;
                  subst a1 ;
                  clear Heq0 afte0 H H4 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [  destruct H; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                     destruct H ; try (by inversion Heq0) ;
                     try (by destruct v; inversion Heq0);
                     try (by destruct v0; inversion Heq0);
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption)  ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs ]] .
        destruct vs0.
        exfalso ;
          apply Logic.eq_sym in Heq0 ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b2 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: b2 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst).
          destruct H; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b2 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: b2 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst). 
        destruct H ; try (by inversion Heq0) ;
          try (by repeat (destruct vs ; first by inversion Heq0) ;
               inversion Heq0 ;
               first_not_const H) ; 
          try (by inversion Heq0 ; subst ; simpl in H ; false_assumption).
        unfold lfilled, lfill in H0 ;
          destruct lh as [bef aft |] ; last (by false_assumption) ;
          destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
          move/eqP in H0 ;
          rewrite H0 in Heq0.
        repeat (destruct bef ; first by inversion Heq0 ; subst ; first_not_const Hvs0).
        inversion Heq0 ; subst. first_not_const Hbef.
        rewrite - Heq0 in H ;
          simple_filled2 H k lh bef aft nn ll ll'.
        destruct bef.
        destruct es ; first empty_list_no_reduce.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [Hvs0 _].
        by rewrite Hvs0.
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        inversion H. subst.
        by eapply IHHred0.
        destruct bef. 
        destruct es ; first empty_list_no_reduce. 
        destruct es ; first (inversion H ; subst ; values_no_reduce).
        unfold const_list, forallb in Hvs0.
        repeat apply andb_true_iff in Hvs0 as [? Hvs0].
        by rewrite H2.
        inversion H.
        remember (a2 :: a3 :: es) as es0 ;
          subst a2 a3.
        clear Heq0 afte0 H H5 aft H0 IHHred0 ;
          generalize dependent es.
        unfold const_list, forallb in Hvs0.
        apply andb_true_iff in Hvs0 as [_ Hvs0].
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [  destruct H; try (by inversion Heq0) ;
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
             destruct H ;
             try (by inversion Heq0) ;
             try (by destruct v; inversion Heq0);
             try (by destruct v3; inversion Heq0);
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ; 
            rewrite H0 in Heq0 ;
            destruct bef ; 
            inversion Heq0 ; subst ;
            inversion Hvs0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                destruct es ; inversion H ; subst ;
                [ values_no_reduce 
                | by eapply IHHred0 ]
              | destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ;
                  remember (a3 :: es) as es0 ;
                  subst a3 ;
                  clear Heq0 afte0 H H5 aft H0 IHHred0 ;
                  generalize dependent es ;
                  induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                  [  destruct H; try (by inversion Heq0) ;
                  try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                       assert (const_list (b0 :: ves)) as Hconst ;
                       first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                       first_not_const Hconst) ;
                     destruct H ; try (by inversion Heq0) ;
                     try (by destruct v; inversion Heq0);
                     try (by destruct v0; inversion Heq0);
                    try (by destruct vs ; inversion Heq0 ;
                         first_not_const H) ; 
                    try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
                    unfold lfilled, lfill in H0 ;
                    destruct lh as [bef aft |] ; last (by false_assumption) ;
                    destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                    move/eqP in H0 ;
                    rewrite H0 in Heq0 ; 
                    destruct bef ; inversion Heq0 ;
                    first_not_const Hbef
                  | rewrite Heq0 in H ;
                    simple_filled2 H k lh bef aft nn ll ll' ;
                    [ destruct bef ;
                      [ destruct es ; first empty_list_no_reduce ;
                        inversion H ; subst ;
                          by eapply IHHred0
                      | inversion H ;
                        first_not_const Hvs ]
                    | destruct bef ; inversion H ;
                      first_not_const Hvs ]]
                | inversion H ;
                  first_not_const Hvs1 ]]
            | destruct bef ; inversion H ;
              subst ; inversion Hvs0 ;
              destruct bef ; inversion H ;
              first_not_const Hvs1 ]] .
        destruct bef ; last by inversion H ; first_not_const Hvs.
        destruct es ; first empty_list_no_reduce.
        inversion H.
        remember (a3 :: es) as es0.
        subst a3.
        clear afte0 H5 Heq0 H aft H0 IHHred0.
        generalize dependent es. 
        induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; inversion Heq0 ;
               assert (const_list (b0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
          [  destruct H; try (by inversion Heq0) ;
          try (by destruct ves as [|b0 ves]; inversion Heq0 ;
               assert (const_list (b0 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) ;
             destruct H ; try (by inversion Heq0) ;
             try (by destruct v; inversion Heq0);
             try (by destruct v0; inversion Heq0);
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ; 
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) ;
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ; 
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef 
          | rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' ;
            [ destruct bef ;
              [ destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0
              | inversion H ;
                first_not_const Hvs ]
            | destruct bef ; inversion H ;
              first_not_const Hvs ]].
        apply first_values in H as (_ & Habs & _) => //= ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
        get_tail a1 vs0 vs1 b1 Htail1.
        rewrite Htail1 app_comm_cons in Hbefs.
        get_tail a0 vs1 vs2 b2 Htail2.
        rewrite Htail2 app_comm_cons app_comm_cons in Hbefs.
        get_tail a vs2 vs3 b3 Htail3.
        rewrite Htail3 in Hbefs.
        rewrite (separate1 (AI_const _)) in Hbefs.
        rewrite (separate1 _ [_]) in Hbefs.
        repeat rewrite assoc_list_seq in Hbefs.
        repeat rewrite app_assoc in Hbefs.
        repeat apply app_inj_tail in Hbefs as [Hbefs ->].
        rewrite Htail1 app_comm_cons Htail2 app_comm_cons app_comm_cons Htail3 in Heq0.
        repeat rewrite - app_assoc in Heq0.
        simpl in Heq0.
        rewrite separate4 in Heq0.
        eexists _, vs3, afte0, [], [], _.
        repeat split => //= ; try by rewrite app_nil_r.
        rewrite - Hbefs in Hbef1.
        unfold const_list in Hbef1.
        rewrite forallb_app in Hbef1.
        apply andb_true_iff in Hbef1 as [_ Hbef1].
        done.
        by repeat econstructor.
(* block subcase *)
      - left ; repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app).
        cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
(* block: bound length vs0 < n *)
        { intros Hnnn. destruct (decide (length vs0 < n)).
          exfalso ; by eapply Hnnn.
          assert (length vs0 >= n) ; first lia.
          rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
          assert (length (drop (length vs0 - n) vs0) = length vs). 
(* drop-length subgoal *)
          { rewrite drop_length. rewrite Hr2. lia. }
          rewrite assoc_list_seq in Hbefs.
          destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
          rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
          rewrite - app_assoc in Heq0.
          rewrite separate1 in Heq0.
          rewrite (app_assoc vs) in Heq0.
          eexists _,(take (length vs0 - n) vs0),afte0,[],[],_;
            repeat split ; try done ; try by rewrite app_nil_r.
          rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
          unfold const_list in Hvs0.
          rewrite forallb_app in Hvs0.
          by apply andb_true_iff in Hvs0 as [? _].
          apply rm_silent, r_simple. by eapply rs_block. }
        intros nnn.
        clear Hbefs Hafts.
        generalize dependent afte0.
        generalize dependent vs0.
        generalize dependent es0'.
        generalize dependent es0.
        induction nnn.
        intros ; lia.
        intros es0 es0' Hred.
        induction Hred ; intros vs0 Hvs0 afte0 Heq Hnnn Hlen'  ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by  rewrite - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
               rewrite H1 ; apply v_to_e_is_const_list).
(* block: destruct Hred steps *)
        { destruct H;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by  rewrite - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
               rewrite H1 ; apply v_to_e_is_const_list).
          destruct H ;
            try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])).
(* block: not-enough-args no-reduce *)
          - rewrite - (app_nil_r [_]) in Heq.
            apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
            apply (block_not_enough_arguments_no_reduce s f vs0 t1s0 t2s0 es0 Eempty
                                                        s f [AI_label m0 [] (vs0 ++ to_e_list es0)]) => //=.
            apply rm_silent, r_simple ; eapply rs_block => //=.
            inversion Hblock ; subst.
            by rewrite - Hr3 in Hlen'.
(* block: const-tail values *)
          - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
            unfold const_list, forallb ; by rewrite H.
(* block: hole reduction *)
          - unfold lfilled, lfill in H0.
            destruct lh as [bef aft|] ; last by false_assumption.
            destruct (const_list bef) eqn:Hbef ; last by false_assumption.
            move/eqP in H0.
            rewrite H0 in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
        simple_filled2 H k lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ;
          try (destruct He as [-> | ->]; by intros [? ?]) ;
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
(* loop subcase *)
      - left ; repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app).
        cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
(* loop: bound length vs0 < n *)
        { intros Hnnn. destruct (decide (length vs0 < n)).
          exfalso ; by eapply Hnnn.
          assert (length vs0 >= n) ; first lia.
          rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
          assert (length (drop (length vs0 - n) vs0) = length vs). 
(* drop-length subgoal *)
          { rewrite drop_length. rewrite Hr2. lia. }
          rewrite assoc_list_seq in Hbefs.
          destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
          rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
          rewrite - app_assoc in Heq0.
          rewrite separate1 in Heq0.
          rewrite (app_assoc vs) in Heq0.
          eexists _,(take (length vs0 - n) vs0),afte0,[],[],_;
            repeat split ; try done ; try by rewrite app_nil_r.
          rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
          unfold const_list in Hvs0.
          rewrite forallb_app in Hvs0.
          by apply andb_true_iff in Hvs0 as [? _].
          apply rm_silent, r_simple. by eapply rs_loop. }
        intros nnn.
        clear Hbefs Hafts.
        generalize dependent afte0.
        generalize dependent vs0.
        generalize dependent es0'.
        generalize dependent es0.
        induction nnn.
        intros ; lia.
        intros es0 es0' Hred.
        induction Hred ; intros vs0 Hvs0 afte0 Heq Hnnn Hlen' ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (destruct v ; try (destruct b) ; try done) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by  rewrite - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?]) ;
               rewrite H1 ; apply v_to_e_is_const_list).
(* loop: destruct Hred steps *)
        {  destruct H;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (destruct v ; try (destruct b) ; try done) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by  rewrite - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
               try (destruct He0 as [-> | ->]; by intros [? ?]) ;
               rewrite H1 ; apply v_to_e_is_const_list).
           destruct H ;
            try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])) ;
            try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
                 apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
                 try (destruct He0 as [-> | ->]; by intros [? ?])).
(* loop: not-enough-args no-reduce *)
          - rewrite - (app_nil_r [_]) in Heq.
            apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]);
              apply (block_not_enough_arguments_no_reduce s f vs0 t1s0 t2s0 es0 Eempty
                                                          s f [AI_label m0 [] (vs0 ++ to_e_list es0)]) => //=.
            apply rm_silent, r_simple ; eapply rs_block => //=.
            inversion Hblock ; subst.
            by rewrite - Hr3 in Hlen'.
(* loop: const-tail values *)
          - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]).
            unfold const_list, forallb ; by rewrite H.
(* loop: hole reduction *)
          - unfold lfilled, lfill in H0.
            destruct lh as [bef aft|] ; last by false_assumption.
            destruct (const_list bef) eqn:Hbef ; last by false_assumption.
            move/eqP in H0.
            rewrite H0 in Heq.
            apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
        simple_filled2 H k lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ;
          try (destruct He as [-> | ->]; by intros [? ?]) ;
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
(* ptr_add success *)
      - left ; rewrite separate2 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app) .
        destruct vs0 .
(* vs0 empty -> contradiction *)
        { simpl in Heq0 ;
            exfalso ;
            apply Logic.eq_sym in Heq0 ;
            clear Hafts ;
            generalize dependent afte0 .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                 assert (const_list (a0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on non-const head *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                   assert (const_list (a0 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. }
           rewrite - Heq0 in H ;
             simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef .
            destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0.
             inversion H ;
                   first_not_const Hvs .
              destruct bef ; inversion H ;
                 first_not_const Hvs . } 
        destruct vs0 .
(* vs0 one value -> contradiction *)
        { exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) . 
(* case on head *)
          {  destruct H;
              try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                   destruct ves as [| b1 ves] ; inversion Heq0 ;
                   assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ;
               try (by inversion Heq0) ;
               try (by destruct v2; inversion Heq0);
               try (by destruct vs ; first (by inversion Heq0) ;
                    destruct vs ; inversion Heq0 ;
                    first_not_const H) .
             unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ; 
               rewrite H0 in Heq0 ;
               destruct bef ; 
               inversion Heq0 ; subst ;
               inversion Hvs0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef . } 
          rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' .
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            destruct es ; inversion H ; subst ;
            [ values_no_reduce 
            | by eapply IHHred0 ].
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            inversion H ;
            remember (a1 :: es) as es0 ;
            subst a1 ;
            clear Heq0 afte0 H H4 aft H0 IHHred0 ;
            generalize dependent es .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                 assert (const_list (b0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) . 
(* case on inner const *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
               try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                    assert (const_list (b0 :: ves)) as Hconst ;
                    first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                    first_not_const Hconst) .
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. } 
           rewrite Heq0 in H ;
              simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ; subst ;
                    by eapply IHHred0
                | inversion H ;
                  first_not_const Hvs ].
            destruct bef ; inversion H ;
                first_not_const Hvs .
             inversion H ;
            first_not_const Hvs.
             destruct bef ; inversion H ;
               subst ; inversion Hvs0 ;
               destruct bef ; inversion H ;
               first_not_const Hvs . } 
        get_tail a0 vs0 ys y Htail ;
          rewrite Htail in Hbefs ;
          rewrite app_comm_cons in Hbefs ;
          get_tail a ys ys' y' Htail' ;
          rewrite Htail' in Hbefs ;
          rewrite (separate1 (AI_const _)) in Hbefs ;
          repeat rewrite catA in Hbefs ;
          rewrite assoc_list_seq in Hbefs ;
          apply app_inj_tail in Hbefs as [Hys' ->] ;
          apply app_inj_tail in Hys' as [Hys ->] ;
          rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
          - separate1 separate3 in Heq0 ;
          eexists _, ys', afte0, [], [], _.
          repeat split ; try done ; try (by rewrite app_nil_r) .
           rewrite Htail app_comm_cons Htail' in Hvs0 ;
            unfold const_list in Hvs0 ;
            repeat rewrite forallb_app in Hvs0 ;
            repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
            done.
           by eapply rm_silent, r_simple, rs_pointeradd_success.
(* ptr_add failure *)
      - left ; rewrite separate2 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app) .
        destruct vs0 .
(* vs0 empty -> contradiction *)
        { simpl in Heq0 ;
            exfalso ;
            apply Logic.eq_sym in Heq0 ;
            clear Hafts ;
            generalize dependent afte0 .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                 assert (const_list (a0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on non-const head *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                   assert (const_list (a0 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. }
           rewrite - Heq0 in H ;
             simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef .
            destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0.
             inversion H ;
                   first_not_const Hvs .
              destruct bef ; inversion H ;
                 first_not_const Hvs . } 
        destruct vs0 .
(* vs0 one value -> contradiction *)
        { exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) . 
(* case on head *)
          {  destruct H;
              try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                   destruct ves as [| b1 ves] ; inversion Heq0 ;
                   assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ;
               try (by inversion Heq0) ;
               try (by destruct v2; inversion Heq0);
               try (by destruct vs ; first (by inversion Heq0) ;
                    destruct vs ; inversion Heq0 ;
                    first_not_const H) .
             unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ; 
               rewrite H0 in Heq0 ;
               destruct bef ; 
               inversion Heq0 ; subst ;
               inversion Hvs0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef . } 
          rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' .
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            destruct es ; inversion H ; subst ;
            [ values_no_reduce 
            | by eapply IHHred0 ].
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            inversion H ;
            remember (a1 :: es) as es0 ;
            subst a1 ;
            clear Heq0 afte0 H H4 aft H0 IHHred0 ;
            generalize dependent es .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            
            try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                 assert (const_list (b0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on inner const *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
               try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                    assert (const_list (b0 :: ves)) as Hconst ;
                    first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                    first_not_const Hconst) .
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v1; inversion Heq0);
               try (by destruct v; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. } 
           rewrite Heq0 in H ;
              simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ; subst ;
                    by eapply IHHred0
                | inversion H ;
                  first_not_const Hvs ].
            destruct bef ; inversion H ;
                first_not_const Hvs .
             inversion H ;
            first_not_const Hvs.
             destruct bef ; inversion H ;
               subst ; inversion Hvs0 ;
               destruct bef ; inversion H ;
               first_not_const Hvs . } 
        get_tail a0 vs0 ys y Htail ;
          rewrite Htail in Hbefs ;
          rewrite app_comm_cons in Hbefs ;
          get_tail a ys ys' y' Htail' ;
          rewrite Htail' in Hbefs ;
          rewrite (separate1 (AI_const _)) in Hbefs ;
          repeat rewrite catA in Hbefs ;
          rewrite assoc_list_seq in Hbefs ;
          apply app_inj_tail in Hbefs as [Hys' ->] ;
          apply app_inj_tail in Hys' as [Hys ->] ;
          rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
          - separate1 separate3 in Heq0 ;
          eexists _, ys', afte0, [], [], _.
          repeat split ; try done ; try (by rewrite app_nil_r) .
           rewrite Htail app_comm_cons Htail' in Hvs0 ;
            unfold const_list in Hvs0 ;
            repeat rewrite forallb_app in Hvs0 ;
            repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
            done.
           by eapply rm_silent, r_simple, rs_pointeradd_failure.


(* ptr_sub success *)
      - left ; rewrite separate2 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app); rename H0 into Hr2; rename H into Hr1 .
        destruct vs0 .
(* vs0 empty -> contradiction *)
        { simpl in Heq0 ;
            exfalso ;
            apply Logic.eq_sym in Heq0 ;
            clear Hafts ;
            generalize dependent afte0 .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                 assert (const_list (a0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on head *)
          {
            destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                   assert (const_list (a0 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. }
           rewrite - Heq0 in H ;
             simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef .
            destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0.
             inversion H ;
                   first_not_const Hvs .
              destruct bef ; inversion H ;
                 first_not_const Hvs . } 
        destruct vs0 .
(* vs0 one value -> contradiction *)
        { exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) . 
(* case on head *)
          {  
            destruct H;
              try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                   destruct ves as [| b1 ves] ; inversion Heq0 ;
                   assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ;
               try (by inversion Heq0) ;
               try (by destruct v2; inversion Heq0);
               try (by destruct vs ; first (by inversion Heq0) ;
                    destruct vs ; inversion Heq0 ;
                    first_not_const H) .
             unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ; 
               rewrite H0 in Heq0 ;
               destruct bef ; 
               inversion Heq0 ; subst ;
               inversion Hvs0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef . } 
          rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' .
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            destruct es ; inversion H ; subst ;
            [ values_no_reduce 
            | by eapply IHHred0 ].
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            inversion H ;
            remember (a1 :: es) as es0 ;
            subst a1 ;
            clear Heq0 afte0 H H4 aft H0 IHHred0 ;
            generalize dependent es .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                 assert (const_list (b0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) . 
(* case on inner const *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
               try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                    assert (const_list (b0 :: ves)) as Hconst ;
                    first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                    first_not_const Hconst) .
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. } 
           rewrite Heq0 in H ;
              simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ; subst ;
                    by eapply IHHred0
                | inversion H ;
                  first_not_const Hvs ].
            destruct bef ; inversion H ;
                first_not_const Hvs .
             inversion H ;
            first_not_const Hvs.
             destruct bef ; inversion H ;
               subst ; inversion Hvs0 ;
               destruct bef ; inversion H ;
               first_not_const Hvs . } 
        get_tail a0 vs0 ys y Htail ;
          rewrite Htail in Hbefs ;
          rewrite app_comm_cons in Hbefs ;
          get_tail a ys ys' y' Htail' ;
          rewrite Htail' in Hbefs ;
          rewrite (separate1 (AI_const _)) in Hbefs ;
          repeat rewrite catA in Hbefs ;
          rewrite assoc_list_seq in Hbefs ;
          apply app_inj_tail in Hbefs as [Hys' ->] ;
          apply app_inj_tail in Hys' as [Hys ->] ;
          rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
          - separate1 separate3 in Heq0 ;
          eexists _, ys', afte0, [], [], _.
          repeat split ; try done ; try (by rewrite app_nil_r) .
           rewrite Htail app_comm_cons Htail' in Hvs0 ;
            unfold const_list in Hvs0 ;
            repeat rewrite forallb_app in Hvs0 ;
            repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
            done.
           by eapply rm_silent, r_simple, rs_pointersub_success.


(* ptr_sub failure *)
      - left ; rewrite separate2 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app); rename H0 into Hr2; rename H into Hr1 .
        destruct vs0 .
(* vs0 empty -> contradiction *)
        { simpl in Heq0 ;
            exfalso ;
            apply Logic.eq_sym in Heq0 ;
            clear Hafts ;
            generalize dependent afte0 .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                 assert (const_list (a0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on non-const head *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                   assert (const_list (a0 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. }
           rewrite - Heq0 in H ;
             simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef .
            destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0.
             inversion H ;
                   first_not_const Hvs .
              destruct bef ; inversion H ;
                 first_not_const Hvs . } 
        destruct vs0 .
(* vs0 one value -> contradiction *)
        { exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ; 
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) . 
(* case on head *)
          {  destruct H;
              try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                   destruct ves as [| b1 ves] ; inversion Heq0 ;
                   assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ;
               try (by inversion Heq0) ;
               try (by destruct v2; inversion Heq0);
               try (by destruct vs ; first (by inversion Heq0) ;
                    destruct vs ; inversion Heq0 ;
                    first_not_const H) .
             unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ; 
               rewrite H0 in Heq0 ;
               destruct bef ; 
               inversion Heq0 ; subst ;
               inversion Hvs0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef . } 
          rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' .
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            destruct es ; inversion H ; subst ;
            [ values_no_reduce 
            | by eapply IHHred0 ].
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            inversion H ;
            remember (a1 :: es) as es0 ;
            subst a1 ;
            clear Heq0 afte0 H H4 aft H0 IHHred0 ;
            generalize dependent es .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            
            try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                 assert (const_list (b0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on inner const *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
               try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                    assert (const_list (b0 :: ves)) as Hconst ;
                    first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                    first_not_const Hconst) .
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v1; inversion Heq0);
               try (by destruct v; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. } 
           rewrite Heq0 in H ;
              simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ; subst ;
                    by eapply IHHred0
                | inversion H ;
                  first_not_const Hvs ].
            destruct bef ; inversion H ;
                first_not_const Hvs .
             inversion H ;
            first_not_const Hvs.
             destruct bef ; inversion H ;
               subst ; inversion Hvs0 ;
               destruct bef ; inversion H ;
               first_not_const Hvs . } 
        get_tail a0 vs0 ys y Htail ;
          rewrite Htail in Hbefs ;
          rewrite app_comm_cons in Hbefs ;
          get_tail a ys ys' y' Htail' ;
          rewrite Htail' in Hbefs ;
          rewrite (separate1 (AI_const _)) in Hbefs ;
          repeat rewrite catA in Hbefs ;
          rewrite assoc_list_seq in Hbefs ;
          apply app_inj_tail in Hbefs as [Hys' ->] ;
          apply app_inj_tail in Hys' as [Hys ->] ;
          rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
          - separate1 separate3 in Heq0 ;
          eexists _, ys', afte0, [], [], _.
          repeat split ; try done ; try (by rewrite app_nil_r) .
           rewrite Htail app_comm_cons Htail' in Hvs0 ;
            unfold const_list in Hvs0 ;
            repeat rewrite forallb_app in Hvs0 ;
            repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
            done.
           by eapply rm_silent, r_simple, rs_pointersub_failure.


(* ptr_diff success *)
        - left ; rewrite separate2 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app); rename H0 into Hr2; rename H into Hr1 .
        destruct vs0 .
(* vs0 empty -> contradiction *)
        { simpl in Heq0 ;
            exfalso ;
            apply Logic.eq_sym in Heq0 ;
            clear Hafts ;
            generalize dependent afte0 .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                 assert (const_list (a0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on non-const head *)
          { destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                   assert (const_list (a0 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v1; inversion Heq0);
               try (by destruct v; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ; 
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ; 
                destruct bef ; inversion Heq0 ;
                first_not_const Hbef. }
             rewrite - Heq0 in H ;
              simple_filled2 H k lh bef aft nn ll ll' .
            destruct bef ;
                 [ destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0
                 | inversion H ;
                   first_not_const Hvs ].
             destruct bef ; inversion H ;
                 first_not_const Hvs .
              } 
        destruct vs0 .
(* vs0 one value -> contradiction *)
        { exfalso ;
            clear Hafts ;
            generalize dependent afte0 ;
            induction Hred0 ; intros afte0 Heq0 ; 
              try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
            try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                 destruct ves as [| b1 ves] ; inversion Heq0 ;
                 assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) . 
(* case on head *)
          { destruct H;
              try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                   destruct ves as [| b1 ves] ; inversion Heq0 ;
                   assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) . 
             destruct H ;
               try (by inversion Heq0) ;
               try (by destruct v2; inversion Heq0);
               try (by destruct vs ; first (by inversion Heq0) ;
                    destruct vs ; inversion Heq0 ;
                    first_not_const H) .
             unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ; 
               rewrite H0 in Heq0 ;
               destruct bef ; 
               inversion Heq0 ; subst ;
               inversion Hvs0 ; 
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef . } 
           rewrite Heq0 in H ;
             simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef .
           destruct es ; first empty_list_no_reduce ;
             destruct es ; inversion H ; subst ;
             [ values_no_reduce 
             | by eapply IHHred0 ].
           destruct bef .
           destruct es ; first empty_list_no_reduce ;
             inversion H ;
             remember (a1 :: es) as es0 ;
             subst a1 ;
             clear Heq0 afte0 H H4 aft H0 IHHred0 ;
             generalize dependent es .
           induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
             try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                  assert (const_list (b0 :: ves)) as Hconst ;
                  first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                  first_not_const Hconst) . 
(* case on inner const *)
           { destruct H; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                    assert (const_list (b0 :: ves)) as Hconst ;
                    first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                    first_not_const Hconst) .
              destruct H ; try (by inversion Heq0) ;
                try (by destruct v1; inversion Heq0);
                try (by destruct v; inversion Heq0);
                 try (by destruct vs ; inversion Heq0 ;
                      first_not_const H) ; 
              try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
              unfold lfilled, lfill in H0 ;
                destruct lh as [bef aft |] ; last (by false_assumption) ;
                destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                move/eqP in H0 ;
                rewrite H0 in Heq0 ; 
                destruct bef ; inversion Heq0 ;
                first_not_const Hbef. } 
            rewrite Heq0 in H ;
               simple_filled2 H k lh bef aft nn ll ll' .
            destruct bef ;
                 [ destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0
                 | inversion H ;
                   first_not_const Hvs ].
             destruct bef ; inversion H ;
                 first_not_const Hvs .
              inversion H ;
             first_not_const Hvs.
              destruct bef ; inversion H ;
                subst ; inversion Hvs0 ;
                destruct bef ; inversion H ;
                first_not_const Hvs . } 
        get_tail a0 vs0 ys y Htail ;
          rewrite Htail in Hbefs ;
          rewrite app_comm_cons in Hbefs ;
          get_tail a ys ys' y' Htail' ;
          rewrite Htail' in Hbefs ;
          rewrite (separate1 (AI_const _)) in Hbefs ;
          repeat rewrite catA in Hbefs ;
          rewrite assoc_list_seq in Hbefs ;
          apply app_inj_tail in Hbefs as [Hys' ->] ;
          apply app_inj_tail in Hys' as [Hys ->] ;
          rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
          - separate1 separate3 in Heq0 ;
          eexists _, ys', afte0, [], [], _.
          repeat split ; try done ; try (by rewrite app_nil_r) .
           rewrite Htail app_comm_cons Htail' in Hvs0 ;
            unfold const_list in Hvs0 ;
            repeat rewrite forallb_app in Hvs0 ;
            repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
            done.
           by eapply rm_silent, r_simple, rs_pointerdiff_success.



(* ptr_diff failure *)
        - left ; rewrite separate2 in Heq ;
          repeat rewrite app_assoc in Heq ;
          repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
          rewrite - app_comm_cons in Heq ;
          apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try (by const_list_app); rename H into Hr1 .
        destruct vs0 .
(* vs0 empty -> contradiction *)
        { simpl in Heq0 ;
            exfalso ;
            apply Logic.eq_sym in Heq0 ;
            clear Hafts ;
            generalize dependent afte0 .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                 assert (const_list (a0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on non-const head *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                   assert (const_list (a0 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) .
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ;
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ;
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. }
           rewrite - Heq0 in H ;
             simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef .
            destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0.
             inversion H ;
                   first_not_const Hvs .
              destruct bef ; inversion H ;
                  first_not_const Hvs . }
        destruct vs0 .
(* vs0 one value -> contradiction *)
        { exfalso ;
          clear Hafts ;
          generalize dependent afte0 ;
          induction Hred0 ; intros afte0 Heq0 ;
            try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
          try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
               destruct ves as [| b1 ves] ; inversion Heq0 ;
               assert (const_list (b0 :: b1 :: ves)) as Hconst ;
               first (by rewrite H1 ; apply v_to_e_is_const_list) ;
               first_not_const Hconst) .
(* case on head *)
          {  destruct H;
              try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                    destruct ves as [| b1 ves] ; inversion Heq0 ;
                    assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                    first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                    first_not_const Hconst) .
             destruct H ;
               try (by inversion Heq0) ;
               try (by destruct v2; inversion Heq0);
               try (by destruct vs ; first (by inversion Heq0) ;
                    destruct vs ; inversion Heq0 ;
                    first_not_const H) .
             unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ;
               destruct bef ;
               inversion Heq0 ; subst ;
               inversion Hvs0 ;
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef . }
          rewrite Heq0 in H ;
            simple_filled2 H k lh bef aft nn ll ll' .
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            destruct es ; inversion H ; subst ;
            [ values_no_reduce
            | by eapply IHHred0 ].
          destruct bef .
          destruct es ; first empty_list_no_reduce ;
            inversion H ;
            remember (a1 :: es) as es0 ;
            subst a1 ;
            clear Heq0 afte0 H H4 aft H0 IHHred0 ;
            generalize dependent es .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                 assert (const_list (b0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on inner const *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
               try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                    assert (const_list (b0 :: ves)) as Hconst ;
                    first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                    first_not_const Hconst) .
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v1; inversion Heq0);
               try (by destruct v; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ;
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ;
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. }
           rewrite Heq0 in H ;
              simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef ;
                [ destruct es ; first empty_list_no_reduce ;
                  inversion H ; subst ;
                    by eapply IHHred0
                | inversion H ;
                  first_not_const Hvs ].
             destruct bef ; inversion H ;
                 first_not_const Hvs .
              inversion H ;
             first_not_const Hvs.
              destruct bef ; inversion H ;
                subst ; inversion Hvs0 ;
                destruct bef ; inversion H ;
                first_not_const Hvs . }
         get_tail a0 vs0 ys y Htail ;
           rewrite Htail in Hbefs ;
           rewrite app_comm_cons in Hbefs ;
           get_tail a ys ys' y' Htail' ;
           rewrite Htail' in Hbefs ;
           rewrite (separate1 (AI_const _)) in Hbefs ;
           repeat rewrite catA in Hbefs ;
           rewrite assoc_list_seq in Hbefs ;
           apply app_inj_tail in Hbefs as [Hys' ->] ;
           apply app_inj_tail in Hys' as [Hys ->] ;
           rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
           - separate1 separate3 in Heq0 ;
           eexists _, ys', afte0, [], [], _.
           repeat split ; try done ; try (by rewrite app_nil_r) .
            rewrite Htail app_comm_cons Htail' in Hvs0 ;
             unfold const_list in Hvs0 ;
             repeat rewrite forallb_app in Hvs0 ;
             repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
             done.
            by eapply rm_silent, r_simple, rs_pointerdiff_failure.

  (* isnull *)
(* isnull subcase *)
- left ; rewrite (separate1 (AI_const (VAL_pointer p))) in Heq ;
       repeat rewrite app_assoc in Heq ;
       repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
       rewrite - app_comm_cons in Heq ;
        apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
        try (destruct He0 as [-> | ->]; by intros [? ?]);
        try (by const_list_app); rename H into Hr1 .
        destruct vs0 .
(* vs0 empty -> contradiction *)
        { simpl in Heq0 ;
            exfalso ;
            apply Logic.eq_sym in Heq0 ;
            clear Hafts ;
            generalize dependent afte0 .
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
            try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                 assert (const_list (a0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
(* case on non-const head *)
          {  destruct H; try (by inversion Heq0) ;
              try (by destruct v; inversion Heq0);
              try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                   assert (const_list (a0 :: ves)) as Hconst ;
                   first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                   first_not_const Hconst) .
             destruct H ; try (by inversion Heq0) ;
               try (by destruct v; inversion Heq0);
               try (by destruct v1; inversion Heq0);
               try (by destruct vs ; inversion Heq0 ;
                    first_not_const H) ;
               try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
               unfold lfilled, lfill in H0 ;
               destruct lh as [bef aft |] ; last (by false_assumption) ;
               destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
               move/eqP in H0 ;
               rewrite H0 in Heq0 ;
               destruct bef ; inversion Heq0 ;
               first_not_const Hbef. }
           rewrite - Heq0 in H ;
             simple_filled2 H k lh bef aft nn ll ll' .
           destruct bef .
            destruct es ; first empty_list_no_reduce ;
                   inversion H ; subst ;
                     by eapply IHHred0.
             inversion H ;
                   first_not_const Hvs .
              destruct bef ; inversion H ;
                  first_not_const Hvs . }
          get_tail a vs0 ys y Htail ;
            rewrite Htail in Hbefs ;
            repeat rewrite catA in Hbefs ;
            apply app_inj_tail in Hbefs as [Hbefs ->] ;
            rewrite Htail in Heq0 ;
            rewrite - app_assoc in Heq0 ;
            rewrite - separate1 in Heq0 ;
            rewrite separate2 in Heq0 ;
            eexists _, ys, afte0, [], [], _ ;
            repeat split ; try done ; try (by rewrite app_nil_r) ;
            [ rewrite Htail in Hvs0 ;
              unfold const_list in Hvs0 ;
              rewrite forallb_app in Hvs0 ;
              apply andb_true_iff in Hvs0 as [Hys _] ;
                by unfold const_list
            | by eapply rm_silent, r_simple, rs_isnull_false; exact Hr1 ].

            (* demote *)
(* demote subcase *)
            - left ; rewrite (separate1 (AI_const (VAL_pointer p))) in Heq ;
              repeat rewrite app_assoc in Heq ;
              repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
              rewrite - app_comm_cons in Heq ;
              apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
              try (destruct He0 as [-> | ->]; by intros [? ?]);
                  try (by const_list_app); rename H into Hr1 .
                  destruct vs0 .
(* vs0 empty -> contradiction *)
                  { simpl in Heq0 ;
                    exfalso ;
                    apply Logic.eq_sym in Heq0 ;
                    clear Hafts ;
                    generalize dependent afte0 .
                    induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
                    try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                        assert (const_list (a0 :: ves)) as Hconst ;
                        first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                        first_not_const Hconst) .
(* case on non-const head *)
                        {  destruct H; try (by inversion Heq0) ;
                          try (by destruct v; inversion Heq0);
                          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                              assert (const_list (a0 :: ves)) as Hconst ;
                              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                              first_not_const Hconst) .
         destruct H ; try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
           try (by destruct v1; inversion Heq0);
           try (by destruct vs ; inversion Heq0 ;
                first_not_const H) ;
           try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
           unfold lfilled, lfill in H2 ;
           destruct lh as [bef aft |] ; last (by false_assumption) ;
                                  destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
                                  move/eqP in H2 ;
                                  rewrite H2 in Heq0 ;
                                  destruct bef ; inversion Heq0 ;
                                  first_not_const Hbef.
                                  all: rewrite H3 in Heq0 ;
                                  destruct vcs as [| vc vcs'] ; unfold v_to_e_list in Heq0 ; simpl in Heq0 ;
                                      injection Heq0 ; move=> Ht Hh ;
                                      try (by discriminate Hh) ;
                                      destruct vc ; simpl in Hh ;
                                      try (by discriminate Hh) ;
                                      injection Hh ; discriminate .
                        }
                        rewrite - Heq0 in H ;
                         simple_filled2 H k lh bef aft nn ll ll' .
        destruct bef .
          destruct es ; first empty_list_no_reduce ;
                 inversion H ; subst ;
                   by eapply IHHred0.
          inversion H ;
                first_not_const Hvs .
                        destruct bef ; inversion H ;
                        first_not_const Hvs .
                  }
                  get_tail a vs0 ys y Htail ;
                  rewrite Htail in Hbefs ;
                  repeat rewrite catA in Hbefs ;
                  apply app_inj_tail in Hbefs as [Hbefs ->] ;
                  rewrite Htail in Heq0 ;
                  rewrite - app_assoc in Heq0 ;
                  rewrite - separate1 in Heq0 ;
                  rewrite separate2 in Heq0 ;
                  eexists _, ys, afte0, [], [], _ ;
                  repeat split ; try done ; try (by rewrite app_nil_r) ;
                  [ rewrite Htail in Hvs0 ;
                  unfold const_list in Hvs0 ;
                  rewrite forallb_app in Hvs0 ;
                  apply andb_true_iff in Hvs0 as [Hys _] ;
                  by unfold const_list
             | by eapply rm_silent, r_simple, rs_demote; eauto ].

        (* trap *)
(* trap case *)
      - right.
        unfold lfilled, lfill in H0.
        destruct lh as [bef aft|] ; last by false_assumption.
        destruct (const_list bef) eqn:Hbef ; last by false_assumption.
        move/eqP in H0 ; subst es.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]);
          try by const_list_app.
        exists (LH_base vs0 afte0), (LH_base bef aft).
        repeat split => //; unfold lfilled, lfill.
        by rewrite Hvs0 Heq0.
        by rewrite Hbef.

       }
(* invoke native subcase *)
     - left ; repeat rewrite app_assoc in Heq.
       repeat rewrite - (app_assoc (_ ++ _)) in Heq.
       rewrite - app_comm_cons in Heq. 

      apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
        try (by const_list_app ; rewrite Hr3 ; apply v_to_e_is_const_list ).
      cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
(* invoke: bound length vs0 < n *)
      { intros Hnnn. destruct (decide (length vs0 < n)).
        exfalso ; by eapply Hnnn.
        assert (length vs0 >= n) ; first lia.
        rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
        assert (length (drop (length vs0 - n) vs0) = length ves). 
(* drop-length subgoal *)
        { rewrite drop_length. rewrite Hr3 v_to_e_length Hr4. lia. }
        rewrite assoc_list_seq in Hbefs.
        destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
        rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
        rewrite - app_assoc in Heq0.
        rewrite separate1 in Heq0.
        rewrite (app_assoc ves) in Heq0.
        eexists _,(take (length vs0 - n) vs0),afte0,[],[],_;
          repeat split ; try done ; try by rewrite app_nil_r.
        rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
        unfold const_list in Hvs0.
        rewrite forallb_app in Hvs0.
        by apply andb_true_iff in Hvs0 as [? _].
        by eapply rm_silent, r_invoke_native. }
      intros nnn.
      clear Hbefs Hafts.
      generalize dependent afte0.
      generalize dependent vs0.
      generalize dependent es0'.
      generalize dependent es0.
      induction nnn.
      intros ; lia.
      intros es0 es0' Hred.
      induction Hred ; intros afte0 vs0 Hvs0 Heq Hnnn Hlen' ;
        try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by  rewrite - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ;try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
             rewrite H1 ; apply v_to_e_is_const_list).
       destruct H;
        try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by  rewrite - (app_nil_r [_]) in Heq ; 
             apply first_values in Heq as (_ & Habs & _) ;try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ; 
             rewrite H1 ; apply v_to_e_is_const_list) . 
(* invoke: destruct Hred steps *)
       { destruct H ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])).
(* invoke: const-tail values *)
        - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
          unfold const_list, forallb ; by rewrite H.
(* invoke: hole reduction *)
        - unfold lfilled, lfill in H0.
          destruct lh as [bef aft|] ; last by false_assumption.
          destruct (const_list bef) eqn:Hbef ; last by false_assumption.
          move/eqP in H0.
          rewrite H0 in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_native s f _ _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by eapply rm_silent, r_invoke_native.
        by rewrite Hr6.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_native s f _ _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by eapply rm_silent; econstructor.
        by rewrite Hr6.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + simple_filled2 H k0 lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ;
          try (destruct He as [-> | ->]; by intros [? ?]);
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
(* invoke host subcase *)
    - left ; repeat rewrite app_assoc in Heq.
      repeat rewrite - (app_assoc (_ ++ _)) in Heq.
      rewrite - app_comm_cons in Heq. 

      apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
        try (by const_list_app ; rewrite Hr3 ; apply v_to_e_is_const_list ).
      cut (forall nnn, length vs0 < nnn -> length vs0 < n  -> False).
(* invoke: bound length vs0 < n *)
      { intros Hnnn. destruct (decide (length vs0 < n)).
        exfalso ; by eapply Hnnn.
        assert (length vs0 >= n) ; first lia.
        rewrite - (take_drop (length vs0 - n) vs0) in Hbefs.
        assert (length (drop (length vs0 - n) vs0) = length ves). 
(* drop-length subgoal *)
        { rewrite drop_length. rewrite Hr3 v_to_e_length Hr4. lia. }
        rewrite assoc_list_seq in Hbefs.
        destruct (app_inj_2 _ _ _ _ H0 Hbefs) as [Hbefs' Hvss].
        rewrite - (take_drop (length vs0 - n) vs0) Hvss in Heq0.
        rewrite - app_assoc in Heq0.
        rewrite separate1 in Heq0.
        rewrite (app_assoc ves) in Heq0.
        eexists _,(take (length vs0 - n) vs0),afte0,[],[],_;
          repeat split ; try done ; try by rewrite app_nil_r.
        rewrite - (take_drop (length vs0 - n) vs0) in Hvs0.
        unfold const_list in Hvs0.
        rewrite forallb_app in Hvs0.
        by apply andb_true_iff in Hvs0 as [? _].
        by eapply rm_silent; econstructor. }
      intros nnn.
      clear Hbefs Hafts.
      generalize dependent afte0.
      generalize dependent vs0.
      generalize dependent es0'.
      generalize dependent es0.
      induction nnn.
      intros ; lia.
      intros es0 es0' Hred.
      induction Hred ; intros afte0 vs0 Hvs0 Heq Hnnn Hlen' ;
        try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by  rewrite - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ;try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
             rewrite H1 ; apply v_to_e_is_const_list).
      destruct H;
        try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
             apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
        try (by  rewrite - (app_nil_r [_]) in Heq ;
             apply first_values in Heq as (_ & Habs & _) ;try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]) ;
             rewrite H1 ; apply v_to_e_is_const_list).
(* invoke: destruct Hred steps *)
      { destruct H ;
          try (by rewrite - (app_nil_l [_]) - (app_nil_r [_]) in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_ ; _ ; _]) separate2 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])) ;
          try (by rewrite - (app_nil_r [_;_;_;_]) separate3 - app_assoc in Heq ;
               apply first_values in Heq as (_ & Habs & _) ; try done ; try (by simpl; repeat rewrite const_const); try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?])).
(* invoke: const-tail values *)
        - rewrite - (app_nil_r [_ ; _]) separate1 - app_assoc in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).
          unfold const_list, forallb ; by rewrite H.
(* invoke: hole reduction *)
        - unfold lfilled, lfill in H0.
          destruct lh as [bef aft|] ; last by false_assumption.
          destruct (const_list bef) eqn:Hbef ; last by false_assumption.
          move/eqP in H0.
          rewrite H0 in Heq.
          apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]). }
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ; 
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_host s f _ _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by eapply rm_silent; econstructor.
        by rewrite Hr5.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + rewrite - (app_nil_r [_]) in Heq.
        apply first_values in Heq as (-> & Hblock & <-) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
          try (destruct He0 as [-> | ->]; by intros [? ?]).
        eapply (invoke_not_enough_arguments_no_reduce_host s f _ _ _ s f) => //=.
        rewrite Hr2 in Hr1.
        inversion Hblock ; subst a.
        exact Hr1.
        by eapply rm_silent; econstructor.
        by rewrite Hr5.
        rewrite H1.
        by apply v_to_e_is_const_list.
      + simple_filled2 H k lh bef aft nn ll ll'.
        rewrite H in Heq.
        edestruct first_non_value_reduce as (vse & e & afte & Hvse & He & Heqe) ;
          try exact Hred.
        rewrite Heqe in Heq.
        repeat rewrite app_assoc in Heq.
        repeat rewrite - (app_assoc (_ ++ _)) in Heq.
        rewrite - app_comm_cons in Heq.
        apply first_values in Heq as (<- & -> & <-) ; try done ; try (by destruct He ; destruct e => // ; destruct b => //) ; try (destruct He as [-> | ->]; by intros [? ?]);
          try by const_list_app.
        destruct bef.
        eapply IHHred => //=.
        simpl in Hlen', Hnnn.
        rewrite app_length in Hlen', Hnnn.
        eapply IHnnn => //= ; lia.
        rewrite H in Heq.
        apply first_values in Heq as (_ & Habs & _) ; try done ; try (by intros [? ?]); try (destruct He0 as [-> | ->]; by intros [? ?]).  }

    (* To stop messing up the `-` bullets *)
Set Bullet Behavior "Strict Subproofs".

(* colload  *)
   - left ; rewrite (separate1 (AI_const (VAL_pointer p))) in Heq ;
       repeat rewrite app_assoc in Heq ;
       repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
       rewrite - app_comm_cons in Heq ;
       apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
       try (destruct He0 as [-> | ->]; by intros [? ?]);
       rename H into H_all.
       try (by const_list_app).
     destruct vs0 .
(* vs0 empty -> contradiction *)
     { simpl in Heq0 ;
         exfalso ;
         apply Logic.eq_sym in Heq0 ;
         clear Hafts ;
         generalize dependent afte0 .
       induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
         try (by destruct ves as [|a0 ves]; inversion Heq0 ;
              assert (const_list (a0 :: ves)) as Hconst ;
              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
              first_not_const Hconst) .
(* case on non-const head *)
       { destruct H; try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
           try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                assert (const_list (a0 :: ves)) as Hconst ;
                first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                first_not_const Hconst) .
         destruct H ; try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
           try (by destruct v1; inversion Heq0);
           try (by destruct vs ; inversion Heq0 ;
                first_not_const H) ;
           try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
           unfold lfilled, lfill in H2 ;
           destruct lh as [bef aft |] ; last (by false_assumption) ;
           destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
           move/eqP in H2 ;
           rewrite H2 in Heq0 ;
           destruct bef ; inversion Heq0 ;
           first_not_const Hbef.
           all: rewrite H3 in Heq0 ;
           destruct vcs as [| vc vcs'] ; unfold v_to_e_list in Heq0 ; simpl in Heq0 ;
               injection Heq0 ; move=> Ht Hh ;
               try (by discriminate Hh) ;
               destruct vc ; simpl in Hh ;
               try (by discriminate Hh) ;
               injection Hh ; discriminate .
       }
       rewrite - Heq0 in H ;
         simple_filled2 H k lh bef aft nn ll ll' .
       destruct bef .
         destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0.
         inversion H ;
               first_not_const Hvs .
         destruct bef ; inversion H ;
             first_not_const Hvs . }
     get_tail a vs0 ys y Htail ;
       rewrite Htail in Hbefs ;
       repeat rewrite catA in Hbefs ;
       apply app_inj_tail in Hbefs as [Hbefs ->] ;
       rewrite Htail in Heq0 ;
       rewrite - app_assoc in Heq0 ;
       rewrite - separate1 in Heq0 ;
       rewrite separate2 in Heq0 ;
       eexists _, ys, afte0, [], [], _ ;
       repeat split ; try done ; try (by rewrite app_nil_r) ;
       [ rewrite Htail in Hvs0 ;
         unfold const_list in Hvs0 ;
         rewrite forallb_app in Hvs0 ;
         apply andb_true_iff in Hvs0 as [Hys _] ;
           by unfold const_list
       | by eapply rm_colload_success; eauto ].
    by const_list_app.
    by const_list_app; repeat rewrite const_const.

(* colload ptr subcase *)
   - left ; rewrite (separate1 (AI_const (VAL_pointer p))) in Heq ;
       repeat rewrite app_assoc in Heq ;
       repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
       rewrite - app_comm_cons in Heq ;
       apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
       try (destruct He0 as [-> | ->]; by intros [? ?]);
       rename H into H_all.
       try (by const_list_app).
     destruct vs0 .
(* vs0 empty -> contradiction *)
     { simpl in Heq0 ;
         exfalso ;
         apply Logic.eq_sym in Heq0 ;
         clear Hafts ;
         generalize dependent afte0 .
       induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
         try (by destruct ves as [|a0 ves]; inversion Heq0 ;
              assert (const_list (a0 :: ves)) as Hconst ;
              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
              first_not_const Hconst) .
(* case on non-const head *)
       { destruct H; try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
           try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                assert (const_list (a0 :: ves)) as Hconst ;
                first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                first_not_const Hconst) .
           destruct H ; try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
           try (by destruct v1; inversion Heq0);
           try (by destruct vs ; inversion Heq0 ;
                first_not_const H) ;
           try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
            all: try (clear -Heq0 ; case: v0 Heq0 => [p0 | n0] E ;
                      simpl in E ; by discriminate E).
            all: try (rewrite H2 in Heq0 ; destruct vcs as [| vc vcs'] ;
                      unfold v_to_e_list in Heq0 ; simpl in Heq0 ;
                      [ by discriminate Heq0
                      | clear -Heq0 vcs' ;
                        case: vc Heq0 => [p0 | n0] E ; simpl in E ;
                        by discriminate E ]).
            unfold lfilled, lfill in H1 ;
              destruct lh as [bef aft |] ; last (by false_assumption) ;
              destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
              move/eqP in H1 ;
              rewrite H1 in Heq0 ;
              destruct bef ; inversion Heq0 ;
              first_not_const Hbef.
        }
        rewrite - Heq0 in H ;
         simple_filled2 H k lh bef aft nn ll ll' .
       destruct bef .
         destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0.
         inversion H ;
               first_not_const Hvs .
         destruct bef ; inversion H ;
             first_not_const Hvs . }
     get_tail a vs0 ys y Htail ;
       rewrite Htail in Hbefs ;
       repeat rewrite catA in Hbefs ;
       apply app_inj_tail in Hbefs as [Hbefs ->] ;
       rewrite Htail in Heq0 ;
       rewrite - app_assoc in Heq0 ;
       rewrite - separate1 in Heq0 ;
       rewrite separate2 in Heq0 ;
       eexists _, ys, afte0, [], [], _ ;
       repeat split ; try done ; try (by rewrite app_nil_r) ;
       [ rewrite Htail in Hvs0 ;
         unfold const_list in Hvs0 ;
         rewrite forallb_app in Hvs0 ;
         apply andb_true_iff in Hvs0 as [Hys _] ;
           by unfold const_list
        | by eapply rm_colload_ptr_success; eauto ].
     by const_list_app.
     by const_list_app; repeat rewrite const_const.


(*colstore*)
   - left ; rewrite separate2 in Heq ;
       repeat rewrite app_assoc in Heq ;
       repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
       rewrite - app_comm_cons in Heq ;
       apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
       try (destruct He0 as [-> | ->]; by intros [? ?]);
       try (by const_list_app).
     try (rename H into Hbs_all); try (rename H0 into Hbs_map); try (rename H1 into Hv_des); try (rename H2 into Hw_des).
     destruct vs0 .
(* vs0 empty -> contradiction *)
     { simpl in Heq0 ;
         exfalso ;
         apply Logic.eq_sym in Heq0 ;
         clear Hafts ;
         generalize dependent afte0 .
       induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
         try (by destruct ves as [|a0 ves]; inversion Heq0 ;
              assert (const_list (a0 :: ves)) as Hconst ;
              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
              first_not_const Hconst) .
(* case on non-const head *)
       {  destruct H; try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
           try (by destruct ves as [|a0 ves]; inversion Heq0 ;
                assert (const_list (a0 :: ves)) as Hconst ;
                first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                first_not_const Hconst) .
          destruct H ; try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
            try (by destruct v1; inversion Heq0);
            try (by destruct vs ; inversion Heq0 ; first_not_const H) ;
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
            try (inversion Heq0; destruct v0; discriminate).
            all: try (inversion Heq0; destruct v0; discriminate).
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ;
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef. }
        rewrite - Heq0 in H ;
          simple_filled2 H k lh bef aft nn ll ll' .
        destruct bef .
         destruct es ; first empty_list_no_reduce ;
                inversion H ; subst ;
                  by eapply IHHred0.
          inversion H ;
                first_not_const Hvs .
           destruct bef ; inversion H ;
              first_not_const Hvs . }
     destruct vs0 .
(* vs0 one value -> contradiction *)
     { exfalso ;
       clear Hafts ;
       generalize dependent afte0 ;
       induction Hred0 ; intros afte0 Heq0 ;
         try (by inversion Heq0) ;
         try (by destruct v; inversion Heq0);
       try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
            destruct ves as [| b1 ves] ; inversion Heq0 ;
            assert (const_list (b0 :: b1 :: ves)) as Hconst ;
            first (by rewrite H1 ; apply v_to_e_is_const_list) ;
            first_not_const Hconst) .
(* case on head *)
       {  destruct H;
           try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
           try (by destruct ves as [| b0 ves] ; first (by inversion Heq0) ;
                destruct ves as [| b1 ves] ; inversion Heq0 ;
                assert (const_list (b0 :: b1 :: ves)) as Hconst ;
                first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                first_not_const Hconst) .
          destruct H ;
            try (by inversion Heq0) ;
            try (by destruct v2; inversion Heq0);
            try (by destruct vs ; first (by inversion Heq0) ;
                 destruct vs ; inversion Heq0 ;
                 first_not_const H) .
          unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ;
            destruct bef ;
            inversion Heq0 ; subst ;
            inversion Hvs0 ;
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef .
all: inversion Heq0; destruct v0; discriminate.
       }
all: try ( inversion Heq0; destruct v0; discriminate ).
       rewrite Heq0 in H ;
         simple_filled2 H k lh bef aft nn ll ll' .
       destruct bef .
       destruct es ; first empty_list_no_reduce ;
         destruct es ; inversion H ; subst ;
         [ values_no_reduce
         | by eapply IHHred0 ].
       destruct bef .
       destruct es ; first empty_list_no_reduce ;
         inversion H ;
         remember (a1 :: es) as es0 ;
         subst a1 ;
         clear Heq0 afte0 H H4 aft H0 IHHred0 ;
         generalize dependent es .
       induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
         try (by destruct ves as [|b0 ves]; inversion Heq0 ;
              assert (const_list (b0 :: ves)) as Hconst ;
              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
              first_not_const Hconst) .
(* case on inner const *)
       {  destruct H; try (by inversion Heq0) ;
           try (by destruct v; inversion Heq0);
            try (by destruct ves as [|b0 ves]; inversion Heq0 ;
                 assert (const_list (b0 :: ves)) as Hconst ;
                 first (by rewrite H1 ; apply v_to_e_is_const_list) ;
                 first_not_const Hconst) .
          destruct H ; try (by inversion Heq0) ;
            try (by destruct v; inversion Heq0);
            try (by destruct v1; inversion Heq0);
            try (by destruct vs ; inversion Heq0 ;
                 first_not_const H) ;
            try (by inversion Heq0 ; subst ; simpl in H ; false_assumption) .
all: try (inversion Heq0; destruct v0; discriminate).
            unfold lfilled, lfill in H0 ;
            destruct lh as [bef aft |] ; last (by false_assumption) ;
            destruct (const_list bef) eqn:Hbef ; last (by false_assumption) ;
            move/eqP in H0 ;
            rewrite H0 in Heq0 ;
            destruct bef ; inversion Heq0 ;
            first_not_const Hbef. }
        rewrite Heq0 in H ;
           simple_filled2 H k lh bef aft nn ll ll' .
        destruct bef ;
             [ destruct es ; first empty_list_no_reduce ;
               inversion H ; subst ;
                 by eapply IHHred0
             | inversion H ;
               first_not_const Hvs ].
         destruct bef ; inversion H ;
             first_not_const Hvs .
          inversion H ;
         first_not_const Hvs.
          destruct bef ; inversion H ;
            subst ; inversion Hvs0 ;
            destruct bef ; inversion H ;
            first_not_const Hvs . }
     get_tail a0 vs0 ys y Htail ;
       rewrite Htail in Hbefs ;
       rewrite app_comm_cons in Hbefs ;
       get_tail a ys ys' y' Htail' ;
       rewrite Htail' in Hbefs ;
       rewrite (separate1 (AI_const _)) in Hbefs ;
       repeat rewrite catA in Hbefs ;
       rewrite assoc_list_seq in Hbefs ;
       apply app_inj_tail in Hbefs as [Hys' ->] ;
       apply app_inj_tail in Hys' as [Hys ->] ;
       rewrite Htail app_comm_cons Htail' - app_assoc - separate1 - app_assoc
       - separate1 separate3 in Heq0 ;
       eexists _, ys', afte0, [], [], _.
       repeat split ; try done ; try (by rewrite app_nil_r) .
        rewrite Htail app_comm_cons Htail' in Hvs0 ;
         unfold const_list in Hvs0 ;
         repeat rewrite forallb_app in Hvs0 ;
         repeat apply andb_true_iff in Hvs0 as [Hvs0 _] ;
         done.
        by eapply rm_colstore_success; eauto.
clear -Hbef1.
unfold const_list; unfold const_list in Hbef1.
rewrite forallb_app.
rewrite Hbef1.
destruct v; by simpl.




     (* colalloc *)
   - left ; rewrite (separate1 (AI_basic (BI_const (NVAL_int32 n)))) in Heq ;
     repeat rewrite app_assoc in Heq ;
     repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
     rewrite - app_comm_cons in Heq ;
     apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
     try (destruct He0 as [-> | ->]; by intros [? ?]); rename H into H_all.
          destruct vs0 .
          { exfalso.
            simpl in Heq0. apply Logic.eq_sym in Heq0.
          clear Hafts.
          generalize dependent afte0.
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
              assert (const_list (a0 :: ves)) as Hconst ;
              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
              first_not_const Hconst) .
          {
            destruct H; try (by inversion Heq0).
          rewrite cats0 in Hbefs.
          destruct H.
          all: try (inversion Heq0; destruct v; by []).
          all: try (inversion Heq0; destruct v1; by []).
          all: try (destruct vs; [ discriminate | inversion Heq0; first_not_const H ] ).
          all: try (by inversion Heq0; unfold is_const in H; rewrite <- H1 in H).
          unfold lfilled, lfill in H0; destruct lh.
          case Lconst: (const_list l); rewrite Lconst in H0.
          subst es; move /eqP in H0; destruct l.
          all : try by [].
          inversion H0; first_not_const Lconst.
          all: destruct vcs; [ simpl in *; subst; inversion Heq0 |
              destruct ves; [ simpl in *; subst; inversion Heq0 |
                  rewrite cats0 in Hbefs; simpl in *; subst; inversion H1;
                  inversion Heq0; subst a0; destruct v; discriminate H5
                  ]].
          }
          rewrite cats0 in Hbefs.
          simpl in *; subst.
          destruct k.
          {
          unfold lfilled, lfill in H; destruct lh.
          case Hl : (const_list l); rewrite Hl in H.
          move /eqP in H; destruct l.
          all : try by []; simpl in H.
          destruct es; simpl in H.
          destruct l0; inversion H.
          simpl in *; subst.
          inversion Hred0. inversion H1. inversion H9; simpl in *; subst.
          all: try( destruct vs; discriminate).
          unfold lfilled, lfill in H17; destruct lh; [
          case Hl': (const_list l); rewrite Hl' in H17 ; move /eqP in H17; [
          destruct l; discriminate | by [] ] | by [] ].
          simpl in *; subst; destruct vcs; discriminate.
          simpl in *; subst; destruct vcs; discriminate.
          apply (empty_no_reduce s f me s' f' es'); exact Hred0.
          inversion H. subst; simpl in *.
          move: H0. move/lfilledP => Hfill.
          inversion Hfill => //=.
          simpl in *. subst.
          inversion Hred0; subst.
          inversion H0; subst.
          inversion H1; subst.
          all: try (destruct v; discriminate).
          all: try (destruct v1; discriminate).
          all: try (destruct vs; [ inversion H3 | inversion H3; first_not_const H4 ] ).
          inversion H6.
          move: H4. move/lfilledP => Hfill'.
          inversion Hfill' => //=.
          simpl in *; subst.
          destruct vs; [ inversion H4 | inversion H4; first_not_const H5 ].
          1-2: destruct vcs ; [ discriminate | simpl in H1; inversion H1; destruct v; inversion H5 ].
          eapply IHHred0; [ exact IHnnnn | reflexivity | reflexivity | reflexivity ].
          inversion H. first_not_const Hl.
          }
          unfold lfilled, lfill in H.
          destruct lh as [l l0 | l n0 l0 l1 l2]; first by [].
          case Hl : (const_list l); rewrite Hl in H; last by [].
          fold lfill in H.
          destruct (lfill k l1 es) eqn:Hfill'; last by [].
          move /eqP in H.
          destruct l as [| a l']; first by (simpl in H; discriminate).
          simpl in H; inversion H; first_not_const Hl.
      }
     get_tail a vs0 ys y Htail .
       rewrite Htail in Hbefs .
       repeat rewrite catA in Hbefs .
       apply app_inj_tail in Hbefs as [Hbefs ->] .
       rewrite Htail in Heq0 .
       rewrite - app_assoc in Heq0 .
       rewrite - separate1 in Heq0 .
       rewrite separate2 in Heq0 .
       eexists _, ys, afte0, [], [], _ .
       repeat split ; try done ; try (by rewrite app_nil_r) .
        rewrite Htail in Hvs0 .
         unfold const_list in Hvs0 .
         rewrite forallb_app in Hvs0 .
         apply andb_true_iff in Hvs0 as [Hys _] .
           by unfold const_list.
       eapply rm_colalloc_success; eauto.
    by const_list_app.
    by const_list_app; repeat rewrite const_const.




(* colalloc failure *)
   - left ; rewrite (separate1 (AI_basic (BI_const (NVAL_int32 n)))) in Heq ;
     repeat rewrite app_assoc in Heq ;
     repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
     rewrite - app_comm_cons in Heq ;
     apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
     try (destruct He0 as [-> | ->]; by intros [? ?]).
          destruct vs0 .
          { exfalso.
            simpl in Heq0. apply Logic.eq_sym in Heq0.
          clear Hafts.
          generalize dependent afte0.
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
              assert (const_list (a0 :: ves)) as Hconst ;
              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
              first_not_const Hconst) .
          {
            destruct H; try (by inversion Heq0).
          rewrite cats0 in Hbefs.
          destruct H.
          all: try (inversion Heq0; destruct v; by []).
          all: try (inversion Heq0; destruct v1; by []).
          all: try (destruct vs; [ discriminate | inversion Heq0; first_not_const H ] ).
          all: try (by inversion Heq0; unfold is_const in H; rewrite <- H1 in H).
          unfold lfilled, lfill in H0; destruct lh.
          case Lconst: (const_list l); rewrite Lconst in H0.
          subst es; move /eqP in H0; destruct l.
          all : try by [].
          inversion H0; first_not_const Lconst.
          all: destruct vcs; [ simpl in *; subst; inversion Heq0 |
              destruct ves; [ simpl in *; subst; inversion Heq0 |
                  rewrite cats0 in Hbefs; simpl in *; subst; inversion H1;
                  inversion Heq0; subst a0; destruct v; discriminate H5
                  ]].
          }
          rewrite cats0 in Hbefs.
          simpl in *; subst.
          destruct k.
          {
          unfold lfilled, lfill in H; destruct lh.
          case Hl : (const_list l); rewrite Hl in H.
          move /eqP in H; destruct l.
          all : try by []; simpl in H.
          destruct es; simpl in H.
          destruct l0; inversion H.
          simpl in *; subst.
          inversion Hred0. inversion H1. inversion H9; simpl in *; subst.
          all: try( destruct vs; discriminate).
          unfold lfilled, lfill in H17; destruct lh; [
          case Hl': (const_list l); rewrite Hl' in H17 ; move /eqP in H17; [
          destruct l; discriminate | by [] ] | by [] ].
          simpl in *; subst; destruct vcs; discriminate.
          simpl in *; subst; destruct vcs; discriminate.
          apply (empty_no_reduce s f me s' f' es'); exact Hred0.
          inversion H. subst; simpl in *.
          move: H0. move/lfilledP => Hfill.
          inversion Hfill => //=.
          simpl in *. subst.
          inversion Hred0; subst.
          inversion H0; subst.
          inversion H1; subst.
          all: try (destruct v; discriminate).
          all: try (destruct v1; discriminate).
          all: try (destruct vs; [ inversion H3 | inversion H3; first_not_const H4 ] ).
          inversion H6.
          move: H4. move/lfilledP => Hfill'.
          inversion Hfill' => //=.
          simpl in *; subst.
          destruct vs; [ inversion H4 | inversion H4; first_not_const H5 ].
          1-2: destruct vcs ; [ discriminate | simpl in H1; inversion H1; destruct v; inversion H5 ].
          eapply IHHred0.
          eapply IHnnnn.
          reflexivity. reflexivity.
          instantiate (1:=es). reflexivity.
          inversion H. first_not_const Hl.
          }
          unfold lfilled, lfill in H.
          destruct lh as [l l0 | l n0 l0 l1 l2]; first by [].
          case Hl : (const_list l); rewrite Hl in H; last by [].
          fold lfill in H.
          destruct (lfill k l1 es) eqn:Hfill'; last by [].
          move /eqP in H.
          destruct l as [| a l']; first by (simpl in H; discriminate).
          simpl in H; inversion H; first_not_const Hl.
      }
     get_tail a vs0 ys y Htail .
       rewrite Htail in Hbefs .
       repeat rewrite catA in Hbefs .
       apply app_inj_tail in Hbefs as [Hbefs ->] .
       rewrite Htail in Heq0 .
       rewrite - app_assoc in Heq0 .
       rewrite - separate1 in Heq0 .
       rewrite separate2 in Heq0 .
       eexists _, ys, afte0, [], [], _ .
       repeat split ; try done ; try (by rewrite app_nil_r) .
        rewrite Htail in Hvs0 .
         unfold const_list in Hvs0 .
         rewrite forallb_app in Hvs0 .
         apply andb_true_iff in Hvs0 as [Hys _] .
           by unfold const_list.
       eapply rm_colalloc_failure. eauto. eauto.
    by const_list_app.
    by const_list_app; repeat rewrite const_const.

(* colfree *)
   - left ; rewrite (separate1 (AI_const (VAL_pointer p))) in Heq ;
     repeat rewrite app_assoc in Heq ;
     repeat rewrite - (app_assoc (_ ++ _)) in Heq ;
     rewrite - app_comm_cons in Heq ;
     apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ;
     try (destruct He0 as [-> | ->]; by intros [? ?]).
     rename H into Hupd. rename s' into s_r.
          destruct vs0 .
          { exfalso.
            simpl in Heq0. apply Logic.eq_sym in Heq0.
          clear Hafts.
          generalize dependent afte0.
          induction Hred0 ; intros afte0 Heq0 ; try (by inversion Heq0) ;
          try (by destruct ves as [|a0 ves]; inversion Heq0 ;
              assert (const_list (a0 :: ves)) as Hconst ;
              first (by rewrite H1 ; apply v_to_e_is_const_list) ;
              first_not_const Hconst) .
          {
            destruct H; try (by inversion Heq0).
          rewrite cats0 in Hbefs.
          destruct H.
          all: try (inversion Heq0; destruct v; by []).
          all: try (inversion Heq0; destruct v1; by []).
          all: try (destruct vs; [ discriminate | inversion Heq0; first_not_const H ] ).
          all: try (by inversion Heq0; unfold is_const in H; rewrite <- H1 in H).
          unfold lfilled, lfill in H0; destruct lh.
          case Lconst: (const_list l); rewrite Lconst in H0.
          subst es; move /eqP in H0; destruct l.
          all : try by [].
          inversion H0; first_not_const Lconst.
          all: destruct vcs; [ simpl in *; subst; inversion Heq0 |
              destruct ves; [ simpl in *; subst; inversion Heq0 |
                  rewrite cats0 in Hbefs; simpl in *; subst; inversion H1;
                  inversion Heq0; subst a0; destruct v; discriminate H5
                  ]].
          }
          rewrite cats0 in Hbefs.
          simpl in *; subst.
          destruct k.
          {
          unfold lfilled, lfill in H; destruct lh.
          case Hl : (const_list l); rewrite Hl in H.
          move /eqP in H; destruct l.
          all : try by []; simpl in H.
          destruct es; simpl in H.
          destruct l0; inversion H.
          simpl in *; subst.
          inversion Hred0. inversion H1. inversion H9; simpl in *; subst.
          all: try( destruct vs; discriminate).
          unfold lfilled, lfill in H17; destruct lh; [
          case Hl': (const_list l); rewrite Hl' in H17 ; move /eqP in H17; [
          destruct l; discriminate | by [] ] | by [] ].
          simpl in *; subst; destruct vcs; discriminate.
          simpl in *; subst; destruct vcs; discriminate.
          apply (empty_no_reduce s f me s' f' es'); exact Hred0.
          inversion H. subst; simpl in *.
          move: H0. move/lfilledP => Hfill.
          inversion Hfill => //=.
          simpl in *. subst.
          inversion Hred0; subst.
          inversion H0; subst.
          inversion H1; subst.
          all: try (destruct v; discriminate).
          all: try (destruct v1; discriminate).
          all: try (destruct vs; [ inversion H3 | inversion H3; first_not_const H4 ] ).
          inversion H6.
          move: H4. move/lfilledP => Hfill'.
          inversion Hfill' => //=.
          simpl in *; subst.
          destruct vs; [ inversion H4 | inversion H4; first_not_const H5 ].
          1-2: destruct vcs ; [ discriminate | simpl in H1; inversion H1; destruct v; inversion H5 ].
          eapply IHHred0.
          eapply IHnnnn.
          all: try reflexivity.
          inversion H. first_not_const Hl.
          }
          unfold lfilled, lfill in H.
          destruct lh as [l l0 | l n0 l0 l1 l2]; first by [].
          case Hl : (const_list l); rewrite Hl in H; last by [].
          fold lfill in H.
          destruct (lfill k l1 es) eqn:Hfill'; last by [].
          move /eqP in H.
          destruct l as [| a l']; first by (simpl in H; discriminate).
          simpl in H; inversion H; first_not_const Hl.
      }
     get_tail a vs0 ys y Htail .
       rewrite Htail in Hbefs .
       repeat rewrite catA in Hbefs .
       apply app_inj_tail in Hbefs as [Hbefs ->] .
       rewrite Htail in Heq0 .
       rewrite - app_assoc in Heq0 .
       rewrite - separate1 in Heq0 .
       rewrite separate2 in Heq0 .
       eexists _, ys, afte0, [], [], _ .
       repeat split ; try done ; try (by rewrite app_nil_r) .
        rewrite Htail in Hvs0 .
         unfold const_list in Hvs0 .
         rewrite forallb_app in Hvs0 .
         apply andb_true_iff in Hvs0 as [Hys _] .
           by unfold const_list.
       eapply rm_colfree_success; eauto.
    by const_list_app.
    by const_list_app; repeat rewrite const_const.

(* AI_trap? *)
   - unfold lfilled, lfill in Hr2.
      destruct k.
      { destruct lh as [bef aft|] ; last by false_assumption.
        destruct (const_list bef) eqn:Hbef ; last by false_assumption.
        move/eqP in Hr2.
        destruct bef.
        destruct aft.
        unfold lfilled, lfill in Hr3 ; simpl in Hr3, Hr2.
        repeat rewrite app_nil_r in Hr3, Hr2.
        move/eqP in Hr3.
        subst.
        by eapply IHHred.
        edestruct IHnnnn as [(core & bc0 & ac0 & bc1 & ac1 & core' & Hbc0 & Hbc1 &
                                Hes0 & Hes & Hbefs & Hafts & Hredcore & Hcore') |
                              (lh0 & lh1 & Hfill0 & Hfill1 & Hσ)].
        exact Hbef1.
        exact Hred0.
        exact Hr1.
        subst.
        rewrite Heq.
        simpl.
        repeat rewrite app_assoc.
        rewrite - (app_assoc (_ ++ _)).
        done.
        rewrite Hr2 in Hlen.
        simpl in Hlen.
        rewrite app_length in Hlen.
        simpl in Hlen.
        lia.
        left.
        eexists core,bc0,ac0,bc1,(ac1 ++ (a :: aft)),core'.
        repeat split => //=.
        rewrite Hr2 Hes.
        simpl.
        repeat rewrite app_assoc.
        done.
        by rewrite - app_assoc.
        repeat rewrite app_assoc.
        rewrite - (app_assoc bc1).
        rewrite Hcore'.
        unfold lfilled, lfill in Hr3 ; simpl in Hr3.
        move/eqP in Hr3.
        by rewrite Hr3.
        right.
        assert (lfilled 0 (LH_base [] (a :: aft)) es les).
        unfold lfilled, lfill => //= ; by rewrite Hr2.
        destruct (lfilled_trans Hfill1 H) as [lh' Hfilltrap].
        eexists _,_ ; split => //=.
        edestruct IHnnnn as [(core & bc0 & ac0 & bc1 & ac1 & core' & Hbc0 & Hbc1 &
                                Hes0 & Hes & Hbefs & Hafts & Hredcore & Hcore') |
                              (lh0 & lh1 & Hfill0 & Hfill1 & Hσ)].
        instantiate (1 := (bef1 ++ a :: bef)).
        by const_list_app.
        exact Hred0.
        exact Hr1.
        instantiate (1 := (aft ++ aft1)).
        subst.
        rewrite Heq.
        simpl.
        repeat rewrite - app_assoc.
        done.
        rewrite Hr2 in Hlen.
        simpl in Hlen.
        repeat rewrite app_length in Hlen.
        simpl in Hlen.
        lia.
        left.
        eexists core,bc0,ac0,(a :: bef ++ bc1),(ac1 ++ aft),core'.
        repeat split => //.
        rewrite app_comm_cons.
        by const_list_app.
        rewrite Hr2 Hes.
        simpl.
        repeat rewrite app_assoc.
        done.
        rewrite Hbefs.
        repeat rewrite - app_assoc.
        done.
        rewrite Hafts.
        by rewrite - app_assoc.
        rewrite app_comm_cons.
        repeat rewrite - app_assoc.
        rewrite (app_assoc bc1).
        rewrite (app_assoc (bc1 ++ core')).
        rewrite - (app_assoc bc1).
        rewrite Hcore'.
        unfold lfilled, lfill in Hr3.
        rewrite Hbef in Hr3.
        move/eqP in Hr3.
        by rewrite Hr3.
        right.
        assert (lfilled 0 (LH_base (a :: bef) aft) es les).
        unfold lfilled, lfill ; by rewrite Hbef Hr2.
        destruct (lfilled_trans Hfill1 H) as [lh' Hfilltrap].
        eexists _,_ ; split => //=.  }
      fold lfill in Hr2.
      destruct lh ; first by false_assumption.
      destruct (const_list l) eqn:Hl ; last by false_assumption.
      destruct (lfill k lh es) eqn:Hfill ; last by false_assumption.
      move/eqP in Hr2.
      rewrite Hr2 in Heq.
      repeat rewrite app_assoc in Heq.
      repeat rewrite - (app_assoc (_ ++ _)) in Heq.
      repeat rewrite - app_comm_cons in Heq.
      apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ; try (destruct He0 as [-> | ->]; by intros [? ?]);
        try by const_list_app.
      unfold lfilled, lfill in Hr3 ; fold lfill in Hr3.
      rewrite Hl in Hr3.
      destruct (lfill k lh es') eqn : Hfill' ; last by false_assumption.
      left ; eexists [AI_label n l0 l2], vs0, afte0, l, l1, _.
      repeat split => //=.
      eapply rm_label.
      exact Hr1.
      instantiate (1 := LH_rec [] n l0 lh []).
      instantiate (1 := S k).
      unfold lfilled, lfill ; fold lfill => //=.
      rewrite Hfill.
      done.
      unfold lfilled, lfill ; fold lfill => //=.
      rewrite Hfill'.
      done.
      by move/eqP in Hr3.
  Qed.

End reduction_core.
