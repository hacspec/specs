Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.

(* From JasminSSProve Require Import jasmin_translate. *)
From Crypt Require Import Prelude Package pkg_composition.
From extructures Require Import ord fset fmap.
Import PackageNotation.
From Coq Require Import ZArith.
(* #[global] Hint Resolve preceq_I preceq_O preceq_refl : preceq. *)

Definition pdisj (P : precond) (* (s_id : p_id) *) (rhs : {fset Location}) :=
  (forall h1 h2 l a (* v *) (* s_id' *), (* l = translate_var s_id' v -> (s_id ⪯ s_id') -> *) (P (h1, h2) -> P (set_heap h1 l a, h2))) /\
    (forall h1 h2 l a, l \in rhs -> (P (h1, h2) -> P (h1, set_heap h2 l a))).

(* From Crypt Require Import choice_type Package Prelude. *)
From Crypt Require Import Axioms.

(* Require Import Hacspec_ovn_Schnorr_Random_oracle. *)

Require Import SigmaProtocol.
Require Import DDH.

(* Require Import Hacspec_ovn_Schnorr. *)
Require Import Schnorr.

Require Import Hacspec_ovn.
Require Import OVN.

From Hacspec Require Import ChoiceEquality.
(* From Hacspec Require Import Hacspec_Lib_Pre. *)
From Hacspec Require Import Hacspec_Lib.

Module Schnorr_eq (GP : GroupParam)  (OP : OVNParam).
  Import GP.
  Module Sigma1 := Schnorr GP.
  Module RO1 := Sigma1.Sigma.Oracle.

  Check both_prog.

  (* Check (chProd Sigma1.MyAlg.choiceStatement Sigma1.MyAlg.choiceWitness). *)
  Locate choiceTranscript.

  Notation mymod := (4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787)%Z.
  Axiom mymod_is_statement : Z.to_nat mymod = #|Sigma1.MyParam.Statement|.

  Notation mymod2 := (9574)%Z.
  Axiom mymod2_is_statement : Z.to_nat mymod2 = #|Sigma1.MyParam.Witness|.
  
  Definition Schnorr_translate_type (x : Sigma1.MyAlg.choiceStatement × Sigma1.MyAlg.choiceWitness) : t_Relation.
  Proof.
    refine (cast_ord _ (fst x), cast_ord _ (snd x)).
    unfold pos.
    rewrite mymod_is_statement.
    symmetry.
    eapply prednK.
    apply Sigma1.MyParam.positive_gT.

    rewrite mymod2_is_statement.
    symmetry.
    eapply prednK.
    apply Sigma1.MyParam.Witness_pos.
  Defined.

  Ltac destruct_pre :=
    repeat
      match goal with
      | [ H : set_lhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : set_rhs _ _ _ _ |- _ ] =>
          let sn := fresh in
          let Hsn := fresh in
          destruct H as [sn [Hsn]]
      | [ H : _ /\ _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : (_ ⋊ _) _ |- _ ] =>
          let H1 := fresh in
          let H2 := fresh in
          destruct H as [H1 H2]
      | [ H : exists _, _ |- _ ] =>
          let o := fresh in
          destruct H as [o]
      end; simpl in *; subst.

  (* Ltac remove_get_in_lhs := *)
  (*   eapply better_r_get_remind_lhs ; *)
  (*   unfold Remembers_lhs , rem_lhs ; *)
  (*   [ intros ? ? ? ; *)
  (*     destruct_pre ; *)
  (*     repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ; *)
  (*     rewrite get_set_heap_eq ; *)
  (*     reflexivity | ]. *)

  Definition uniform_secret (x : Arit (uniform (H := Sigma1.MyParam.Witness_pos) #|Sigma1.MyParam.Witness|)) : t_Secret.
  Proof.
    simpl in x.
    
    refine (cast_ord _ x).
    rewrite mymod2_is_statement.
    simpl.
    symmetry.
    eapply prednK.
    apply Sigma1.MyParam.Witness_pos.
  Defined.    
    (* Hacspec_Lib_Pre.repr _ (word.modulus (nat_of_ord x)). *)

  Theorem random_sample (pre : precond) :
    forall i `{Positive i},
    exists (random_val : Arit (uniform i)),
      ⊢ ⦃ pre ⦄
          x ← sample uniform i ;; ret x ≈ ret random_val
                                      ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) ⦄.
  Proof.
    intros.
    eexists.
    apply (r_const_sample_L _ (fun x => ret x) _).
    apply LosslessOp_uniform.
    intros.
    apply r_ret.
    intros.
    apply H0.
    Unshelve.
    refine (Ordinal (n:={| pos := i; cond_pos := H |}) (m := 0) _).
    easy.
  Qed.

  (* Definition cast_type (x : (chProd (chProd (chProd t_G t_G) t_Q) t_Q)) : (tgt *)
  (*            (@pair ident (prod choice_type choice_type) Sigma1.Sigma.RUN *)
  (*               (@pair choice_type choice_type *)
  (*                  (chProd Sigma1.MyAlg.choiceStatement *)
  (*                     Sigma1.MyAlg.choiceWitness) *)
  (*                  Sigma1.MyAlg.choiceTranscript))). *)
  (* Proof. *)
  (*   destruct x as [[[]]]. *)
  (*   repeat split. *)
  (*   refine (Ordinal (m := Z.to_nat (Hacspec_Lib_Pre.unsigned s)) _). *)
  (*   simpl. *)
Theorem better_rsame_head_cmd_alt :
  forall {A B C : choiceType} {f₀  : A -> raw_code B}  {f₁ : A -> raw_code C}
    (m : command A) pre (post : postcond B C),
    ⊢ ⦃ pre ⦄
      x ← cmd m ;; ret x ≈ x ← cmd m ;; ret x
    ⦃ fun '(a₀, s₀) '(a₁, s₁) => pre (s₀, s₁) /\ a₀ = a₁ ⦄ ->
    (forall a, ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) ->
    ⊢ ⦃ pre ⦄ x ← cmd m ;; f₀ x ≈ x ← cmd m ;; f₁ x ⦃ post ⦄.
Proof.
  intros A B C f₀ f₁ m pre post hm hf.
  eapply from_sem_jdg. rewrite !repr_cmd_bind.
  eapply (RulesStateProb.bind_rule_pp (repr_cmd m) (repr_cmd m)).
  - eapply to_sem_jdg in hm. rewrite !repr_cmd_bind in hm.
    rewrite bindrFree_ret in hm. eauto.
  - intros a₀ a₁. eapply to_sem_jdg.
    eapply rpre_hypothesis_rule.
    intros s₀ s₁ [h e]. subst.
    eapply rpre_weaken_rule. 1: eapply hf.
    simpl. intros ? ? [? ?]. subst. auto.
Qed.
    
  Lemma better_r_const_sample_R :
  forall {A B : choiceType} (op : Op) c₀ c₁ (pre : precond) (post : postcond A B),
    LosslessOp op ->
    (forall x, ⊢ ⦃ pre ⦄ c₀ ≈ c₁ x ⦃ post ⦄) ->
    ⊢ ⦃ pre ⦄ c₀ ≈ x ← sample op ;; c₁ x ⦃ post ⦄.
Proof.
  intros A B op c₀ c₁ pre post hop h.
  eapply r_transL with (x ← sample op ;; (fun _ => c₀) x).
  - apply r_dead_sample_L. 1: auto.
    apply rreflexivity_rule.
  - apply (better_rsame_head_cmd_alt (cmd_sample op)).
    + eapply rpre_weaken_rule. 1: eapply cmd_sample_preserve_pre.
      auto.
    + apply h.
Qed.

  (* Ltac solve_var_neq := *)
  (*   ((now apply injective_translate_var3) || *)
  (*            (apply injective_translate_var2 ; red ; intros ; subst)). *)
  (* Ltac eexists_set_heap := *)
  (*   eexists ; split ; [ | *)
  (*   match goal with *)
  (*   | [ |- context [ *)
  (*             set_heap _ _ ?d *)
  (*             = set_heap _ _ ?d *)
  (*     ] ] => *)
  (*       reflexivity *)
  (*   end || *)
  (*       match goal with *)
  (*       | [ |- context [ *)
  (*                 set_heap ?a ?b ?c *)
  (*                 = set_heap _ _ ?e *)
  (*         ] ] => *)
  (*           rewrite [set_heap a b c]set_heap_commut ; [ reflexivity | *)
  (*           solve_var_neq ] *)
  (*       end]. *)

  Ltac solve_in :=
    repeat match goal with
           | |- is_true (?v \in fset1 ?v :|: _) => apply/fsetU1P; left; auto
           | |- is_true (_ \in fsetU _ _) => apply/fsetU1P; right
           end.

  Ltac pdisj_apply h :=
    lazymatch goal with
    | |- ?pre (set_heap _ _ _, set_heap _ _ _) => eapply h; [ solve_in | pdisj_apply h ]
    | |- ?pre (set_heap _ _ _, _) =>
        eapply h ; [ reflexivity | auto with preceq | pdisj_apply h ]
    | |- _ => try assumption
    end.


  Ltac solve_in_fset :=
    rewrite in_fset ; repeat (reflexivity || (rewrite mem_head) || (now rewrite Bool.orb_true_r) || (now rewrite Bool.orb_true_l) || rewrite in_cons ; simpl).

  Theorem unfold_prod0 :
    forall L I A (x : both L I A), prod_to_prod_n 0 x = x.
  Proof. destruct A ; reflexivity. Qed.

  Lemma bind_solve_lift_ret_both : forall {A B : choice_type} {L1 L2 I1 I2} `{fsubset_loc : is_true (fsubset (fset [::]) L1)} `{fsubset_opsig : is_true (fsubset (fset [::]) I1)} `{fsubset_loc2 : is_true (fsubset L1 L2)} `{fsubset_opsig2 : is_true (fsubset I1 I2)} (f : A -> both L2 I2 B) (x : A),
      (bind_both (L1 := L1)  (I1 := I1) (fsubset_loc := fsubset_loc2) (fsubset_opsig := fsubset_opsig2) (lift_both (fsubset_loc := fsubset_loc) (fsubset_opsig := fsubset_opsig) (ret_both x)) f) = f x.
  Proof.
    intros.
    apply both_eq.
    simpl.
    unfold bind_raw_both.
    simpl.
    destruct (f x). simpl.
    destruct both_prog. simpl.
    reflexivity.
  Qed.

  Lemma bind_solve_both_assoc :
    forall {A B : choice_type} {L1 L2 I1 I2} (f : A -> both L2 I2 B) (x : A) `{fsubset_loc : is_true (fsubset (fset [::]) L1)} `{fsubset_opsig : is_true (fsubset (fset [::]) I1)} `{fsubset_loc2 : is_true (fsubset L1 L2)} `{fsubset_opsig2 : is_true (fsubset I1 I2)},
      (bind_both (fsubset_loc := fsubset_loc2) (fsubset_opsig := fsubset_opsig2) (lift_both (L2 := L1) (I2 := I1) (fsubset_loc := fsubset_loc) (fsubset_opsig := fsubset_opsig) (ret_both x)) f) =
      (bind_both (fsubset_loc := fsubset_trans fsubset_loc fsubset_loc2) (fsubset_opsig := fsubset_trans fsubset_opsig fsubset_opsig2) (ret_both x) f).
  Proof.
    intros.
    apply both_eq.
    simpl.
    unfold bind_raw_both.
    simpl.
    destruct (f x). simpl.
    destruct both_prog. simpl.
    reflexivity.
  Qed.

  Theorem unfold_letb'2 :
    forall L1 L2 I1 I2 A B C,
    forall (z : both L1 I1 (A × B)) (f : _ -> both L2 I2 C),
    forall `{fsubset_loc1 : is_true (fsubset (fset [::]) L1)} `{fsubset_opsig1 : is_true (fsubset (fset [::]) I1)},
    forall `{fsubset_loc2 : is_true (fsubset L1 L2)} `{fsubset_opsig2 : is_true (fsubset I1 I2)},
      is_state (lift_n (fsubset_loc := fsubset_loc2) (fsubset_opsig := fsubset_opsig2) 1 z f) =
        ('(x, y) ← is_state z ;; is_state (f (lift_both (fsubset_loc := fsubset_loc1) (fsubset_opsig := fsubset_opsig1) (ret_both x) : both _ _ A, lift_both (fsubset_loc := fsubset_loc1) (fsubset_opsig := fsubset_opsig1) (ret_both y) : both _ _ B))).
  Proof.
    intros.
    unfold lift_n at 1.
    simpl.

    f_equal.
    apply functional_extensionality.
    intros [].

    rewrite unfold_prod0.

    rewrite <- surjective_pairing.
    set (prod_to_prod _).
    set (solve_lift _, solve_lift _).
    replace p with p0 ; [ reflexivity | subst p p0 ].

    unfold prod_to_prod at 1.

    rewrite bind_solve_both_assoc.
    rewrite bind_solve_both_assoc.

    rewrite bind_ret_both.
    rewrite bind_ret_both.

    simpl.

    f_equal.
    f_equal.
    apply proof_irrelevance.
    apply proof_irrelevance.
    f_equal.
    f_equal.
    apply proof_irrelevance.
    apply proof_irrelevance.
  Qed.
  
  Theorem Schnorr_eq_proof (* id0 *) (pre : precond)  :
    forall (hw : (Sigma1.MyAlg.choiceStatement × Sigma1.MyAlg.choiceWitness)),
    forall (H_pdisj : pdisj pre (* id0 *) (fset [ :: RO1.queries_loc ; Sigma1.MyAlg.commit_loc ])),
      forall (* exists *) (random_sample1 : Arit (uniform (H := Sigma1.MyParam.Witness_pos) Sigma1.MyAlg.i_witness)) random_sample2,
    ⊢ ⦃ pre ⦄
        is_state (both_prog (fiat_shamir_run (ret_both (Schnorr_translate_type hw)) (ret_both (uniform_secret random_sample1)) (ret_both random_sample2)))
        ≈
        get_op_default (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO) (Sigma1.Sigma.RUN, ((chProd Sigma1.MyAlg.choiceStatement Sigma1.MyAlg.choiceWitness), Sigma1.MyAlg.choiceTranscript)) hw
        ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) ⦄.
  Proof.
    intros.
    (* eexists. *)
    (* eexists. *)

    (* Unfolding and simplifying to raw code! *)
    (* TODO: Work on higher level than raw code? *)

    rewrite get_op_default_link.
    erewrite get_op_default_spec.
    2: {cbn. done.}
    ssprove_code_simpl.
    destruct hw.
    hnf.
    rewrite fiat_shamir_run_equation_1.
    
    ssprove_code_simpl.
    ssprove_code_simpl_more.

    (* Ltac get_next_statement := _. *)
    unfold let_both at 1.
    rewrite unfold_letb'2.
    rewrite bind_rewrite.
    destruct Schnorr_translate_type eqn:So.
    unfold let_both at 1.
    unfold let_both at 1.
    unfold let_both at 1.
    unfold let_both at 1.
    unfold let_both at 1.
    rewrite unfold_letb'2.
    
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?x ≈ assertD ?b ?f ⦃ ?Q ⦄ ] ] =>
        change x with (assertD true (fun _ => x)) ;
        apply (r_assertD true b pre _ (fun _ => x))
    end.
    {
      clear -So.
      intros.
      apply pair_equal_spec in So.
      destruct So.
      
      eapply (@f_equal _ _ (cast_ord (esym _)) _ _) in H0.
      erewrite cast_ordK in H0.
      unfold fst in H0.
      rewrite H0 ; clear H0.

      eapply (@f_equal _ _ (cast_ord (esym _)) _ _) in H1.
      erewrite cast_ordK in H1.
      unfold snd in H1.
      rewrite H1 ; clear H1.
      clear.

      destruct s1 , s2.
      cbn.
      unfold cast_ord.


      unfold Sigma1.MyParam.R.
      cbn.
      pose nth_ord_enum.
      unfold enum.
      cbn.
      simpl.
      setoid_rewrite nth_ord_enum.
      admit.
    }
    intros _ ?.
    apply (better_r_const_sample_R) ; [ apply LosslessOp_uniform | intros ].

    unfold random_oracle_query at 1.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.

    apply better_r_put_rhs.
    apply better_r_put_get_rhs.
    apply better_r_put_rhs.

    rewrite emptymE.

    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    rewrite bind_assoc.
    rewrite bind_assoc.

    (* Sample *)
    apply (better_r_const_sample_R) ; [ apply LosslessOp_uniform | intros ].
    rewrite bind_rewrite.

    unfold is_state at 1, both_prog at 1.
    unfold bind ; fold @bind.
    apply better_r_put_get_lhs.
    apply better_r_put_lhs.

    rewrite bind_rewrite.
    rewrite bind_rewrite.

    unfold prod_to_prod_n at 1 ; fold @prod_to_prod_n.
    rewrite bind_rewrite.
    rewrite bind_rewrite.

    rewrite emptymE.
    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    apply better_r_put_rhs.

    apply better_r.
    apply r_get_remind_rhs with (v := x).
    {
      unfold Remembers_rhs  , rem_rhs.
      intros ? ? ?.
      clear -H.
      destruct_pre.
      rewrite get_set_heap_neq ; [ | easy ].
      rewrite get_set_heap_neq ; [ | easy ].
      rewrite get_set_heap_eq. reflexivity.
    }
    apply better_r.

    repeat (rewrite !bind_assoc ; rewrite bind_rewrite).
    unfold is_state at 1, both_prog at 1.
    unfold bind ; fold @bind.

    apply better_r_put_get_lhs.
    apply better_r_put_lhs.

    rewrite bind_rewrite.
    rewrite bind_rewrite.

    unfold prod_to_prod_n at 1 ; fold @prod_to_prod_n.

    rewrite bind_rewrite.
    rewrite bind_assoc.
    rewrite bind_rewrite.
    rewrite bind_rewrite.
    unfold prod_to_prod_n at 1 ; fold @prod_to_prod_n.
    rewrite !unfold_prod0.
    rewrite bind_assoc.
    rewrite bind_assoc.
    rewrite bind_rewrite. 
    rewrite bind_rewrite. 
    rewrite bind_assoc.
    rewrite bind_rewrite. 
    rewrite bind_rewrite. 

    unfold prod_both at 1.
    unfold prod_both at 1.
    unfold prod_both at 1.
    unfold is_state.
    setoid_rewrite bind_assoc.
    setoid_rewrite bind_assoc.
    setoid_rewrite bind_assoc.
    setoid_rewrite bind_assoc.
    rewrite bind_rewrite.
    unfold both_prog at 1 , is_state at 1.
    unfold bind ; fold @bind.

    apply better_r_put_get_lhs.
    apply better_r_put_lhs.

    rewrite bind_rewrite.
    rewrite bind_rewrite.


    rewrite bind_assoc.
    rewrite bind_rewrite.
    rewrite bind_rewrite.
    apply r_ret.

    intros.

    clear -H H_pdisj.
    destruct_pre.

    repeat apply H_pdisj.
    - solve_in_fset.
    - solve_in_fset.
    - solve_in_fset.
    - assumption.

      Unshelve.
      all: intros ? ? ? ? ; apply proof_irrelevance.
  Admitted.

  Definition Schnorr_translate_type2 (x : Sigma1.MyAlg.choiceTranscript) : t_Transcript.
  Proof.
    destruct x as [[[]]].
    refine (cast_ord _ s, cast_ord _ s0, cast_ord _ s1, cast_ord _ s2).
    unfold pos.
    rewrite mymod_is_statement.
    symmetry.
    eapply prednK.
    apply Sigma1.MyParam.positive_gT.

    unfold pos.
    rewrite mymod_is_statement.
    symmetry.
    eapply prednK.
    apply Sigma1.MyParam.positive_gT.

    rewrite mymod2_is_statement.
    symmetry.
    eapply prednK.
    apply Sigma1.MyParam.Witness_pos.

    rewrite mymod2_is_statement.
    symmetry.
    eapply prednK.
    apply Sigma1.MyParam.Witness_pos.
  Defined.

  Module OVN_mod := OVN GP OP.
  Import OVN_mod.
  Module OVN_proof (π2 : CDSParams) (Alg2 : SigmaProtocolAlgorithms π2).
  Module OVN_OVN_mod := OVN π2 Alg2.
  Import OVN_OVN_mod.

  Theorem Schnorr__eq_proof (* id0 *) (pre : precond)  :
    forall (hw : Sigma1.MyAlg.choiceTranscript),
    forall (H_pdisj : pdisj pre (* id0 *) (fset [ :: RO1.queries_loc ; Sigma1.MyAlg.commit_loc ])),
      (* forall i b, *)
      forall (* exists *) (random_sample1 : Arit (uniform _)),
    ⊢ ⦃ pre ⦄
        is_state (both_prog (fiat_shamir_verify (ret_both (Schnorr_translate_type2 hw)) (ret_both (uniform_secret random_sample1))))
        ≈
        get_op_default ((Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) (Sigma1.Sigma.VERIFY, ((Sigma1.MyAlg.choiceTranscript, 'bool))) hw
        ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) ⦄.
  Proof.
        intros.
    (* eexists. *)
    (* eexists. *)

    (* Unfolding and simplifying to raw code! *)
    (* TODO: Work on higher level than raw code? *)

    rewrite get_op_default_link.
    erewrite get_op_default_spec.
    2: {cbn. done.}
    ssprove_code_simpl.
    destruct hw as [[[]]].
    hnf.
    rewrite fiat_shamir_verify_equation_1.
    
    ssprove_code_simpl.
    ssprove_code_simpl_more.

    (* setoid_rewrite bind_rewrite. *)

    unfold prod_to_prod_n at 1 ; fold @prod_to_prod_n ; rewrite !unfold_prod0.
    autorewrite with let_both.
    autorewrite with prod_to_prod.
    rewrite prod_assoc_equation_1.
    
    rewrite !bind_ret_both.

    rewrite !bind_solve_both_assoc.
    rewrite !bind_ret_both.
    rewrite !bind_solve_both_assoc.
    rewrite !bind_ret_both.
    
    unfold fst, snd.

    unfold Schnorr_translate_type2.

    unfold prod_to_prod_n at 2 ; fold @prod_to_prod_n.

    (* Unset Printing Notations. *)
    (* Set Printing Coercions. *)
    match goal with
    | |- context [let 'pair _ _ := prod_to_prod_n 1 ?b in ?x] =>
        pose (is_state (both_prog (let 'pair _ _ := prod_to_prod_n 1 b in x)));
        pose ('(_, _) ← is_state (both_prog b) ;; is_state (both_prog x))
        ; set (b) ; set (x)
    end.

    epose (is_state (both_prog b) ;; _).

    epose (_ ← (is_state b) ;; _).

    assert (forall L1 I1 A B L2 I2 C (b : both L1 I1 (A × B)) (x : both L2 I2 C),
               is_state (letb '(_, _) := b in x) =
              '(_, _) ← is_state b ;; is_state x).
    {
      clear.
      intros.
      destruct b.
      destruct both_prog_valid.
      simpl.
      inversion is_valid_code.
      - simpl.
        destruct x0.
        reflexivity.
      - simpl.
        
      

    
    replace (is_state (both_prog (let 'pair _ _ := prod_to_prod_n 1 b in b0)))
      with
      ('(_, _) ← (is_state b) ;; is_state b0).
    2:{
      clear.
      destruct b.
      destruct both_prog.
      unfold both_prog.
      unfold ChoiceEquality.is_state.
      destruct is_state.
      
      
    change (is_state b0) with
       ('(_, _) ← (is_state b) ;; is_state b0).
    
    unfold prod_to_prod_n at 1 ; fold @prod_to_prod_n.
    
    (* TODO, Sub proofs: *)
    rewrite random_oracle_query_equation_1.
    (* TODO, verify proofs: *)
    rewrite verify_equation_1.

    rewrite prod_both_equation_1.
    

    setoid_rewrite bind_rewrite.

    
    


  
(* Exec_i_realised *)
(* {package (Exec_i i j m) ∘ (par ((P_i i b) ∘ (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) *)
(*                                       (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO))} *)
