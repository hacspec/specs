Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.

From JasminSSProve Require Import jasmin_translate.
From Crypt Require Import Prelude Package pkg_composition.
From Crypt Require Import Axioms. (* proof_irrelevance *)
From extructures Require Import ord fset fmap.
Import PackageNotation.

#[global] Hint Resolve preceq_I preceq_O preceq_refl : preceq.

Definition pdisj (P : precond) (s_id : p_id) (rhs : {fset Location}) :=
  (forall h1 h2 l a v s_id', l = translate_var s_id' v -> (s_id ⪯ s_id') -> (P (h1, h2) -> P (set_heap h1 l a, h2))) /\
    (forall h1 h2 l a, l \in rhs -> (P (h1, h2) -> P (h1, set_heap h2 l a))).

(* From Crypt Require Import choice_type Package Prelude. *)

Require Import Hacspec_ovn_Schnorr_Random_oracle.

Require Import SigmaProtocol.
Require Import DDH.

Require Import Hacspec_ovn_Schnorr.

Require Import Schnorr.

Require Import Hacspec_ovn.

From Hacspec Require Import ChoiceEquality.
(* From Hacspec Require Import Hacspec_Lib_Pre. *)
From Hacspec Require Import Hacspec_Lib.

Module Schnorr_eq (GP : GroupParam).
  Import GP.
  Module Sigma1 := Schnorr GP.
  Module RO1 := Sigma1.Sigma.Oracle.

  Check both_prog.

  (* Check (chProd Sigma1.MyAlg.choiceStatement Sigma1.MyAlg.choiceWitness). *)
  Locate choiceTranscript.

  Definition Schnorr_translate_type (x : Sigma1.MyAlg.choiceStatement × Sigma1.MyAlg.choiceWitness) : t_Relation :=
    (Hacspec_Lib_Pre.repr _ (word.modulus (nat_of_ord (fst x))),
      Hacspec_Lib_Pre.repr _ (word.modulus (nat_of_ord (snd x) ))).

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

  Ltac remove_get_in_lhs :=
    eapply better_r_get_remind_lhs ;
    unfold Remembers_lhs , rem_lhs ;
    [ intros ? ? ? ;
      destruct_pre ;
      repeat (rewrite get_set_heap_neq ; [ | apply injective_translate_var3 ; reflexivity ]) ;
      rewrite get_set_heap_eq ;
      reflexivity | ].

  From Crypt Require Import Axioms.

  Check proof_irrelevance.

  Lemma both_eq : forall {A : choice_type} {L I} (a b : both L I A),
      both_prog a = both_prog b ->
      a = b.
  Proof.
    intros.
    destruct a , b.
    cbn in *. subst.
    f_equal ; apply proof_irrelevance.
  Qed.

  Lemma bind_ret_both : forall {A B : choice_type} {L I} `{fsubset_loc : is_true (fsubset (fset [::]) L)} `{fsubset_opsig : is_true (fsubset (fset [::]) I)} (f : A -> both L I B) (x : A),
      (bind_both (fsubset_loc := fsubset_loc) (fsubset_opsig := fsubset_opsig) (ret_both x) f) = f x.
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
  
  Theorem Schnorr_eq_proof id0 (pre : precond)  :
    forall (hw : (Sigma1.MyAlg.choiceStatement × Sigma1.MyAlg.choiceWitness)),
    (pdisj pre id0 (fset0)) ->
    ⊢ ⦃ pre ⦄
        is_state (both_prog (fiat_shamir_run (ret_both (Schnorr_translate_type hw))))
        ≈
        get_op_default (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO) (Sigma1.Sigma.RUN, ((chProd Sigma1.MyAlg.choiceStatement Sigma1.MyAlg.choiceWitness), Sigma1.MyAlg.choiceTranscript)) hw
        ⦃ fun '(v0, h0) '(v1, h1) => pre (h0, h1) ⦄.
  Proof.
    intros.
    
    (* Unfolding and simplifying to raw code! *)
    (* TODO: Work on higher level than raw code? *)
    
    rewrite get_op_default_link.
    erewrite get_op_default_spec.
    2: {
      cbn.
      done.
    }
    ssprove_code_simpl.

    rewrite fiat_shamir_run_equation_1.
    destruct hw.

    ssprove_code_simpl.
    ssprove_code_simpl_more.

    unfold let_both at 1.

    unfold prod_to_prod_n at 1 ; fold @prod_to_prod_n ; rewrite prod_to_prod_equation_1 ; rewrite !bind_ret_both ; simpl.
    unfold Schnorr_translate_type ; simpl.
    rewrite v_Commit_equation_1.

    unfold Build_t_G at 1.

    
    unfold is_state , both_prog.
    rewrite !let_both_equation_1.
    unfold both_prog.
    rewrite !prod_both_equation_1.
    setoid_rewrite bind_assoc.
    setoid_rewrite bind_assoc.
    setoid_rewrite bind_assoc.
    setoid_rewrite bind_assoc.
    (* unfold is_state, ret_both, lift_both, both_prog, bind_both, bind_raw_both. *)

    (* Actual proof *)

    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ ?x ≈ assertD ?b ?f ⦃ ?Q ⦄ ] ] =>
        change x with (assertD true (fun _ => x)) ;
        apply (r_assertD true b pre _ (fun _ => x))
    end.
    {
      intros.
      admit.
    }
    intros.
    
    match goal with
    | [ |- context [ ⊢ ⦃ ?P ⦄ bind ?a ?f ≈ pkg_core_definition.sampler ?x ?y ⦃ ?Q ⦄ ] ] =>
        set (a) ; set (f) ; set (x) ; set (y)
    end.
    Check pkg_core_definition.sampler o.
    pose (Arit o).
    cbn in t.
    pose Sigma1.MyAlg.i_witness.
    cbn in n.
    
    assert (s1 : forall (x : Arit o), commit_loc).
    { clear. intros.
      apply (Schnorr_translate_type).
      split.
      (* apply (Hacspec_Lib_Pre.repr _ (word.modulus 1%nat)). *)
      2:{
        apply x.
      }.
      admit.
    }
    replace (x ← r ;; r0 _) with (x ← sample o ;; r0 (s1 x)) by admit.
    apply r_uniform_bij with (f := id).
    {
      apply injF_bij.
      apply inj_id.
    }
    intros.
    subst r0 r1.
    hnf.

    
    Set Printing Coercions.
    Unset Printing Notations.
    
    pose (r_bind).
    
    apply r_bind.
    
    bind_jazz_bind.
    
    
    
    apply r_assertR.
    r_assertR.
    
    rewrite bind_assoc.
    rewrite bind_assoc.

    r_assertR.

    ssprove_sync_eq.

    
Require Import OVN.

(* Exec_i_realised *)
(* {package (Exec_i i j m) ∘ (par ((P_i i b) ∘ (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) *)
(*                                       (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO))} *)

