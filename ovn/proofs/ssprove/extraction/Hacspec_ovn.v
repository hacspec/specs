(* File automatically generated by Hacspec *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import ssrZ word.
From Jasmin Require Import word.

From Coq Require Import ZArith.
From Coq Require Import Strings.String.
   Import List.ListNotations.
Open Scope list_scope.
Open Scope Z_scope.
Open Scope bool_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.

Open Scope hacspec_scope.
Import choice.Choice.Exports.

Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

(** Tool: prelude_import _  **)

(** Tool: macro_use _  **)
(*Not implemented yet? todo(item)*)

Require Import Core.
Export Core.

Require Import Hacspec_lib.
Export Hacspec_lib.

Require Import Creusot_contracts.
Export Creusot_contracts.

(** DocComment:  Interface for group implementation  **)
Class t_Group (Self : choice_type) := {
  t_group_type : choice_type ;
  t_group_type_t_Group :> t_Group (t_group_type) ;
  q : forall {L0 I0}, both L0 I0 (uint_size) ;
  g : forall {L0 I0}, both L0 I0 (t_group_type) ;
  g_pow : forall {L0 I0}, both L0 I0 (uint_size) -> both L0 I0 (t_group_type) ;
  pow : forall {L0 L1 I0 I1}, both L0 I0 (t_group_type) -> both L1 I1 (uint_size) -> both (L0 :|: L1) (I0 :|: I1) (t_group_type) ;
  one : forall {L0 I0}, both L0 I0 (t_group_type) ;
  prod : forall {L0 L1 I0 I1}, both L0 I0 (t_group_type) -> both L1 I1 (t_group_type) -> both (L0 :|: L1) (I0 :|: I1) (t_group_type) ;
  div : forall {L0 L1 I0 I1}, both L0 I0 (t_group_type) -> both L1 I1 (t_group_type) -> both (L0 :|: L1) (I0 :|: I1) (t_group_type) ;
  random_element : forall {L0 I0}, both L0 I0 (t_group_type) ;
}.

(** DocComment:  number of parties  **)
Equations n : both (fset []) ([interface ]) (uint_size) :=
  n  :=
    solve_lift (ret_both (3 : uint_size)) : both (fset []) ([interface ]) (uint_size).
Fail Next Obligation.

(** Tool: cfg _ not(simple_test)
DocComment:  Currently randomness needs to be injected  **)
Equations select_private_voting_key {G : _} `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {I1 : Interface} (random : both L1 I1 (uint_size)) : both (L1) (I1) (uint_size) :=
  select_private_voting_key random  :=
    solve_lift (random .% q) : both (L1) (I1) (uint_size).
Fail Next Obligation.

(** DocComment:  TODO: Non-interactive Schnorr proof using Fiat-Shamir heuristics  **)
Equations v_ZKP {G : _} `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {I1 : Interface} (xi : both L1 I1 (uint_size)) : both (L1) (I1) (uint_size) :=
  v_ZKP xi  :=
    solve_lift (ret_both (0 : uint_size)) : both (L1) (I1) (uint_size).
Fail Next Obligation.

(** DocComment:  State of bulletin board  **)
Equations get_broadcast1 : both (fset []) ([interface ]) ((t_Vec (uint_size) (t_Global) × t_Vec (uint_size) (t_Global))) :=
  get_broadcast1  :=
    solve_lift (prod_b (new_under_impl,new_under_impl)) : both (fset []) ([interface ]) ((t_Vec (uint_size) (t_Global) × t_Vec (uint_size) (t_Global))).
Fail Next Obligation.

Equations check_valid {L1 : {fset Location}} {I1 : Interface} (zkp : both L1 I1 (uint_size)) : both (L1) (I1) ('bool) :=
  check_valid zkp  :=
    solve_lift (ret_both (true : 'bool)) : both (L1) (I1) ('bool).
Fail Next Obligation.

Equations broadcast1 {G : _} `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (xi : both L1 I1 (t_group_type)) (zkp : both L2 I2 (uint_size)) (i : both L3 I3 (uint_size)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit) :=
  broadcast1 xi zkp i  :=
    solve_lift (ret_both (tt : 'unit)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit).
Fail Next Obligation.

(** DocComment:  Primary function in round 1  **)
Equations register_vote_pre {G : _} `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (i : both L1 I1 (uint_size)) (random : both L2 I2 (uint_size)) : both (L1:|:L2) (I1:|:I2) (uint_size) :=
  register_vote_pre i random  :=
    letb xi := select_private_voting_key random :of: uint_size in
    letb _ := broadcast1 (g_pow xi) (v_ZKP xi) i :of: 'unit in
    letb _ := ret_both (tt : 'unit) :of: 'unit in
    solve_lift xi : both (L1:|:L2) (I1:|:I2) (uint_size).
Fail Next Obligation.

(** DocComment:  Primary function in round 1  **)
Definition prod1_loc {G : _} `{ t_Sized (G)} `{ t_Group (G)} : Location :=
  (t_group_type ; 0%nat).
Equations register_vote_post {G : _} `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (i : both L1 I1 (uint_size)) (gs : both L2 I2 (t_Vec (uint_size) (t_Global))) (zkps : both L3 I3 (t_Vec (uint_size) (t_Global))) : both (L1:|:L2:|:L3 :|: fset [prod1_loc]) (I1:|:I2:|:I3) (t_group_type) :=
  register_vote_post i gs zkps  :=
    letb _ := foldi_both_list (into_iter zkps) (fun {L I _ _} =>fun zkp =>
        ssp (fun _ =>
          letb _ := check_valid zkp :of: 'bool in
          solve_lift (ret_both (tt : 'unit)))) (ret_both (tt : 'unit)) :of: 'unit in
    letbm prod1 loc(prod1_loc) := (one) : both _ _ (t_group_type) in
    letb prod1 := foldi_both_list (into_iter (Build_t_Range  (ret_both (0 : uint_size)) (i .- (ret_both (1 : uint_size))))) (fun {L I _ _} =>fun j =>
        ssp (fun prod1 =>
          solve_lift (prod prod1 (g_pow (gs.a[j]))))) prod1 :of: t_group_type in
    letb prod2 := one :of: t_group_type in
    letb prod1 := foldi_both_list (into_iter (Build_t_Range  (i .+ (ret_both (1 : uint_size))) n)) (fun {L I _ _} =>fun j =>
        ssp (fun prod1 =>
          solve_lift (prod prod1 (g_pow (gs.a[j]))))) prod1 :of: t_group_type in
    solve_lift (div prod1 prod2) : both (L1:|:L2:|:L3 :|: fset [prod1_loc]) (I1:|:I2:|:I3) (t_group_type).
Fail Next Obligation.

(** DocComment:  Cramer, Damgård and Schoenmakers (CDS) technique  **)
Equations v_ZKP_one_out_of_two {L1 : {fset Location}} {I1 : Interface} (vi : both L1 I1 ('bool)) : both (L1) (I1) (uint_size) :=
  v_ZKP_one_out_of_two vi  :=
    solve_lift (ret_both (32 : uint_size)) : both (L1) (I1) (uint_size).
Fail Next Obligation.

Equations broadcast2 {G : _} `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (g_pow_xiyi : both L1 I1 (t_group_type)) (g_pow_vi : both L2 I2 (t_group_type)) (g_pow_vi_zkp : both L3 I3 (uint_size)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit) :=
  broadcast2 g_pow_xiyi g_pow_vi g_pow_vi_zkp  :=
    solve_lift (ret_both (tt : 'unit)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit).
Fail Next Obligation.

Equations get_broadcast2 {G : _} `{ t_Sized (G)} `{ t_Group (G)} : both (fset []) ([interface ]) ((t_Vec (t_group_type) (t_Global) × t_Vec (t_group_type) (t_Global) × t_Vec (uint_size) (t_Global))) :=
  get_broadcast2  :=
    solve_lift (prod_b (new_under_impl,new_under_impl,new_under_impl)) : both (fset []) ([interface ]) ((t_Vec (t_group_type) (t_Global) × t_Vec (t_group_type) (t_Global) × t_Vec (uint_size) (t_Global))).
Fail Next Obligation.

(** DocComment:  Primary function in round 2  **)
Equations cast_vote {G : _} `{ t_Sized (G)} `{ t_Group (G)} {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (xi : both L1 I1 (uint_size)) (Yi : both L2 I2 (t_group_type)) (vi : both L3 I3 ('bool)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit) :=
  cast_vote xi Yi vi  :=
    letb _ := broadcast2 (pow Yi xi) (g_pow (ifb vi
      then ret_both (1 : uint_size)
      else ret_both (0 : uint_size))) (v_ZKP_one_out_of_two vi) :of: 'unit in
    letb _ := ret_both (tt : 'unit) :of: 'unit in
    solve_lift (ret_both (tt : 'unit)) : both (L1:|:L2:|:L3) (I1:|:I2:|:I3) ('unit).
Fail Next Obligation.

(** DocComment:  Anyone can tally the votes  **)
Definition vote_result_loc {G : _} `{ t_Sized (G)} `{ t_Group (G)} : Location :=
  (t_group_type ; 2%nat).
Definition tally_loc {G : _} `{ t_Sized (G)} `{ t_Group (G)} : Location :=
  (uint_size ; 1%nat).
Equations tally_votes {G : _} `{ t_Sized (G)} `{ t_Group (G)} : both (fset [tally_loc; vote_result_loc]) ([interface ]) (uint_size) :=
  tally_votes  :=
    letb '(g_pow_xi_yi,g_pow_vi,zkps) := get_broadcast2 :of: (t_Vec (t_group_type) (t_Global) × t_Vec (t_group_type) (t_Global) × t_Vec (uint_size) (t_Global)) in
    letb _ := foldi_both_list (into_iter zkps) (fun {L I _ _} =>fun zkp =>
        ssp (fun _ =>
          letb _ := check_valid zkp :of: 'bool in
          solve_lift (ret_both (tt : 'unit)))) (ret_both (tt : 'unit)) :of: 'unit in
    letbm vote_result loc(vote_result_loc) := (one) : both _ _ (t_group_type) in
    letb vote_result := foldi_both_list (into_iter (Build_t_Range  (ret_both (0 : uint_size)) (len_under_impl_1 g_pow_vi))) (fun {L I _ _} =>fun i =>
        ssp (fun vote_result =>
          solve_lift (prod vote_result (prod (clone (g_pow_xi_yi.a[i])) (clone (g_pow_vi.a[i])))))) vote_result :of: t_group_type in
    letbm tally loc(tally_loc) := (ret_both (0 : uint_size)) : both _ _ (uint_size) in
    letb tally := foldi_both_list (into_iter (Build_t_Range  (ret_both (1 : uint_size)) n)) (fun {L I _ _} =>fun i =>
        ssp (fun tally =>
          solve_lift (ifb (g_pow i) =.? vote_result
          then letb tally := i :of: uint_size in
            tally
          else tally))) tally :of: uint_size in
    solve_lift tally : both (fset [tally_loc; vote_result_loc]) ([interface ]) (uint_size).
Fail Next Obligation.

Definition t_votes : choice_type :=
  (nseq 'bool 3).
Equations Build_t_votes {L : {fset Location}} {I : Interface} (f_elems : both L I (nseq 'bool 3)) : both L I (t_votes) :=
  Build_t_votes f_elems  :=
    bind_both f_elems (fun f_elems =>
      solve_lift (ret_both ((f_elems) : (t_votes)))) : both L I (t_votes).
Fail Next Obligation.

Definition t_randomness : choice_type :=
  (nseq uint_size 3).
Equations Build_t_randomness {L : {fset Location}} {I : Interface} (f_elems : both L I (nseq uint_size 3)) : both L I (t_randomness) :=
  Build_t_randomness f_elems  :=
    bind_both f_elems (fun f_elems =>
      solve_lift (ret_both ((f_elems) : (t_randomness)))) : both L I (t_randomness).
Fail Next Obligation.
