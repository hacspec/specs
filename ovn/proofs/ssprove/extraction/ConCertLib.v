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

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.
From Hacspec Require Import Hacspec_Lib.

From Coq Require Import Morphisms ZArith.
From Coq Require Import List.
Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

(* From QuickChick Require Import QuickChick. *)
(* Require Import QuickChickLib. *)

From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import Blockchain.

(* Require Import Hacspec_Concordium. *)
(* Export Hacspec_Concordium. *)

Global Program Instance int_serializable {ws : wsize} : Serializable (int ws) :=
  {| serialize m := (serialize (unsigned m)) ;
    deserialize l := option_map (fun (x : Z) => @repr ws x) (deserialize l) |}.
Next Obligation.
  intros. hnf. rewrite deserialize_serialize.
  unfold option_map. now rewrite wrepr_unsigned.
Defined.

(* Global Program Instance nseq_serializable len : Serializable (nseq int8 len) := *)
(*   {| serialize m := (serialize (nat_from_be_bytes m)) ; *)
(*     deserialize l := option_map (fun (x : nat) => nat_to_be_bytes x) (deserialize l) |}. *)
(* Next Obligation. *)
(*   intros. cbn. rewrite deserialize_serialize. cbn. rewrite nat_to_from_be_bytes. reflexivity. *)
(* Defined. *)

(* Global Program Instance nseq_countable len : countable.Countable (nseq int8 len) := *)
(* {| *)
(*     countable.encode := fun X : nseq int8 _ => countable.encode (nat_from_be_bytes X); *)
(*     countable.decode := fun H : positive => option_map (@nat_to_be_bytes _) (countable.decode H : option nat); *)
(* |}. *)
(* Next Obligation. *)
(*   intros. *)
(*   rewrite countable.decode_encode. *)
(*   cbn. *)
(*   now rewrite nat_to_from_be_bytes. *)
(* Qed. *)

Instance BaseTypes : ChainBase := {|
    Address := int32;
    address_eqb := Hacspec_Lib_Comparable.eqb ;
    address_eqb_spec := Hacspec_Lib_Comparable.eqbP ;
    (* address_eqdec x y := (EqDecIsDecidable x y); *)
    address_countable := (* nseq_countable *) _;
    address_serializable := (* nseq_serializable *) _;
    address_is_contract := (fun x => Nat.even ((* nat_from_be_bytes x *) Z.to_nat (unsigned x))); |}.

(* Definition context_t_from_context (ctx : ContractCallContext) : context_t := *)
(*   (ctx.(ctx_from), ctx.(ctx_origin), repr (ctx.(ctx_amount))). *)

(* Definition accept (ctx : ContractCallContext) := act_transfer ctx.(ctx_origin) ctx.(ctx_amount). *)

(* Definition has_action_t := ActionBody. *)

(* Definition action_body_t := ActionBody. *)
(* Definition list_action_t := list ActionBody. *)
(* Definition ACT_TRANSFER (p : Address ∏ int64) := act_transfer (fst p) (unsigned (snd p)).   *)
(* Instance d_ab : Default ActionBody := {| default := act_transfer (array_new_ (default : int8) 32) 0 |}. *)

(* Program Definition to_action_body (ctx : ContractCallContext) (y : has_action_t) : ActionBody := *)
(*   match y with *)
(*   | (Accept _) => act_transfer (ctx.(ctx_from)) (ctx.(ctx_amount)) *)
(*   | (SimpleTransfer (ua, i)) => act_transfer (ua) (i) *)
(*   | (SendRaw (ua, receive_name, amount, data)) => *)
(*       act_call (ua) (amount) (list_rect (fun _ : list int8 => SerializedValue) *)
(*                                         (build_ser_value ser_unit tt) *)
(*                                         (fun a _ IHdata => *)
(*                                            build_ser_value *)
(*                                              (ser_pair ser_int (ser_value_type IHdata)) *)
(*                                              (unsigned a, ser_value IHdata)) *)
(*                                         data) *)
(*   end. *)
(* Instance default_has_action : Default has_action_t := {| default := Accept tt |}. *)

(* Global Instance serializable_has_action_t : Serializable has_action_t := *)
(*   Derive Serializable has_action_t_rect<Accept,SimpleTransfer,SendRaw>. *)
(* Global Instance show_has_action_t : Show (has_action_t) := *)
(*  @Build_Show (has_action_t) (fun x => *)
(*  match x with *)
(*  Accept a => ("Accept" ++ show a)%string *)
(*  | SimpleTransfer a => ("SimpleTransfer" ++ show a)%string *)
(*  | SendRaw a => ("SendRaw" ++ show a)%string *)
(*  end). *)
(* Definition g_has_action_t : G (has_action_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (Accept a))) [bindGen arbitrary (fun a => returnGen (Accept a));bindGen arbitrary (fun a => returnGen (SimpleTransfer a))]. *)
(* Global Instance gen_has_action_t : Gen (has_action_t) := Build_Gen has_action_t g_has_action_t. *)

(* Definition to_action_body_list (ctx : ContractCallContext) {X} (k : option (X ∏ list has_action_t)) : ResultMonad.result (X ∏ list ActionBody) unit  := *)
(*   match (option_map (fun '(x, y) => (x, List.map (to_action_body ctx) y)) k) with *)
(*     Some a => ResultMonad.Ok a *)
(*   | None => ResultMonad.Err tt *)
(*   end. *)


(* Instance show_user_address_t : Show (user_address_t) := Build_Show (user_address_t) show. *)
(* Definition g_user_address_t : G (user_address_t) := arbitrary. *)
(* Instance gen_user_address_t : Gen (user_address_t) := Build_Gen user_address_t g_user_address_t. *)

(* Global Instance serializable_context_t : Serializable context_t := *)
(*   Derive Serializable context_t_rect<Context>. *)
(* Global Instance show_context_t : Show (context_t) := *)
(*  @Build_Show (context_t) (fun x => *)
(*  match x with *)
(*  Context a => ("Context" ++ show a)%string *)
(*  end). *)
(* Definition g_context_t : G (context_t) := oneOf_ (bindGen arbitrary (fun a => returnGen (Context a))) [bindGen arbitrary (fun a => returnGen (Context a))]. *)
(* Global Instance gen_context_t : Gen (context_t) := Build_Gen context_t g_context_t. *)
