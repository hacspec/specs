(* File automatically generated by Hacspec *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset.
From mathcomp Require Import word_ssrZ word.
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

Definition t_LogError : choice_type :=
  ('unit ∐ 'unit).
Notation "'LogError_Full_case'" := (inl tt) (at level 100).
Equations LogError_Full {L : {fset Location}} {I : Interface} : both L I (t_LogError) :=
  LogError_Full  :=
    solve_lift (ret_both (inl (tt : 'unit) : t_LogError)) : both L I (t_LogError).
Fail Next Obligation.
Notation "'LogError_Malformed_case'" := (inr tt) (at level 100).
Equations LogError_Malformed {L : {fset Location}} {I : Interface} : both L I (t_LogError) :=
  LogError_Malformed  :=
    solve_lift (ret_both (inr (tt : 'unit) : t_LogError)) : both L I (t_LogError).
Fail Next Obligation.

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Definition t_Action : choice_type :=
  (int32).
Equations f__private_action {L : {fset Location}} {I : Interface} (s : both L I (t_Action)) : both L I (int32) :=
  f__private_action s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (x : int32))) : both L I (int32).
Fail Next Obligation.
Equations Build_t_Action {L0 : {fset Location}} {I0 : Interface} {f__private_action : both L0 I0 (int32)} : both L0 I0 (t_Action) :=
  Build_t_Action  :=
    bind_both f__private_action (fun f__private_action =>
      solve_lift (ret_both ((f__private_action) : (t_Action)))) : both L0 I0 (t_Action).
Fail Next Obligation.
Notation "'Build_t_Action' '[' x ']' '(' 'f__private_action' ':=' y ')'" := (Build_t_Action (f__private_action := y)).

Equations impl__Action__tag {L1 : {fset Location}} {I1 : Interface} (self : both L1 I1 (t_Action)) : both L1 I1 (int32) :=
  impl__Action__tag self  :=
    solve_lift (f__private_action self) : both L1 I1 (int32).
Fail Next Obligation.

Definition t_AttributesCursor : choice_type :=
  (int32 × int16).
Equations f_current_attribute_cursor_position {L : {fset Location}} {I : Interface} (s : both L I (t_AttributesCursor)) : both L I (int32) :=
  f_current_attribute_cursor_position s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (fst x : int32))) : both L I (int32).
Fail Next Obligation.
Equations f_remaining_items {L : {fset Location}} {I : Interface} (s : both L I (t_AttributesCursor)) : both L I (int16) :=
  f_remaining_items s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (snd x : int16))) : both L I (int16).
Fail Next Obligation.
Equations Build_t_AttributesCursor {L0 : {fset Location}} {L1 : {fset Location}} {I0 : Interface} {I1 : Interface} {f_current_attribute_cursor_position : both L0 I0 (int32)} {f_remaining_items : both L1 I1 (int16)} : both (L0:|:L1) (I0:|:I1) (t_AttributesCursor) :=
  Build_t_AttributesCursor  :=
    bind_both f_remaining_items (fun f_remaining_items =>
      bind_both f_current_attribute_cursor_position (fun f_current_attribute_cursor_position =>
        solve_lift (ret_both ((f_current_attribute_cursor_position,f_remaining_items) : (t_AttributesCursor))))) : both (L0:|:L1) (I0:|:I1) (t_AttributesCursor).
Fail Next Obligation.
Notation "'Build_t_AttributesCursor' '[' x ']' '(' 'f_current_attribute_cursor_position' ':=' y ')'" := (Build_t_AttributesCursor (f_current_attribute_cursor_position := y) (f_remaining_items := f_remaining_items x)).
Notation "'Build_t_AttributesCursor' '[' x ']' '(' 'f_remaining_items' ':=' y ')'" := (Build_t_AttributesCursor (f_current_attribute_cursor_position := f_current_attribute_cursor_position x) (f_remaining_items := y)).

Definition t_ChainMetaExtern : choice_type :=
  'unit.
Equations Build_t_ChainMetaExtern : both (fset []) (fset []) (t_ChainMetaExtern) :=
  Build_t_ChainMetaExtern  :=
    solve_lift (ret_both (tt (* Empty tuple *) : (t_ChainMetaExtern))) : both (fset []) (fset []) (t_ChainMetaExtern).
Fail Next Obligation.

Definition t_ContractState : choice_type :=
  (int32).
Equations f_current_contract_state_position {L : {fset Location}} {I : Interface} (s : both L I (t_ContractState)) : both L I (int32) :=
  f_current_contract_state_position s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (x : int32))) : both L I (int32).
Fail Next Obligation.
Equations Build_t_ContractState {L0 : {fset Location}} {I0 : Interface} {f_current_contract_state_position : both L0 I0 (int32)} : both L0 I0 (t_ContractState) :=
  Build_t_ContractState  :=
    bind_both f_current_contract_state_position (fun f_current_contract_state_position =>
      solve_lift (ret_both ((f_current_contract_state_position) : (t_ContractState)))) : both L0 I0 (t_ContractState).
Fail Next Obligation.
Notation "'Build_t_ContractState' '[' x ']' '(' 'f_current_contract_state_position' ':=' y ')'" := (Build_t_ContractState (f_current_contract_state_position := y)).

Definition t_ExternContext {v_T : _} `{ t_Sized (v_T)} `{ t_ContextType (v_T)} : choice_type :=
  (t_PhantomData (v_T)).
Equations f_marker {L : {fset Location}} {I : Interface} {v_T : _} `{ t_Sized (v_T)} `{ t_ContextType (v_T)} (s : both L I (t_ExternContext)) : both L I (t_PhantomData (v_T)) :=
  f_marker s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (x : t_PhantomData (v_T)))) : both L I (t_PhantomData (v_T)).
Fail Next Obligation.
Equations Build_t_ExternContext {L0 : {fset Location}} {I0 : Interface} {v_T : _} `{ t_Sized (v_T)} `{ t_ContextType (v_T)} {f_marker : both L0 I0 (t_PhantomData (v_T))} : both L0 I0 (t_ExternContext) :=
  Build_t_ExternContext  :=
    bind_both f_marker (fun f_marker =>
      solve_lift (ret_both ((f_marker) : (t_ExternContext)))) : both L0 I0 (t_ExternContext).
Fail Next Obligation.
Notation "'Build_t_ExternContext' '[' x ']' '(' 'f_marker' ':=' y ')'" := (Build_t_ExternContext (f_marker := y)).

Definition t_InitContextExtern : choice_type :=
  'unit.
Equations Build_t_InitContextExtern : both (fset []) (fset []) (t_InitContextExtern) :=
  Build_t_InitContextExtern  :=
    solve_lift (ret_both (tt (* Empty tuple *) : (t_InitContextExtern))) : both (fset []) (fset []) (t_InitContextExtern).
Fail Next Obligation.

Definition t_Logger : choice_type :=
  ('unit).
Equations f__private_logger {L : {fset Location}} {I : Interface} (s : both L I (t_Logger)) : both L I ('unit) :=
  f__private_logger s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (x : 'unit))) : both L I ('unit).
Fail Next Obligation.
Equations Build_t_Logger {L0 : {fset Location}} {I0 : Interface} {f__private_logger : both L0 I0 ('unit)} : both L0 I0 (t_Logger) :=
  Build_t_Logger  :=
    bind_both f__private_logger (fun f__private_logger =>
      solve_lift (ret_both ((f__private_logger) : (t_Logger)))) : both L0 I0 (t_Logger).
Fail Next Obligation.
Notation "'Build_t_Logger' '[' x ']' '(' 'f__private_logger' ':=' y ')'" := (Build_t_Logger (f__private_logger := y)).

Definition t_NotPayableError : choice_type :=
  'unit.
Equations Build_t_NotPayableError : both (fset []) (fset []) (t_NotPayableError) :=
  Build_t_NotPayableError  :=
    solve_lift (ret_both (tt (* Empty tuple *) : (t_NotPayableError))) : both (fset []) (fset []) (t_NotPayableError).
Fail Next Obligation.

Definition t_Parameter : choice_type :=
  (int32).
Equations f_current_parameter_position {L : {fset Location}} {I : Interface} (s : both L I (t_Parameter)) : both L I (int32) :=
  f_current_parameter_position s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (x : int32))) : both L I (int32).
Fail Next Obligation.
Equations Build_t_Parameter {L0 : {fset Location}} {I0 : Interface} {f_current_parameter_position : both L0 I0 (int32)} : both L0 I0 (t_Parameter) :=
  Build_t_Parameter  :=
    bind_both f_current_parameter_position (fun f_current_parameter_position =>
      solve_lift (ret_both ((f_current_parameter_position) : (t_Parameter)))) : both L0 I0 (t_Parameter).
Fail Next Obligation.
Notation "'Build_t_Parameter' '[' x ']' '(' 'f_current_parameter_position' ':=' y ')'" := (Build_t_Parameter (f_current_parameter_position := y)).

Definition t_ReceiveContextExtern : choice_type :=
  'unit.
Equations Build_t_ReceiveContextExtern : both (fset []) (fset []) (t_ReceiveContextExtern) :=
  Build_t_ReceiveContextExtern  :=
    solve_lift (ret_both (tt (* Empty tuple *) : (t_ReceiveContextExtern))) : both (fset []) (fset []) (t_ReceiveContextExtern).
Fail Next Obligation.

Definition t_Reject : choice_type :=
  (t_NonZeroI32).
Equations f_error_code {L : {fset Location}} {I : Interface} (s : both L I (t_Reject)) : both L I (t_NonZeroI32) :=
  f_error_code s  :=
    bind_both s (fun x =>
      solve_lift (ret_both (x : t_NonZeroI32))) : both L I (t_NonZeroI32).
Fail Next Obligation.
Equations Build_t_Reject {L0 : {fset Location}} {I0 : Interface} {f_error_code : both L0 I0 (t_NonZeroI32)} : both L0 I0 (t_Reject) :=
  Build_t_Reject  :=
    bind_both f_error_code (fun f_error_code =>
      solve_lift (ret_both ((f_error_code) : (t_Reject)))) : both L0 I0 (t_Reject).
Fail Next Obligation.
Notation "'Build_t_Reject' '[' x ']' '(' 'f_error_code' ':=' y ')'" := (Build_t_Reject (f_error_code := y)).

Definition t_InitResult {v_S : _} `{ t_Sized (v_S)} : choice_type :=
  t_Result (v_S) (t_Reject).

Definition t_ReceiveResult {v_A : _} `{ t_Sized (v_A)} : choice_type :=
  t_Result (v_A) (t_Reject).
