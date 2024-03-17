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

Require Import Alloc.
Export Alloc.

Require Import ToOwned.
Export ToOwned.

Require Import string.
Export string.

Require Import String.
Export String.

Require Import ToString.
Export ToString.

Require Import vec.
Export vec.

Require Import Vec.
Export Vec.

Require Import Core.
Export Core.

Require Import convert.
Export convert.

Require Import hash.
Export hash.

Require Import marker.
Export marker.

Require Import mem.
Export mem.

Require Import num.
Export num.

Require Import Core_Result.
Export Core_Result.

Require Import collections.
Export collections.

Require Import Concordium_prims.
Export Concordium_prims.

Require Import Concordium_impls.
Export Concordium_impls.

Require Import Concordium_types.
Export Concordium_types.

Require Import Concordium_traits.
Export Concordium_traits.

Require Import Concordium_contracts_common.
Export Concordium_contracts_common.

Require Import Hacspec_concordium_derive.
Export Hacspec_concordium_derive.

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Equations trap {L1 : {fset Location}} {I1 : Interface} (_ : both L1 I1 ('unit)) : both L1 I1 (t_Never) :=
  trap _  :=
    solve_lift (abort (ret_both (tt : 'unit))) : both L1 I1 (t_Never).
Fail Next Obligation.