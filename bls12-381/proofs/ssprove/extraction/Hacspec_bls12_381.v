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

Require Import Hacspec_lib.
Export Hacspec_lib.

Notation "'t_Fp12'" := ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).

Notation "'t_Fp2'" := ((t_Fp × t_Fp)).

Notation "'t_Fp6'" := (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).

Notation "'t_G1'" := ((t_Fp × t_Fp × 'bool)).

Notation "'t_G2'" := (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).

(*Not implemented yet? todo(item)*)

Equations fp2add {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 ((t_Fp × t_Fp))) (m : both L2 I2 ((t_Fp × t_Fp))) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp)) :=
  fp2add n m  :=
    letb '(n1,n2) := n in
    letb '(m1,m2) := m in
    solve_lift (prod_b (n1 .+ m1,n2 .+ m2)) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp2mul {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 ((t_Fp × t_Fp))) (m : both L2 I2 ((t_Fp × t_Fp))) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp)) :=
  fp2mul n m  :=
    letb '(n1,n2) := n in
    letb '(m1,m2) := m in
    letb x1 := (n1 .* m1) .- (n2 .* m2) in
    letb x2 := (n1 .* m2) .+ (n2 .* m1) in
    solve_lift (prod_b (x1,x2)) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp6add {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) (m : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) :=
  fp6add n m  :=
    letb '(n1,n2,n3) := n in
    letb '(m1,m2,m3) := m in
    solve_lift (prod_b (fp2add n1 m1,fp2add n2 m2,fp2add n3 m3)) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).
Fail Next Obligation.

Equations fp12add {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) (m : both L2 I2 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12add n m  :=
    letb '(n1,n2) := n in
    letb '(m1,m2) := m in
    solve_lift (prod_b (fp6add n1 m1,fp6add n2 m2)) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations g1 {L1 : {fset Location}} {I1 : Interface} (_ : both L1 I1 ('unit)) : both L1 I1 ((t_Fp × t_Fp × 'bool)) :=
  g1 _  :=
    solve_lift (prod_b (impl__Fp__from_hex (ret_both (17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb : chString)),impl__Fp__from_hex (ret_both (08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1 : chString)),ret_both (false : 'bool))) : both L1 I1 ((t_Fp × t_Fp × 'bool)).
Fail Next Obligation.

Equations g2 {L1 : {fset Location}} {I1 : Interface} (_ : both L1 I1 ('unit)) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)) :=
  g2 _  :=
    solve_lift (prod_b (prod_b (impl__Fp__from_hex (ret_both (24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8 : chString)),impl__Fp__from_hex (ret_both (13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e : chString))),prod_b (impl__Fp__from_hex (ret_both (0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801 : chString)),impl__Fp__from_hex (ret_both (0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be : chString))),ret_both (false : 'bool))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).
Fail Next Obligation.

Notation "'t_ArrayFp'" := (nseq int64 6).
Definition ArrayFp {L : {fset Location}} {I : Interface} : both L I (t_ArrayFp) -> both L I (t_ArrayFp) :=
  id.

Notation "'t_SerializedFp'" := (nseq int8 48).
Definition SerializedFp {L : {fset Location}} {I : Interface} : both L I (t_SerializedFp) -> both L I (t_SerializedFp) :=
  id.

Notation "'t_Fp'" := (nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).
Definition Fp {L : {fset Location}} {I : Interface} : both L I (t_Fp) -> both L I (t_Fp) :=
  id.

Notation "'t_Scalar'" := (nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000).
Definition Scalar {L : {fset Location}} {I : Interface} : both L I (t_Scalar) -> both L I (t_Scalar) :=
  id.

Equations fp2conjugate {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 ((t_Fp × t_Fp))) : both L1 I1 ((t_Fp × t_Fp)) :=
  fp2conjugate n  :=
    letb '(n1,n2) := n in
    solve_lift (prod_b (n1,(f_ZERO (ret_both (tt : 'unit))) .- n2)) : both L1 I1 ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp2fromfp {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 (t_Fp)) : both L1 I1 ((t_Fp × t_Fp)) :=
  fp2fromfp n  :=
    solve_lift (prod_b (n,f_ZERO (ret_both (tt : 'unit)))) : both L1 I1 ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp2inv {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 ((t_Fp × t_Fp))) : both L1 I1 ((t_Fp × t_Fp)) :=
  fp2inv n  :=
    letb '(n1,n2) := n in
    letb t0 := (n1 .* n1) .+ (n2 .* n2) in
    letb t1 := impl__Fp__inv t0 in
    letb x1 := n1 .* t1 in
    letb x2 := (f_ZERO (ret_both (tt : 'unit))) .- (n2 .* t1) in
    solve_lift (prod_b (x1,x2)) : both L1 I1 ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp2neg {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 ((t_Fp × t_Fp))) : both L1 I1 ((t_Fp × t_Fp)) :=
  fp2neg n  :=
    letb '(n1,n2) := n in
    solve_lift (prod_b ((f_ZERO (ret_both (tt : 'unit))) .- n1,(f_ZERO (ret_both (tt : 'unit))) .- n2)) : both L1 I1 ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp2sub {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 ((t_Fp × t_Fp))) (m : both L2 I2 ((t_Fp × t_Fp))) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp)) :=
  fp2sub n m  :=
    solve_lift (fp2add n (fp2neg m)) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp2zero {L1 : {fset Location}} {I1 : Interface} (_ : both L1 I1 ('unit)) : both L1 I1 ((t_Fp × t_Fp)) :=
  fp2zero _  :=
    solve_lift (fp2fromfp (f_ZERO (ret_both (tt : 'unit)))) : both L1 I1 ((t_Fp × t_Fp)).
Fail Next Obligation.

Equations fp6fromfp2 {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 ((t_Fp × t_Fp))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) :=
  fp6fromfp2 n  :=
    solve_lift (prod_b (n,fp2zero (ret_both (tt : 'unit)),fp2zero (ret_both (tt : 'unit)))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).
Fail Next Obligation.

Equations fp6inv {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) :=
  fp6inv n  :=
    letb '(n1,n2,n3) := n in
    letb eps := prod_b (f_ONE (ret_both (tt : 'unit)),f_ONE (ret_both (tt : 'unit))) in
    letb t1 := fp2mul n1 n1 in
    letb t2 := fp2mul n2 n2 in
    letb t3 := fp2mul n3 n3 in
    letb t4 := fp2mul n1 n2 in
    letb t5 := fp2mul n1 n3 in
    letb t6 := fp2mul n2 n3 in
    letb x0 := fp2sub t1 (fp2mul eps t6) in
    letb y0 := fp2sub (fp2mul eps t3) t4 in
    letb z0 := fp2sub t2 t5 in
    letb t0 := fp2mul n1 x0 in
    letb t0 := fp2add t0 (fp2mul eps (fp2mul n3 y0)) in
    letb t0 := fp2add t0 (fp2mul eps (fp2mul n2 z0)) in
    letb t0 := fp2inv t0 in
    letb x := fp2mul x0 t0 in
    letb y := fp2mul y0 t0 in
    letb z := fp2mul z0 t0 in
    solve_lift (prod_b (x,y,z)) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).
Fail Next Obligation.

Equations fp6mul {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) (m : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) :=
  fp6mul n m  :=
    letb '(n1,n2,n3) := n in
    letb '(m1,m2,m3) := m in
    letb eps := prod_b (f_ONE (ret_both (tt : 'unit)),f_ONE (ret_both (tt : 'unit))) in
    letb t1 := fp2mul n1 m1 in
    letb t2 := fp2mul n2 m2 in
    letb t3 := fp2mul n3 m3 in
    letb t4 := fp2mul (fp2add n2 n3) (fp2add m2 m3) in
    letb t5 := fp2sub (fp2sub t4 t2) t3 in
    letb x := fp2add (fp2mul t5 eps) t1 in
    letb t4 := fp2mul (fp2add n1 n2) (fp2add m1 m2) in
    letb t5 := fp2sub (fp2sub t4 t1) t2 in
    letb y := fp2add t5 (fp2mul eps t3) in
    letb t4 := fp2mul (fp2add n1 n3) (fp2add m1 m3) in
    letb t5 := fp2sub (fp2sub t4 t1) t3 in
    letb z := fp2add t5 t2 in
    solve_lift (prod_b (x,y,z)) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).
Fail Next Obligation.

Equations fp6neg {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) :=
  fp6neg n  :=
    letb '(n1,n2,n3) := n in
    solve_lift (prod_b (fp2sub (fp2zero (ret_both (tt : 'unit))) n1,fp2sub (fp2zero (ret_both (tt : 'unit))) n2,fp2sub (fp2zero (ret_both (tt : 'unit))) n3)) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).
Fail Next Obligation.

Equations fp12conjugate {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12conjugate n  :=
    letb '(n1,n2) := n in
    solve_lift (prod_b (n1,fp6neg n2)) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations fp6sub {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) (m : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) :=
  fp6sub n m  :=
    solve_lift (fp6add n (fp6neg m)) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).
Fail Next Obligation.

Equations fp12inv {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12inv n  :=
    letb '(n1,n2) := n in
    letb gamma := prod_b (fp2zero (ret_both (tt : 'unit)),fp2fromfp (f_ONE (ret_both (tt : 'unit))),fp2zero (ret_both (tt : 'unit))) in
    letb t1 := fp6mul n1 n1 in
    letb t2 := fp6mul n2 n2 in
    letb t1 := fp6sub t1 (fp6mul gamma t2) in
    letb t2 := fp6inv t1 in
    letb x := fp6mul n1 t2 in
    letb y := fp6neg (fp6mul n2 t2) in
    solve_lift (prod_b (x,y)) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations fp12mul {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) (m : both L2 I2 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12mul n m  :=
    letb '(n1,n2) := n in
    letb '(m1,m2) := m in
    letb gamma := prod_b (fp2zero (ret_both (tt : 'unit)),fp2fromfp (f_ONE (ret_both (tt : 'unit))),fp2zero (ret_both (tt : 'unit))) in
    letb t1 := fp6mul n1 m1 in
    letb t2 := fp6mul n2 m2 in
    letb x := fp6add t1 (fp6mul t2 gamma) in
    letb y := fp6mul (fp6add n1 n2) (fp6add m1 m2) in
    letb y := fp6sub (fp6sub y t1) t2 in
    solve_lift (prod_b (x,y)) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations fp6zero {L1 : {fset Location}} {I1 : Interface} (_ : both L1 I1 ('unit)) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) :=
  fp6zero _  :=
    solve_lift (fp6fromfp2 (fp2zero (ret_both (tt : 'unit)))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))).
Fail Next Obligation.

Equations fp12fromfp6 {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12fromfp6 n  :=
    solve_lift (prod_b (n,fp6zero (ret_both (tt : 'unit)))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations fp12neg {L1 : {fset Location}} {I1 : Interface} (n : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12neg n  :=
    letb '(n1,n2) := n in
    solve_lift (prod_b (fp6sub (fp6zero (ret_both (tt : 'unit))) n1,fp6sub (fp6zero (ret_both (tt : 'unit))) n2)) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations fp12sub {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) (m : both L2 I2 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12sub n m  :=
    solve_lift (fp12add n (fp12neg m)) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations fp12zero {L1 : {fset Location}} {I1 : Interface} (_ : both L1 I1 ('unit)) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12zero _  :=
    solve_lift (fp12fromfp6 (fp6zero (ret_both (tt : 'unit)))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations g1neg {L1 : {fset Location}} {I1 : Interface} (p : both L1 I1 ((t_Fp × t_Fp × 'bool))) : both L1 I1 ((t_Fp × t_Fp × 'bool)) :=
  g1neg p  :=
    letb '(x,y,inf) := p in
    solve_lift (prod_b (x,(f_ZERO (ret_both (tt : 'unit))) .- y,inf)) : both L1 I1 ((t_Fp × t_Fp × 'bool)).
Fail Next Obligation.

Equations g2add_a {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (p : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) (q : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)) :=
  g2add_a p q  :=
    letb '(x1,y1,_) := p in
    letb '(x2,y2,_) := q in
    letb x_diff := fp2sub x2 x1 in
    letb y_diff := fp2sub y2 y1 in
    letb xovery := fp2mul y_diff (fp2inv x_diff) in
    letb t1 := fp2mul xovery xovery in
    letb t2 := fp2sub t1 x1 in
    letb x3 := fp2sub t2 x2 in
    letb t1 := fp2sub x1 x3 in
    letb t2 := fp2mul xovery t1 in
    letb y3 := fp2sub t2 y1 in
    solve_lift (prod_b (x3,y3,ret_both (false : 'bool))) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).
Fail Next Obligation.

Equations g2double_a {L1 : {fset Location}} {I1 : Interface} (p : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)) :=
  g2double_a p  :=
    letb '(x1,y1,_) := p in
    letb x12 := fp2mul x1 x1 in
    letb t1 := fp2mul (fp2fromfp (impl__Fp__from_literal (ret_both (3 : int128)))) x12 in
    letb t2 := fp2inv (fp2mul (fp2fromfp (f_TWO (ret_both (tt : 'unit)))) y1) in
    letb xovery := fp2mul t1 t2 in
    letb t1 := fp2mul xovery xovery in
    letb t2 := fp2mul (fp2fromfp (f_TWO (ret_both (tt : 'unit)))) x1 in
    letb x3 := fp2sub t1 t2 in
    letb t1 := fp2sub x1 x3 in
    letb t2 := fp2mul xovery t1 in
    letb y3 := fp2sub t2 y1 in
    solve_lift (prod_b (x3,y3,ret_both (false : 'bool))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).
Fail Next Obligation.

Equations g2double {L1 : {fset Location}} {I1 : Interface} (p : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)) :=
  g2double p  :=
    letb '(v__x1,y1,inf1) := p in
    solve_lift (ifb andb (y1 <> (fp2zero (ret_both (tt : 'unit)))) (not inf1)
    then g2double_a p
    else prod_b (fp2zero (ret_both (tt : 'unit)),fp2zero (ret_both (tt : 'unit)),ret_both (true : 'bool))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).
Fail Next Obligation.

Equations g2add {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (p : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) (q : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)) :=
  g2add p q  :=
    letb '(x1,y1,inf1) := p in
    letb '(x2,y2,inf2) := q in
    solve_lift (ifb inf1
    then q
    else ifb inf2
    then p
    else ifb p =.? q
    then g2double p
    else ifb not (andb (x1 =.? x2) (y1 =.? (fp2neg y2)))
    then g2add_a p q
    else prod_b (fp2zero (ret_both (tt : 'unit)),fp2zero (ret_both (tt : 'unit)),ret_both (true : 'bool))) : both (L1 :|: L2) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).
Fail Next Obligation.

Equations g2neg {L1 : {fset Location}} {I1 : Interface} (p : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)) :=
  g2neg p  :=
    letb '(x,y,inf) := p in
    solve_lift (prod_b (x,fp2neg y,inf)) : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).
Fail Next Obligation.

Equations twist {L1 : {fset Location}} {I1 : Interface} (p : both L1 I1 ((t_Fp × t_Fp × 'bool))) : both L1 I1 (((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) × (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) :=
  twist p  :=
    letb '(p0,p1,_) := p in
    letb x := prod_b (prod_b (fp2zero (ret_both (tt : 'unit)),fp2fromfp p0,fp2zero (ret_both (tt : 'unit))),fp6zero (ret_both (tt : 'unit))) in
    letb y := prod_b (fp6zero (ret_both (tt : 'unit)),prod_b (fp2zero (ret_both (tt : 'unit)),fp2fromfp p1,fp2zero (ret_both (tt : 'unit)))) in
    solve_lift (prod_b (x,y)) : both L1 I1 (((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))) × (((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))).
Fail Next Obligation.

Equations line_add_p {L1 : {fset Location}} {L2 : {fset Location}} {L3 : {fset Location}} {I1 : Interface} {I2 : Interface} {I3 : Interface} (r : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) (q : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) (p : both L3 I3 ((t_Fp × t_Fp × 'bool))) : both (L1 :|: L2 :|: L3) (I1 :|: I2 :|: I3) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  line_add_p r q p  :=
    letb '(r0,r1,_) := r in
    letb '(q0,q1,_) := q in
    letb a := fp2mul (fp2sub q1 r1) (fp2inv (fp2sub q0 r0)) in
    letb b := fp2sub r1 (fp2mul a r0) in
    letb a := fp12fromfp6 (fp6fromfp2 a) in
    letb b := fp12fromfp6 (fp6fromfp2 b) in
    letb '(x,y) := twist p in
    solve_lift (fp12neg (fp12sub (fp12sub y (fp12mul a x)) b)) : both (L1 :|: L2 :|: L3) (I1 :|: I2 :|: I3) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations line_double_p {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (r : both L1 I1 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) (p : both L2 I2 ((t_Fp × t_Fp × 'bool))) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  line_double_p r p  :=
    letb '(r0,r1,_) := r in
    letb a := fp2mul (fp2fromfp (impl__Fp__from_literal (ret_both (3 : int128)))) (fp2mul r0 r0) in
    letb a := fp2mul a (fp2inv (fp2mul (fp2fromfp (f_TWO (ret_both (tt : 'unit)))) r1)) in
    letb b := fp2sub r1 (fp2mul a r0) in
    letb a := fp12fromfp6 (fp6fromfp2 a) in
    letb b := fp12fromfp6 (fp6fromfp2 b) in
    letb '(x,y) := twist p in
    solve_lift (fp12neg (fp12sub (fp12sub y (fp12mul a x)) b)) : both (L1 :|: L2) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations g1add_a {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (p : both L1 I1 ((t_Fp × t_Fp × 'bool))) (q : both L2 I2 ((t_Fp × t_Fp × 'bool))) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp × 'bool)) :=
  g1add_a p q  :=
    letb '(x1,y1,_) := p in
    letb '(x2,y2,_) := q in
    letb x_diff := x2 .- x1 in
    letb y_diff := y2 .- y1 in
    letb xovery := y_diff .* (impl__Fp__inv x_diff) in
    letb x3 := ((f_exp xovery (ret_both (2 : int32))) .- x1) .- x2 in
    letb y3 := (xovery .* (x1 .- x3)) .- y1 in
    solve_lift (prod_b (x3,y3,ret_both (false : 'bool))) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp × 'bool)).
Fail Next Obligation.

Equations g1double_a {L1 : {fset Location}} {I1 : Interface} (p : both L1 I1 ((t_Fp × t_Fp × 'bool))) : both L1 I1 ((t_Fp × t_Fp × 'bool)) :=
  g1double_a p  :=
    letb '(x1,y1,_) := p in
    letb x12 := f_exp x1 (ret_both (2 : int32)) in
    letb xovery := ((impl__Fp__from_literal (ret_both (3 : int128))) .* x12) .* (impl__Fp__inv ((f_TWO (ret_both (tt : 'unit))) .* y1)) in
    letb x3 := (f_exp xovery (ret_both (2 : int32))) .- ((f_TWO (ret_both (tt : 'unit))) .* x1) in
    letb y3 := (xovery .* (x1 .- x3)) .- y1 in
    solve_lift (prod_b (x3,y3,ret_both (false : 'bool))) : both L1 I1 ((t_Fp × t_Fp × 'bool)).
Fail Next Obligation.

Equations g1double {L1 : {fset Location}} {I1 : Interface} (p : both L1 I1 ((t_Fp × t_Fp × 'bool))) : both L1 I1 ((t_Fp × t_Fp × 'bool)) :=
  g1double p  :=
    letb '(v__x1,y1,inf1) := p in
    solve_lift (ifb andb (y1 <> (f_ZERO (ret_both (tt : 'unit)))) (not inf1)
    then g1double_a p
    else prod_b (f_ZERO (ret_both (tt : 'unit)),f_ZERO (ret_both (tt : 'unit)),ret_both (true : 'bool))) : both L1 I1 ((t_Fp × t_Fp × 'bool)).
Fail Next Obligation.

Equations g1add {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (p : both L1 I1 ((t_Fp × t_Fp × 'bool))) (q : both L2 I2 ((t_Fp × t_Fp × 'bool))) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp × 'bool)) :=
  g1add p q  :=
    letb '(x1,y1,inf1) := p in
    letb '(x2,y2,inf2) := q in
    solve_lift (ifb inf1
    then q
    else ifb inf2
    then p
    else ifb p =.? q
    then g1double p
    else ifb not (andb (x1 =.? x2) (y1 =.? ((f_ZERO (ret_both (tt : 'unit))) .- y2)))
    then g1add_a p q
    else prod_b (f_ZERO (ret_both (tt : 'unit)),f_ZERO (ret_both (tt : 'unit)),ret_both (true : 'bool))) : both (L1 :|: L2) (I1 :|: I2) ((t_Fp × t_Fp × 'bool)).
Fail Next Obligation.

Definition c_loc : Location :=
  ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)));0%nat).
Equations fp12exp {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (n : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) (k : both L2 I2 (t_Scalar)) : both (L1 :|: L2 :|: fset [c_loc]) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  fp12exp n k  :=
    letb c loc(c_loc) := fp12fromfp6 (fp6fromfp2 (fp2fromfp (f_ONE (ret_both (tt : 'unit))))) in
    letb _ := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := ret_both (256 : uint_size)))) (fun i =>
      ssp (fun _ =>
        letb _ := assign todo(term) in
        solve_lift (ifb impl__Scalar__bit k ((ret_both (255 : uint_size)) .- i)
        then letb _ := assign todo(term) in
        ret_both (tt : 'unit)
        else ()) : both (*1*)(L1:|:L2:|:fset [c_loc]) (I1:|:I2) ('unit))) (ret_both (tt : 'unit)) in
    solve_lift c : both (L1 :|: L2 :|: fset [c_loc]) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Definition t_loc : Location :=
  ((t_Fp × t_Fp × 'bool);1%nat).
Equations g1mul {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (m : both L1 I1 (t_Scalar)) (p : both L2 I2 ((t_Fp × t_Fp × 'bool))) : both (L1 :|: L2 :|: fset [t_loc]) (I1 :|: I2) ((t_Fp × t_Fp × 'bool)) :=
  g1mul m p  :=
    letb t loc(t_loc) := prod_b (f_ZERO (ret_both (tt : 'unit)),f_ZERO (ret_both (tt : 'unit)),ret_both (true : 'bool)) in
    letb _ := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := ret_both (256 : uint_size)))) (fun i =>
      ssp (fun _ =>
        letb _ := assign todo(term) in
        solve_lift (ifb impl__Scalar__bit m ((ret_both (255 : uint_size)) .- i)
        then letb _ := assign todo(term) in
        ret_both (tt : 'unit)
        else ()) : both (*1*)(L1:|:L2:|:fset [t_loc]) (I1:|:I2) ('unit))) (ret_both (tt : 'unit)) in
    solve_lift t : both (L1 :|: L2 :|: fset [t_loc]) (I1 :|: I2) ((t_Fp × t_Fp × 'bool)).
Fail Next Obligation.

Definition t_loc : Location :=
  (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool);2%nat).
Equations g2mul {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (m : both L1 I1 (t_Scalar)) (p : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) : both (L1 :|: L2 :|: fset [t_loc]) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)) :=
  g2mul m p  :=
    letb t loc(t_loc) := prod_b (fp2zero (ret_both (tt : 'unit)),fp2zero (ret_both (tt : 'unit)),ret_both (true : 'bool)) in
    letb _ := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (0 : uint_size)) (f_end := ret_both (256 : uint_size)))) (fun i =>
      ssp (fun _ =>
        letb _ := assign todo(term) in
        solve_lift (ifb impl__Scalar__bit m ((ret_both (255 : uint_size)) .- i)
        then letb _ := assign todo(term) in
        ret_both (tt : 'unit)
        else ()) : both (*1*)(L1:|:L2:|:fset [t_loc]) (I1:|:I2) ('unit))) (ret_both (tt : 'unit)) in
    solve_lift t : both (L1 :|: L2 :|: fset [t_loc]) (I1 :|: I2) (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool)).
Fail Next Obligation.

Equations frobenius {L1 : {fset Location}} {I1 : Interface} (f : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  frobenius f  :=
    letb '((g0,g1,g2),(h0,h1,h2)) := f in
    letb t1 := fp2conjugate g0 in
    letb t2 := fp2conjugate h0 in
    letb t3 := fp2conjugate g1 in
    letb t4 := fp2conjugate h1 in
    letb t5 := fp2conjugate g2 in
    letb t6 := fp2conjugate h2 in
    letb c1 := ArrayFp (array_from_list [U64 (ret_both (10162220747404304312 : int64));
      U64 (ret_both (17761815663483519293 : int64));
      U64 (ret_both (8873291758750579140 : int64));
      U64 (ret_both (1141103941765652303 : int64));
      U64 (ret_both (13993175198059990303 : int64));
      U64 (ret_both (1802798568193066599 : int64))]) in
    letb c1 := impl__ArrayFp__to_le_bytes c1 in
    letb c1 := impl__Fp__from_byte_seq_le c1 in
    letb c2 := ArrayFp (array_from_list [U64 (ret_both (3240210268673559283 : int64));
      U64 (ret_both (2895069921743240898 : int64));
      U64 (ret_both (17009126888523054175 : int64));
      U64 (ret_both (6098234018649060207 : int64));
      U64 (ret_both (9865672654120263608 : int64));
      U64 (ret_both (71000049454473266 : int64))]) in
    letb c2 := impl__ArrayFp__to_le_bytes c2 in
    letb c2 := impl__Fp__from_byte_seq_le c2 in
    letb gamma11 := prod_b (c1,c2) in
    letb gamma12 := fp2mul gamma11 gamma11 in
    letb gamma13 := fp2mul gamma12 gamma11 in
    letb gamma14 := fp2mul gamma13 gamma11 in
    letb gamma15 := fp2mul gamma14 gamma11 in
    letb t2 := fp2mul t2 gamma11 in
    letb t3 := fp2mul t3 gamma12 in
    letb t4 := fp2mul t4 gamma13 in
    letb t5 := fp2mul t5 gamma14 in
    letb t6 := fp2mul t6 gamma15 in
    solve_lift (prod_b (prod_b (t1,t3,t5),prod_b (t2,t4,t6))) : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Equations final_exponentiation {L1 : {fset Location}} {I1 : Interface} (f : both L1 I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp))))) : both (L1 :|: fset [c_loc]) I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  final_exponentiation f  :=
    letb fp6 := fp12conjugate f in
    letb finv := fp12inv f in
    letb fp6_1_ := fp12mul fp6 finv in
    letb fp8 := frobenius (frobenius fp6_1_) in
    letb f := fp12mul fp8 fp6_1_ in
    letb u := impl__Scalar__from_literal (ret_both (15132376222941642752 : int128)) in
    letb u_half := impl__Scalar__from_literal (ret_both (7566188111470821376 : int128)) in
    letb t0 := fp12mul f f in
    letb t1 := fp12exp t0 u in
    letb t1 := fp12conjugate t1 in
    letb t2 := fp12exp t1 u_half in
    letb t2 := fp12conjugate t2 in
    letb t3 := fp12conjugate f in
    letb t1 := fp12mul t3 t1 in
    letb t1 := fp12conjugate t1 in
    letb t1 := fp12mul t1 t2 in
    letb t2 := fp12exp t1 u in
    letb t2 := fp12conjugate t2 in
    letb t3 := fp12exp t2 u in
    letb t3 := fp12conjugate t3 in
    letb t1 := fp12conjugate t1 in
    letb t3 := fp12mul t1 t3 in
    letb t1 := fp12conjugate t1 in
    letb t1 := frobenius (frobenius (frobenius t1)) in
    letb t2 := frobenius (frobenius t2) in
    letb t1 := fp12mul t1 t2 in
    letb t2 := fp12exp t3 u in
    letb t2 := fp12conjugate t2 in
    letb t2 := fp12mul t2 t0 in
    letb t2 := fp12mul t2 f in
    letb t1 := fp12mul t1 t2 in
    letb t2 := frobenius t3 in
    solve_lift (fp12mul t1 t2) : both (L1 :|: fset [c_loc]) I1 ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.

Definition f_loc : Location :=
  ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)));3%nat).
Definition r_loc : Location :=
  (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool);4%nat).
Equations pairing {L1 : {fset Location}} {L2 : {fset Location}} {I1 : Interface} {I2 : Interface} (p : both L1 I1 ((t_Fp × t_Fp × 'bool))) (q : both L2 I2 (((t_Fp × t_Fp) × (t_Fp × t_Fp) × 'bool))) : both (L1 :|: L2 :|: fset [f_loc;r_loc;c_loc]) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))) :=
  pairing p q  :=
    letb t := impl__Scalar__from_literal (ret_both (15132376222941642752 : int128)) in
    letb r loc(r_loc) := q in
    letb f loc(f_loc) := fp12fromfp6 (fp6fromfp2 (fp2fromfp (f_ONE (ret_both (tt : 'unit))))) in
    letb _ := foldi_both_list (f_into_iter (Build_t_Range (f_start := ret_both (1 : uint_size)) (f_end := ret_both (64 : uint_size)))) (fun i =>
      ssp (fun _ =>
        letb lrr := line_double_p r p in
        letb _ := assign todo(term) in
        letb _ := assign todo(term) in
        solve_lift (ifb impl__Scalar__bit t (((ret_both (64 : uint_size)) .- i) .- (ret_both (1 : uint_size)))
        then letb lrq := line_add_p r q p in
        letb _ := assign todo(term) in
        letb _ := assign todo(term) in
        ret_both (tt : 'unit)
        else ()) : both (*2*)(L1:|:L2:|:fset [f_loc;r_loc]) (I1:|:I2) ('unit))) (ret_both (tt : 'unit)) in
    solve_lift (final_exponentiation (fp12conjugate f)) : both (L1 :|: L2 :|: fset [f_loc;r_loc;c_loc]) (I1 :|: I2) ((((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)) × ((t_Fp × t_Fp) × (t_Fp × t_Fp) × (t_Fp × t_Fp)))).
Fail Next Obligation.