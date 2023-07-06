module Hacspec_ecdsa_p256_sha256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_Error =
  | Error_InvalidScalar : t_Error
  | Error_InvalidSignature : t_Error

let t_P256PublicKey = (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)

let t_P256SecretKey = Hacspec_p256.t_P256Scalar

let t_P256Signature = (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar)

let t_P256SignatureResult =
  Core.Result.t_Result (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar) t_Error

let t_P256VerifyResult = Core.Result.t_Result Prims.unit t_Error

let t_CheckResult = Core.Result.t_Result Prims.unit t_Error

let t_ArithmeticResult =
  Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement) t_Error

let check_scalar_zero (r: Hacspec_p256.t_P256Scalar) : Core.Result.t_Result Prims.unit t_Error =
  if Hacspec_lib.Traits.Numeric.equal r Hacspec_lib.Traits.Integer.v_ZERO
  then Core.Result.Result.v_Err Error_InvalidScalar
  else Core.Result.Result.v_Ok ()

let ecdsa_point_mul_base (x: Hacspec_p256.t_P256Scalar)
    : Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      t_Error =
  match Hacspec_p256.p256_point_mul_base x with
  | (Core.Result.Result_Ok s:
    Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      Hacspec_p256.t_Error) ->
    Core.Result.Result.v_Ok s
  | (Core.Result.Result_Err _:
    Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      Hacspec_p256.t_Error) ->
    Core.Result.Result.v_Err Error_InvalidScalar

let ecdsa_point_mul
      (k: Hacspec_p256.t_P256Scalar)
      (p: (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement))
    : Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      t_Error =
  match Hacspec_p256.p256_point_mul k p with
  | (Core.Result.Result_Ok s:
    Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      Hacspec_p256.t_Error) ->
    Core.Result.Result.v_Ok s
  | (Core.Result.Result_Err _:
    Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      Hacspec_p256.t_Error) ->
    Core.Result.Result.v_Err Error_InvalidScalar

let ecdsa_point_add (p q: (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement))
    : Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      t_Error =
  match Hacspec_p256.point_add p q with
  | (Core.Result.Result_Ok s:
    Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      Hacspec_p256.t_Error) ->
    Core.Result.Result.v_Ok s
  | (Core.Result.Result_Err _:
    Core.Result.t_Result (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement)
      Hacspec_p256.t_Error) ->
    Core.Result.Result.v_Err Error_InvalidScalar

let sign (payload: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (sk nonce: Hacspec_p256.t_P256Scalar)
    : Core.Result.t_Result (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar) t_Error =
  let _:Core.Result.t_Result (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar) t_Error =
    Core.Ops.Try_trait.FromResidual.from_residual (check_scalar_zero nonce)
  in
  let k_x, _k_y:Core.Result.t_Result (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar) t_Error
  =
    Core.Ops.Try_trait.FromResidual.from_residual (ecdsa_point_mul_base nonce)
  in
  let r:Hacspec_p256.t_P256Scalar =
    Hacspec_p256.from_byte_seq_be_under_impl_68 (Hacspec_p256.to_byte_seq_be_under_impl_1 k_x)
  in
  let _:Core.Result.t_Result (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar) t_Error =
    Core.Ops.Try_trait.FromResidual.from_residual (check_scalar_zero r)
  in
  let payload_hash:Hacspec_sha256.t_Sha256Digest = Hacspec_sha256.hash payload in
  let payload_hash:Hacspec_p256.t_P256Scalar =
    Hacspec_p256.from_byte_seq_be_under_impl_68 payload_hash
  in
  let rsk = r *. sk in
  let hash_rsk = payload_hash +. rsk in
  let nonce_inv:Hacspec_p256.t_P256Scalar = Hacspec_p256.inv_under_impl_125 nonce in
  let s = nonce_inv *. hash_rsk in
  Core.Result.Result.v_Ok (r, s)

let ecdsa_p256_sha256_sign
      (payload: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (sk nonce: Hacspec_p256.t_P256Scalar)
    : Core.Result.t_Result (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar) t_Error =
  sign payload sk nonce

let verify
      (payload: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (pk: (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement))
      (signature: (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar))
    : Core.Result.t_Result Prims.unit t_Error =
  let r, s:(Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar) = signature in
  let payload_hash:Hacspec_sha256.t_Sha256Digest = Hacspec_sha256.hash payload in
  let payload_hash:Hacspec_p256.t_P256Scalar =
    Hacspec_p256.from_byte_seq_be_under_impl_68 payload_hash
  in
  let s_inv:Hacspec_p256.t_P256Scalar = Hacspec_p256.inv_under_impl_125 s in
  let u1 = payload_hash *. s_inv in
  let u1:Core.Result.t_Result Prims.unit t_Error =
    Core.Ops.Try_trait.FromResidual.from_residual (ecdsa_point_mul_base u1)
  in
  let u2 = r *. s_inv in
  let u2:Core.Result.t_Result Prims.unit t_Error =
    Core.Ops.Try_trait.FromResidual.from_residual (ecdsa_point_mul u2 pk)
  in
  let x, _y:Core.Result.t_Result Prims.unit t_Error =
    Core.Ops.Try_trait.FromResidual.from_residual (ecdsa_point_add u1 u2)
  in
  let x:Hacspec_p256.t_P256Scalar =
    Hacspec_p256.from_byte_seq_be_under_impl_68 (Hacspec_p256.to_byte_seq_be_under_impl_1 x)
  in
  if x =. r then Core.Result.Result.v_Ok () else Core.Result.Result.v_Err Error_InvalidSignature

let ecdsa_p256_sha256_verify
      (payload: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (pk: (Hacspec_p256.t_P256FieldElement & Hacspec_p256.t_P256FieldElement))
      (signature: (Hacspec_p256.t_P256Scalar & Hacspec_p256.t_P256Scalar))
    : Core.Result.t_Result Prims.unit t_Error = verify payload pk signature