module Hacspec_ed25519
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let scalar_from_hash (h: Hacspec_sha512.t_Sha512Digest) : Hacspec_edwards25519.t_Scalar =
  let s:Hacspec_edwards25519.t_BigScalar = Hacspec_edwards25519.from_byte_seq_le_under_impl_134 h in
  Hacspec_edwards25519.from_byte_seq_le_under_impl_67 (Hacspec_lib.Seq.slice_under_impl_41 (Hacspec_edwards25519.to_byte_seq_le_under_impl_134
            s)
        0sz
        32sz)

let sign
      (sk: Hacspec_edwards25519.t_SerializedScalar)
      (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Hacspec_edwards25519.t_Signature =
  let a, prefix:(Hacspec_edwards25519.t_SerializedScalar & Hacspec_edwards25519.t_SerializedScalar)
  =
    Hacspec_edwards25519.secret_expand sk
  in
  let a:Hacspec_edwards25519.t_Scalar = Hacspec_edwards25519.from_byte_seq_le_under_impl_67 a in
  let b:(Hacspec_edwards25519.t_Ed25519FieldElement & Hacspec_edwards25519.t_Ed25519FieldElement &
    Hacspec_edwards25519.t_Ed25519FieldElement &
    Hacspec_edwards25519.t_Ed25519FieldElement) =
    Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE)
  in
  let a_p:Hacspec_edwards25519.t_CompressedEdPoint =
    Hacspec_edwards25519.compress (Hacspec_edwards25519.point_mul a b)
  in
  let r:Hacspec_edwards25519.t_Scalar =
    scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_edwards25519.concat_under_impl_309 prefix msg))
  in
  let r_p:(Hacspec_edwards25519.t_Ed25519FieldElement & Hacspec_edwards25519.t_Ed25519FieldElement &
    Hacspec_edwards25519.t_Ed25519FieldElement &
    Hacspec_edwards25519.t_Ed25519FieldElement) =
    Hacspec_edwards25519.point_mul r b
  in
  let r_s:Hacspec_edwards25519.t_CompressedEdPoint = Hacspec_edwards25519.compress r_p in
  let h:Hacspec_edwards25519.t_Scalar =
    scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                  r_s
                  a_p)
              msg))
  in
  let s = r +. h *. a in
  let s_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.slice_under_impl_41 (Hacspec_edwards25519.to_byte_seq_le_under_impl_67 s)
      0sz
      32sz
  in
  Hacspec_lib.Traits.SeqTrait.update (Hacspec_lib.Traits.SeqTrait.update Hacspec_edwards25519.new_under_impl_343
        0sz
        r_s)
    32sz
    s_bytes

let zcash_verify
      (pk: Hacspec_edwards25519.t_CompressedEdPoint)
      (signature: Hacspec_edwards25519.t_Signature)
      (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement) =
        Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress_non_canonical Hacspec_edwards25519.v_BASE
            )
      in
      let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
        Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress_non_canonical
                  pk)
              Hacspec_edwards25519.Error_InvalidPublickey)
      in
      let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
        Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
      in
      let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
        Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
      in
      let* _:Prims.unit =
        if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
        then
          let* _:Prims.unit = Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
          Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress_non_canonical
                    r_bytes)
                Hacspec_edwards25519.Error_InvalidR)
        in
        let s:Hacspec_edwards25519.t_Scalar =
          Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
        in
        let k:Hacspec_edwards25519.t_Scalar =
          scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                        r_bytes
                        pk)
                    msg))
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_mul s b)
        in
        let rc:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor r
        in
        let ka:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_mul k a)
        in
        if Hacspec_edwards25519.point_eq sb (Hacspec_edwards25519.point_add rc ka)
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))

let ietf_cofactored_verify
      (pk: Hacspec_edwards25519.t_CompressedEdPoint)
      (signature: Hacspec_edwards25519.t_Signature)
      (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement) =
        Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE)
      in
      let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
        Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                  pk)
              Hacspec_edwards25519.Error_InvalidPublickey)
      in
      let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
        Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
      in
      let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
        Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
      in
      let* _:Prims.unit =
        if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
        then
          let* _:Prims.unit = Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
          Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                    r_bytes)
                Hacspec_edwards25519.Error_InvalidR)
        in
        let s:Hacspec_edwards25519.t_Scalar =
          Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
        in
        let k:Hacspec_edwards25519.t_Scalar =
          scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                        r_bytes
                        pk)
                    msg))
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_mul s b)
        in
        let rc:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor r
        in
        let ka:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_mul k a)
        in
        if Hacspec_edwards25519.point_eq sb (Hacspec_edwards25519.point_add rc ka)
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))

let ietf_cofactorless_verify
      (pk: Hacspec_edwards25519.t_CompressedEdPoint)
      (signature: Hacspec_edwards25519.t_Signature)
      (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement) =
        Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE)
      in
      let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
        Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                  pk)
              Hacspec_edwards25519.Error_InvalidPublickey)
      in
      let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
        Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
      in
      let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
        Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
      in
      let* _:Prims.unit =
        if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
        then
          let* _:Prims.unit = Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
          Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                    r_bytes)
                Hacspec_edwards25519.Error_InvalidR)
        in
        let s:Hacspec_edwards25519.t_Scalar =
          Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
        in
        let k:Hacspec_edwards25519.t_Scalar =
          scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                        r_bytes
                        pk)
                    msg))
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul s b
        in
        let ka:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul k a
        in
        if Hacspec_edwards25519.point_eq sb (Hacspec_edwards25519.point_add r ka)
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))

let is_identity
      (p:
          (Hacspec_edwards25519.t_Ed25519FieldElement & Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement))
    : bool = Hacspec_edwards25519.point_eq p Hacspec_edwards25519.point_identity

let alg2_verify
      (pk: Hacspec_edwards25519.t_CompressedEdPoint)
      (signature: Hacspec_edwards25519.t_Signature)
      (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement &
        Hacspec_edwards25519.t_Ed25519FieldElement) =
        Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE)
      in
      let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
        Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                  pk)
              Hacspec_edwards25519.Error_InvalidPublickey)
      in
      let* _:Prims.unit =
        if is_identity (Hacspec_edwards25519.point_mul_by_cofactor a)
        then
          let* _:Prims.unit = Core.Result.Result.v_Err Hacspec_edwards25519.Error_SmallOrderPoint in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
        Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
      in
      let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
        Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
      in
      let* _:Prims.unit =
        if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
        then
          let* _:Prims.unit = Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
          Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                    r_bytes)
                Hacspec_edwards25519.Error_InvalidR)
        in
        let s:Hacspec_edwards25519.t_Scalar =
          Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
        in
        let k:Hacspec_edwards25519.t_Scalar =
          scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                        r_bytes
                        pk)
                    msg))
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_mul s b)
        in
        let rc:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor r
        in
        let ka:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_mul k a)
        in
        if Hacspec_edwards25519.point_eq sb (Hacspec_edwards25519.point_add rc ka)
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))

type t_BatchEntry =
  | BatchEntry :
      Hacspec_edwards25519.t_CompressedEdPoint ->
      Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 ->
      Hacspec_edwards25519.t_Signature
    -> t_BatchEntry

let zcash_batch_verify
      (entries: Hacspec_lib.Seq.t_Seq t_BatchEntry)
      (entropy: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let* _:Prims.unit =
        if
          Hacspec_lib.Seq.len_under_impl_41 entropy <.
          16sz *. Hacspec_lib.Seq.len_under_impl_41 entries
        then
          let* _:Prims.unit =
            Core.Result.Result.v_Err Hacspec_edwards25519.Error_NotEnoughRandomness
          in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let s_sum:Hacspec_edwards25519.t_Scalar = Hacspec_lib.Traits.Integer.v_ZERO in
        let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum, r_sum, s_sum:((Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          (Hacspec_edwards25519.t_Ed25519FieldElement & Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          _) =
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 entries
                  }))
            (a_sum, r_sum, s_sum)
            (fun (a_sum, r_sum, s_sum) i ->
                let BatchEntry pk msg signature:t_BatchEntry =
                  Core.Clone.Clone.clone entries.[ i ]
                in
                let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                  Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress_non_canonical
                            pk)
                        Hacspec_edwards25519.Error_InvalidPublickey)
                in
                let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
                  Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
                in
                let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
                  Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
                in
                let* _:Prims.unit =
                  if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
                  then
                    let* _:Prims.unit =
                      Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS
                    in
                    Core.Result.Result_Ok ()
                  else Core.Result.Result_Ok ()
                in
                Core.Result.Result_Ok
                (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                    Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress_non_canonical
                              r_bytes)
                          Hacspec_edwards25519.Error_InvalidR)
                  in
                  let s:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
                  in
                  let c:Hacspec_edwards25519.t_Scalar =
                    scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                                  r_bytes
                                  pk)
                              msg))
                  in
                  let z:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
                    Hacspec_lib.Seq.slice_under_impl_41 entropy (16sz *. i) 16sz
                  in
                  let z:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 (Hacspec_lib.Seq.concat_under_impl_41
                          z
                          (Hacspec_lib.Seq.new_under_impl_41 16sz))
                  in
                  let s_sum = s_sum +. s *. z in
                  let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement) =
                    Hacspec_edwards25519.point_add r_sum (Hacspec_edwards25519.point_mul z r)
                  in
                  Hacspec_edwards25519.point_add a_sum (Hacspec_edwards25519.point_mul (z *. c) a),
                  r_sum,
                  s_sum))
        in
        let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE
            )
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul s_sum b
        in
        let check:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_add (Hacspec_edwards25519.point_neg
                    sb)
                (Hacspec_edwards25519.point_add r_sum a_sum))
        in
        if is_identity check
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))

let ietf_cofactored_batch_verify
      (entries: Hacspec_lib.Seq.t_Seq t_BatchEntry)
      (entropy: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let* _:Prims.unit =
        if
          Hacspec_lib.Seq.len_under_impl_41 entropy <.
          16sz *. Hacspec_lib.Seq.len_under_impl_41 entries
        then
          let* _:Prims.unit =
            Core.Result.Result.v_Err Hacspec_edwards25519.Error_NotEnoughRandomness
          in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let s_sum:Hacspec_edwards25519.t_Scalar = Hacspec_lib.Traits.Integer.v_ZERO in
        let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum, r_sum, s_sum:((Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          (Hacspec_edwards25519.t_Ed25519FieldElement & Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          _) =
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 entries
                  }))
            (a_sum, r_sum, s_sum)
            (fun (a_sum, r_sum, s_sum) i ->
                let BatchEntry pk msg signature:t_BatchEntry =
                  Core.Clone.Clone.clone entries.[ i ]
                in
                let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                  Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                            pk)
                        Hacspec_edwards25519.Error_InvalidPublickey)
                in
                let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
                  Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
                in
                let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
                  Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
                in
                let* _:Prims.unit =
                  if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
                  then
                    let* _:Prims.unit =
                      Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS
                    in
                    Core.Result.Result_Ok ()
                  else Core.Result.Result_Ok ()
                in
                Core.Result.Result_Ok
                (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                    Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                              r_bytes)
                          Hacspec_edwards25519.Error_InvalidR)
                  in
                  let s:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
                  in
                  let c:Hacspec_edwards25519.t_Scalar =
                    scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                                  r_bytes
                                  pk)
                              msg))
                  in
                  let z:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
                    Hacspec_lib.Seq.slice_under_impl_41 entropy (16sz *. i) 16sz
                  in
                  let z:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 (Hacspec_lib.Seq.concat_under_impl_41
                          z
                          (Hacspec_lib.Seq.new_under_impl_41 16sz))
                  in
                  let s_sum = s_sum +. s *. z in
                  let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement) =
                    Hacspec_edwards25519.point_add r_sum (Hacspec_edwards25519.point_mul z r)
                  in
                  Hacspec_edwards25519.point_add a_sum (Hacspec_edwards25519.point_mul (z *. c) a),
                  r_sum,
                  s_sum))
        in
        let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE
            )
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul s_sum b
        in
        let check:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_add (Hacspec_edwards25519.point_neg
                    sb)
                (Hacspec_edwards25519.point_add r_sum a_sum))
        in
        if is_identity check
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))

let ietf_cofactorless_batch_verify
      (entries: Hacspec_lib.Seq.t_Seq t_BatchEntry)
      (entropy: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let* _:Prims.unit =
        if
          Hacspec_lib.Seq.len_under_impl_41 entropy <.
          16sz *. Hacspec_lib.Seq.len_under_impl_41 entries
        then
          let* _:Prims.unit =
            Core.Result.Result.v_Err Hacspec_edwards25519.Error_NotEnoughRandomness
          in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let s_sum:Hacspec_edwards25519.t_Scalar = Hacspec_lib.Traits.Integer.v_ZERO in
        let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum, r_sum, s_sum:((Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          (Hacspec_edwards25519.t_Ed25519FieldElement & Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          _) =
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 entries
                  }))
            (a_sum, r_sum, s_sum)
            (fun (a_sum, r_sum, s_sum) i ->
                let BatchEntry pk msg signature:t_BatchEntry =
                  Core.Clone.Clone.clone entries.[ i ]
                in
                let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                  Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                            pk)
                        Hacspec_edwards25519.Error_InvalidPublickey)
                in
                let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
                  Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
                in
                let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
                  Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
                in
                let* _:Prims.unit =
                  if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
                  then
                    let* _:Prims.unit =
                      Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS
                    in
                    Core.Result.Result_Ok ()
                  else Core.Result.Result_Ok ()
                in
                Core.Result.Result_Ok
                (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                    Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                              r_bytes)
                          Hacspec_edwards25519.Error_InvalidR)
                  in
                  let s:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
                  in
                  let c:Hacspec_edwards25519.t_Scalar =
                    scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                                  r_bytes
                                  pk)
                              msg))
                  in
                  let z:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
                    Hacspec_lib.Seq.slice_under_impl_41 entropy (16sz *. i) 16sz
                  in
                  let z:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 (Hacspec_lib.Seq.concat_under_impl_41
                          z
                          (Hacspec_lib.Seq.new_under_impl_41 16sz))
                  in
                  let s_sum = s_sum +. s *. z in
                  let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement) =
                    Hacspec_edwards25519.point_add r_sum (Hacspec_edwards25519.point_mul z r)
                  in
                  Hacspec_edwards25519.point_add a_sum (Hacspec_edwards25519.point_mul (z *. c) a),
                  r_sum,
                  s_sum))
        in
        let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE
            )
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul s_sum b
        in
        let check:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_add (Hacspec_edwards25519.point_neg sb)
            (Hacspec_edwards25519.point_add r_sum a_sum)
        in
        if is_identity check
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))

let alg3_batch_verify
      (entries: Hacspec_lib.Seq.t_Seq t_BatchEntry)
      (entropy: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
  Rust_primitives.Hax.Control_flow_monad.Mresult.run (let* _:Prims.unit =
        if
          Hacspec_lib.Seq.len_under_impl_41 entropy <.
          16sz *. Hacspec_lib.Seq.len_under_impl_41 entries
        then
          let* _:Prims.unit =
            Core.Result.Result.v_Err Hacspec_edwards25519.Error_NotEnoughRandomness
          in
          Core.Result.Result_Ok ()
        else Core.Result.Result_Ok ()
      in
      Core.Result.Result_Ok
      (let s_sum:Hacspec_edwards25519.t_Scalar = Hacspec_lib.Traits.Integer.v_ZERO in
        let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_identity
        in
        let a_sum, r_sum, s_sum:((Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          (Hacspec_edwards25519.t_Ed25519FieldElement & Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement &
            Hacspec_edwards25519.t_Ed25519FieldElement) &
          _) =
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 entries
                  }))
            (a_sum, r_sum, s_sum)
            (fun (a_sum, r_sum, s_sum) i ->
                let BatchEntry pk msg signature:t_BatchEntry =
                  Core.Clone.Clone.clone entries.[ i ]
                in
                let a:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                  Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                            pk)
                        Hacspec_edwards25519.Error_InvalidPublickey)
                in
                let* _:Prims.unit =
                  if is_identity (Hacspec_edwards25519.point_mul_by_cofactor a)
                  then
                    let* _:Prims.unit =
                      Core.Result.Result.v_Err Hacspec_edwards25519.Error_SmallOrderPoint
                    in
                    Core.Result.Result_Ok ()
                  else Core.Result.Result_Ok ()
                in
                let r_bytes:Hacspec_edwards25519.t_CompressedEdPoint =
                  Hacspec_edwards25519.from_slice_under_impl_274 signature 0sz 32sz
                in
                let s_bytes:Hacspec_edwards25519.t_SerializedScalar =
                  Hacspec_edwards25519.from_slice_under_impl_309 signature 32sz 32sz
                in
                let* _:Prims.unit =
                  if ~.(Hacspec_edwards25519.check_canonical_scalar s_bytes)
                  then
                    let* _:Prims.unit =
                      Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidS
                    in
                    Core.Result.Result_Ok ()
                  else Core.Result.Result_Ok ()
                in
                Core.Result.Result_Ok
                (let r:Core.Result.t_Result Prims.unit Hacspec_edwards25519.t_Error =
                    Core.Ops.Try_trait.FromResidual.from_residual (Core.Option.ok_or_under_impl (Hacspec_edwards25519.decompress
                              r_bytes)
                          Hacspec_edwards25519.Error_InvalidR)
                  in
                  let s:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 s_bytes
                  in
                  let c:Hacspec_edwards25519.t_Scalar =
                    scalar_from_hash (Hacspec_sha512.sha512 (Hacspec_lib.Seq.concat_under_impl_41 (Hacspec_edwards25519.concat_under_impl_274
                                  r_bytes
                                  pk)
                              msg))
                  in
                  let z:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
                    Hacspec_lib.Seq.slice_under_impl_41 entropy (16sz *. i) 16sz
                  in
                  let z:Hacspec_edwards25519.t_Scalar =
                    Hacspec_edwards25519.from_byte_seq_le_under_impl_67 (Hacspec_lib.Seq.concat_under_impl_41
                          z
                          (Hacspec_lib.Seq.new_under_impl_41 16sz))
                  in
                  let s_sum = s_sum +. s *. z in
                  let r_sum:(Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement &
                    Hacspec_edwards25519.t_Ed25519FieldElement) =
                    Hacspec_edwards25519.point_add r_sum (Hacspec_edwards25519.point_mul z r)
                  in
                  Hacspec_edwards25519.point_add a_sum (Hacspec_edwards25519.point_mul (z *. c) a),
                  r_sum,
                  s_sum))
        in
        let b:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Core.Option.unwrap_under_impl (Hacspec_edwards25519.decompress Hacspec_edwards25519.v_BASE
            )
        in
        let sb:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul s_sum b
        in
        let check:(Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement &
          Hacspec_edwards25519.t_Ed25519FieldElement) =
          Hacspec_edwards25519.point_mul_by_cofactor (Hacspec_edwards25519.point_add (Hacspec_edwards25519.point_neg
                    sb)
                (Hacspec_edwards25519.point_add r_sum a_sum))
        in
        if is_identity check
        then Core.Result.Result.v_Ok ()
        else Core.Result.Result.v_Err Hacspec_edwards25519.Error_InvalidSignature))