module Hacspec_hkdf
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_HASH_LEN: usize = 256sz /. 8sz

type t_HkdfError = | HkdfError_InvalidOutputLength : t_HkdfError

let t_HkdfByteSeqResult =
  Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) t_HkdfError

let extract (salt ikm: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : Hacspec_hmac.t_PRK =
  let salt_or_zero:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 v_HASH_LEN
  in
  let salt_or_zero:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    if Hacspec_lib.Seq.len_under_impl_41 salt >. 0sz
    then Hacspec_lib.Seq.from_seq_under_impl_52 salt
    else salt_or_zero
  in
  Hacspec_hmac.from_seq_under_impl_18 (Hacspec_hmac.hmac salt_or_zero ikm)

let build_hmac_txt
      (t info: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (iteration: Secret_integers.t_U8)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 (Hacspec_lib.Seq.len_under_impl_41 t +.
        Hacspec_lib.Seq.len_under_impl_41 info +.
        1sz)
  in
  let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Traits.SeqTrait.update out 0sz t
  in
  let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Traits.SeqTrait.update out (Hacspec_lib.Seq.len_under_impl_41 t) info
  in
  let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Rust_primitives.Hax.update_at out
      (Hacspec_lib.Seq.len_under_impl_41 t +. Hacspec_lib.Seq.len_under_impl_41 info)
      iteration
  in
  out

let div_ceil (a b: usize) : usize =
  let q:usize = a /. b in
  let q:usize =
    if a %. b <>. 0sz
    then
      let q:usize = q +. 1sz in
      q
    else q
  in
  q

let check_output_limit (l: usize) : Core.Result.t_Result usize t_HkdfError =
  let n:usize = div_ceil l v_HASH_LEN in
  if n <=. 255sz
  then Core.Result.Result_Ok n
  else Core.Result.Result_Err HkdfError_InvalidOutputLength

let expand (prk info: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (l: usize)
    : Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) t_HkdfError =
  let n:Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) t_HkdfError =
    Core.Ops.Try_trait.FromResidual.from_residual (check_output_limit l)
  in
  let t_i:Hacspec_hmac.t_PRK = Hacspec_hmac.new_under_impl_5 in
  let t:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 (n *. Hacspec_sha256.v_HASH_SIZE)
  in
  let t, t_i:(Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & Hacspec_hmac.t_PRK) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = n
            }))
      (t, t_i)
      (fun (t, t_i) i ->
          let hmac_txt_in:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            if i =. 0sz
            then
              build_hmac_txt (Hacspec_lib.Seq.new_under_impl_41 0sz)
                info
                (Secret_integers.U8 (cast i +. 1uy))
            else
              build_hmac_txt (Hacspec_lib.Seq.from_seq_under_impl_52 t_i)
                info
                (Secret_integers.U8 (cast i +. 1uy))
          in
          let t_i:Hacspec_hmac.t_PRK = Hacspec_hmac.hmac prk hmac_txt_in in
          let t:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Traits.SeqTrait.update t (i *. Hacspec_lib.Traits.SeqTrait.len t_i) t_i
          in
          t, t_i)
  in
  Core.Result.Result.v_Ok (Hacspec_lib.Seq.slice_under_impl_41 t 0sz l)