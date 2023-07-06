module Hacspec_aes128_gcm
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_AesGcmByteSeqResult = Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8

let v_INVALID_TAG: u8 = 1uy

let pad_aad_msg (aad msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let laad:usize = Hacspec_lib.Seq.len_under_impl_41 aad in
  let lmsg:usize = Hacspec_lib.Seq.len_under_impl_41 msg in
  let pad_aad:usize = if laad %. 16sz =. 0sz then laad else laad +. (16sz -. laad %. 16sz) in
  let pad_msg:usize = if lmsg %. 16sz =. 0sz then lmsg else lmsg +. (16sz -. lmsg %. 16sz) in
  let padded_msg:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 (pad_aad +. pad_msg +. 16sz)
  in
  let padded_msg:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Traits.SeqTrait.update padded_msg 0sz aad
  in
  let padded_msg:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Traits.SeqTrait.update padded_msg pad_aad msg
  in
  let padded_msg:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Traits.SeqTrait.update padded_msg
      (pad_aad +. pad_msg)
      (Hacspec_lib.Transmute.v_U64_to_be_bytes (Secret_integers.U64 (cast laad) *.
            Secret_integers.U64 8uL))
  in
  let padded_msg:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Traits.SeqTrait.update padded_msg
      (pad_aad +. pad_msg +. 8sz)
      (Hacspec_lib.Transmute.v_U64_to_be_bytes (Secret_integers.U64 (cast lmsg) *.
            Secret_integers.U64 8uL))
  in
  padded_msg

let encrypt_aes
      (key: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (iv: Hacspec_aes.t_AesNonce)
      (aad msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & Hacspec_gf128.t_Gf128Tag) =
  let iv0:Hacspec_aes.t_AesNonce = Hacspec_aes.new_under_impl_110 in
  let mac_key:Hacspec_aes.t_Block =
    Core.Result.unwrap_under_impl (Hacspec_aes.aes_ctr_key_block key
          iv0
          (Secret_integers.U32 0ul)
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ROUNDS
          Hacspec_aes.v_KEY_SCHEDULE_LENGTH
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ITERATIONS)
  in
  let tag_mix:Hacspec_aes.t_Block =
    Core.Result.unwrap_under_impl (Hacspec_aes.aes_ctr_key_block key
          (Core.Clone.Clone.clone iv)
          (Secret_integers.U32 1ul)
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ROUNDS
          Hacspec_aes.v_KEY_SCHEDULE_LENGTH
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ITERATIONS)
  in
  let cipher_text:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_aes.aes128_encrypt (Hacspec_aes.from_seq_under_impl_298 key)
      iv
      (Secret_integers.U32 2ul)
      msg
  in
  let padded_msg:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = pad_aad_msg aad cipher_text in
  let tag:Hacspec_gf128.t_Gf128Tag =
    Hacspec_gf128.gmac padded_msg (Hacspec_gf128.from_seq_under_impl_53 mac_key)
  in
  let tag:Hacspec_aes.t_Block =
    Hacspec_aes.xor_block (Hacspec_aes.from_seq_under_impl_18 tag) tag_mix
  in
  cipher_text, Hacspec_gf128.from_seq_under_impl_88 tag

let encrypt_aes128
      (key: Hacspec_aes.t_Key128)
      (iv: Hacspec_aes.t_AesNonce)
      (aad msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & Hacspec_gf128.t_Gf128Tag) =
  encrypt_aes (Hacspec_lib.Seq.from_seq_under_impl_52 key) iv aad msg

let decrypt_aes
      (key: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (iv: Hacspec_aes.t_AesNonce)
      (aad cipher_text: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (tag: Hacspec_gf128.t_Gf128Tag)
    : Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
  let iv0:Hacspec_aes.t_AesNonce = Hacspec_aes.new_under_impl_110 in
  let mac_key:Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
    Core.Ops.Try_trait.FromResidual.from_residual (Hacspec_aes.aes_ctr_key_block key
          iv0
          (Secret_integers.U32 0ul)
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ROUNDS
          Hacspec_aes.v_KEY_SCHEDULE_LENGTH
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ITERATIONS)
  in
  let tag_mix:Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
    Core.Ops.Try_trait.FromResidual.from_residual (Hacspec_aes.aes_ctr_key_block key
          (Core.Clone.Clone.clone iv)
          (Secret_integers.U32 1ul)
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ROUNDS
          Hacspec_aes.v_KEY_SCHEDULE_LENGTH
          Hacspec_aes.v_KEY_LENGTH
          Hacspec_aes.v_ITERATIONS)
  in
  let padded_msg:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = pad_aad_msg aad cipher_text in
  let my_tag:Hacspec_gf128.t_Gf128Tag =
    Hacspec_gf128.gmac padded_msg (Hacspec_gf128.from_seq_under_impl_53 mac_key)
  in
  let my_tag:Hacspec_aes.t_Block =
    Hacspec_aes.xor_block (Hacspec_aes.from_seq_under_impl_18 my_tag) tag_mix
  in
  let ptxt:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_aes.aes128_decrypt (Hacspec_aes.from_seq_under_impl_298 key)
      iv
      (Secret_integers.U32 2ul)
      cipher_text
  in
  if Hacspec_aes.declassify_eq_under_impl_2 my_tag (Hacspec_aes.from_seq_under_impl_18 tag)
  then Core.Result.Result.v_Ok ptxt
  else Core.Result.Result.v_Err v_INVALID_TAG

let decrypt_aes128
      (key: Hacspec_aes.t_Key128)
      (iv: Hacspec_aes.t_AesNonce)
      (aad cipher_text: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (tag: Hacspec_gf128.t_Gf128Tag)
    : Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
  decrypt_aes (Hacspec_lib.Seq.from_seq_under_impl_52 key) iv aad cipher_text tag