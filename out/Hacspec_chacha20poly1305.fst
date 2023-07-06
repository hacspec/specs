module Hacspec_chacha20poly1305
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_Error = | Error_InvalidTag : t_Error

let t_ChaChaPolyKey = Hacspec_chacha20.t_ChaChaKey

let t_ChaChaPolyIV = Hacspec_chacha20.t_ChaChaIV

let t_ByteSeqResult = Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) t_Error

let init (key: Hacspec_chacha20.t_ChaChaKey) (iv: Hacspec_chacha20.t_ChaChaIV)
    : (Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
      Hacspec_poly1305.t_PolyKey) =
  let key_block0:Hacspec_chacha20.t_Block = Hacspec_chacha20.chacha20_key_block0 key iv in
  let poly_key:Hacspec_poly1305.t_PolyKey =
    Hacspec_poly1305.from_slice_under_impl_6 key_block0 0sz 32sz
  in
  Hacspec_poly1305.poly1305_init poly_key

let poly1305_update_padded
      (m: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (st:
          (Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
            Hacspec_poly1305.t_PolyKey))
    : (Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
      Hacspec_poly1305.t_PolyKey) =
  let st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    Hacspec_poly1305.poly1305_update_blocks m st
  in
  let last:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.get_remainder_chunk_under_impl_41 m 16sz
  in
  Hacspec_poly1305.poly1305_update_last 16sz last st

let finish
      (aad_len cipher_len: usize)
      (st:
          (Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
            Hacspec_poly1305.t_PolyKey))
    : Hacspec_poly1305.t_Poly1305Tag =
  let last_block:Hacspec_poly1305.t_PolyBlock = Hacspec_poly1305.new_under_impl_40 in
  let last_block:Hacspec_poly1305.t_PolyBlock =
    Hacspec_lib.Traits.SeqTrait.update last_block
      0sz
      (Hacspec_lib.Transmute.v_U64_to_le_bytes (Secret_integers.U64 (cast aad_len)))
  in
  let last_block:Hacspec_poly1305.t_PolyBlock =
    Hacspec_lib.Traits.SeqTrait.update last_block
      8sz
      (Hacspec_lib.Transmute.v_U64_to_le_bytes (Secret_integers.U64 (cast cipher_len)))
  in
  let st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    Hacspec_poly1305.poly1305_update_block last_block st
  in
  Hacspec_poly1305.poly1305_finish st

let chacha20_poly1305_encrypt
      (key: Hacspec_chacha20.t_ChaChaKey)
      (iv: Hacspec_chacha20.t_ChaChaIV)
      (aad msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & Hacspec_poly1305.t_Poly1305Tag) =
  let cipher_text:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_chacha20.chacha20 key iv 1ul msg
  in
  let poly_st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    init key iv
  in
  let poly_st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    poly1305_update_padded aad poly_st
  in
  let poly_st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    poly1305_update_padded cipher_text poly_st
  in
  let tag:Hacspec_poly1305.t_Poly1305Tag =
    finish (Hacspec_lib.Seq.len_under_impl_41 aad)
      (Hacspec_lib.Seq.len_under_impl_41 cipher_text)
      poly_st
  in
  cipher_text, tag

let chacha20_poly1305_decrypt
      (key: Hacspec_chacha20.t_ChaChaKey)
      (iv: Hacspec_chacha20.t_ChaChaIV)
      (aad cipher_text: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (tag: Hacspec_poly1305.t_Poly1305Tag)
    : Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) t_Error =
  let poly_st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    init key iv
  in
  let poly_st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    poly1305_update_padded aad poly_st
  in
  let poly_st:(Hacspec_poly1305.t_FieldElement & Hacspec_poly1305.t_FieldElement &
    Hacspec_poly1305.t_PolyKey) =
    poly1305_update_padded cipher_text poly_st
  in
  let my_tag:Hacspec_poly1305.t_Poly1305Tag =
    finish (Hacspec_lib.Seq.len_under_impl_41 aad)
      (Hacspec_lib.Seq.len_under_impl_41 cipher_text)
      poly_st
  in
  if Hacspec_poly1305.declassify_eq_under_impl_72 my_tag tag
  then Core.Result.Result.v_Ok (Hacspec_chacha20.chacha20 key iv 1ul cipher_text)
  else Core.Result.Result.v_Err Error_InvalidTag