module Hacspec_hmac
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BLOCK_LEN: usize = Hacspec_sha256.v_K_SIZE

unfold
type t_prk = lseq uint8 HASH_SIZE

unfold
type t_block = lseq uint8 BLOCK_LEN

let v_I_PAD: t_Block =
  Block
  (let l =
      [
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy; Secret_integers.U8 54uy; Secret_integers.U8 54uy;
        Secret_integers.U8 54uy
      ]
    in
    assert_norm (List.Tot.length l == 64);
    Rust_primitives.Hax.array_of_list l)

let v_O_PAD: t_Block =
  Block
  (let l =
      [
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy; Secret_integers.U8 92uy; Secret_integers.U8 92uy;
        Secret_integers.U8 92uy
      ]
    in
    assert_norm (List.Tot.length l == 64);
    Rust_primitives.Hax.array_of_list l)

let k_block (k: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Block =
  if Hacspec_lib.Seq.len_under_impl_41 k >. v_BLOCK_LEN
  then Hacspec_lib.Traits.SeqTrait.update_start new_under_impl_40 (Hacspec_sha256.hash k)
  else Hacspec_lib.Traits.SeqTrait.update_start new_under_impl_40 k

let hmac (k txt: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_PRK =
  let k_block:t_Block = k_block k in
  let h_in:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.from_seq_under_impl_52 (k_block ^. v_I_PAD)
  in
  let h_in:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.concat_under_impl_41 h_in txt
  in
  let h_inner:Hacspec_sha256.t_Sha256Digest = Hacspec_sha256.hash h_in in
  let h_in:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.from_seq_under_impl_52 (k_block ^. v_O_PAD)
  in
  let h_in:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.concat_under_impl_41 h_in h_inner
  in
  from_seq_under_impl_18 (Hacspec_sha256.hash h_in)