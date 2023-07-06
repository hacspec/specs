module Hacspec_poly1305
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_polykey = lseq uint8 32

let v_BLOCKSIZE: usize = 16sz

unfold
type t_polyblock = lseq uint8 16

unfold
type t_poly1305tag = lseq uint8 16

let t_SubBlock = Hacspec_lib.Seq.t_Seq Secret_integers.t_U8

let t_BlockIndex = usize

unfold
type t_fieldelement = nat_mod 0x03fffffffffffffffffffffffffffffffb
unfold
type t_fieldcanvas = lseq pub_uint8 131

let t_PolyState = (t_FieldElement & t_FieldElement & t_PolyKey)

let poly1305_encode_r (b: t_PolyBlock) : t_FieldElement =
  let n:Secret_integers.t_U128 =
    Hacspec_lib.Transmute.v_U128_from_le_bytes (Hacspec_lib.Prelude.from_seq_under_impl_123 b)
  in
  let n = n &. Secret_integers.U128 (pub_u128 21267647620597763993911028882763415551sz) in
  from_secret_literal_under_impl_105 n

let poly1305_encode_block (b: t_PolyBlock) : _ =
  let n:Secret_integers.t_U128 =
    Hacspec_lib.Transmute.v_U128_from_le_bytes (Hacspec_lib.Prelude.from_seq_under_impl_123 b)
  in
  let f:t_FieldElement = from_secret_literal_under_impl_105 n in
  f +. pow2_under_impl_162 128sz

let poly1305_encode_last (pad_len: usize) (b: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : _ =
  let n:Secret_integers.t_U128 =
    Hacspec_lib.Transmute.v_U128_from_le_bytes (Hacspec_lib.Prelude.from_slice_under_impl_111 b
          0sz
          (Hacspec_lib.Seq.len_under_impl_41 b))
  in
  let f:t_FieldElement = from_secret_literal_under_impl_105 n in
  f +. pow2_under_impl_162 (8sz *. pad_len)

let poly1305_init (k: t_PolyKey) : (t_FieldElement & t_FieldElement & t_PolyKey) =
  let r:t_FieldElement = poly1305_encode_r (from_slice_under_impl_41 k 0sz 16sz) in
  Hacspec_lib.Traits.Integer.v_ZERO, r, k

let poly1305_update_block (b: t_PolyBlock) (st: (t_FieldElement & t_FieldElement & t_PolyKey))
    : (t_FieldElement & t_FieldElement & t_PolyKey) =
  let acc, r, k:(t_FieldElement & t_FieldElement & t_PolyKey) = st in
  (poly1305_encode_block b +. acc) *. r, r, k

let poly1305_update_blocks
      (m: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (st: (t_FieldElement & t_FieldElement & t_PolyKey))
    : (t_FieldElement & t_FieldElement & t_PolyKey) =
  let st:(t_FieldElement & t_FieldElement & t_PolyKey) = st in
  let n_blocks:usize = Hacspec_lib.Seq.len_under_impl_41 m /. v_BLOCKSIZE in
  let st:(t_FieldElement & t_FieldElement & t_PolyKey) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = n_blocks
            }))
      st
      (fun st i ->
          let block:t_PolyBlock =
            from_seq_under_impl_53 (Hacspec_lib.Seq.get_exact_chunk_under_impl_41 m v_BLOCKSIZE i)
          in
          let st:(t_FieldElement & t_FieldElement & t_PolyKey) = poly1305_update_block block st in
          st)
  in
  st

let poly1305_update_last
      (pad_len: usize)
      (b: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (st: (t_FieldElement & t_FieldElement & t_PolyKey))
    : (t_FieldElement & t_FieldElement & t_PolyKey) =
  let st:(t_FieldElement & t_FieldElement & t_PolyKey) = st in
  let st:(t_FieldElement & t_FieldElement & t_PolyKey) =
    if Hacspec_lib.Seq.len_under_impl_41 b <>. 0sz
    then
      let acc, r, k:(t_FieldElement & t_FieldElement & t_PolyKey) = st in
      let st:(t_FieldElement & t_FieldElement & t_PolyKey) =
        (poly1305_encode_last pad_len b +. acc) *. r, r, k
      in
      st
    else st
  in
  st

let poly1305_update
      (m: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (st: (t_FieldElement & t_FieldElement & t_PolyKey))
    : (t_FieldElement & t_FieldElement & t_PolyKey) =
  let st:(t_FieldElement & t_FieldElement & t_PolyKey) = poly1305_update_blocks m st in
  let last:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.get_remainder_chunk_under_impl_41 m v_BLOCKSIZE
  in
  poly1305_update_last (Hacspec_lib.Seq.len_under_impl_41 last) last st

let poly1305_finish (st: (t_FieldElement & t_FieldElement & t_PolyKey)) : t_Poly1305Tag =
  let acc, _, k:(t_FieldElement & t_FieldElement & t_PolyKey) = st in
  let n:Secret_integers.t_U128 =
    Hacspec_lib.Transmute.v_U128_from_le_bytes (Hacspec_lib.Prelude.from_slice_under_impl_111 k
          16sz
          16sz)
  in
  let aby:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = to_byte_seq_le_under_impl_105 acc in
  let a:Secret_integers.t_U128 =
    Hacspec_lib.Transmute.v_U128_from_le_bytes (Hacspec_lib.Prelude.from_slice_under_impl_111 aby
          0sz
          16sz)
  in
  from_seq_under_impl_88 (Hacspec_lib.Transmute.v_U128_to_le_bytes (a +. n))

let poly1305 (m: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (key: t_PolyKey) : t_Poly1305Tag =
  let st:(t_FieldElement & t_FieldElement & t_PolyKey) = poly1305_init key in
  let st:(t_FieldElement & t_FieldElement & t_PolyKey) = poly1305_update m st in
  poly1305_finish st