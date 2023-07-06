module Hacspec_gf128
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BLOCKSIZE: usize = 16sz

unfold
type t_gf128block = lseq uint8 BLOCKSIZE

unfold
type t_gf128key = lseq uint8 BLOCKSIZE

unfold
type t_gf128tag = lseq uint8 BLOCKSIZE

let t_Element = Secret_integers.t_U128

let v_IRRED: Secret_integers.t_U128 =
  Secret_integers.U128 (pub_u128 299076299051606071403356588563077529600sz)

let fadd (x y: Secret_integers.t_U128) : _ = x ^. y

let fmul (x y: Secret_integers.t_U128) : Secret_integers.t_U128 =
  let (res: Secret_integers.t_U128):Secret_integers.t_U128 = Secret_integers.U128 (pub_u128 0sz) in
  let sh:Secret_integers.t_U128 = x in
  let res, sh:(_ & _) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 128sz
            }))
      (res, sh)
      (fun (res, sh) i ->
          let res =
            if
              Secret_integers.declassify_under_impl_126 (y &.
                  Secret_integers.U128 (pub_u128 1sz) >>. 127sz -. i) <>.
              Secret_integers.declassify_under_impl_126 (Secret_integers.U128 (pub_u128 0sz))
            then
              let res = res ^. sh in
              res
            else res
          in
          if
            Secret_integers.declassify_under_impl_126 (sh &. Secret_integers.U128 (pub_u128 1sz)) <>.
            Secret_integers.declassify_under_impl_126 (Secret_integers.U128 (pub_u128 0sz))
          then
            let sh = (sh <<. 1sz) ^. v_IRRED in
            res, sh
          else
            let sh = sh <<. 1sz in
            res, sh)
  in
  res

let encode (block: t_Gf128Block) : Secret_integers.t_U128 =
  Hacspec_lib.Transmute.v_U128_from_be_bytes (Hacspec_lib.Prelude.from_seq_under_impl_123 block)

let decode (e: Secret_integers.t_U128) : t_Gf128Block =
  from_seq_under_impl_18 (Hacspec_lib.Transmute.v_U128_to_be_bytes e)

let update (r: Secret_integers.t_U128) (block: t_Gf128Block) (acc: Secret_integers.t_U128)
    : Secret_integers.t_U128 = fmul (fadd (encode block) acc) r

let poly (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (r: Secret_integers.t_U128)
    : Secret_integers.t_U128 =
  let l:usize = Hacspec_lib.Seq.len_under_impl_41 msg in
  let (n_blocks: usize):usize = l /. v_BLOCKSIZE in
  let rem:usize = l %. v_BLOCKSIZE in
  let acc:Secret_integers.t_U128 = Secret_integers.U128 (pub_u128 0sz) in
  let acc:Secret_integers.t_U128 =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = n_blocks
            }))
      acc
      (fun acc i ->
          let k:usize = i *. v_BLOCKSIZE in
          let block:t_Gf128Block = new_under_impl_5 in
          let block:t_Gf128Block =
            Hacspec_lib.Traits.SeqTrait.update_start block
              (Hacspec_lib.Seq.slice_range_under_impl_41 msg
                  ({
                      Core.Ops.Range.Range.f_start = k;
                      Core.Ops.Range.Range.f_end = k +. v_BLOCKSIZE
                    }))
          in
          let acc:Secret_integers.t_U128 = update r block acc in
          acc)
  in
  let acc:Secret_integers.t_U128 =
    if rem <>. 0sz
    then
      let k:usize = n_blocks *. v_BLOCKSIZE in
      let last_block:t_Gf128Block = new_under_impl_5 in
      let last_block:t_Gf128Block =
        Hacspec_lib.Traits.SeqTrait.update_slice last_block 0sz msg k rem
      in
      let acc:Secret_integers.t_U128 = update r last_block acc in
      acc
    else acc
  in
  acc

let gmac (text: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (k: t_Gf128Key) : t_Gf128Tag =
  let s:t_Gf128Block = new_under_impl_5 in
  let r:Secret_integers.t_U128 = encode (from_seq_under_impl_18 k) in
  let a:Secret_integers.t_U128 = poly text r in
  from_seq_under_impl_88 (decode (fadd a (encode s)))