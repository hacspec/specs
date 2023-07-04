module Poly1305
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_PolyKey = array u8 32sz

let v_BLOCKSIZE: usize = 16sz

let t_PolyBlock = array u8 16sz

let t_Poly1305Tag = array u8 16sz

let t_SubBlock = Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global

let t_BlockIndex = usize

type t_FieldElement = { f_value:array u8 17sz }

type t_PolyState = {
  f_acc:t_FieldElement;
  f_r:t_FieldElement;
  f_key:array u8 32sz
}

let poly1305_encode_r (b: array u8 16sz) : t_FieldElement =
  let n:u128 = Core.Num.from_le_bytes_under_impl_10 b in
  let n:u128 = n &. pub_u128 21267647620597763993911028882763415551sz in
  Poly1305.Hacspec_helper.NatMod.from_u128 n

let poly1305_encode_block (b: array u8 16sz) : _ =
  let f:t_FieldElement = Poly1305.Hacspec_helper.NatMod.from_le_bytes (Rust_primitives.unsize b) in
  f +. Poly1305.Hacspec_helper.NatMod.pow2 128sz

let poly1305_encode_last (pad_len: usize) (b: slice u8) : _ =
  let f:t_FieldElement = Poly1305.Hacspec_helper.NatMod.from_le_bytes b in
  f +. Poly1305.Hacspec_helper.NatMod.pow2 (8sz *. pad_len)

let poly1305_init (key: array u8 32sz) : t_PolyState =
  let r:t_FieldElement =
    poly1305_encode_r (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into key.[ {
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end = 16sz
                } ]))
  in
  {
    Poly1305.PolyState.f_acc = Poly1305.Hacspec_helper.NatMod.zero;
    Poly1305.PolyState.f_r = r;
    Poly1305.PolyState.f_key = key
  }

let poly1305_update_block (b: array u8 16sz) (st: t_PolyState) : t_PolyState =
  let st:t_PolyState =
    {
      st with
      Poly1305.PolyState.f_acc
      =
      (poly1305_encode_block b +. st.Poly1305.PolyState.f_acc) *. st.Poly1305.PolyState.f_r
    }
  in
  st

let poly1305_update_blocks (m: slice u8) (st: t_PolyState) : t_PolyState =
  let st:t_PolyState =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks_exact_under_impl
              m
              v_BLOCKSIZE))
      st
      (fun st chunk ->
          poly1305_update_block (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into chunk)
            )
            st)
  in
  st

let poly1305_update_last (pad_len: usize) (b: slice u8) (st: t_PolyState) : t_PolyState =
  let st:t_PolyState = st in
  let st:t_PolyState =
    if Core.Slice.len_under_impl b <>. 0sz
    then
      let st:t_PolyState =
        {
          st with
          Poly1305.PolyState.f_acc
          =
          (poly1305_encode_last pad_len b +. st.Poly1305.PolyState.f_acc) *.
          st.Poly1305.PolyState.f_r
        }
      in
      st
    else st
  in
  st

let poly1305_update (m: slice u8) (st: t_PolyState) : t_PolyState =
  let st:t_PolyState = poly1305_update_blocks m st in
  let last:slice u8 =
    Core.Slice.Iter.remainder_under_impl_87 (Core.Slice.chunks_exact_under_impl m v_BLOCKSIZE)
  in
  poly1305_update_last (Core.Slice.len_under_impl last) last st

let poly1305_finish (st: t_PolyState) : array u8 16sz =
  let n:u128 =
    Core.Num.from_le_bytes_under_impl_10 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
              st.Poly1305.PolyState.f_key.[ {
                  Core.Ops.Range.Range.f_start = 16sz;
                  Core.Ops.Range.Range.f_end = 32sz
                } ]))
  in
  let aby:array u8 17sz = Poly1305.Hacspec_helper.NatMod.to_le_bytes st.Poly1305.PolyState.f_acc in
  let a:u128 =
    Core.Num.from_le_bytes_under_impl_10 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
              aby.[ { Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = 16sz } ]))
  in
  Core.Num.to_le_bytes_under_impl_10 (Core.Num.wrapping_add_under_impl_10 a n)

let poly1305 (m: slice u8) (key: array u8 32sz) : array u8 16sz =
  let st:t_PolyState = poly1305_init key in
  let st:t_PolyState = poly1305_update m st in
  poly1305_finish st