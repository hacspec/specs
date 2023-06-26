module Chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_State = array u32 16sz

let t_Block = array u8 64sz

let t_ChaChaIV = array u8 12sz

let t_ChaChaKey = array u8 32sz

let t_StateIdx = Hax.Lib.bounded_index 16sz

let v_BoundedIndex (x: usize {SizeT.v x < 16}): t_StateIdx = Hax.Lib.Bounded x

let chacha20_line (a b d: t_StateIdx) (s: u32) (m: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = m in
  let state:array u32 16sz =
    state.[ a ] <- Core.Num.wrapping_add_under_impl_8 state.[ a ] state.[ b ]
  in
  let state:array u32 16sz = state.[ d ] <- state.[ d ] ^. state.[ a ] in
  let state:array u32 16sz = state.[ d ] <- Core.Num.rotate_left_under_impl_8 state.[ d ] s in
  state

let chacha20_quarter_round (a b c d: t_StateIdx) (state: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = chacha20_line a b d 16ul state in
  let state:array u32 16sz = chacha20_line c d b 12ul state in
  let state:array u32 16sz = chacha20_line a b d 8ul state in
  chacha20_line c d b 7ul state

let chacha20_double_round (state: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz =
    chacha20_quarter_round (v_BoundedIndex 0sz)
      (v_BoundedIndex 4sz)
      (v_BoundedIndex 8sz)
      (v_BoundedIndex 12sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (v_BoundedIndex 1sz)
      (v_BoundedIndex 5sz)
      (v_BoundedIndex 9sz)
      (v_BoundedIndex 13sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (v_BoundedIndex 2sz)
      (v_BoundedIndex 6sz)
      (v_BoundedIndex 10sz)
      (v_BoundedIndex 14sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (v_BoundedIndex 3sz)
      (v_BoundedIndex 7sz)
      (v_BoundedIndex 11sz)
      (v_BoundedIndex 15sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (v_BoundedIndex 0sz)
      (v_BoundedIndex 5sz)
      (v_BoundedIndex 10sz)
      (v_BoundedIndex 15sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (v_BoundedIndex 1sz)
      (v_BoundedIndex 6sz)
      (v_BoundedIndex 11sz)
      (v_BoundedIndex 12sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (v_BoundedIndex 2sz)
      (v_BoundedIndex 7sz)
      (v_BoundedIndex 8sz)
      (v_BoundedIndex 13sz)
      state
  in
  chacha20_quarter_round (v_BoundedIndex 3sz)
    (v_BoundedIndex 4sz)
    (v_BoundedIndex 9sz)
    (v_BoundedIndex 14sz)
    state

let chacha20_rounds (state: array u32 16sz) : array u32 16sz =
  let st:array u32 16sz = state in
  let st:array u32 16sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 10sz
            }))
      st
      (fun st _i -> chacha20_double_round st)
  in
  st

let chacha20_core (ctr: u32) (st0: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = st0 in
  let state:array u32 16sz =
    state.[ 12sz ] <- Core.Num.wrapping_add_under_impl_8 state.[ 12sz ] ctr
  in
  let k:array u32 16sz = chacha20_rounds state in
  Chacha20.Hacspec_helper.add_state state k

let chacha20_init (key: array u8 32sz) (iv: array u8 12sz) (ctr: u32) : array u32 16sz =
  let (key_u32: array u32 8sz):array u32 8sz =
    Chacha20.Hacspec_helper.to_le_u32s_8_ (Hax.CoerceUnsize.unsize key)
  in
  let (iv_u32: array u32 3sz):array u32 3sz =
    Chacha20.Hacspec_helper.to_le_u32s_3_ (Hax.CoerceUnsize.unsize iv)
  in
  (let l =
      [
        1634760805ul; 857760878ul; 2036477234ul; 1797285236ul; key_u32.[ 0sz ]; key_u32.[ 1sz ];
        key_u32.[ 2sz ]; key_u32.[ 3sz ]; key_u32.[ 4sz ]; key_u32.[ 5sz ]; key_u32.[ 6sz ];
        key_u32.[ 7sz ]; ctr; iv_u32.[ 0sz ]; iv_u32.[ 1sz ]; iv_u32.[ 2sz ]
      ]
    in
    assert_norm (List.Tot.length l == 16);
    array_of_list l)

let chacha20_key_block (state: array u32 16sz) : array u8 64sz =
  let state:array u32 16sz = chacha20_core 0ul state in
  Chacha20.Hacspec_helper.u32s_to_le_bytes state

let chacha20_key_block0 (key: array u8 32sz) (iv: array u8 12sz) : array u8 64sz =
  let state:array u32 16sz = chacha20_init key iv 0ul in
  chacha20_key_block state

let chacha20_encrypt_block (st0: array u32 16sz) (ctr: u32) (plain: array u8 64sz) : array u8 64sz =
  let st:array u32 16sz = chacha20_core ctr st0 in
  let (pl: array u32 16sz):array u32 16sz =
    Chacha20.Hacspec_helper.to_le_u32s_16_ (Hax.CoerceUnsize.unsize plain)
  in
  let encrypted:array u32 16sz = Chacha20.Hacspec_helper.xor_state st pl in
  Chacha20.Hacspec_helper.u32s_to_le_bytes encrypted

let chacha20_encrypt_last (st0: array u32 16sz) (ctr: u32) (plain: slice u8 {Seq.length plain < 64})
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let (b: array u8 64sz):array u8 64sz = Hax.Array.repeat 0uy 64sz in
  let b:array u8 64sz = Chacha20.Hacspec_helper.update_array b plain in
  let b:array u8 64sz = chacha20_encrypt_block st0 ctr b in
  Alloc.Slice.to_vec_under_impl b.[ {
        Core.Ops.Range.RangeTo.f_end = Core.Slice.len_under_impl plain
      } ]

let chacha20_update (st0: array u32 16sz) (m: slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let num_blocks:usize = Core.Slice.len_under_impl m /. 64sz in
  let remainder_len:usize = Core.Slice.len_under_impl m %. 64sz in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = num_blocks
            }))
      blocks_out
      (fun blocks_out i ->
          let b:array u8 64sz =
            chacha20_encrypt_block st0
              (SizeT.sizet_to_uint32 i)
              (Core.Result.unwrap_under_impl (Core.Convert.try_into ((m.[ {
                          Core.Ops.Range.Range.f_start = 64sz *. i;
                          Core.Ops.Range.Range.f_end = 64sz *. i +. 64sz
                        } ]) <: slice u8) <: Core.Result.t_Result (array u8 64sz) _))
          in
          let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.extend_from_slice_under_impl_2 blocks_out (Hax.CoerceUnsize.unsize b)
          in
          blocks_out)
  in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if remainder_len <>. 0sz
    then
      let b:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        chacha20_encrypt_last st0
          (SizeT.sizet_to_uint32 num_blocks)
          m.[ { Core.Ops.Range.RangeFrom.f_start = 64sz *. num_blocks } ]
      in
      let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.extend_from_slice_under_impl_2 blocks_out (Core.Ops.Deref.Deref.deref b)
      in
      blocks_out
    else blocks_out
  in
  blocks_out

let chacha20 (m: slice u8) (key: array u8 32sz) (iv: array u8 12sz) (ctr: u32)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let state:array u32 16sz = chacha20_init key iv ctr in
  chacha20_update state m
