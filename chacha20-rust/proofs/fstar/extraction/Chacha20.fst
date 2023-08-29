module Chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_State = array u32 16sz

let t_Block = array u8 64sz

let t_ChaChaIV = array u8 12sz

let t_ChaChaKey = array u8 32sz

let t_StateIdx = Bounded_indexes.t_BoundedIndex 16sz

let chacha20_line (a b d: Bounded_indexes.t_BoundedIndex 16sz) (s: u32) (m: array u32 16sz)
    : array u32 16sz =
  let state:array u32 16sz = m in
  let state:array u32 16sz =
    Rust_primitives.Hax.update_at state
      a
      (Core.Num.wrapping_add_under_impl_8 (state.[ a ] <: u32) (state.[ b ] <: u32) <: u32)
  in
  let state:array u32 16sz =
    Rust_primitives.Hax.update_at state d ((state.[ d ] <: u32) ^. (state.[ a ] <: u32) <: u32)
  in
  let state:array u32 16sz =
    Rust_primitives.Hax.update_at state
      d
      (Core.Num.rotate_left_under_impl_8 (state.[ d ] <: u32) s <: u32)
  in
  state

let chacha20_quarter_round (a b c d: Bounded_indexes.t_BoundedIndex 16sz) (state: array u32 16sz)
    : array u32 16sz =
  let state:array u32 16sz = chacha20_line a b d 16ul state in
  let state:array u32 16sz = chacha20_line c d b 12ul state in
  let state:array u32 16sz = chacha20_line a b d 8ul state in
  chacha20_line c d b 7ul state

let chacha20_double_round (state: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz =
    chacha20_quarter_round (Bounded_indexes.BoundedIndex 0sz)
      (Bounded_indexes.BoundedIndex 4sz)
      (Bounded_indexes.BoundedIndex 8sz)
      (Bounded_indexes.BoundedIndex 12sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (Bounded_indexes.BoundedIndex 1sz)
      (Bounded_indexes.BoundedIndex 5sz)
      (Bounded_indexes.BoundedIndex 9sz)
      (Bounded_indexes.BoundedIndex 13sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (Bounded_indexes.BoundedIndex 2sz)
      (Bounded_indexes.BoundedIndex 6sz)
      (Bounded_indexes.BoundedIndex 10sz)
      (Bounded_indexes.BoundedIndex 14sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (Bounded_indexes.BoundedIndex 3sz)
      (Bounded_indexes.BoundedIndex 7sz)
      (Bounded_indexes.BoundedIndex 11sz)
      (Bounded_indexes.BoundedIndex 15sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (Bounded_indexes.BoundedIndex 0sz)
      (Bounded_indexes.BoundedIndex 5sz)
      (Bounded_indexes.BoundedIndex 10sz)
      (Bounded_indexes.BoundedIndex 15sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (Bounded_indexes.BoundedIndex 1sz)
      (Bounded_indexes.BoundedIndex 6sz)
      (Bounded_indexes.BoundedIndex 11sz)
      (Bounded_indexes.BoundedIndex 12sz)
      state
  in
  let state:array u32 16sz =
    chacha20_quarter_round (Bounded_indexes.BoundedIndex 2sz)
      (Bounded_indexes.BoundedIndex 7sz)
      (Bounded_indexes.BoundedIndex 8sz)
      (Bounded_indexes.BoundedIndex 13sz)
      state
  in
  chacha20_quarter_round (Bounded_indexes.BoundedIndex 3sz)
    (Bounded_indexes.BoundedIndex 4sz)
    (Bounded_indexes.BoundedIndex 9sz)
    (Bounded_indexes.BoundedIndex 14sz)
    state

let chacha20_rounds (state: array u32 16sz) : array u32 16sz =
  let st:array u32 16sz = state in
  let st:array u32 16sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 10sz
            })
        <:
        _)
      st
      (fun st v__i -> chacha20_double_round st <: array u32 16sz)
  in
  st

let chacha20_core (ctr: u32) (st0: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = st0 in
  let state:array u32 16sz =
    Rust_primitives.Hax.update_at state
      12sz
      (Core.Num.wrapping_add_under_impl_8 (state.[ 12sz ] <: u32) ctr <: u32)
  in
  let k:array u32 16sz = chacha20_rounds state in
  Chacha20.Hacspec_helper.add_state state k

let chacha20_init (key: array u8 32sz) (iv: array u8 12sz) (ctr: u32) : array u32 16sz =
  let (key_u32: array u32 8sz):array u32 8sz =
    Chacha20.Hacspec_helper.to_le_u32s_8_ (Rust_primitives.unsize key <: slice u8)
  in
  let (iv_u32: array u32 3sz):array u32 3sz =
    Chacha20.Hacspec_helper.to_le_u32s_3_ (Rust_primitives.unsize iv <: slice u8)
  in
  let list =
    [
      1634760805ul; 857760878ul; 2036477234ul; 1797285236ul; key_u32.[ 0sz ]; key_u32.[ 1sz ];
      key_u32.[ 2sz ]; key_u32.[ 3sz ]; key_u32.[ 4sz ]; key_u32.[ 5sz ]; key_u32.[ 6sz ];
      key_u32.[ 7sz ]; ctr; iv_u32.[ 0sz ]; iv_u32.[ 1sz ]; iv_u32.[ 2sz ]
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
  Rust_primitives.Hax.array_of_list list

let chacha20_key_block (state: array u32 16sz) : array u8 64sz =
  let state:array u32 16sz = chacha20_core 0ul state in
  Chacha20.Hacspec_helper.u32s_to_le_bytes state

let chacha20_key_block0 (key: array u8 32sz) (iv: array u8 12sz) : array u8 64sz =
  let state:array u32 16sz = chacha20_init key iv 0ul in
  chacha20_key_block state

let chacha20_encrypt_block (st0: array u32 16sz) (ctr: u32) (plain: array u8 64sz) : array u8 64sz =
  let st:array u32 16sz = chacha20_core ctr st0 in
  let (pl: array u32 16sz):array u32 16sz =
    Chacha20.Hacspec_helper.to_le_u32s_16_ (Rust_primitives.unsize plain <: slice u8)
  in
  let encrypted:array u32 16sz = Chacha20.Hacspec_helper.xor_state st pl in
  Chacha20.Hacspec_helper.u32s_to_le_bytes encrypted

let chacha20_encrypt_last (st0: array u32 16sz) (ctr: u32) (plain: slice u8)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let (b: array u8 64sz):array u8 64sz = Rust_primitives.Hax.repeat 0uy 64sz in
  let b:array u8 64sz = Chacha20.Hacspec_helper.update_array b plain in
  let b:array u8 64sz = chacha20_encrypt_block st0 ctr b in
  Alloc.Slice.to_vec_under_impl (b.[ {
          Core.Ops.Range.RangeTo.f_end = Core.Slice.len_under_impl plain <: usize
        } ]
      <:
      slice u8)

let chacha20_update (st0: array u32 16sz) (m: slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let num_blocks:usize = (Core.Slice.len_under_impl m <: usize) /. 64sz in
  let remainder_len:usize = (Core.Slice.len_under_impl m <: usize) %. 64sz in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = num_blocks
            })
        <:
        _)
      blocks_out
      (fun blocks_out i ->
          let b:array u8 64sz =
            chacha20_encrypt_block st0
              (cast i)
              (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into (m.[ {
                            Core.Ops.Range.Range.f_start = 64sz *. i <: usize;
                            Core.Ops.Range.Range.f_end = (64sz *. i <: usize) +. 64sz <: usize
                          } ]
                        <:
                        slice u8)
                    <:
                    Core.Result.t_Result (array u8 64sz) _)
                <:
                array u8 64sz)
          in
          let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.extend_from_slice_under_impl_2 blocks_out
              (Rust_primitives.unsize b <: slice u8)
          in
          blocks_out)
  in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if remainder_len <>. 0sz
    then
      let b:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        chacha20_encrypt_last st0
          (cast num_blocks)
          (m.[ { Core.Ops.Range.RangeFrom.f_start = 64sz *. num_blocks <: usize } ] <: slice u8)
      in
      let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.extend_from_slice_under_impl_2 blocks_out
          (Core.Ops.Deref.Deref.deref b <: slice u8)
      in
      blocks_out
    else blocks_out
  in
  blocks_out

let chacha20 (m: slice u8) (key: array u8 32sz) (iv: array u8 12sz) (ctr: u32)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let state:array u32 16sz = chacha20_init key iv ctr in
  chacha20_update state m
