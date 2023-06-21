module Chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core
// open Hacspec.Lib
// open Hacspec_lib_tc

let t_State = array u32 16sz

let t_Block = array u8 64sz

let t_ChaChaIV = array u8 12sz

let t_ChaChaKey = array u8 32sz

open Hax.Lib
type t_state_idx = bounded_index 16sz

let chacha20_line (a b d: t_state_idx) (s: u32) (m: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = m in
  let state:array u32 16sz =
    state.[ a ] <- Core.Num.wrapping_add_under_impl_8 state.[ a ] state.[ b ]
  in
  let state:array u32 16sz = state.[ d ] <- state.[ d ] ^. state.[ a ] in
  let state:array u32 16sz = state.[ d ] <- Core.Num.rotate_left_under_impl_8 state.[ d ] s in
  state

let chacha20_quarter_round (a b c d: t_state_idx) (state: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = chacha20_line a b d 16ul state in
  let state:array u32 16sz = chacha20_line c d b 12ul state in
  let state:array u32 16sz = chacha20_line a b d 8ul state in
  chacha20_line c d b 7ul state

let chacha20_double_round (state: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = chacha20_quarter_round (Bounded 0sz) (Bounded 4sz) (Bounded 8sz) (Bounded 12sz) state in
  let state:array u32 16sz = chacha20_quarter_round (Bounded 1sz) (Bounded 5sz) (Bounded 9sz) (Bounded 13sz) state in
  let state:array u32 16sz = chacha20_quarter_round (Bounded 2sz) (Bounded 6sz) (Bounded 10sz) (Bounded 14sz) state in
  let state:array u32 16sz = chacha20_quarter_round (Bounded 3sz) (Bounded 7sz) (Bounded 11sz) (Bounded 15sz) state in
  let state:array u32 16sz = chacha20_quarter_round (Bounded 0sz) (Bounded 5sz) (Bounded 10sz) (Bounded 15sz) state in
  let state:array u32 16sz = chacha20_quarter_round (Bounded 1sz) (Bounded 6sz) (Bounded 11sz) (Bounded 12sz) state in
  let state:array u32 16sz = chacha20_quarter_round (Bounded 2sz) (Bounded 7sz) (Bounded 8sz) (Bounded 13sz) state in
  chacha20_quarter_round (Bounded 3sz) (Bounded 4sz) (Bounded 9sz) (Bounded 14sz) state

let chacha20_rounds (state: array u32 16sz) : array u32 16sz =
  let st:array u32 16sz = state in
  let st:array u32 16sz =
    Core.Iter.fold (Core.Iter.into_iter (
                   {
              f_start = 0sz;
              f_end = 10sz
            }
            ))
      st
      (fun st _i -> chacha20_double_round st)
  in
  st

let chacha20_core (ctr: u32) (st0: array u32 16sz) : array u32 16sz =
  let state:array u32 16sz = st0 in
  let state:array u32 16sz = state.[ 12sz ] <- state.[ 12sz ] +. ctr in
  let k:array u32 16sz = chacha20_rounds state in
  Chacha20.Hacspec_helper.add_state state k

// let chacha20_init (key: array u8 32sz) (iv: array u8 12sz) (ctr: u32) : array u32 16sz =
//   let (key_u32: array u32 8sz):array u32 8sz =
//     Chacha20.Hacspec_helper.to_le_u32s_8_ (Hax.CoerceUnsize.unsize key)
//   in
//   let (iv_u32: array u32 3sz):array u32 3sz =
//     Chacha20.Hacspec_helper.to_le_u32s_3_ (Hax.CoerceUnsize.unsize iv)
//   in
//   [
//     1634760805ul; 857760878ul; 2036477234ul; 1797285236ul; key_u32.[ 0sz ]; key_u32.[ 1sz ];
//     key_u32.[ 2sz ]; key_u32.[ 3sz ]; key_u32.[ 4sz ]; key_u32.[ 5sz ]; key_u32.[ 6sz ];
//     key_u32.[ 7sz ]; ctr; iv_u32.[ 0sz ]; iv_u32.[ 1sz ]; iv_u32.[ 2sz ]
//   ]

// let chacha20_key_block (state: array u32 16sz) : array u8 64sz =
//   let state:array u32 16sz = chacha20_core 0ul state in
//   Chacha20.Hacspec_helper.u32s_to_le_bytes state

// let chacha20_key_block0 (key: array u8 32sz) (iv: array u8 12sz) : array u8 64sz =
//   let state:array u32 16sz = chacha20_init key iv 0ul in
//   chacha20_key_block state

// let chacha20_encrypt_block (st0: array u32 16sz) (ctr: u32) (plain: array u8 64sz) : array u8 64sz =
//   let st:array u32 16sz = chacha20_core ctr st0 in
//   let (pl: array u32 16sz):array u32 16sz =
//     Chacha20.Hacspec_helper.to_le_u32s_16_ (Hax.CoerceUnsize.unsize plain)
//   in
//   let encrypted:array u32 16sz = Chacha20.Hacspec_helper.xor_state st pl in
//   Chacha20.Hacspec_helper.u32s_to_le_bytes encrypted

// let chacha20_encrypt_last (st0: array u32 16sz) (ctr: u32) (plain: slice u8)
//     : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//   let (b: array u8 64sz):array u8 64sz = Hax.Array.repeat 0uy 64sz in
//   let b:array u8 64sz = Chacha20.Hacspec_helper.update_array b plain in
//   let b:array u8 64sz = chacha20_encrypt_block st0 ctr b in
//   Alloc.Slice.to_vec_under_impl b.[ { f_end = Core.Slice.len_under_impl plain } ]

// let chacha20_update (st0: array u32 16sz) (m: slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//   let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
//   let num_blocks:usize = Core.Slice.len_under_impl m / 64sz in
//   let remainder_len:usize = Core.Slice.len_under_impl m % 64sz in
//   let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//     Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
//               f_start = 0sz;
//               f_end = num_blocks
//             }))
//       blocks_out
//       (fun i blocks_out ->
//           let b:array u8 64sz =
//             chacha20_encrypt_block st0
//               (cast i)
//               (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into m.[ {
//                           f_start = 64sz * i;
//                           f_end = 64sz * i + 64sz
//                         } ]))
//           in
//           let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//             Alloc.Vec.extend_from_slice_under_impl_2 blocks_out (Hax.CoerceUnsize.unsize b)
//           in
//           blocks_out)
//   in
//   let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//     if remainder_len <> 0sz
//     then
//       let b:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//         chacha20_encrypt_last st0 (cast num_blocks) m.[ { f_start = 64sz * num_blocks } ]
//       in
//       let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//         Alloc.Vec.extend_from_slice_under_impl_2 blocks_out (Core.Ops.Deref.Deref.deref b)
//       in
//       blocks_out
//     else blocks_out
//   in
//   blocks_out

// let chacha20 (m: slice u8) (key: array u8 32sz) (iv: array u8 12sz) (ctr: u32)
//     : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
//   let state:array u32 16sz = chacha20_init key iv ctr in
//   chacha20_update state m
