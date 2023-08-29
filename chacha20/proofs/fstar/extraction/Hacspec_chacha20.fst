module Hacspec_chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_state = lseq uint32 16
unfold
type t_state_idx = nat_mod 16

unfold
type t_constants = lseq uint32 4
unfold
type t_constants_idx = nat_mod 4

unfold
type t_block = lseq uint8 64

unfold
type t_chachaiv = lseq uint8 12

unfold
type t_chachakey = lseq uint8 32

let chacha20_line (a b d s: usize) (m: t_State) : t_State =
  let state:t_State = m in
  let state:t_State =
    Rust_primitives.Hax.update_at state
      a
      ((state.[ a ] <: Secret_integers.t_U32) +. (state.[ b ] <: Secret_integers.t_U32) <: _)
  in
  let state:t_State =
    Rust_primitives.Hax.update_at state
      d
      ((state.[ d ] <: Secret_integers.t_U32) ^. (state.[ a ] <: Secret_integers.t_U32) <: _)
  in
  let state:t_State =
    Rust_primitives.Hax.update_at state
      d
      (Secret_integers.rotate_left_under_impl_66 (state.[ d ] <: Secret_integers.t_U32) s
        <:
        Secret_integers.t_U32)
  in
  state

let chacha20_quarter_round (a b c d: usize) (state: t_State) : t_State =
  let state:t_State = chacha20_line a b d 16sz state in
  let state:t_State = chacha20_line c d b 12sz state in
  let state:t_State = chacha20_line a b d 8sz state in
  chacha20_line c d b 7sz state

let chacha20_double_round (state: t_State) : t_State =
  let state:t_State = chacha20_quarter_round 0sz 4sz 8sz 12sz state in
  let state:t_State = chacha20_quarter_round 1sz 5sz 9sz 13sz state in
  let state:t_State = chacha20_quarter_round 2sz 6sz 10sz 14sz state in
  let state:t_State = chacha20_quarter_round 3sz 7sz 11sz 15sz state in
  let state:t_State = chacha20_quarter_round 0sz 5sz 10sz 15sz state in
  let state:t_State = chacha20_quarter_round 1sz 6sz 11sz 12sz state in
  let state:t_State = chacha20_quarter_round 2sz 7sz 8sz 13sz state in
  chacha20_quarter_round 3sz 4sz 9sz 14sz state

let chacha20_rounds (state: t_State) : t_State =
  let st:t_State = state in
  let st:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 10l
            })
        <:
        _)
      st
      (fun st v__i -> chacha20_double_round st <: t_State)
  in
  st

let chacha20_core (ctr: Secret_integers.t_U32) (st0: t_State) : t_State =
  let state:t_State = st0 in
  let state:t_State =
    Rust_primitives.Hax.update_at state 12l ((state.[ 12l ] <: Secret_integers.t_U32) +. ctr <: _)
  in
  let k:t_State = chacha20_rounds state in
  k +. state

let chacha20_constants_init: t_Constants =
  let constants:t_Constants = new_under_impl_38 in
  let constants:t_Constants =
    Rust_primitives.Hax.update_at constants 0l (Secret_integers.U32 1634760805ul)
  in
  let constants:t_Constants =
    Rust_primitives.Hax.update_at constants 1l (Secret_integers.U32 857760878ul)
  in
  let constants:t_Constants =
    Rust_primitives.Hax.update_at constants 2l (Secret_integers.U32 2036477234ul)
  in
  let constants:t_Constants =
    Rust_primitives.Hax.update_at constants 3l (Secret_integers.U32 1797285236ul)
  in
  constants

let chacha20_init (key: t_ChaChaKey) (iv: t_ChaChaIV) (ctr: Secret_integers.t_U32) : t_State =
  let st:t_State = new_under_impl_4 in
  let st:t_State =
    Hacspec_lib.Traits.SeqTrait.update st 0sz (chacha20_constants_init <: t_Constants)
  in
  let st:t_State =
    Hacspec_lib.Traits.SeqTrait.update st
      4sz
      (to_le_U32s_under_impl_138 key <: Hacspec_lib.Seq.t_Seq Secret_integers.t_U32)
  in
  let st:t_State = Rust_primitives.Hax.update_at st 12l ctr in
  let st:t_State =
    Hacspec_lib.Traits.SeqTrait.update st
      13sz
      (to_le_U32s_under_impl_103 iv <: Hacspec_lib.Seq.t_Seq Secret_integers.t_U32)
  in
  st

let chacha20_key_block (state: t_State) : t_Block =
  let state:t_State = chacha20_core (Secret_integers.U32 0ul) state in
  from_seq_under_impl_86 (to_le_bytes_under_impl_2 state
      <:
      Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)

let chacha20_key_block0 (key: t_ChaChaKey) (iv: t_ChaChaIV) : t_Block =
  let state:t_State = chacha20_init key iv (Secret_integers.U32 0ul) in
  chacha20_key_block state

let chacha20_encrypt_block (st0: t_State) (ctr: Secret_integers.t_U32) (plain: t_Block) : t_Block =
  let st:t_State = chacha20_core ctr st0 in
  let pl:t_State =
    from_seq_under_impl_17 (to_le_U32s_under_impl_68 plain
        <:
        Hacspec_lib.Seq.t_Seq Secret_integers.t_U32)
  in
  let st = pl ^. st in
  from_seq_under_impl_86 (to_le_bytes_under_impl_2 st <: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)

let chacha20_encrypt_last
      (st0: t_State)
      (ctr: Secret_integers.t_U32)
      (plain: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let b:t_Block = new_under_impl_73 in
  let b:t_Block = Hacspec_lib.Traits.SeqTrait.update b 0sz plain in
  let b:t_Block = chacha20_encrypt_block st0 ctr b in
  slice_under_impl_74 b 0sz (Hacspec_lib.Seq.len_under_impl_41 plain <: usize)

let chacha20_update (st0: t_State) (m: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 (Hacspec_lib.Seq.len_under_impl_41 m <: usize)
  in
  let n_blocks:usize = Hacspec_lib.Seq.num_exact_chunks_under_impl_41 m 64sz in
  let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = n_blocks
            })
        <:
        _)
      blocks_out
      (fun blocks_out i ->
          let msg_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.get_exact_chunk_under_impl_41 m 64sz i
          in
          let b:t_Block =
            chacha20_encrypt_block st0
              (Secret_integers.U32 (cast i))
              (from_seq_under_impl_86 msg_block <: t_Block)
          in
          let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.set_exact_chunk_under_impl_41 blocks_out 64sz i b
          in
          blocks_out)
  in
  let last_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.get_remainder_chunk_under_impl_41 m 64sz
  in
  let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    if (Hacspec_lib.Seq.len_under_impl_41 last_block <: usize) <>. 0sz
    then
      let b:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
        chacha20_encrypt_last st0 (Secret_integers.U32 (cast n_blocks)) last_block
      in
      let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
        Hacspec_lib.Seq.set_chunk_under_impl_41 blocks_out 64sz n_blocks b
      in
      blocks_out
    else blocks_out
  in
  blocks_out

let chacha20
      (key: t_ChaChaKey)
      (iv: t_ChaChaIV)
      (ctr: u32)
      (m: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let state:t_State = chacha20_init key iv (Secret_integers.U32 ctr) in
  chacha20_update state m