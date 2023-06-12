module Chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

let state = x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}

let block = x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}

let chaChaIV = x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 12}

let chaChaKey = x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32}

let chacha20_line
      (a b d: uint_size)
      (s: UInt32.t)
      (m: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} = m in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    state.[ a ] <-
      Core.Num.wrapping_add (Core.Ops.Index.index state a) (Core.Ops.Index.index state b)
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    state.[ d ] <- Hacspec_lib.^. (Core.Ops.Index.index state d) (Core.Ops.Index.index state a)
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    state.[ d ] <- Core.Num.rotate_left (Core.Ops.Index.index state d) s
  in
  state

let chacha20_quarter_round
      (a b c d: uint_size)
      (state: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_line a b d 16ul state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_line c d b 12ul state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_line a b d 8ul state
  in
  chacha20_line c d b 7ul state

let chacha20_double_round
      (state: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_quarter_round 0 4 8 12 state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_quarter_round 1 5 9 13 state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_quarter_round 2 6 10 14 state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_quarter_round 3 7 11 15 state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_quarter_round 0 5 10 15 state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_quarter_round 1 6 11 12 state
  in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_quarter_round 2 7 8 13 state
  in
  chacha20_quarter_round 3 4 9 14 state

let chacha20_rounds
      (state: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let st:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} = state in
  let st:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0l;
              end = 10l
            }))
      st
      (fun _i st -> chacha20_double_round st)
  in
  st

let chacha20_core
      (ctr: UInt32.t)
      (st0: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} = st0 in
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    state.[ 12 ] <- Core.Ops.Index.index state 12 + ctr
  in
  let k:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_rounds state
  in
  Chacha20.Hacspec_helper.add_state state k

let chacha20_init
      (key: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32}))
      (iv: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 12}))
      (ctr: UInt32.t)
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
  let (key_u32: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8})):x:
  Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
    Chacha20.Hacspec_helper.to_le_u32s_8 (Hacspec.Lib.unsize key)
  in
  let (iv_u32: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 3})):x:
  Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 3} =
    Chacha20.Hacspec_helper.to_le_u32s_3 (Hacspec.Lib.unsize iv)
  in
  [
    1634760805ul; 857760878ul; 2036477234ul; 1797285236ul; Core.Ops.Index.index key_u32 0;
    Core.Ops.Index.index key_u32 1; Core.Ops.Index.index key_u32 2; Core.Ops.Index.index key_u32 3;
    Core.Ops.Index.index key_u32 4; Core.Ops.Index.index key_u32 5; Core.Ops.Index.index key_u32 6;
    Core.Ops.Index.index key_u32 7; ctr; Core.Ops.Index.index iv_u32 0;
    Core.Ops.Index.index iv_u32 1; Core.Ops.Index.index iv_u32 2
  ]

let chacha20_key_block
      (state: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_core 0ul state
  in
  Chacha20.Hacspec_helper.u32s_to_le_bytes state

let chacha20_key_block0
      (key: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32}))
      (iv: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 12}))
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_init key iv 0ul
  in
  chacha20_key_block state

let chacha20_encrypt_block
      (st0: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
      (ctr: UInt32.t)
      (plain: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}))
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
  let st:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_core ctr st0
  in
  let (pl: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16})):x:
  Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    Chacha20.Hacspec_helper.to_le_u32s_16 (Hacspec.Lib.unsize plain)
  in
  let encrypted:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    Chacha20.Hacspec_helper.xor_state st pl
  in
  Chacha20.Hacspec_helper.u32s_to_le_bytes encrypted

let chacha20_encrypt_last
      (st0: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
      (ctr: UInt32.t)
      (plain: FStar.Seq.seq UInt8.t)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
  let (b: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})):Alloc.Boxed.box_t
    (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0uy 64
  in
  let b:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
    Chacha20.Hacspec_helper.update_array b plain
  in
  let b:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
    chacha20_encrypt_block st0 ctr b
  in
  Alloc.Slice.to_vec b.[ { end = Core.Slice.len plain } ]

let chacha20_update
      (st0: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16}))
      (m: FStar.Seq.seq UInt8.t)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
  let blocks_out:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t = Alloc.Vec.new_ in
  let num_blocks:uint_size = Prims.op_Division (Core.Slice.len m) 64 in
  let remainder_len:uint_size = Prims.op_Modulus (Core.Slice.len m) 64 in
  let blocks_out:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = num_blocks
            }))
      blocks_out
      (fun i blocks_out ->
          let b:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
            chacha20_encrypt_block st0
              (cast i)
              (Core.Result.unwrap (Core.Convert.TryInto.try_into m.[ {
                          start = 64 * i;
                          end = 64 * i + 64
                        } ]))
          in
          let blocks_out:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
            Alloc.Vec.extend_from_slice blocks_out (Hacspec.Lib.unsize b)
          in
          blocks_out)
  in
  let blocks_out:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    if remainder_len <> 0
    then
      let b:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
        chacha20_encrypt_last st0 (cast num_blocks) m.[ { start = 64 * num_blocks } ]
      in
      let blocks_out:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
        Alloc.Vec.extend_from_slice blocks_out (Core.Ops.Deref.Deref.deref b)
      in
      blocks_out
    else blocks_out
  in
  blocks_out

let chacha20
      (m: FStar.Seq.seq UInt8.t)
      (key: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32}))
      (iv: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 12}))
      (ctr: UInt32.t)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
  let state:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 16} =
    chacha20_init key iv ctr
  in
  chacha20_update state m