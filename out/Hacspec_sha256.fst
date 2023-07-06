module Hacspec_sha256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BLOCK_SIZE: usize = 64sz

let v_LEN_SIZE: usize = 8sz

let v_K_SIZE: usize = 64sz

let v_HASH_SIZE: usize = 256sz /. 8sz

unfold
type t_block = lseq uint8 BLOCK_SIZE

unfold
type t_optabletype = lseq uint_size 12

unfold
type t_sha256digest = lseq uint8 HASH_SIZE

unfold
type t_roundconstantstable = lseq uint32 K_SIZE

unfold
type t_hash = lseq uint32 8

let ch (x y z: Secret_integers.t_U32) : _ = (x &. y) ^. (~.x &. z)

let maj (x y z: Secret_integers.t_U32) : _ = (x &. y) ^. (x &. z) ^. (y &. z)

let v_OP_TABLE: t_OpTableType =
  OpTableType
  (let l = [2sz; 13sz; 22sz; 6sz; 11sz; 25sz; 7sz; 18sz; 3sz; 17sz; 19sz; 10sz] in
    assert_norm (List.Tot.length l == 12);
    Rust_primitives.Hax.array_of_list l)

let v_K_TABLE: t_RoundConstantsTable =
  RoundConstantsTable
  (let l =
      [
        Secret_integers.U32 1116352408ul; Secret_integers.U32 1899447441ul;
        Secret_integers.U32 3049323471ul; Secret_integers.U32 3921009573ul;
        Secret_integers.U32 961987163ul; Secret_integers.U32 1508970993ul;
        Secret_integers.U32 2453635748ul; Secret_integers.U32 2870763221ul;
        Secret_integers.U32 3624381080ul; Secret_integers.U32 310598401ul;
        Secret_integers.U32 607225278ul; Secret_integers.U32 1426881987ul;
        Secret_integers.U32 1925078388ul; Secret_integers.U32 2162078206ul;
        Secret_integers.U32 2614888103ul; Secret_integers.U32 3248222580ul;
        Secret_integers.U32 3835390401ul; Secret_integers.U32 4022224774ul;
        Secret_integers.U32 264347078ul; Secret_integers.U32 604807628ul;
        Secret_integers.U32 770255983ul; Secret_integers.U32 1249150122ul;
        Secret_integers.U32 1555081692ul; Secret_integers.U32 1996064986ul;
        Secret_integers.U32 2554220882ul; Secret_integers.U32 2821834349ul;
        Secret_integers.U32 2952996808ul; Secret_integers.U32 3210313671ul;
        Secret_integers.U32 3336571891ul; Secret_integers.U32 3584528711ul;
        Secret_integers.U32 113926993ul; Secret_integers.U32 338241895ul;
        Secret_integers.U32 666307205ul; Secret_integers.U32 773529912ul;
        Secret_integers.U32 1294757372ul; Secret_integers.U32 1396182291ul;
        Secret_integers.U32 1695183700ul; Secret_integers.U32 1986661051ul;
        Secret_integers.U32 2177026350ul; Secret_integers.U32 2456956037ul;
        Secret_integers.U32 2730485921ul; Secret_integers.U32 2820302411ul;
        Secret_integers.U32 3259730800ul; Secret_integers.U32 3345764771ul;
        Secret_integers.U32 3516065817ul; Secret_integers.U32 3600352804ul;
        Secret_integers.U32 4094571909ul; Secret_integers.U32 275423344ul;
        Secret_integers.U32 430227734ul; Secret_integers.U32 506948616ul;
        Secret_integers.U32 659060556ul; Secret_integers.U32 883997877ul;
        Secret_integers.U32 958139571ul; Secret_integers.U32 1322822218ul;
        Secret_integers.U32 1537002063ul; Secret_integers.U32 1747873779ul;
        Secret_integers.U32 1955562222ul; Secret_integers.U32 2024104815ul;
        Secret_integers.U32 2227730452ul; Secret_integers.U32 2361852424ul;
        Secret_integers.U32 2428436474ul; Secret_integers.U32 2756734187ul;
        Secret_integers.U32 3204031479ul; Secret_integers.U32 3329325298ul
      ]
    in
    assert_norm (List.Tot.length l == 64);
    Rust_primitives.Hax.array_of_list l)

let v_HASH_INIT: t_Hash =
  Hash
  (let l =
      [
        Secret_integers.U32 1779033703ul;
        Secret_integers.U32 3144134277ul;
        Secret_integers.U32 1013904242ul;
        Secret_integers.U32 2773480762ul;
        Secret_integers.U32 1359893119ul;
        Secret_integers.U32 2600822924ul;
        Secret_integers.U32 528734635ul;
        Secret_integers.U32 1541459225ul
      ]
    in
    assert_norm (List.Tot.length l == 8);
    Rust_primitives.Hax.array_of_list l)

let sigma (x: Secret_integers.t_U32) (i op: usize) : _ =
  let (tmp: Secret_integers.t_U32):Secret_integers.t_U32 =
    Secret_integers.rotate_right_under_impl_66 x v_OP_TABLE.[ 3sz *. i +. 2sz ]
  in
  let tmp = if op =. 0sz then x <<. v_OP_TABLE.[ 3sz *. i +. 2sz ] else tmp in
  (Secret_integers.rotate_right_under_impl_66 x v_OP_TABLE.[ 3sz *. i ] ^.
  Secret_integers.rotate_right_under_impl_66 x v_OP_TABLE.[ 3sz *. i +. 1sz ]) ^.
  tmp

let schedule (block: t_Block) : t_RoundConstantsTable =
  let b:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 = to_be_U32s_under_impl block in
  let s:t_RoundConstantsTable = new_under_impl_94 in
  let s:t_RoundConstantsTable =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K_SIZE
            }))
      s
      (fun s i ->
          if i <. 16sz
          then
            let s:t_RoundConstantsTable = Rust_primitives.Hax.update_at s i b.[ i ] in
            s
          else
            let t16:Secret_integers.t_U32 = s.[ i -. 16sz ] in
            let t15:Secret_integers.t_U32 = s.[ i -. 15sz ] in
            let t7:Secret_integers.t_U32 = s.[ i -. 7sz ] in
            let t2:Secret_integers.t_U32 = s.[ i -. 2sz ] in
            let s1:Secret_integers.t_U32 = sigma t2 3sz 0sz in
            let s0:Secret_integers.t_U32 = sigma t15 2sz 0sz in
            let s:t_RoundConstantsTable =
              Rust_primitives.Hax.update_at s i (s1 +. t7 +. s0 +. t16)
            in
            s)
  in
  s

let shuffle (ws: t_RoundConstantsTable) (hashi: t_Hash) : t_Hash =
  let h:t_Hash = hashi in
  let h:t_Hash =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K_SIZE
            }))
      h
      (fun h i ->
          let a0:Secret_integers.t_U32 = h.[ 0l ] in
          let b0:Secret_integers.t_U32 = h.[ 1l ] in
          let c0:Secret_integers.t_U32 = h.[ 2l ] in
          let d0:Secret_integers.t_U32 = h.[ 3l ] in
          let e0:Secret_integers.t_U32 = h.[ 4l ] in
          let f0:Secret_integers.t_U32 = h.[ 5l ] in
          let g0:Secret_integers.t_U32 = h.[ 6l ] in
          let (h0: Secret_integers.t_U32):Secret_integers.t_U32 = h.[ 7l ] in
          let t1 = h0 +. sigma e0 1sz 1sz +. ch e0 f0 g0 +. v_K_TABLE.[ i ] +. ws.[ i ] in
          let t2 = sigma a0 0sz 1sz +. maj a0 b0 c0 in
          let h:t_Hash = Rust_primitives.Hax.update_at h 0l (t1 +. t2) in
          let h:t_Hash = Rust_primitives.Hax.update_at h 1l a0 in
          let h:t_Hash = Rust_primitives.Hax.update_at h 2l b0 in
          let h:t_Hash = Rust_primitives.Hax.update_at h 3l c0 in
          let h:t_Hash = Rust_primitives.Hax.update_at h 4l (d0 +. t1) in
          let h:t_Hash = Rust_primitives.Hax.update_at h 5l e0 in
          let h:t_Hash = Rust_primitives.Hax.update_at h 6l f0 in
          let h:t_Hash = Rust_primitives.Hax.update_at h 7l g0 in
          h)
  in
  h

let compress (block: t_Block) (h_in: t_Hash) : t_Hash =
  let s:t_RoundConstantsTable = schedule block in
  let h:t_Hash = shuffle s h_in in
  let h:t_Hash =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 8l
            }))
      h
      (fun h i -> Rust_primitives.Hax.update_at h i (h.[ i ] +. h_in.[ i ]))
  in
  h

let hash (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Sha256Digest =
  let h:t_Hash = v_HASH_INIT in
  let last_block:t_Block = new_under_impl_5 in
  let last_block_len:usize = 0sz in
  let h, last_block, last_block_len:(t_Hash & t_Block & usize) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.num_chunks_under_impl_41 msg v_BLOCK_SIZE
            }))
      (h, last_block, last_block_len)
      (fun (h, last_block, last_block_len) i ->
          let block_len, block:(usize & Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) =
            Hacspec_lib.Seq.get_chunk_under_impl_41 msg v_BLOCK_SIZE i
          in
          if block_len <. v_BLOCK_SIZE
          then
            let last_block:t_Block =
              Hacspec_lib.Traits.SeqTrait.update_start new_under_impl_5 block
            in
            let last_block_len:usize = block_len in
            h, last_block, last_block_len
          else
            let compress_input:t_Block = from_seq_under_impl_18 block in
            let h:t_Hash = compress compress_input h in
            h, last_block, last_block_len)
  in
  let last_block:t_Block =
    Rust_primitives.Hax.update_at last_block last_block_len (Secret_integers.U8 128uy)
  in
  let len_bist:Secret_integers.t_U64 =
    Secret_integers.U64 (cast (Hacspec_lib.Seq.len_under_impl_41 msg *. 8sz))
  in
  let h, last_block:(t_Hash & t_Block) =
    if last_block_len <. v_BLOCK_SIZE -. v_LEN_SIZE
    then
      let last_block:t_Block =
        Hacspec_lib.Traits.SeqTrait.update last_block
          (v_BLOCK_SIZE -. v_LEN_SIZE)
          (Hacspec_lib.Transmute.v_U64_to_be_bytes len_bist)
      in
      let h:t_Hash = compress last_block h in
      h, last_block
    else
      let pad_block:t_Block = new_under_impl_5 in
      let pad_block:t_Block =
        Hacspec_lib.Traits.SeqTrait.update pad_block
          (v_BLOCK_SIZE -. v_LEN_SIZE)
          (Hacspec_lib.Transmute.v_U64_to_be_bytes len_bist)
      in
      let h:t_Hash = compress last_block h in
      let h:t_Hash = compress pad_block h in
      h, last_block
  in
  from_seq_under_impl_73 (to_be_bytes_under_impl_126 h)

let sha256 (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Sha256Digest = hash msg