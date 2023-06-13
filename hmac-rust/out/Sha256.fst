module Sha256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

let bLOCK_SIZE: uint_size = 64

let lEN_SIZE: uint_size = 8

let k_SIZE: uint_size = 64

let hASH_SIZE: uint_size = Prims.op_Division 256 8

let block = x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}

let opTableType = x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 12}

let sha256Digest = x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32}

let roundConstantsTable =
  x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}

let hash = x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8}

let ch (x y z: UInt32.t) : UInt32.t =
  Hacspec_lib.^. (Hacspec_lib.&. x y) (Hacspec_lib.&. (Prims.l_Not x) z)

let maj (x y z: UInt32.t) : UInt32.t =
  Hacspec_lib.^. (Hacspec_lib.&. x y) (Hacspec_lib.^. (Hacspec_lib.&. x z) (Hacspec_lib.&. y z))

let oP_TABLE: x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 12} =
  [2uy; 13uy; 22uy; 6uy; 11uy; 25uy; 7uy; 18uy; 3uy; 17uy; 19uy; 10uy]

let k_TABLE: x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
  [
    1116352408ul; 1899447441ul; 3049323471ul; 3921009573ul; 961987163ul; 1508970993ul; 2453635748ul;
    2870763221ul; 3624381080ul; 310598401ul; 607225278ul; 1426881987ul; 1925078388ul; 2162078206ul;
    2614888103ul; 3248222580ul; 3835390401ul; 4022224774ul; 264347078ul; 604807628ul; 770255983ul;
    1249150122ul; 1555081692ul; 1996064986ul; 2554220882ul; 2821834349ul; 2952996808ul; 3210313671ul;
    3336571891ul; 3584528711ul; 113926993ul; 338241895ul; 666307205ul; 773529912ul; 1294757372ul;
    1396182291ul; 1695183700ul; 1986661051ul; 2177026350ul; 2456956037ul; 2730485921ul; 2820302411ul;
    3259730800ul; 3345764771ul; 3516065817ul; 3600352804ul; 4094571909ul; 275423344ul; 430227734ul;
    506948616ul; 659060556ul; 883997877ul; 958139571ul; 1322822218ul; 1537002063ul; 1747873779ul;
    1955562222ul; 2024104815ul; 2227730452ul; 2361852424ul; 2428436474ul; 2756734187ul; 3204031479ul;
    3329325298ul
  ]

let hASH_INIT: x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
  [
    1779033703ul;
    3144134277ul;
    1013904242ul;
    2773480762ul;
    1359893119ul;
    2600822924ul;
    528734635ul;
    1541459225ul
  ]

let sigma (x: UInt32.t) (i op: uint_size) : UInt32.t =
  let (tmp: UInt32.t):UInt32.t =
    Core.Num.rotate_right x (Core.Convert.Into.into (Core.Ops.Index.index oP_TABLE (3 * i + 2)))
  in
  let tmp:UInt32.t =
    if op = 0 then Hacspec_lib.>>. x (Core.Ops.Index.index oP_TABLE (3 * i + 2)) else tmp
  in
  let rot_val_1:UInt32.t = Core.Convert.Into.into (Core.Ops.Index.index oP_TABLE (3 * i)) in
  let rot_val_2:UInt32.t = Core.Convert.Into.into (Core.Ops.Index.index oP_TABLE (3 * i + 1)) in
  Hacspec_lib.^. (Hacspec_lib.^. (Core.Num.rotate_right x rot_val_1)
        (Core.Num.rotate_right x rot_val_2))
    tmp

let to_be_u32s
      (block: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}))
    : Alloc.Vec.vec_t UInt32.t Alloc.Alloc.global_t =
  let out:Alloc.Vec.vec_t UInt32.t Alloc.Alloc.global_t =
    Alloc.Vec.with_capacity (Prims.op_Division bLOCK_SIZE 4)
  in
  let out:Alloc.Vec.vec_t UInt32.t Alloc.Alloc.global_t =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks (Hacspec.Lib.unsize
                  block)
              4))
      out
      (fun block_chunk out ->
          let block_chunk_array:UInt32.t =
            Core.Num.from_be_bytes (Core.Result.unwrap (Core.Convert.TryInto.try_into block_chunk))
          in
          let out:Alloc.Vec.vec_t UInt32.t Alloc.Alloc.global_t =
            Alloc.Vec.push out block_chunk_array
          in
          out)
  in
  out

let schedule (block: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
  let b:Alloc.Vec.vec_t UInt32.t Alloc.Alloc.global_t = to_be_u32s block in
  let s:Alloc.Boxed.box_t
    (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0ul 64
  in
  let s:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = k_SIZE
            }))
      s
      (fun i s ->
          if Prims.op_LessThan i 16
          then
            let s:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
              s.[ i ] <- b.[ i ]
            in
            s
          else
            let t16:UInt32.t = Core.Ops.Index.index s (i - 16) in
            let t15:UInt32.t = Core.Ops.Index.index s (i - 15) in
            let t7:UInt32.t = Core.Ops.Index.index s (i - 7) in
            let t2:UInt32.t = Core.Ops.Index.index s (i - 2) in
            let s1:UInt32.t = sigma t2 3 0 in
            let s0:UInt32.t = sigma t15 2 0 in
            let s:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
              s.[ i ] <-
                Core.Num.wrapping_add (Core.Num.wrapping_add (Core.Num.wrapping_add s1 t7) s0) t16
            in
            s)
  in
  s

let shuffle
      (ws: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}))
      (hashi: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
  let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} = hashi in
  let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = k_SIZE
            }))
      h
      (fun i h ->
          let a0:UInt32.t = Core.Ops.Index.index h 0 in
          let b0:UInt32.t = Core.Ops.Index.index h 1 in
          let c0:UInt32.t = Core.Ops.Index.index h 2 in
          let d0:UInt32.t = Core.Ops.Index.index h 3 in
          let e0:UInt32.t = Core.Ops.Index.index h 4 in
          let f0:UInt32.t = Core.Ops.Index.index h 5 in
          let g0:UInt32.t = Core.Ops.Index.index h 6 in
          let (h0: UInt32.t):UInt32.t = Core.Ops.Index.index h 7 in
          let t1:UInt32.t =
            Core.Num.wrapping_add (Core.Num.wrapping_add (Core.Num.wrapping_add (Core.Num.wrapping_add
                          h0
                          (sigma e0 1 1))
                      (ch e0 f0 g0))
                  (Core.Ops.Index.index k_TABLE i))
              (Core.Ops.Index.index ws i)
          in
          let t2:UInt32.t = Core.Num.wrapping_add (sigma a0 0 1) (maj a0 b0 c0) in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 0 ] <- Core.Num.wrapping_add t1 t2
          in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 1 ] <- a0
          in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 2 ] <- b0
          in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 3 ] <- c0
          in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 4 ] <- Core.Num.wrapping_add d0 t1
          in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 5 ] <- e0
          in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 6 ] <- f0
          in
          let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
            h.[ 7 ] <- g0
          in
          h)
  in
  h

let compress
      (block: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}))
      (h_in: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8}))
    : x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
  let s:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
    schedule block
  in
  let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
    shuffle s h_in
  in
  let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({ start = 0; end = 8 }
          ))
      h
      (fun i h ->
          h.[ i ] <- Core.Num.wrapping_add (Core.Ops.Index.index h i) (Core.Ops.Index.index h_in i))
  in
  h

let u32s_to_be_bytes
      (state: (x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8}))
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32} =
  let (out: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32})):Alloc.Boxed.box_t
    (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0uy 32
  in
  let out:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32} =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = lEN_SIZE
            }))
      out
      (fun i out ->
          let tmp:UInt32.t = Core.Ops.Index.index state i in
          let tmp:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 4} =
            Core.Num.to_be_bytes tmp
          in
          Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    start = 0;
                    end = 4
                  }))
            out
            (fun j out -> out.[ i * 4 + j ] <- Core.Ops.Index.index tmp j))
  in
  out

let hash (msg: FStar.Seq.seq UInt8.t)
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32} =
  let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} = hASH_INIT in
  let (last_block: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})):Alloc.Boxed.box_t
    (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})
    Alloc.Alloc.global_t =
    Hacspec.Lib.repeat 0uy 64
  in
  let last_block_len:uint_size = 0 in
  let h, last_block, last_block_len:(x:
    Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} &
    x:
    Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} &
    uint_size) =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks msg
              bLOCK_SIZE))
      (h, last_block, last_block_len)
      (fun block (h, last_block, last_block_len) ->
          if Prims.op_LessThan (Core.Slice.len block) bLOCK_SIZE
          then
            let last_block:x:
            Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
              Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                        start = 0;
                        end = Core.Slice.len block
                      }))
                last_block
                (fun i last_block -> last_block.[ i ] <- Core.Ops.Index.index block i)
            in
            let last_block_len:uint_size = Core.Slice.len block in
            h, last_block, last_block_len
          else
            let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
              compress (Core.Result.unwrap (Core.Convert.TryInto.try_into block)) h
            in
            h, last_block, last_block_len)
  in
  let last_block:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
    last_block.[ last_block_len ] <- 128uy
  in
  let len_bist:UInt64.t = cast (Core.Slice.len msg * 8) in
  let len_bist_bytes:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
    Core.Num.to_be_bytes len_bist
  in
  let h, last_block:(x:
    Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} &
    x:
    Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64}) =
    if Prims.op_LessThan last_block_len (bLOCK_SIZE - lEN_SIZE)
    then
      let last_block:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
        Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                  start = 0;
                  end = lEN_SIZE
                }))
          last_block
          (fun i last_block ->
              last_block.[ bLOCK_SIZE - lEN_SIZE + i ] <- Core.Ops.Index.index len_bist_bytes i)
      in
      let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
        compress last_block h
      in
      h, last_block
    else
      let (pad_block: (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})):Alloc.Boxed.box_t
        (x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64})
        Alloc.Alloc.global_t =
        Hacspec.Lib.repeat 0uy 64
      in
      let pad_block:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 64} =
        Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                  start = 0;
                  end = lEN_SIZE
                }))
          pad_block
          (fun i pad_block ->
              pad_block.[ bLOCK_SIZE - lEN_SIZE + i ] <- Core.Ops.Index.index len_bist_bytes i)
      in
      let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
        compress last_block h
      in
      let h:x: Prims.list UInt32.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 8} =
        compress pad_block h
      in
      h, last_block
  in
  u32s_to_be_bytes h

let sha256 (msg: FStar.Seq.seq UInt8.t)
    : x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32} = hash msg