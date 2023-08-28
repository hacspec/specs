module Sha256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BLOCK_SIZE: usize = 64sz

let v_LEN_SIZE: usize = 8sz

let v_K_SIZE: usize = 64sz

let v_HASH_SIZE: usize = 256sz /. 8sz

let t_Block = t_Array u8 64sz

let t_OpTableType = t_Array u8 12sz

let t_Sha256Digest = t_Array u8 32sz

let t_RoundConstantsTable = t_Array u32 64sz

let t_Hash = t_Array u32 8sz

let ch (x y z: u32) : u32 = (x &. y <: u32) ^. ((~.x <: u32) &. z <: u32)

let maj (x y z: u32) : u32 = (x &. y <: u32) ^. ((x &. z <: u32) ^. (y &. z <: u32) <: u32)

let v_OP_TABLE: t_Array u8 12sz =
  (let l = [2uy; 13uy; 22uy; 6uy; 11uy; 25uy; 7uy; 18uy; 3uy; 17uy; 19uy; 10uy] in
    assert_norm (List.Tot.length l == 12);
    Rust_primitives.Hax.array_of_list l)

let v_K_TABLE: t_Array u32 64sz =
  (let l =
      [
        1116352408ul; 1899447441ul; 3049323471ul; 3921009573ul; 961987163ul; 1508970993ul;
        2453635748ul; 2870763221ul; 3624381080ul; 310598401ul; 607225278ul; 1426881987ul;
        1925078388ul; 2162078206ul; 2614888103ul; 3248222580ul; 3835390401ul; 4022224774ul;
        264347078ul; 604807628ul; 770255983ul; 1249150122ul; 1555081692ul; 1996064986ul;
        2554220882ul; 2821834349ul; 2952996808ul; 3210313671ul; 3336571891ul; 3584528711ul;
        113926993ul; 338241895ul; 666307205ul; 773529912ul; 1294757372ul; 1396182291ul; 1695183700ul;
        1986661051ul; 2177026350ul; 2456956037ul; 2730485921ul; 2820302411ul; 3259730800ul;
        3345764771ul; 3516065817ul; 3600352804ul; 4094571909ul; 275423344ul; 430227734ul;
        506948616ul; 659060556ul; 883997877ul; 958139571ul; 1322822218ul; 1537002063ul; 1747873779ul;
        1955562222ul; 2024104815ul; 2227730452ul; 2361852424ul; 2428436474ul; 2756734187ul;
        3204031479ul; 3329325298ul
      ]
    in
    assert_norm (List.Tot.length l == 64);
    Rust_primitives.Hax.array_of_list l)

let v_HASH_INIT: t_Array u32 8sz =
  (let l =
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
    in
    assert_norm (List.Tot.length l == 8);
    Rust_primitives.Hax.array_of_list l)

let sigma (x: u32) (i op: usize) : u32 =
  let (tmp: u32):u32 =
    Core.Num.rotate_right_under_impl_8 x
      (Core.Convert.Into.into (v_OP_TABLE.[ (3sz *. i <: usize) +. 2sz <: usize ] <: u8) <: u32)
  in
  let tmp:u32 =
    if op =. 0sz then x <<. (v_OP_TABLE.[ (3sz *. i <: usize) +. 2sz <: usize ] <: u8) else tmp
  in
  let rot_val_1_:u32 = Core.Convert.Into.into (v_OP_TABLE.[ 3sz *. i <: usize ] <: u8) in
  let rot_val_2_:u32 =
    Core.Convert.Into.into (v_OP_TABLE.[ (3sz *. i <: usize) +. 1sz <: usize ] <: u8)
  in
  ((Core.Num.rotate_right_under_impl_8 x rot_val_1_ <: u32) ^.
    (Core.Num.rotate_right_under_impl_8 x rot_val_2_ <: u32)
    <:
    u32) ^.
  tmp

let to_be_u32s (block: t_Array u8 64sz) : Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
  let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
    Alloc.Vec.with_capacity_under_impl (v_BLOCK_SIZE /. 4sz <: usize)
  in
  let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks_under_impl
              (Rust_primitives.unsize block <: slice u8)
              4sz
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        _)
      out
      (fun (out: Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global) (block_chunk: slice u8) ->
          let block_chunk_array:u32 =
            Core.Num.from_be_bytes_under_impl_8 (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into
                      block_chunk
                    <:
                    Core.Result.t_Result (t_Array u8 4sz) _)
                <:
                t_Array u8 4sz)
          in
          let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
            Alloc.Vec.push_under_impl_1 out block_chunk_array
          in
          out)
  in
  out

let schedule (block: t_Array u8 64sz) : t_Array u32 64sz =
  let b:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global = to_be_u32s block in
  let s:t_Array u32 64sz = Rust_primitives.Hax.repeat 0ul 64sz in
  let s:t_Array u32 64sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K_SIZE
            })
        <:
        _)
      s
      (fun (s: t_Array u32 64sz) (i: usize) ->
          if i <. 16sz <: bool
          then
            let s:t_Array u32 64sz = s.[ i ] <- b.[ i ] <: u32 in
            s
          else
            let t16:u32 = s.[ i -. 16sz <: usize ] in
            let t15:u32 = s.[ i -. 15sz <: usize ] in
            let t7:u32 = s.[ i -. 7sz <: usize ] in
            let t2:u32 = s.[ i -. 2sz <: usize ] in
            let s1:u32 = sigma t2 3sz 0sz in
            let s0:u32 = sigma t15 2sz 0sz in
            let s:t_Array u32 64sz =
              s.[ i ] <-
                Core.Num.wrapping_add_under_impl_8 (Core.Num.wrapping_add_under_impl_8 (Core.Num.wrapping_add_under_impl_8
                          s1
                          t7
                        <:
                        u32)
                      s0
                    <:
                    u32)
                  t16
                <:
                u32
            in
            s)
  in
  s

let shuffle (ws: t_Array u32 64sz) (hashi: t_Array u32 8sz) : t_Array u32 8sz =
  let h:t_Array u32 8sz = hashi in
  let h:t_Array u32 8sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_K_SIZE
            })
        <:
        _)
      h
      (fun (h: t_Array u32 8sz) (i: usize) ->
          let a0:u32 = h.[ 0sz ] in
          let b0:u32 = h.[ 1sz ] in
          let c0:u32 = h.[ 2sz ] in
          let d0:u32 = h.[ 3sz ] in
          let e0:u32 = h.[ 4sz ] in
          let f0:u32 = h.[ 5sz ] in
          let g0:u32 = h.[ 6sz ] in
          let (h0: u32):u32 = h.[ 7sz ] in
          let t1:u32 =
            Core.Num.wrapping_add_under_impl_8 (Core.Num.wrapping_add_under_impl_8 (Core.Num.wrapping_add_under_impl_8
                      (Core.Num.wrapping_add_under_impl_8 h0 (sigma e0 1sz 1sz <: u32) <: u32)
                      (ch e0 f0 g0 <: u32)
                    <:
                    u32)
                  (v_K_TABLE.[ i ] <: u32)
                <:
                u32)
              (ws.[ i ] <: u32)
          in
          let t2:u32 =
            Core.Num.wrapping_add_under_impl_8 (sigma a0 0sz 1sz <: u32) (maj a0 b0 c0 <: u32)
          in
          let h:t_Array u32 8sz = h.[ 0sz ] <- Core.Num.wrapping_add_under_impl_8 t1 t2 <: u32 in
          let h:t_Array u32 8sz = h.[ 1sz ] <- a0 in
          let h:t_Array u32 8sz = h.[ 2sz ] <- b0 in
          let h:t_Array u32 8sz = h.[ 3sz ] <- c0 in
          let h:t_Array u32 8sz = h.[ 4sz ] <- Core.Num.wrapping_add_under_impl_8 d0 t1 <: u32 in
          let h:t_Array u32 8sz = h.[ 5sz ] <- e0 in
          let h:t_Array u32 8sz = h.[ 6sz ] <- f0 in
          let h:t_Array u32 8sz = h.[ 7sz ] <- g0 in
          h)
  in
  h

let compress (block: t_Array u8 64sz) (h_in: t_Array u32 8sz) : t_Array u32 8sz =
  let s:t_Array u32 64sz = schedule block in
  let h:t_Array u32 8sz = shuffle s h_in in
  let h:t_Array u32 8sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 8sz
            })
        <:
        _)
      h
      (fun (h: t_Array u32 8sz) (i: usize) ->
          (h.[ i ] <- Core.Num.wrapping_add_under_impl_8 (h.[ i ] <: u32) (h_in.[ i ] <: u32) <: u32
          )
          <:
          t_Array u32 8sz)
  in
  h

let u32s_to_be_bytes (state: t_Array u32 8sz) : t_Array u8 32sz =
  let (out: t_Array u8 32sz):t_Array u8 32sz = Rust_primitives.Hax.repeat 0uy 32sz in
  let out:t_Array u8 32sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_LEN_SIZE
            })
        <:
        _)
      out
      (fun (out: t_Array u8 32sz) (i: usize) ->
          let tmp:u32 = state.[ i ] in
          let tmp:t_Array u8 4sz = Core.Num.to_be_bytes_under_impl_8 tmp in
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = 4sz
                  })
              <:
              _)
            out
            (fun (out: t_Array u8 32sz) (j: usize) ->
                (out.[ (i *. 4sz <: usize) +. j <: usize ] <- tmp.[ j ] <: u8) <: t_Array u8 32sz))
  in
  out

let hash (msg: slice u8) : t_Array u8 32sz =
  let h:t_Array u32 8sz = v_HASH_INIT in
  let (last_block: t_Array u8 64sz):t_Array u8 64sz = Rust_primitives.Hax.repeat 0uy 64sz in
  let last_block_len:usize = 0sz in
  let h, last_block, last_block_len:(t_Array u32 8sz & t_Array u8 64sz & usize) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks_under_impl
              msg
              v_BLOCK_SIZE
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        _)
      (h, last_block, last_block_len)
      (fun
          (h, last_block, last_block_len: (t_Array u32 8sz & t_Array u8 64sz & usize))
          (block: slice u8)
          ->
          if (Core.Slice.len_under_impl block <: usize) <. v_BLOCK_SIZE <: bool
          then
            let last_block:t_Array u8 64sz =
              Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                    ({
                        Core.Ops.Range.Range.f_start = 0sz;
                        Core.Ops.Range.Range.f_end = Core.Slice.len_under_impl block <: usize
                      })
                  <:
                  _)
                last_block
                (fun (last_block: t_Array u8 64sz) (i: usize) ->
                    (last_block.[ i ] <- block.[ i ] <: u8) <: t_Array u8 64sz)
            in
            let last_block_len:usize = Core.Slice.len_under_impl block in
            h, last_block, last_block_len
          else
            let h:t_Array u32 8sz =
              compress (Core.Result.unwrap_under_impl (Core.Convert.TryInto.try_into block
                      <:
                      Core.Result.t_Result (t_Array u8 64sz) _)
                  <:
                  t_Array u8 64sz)
                h
            in
            h, last_block, last_block_len)
  in
  let last_block:t_Array u8 64sz = last_block.[ last_block_len ] <- 128uy in
  let len_bist:u64 = cast ((Core.Slice.len_under_impl msg <: usize) *. 8sz) in
  let len_bist_bytes:t_Array u8 8sz = Core.Num.to_be_bytes_under_impl_9 len_bist in
  let h, last_block:(t_Array u32 8sz & t_Array u8 64sz) =
    if last_block_len <. (v_BLOCK_SIZE -. v_LEN_SIZE <: usize)
    then
      let last_block:t_Array u8 64sz =
        Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end = v_LEN_SIZE
                })
            <:
            _)
          last_block
          (fun (last_block: t_Array u8 64sz) (i: usize) ->
              (last_block.[ (v_BLOCK_SIZE -. v_LEN_SIZE <: usize) +. i <: usize ] <-
                  len_bist_bytes.[ i ] <: u8)
              <:
              t_Array u8 64sz)
      in
      let h:t_Array u32 8sz = compress last_block h in
      h, last_block
    else
      let (pad_block: t_Array u8 64sz):t_Array u8 64sz = Rust_primitives.Hax.repeat 0uy 64sz in
      let pad_block:t_Array u8 64sz =
        Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end = v_LEN_SIZE
                })
            <:
            _)
          pad_block
          (fun (pad_block: t_Array u8 64sz) (i: usize) ->
              (pad_block.[ (v_BLOCK_SIZE -. v_LEN_SIZE <: usize) +. i <: usize ] <-
                  len_bist_bytes.[ i ] <: u8)
              <:
              t_Array u8 64sz)
      in
      let h:t_Array u32 8sz = compress last_block h in
      let h:t_Array u32 8sz = compress pad_block h in
      h, last_block
  in
  u32s_to_be_bytes h

let sha256 (msg: slice u8) : t_Array u8 32sz = hash msg