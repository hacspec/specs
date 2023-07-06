module Hacspec_sha3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_ROUNDS: usize = 24sz

let v_SHA3224_RATE: usize = 144sz

let v_SHA3256_RATE: usize = 136sz

let v_SHA3384_RATE: usize = 104sz

let v_SHA3512_RATE: usize = 72sz

let v_SHAKE128_RATE: usize = 168sz

let v_SHAKE256_RATE: usize = 136sz

unfold
type t_state = lseq uint_size 25

unfold
type t_row = lseq uint_size 5

unfold
type t_digest224 = lseq uint8 28

unfold
type t_digest256 = lseq uint8 32

unfold
type t_digest384 = lseq uint8 48

unfold
type t_digest512 = lseq uint8 64

unfold
type t_roundconstants = lseq uint_size ROUNDS

unfold
type t_rotationconstants = lseq uint_size 25

let v_ROUNDCONSTANTS: t_RoundConstants =
  RoundConstants
  (let l =
      [
        1uL; 32898uL; 9223372036854808714uL; 9223372039002292224uL; 32907uL; 2147483649uL;
        9223372039002292353uL; 9223372036854808585uL; 138uL; 136uL; 2147516425uL; 2147483658uL;
        2147516555uL; 9223372036854775947uL; 9223372036854808713uL; 9223372036854808579uL;
        9223372036854808578uL; 9223372036854775936uL; 32778uL; 9223372039002259466uL;
        9223372039002292353uL; 9223372036854808704uL; 2147483649uL; 9223372039002292232uL
      ]
    in
    assert_norm (List.Tot.length l == 24);
    Rust_primitives.Hax.array_of_list l)

let v_ROTC: t_RotationConstants =
  RotationConstants
  (let l =
      [
        0sz; 1sz; 62sz; 28sz; 27sz; 36sz; 44sz; 6sz; 55sz; 20sz; 3sz; 10sz; 43sz; 25sz; 39sz; 41sz;
        45sz; 15sz; 21sz; 8sz; 18sz; 2sz; 61sz; 56sz; 14sz
      ]
    in
    assert_norm (List.Tot.length l == 25);
    Rust_primitives.Hax.array_of_list l)

let v_PI: t_RotationConstants =
  RotationConstants
  (let l =
      [
        0sz; 6sz; 12sz; 18sz; 24sz; 3sz; 9sz; 10sz; 16sz; 22sz; 1sz; 7sz; 13sz; 19sz; 20sz; 4sz; 5sz;
        11sz; 17sz; 23sz; 2sz; 8sz; 14sz; 15sz; 21sz
      ]
    in
    assert_norm (List.Tot.length l == 25);
    Rust_primitives.Hax.array_of_list l)

let theta (s: t_State) : t_State =
  let b:t_Row = new_under_impl_38 in
  let b:t_Row =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 5l
            }))
      b
      (fun b i ->
          Rust_primitives.Hax.update_at b
            i
            ((((s.[ i ] ^. s.[ i +. 5l ]) ^. s.[ i +. 10l ]) ^. s.[ i +. 15l ]) ^. s.[ i +. 20l ]))
  in
  let s:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 5l
            }))
      s
      (fun s i ->
          let (u: Secret_integers.t_U64):Secret_integers.t_U64 = b.[ (i +. 1l) %. 5l ] in
          let t = b.[ (i +. 4l) %. 5l ] ^. Secret_integers.rotate_left_under_impl_97 u 1sz in
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0l;
                    Core.Ops.Range.Range.f_end = 5l
                  }))
            s
            (fun s j -> Rust_primitives.Hax.update_at s (5l *. j +. i) (s.[ 5l *. j +. i ] ^. t)))
  in
  s

let rho (s: t_State) : t_State =
  let s:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 25l
            }))
      s
      (fun s i ->
          let (u: Secret_integers.t_U64):Secret_integers.t_U64 = s.[ i ] in
          let s:t_State =
            Rust_primitives.Hax.update_at s
              i
              (Secret_integers.rotate_left_under_impl_97 u v_ROTC.[ i ])
          in
          s)
  in
  s

let pi (s: t_State) : t_State =
  let v:t_State = new_under_impl_4 in
  let v:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 25l
            }))
      v
      (fun v i -> Rust_primitives.Hax.update_at v i s.[ v_PI.[ i ] ])
  in
  v

let chi (s: t_State) : t_State =
  let b:t_Row = new_under_impl_38 in
  let b, s:(t_Row & t_State) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 5l
            }))
      (b, s)
      (fun (b, s) i ->
          let b:t_Row =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = 0l; Core.Ops.Range.Range.f_end = 5l }))
              b
              (fun b j -> Rust_primitives.Hax.update_at b j s.[ 5l *. i +. j ])
          in
          let s:t_State =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({ Core.Ops.Range.Range.f_start = 0l; Core.Ops.Range.Range.f_end = 5l }))
              s
              (fun s j ->
                  let (u: Secret_integers.t_U64):Secret_integers.t_U64 = b.[ (j +. 1l) %. 5l ] in
                  let s:t_State =
                    Rust_primitives.Hax.update_at s
                      (5l *. i +. j)
                      (s.[ 5l *. i +. j ] ^. (~.u &. b.[ (j +. 2l) %. 5l ]))
                  in
                  s)
          in
          b, s)
  in
  s

let iota (s: t_State) (rndconst: u64) : t_State =
  let s:t_State =
    Rust_primitives.Hax.update_at s 0l (s.[ 0l ] ^. Secret_integers.classify_under_impl_95 rndconst)
  in
  s

let keccakf1600 (s: t_State) : t_State =
  let s:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_ROUNDS
            }))
      s
      (fun s i ->
          let s:t_State = theta s in
          let s:t_State = rho s in
          let s:t_State = pi s in
          let s:t_State = chi s in
          let s:t_State = iota s v_ROUNDCONSTANTS.[ i ] in
          s)
  in
  s

let absorb_block (s: t_State) (block: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_State =
  let s:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.len_under_impl_41 block
            }))
      s
      (fun s i ->
          let w:usize = i <<. 3ul in
          let o:usize = 8sz *. (i &. 7sz) in
          let s:t_State =
            Rust_primitives.Hax.update_at s
              w
              (s.[ w ] ^. (Secret_integers.v_U64_from_U8 block.[ i ] >>. o))
          in
          s)
  in
  keccakf1600 s

let squeeze (s: t_State) (nbytes rate: usize) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = Hacspec_lib.Seq.new_under_impl_41 nbytes in
  let out, s:(Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & t_State) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = nbytes
            }))
      (out, s)
      (fun (out, s) i ->
          let pos:usize = i %. rate in
          let w:usize = pos <<. 3ul in
          let o:usize = 8sz *. (pos &. 7sz) in
          let b = s.[ w ] <<. o &. Secret_integers.classify_under_impl_95 255uL in
          let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Rust_primitives.Hax.update_at out i (Secret_integers.v_U8_from_U64 b)
          in
          if (i +. 1sz) %. rate =. 0sz
          then
            let s:t_State = keccakf1600 s in
            out, s
          else out, s)
  in
  out

let keccak
      (rate: usize)
      (data: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (p: u8)
      (outbytes: usize)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let buf:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = Hacspec_lib.Seq.new_under_impl_41 rate in
  let last_block_len:usize = 0sz in
  let s:t_State = new_under_impl_4 in
  let buf, last_block_len, s:(Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & usize & t_State) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.num_chunks_under_impl_41 data rate
            }))
      (buf, last_block_len, s)
      (fun (buf, last_block_len, s) i ->
          let block_len, block:(usize & Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) =
            Hacspec_lib.Seq.get_chunk_under_impl_41 data rate i
          in
          if block_len =. rate
          then
            let s:t_State = absorb_block s block in
            buf, last_block_len, s
          else
            let buf:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
              Hacspec_lib.Traits.SeqTrait.update_start buf block
            in
            let last_block_len:usize = block_len in
            buf, last_block_len, s)
  in
  let buf:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Rust_primitives.Hax.update_at buf last_block_len (Secret_integers.U8 p)
  in
  let buf:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Rust_primitives.Hax.update_at buf
      (rate -. 1sz)
      (buf.[ rate -. 1sz ] |. Secret_integers.U8 128uy)
  in
  let s:t_State = absorb_block s buf in
  squeeze s outbytes rate

let sha3224 (data: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Digest224 =
  let t:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = keccak v_SHA3224_RATE data 6uy 28sz in
  from_seq_under_impl_86 t

let sha3256 (data: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Digest256 =
  let t:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = keccak v_SHA3256_RATE data 6uy 32sz in
  from_seq_under_impl_121 t

let sha3384 (data: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Digest384 =
  let t:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = keccak v_SHA3384_RATE data 6uy 48sz in
  from_seq_under_impl_156 t

let sha3512 (data: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Digest512 =
  let t:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = keccak v_SHA3512_RATE data 6uy 64sz in
  from_seq_under_impl_191 t

let shake128 (data: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (outlen: usize)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = keccak v_SHAKE128_RATE data 31uy outlen

let shake256 (data: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (outlen: usize)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = keccak v_SHAKE256_RATE data 31uy outlen