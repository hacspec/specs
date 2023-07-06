module Hacspec_gimli
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_state = lseq uint32 12
unfold
type t_state_idx = nat_mod 12

let swap (s: t_State) (i j: usize) : t_State =
  let tmp:Secret_integers.t_U32 = s.[ i ] in
  let s:t_State = Rust_primitives.Hax.update_at s i s.[ j ] in
  let s:t_State = Rust_primitives.Hax.update_at s j tmp in
  s

let gimli_round (s: t_State) (r: u32) : t_State =
  let s:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = 4sz
            }))
      s
      (fun s col ->
          let x:Secret_integers.t_U32 = Secret_integers.rotate_left_under_impl_66 s.[ col ] 24sz in
          let y:Secret_integers.t_U32 =
            Secret_integers.rotate_left_under_impl_66 s.[ col +. 4sz ] 9sz
          in
          let z:Secret_integers.t_U32 = s.[ col +. 8sz ] in
          let s:t_State =
            Rust_primitives.Hax.update_at s (col +. 8sz) ((x ^. (z >>. 1sz)) ^. ((y &. z) >>. 2sz))
          in
          let s:t_State =
            Rust_primitives.Hax.update_at s (col +. 4sz) ((y ^. x) ^. ((x |. z) >>. 1sz))
          in
          let s:t_State = Rust_primitives.Hax.update_at s col ((z ^. y) ^. ((x &. y) >>. 3sz)) in
          s)
  in
  let s:t_State =
    if (r &. 3ul) =. 0ul
    then
      let s:t_State = swap s 0sz 1sz in
      let s:t_State = swap s 2sz 3sz in
      s
    else s
  in
  let s:t_State =
    if (r &. 3ul) =. 2ul
    then
      let s:t_State = swap s 0sz 2sz in
      let s:t_State = swap s 1sz 3sz in
      s
    else s
  in
  let s:t_State =
    if (r &. 3ul) =. 0ul
    then
      Rust_primitives.Hax.update_at s
        0l
        (s.[ 0l ] ^. (Secret_integers.U32 2654435584ul |. Secret_integers.U32 r))
    else s
  in
  s

let gimli (s: t_State) : t_State =
  let s:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 24l
            }))
      s
      (fun s rnd ->
          let rnd:u32 = cast (24l -. rnd) in
          let s:t_State = gimli_round s rnd in
          s)
  in
  s

unfold
type t_block = lseq uint8 16

unfold
type t_digest = lseq uint8 32

let absorb_block (input_block: t_Block) (s: t_State) : t_State =
  let input_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    to_le_U32s_under_impl_34 input_block
  in
  let s:t_State = Rust_primitives.Hax.update_at s 0l (s.[ 0l ] ^. input_bytes.[ 0l ]) in
  let s:t_State = Rust_primitives.Hax.update_at s 1l (s.[ 1l ] ^. input_bytes.[ 1l ]) in
  let s:t_State = Rust_primitives.Hax.update_at s 2l (s.[ 2l ] ^. input_bytes.[ 2l ]) in
  let s:t_State = Rust_primitives.Hax.update_at s 3l (s.[ 3l ] ^. input_bytes.[ 3l ]) in
  gimli s

let squeeze_block (s: t_State) : t_Block =
  let block:t_Block = new_under_impl_39 in
  let block:t_Block =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0l;
              Core.Ops.Range.Range.f_end = 4l
            }))
      block
      (fun block i ->
          let (s_i: Secret_integers.t_U32):Secret_integers.t_U32 = s.[ i ] in
          let s_i_bytes:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Traits.UnsignedSecretInteger.to_le_bytes s_i
          in
          let block:t_Block = Rust_primitives.Hax.update_at block (4l *. i) s_i_bytes.[ 0l ] in
          let block:t_Block =
            Rust_primitives.Hax.update_at block (4l *. i +. 1l) s_i_bytes.[ 1l ]
          in
          let block:t_Block =
            Rust_primitives.Hax.update_at block (4l *. i +. 2l) s_i_bytes.[ 2l ]
          in
          let block:t_Block =
            Rust_primitives.Hax.update_at block (4l *. i +. 3l) s_i_bytes.[ 3l ]
          in
          block)
  in
  block

let gimli_hash_state (input: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (s: t_State) : t_State =
  let rate:usize = length_under_impl_39 in
  let chunks:usize = Hacspec_lib.Seq.num_exact_chunks_under_impl_41 input rate in
  let s:t_State =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = chunks
            }))
      s
      (fun s i ->
          let input_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.get_exact_chunk_under_impl_41 input rate i
          in
          let full_block:t_Block = from_seq_under_impl_52 input_block in
          let s:t_State = absorb_block full_block s in
          s)
  in
  let input_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.get_remainder_chunk_under_impl_41 input rate
  in
  let input_block_padded:t_Block = new_under_impl_39 in
  let input_block_padded:t_Block =
    Hacspec_lib.Traits.SeqTrait.update_start input_block_padded input_block
  in
  let input_block_padded:t_Block =
    Rust_primitives.Hax.update_at input_block_padded
      (Hacspec_lib.Seq.len_under_impl_41 input_block)
      (Secret_integers.U8 1uy)
  in
  let s:t_State =
    Rust_primitives.Hax.update_at s 11l (s.[ 11l ] ^. Secret_integers.U32 16777216ul)
  in
  let s:t_State = absorb_block input_block_padded s in
  s

let gimli_hash (input_bytes: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Digest =
  let s:t_State = new_under_impl_4 in
  let s:t_State = gimli_hash_state input_bytes s in
  let output:t_Digest = new_under_impl_74 in
  let output:t_Digest = Hacspec_lib.Traits.SeqTrait.update_start output (squeeze_block s) in
  let s:t_State = gimli s in
  Hacspec_lib.Traits.SeqTrait.update output length_under_impl_39 (squeeze_block s)

unfold
type t_nonce = lseq uint8 16

unfold
type t_key = lseq uint8 32

unfold
type t_tag = lseq uint8 16

let process_ad (ad: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (s: t_State) : t_State =
  gimli_hash_state ad s

let process_msg (message: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (s: t_State)
    : (t_State & Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) =
  let ciphertext:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 (Hacspec_lib.Seq.len_under_impl_41 message)
  in
  let rate:usize = length_under_impl_39 in
  let num_chunks:usize = Hacspec_lib.Seq.num_exact_chunks_under_impl_41 message rate in
  let ciphertext, s:(Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & t_State) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = num_chunks
            }))
      (ciphertext, s)
      (fun (ciphertext, s) i ->
          let key_block:t_Block = squeeze_block s in
          let msg_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.get_exact_chunk_under_impl_41 message rate i
          in
          let msg_block:t_Block = from_seq_under_impl_52 msg_block in
          let ciphertext:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.set_exact_chunk_under_impl_41 ciphertext rate i (msg_block ^. key_block)
          in
          let s:t_State = absorb_block msg_block s in
          ciphertext, s)
  in
  let key_block:t_Block = squeeze_block s in
  let last_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.get_remainder_chunk_under_impl_41 message rate
  in
  let block_len:usize = Hacspec_lib.Seq.len_under_impl_41 last_block in
  let msg_block_padded:t_Block = new_under_impl_39 in
  let msg_block_padded:t_Block =
    Hacspec_lib.Traits.SeqTrait.update_start msg_block_padded last_block
  in
  let ciphertext:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.set_chunk_under_impl_41 ciphertext
      rate
      num_chunks
      (slice_range_under_impl_40 (msg_block_padded ^. key_block)
          ({ Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = block_len }))
  in
  let msg_block_padded:t_Block =
    Rust_primitives.Hax.update_at msg_block_padded
      block_len
      (msg_block_padded.[ block_len ] ^. Secret_integers.U8 1uy)
  in
  let s:t_State =
    Rust_primitives.Hax.update_at s 11l (s.[ 11l ] ^. Secret_integers.U32 16777216ul)
  in
  let s:t_State = absorb_block msg_block_padded s in
  s, ciphertext

let process_ct (ciphertext: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (s: t_State)
    : (t_State & Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) =
  let message:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 (Hacspec_lib.Seq.len_under_impl_41 ciphertext)
  in
  let rate:usize = length_under_impl_39 in
  let num_chunks:usize = Hacspec_lib.Seq.num_exact_chunks_under_impl_41 ciphertext rate in
  let message, s:(Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & t_State) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = num_chunks
            }))
      (message, s)
      (fun (message, s) i ->
          let key_block:t_Block = squeeze_block s in
          let ct_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.get_exact_chunk_under_impl_41 ciphertext rate i
          in
          let ct_block:t_Block = from_seq_under_impl_52 ct_block in
          let msg_block = ct_block ^. key_block in
          let message:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.set_exact_chunk_under_impl_41 message rate i (ct_block ^. key_block)
          in
          let s:t_State = absorb_block msg_block s in
          message, s)
  in
  let key_block:t_Block = squeeze_block s in
  let ct_final:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.get_remainder_chunk_under_impl_41 ciphertext rate
  in
  let block_len:usize = Hacspec_lib.Seq.len_under_impl_41 ct_final in
  let ct_block_padded:t_Block = new_under_impl_39 in
  let ct_block_padded:t_Block = Hacspec_lib.Traits.SeqTrait.update_start ct_block_padded ct_final in
  let msg_block = ct_block_padded ^. key_block in
  let message:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.set_chunk_under_impl_41 message
      rate
      num_chunks
      (slice_range_under_impl_40 msg_block
          ({ Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = block_len }))
  in
  let msg_block:t_Block =
    from_slice_range_under_impl_40 msg_block
      ({ Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = block_len })
  in
  let msg_block:t_Block =
    Rust_primitives.Hax.update_at msg_block
      block_len
      (msg_block.[ block_len ] ^. Secret_integers.U8 1uy)
  in
  let s:t_State =
    Rust_primitives.Hax.update_at s 11l (s.[ 11l ] ^. Secret_integers.U32 16777216ul)
  in
  let s:t_State = absorb_block msg_block s in
  s, message

let nonce_to_u32s (nonce: t_Nonce) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 = Hacspec_lib.Seq.new_under_impl_41 4sz in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      0l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              nonce
              ({ Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = 4sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      1l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              nonce
              ({ Core.Ops.Range.Range.f_start = 4sz; Core.Ops.Range.Range.f_end = 8sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      2l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              nonce
              ({ Core.Ops.Range.Range.f_start = 8sz; Core.Ops.Range.Range.f_end = 12sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      3l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              nonce
              ({ Core.Ops.Range.Range.f_start = 12sz; Core.Ops.Range.Range.f_end = 16sz })))
  in
  uints

let key_to_u32s (key: t_Key) : Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 = Hacspec_lib.Seq.new_under_impl_41 8sz in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      0l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = 4sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      1l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 4sz; Core.Ops.Range.Range.f_end = 8sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      2l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 8sz; Core.Ops.Range.Range.f_end = 12sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      3l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 12sz; Core.Ops.Range.Range.f_end = 16sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      4l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 16sz; Core.Ops.Range.Range.f_end = 20sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      5l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 20sz; Core.Ops.Range.Range.f_end = 24sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      6l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 24sz; Core.Ops.Range.Range.f_end = 28sz })))
  in
  let uints:Hacspec_lib.Seq.t_Seq Secret_integers.t_U32 =
    Rust_primitives.Hax.update_at uints
      7l
      (Hacspec_lib.Transmute.v_U32_from_le_bytes (Hacspec_lib.Prelude.from_slice_range_under_impl_41
              key
              ({ Core.Ops.Range.Range.f_start = 28sz; Core.Ops.Range.Range.f_end = 32sz })))
  in
  uints

let gimli_aead_encrypt
      (message ad: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (nonce: t_Nonce)
      (key: t_Key)
    : (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & t_Tag) =
  let s:t_State =
    from_seq_under_impl_17 (Hacspec_lib.Seq.concat_under_impl_41 (nonce_to_u32s nonce)
          (key_to_u32s key))
  in
  let s:t_State = gimli s in
  let s:t_State = process_ad ad s in
  let s, ciphertext:(t_State & Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) =
    process_msg message s
  in
  let tag:t_Block = squeeze_block s in
  let tag:t_Tag = from_seq_under_impl_192 tag in
  ciphertext, tag

let gimli_aead_decrypt
      (ciphertext ad: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (tag: t_Tag)
      (nonce: t_Nonce)
      (key: t_Key)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  let s:t_State =
    from_seq_under_impl_17 (Hacspec_lib.Seq.concat_under_impl_41 (nonce_to_u32s nonce)
          (key_to_u32s key))
  in
  let s:t_State = gimli s in
  let s:t_State = process_ad ad s in
  let s, message:(t_State & Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) = process_ct ciphertext s in
  let my_tag:t_Block = squeeze_block s in
  let my_tag:t_Tag = from_seq_under_impl_192 my_tag in
  let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = Hacspec_lib.Seq.new_under_impl_41 0sz in
  let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    if Hacspec_lib.Traits.Numeric.equal my_tag tag
    then
      let out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 = message in
      out
    else out
  in
  out