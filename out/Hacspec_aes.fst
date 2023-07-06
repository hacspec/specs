module Hacspec_aes
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BLOCKSIZE: usize = 16sz

let v_IVSIZE: usize = 12sz

let v_KEY_LENGTH: usize = 4sz

let v_ROUNDS: usize = 10sz

let v_KEY_SCHEDULE_LENGTH: usize = 176sz

let v_ITERATIONS: usize = 40sz

let v_INVALID_KEY_EXPANSION_INDEX: u8 = 1uy

unfold
type t_block = lseq uint8 BLOCKSIZE

unfold
type t_word = lseq uint8 KEY_LENGTH

unfold
type t_roundkey = lseq uint8 BLOCKSIZE

unfold
type t_aesnonce = lseq uint8 IVSIZE

unfold
type t_sbox = lseq uint8 256

unfold
type t_rcon = lseq uint8 15

unfold
type t_bytes144 = lseq uint8 144

unfold
type t_bytes176 = lseq uint8 KEY_SCHEDULE_LENGTH

unfold
type t_key128 = lseq uint8 BLOCKSIZE

let t_ByteSeqResult = Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8

let t_BlockResult = Core.Result.t_Result t_Block u8

let t_WordResult = Core.Result.t_Result t_Word u8

let v_SBOX: t_SBox =
  SBox
  (let l =
      [
        Secret_integers.U8 99uy; Secret_integers.U8 124uy; Secret_integers.U8 119uy;
        Secret_integers.U8 123uy; Secret_integers.U8 242uy; Secret_integers.U8 107uy;
        Secret_integers.U8 111uy; Secret_integers.U8 197uy; Secret_integers.U8 48uy;
        Secret_integers.U8 1uy; Secret_integers.U8 103uy; Secret_integers.U8 43uy;
        Secret_integers.U8 254uy; Secret_integers.U8 215uy; Secret_integers.U8 171uy;
        Secret_integers.U8 118uy; Secret_integers.U8 202uy; Secret_integers.U8 130uy;
        Secret_integers.U8 201uy; Secret_integers.U8 125uy; Secret_integers.U8 250uy;
        Secret_integers.U8 89uy; Secret_integers.U8 71uy; Secret_integers.U8 240uy;
        Secret_integers.U8 173uy; Secret_integers.U8 212uy; Secret_integers.U8 162uy;
        Secret_integers.U8 175uy; Secret_integers.U8 156uy; Secret_integers.U8 164uy;
        Secret_integers.U8 114uy; Secret_integers.U8 192uy; Secret_integers.U8 183uy;
        Secret_integers.U8 253uy; Secret_integers.U8 147uy; Secret_integers.U8 38uy;
        Secret_integers.U8 54uy; Secret_integers.U8 63uy; Secret_integers.U8 247uy;
        Secret_integers.U8 204uy; Secret_integers.U8 52uy; Secret_integers.U8 165uy;
        Secret_integers.U8 229uy; Secret_integers.U8 241uy; Secret_integers.U8 113uy;
        Secret_integers.U8 216uy; Secret_integers.U8 49uy; Secret_integers.U8 21uy;
        Secret_integers.U8 4uy; Secret_integers.U8 199uy; Secret_integers.U8 35uy;
        Secret_integers.U8 195uy; Secret_integers.U8 24uy; Secret_integers.U8 150uy;
        Secret_integers.U8 5uy; Secret_integers.U8 154uy; Secret_integers.U8 7uy;
        Secret_integers.U8 18uy; Secret_integers.U8 128uy; Secret_integers.U8 226uy;
        Secret_integers.U8 235uy; Secret_integers.U8 39uy; Secret_integers.U8 178uy;
        Secret_integers.U8 117uy; Secret_integers.U8 9uy; Secret_integers.U8 131uy;
        Secret_integers.U8 44uy; Secret_integers.U8 26uy; Secret_integers.U8 27uy;
        Secret_integers.U8 110uy; Secret_integers.U8 90uy; Secret_integers.U8 160uy;
        Secret_integers.U8 82uy; Secret_integers.U8 59uy; Secret_integers.U8 214uy;
        Secret_integers.U8 179uy; Secret_integers.U8 41uy; Secret_integers.U8 227uy;
        Secret_integers.U8 47uy; Secret_integers.U8 132uy; Secret_integers.U8 83uy;
        Secret_integers.U8 209uy; Secret_integers.U8 0uy; Secret_integers.U8 237uy;
        Secret_integers.U8 32uy; Secret_integers.U8 252uy; Secret_integers.U8 177uy;
        Secret_integers.U8 91uy; Secret_integers.U8 106uy; Secret_integers.U8 203uy;
        Secret_integers.U8 190uy; Secret_integers.U8 57uy; Secret_integers.U8 74uy;
        Secret_integers.U8 76uy; Secret_integers.U8 88uy; Secret_integers.U8 207uy;
        Secret_integers.U8 208uy; Secret_integers.U8 239uy; Secret_integers.U8 170uy;
        Secret_integers.U8 251uy; Secret_integers.U8 67uy; Secret_integers.U8 77uy;
        Secret_integers.U8 51uy; Secret_integers.U8 133uy; Secret_integers.U8 69uy;
        Secret_integers.U8 249uy; Secret_integers.U8 2uy; Secret_integers.U8 127uy;
        Secret_integers.U8 80uy; Secret_integers.U8 60uy; Secret_integers.U8 159uy;
        Secret_integers.U8 168uy; Secret_integers.U8 81uy; Secret_integers.U8 163uy;
        Secret_integers.U8 64uy; Secret_integers.U8 143uy; Secret_integers.U8 146uy;
        Secret_integers.U8 157uy; Secret_integers.U8 56uy; Secret_integers.U8 245uy;
        Secret_integers.U8 188uy; Secret_integers.U8 182uy; Secret_integers.U8 218uy;
        Secret_integers.U8 33uy; Secret_integers.U8 16uy; Secret_integers.U8 255uy;
        Secret_integers.U8 243uy; Secret_integers.U8 210uy; Secret_integers.U8 205uy;
        Secret_integers.U8 12uy; Secret_integers.U8 19uy; Secret_integers.U8 236uy;
        Secret_integers.U8 95uy; Secret_integers.U8 151uy; Secret_integers.U8 68uy;
        Secret_integers.U8 23uy; Secret_integers.U8 196uy; Secret_integers.U8 167uy;
        Secret_integers.U8 126uy; Secret_integers.U8 61uy; Secret_integers.U8 100uy;
        Secret_integers.U8 93uy; Secret_integers.U8 25uy; Secret_integers.U8 115uy;
        Secret_integers.U8 96uy; Secret_integers.U8 129uy; Secret_integers.U8 79uy;
        Secret_integers.U8 220uy; Secret_integers.U8 34uy; Secret_integers.U8 42uy;
        Secret_integers.U8 144uy; Secret_integers.U8 136uy; Secret_integers.U8 70uy;
        Secret_integers.U8 238uy; Secret_integers.U8 184uy; Secret_integers.U8 20uy;
        Secret_integers.U8 222uy; Secret_integers.U8 94uy; Secret_integers.U8 11uy;
        Secret_integers.U8 219uy; Secret_integers.U8 224uy; Secret_integers.U8 50uy;
        Secret_integers.U8 58uy; Secret_integers.U8 10uy; Secret_integers.U8 73uy;
        Secret_integers.U8 6uy; Secret_integers.U8 36uy; Secret_integers.U8 92uy;
        Secret_integers.U8 194uy; Secret_integers.U8 211uy; Secret_integers.U8 172uy;
        Secret_integers.U8 98uy; Secret_integers.U8 145uy; Secret_integers.U8 149uy;
        Secret_integers.U8 228uy; Secret_integers.U8 121uy; Secret_integers.U8 231uy;
        Secret_integers.U8 200uy; Secret_integers.U8 55uy; Secret_integers.U8 109uy;
        Secret_integers.U8 141uy; Secret_integers.U8 213uy; Secret_integers.U8 78uy;
        Secret_integers.U8 169uy; Secret_integers.U8 108uy; Secret_integers.U8 86uy;
        Secret_integers.U8 244uy; Secret_integers.U8 234uy; Secret_integers.U8 101uy;
        Secret_integers.U8 122uy; Secret_integers.U8 174uy; Secret_integers.U8 8uy;
        Secret_integers.U8 186uy; Secret_integers.U8 120uy; Secret_integers.U8 37uy;
        Secret_integers.U8 46uy; Secret_integers.U8 28uy; Secret_integers.U8 166uy;
        Secret_integers.U8 180uy; Secret_integers.U8 198uy; Secret_integers.U8 232uy;
        Secret_integers.U8 221uy; Secret_integers.U8 116uy; Secret_integers.U8 31uy;
        Secret_integers.U8 75uy; Secret_integers.U8 189uy; Secret_integers.U8 139uy;
        Secret_integers.U8 138uy; Secret_integers.U8 112uy; Secret_integers.U8 62uy;
        Secret_integers.U8 181uy; Secret_integers.U8 102uy; Secret_integers.U8 72uy;
        Secret_integers.U8 3uy; Secret_integers.U8 246uy; Secret_integers.U8 14uy;
        Secret_integers.U8 97uy; Secret_integers.U8 53uy; Secret_integers.U8 87uy;
        Secret_integers.U8 185uy; Secret_integers.U8 134uy; Secret_integers.U8 193uy;
        Secret_integers.U8 29uy; Secret_integers.U8 158uy; Secret_integers.U8 225uy;
        Secret_integers.U8 248uy; Secret_integers.U8 152uy; Secret_integers.U8 17uy;
        Secret_integers.U8 105uy; Secret_integers.U8 217uy; Secret_integers.U8 142uy;
        Secret_integers.U8 148uy; Secret_integers.U8 155uy; Secret_integers.U8 30uy;
        Secret_integers.U8 135uy; Secret_integers.U8 233uy; Secret_integers.U8 206uy;
        Secret_integers.U8 85uy; Secret_integers.U8 40uy; Secret_integers.U8 223uy;
        Secret_integers.U8 140uy; Secret_integers.U8 161uy; Secret_integers.U8 137uy;
        Secret_integers.U8 13uy; Secret_integers.U8 191uy; Secret_integers.U8 230uy;
        Secret_integers.U8 66uy; Secret_integers.U8 104uy; Secret_integers.U8 65uy;
        Secret_integers.U8 153uy; Secret_integers.U8 45uy; Secret_integers.U8 15uy;
        Secret_integers.U8 176uy; Secret_integers.U8 84uy; Secret_integers.U8 187uy;
        Secret_integers.U8 22uy
      ]
    in
    assert_norm (List.Tot.length l == 256);
    Rust_primitives.Hax.array_of_list l)

let v_RCON: t_RCon =
  RCon
  (let l =
      [
        Secret_integers.U8 141uy; Secret_integers.U8 1uy; Secret_integers.U8 2uy;
        Secret_integers.U8 4uy; Secret_integers.U8 8uy; Secret_integers.U8 16uy;
        Secret_integers.U8 32uy; Secret_integers.U8 64uy; Secret_integers.U8 128uy;
        Secret_integers.U8 27uy; Secret_integers.U8 54uy; Secret_integers.U8 108uy;
        Secret_integers.U8 216uy; Secret_integers.U8 171uy; Secret_integers.U8 77uy
      ]
    in
    assert_norm (List.Tot.length l == 15);
    Rust_primitives.Hax.array_of_list l)

let sub_bytes (state: t_Block) : t_Block =
  let st:t_Block = state in
  let st:t_Block =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_BLOCKSIZE
            }))
      st
      (fun st i ->
          Rust_primitives.Hax.update_at st
            i
            v_SBOX.[ Secret_integers.declassify_under_impl_2 state.[ i ] ])
  in
  st

let shift_row (i shift: usize) (state: t_Block) : t_Block =
  let out:t_Block = state in
  let out:t_Block = Rust_primitives.Hax.update_at out i state.[ i +. 4sz *. (shift %. 4sz) ] in
  let out:t_Block =
    Rust_primitives.Hax.update_at out (i +. 4sz) state.[ i +. 4sz *. ((shift +. 1sz) %. 4sz) ]
  in
  let out:t_Block =
    Rust_primitives.Hax.update_at out (i +. 8sz) state.[ i +. 4sz *. ((shift +. 2sz) %. 4sz) ]
  in
  let out:t_Block =
    Rust_primitives.Hax.update_at out (i +. 12sz) state.[ i +. 4sz *. ((shift +. 3sz) %. 4sz) ]
  in
  out

let shift_rows (state: t_Block) : t_Block =
  let state:t_Block = shift_row 1sz 1sz state in
  let state:t_Block = shift_row 2sz 2sz state in
  shift_row 3sz 3sz state

let xtime (x: Secret_integers.t_U8) : _ =
  let x1 = x >>. 1sz in
  let x7 = x <<. 7sz in
  let x71 = x7 &. Secret_integers.U8 1uy in
  let x711b = x71 *. Secret_integers.U8 27uy in
  x1 ^. x711b

let mix_column (c: usize) (state: t_Block) : t_Block =
  let i0:usize = 4sz *. c in
  let s0:Secret_integers.t_U8 = state.[ i0 ] in
  let s1:Secret_integers.t_U8 = state.[ i0 +. 1sz ] in
  let s2:Secret_integers.t_U8 = state.[ i0 +. 2sz ] in
  let s3:Secret_integers.t_U8 = state.[ i0 +. 3sz ] in
  let st:t_Block = state in
  let tmp = ((s0 ^. s1) ^. s2) ^. s3 in
  let st:t_Block = Rust_primitives.Hax.update_at st i0 ((s0 ^. tmp) ^. xtime (s0 ^. s1)) in
  let st:t_Block = Rust_primitives.Hax.update_at st (i0 +. 1sz) ((s1 ^. tmp) ^. xtime (s1 ^. s2)) in
  let st:t_Block = Rust_primitives.Hax.update_at st (i0 +. 2sz) ((s2 ^. tmp) ^. xtime (s2 ^. s3)) in
  let st:t_Block = Rust_primitives.Hax.update_at st (i0 +. 3sz) ((s3 ^. tmp) ^. xtime (s3 ^. s0)) in
  st

let mix_columns (state: t_Block) : t_Block =
  let state:t_Block = mix_column 0sz state in
  let state:t_Block = mix_column 1sz state in
  let state:t_Block = mix_column 2sz state in
  mix_column 3sz state

let add_round_key (state: t_Block) (key: t_RoundKey) : t_Block =
  let out:t_Block = state in
  let out:t_Block =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_BLOCKSIZE
            }))
      out
      (fun out i -> Rust_primitives.Hax.update_at out i (out.[ i ] ^. key.[ i ]))
  in
  out

let aes_enc (state: t_Block) (round_key: t_RoundKey) : t_Block =
  let state:t_Block = sub_bytes state in
  let state:t_Block = shift_rows state in
  let state:t_Block = mix_columns state in
  add_round_key state round_key

let aes_enc_last (state: t_Block) (round_key: t_RoundKey) : t_Block =
  let state:t_Block = sub_bytes state in
  let state:t_Block = shift_rows state in
  add_round_key state round_key

let rounds_aes (state: t_Block) (key: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Block =
  let out:t_Block = state in
  let out:t_Block =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Hacspec_lib.Seq.num_chunks_under_impl_41 key v_BLOCKSIZE
            }))
      out
      (fun out i ->
          let _, key_block:(usize & Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) =
            Hacspec_lib.Seq.get_chunk_under_impl_41 key v_BLOCKSIZE i
          in
          let out:t_Block = aes_enc out (from_seq_under_impl_88 key_block) in
          out)
  in
  out

let block_cipher_aes (input: t_Block) (key: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) (nr: usize)
    : t_Block =
  let k0:t_RoundKey =
    from_slice_range_under_impl_76 key
      ({ Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = 16sz })
  in
  let k:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.from_slice_range_under_impl_41 key
      ({ Core.Ops.Range.Range.f_start = 16sz; Core.Ops.Range.Range.f_end = nr *. 16sz })
  in
  let kn:t_RoundKey = from_slice_under_impl_76 key (nr *. 16sz) 16sz in
  let state:t_Block = add_round_key input k0 in
  let state:t_Block = rounds_aes state k in
  aes_enc_last state kn

let rotate_word (w: t_Word) : t_Word =
  Word
  (let l = [w.[ 1l ]; w.[ 2l ]; w.[ 3l ]; w.[ 0l ]] in
    assert_norm (List.Tot.length l == 4);
    Rust_primitives.Hax.array_of_list l)

let slice_word (w: t_Word) : t_Word =
  Word
  (let l =
      [
        v_SBOX.[ Secret_integers.declassify_usize_from_U8 w.[ 0l ] ];
        v_SBOX.[ Secret_integers.declassify_usize_from_U8 w.[ 1l ] ];
        v_SBOX.[ Secret_integers.declassify_usize_from_U8 w.[ 2l ] ];
        v_SBOX.[ Secret_integers.declassify_usize_from_U8 w.[ 3l ] ]
      ]
    in
    assert_norm (List.Tot.length l == 4);
    Rust_primitives.Hax.array_of_list l)

let aes_keygen_assist (w: t_Word) (rcon: Secret_integers.t_U8) : t_Word =
  let k:t_Word = rotate_word w in
  let k:t_Word = slice_word k in
  let k:t_Word = Rust_primitives.Hax.update_at k 0l (k.[ 0l ] ^. rcon) in
  k

let key_expansion_word (w0 w1: t_Word) (i nk nr: usize) : Core.Result.t_Result t_Word u8 =
  let k:t_Word = w1 in
  let result:Core.Result.t_Result t_Word u8 =
    Core.Result.Result.v_Err v_INVALID_KEY_EXPANSION_INDEX
  in
  let k, result:(t_Word & Core.Result.t_Result t_Word u8) =
    if i <. 4sz *. (nr +. 1sz)
    then
      let k:t_Word =
        if i %. nk =. 0sz
        then
          let k:t_Word = aes_keygen_assist k v_RCON.[ i /. nk ] in
          k
        else
          if Prims.op_AmpAmp (nk >. 6sz) (i %. nk =. 4sz)
          then
            let k:t_Word = slice_word k in
            k
          else k
      in
      let k:t_Word =
        Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                  Core.Ops.Range.Range.f_start = 0l;
                  Core.Ops.Range.Range.f_end = 4l
                }))
          k
          (fun k i -> Rust_primitives.Hax.update_at k i (k.[ i ] ^. w0.[ i ]))
      in
      let result:Core.Result.t_Result t_Word u8 = Core.Result.Result.v_Ok k in
      k, result
    else k, result
  in
  result

let key_expansion_aes
      (key: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (nk nr key_schedule_length key_length iterations: usize)
    : Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
  let key_ex:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 key_schedule_length
  in
  let key_ex:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Traits.SeqTrait.update_start key_ex key
  in
  let word_size:usize = key_length in
  let key_ex:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = iterations
            }))
      key_ex
      (fun key_ex j ->
          let i:usize = j +. word_size in
          let word:Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
            Core.Ops.Try_trait.FromResidual.from_residual (key_expansion_word (from_slice_under_impl_41
                      key_ex
                      (4sz *. (i -. word_size))
                      4sz)
                  (from_slice_under_impl_41 key_ex (4sz *. i -. 4sz) 4sz)
                  i
                  nk
                  nr)
          in
          let key_ex:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Traits.SeqTrait.update key_ex (4sz *. i) word
          in
          key_ex)
  in
  Core.Result.Result.v_Ok key_ex

let aes_encrypt_block
      (k: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (input: t_Block)
      (nk nr key_schedule_length key_length iterations: usize)
    : Core.Result.t_Result t_Block u8 =
  let key_ex:Core.Result.t_Result t_Block u8 =
    Core.Ops.Try_trait.FromResidual.from_residual (key_expansion_aes k
          nk
          nr
          key_schedule_length
          key_length
          iterations)
  in
  Core.Result.Result.v_Ok (block_cipher_aes input key_ex nr)

let aes128_encrypt_block (k: t_Key128) (input: t_Block) : t_Block =
  Core.Result.unwrap_under_impl (aes_encrypt_block (Hacspec_lib.Seq.from_seq_under_impl_52 k)
        input
        v_KEY_LENGTH
        v_ROUNDS
        v_KEY_SCHEDULE_LENGTH
        v_KEY_LENGTH
        v_ITERATIONS)

let aes_ctr_key_block
      (k: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (n: t_AesNonce)
      (c: Secret_integers.t_U32)
      (nk nr key_schedule_length key_length iterations: usize)
    : Core.Result.t_Result t_Block u8 =
  let input:t_Block = new_under_impl_5 in
  let input:t_Block = Hacspec_lib.Traits.SeqTrait.update input 0sz n in
  let input:t_Block =
    Hacspec_lib.Traits.SeqTrait.update input 12sz (Hacspec_lib.Transmute.v_U32_to_be_bytes c)
  in
  aes_encrypt_block k input nk nr key_schedule_length key_length iterations

let xor_block (block key_block: t_Block) : t_Block =
  let out:t_Block = block in
  let out:t_Block =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = v_BLOCKSIZE
            }))
      out
      (fun out i -> Rust_primitives.Hax.update_at out i (out.[ i ] ^. key_block.[ i ]))
  in
  out

let aes_counter_mode
      (key: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (nonce: t_AesNonce)
      (counter: Secret_integers.t_U32)
      (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
      (nk nr key_schedule_length key_length iterations: usize)
    : Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
  let ctr:Secret_integers.t_U32 = counter in
  let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.new_under_impl_41 (Hacspec_lib.Seq.len_under_impl_41 msg)
  in
  let n_blocks:usize = Hacspec_lib.Seq.num_exact_chunks_under_impl_41 msg v_BLOCKSIZE in
  let blocks_out, ctr:(Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 & _) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = n_blocks
            }))
      (blocks_out, ctr)
      (fun (blocks_out, ctr) i ->
          let msg_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.get_exact_chunk_under_impl_41 msg v_BLOCKSIZE i
          in
          let key_block:Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
            Core.Ops.Try_trait.FromResidual.from_residual (aes_ctr_key_block key
                  nonce
                  ctr
                  nk
                  nr
                  key_schedule_length
                  key_length
                  iterations)
          in
          let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
            Hacspec_lib.Seq.set_chunk_under_impl_41 blocks_out
              v_BLOCKSIZE
              i
              (xor_block (from_seq_under_impl_18 msg_block) key_block)
          in
          let ctr = ctr +. Secret_integers.U32 1ul in
          blocks_out, ctr)
  in
  let last_block:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    Hacspec_lib.Seq.get_remainder_chunk_under_impl_41 msg v_BLOCKSIZE
  in
  let last_block_len:usize = Hacspec_lib.Seq.len_under_impl_41 last_block in
  let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
    if last_block_len <>. 0sz
    then
      let last_block:t_Block =
        Hacspec_lib.Traits.SeqTrait.update_start new_under_impl_5 last_block
      in
      let key_block:Core.Result.t_Result (Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) u8 =
        Core.Ops.Try_trait.FromResidual.from_residual (aes_ctr_key_block key
              nonce
              ctr
              nk
              nr
              key_schedule_length
              key_length
              iterations)
      in
      let blocks_out:Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
        Hacspec_lib.Seq.set_chunk_under_impl_41 blocks_out
          v_BLOCKSIZE
          n_blocks
          (slice_range_under_impl_6 (xor_block last_block key_block)
              ({ Core.Ops.Range.Range.f_start = 0sz; Core.Ops.Range.Range.f_end = last_block_len }))
      in
      blocks_out
    else blocks_out
  in
  Core.Result.Result.v_Ok blocks_out

let aes128_encrypt
      (key: t_Key128)
      (nonce: t_AesNonce)
      (counter: Secret_integers.t_U32)
      (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Core.Result.unwrap_under_impl (aes_counter_mode (Hacspec_lib.Seq.from_seq_under_impl_52 key)
        nonce
        counter
        msg
        v_KEY_LENGTH
        v_ROUNDS
        v_KEY_SCHEDULE_LENGTH
        v_KEY_LENGTH
        v_ITERATIONS)

let aes128_decrypt
      (key: t_Key128)
      (nonce: t_AesNonce)
      (counter: Secret_integers.t_U32)
      (ctxt: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8)
    : Hacspec_lib.Seq.t_Seq Secret_integers.t_U8 =
  Core.Result.unwrap_under_impl (aes_counter_mode (Hacspec_lib.Seq.from_seq_under_impl_52 key)
        nonce
        counter
        ctxt
        v_KEY_LENGTH
        v_ROUNDS
        v_KEY_SCHEDULE_LENGTH
        v_KEY_LENGTH
        v_ITERATIONS)