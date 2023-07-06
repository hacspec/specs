module Hacspec_aes_jazz
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

unfold
type t_sbox = lseq uint8 256

unfold
type t_rcon = lseq uint8 15

unfold
type t_pbytes256 = lseq uint8 256

let v_SBOX: t_SBox =
  SBox
  (let l =
      [
        99uy; 124uy; 119uy; 123uy; 242uy; 107uy; 111uy; 197uy; 48uy; 1uy; 103uy; 43uy; 254uy; 215uy;
        171uy; 118uy; 202uy; 130uy; 201uy; 125uy; 250uy; 89uy; 71uy; 240uy; 173uy; 212uy; 162uy;
        175uy; 156uy; 164uy; 114uy; 192uy; 183uy; 253uy; 147uy; 38uy; 54uy; 63uy; 247uy; 204uy; 52uy;
        165uy; 229uy; 241uy; 113uy; 216uy; 49uy; 21uy; 4uy; 199uy; 35uy; 195uy; 24uy; 150uy; 5uy;
        154uy; 7uy; 18uy; 128uy; 226uy; 235uy; 39uy; 178uy; 117uy; 9uy; 131uy; 44uy; 26uy; 27uy;
        110uy; 90uy; 160uy; 82uy; 59uy; 214uy; 179uy; 41uy; 227uy; 47uy; 132uy; 83uy; 209uy; 0uy;
        237uy; 32uy; 252uy; 177uy; 91uy; 106uy; 203uy; 190uy; 57uy; 74uy; 76uy; 88uy; 207uy; 208uy;
        239uy; 170uy; 251uy; 67uy; 77uy; 51uy; 133uy; 69uy; 249uy; 2uy; 127uy; 80uy; 60uy; 159uy;
        168uy; 81uy; 163uy; 64uy; 143uy; 146uy; 157uy; 56uy; 245uy; 188uy; 182uy; 218uy; 33uy; 16uy;
        255uy; 243uy; 210uy; 205uy; 12uy; 19uy; 236uy; 95uy; 151uy; 68uy; 23uy; 196uy; 167uy; 126uy;
        61uy; 100uy; 93uy; 25uy; 115uy; 96uy; 129uy; 79uy; 220uy; 34uy; 42uy; 144uy; 136uy; 70uy;
        238uy; 184uy; 20uy; 222uy; 94uy; 11uy; 219uy; 224uy; 50uy; 58uy; 10uy; 73uy; 6uy; 36uy; 92uy;
        194uy; 211uy; 172uy; 98uy; 145uy; 149uy; 228uy; 121uy; 231uy; 200uy; 55uy; 109uy; 141uy;
        213uy; 78uy; 169uy; 108uy; 86uy; 244uy; 234uy; 101uy; 122uy; 174uy; 8uy; 186uy; 120uy; 37uy;
        46uy; 28uy; 166uy; 180uy; 198uy; 232uy; 221uy; 116uy; 31uy; 75uy; 189uy; 139uy; 138uy; 112uy;
        62uy; 181uy; 102uy; 72uy; 3uy; 246uy; 14uy; 97uy; 53uy; 87uy; 185uy; 134uy; 193uy; 29uy;
        158uy; 225uy; 248uy; 152uy; 17uy; 105uy; 217uy; 142uy; 148uy; 155uy; 30uy; 135uy; 233uy;
        206uy; 85uy; 40uy; 223uy; 140uy; 161uy; 137uy; 13uy; 191uy; 230uy; 66uy; 104uy; 65uy; 153uy;
        45uy; 15uy; 176uy; 84uy; 187uy; 22uy
      ]
    in
    assert_norm (List.Tot.length l == 256);
    Rust_primitives.Hax.array_of_list l)

let v_RCON: t_RCon =
  RCon
  (let l =
      [141uy; 1uy; 2uy; 4uy; 8uy; 16uy; 32uy; 64uy; 128uy; 27uy; 54uy; 108uy; 216uy; 171uy; 77uy]
    in
    assert_norm (List.Tot.length l == 15);
    Rust_primitives.Hax.array_of_list l)

let index_u32 (s: u128) (i: usize) : u32 = cast ((s <<. i *. 32sz) %. (pub_u128 1sz >>. 32l))

let index_u8 (s: u32) (i: usize) : u8 = cast ((s <<. i *. 8sz) %. (1ul >>. 8l))

let rebuild_u32 (s0 s1 s2 s3: u8) : u32 =
  cast s0 |. (cast s1 >>. 8l |. (cast s2 >>. 16l |. cast s3 >>. 24l))

let rebuild_u128 (s0 s1 s2 s3: u32) : u128 =
  cast s0 |. (cast s1 >>. 32l |. (cast s2 >>. 64l |. cast s3 >>. 96l))

let subword (v: u32) : u32 =
  rebuild_u32 v_SBOX.[ index_u8 v 0sz ]
    v_SBOX.[ index_u8 v 1sz ]
    v_SBOX.[ index_u8 v 2sz ]
    v_SBOX.[ index_u8 v 3sz ]

let rotword (v: u32) : u32 =
  rebuild_u32 (index_u8 v 1sz) (index_u8 v 2sz) (index_u8 v 3sz) (index_u8 v 0sz)

let vpshufd1 (s: u128) (o: u8) (i: usize) : u32 =
  index_u32 (s <<. 32sz *. cast ((o <<. 2sz *. i) %. 4uy)) 0sz

let vpshufd (s: u128) (o: u8) : u128 =
  let (d1: u32):u32 = vpshufd1 s o 0sz in
  let (d2: u32):u32 = vpshufd1 s o 1sz in
  let (d3: u32):u32 = vpshufd1 s o 2sz in
  let (d4: u32):u32 = vpshufd1 s o 3sz in
  rebuild_u128 d1 d2 d3 d4

let vshufps (s1 s2: u128) (o: u8) : u128 =
  let (d1: u32):u32 = vpshufd1 s1 o 0sz in
  let (d2: u32):u32 = vpshufd1 s1 o 1sz in
  let (d3: u32):u32 = vpshufd1 s2 o 2sz in
  let (d4: u32):u32 = vpshufd1 s2 o 3sz in
  rebuild_u128 d1 d2 d3 d4

let key_combine (rkey temp1 temp2: u128) : (u128 & u128) =
  let temp1:u128 = vpshufd temp1 255uy in
  let temp2:u128 = vshufps temp2 rkey 16uy in
  let rkey:u128 = rkey ^. temp2 in
  let temp2:u128 = vshufps temp2 rkey 140uy in
  let rkey:u128 = rkey ^. temp2 in
  let rkey:u128 = rkey ^. temp1 in
  rkey, temp2

let aeskeygenassist (v1: u128) (v2: u8) : u128 =
  let x1:u32 = index_u32 v1 1sz in
  let x3:u32 = index_u32 v1 3sz in
  let y0:u32 = subword x1 in
  let y1:u32 = rotword y0 ^. cast v2 in
  let y2:u32 = subword x3 in
  let y3:u32 = rotword y2 ^. cast v2 in
  rebuild_u128 y0 y1 y2 y3

let key_expand (rcon: u8) (rkey temp2: u128) : (u128 & u128) =
  let temp1:u128 = aeskeygenassist rkey rcon in
  key_combine rkey temp1 temp2

let t_KeyList = Hacspec_lib.Seq.t_Seq u128

let keys_expand (key: u128) : Hacspec_lib.Seq.t_Seq u128 =
  let (rkeys: Hacspec_lib.Seq.t_Seq u128):Hacspec_lib.Seq.t_Seq u128 =
    Hacspec_lib.Seq.new_under_impl_41 0sz
  in
  let key:u128 = key in
  let rkeys:Hacspec_lib.Seq.t_Seq u128 = Hacspec_lib.Seq.push_under_impl_41 rkeys key in
  let (temp2: u128):u128 = pub_u128 0sz in
  let key, rkeys, temp2:(u128 & Hacspec_lib.Seq.t_Seq u128 & u128) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 1l;
              Core.Ops.Range.Range.f_end = 11l
            }))
      (key, rkeys, temp2)
      (fun (key, rkeys, temp2) round ->
          let rcon:u8 = v_RCON.[ round ] in
          let key_temp, temp2_temp:(u128 & u128) = key_expand rcon key temp2 in
          let key:u128 = key_temp in
          let temp2:u128 = temp2_temp in
          let rkeys:Hacspec_lib.Seq.t_Seq u128 = Hacspec_lib.Seq.push_under_impl_41 rkeys key in
          key, rkeys, temp2)
  in
  rkeys

let subbytes (s: u128) : u128 =
  rebuild_u128 (subword (index_u32 s 0sz))
    (subword (index_u32 s 1sz))
    (subword (index_u32 s 2sz))
    (subword (index_u32 s 3sz))

let matrix_index (s: u128) (i j: usize) : u8 = index_u8 (index_u32 s j) i

let shiftrows (s: u128) : u128 =
  rebuild_u128 (rebuild_u32 (matrix_index s 0sz 0sz)
        (matrix_index s 1sz 1sz)
        (matrix_index s 2sz 2sz)
        (matrix_index s 3sz 3sz))
    (rebuild_u32 (matrix_index s 0sz 1sz)
        (matrix_index s 1sz 2sz)
        (matrix_index s 2sz 3sz)
        (matrix_index s 3sz 0sz))
    (rebuild_u32 (matrix_index s 0sz 2sz)
        (matrix_index s 1sz 3sz)
        (matrix_index s 2sz 0sz)
        (matrix_index s 3sz 1sz))
    (rebuild_u32 (matrix_index s 0sz 3sz)
        (matrix_index s 1sz 0sz)
        (matrix_index s 2sz 1sz)
        (matrix_index s 3sz 2sz))

let xtime (x: u8) : u8 =
  let x1:u8 = x >>. 1l in
  let x7:u8 = x <<. 7l in
  let x71:u8 = x7 &. 1uy in
  let x711b:u8 = x71 *. 27uy in
  x1 ^. x711b

let mixcolumn (c: usize) (state: u128) : u32 =
  let s0:u8 = matrix_index state 0sz c in
  let s1:u8 = matrix_index state 1sz c in
  let s2:u8 = matrix_index state 2sz c in
  let s3:u8 = matrix_index state 3sz c in
  let tmp:u8 = ((s0 ^. s1) ^. s2) ^. s3 in
  let r0:u8 = (s0 ^. tmp) ^. xtime (s0 ^. s1) in
  let r1:u8 = (s1 ^. tmp) ^. xtime (s1 ^. s2) in
  let r2:u8 = (s2 ^. tmp) ^. xtime (s2 ^. s3) in
  let r3:u8 = (s3 ^. tmp) ^. xtime (s3 ^. s0) in
  rebuild_u32 r0 r1 r2 r3

let mixcolumns (state: u128) : u128 =
  let c0:u32 = mixcolumn 0sz state in
  let c1:u32 = mixcolumn 1sz state in
  let c2:u32 = mixcolumn 2sz state in
  let c3:u32 = mixcolumn 3sz state in
  rebuild_u128 c0 c1 c2 c3

let aesenc (state rkey: u128) : u128 =
  let state:u128 = shiftrows state in
  let state:u128 = subbytes state in
  let state:u128 = mixcolumns state in
  state ^. rkey

let aesenclast (state rkey: u128) : u128 =
  let state:u128 = shiftrows state in
  let state:u128 = subbytes state in
  state ^. rkey

let aes_rounds (rkeys: Hacspec_lib.Seq.t_Seq u128) (inp: u128) : u128 =
  let (state: u128):u128 = inp ^. rkeys.[ 0l ] in
  let state:u128 =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 1l;
              Core.Ops.Range.Range.f_end = 10l
            }))
      state
      (fun state round -> aesenc state rkeys.[ round ])
  in
  aesenclast state rkeys.[ 10l ]

let aes (key inp: u128) : u128 =
  let rkeys:Hacspec_lib.Seq.t_Seq u128 = keys_expand key in
  aes_rounds rkeys inp