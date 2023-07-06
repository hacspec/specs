module Hacspec_sha512
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_BLOCK_SIZE: usize = 128sz

let v_LEN_SIZE: usize = 16sz

let v_K_SIZE: usize = 80sz

let v_HASH_SIZE: usize = 512sz /. 8sz

unfold
type t_block = lseq uint8 BLOCK_SIZE

unfold
type t_optabletype = lseq uint_size 12

unfold
type t_sha512digest = lseq uint8 HASH_SIZE

unfold
type t_roundconstantstable = lseq uint_size K_SIZE

unfold
type t_hash = lseq uint_size 8

let ch (x y z: Secret_integers.t_U64) : _ = (x &. y) ^. (~.x &. z)

let maj (x y z: Secret_integers.t_U64) : _ = (x &. y) ^. (x &. z) ^. (y &. z)

let v_OP_TABLE: t_OpTableType =
  OpTableType
  (let l = [28sz; 34sz; 39sz; 14sz; 18sz; 41sz; 1sz; 8sz; 7sz; 19sz; 61sz; 6sz] in
    assert_norm (List.Tot.length l == 12);
    Rust_primitives.Hax.array_of_list l)

let v_K_TABLE: t_RoundConstantsTable =
  RoundConstantsTable
  (let l =
      [
        Secret_integers.U64 4794697086780616226uL; Secret_integers.U64 8158064640168781261uL;
        Secret_integers.U64 13096744586834688815uL; Secret_integers.U64 16840607885511220156uL;
        Secret_integers.U64 4131703408338449720uL; Secret_integers.U64 6480981068601479193uL;
        Secret_integers.U64 10538285296894168987uL; Secret_integers.U64 12329834152419229976uL;
        Secret_integers.U64 15566598209576043074uL; Secret_integers.U64 1334009975649890238uL;
        Secret_integers.U64 2608012711638119052uL; Secret_integers.U64 6128411473006802146uL;
        Secret_integers.U64 8268148722764581231uL; Secret_integers.U64 9286055187155687089uL;
        Secret_integers.U64 11230858885718282805uL; Secret_integers.U64 13951009754708518548uL;
        Secret_integers.U64 16472876342353939154uL; Secret_integers.U64 17275323862435702243uL;
        Secret_integers.U64 1135362057144423861uL; Secret_integers.U64 2597628984639134821uL;
        Secret_integers.U64 3308224258029322869uL; Secret_integers.U64 5365058923640841347uL;
        Secret_integers.U64 6679025012923562964uL; Secret_integers.U64 8573033837759648693uL;
        Secret_integers.U64 10970295158949994411uL; Secret_integers.U64 12119686244451234320uL;
        Secret_integers.U64 12683024718118986047uL; Secret_integers.U64 13788192230050041572uL;
        Secret_integers.U64 14330467153632333762uL; Secret_integers.U64 15395433587784984357uL;
        Secret_integers.U64 489312712824947311uL; Secret_integers.U64 1452737877330783856uL;
        Secret_integers.U64 2861767655752347644uL; Secret_integers.U64 3322285676063803686uL;
        Secret_integers.U64 5560940570517711597uL; Secret_integers.U64 5996557281743188959uL;
        Secret_integers.U64 7280758554555802590uL; Secret_integers.U64 8532644243296465576uL;
        Secret_integers.U64 9350256976987008742uL; Secret_integers.U64 10552545826968843579uL;
        Secret_integers.U64 11727347734174303076uL; Secret_integers.U64 12113106623233404929uL;
        Secret_integers.U64 14000437183269869457uL; Secret_integers.U64 14369950271660146224uL;
        Secret_integers.U64 15101387698204529176uL; Secret_integers.U64 15463397548674623760uL;
        Secret_integers.U64 17586052441742319658uL; Secret_integers.U64 1182934255886127544uL;
        Secret_integers.U64 1847814050463011016uL; Secret_integers.U64 2177327727835720531uL;
        Secret_integers.U64 2830643537854262169uL; Secret_integers.U64 3796741975233480872uL;
        Secret_integers.U64 4115178125766777443uL; Secret_integers.U64 5681478168544905931uL;
        Secret_integers.U64 6601373596472566643uL; Secret_integers.U64 7507060721942968483uL;
        Secret_integers.U64 8399075790359081724uL; Secret_integers.U64 8693463985226723168uL;
        Secret_integers.U64 9568029438360202098uL; Secret_integers.U64 10144078919501101548uL;
        Secret_integers.U64 10430055236837252648uL; Secret_integers.U64 11840083180663258601uL;
        Secret_integers.U64 13761210420658862357uL; Secret_integers.U64 14299343276471374635uL;
        Secret_integers.U64 14566680578165727644uL; Secret_integers.U64 15097957966210449927uL;
        Secret_integers.U64 16922976911328602910uL; Secret_integers.U64 17689382322260857208uL;
        Secret_integers.U64 500013540394364858uL; Secret_integers.U64 748580250866718886uL;
        Secret_integers.U64 1242879168328830382uL; Secret_integers.U64 1977374033974150939uL;
        Secret_integers.U64 2944078676154940804uL; Secret_integers.U64 3659926193048069267uL;
        Secret_integers.U64 4368137639120453308uL; Secret_integers.U64 4836135668995329356uL;
        Secret_integers.U64 5532061633213252278uL; Secret_integers.U64 6448918945643986474uL;
        Secret_integers.U64 6902733635092675308uL; Secret_integers.U64 7801388544844847127uL
      ]
    in
    assert_norm (List.Tot.length l == 80);
    Rust_primitives.Hax.array_of_list l)

let v_HASH_INIT: t_Hash =
  Hash
  (let l =
      [
        Secret_integers.U64 7640891576956012808uL;
        Secret_integers.U64 13503953896175478587uL;
        Secret_integers.U64 4354685564936845355uL;
        Secret_integers.U64 11912009170470909681uL;
        Secret_integers.U64 5840696475078001361uL;
        Secret_integers.U64 11170449401992604703uL;
        Secret_integers.U64 2270897969802886507uL;
        Secret_integers.U64 6620516959819538809uL
      ]
    in
    assert_norm (List.Tot.length l == 8);
    Rust_primitives.Hax.array_of_list l)

let sigma (x: Secret_integers.t_U64) (i op: usize) : _ =
  let (tmp: Secret_integers.t_U64):Secret_integers.t_U64 =
    Secret_integers.rotate_right_under_impl_97 x v_OP_TABLE.[ 3sz *. i +. 2sz ]
  in
  let tmp = if op =. 0sz then x <<. v_OP_TABLE.[ 3sz *. i +. 2sz ] else tmp in
  (Secret_integers.rotate_right_under_impl_97 x v_OP_TABLE.[ 3sz *. i ] ^.
  Secret_integers.rotate_right_under_impl_97 x v_OP_TABLE.[ 3sz *. i +. 1sz ]) ^.
  tmp

let schedule (block: t_Block) : t_RoundConstantsTable =
  let b:Hacspec_lib.Seq.t_Seq Secret_integers.t_U64 = to_be_U64s_under_impl block in
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
            let t16:Secret_integers.t_U64 = s.[ i -. 16sz ] in
            let t15:Secret_integers.t_U64 = s.[ i -. 15sz ] in
            let t7:Secret_integers.t_U64 = s.[ i -. 7sz ] in
            let t2:Secret_integers.t_U64 = s.[ i -. 2sz ] in
            let s1:Secret_integers.t_U64 = sigma t2 3sz 0sz in
            let s0:Secret_integers.t_U64 = sigma t15 2sz 0sz in
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
          let a0:Secret_integers.t_U64 = h.[ 0l ] in
          let b0:Secret_integers.t_U64 = h.[ 1l ] in
          let c0:Secret_integers.t_U64 = h.[ 2l ] in
          let d0:Secret_integers.t_U64 = h.[ 3l ] in
          let e0:Secret_integers.t_U64 = h.[ 4l ] in
          let f0:Secret_integers.t_U64 = h.[ 5l ] in
          let g0:Secret_integers.t_U64 = h.[ 6l ] in
          let (h0: Secret_integers.t_U64):Secret_integers.t_U64 = h.[ 7l ] in
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

let hash (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Sha512Digest =
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
  let len_bist:Secret_integers.t_U128 =
    Secret_integers.U128 (cast (Hacspec_lib.Seq.len_under_impl_41 msg *. 8sz))
  in
  let h, last_block:(t_Hash & t_Block) =
    if last_block_len <. v_BLOCK_SIZE -. v_LEN_SIZE
    then
      let last_block:t_Block =
        Hacspec_lib.Traits.SeqTrait.update last_block
          (v_BLOCK_SIZE -. v_LEN_SIZE)
          (Hacspec_lib.Transmute.v_U128_to_be_bytes len_bist)
      in
      let h:t_Hash = compress last_block h in
      h, last_block
    else
      let pad_block:t_Block = new_under_impl_5 in
      let pad_block:t_Block =
        Hacspec_lib.Traits.SeqTrait.update pad_block
          (v_BLOCK_SIZE -. v_LEN_SIZE)
          (Hacspec_lib.Transmute.v_U128_to_be_bytes len_bist)
      in
      let h:t_Hash = compress last_block h in
      let h:t_Hash = compress pad_block h in
      h, last_block
  in
  from_seq_under_impl_73 (to_be_bytes_under_impl_126 h)

let sha512 (msg: Hacspec_lib.Seq.t_Seq Secret_integers.t_U8) : t_Sha512Digest = hash msg