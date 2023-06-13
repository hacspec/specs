module Hmac
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

class hash (self: Type) = {
  bLOCK_LEN:uint_size;
  hASH_LEN:uint_size;
  hash:FStar.Seq.seq UInt8.t -> Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t
}

type sha256_t = {  }

let impl: Hash sha256_t =
  {
    bLOCK_LEN = (fun  -> 64);
    hASH_LEN = (fun  -> 32);
    hash
    =
    fun (bytes: FStar.Seq.seq UInt8.t) ->
      Alloc.Slice.to_vec (Hacspec.Lib.unsize (Sha256.sha256 bytes))
  }

let o_pad
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: hash_t h)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t = Alloc.Vec.from_elem 92uy Hmac.Hash.bLOCK_LEN

let i_pad
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: hash_t h)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t = Alloc.Vec.from_elem 54uy Hmac.Hash.bLOCK_LEN

let k_block
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: hash_t h)
      (k: FStar.Seq.seq UInt8.t)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
  let k:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    if Prims.op_GreaterThanOrEqual (Core.Slice.len k) Hmac.Hash.bLOCK_LEN
    then Hmac.Hash.hash k
    else Alloc.Slice.to_vec k
  in
  let block:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    Alloc.Vec.from_elem 0uy Hmac.Hash.bLOCK_LEN
  in
  let block:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = Alloc.Vec.len k
            }))
      block
      (fun i block -> block.[ i ] <- k.[ i ])
  in
  block

let hmac
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.sized_t h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: hash_t h)
      (k txt: FStar.Seq.seq UInt8.t)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
  let k_block:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t = k_block k in
  let h_in:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    Hmac.Hacspec_helper.xor_slice (Core.Clone.Clone.clone k_block)
      (Core.Ops.Deref.Deref.deref i_pad)
  in
  let h_in:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t = Alloc.Vec.extend_from_slice h_in txt in
  let h_inner:x: Prims.list UInt8.t {Prims.op_Equality (FStar.List.Tot.Base.length x) 32} =
    Sha256.hash (Core.Ops.Deref.Deref.deref h_in)
  in
  let h_in:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    Hmac.Hacspec_helper.xor_slice k_block (Core.Ops.Deref.Deref.deref o_pad)
  in
  let h_in:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    Alloc.Vec.extend_from_slice h_in (Hacspec.Lib.unsize h_inner)
  in
  Alloc.Slice.to_vec (Hacspec.Lib.unsize (Sha256.hash (Core.Ops.Deref.Deref.deref h_in)))