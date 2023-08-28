module Hmac
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

class toString t = {
      to_string: t -> string
}



class t_Hash (v_Self: Type) = {
  v_BLOCK_LEN:usize;
  v_HASH_LEN:usize;
  hash:slice u8 -> Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

type t_Sha256 = | Sha256 : t_Sha256




let impl_ a: t_Hash (list a) = magic ()


let impl: t_Hash t_Sha256 =
  {
    v_BLOCK_LEN = 64sz;
    v_HASH_LEN = 32sz;
    hash
    =
    fun (bytes: slice u8) ->
      Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (Sha256.sha256 bytes <: t_Array u8 32sz)
          <:
          slice u8)
  }

// let foo x (y: t_Hash x): usize = v_BLOCK_LEN #x #y

let o_pad
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: t_Hash (list h))
      = 
        __1.v_BLOCK_LEN

let impl_list_t_Sha256 = impl_ t_Sha256


let o_pad
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.t_Sized h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: t_Hash h)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = 
      
      Alloc.Vec.from_elem 92uy (v_BLOCK_LEN #h)
      Hash
      
      Alloc.Vec.from_elem 92uy __1.v_BLOCK_LEN


let i_pad
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.t_Sized h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: t_Hash h)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.from_elem 54uy Hmac.Hash.v_BLOCK_LEN

let k_block
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.t_Sized h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: t_Hash h)
      (k: slice u8)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let k:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if (Core.Slice.len_under_impl k <: usize) >. Hmac.Hash.v_BLOCK_LEN
    then Hmac.Hash.hash k
    else Alloc.Slice.to_vec_under_impl k
  in
  let block:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.from_elem 0uy Hmac.Hash.v_BLOCK_LEN
  in
  let block:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Alloc.Vec.len_under_impl_1 k <: usize
            })
        <:
        _)
      block
      (fun (block: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (i: usize) ->
          (block.[ i ] <- k.[ i ] <: u8) <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  in
  block

let hmac
      (#h: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __0: Core.Marker.t_Sized h)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] __1: t_Hash h)
      (k txt: slice u8)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let k_block:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = k_block k in
  let h_in:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Hmac.Hacspec_helper.xor_slice (Core.Clone.Clone.clone k_block
        <:
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      (Core.Ops.Deref.Deref.deref (i_pad <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) <: slice u8)
  in
  let h_in:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.extend_from_slice_under_impl_2 h_in txt
  in
  let h_inner:t_Array u8 32sz = Sha256.hash (Core.Ops.Deref.Deref.deref h_in <: slice u8) in
  let h_in:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Hmac.Hacspec_helper.xor_slice k_block
      (Core.Ops.Deref.Deref.deref (o_pad <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) <: slice u8)
  in
  let h_in:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.extend_from_slice_under_impl_2 h_in (Rust_primitives.unsize h_inner <: slice u8)
  in
  Alloc.Slice.to_vec_under_impl (Rust_primitives.unsize (Sha256.hash (Core.Ops.Deref.Deref.deref h_in

              <:
              slice u8)
          <:
          t_Array u8 32sz)
      <:
      slice u8)
