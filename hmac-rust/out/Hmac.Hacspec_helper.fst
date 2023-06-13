module Hmac.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

let xor_slice (this: Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t) (other: FStar.Seq.seq UInt8.t)
    : Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
  let _:Prims.l_False =
    if Prims.l_Not (Alloc.Vec.len this = Core.Slice.len other)
    then Core.Panicking.panic "assertion failed: this.len() == other.len()"
  in
  let this:Alloc.Vec.vec_t UInt8.t Alloc.Alloc.global_t =
    Core.Iter.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              start = 0;
              end = Alloc.Vec.len this
            }))
      this
      (fun i this -> this.[ i ] <- Hacspec_lib.^. this.[ i ] (Core.Ops.Index.index other i))
  in
  this