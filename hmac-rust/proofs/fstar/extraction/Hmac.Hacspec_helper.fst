module Hmac.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let xor_slice (this: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (other: slice u8)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let _:Prims.unit =
    if
      ~.((Alloc.Vec.len_under_impl_1 this <: usize) =. (Core.Slice.len_under_impl other <: usize)
        <:
        bool)
    then
      let ():Prims.unit =
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: this.len() == other.len()"

            <:
            Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let this:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Alloc.Vec.len_under_impl_1 this <: usize
            })
        <:
        _)
      this
      (fun (this: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) (i: usize) ->
          (this.[ i ] <- (this.[ i ] <: u8) ^. (other.[ i ] <: u8) <: u8)
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  in
  this