module Alloc.Vec
open Core.Types

unfold type t_Vec t _ = slice t

let new_under_impl #t: t_Vec t () = FStar.Seq.empty

let extend_from_slice_under_impl_2 #t (self: t_Vec t ()) (other: slice t {SizeT.fits (Seq.length self + Seq.length other)}): t_Vec t ()
  = FStar.Seq.append self other

