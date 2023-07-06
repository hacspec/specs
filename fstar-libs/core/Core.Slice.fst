module Core.Slice
open Core.Types

let len_under_impl (s: slice 'a)
  : len: usize {len == SizeT.uint_to_t (Seq.length s)} = 
  SizeT.uint_to_t (Seq.length s)
