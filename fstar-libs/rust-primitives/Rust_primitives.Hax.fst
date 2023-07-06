module Rust_primitives.Hax

let x = 0ul

let repeat (value: 'a) (n: SizeT.t): FStar.Seq.seq 'a = 
  FStar.Seq.create (SizeT.v n) value

type t_Never =

open Core.Types
let update_at #t #n (arr: array t n)
  (i: usize {FStar.Seq.length arr > FStar.SizeT.v i})
  (v: t)
 = FStar.Seq.upd arr (FStar.SizeT.v i) v

let never_to_any #t (x: t_Never): t = (match x with)

let array_of_list = Seq.seq_of_list

