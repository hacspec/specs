module Bounded_indexes

open Core
open FStar.Integers

type t_BoundedIndex (max: usize) =
  | BoundedIndex: n:usize {SizeT.v n < SizeT.v max} -> t_BoundedIndex max

instance index_array t (l: SizeT.t): index (array t l) (t_BoundedIndex l) = {
  output = t;
  in_range = (fun (s: array _ _) (BoundedIndex i) -> FStar.Seq.length s > FStar.SizeT.v i);
  (.[]) = (fun s (BoundedIndex i) -> s.[i])
}

instance update_at_array t (l: SizeT.t): update_at (array t l) (t_BoundedIndex l) =
  let super_index = index_array t l in
  let self = array t l in
  let (.[]<-): s: self -> i:_ {super_index.in_range s i} -> super_index.output -> self = 
    fun s (BoundedIndex i) v -> FStar.Seq.upd s (FStar.SizeT.v i) v
  in
  { super_index; (.[]<-) }


