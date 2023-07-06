module Bounded_indexes
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_BoundedIndex = | BoundedIndex : usize -> t_BoundedIndex

let impl (#max: usize) (#t: Type) : Core.Ops.Index.t_Index (array t v_MAX) (t_BoundedIndex v_MAX) =
  {
    output = t;
    index
    =
    fun (#max: usize) (#t: Type) (self: array t v_MAX) (BoundedIndex i: t_BoundedIndex v_MAX) ->
      self.[ i ]
  }

(* RefMut:The mutation of this &mut is not allowed here.

Last available AST for this item:

/* TO DO */
 *)