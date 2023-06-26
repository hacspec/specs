module Chacha20.Bounded_index
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_BoundedIndex = | BoundedIndex : usize -> t_BoundedIndex