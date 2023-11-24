module Hacspec_concordium
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let trap: Rust_primitives.Hax.t_Never = Core.Intrinsics.abort